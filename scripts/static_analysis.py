#!/usr/bin/env python3
"""Static analysis over a 6502 disassembly, via xasm's assembled JSON listing.

Never regex over source: instruction identity, addressing mode, and operand
values come from the listing (``directive_or_opcode`` / ``addressing_mode`` /
``bytes_hex``); a control-flow graph is built from ROM output offsets (unique
across mapper banks, unlike CPU addresses); backward liveness of the registers
{A,X,Y} and flags {Z,N,C,V} runs over that CFG. Every finding is verified against
liveness on all paths.

Reports (see the generated STATIC_ANALYSIS.md for prose):
  A correctness : symptoms that expose likely typos/misconceptions. (1) An index
                  register live-in to a fixed-count copy loop (read before the
                  routine writes it -> overrun); split by confidence -- a
                  wrong-register init is a confirmed defect, else a call-site review
                  candidate. (2) A dead LD? #imm right before a ST? that reads a
                  different register -- a load/store register mismatch, so #imm is
                  discarded and a stale register is stored. (3) A dead
                  carry-setter (CLC/SEC/CMP) discarded by a following accumulator
                  ASL/LSR -- the shift folds 0, not carry, so ROL/ROR was likely
                  meant (a real bug where the carry mattered).
  B dead        : a def whose every output is dead-on-exit, no side effect.
  C micro-opts  : AND #$80 -> BMI/BPL (only when A and Z are both dead after the
                  branch); redundant CMP #$00; TXA/TYA+CMP -> CPX/CPY.
  D reload      : ST_ x ; LD_ x (same location) -> drop reload.
  (Category-C candidates whose value is not provably dead are kept in the
  `excluded` bucket for --json/debugging only; they are not in the doc report.)

Conservative by construction (credibility over completeness): JSR and RTS/RTI use
every register/flag; absolute JMP/JSR targets and non-ROM-contiguous fall-through
(the ``.DB $2C`` opcode-skip idiom, embedded tables) are treated as unresolved, so
live-out becomes the full set there. Reported items are a floor, not guesses.

Reusable: point it at any project's asm. Extend by adding a detector that
consumes the shared CFG + liveness (see ``analyze`` / ``find_overruns``).

Usage:
  static_analysis.py ASM_FILE [--doc-out PATH] [--title TITLE]
                     [--json PATH] [--print]
"""
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile

LABEL_RE = re.compile(r'^([A-Za-z_][A-Za-z0-9_]*)\s*:')


def is_label_record(r):
    """True if a listing record is a label definition. The listing emits every
    label -- global (`Foo:`), local (`@@foo:`), or anonymous (`-`/`+`) -- as its
    own record with the (scope-qualified) name in ``directive_or_opcode``, a null
    ``addressing_mode``, and empty ``bytes_hex``. Directives (`.ORG`, `.DB`) start
    with `.` or carry bytes; EQUs emit no record. An instruction with no label
    record in front of it is reachable only by fall-through."""
    op = r.get('directive_or_opcode')
    return (r.get('addressing_mode') is None and not r.get('bytes_hex')
            and bool(op) and not op.startswith('.'))

A, X, Y, Z, N, C, V = (1 << i for i in range(7))
ALL = A | X | Y | Z | N | C | V
NZ = Z | N
HW = {0x2002, 0x2007, 0x4015, 0x4016, 0x4017}  # reads with side effects

A_PRODUCERS = {'LDA', 'TXA', 'TYA', 'PLA', 'AND', 'ORA', 'EOR', 'ADC', 'SBC'}
X_PRODUCERS = {'LDX', 'TAX', 'TSX', 'INX', 'DEX'}
Y_PRODUCERS = {'LDY', 'TAY', 'INY', 'DEY'}
BRANCHES = {'BEQ', 'BNE', 'BMI', 'BPL', 'BCC', 'BCS', 'BVC', 'BVS'}
TERM = {'RTS', 'RTI', 'BRK'}
NZ_BRANCH = {'BEQ', 'BNE', 'BPL', 'BMI'}
DEAD_CANDIDATES = {
    'LDA', 'LDX', 'LDY', 'TAX', 'TAY', 'TXA', 'TYA', 'TSX',
    'INX', 'DEX', 'INY', 'DEY', 'ADC', 'SBC', 'AND', 'ORA', 'EOR',
    'CMP', 'CPX', 'CPY', 'BIT', 'ASL', 'LSR', 'ROL', 'ROR', 'CLC', 'SEC', 'CLV',
}
CARRY_CONSUMERS = {'BCC', 'BCS', 'ROL', 'ROR', 'ADC', 'SBC'}  # read the carry flag
LOAD_REG = {'LDA': 'A', 'LDX': 'X', 'LDY': 'Y'}
STORE_REG = {'STA': 'A', 'STX': 'X', 'STY': 'Y'}


def sem(op, mode):
    """(uses, defs, side_effect) bitmasks for one instruction (register file)."""
    u = d = 0
    if mode in ('absolute_x', 'zeropage_x'):
        u |= X
    elif mode == 'absolute_y':
        u |= Y
    elif mode == 'postindexed_indirect':
        u |= Y
    elif mode == 'preindexed_indirect':
        u |= X
    se = False
    if op == 'LDA':
        d |= A | NZ
    elif op == 'LDX':
        d |= X | NZ
    elif op == 'LDY':
        d |= Y | NZ
    elif op == 'STA':
        u |= A; se = True
    elif op == 'STX':
        u |= X; se = True
    elif op == 'STY':
        u |= Y; se = True
    elif op == 'TAX':
        u |= A; d |= X | NZ
    elif op == 'TAY':
        u |= A; d |= Y | NZ
    elif op == 'TXA':
        u |= X; d |= A | NZ
    elif op == 'TYA':
        u |= Y; d |= A | NZ
    elif op == 'TSX':
        d |= X | NZ
    elif op == 'TXS':
        u |= X
    elif op == 'INX':
        u |= X; d |= X | NZ
    elif op == 'DEX':
        u |= X; d |= X | NZ
    elif op == 'INY':
        u |= Y; d |= Y | NZ
    elif op == 'DEY':
        u |= Y; d |= Y | NZ
    elif op in ('ADC', 'SBC'):
        u |= A | C; d |= A | C | V | NZ
    elif op in ('AND', 'ORA', 'EOR'):
        u |= A; d |= A | NZ
    elif op == 'CMP':
        u |= A; d |= C | NZ
    elif op == 'CPX':
        u |= X; d |= C | NZ
    elif op == 'CPY':
        u |= Y; d |= C | NZ
    elif op == 'BIT':
        u |= A; d |= V | NZ
    elif op in ('INC', 'DEC'):
        d |= NZ; se = True
    elif op in ('ASL', 'LSR', 'ROL', 'ROR'):
        if mode == 'implied':  # accumulator
            u |= A; d |= A | C | NZ
            if op in ('ROL', 'ROR'):
                u |= C
        else:
            se = True
            if op in ('ROL', 'ROR'):
                u |= C
    elif op == 'PHA':
        u |= A; se = True
    elif op == 'PLA':
        d |= A | NZ; se = True
    elif op == 'PHP':
        u |= Z | N | C | V; se = True
    elif op == 'PLP':
        d |= Z | N | C | V; se = True
    elif op in ('CLC', 'SEC'):
        d |= C
    elif op == 'CLV':
        d |= V
    elif op in ('CLD', 'SED', 'CLI', 'SEI', 'NOP'):
        pass
    elif op in ('BEQ', 'BNE'):
        u |= Z
    elif op in ('BMI', 'BPL'):
        u |= N
    elif op in ('BCC', 'BCS'):
        u |= C
    elif op in ('BVC', 'BVS'):
        u |= V
    elif op in ('JSR', 'RTS', 'RTI'):
        u |= ALL
    elif op == 'BRK':
        u |= ALL; se = True
    elif op == 'JMP':
        pass
    return u, d, se


def run_xasm_listing(asm_file):
    with tempfile.TemporaryDirectory() as tmp:
        listing = os.path.join(tmp, 'listing.json')
        xasm = os.environ.get('XASM_BIN', 'xasm')
        cmd = [xasm, '--pure-binary', '-o', os.path.join(tmp, 'out.bin'),
               '--listing=' + listing, '--listing-format=json', asm_file]
        try:
            subprocess.run(cmd, check=True, stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, text=True)
        except FileNotFoundError:
            sys.exit('error: xasm not found on PATH')
        except subprocess.CalledProcessError as exc:
            sys.stderr.write(exc.stderr or '')
            sys.exit(f'error: xasm failed ({exc.returncode}) on {asm_file}')
        with open(listing, encoding='utf-8') as f:
            return json.load(f)['records']


class Program:
    """Instruction stream + CFG + liveness over one assembled listing."""

    def __init__(self, records):
        ins = []
        cur_routine, cur_rstart, pending = None, 0, True
        label_before = True  # something can enter here (routine/file start)
        for r in records:
            src = (r.get('source_text') or '').strip()
            m = LABEL_RE.match(src)
            if m:
                cur_routine = m.group(1)  # nearest global label = routine entry
                pending = True
            if is_label_record(r):
                label_before = True
            if r.get('addressing_mode') is None:
                continue
            b = [int(x, 16) for x in r.get('bytes_hex') or []]
            if not b:
                continue
            if pending:
                cur_rstart = len(ins)
                pending = False
            ins.append({
                'line': r['line'], 'op': (r['directive_or_opcode'] or '').upper(),
                'mode': r['addressing_mode'], 'off': r['output_offset_start'],
                'nbytes': len(b), 'bytes': b, 'src': src,
                'routine': cur_routine, 'rstart': cur_rstart,
                # A labeled instruction may be a branch/JMP/JSR target whose
                # incoming edges the CFG cannot fully resolve (absolute JMP/JSR
                # are left unresolved), so it is not a sole fall-through entry.
                'labeled': label_before,
            })
            label_before = False
        self.ins = ins
        off_idx = {t['off']: i for i, t in enumerate(ins) if t['off'] is not None}

        def rel_target(t):
            if t['mode'] != 'relative' or t['off'] is None:
                return None
            off = t['bytes'][-1]
            off = off - 256 if off >= 128 else off
            return off_idx.get(t['off'] + t['nbytes'] + off)

        succ = []
        for i, t in enumerate(ins):
            op = t['op']
            s, unresolved = [], False
            nxt = i + 1 if i + 1 < len(ins) else None
            contig = (nxt is not None and t['off'] is not None
                      and ins[nxt]['off'] is not None
                      and ins[nxt]['off'] == t['off'] + t['nbytes'])
            if op in TERM:
                pass
            elif op == 'JMP':
                unresolved = True  # absolute bank not statically known
            elif op in BRANCHES:
                if contig:
                    s.append(nxt)
                else:
                    unresolved = True
                tg = rel_target(t)
                if tg is None:
                    unresolved = True
                else:
                    s.append(tg)
            else:  # JSR + straight-line
                if contig:
                    s.append(nxt)
                else:
                    unresolved = True
            succ.append((s, unresolved))
        self.succ = succ

        preds = [[] for _ in ins]
        for i, (s, _) in enumerate(succ):
            for j in s:
                preds[j].append(i)
        self.preds = preds

        U, D, SE = [0] * len(ins), [0] * len(ins), [False] * len(ins)
        for i, t in enumerate(ins):
            u, d, se = sem(t['op'], t['mode'])
            if t['op'] in ('LDA', 'LDX', 'LDY', 'BIT'):
                addr = None
                if t['mode'] in ('absolute', 'absolute_x', 'absolute_y') and t['nbytes'] >= 3:
                    addr = t['bytes'][1] | (t['bytes'][2] << 8)
                elif t['mode'] in ('zeropage', 'zeropage_x') and t['nbytes'] >= 2:
                    addr = t['bytes'][1]
                if addr in HW:
                    se = True
            U[i], D[i], SE[i] = u, d, se
        self.U, self.D, self.SE = U, D, SE

        live_in = [0] * len(ins)
        changed = True
        while changed:
            changed = False
            for i in range(len(ins) - 1, -1, -1):
                s, unresolved = succ[i]
                lo = ALL if unresolved else 0
                for j in s:
                    lo |= live_in[j]
                li = U[i] | (lo & ~D[i])
                if li != live_in[i]:
                    live_in[i] = li
                    changed = True
        self.live_in = live_in

    def live_out(self, i):
        s, unresolved = self.succ[i]
        lo = ALL if unresolved else 0
        for j in s:
            lo |= self.live_in[j]
        return lo

    def sole_fall_pred(self, i):
        """The instruction i falls through from, iff that is i's only predecessor
        and it is ROM-contiguous (so i's flags/regs come solely from it)."""
        if i == 0 or self.preds[i] != [i - 1]:
            return None
        p = self.ins[i - 1]
        if p['off'] is None or p['off'] + p['nbytes'] != self.ins[i]['off']:
            return None
        return i - 1

    def imm(self, t):
        return t['bytes'][1] if t['mode'] == 'immediate' and t['nbytes'] >= 2 else None

    def operand_addr(self, t):
        """Resolved absolute/zeropage operand address, or None."""
        if t['mode'] in ('absolute', 'absolute_x', 'absolute_y') and t['nbytes'] >= 3:
            return t['bytes'][1] | (t['bytes'][2] << 8)
        if t['mode'] in ('zeropage', 'zeropage_x') and t['nbytes'] >= 2:
            return t['bytes'][1]
        return None


def caller_index_setup(prog, routine, reg):
    """Among direct `JSR <routine>` callers, how many establish index `reg` (via
    LDX/TAX/TSX or LDY/TAY) in the straight-line block just before the call.
    Returns (n_callers, n_setting). This separates a confirmed wrong-register bug
    from an input-register contract the caller satisfies -- proving the index is
    uninitialised *inside* a routine does not prove it is uninitialised at the
    call site."""
    setters = {'LDX', 'TAX', 'TSX'} if reg == 'X' else {'LDY', 'TAY'}
    ins = prog.ins
    n = nset = 0
    for j, t in enumerate(ins):
        if t['op'] != 'JSR':
            continue
        parts = t['src'].split()
        if len(parts) < 2 or parts[1] != routine:
            continue
        n += 1
        k, steps = j - 1, 0
        while k >= 0 and steps < 8:
            p = ins[k]
            if p['op'] in setters:
                nset += 1
                break
            if p['op'] in ('JMP', 'RTS', 'RTI') or prog.preds[k + 1] != [k]:
                break  # left the caller's straight-line block
            k, steps = k - 1, steps + 1
    return n, nset


def find_overruns(prog):
    """Correctness: an index register used by a tight fixed-count copy/fill loop
    (`ST_ base,R` + `IN R` + `CP R #const` + backward branch) that is never
    written in the routine before the loop -- so R is live-in and inherits the
    caller's value, wrapping/overrunning when it is not the expected base.

    Routines that initialise R locally, or that `JSR` a helper before the loop
    (which may set R), are excluded. A wrong-register init (e.g. `LDX` where
    `LDY` was meant) is reported as a typo signal."""
    ins = prog.ins
    found, seen = [], set()
    for i, t in enumerate(ins):
        if t['op'] not in ('BNE', 'BCC', 'BCS'):
            continue
        back = [j for j in prog.succ[i][0] if j != i + 1 and j < i]
        if len(back) != 1:
            continue
        ls = back[0]
        body = ins[ls:i + 1]
        if len(body) > 9 or i == 0:
            continue
        cmp_ins = ins[i - 1]
        if cmp_ins['op'] not in ('CPX', 'CPY') or cmp_ins['mode'] != 'immediate':
            continue
        reg = 'X' if cmp_ins['op'] == 'CPX' else 'Y'
        inc = 'INX' if reg == 'X' else 'INY'
        idxmode = ('absolute_x', 'zeropage_x') if reg == 'X' else ('absolute_y',)
        if not any(b['op'] == inc for b in body):
            continue
        store = next((b for b in body if b['op'] in ('STA', 'STX', 'STY')
                      and b['mode'] in idxmode), None)
        if store is None:
            continue
        rstart = ins[ls]['rstart']
        pre = ins[rstart:ls]
        writes = ({'LDX', 'TAX', 'TSX', 'INX', 'DEX'} if reg == 'X'
                  else {'LDY', 'TAY', 'INY', 'DEY'})
        if any(p['op'] in writes or p['op'] == 'JSR' for p in pre):
            continue
        routine = ins[rstart]['routine']
        if routine in seen:
            continue
        seen.add(routine)
        other = ({'LDY', 'TAY'} if reg == 'X' else {'LDX', 'TAX'})
        typo = next((p['src'] for p in pre if p['op'] in other), None)
        n_call, n_set = caller_index_setup(prog, routine, reg)
        found.append({'line': ins[rstart]['line'], 'routine': routine, 'reg': reg,
                      'bound': cmp_ins['src'], 'store': store['src'], 'typo': typo,
                      'confidence': 'high' if typo else 'review',
                      'n_callers': n_call, 'n_callers_set': n_set,
                      'annotated': has_inline_comment(store['src'], cmp_ins['src'], typo)})
    return found


def carry_discarded_by_shift(prog, i):
    """If the carry set at instruction i is discarded (unused) by a following
    accumulator `ASL`/`LSR` -- a sign the shift was meant to be `ROL`/`ROR` to fold
    the carry into bit 0 -- return that shift record, else None. Stops at a carry
    consumer (the carry is really used), another carry redefine, or a block edge."""
    ins = prog.ins
    j = i + 1
    steps = 0
    while j < len(ins) and steps < 5:
        t = ins[j]
        if (t['labeled'] or ins[j - 1]['off'] is None or t['off'] is None
                or t['off'] != ins[j - 1]['off'] + ins[j - 1]['nbytes']):
            return None  # not a clean fall-through chain
        op = t['op']
        if op in ('ASL', 'LSR') and t['mode'] == 'implied':
            return t  # accumulator shift discards the carry it was handed
        if op in CARRY_CONSUMERS:
            return None  # carry is genuinely used -- no confusion
        if op in ('CLC', 'SEC', 'CMP', 'CPX', 'CPY', 'PLP'):
            return None  # carry redefined by something other than the shift
        if op in BRANCHES or op in ('JMP', 'JSR', 'RTS', 'RTI', 'BRK'):
            return None  # left the straight-line block
        j += 1
        steps += 1
    return None


def reload_producer_jsr(prog, sta_i):
    """Scan back from the store on its sole fall-through chain. If a `JSR` supplies
    the stored A before any local A-producer does, dropping the reload depends on
    that subroutine returning with N/Z set on A -- a *non-local* contract, not a
    local property. Returns the subroutine's name, else None."""
    a_local = {'LDA', 'TXA', 'TYA', 'PLA', 'AND', 'ORA', 'EOR', 'ADC', 'SBC'}
    ins = prog.ins
    j, steps = sta_i - 1, 0
    while j >= 0 and steps < 6:
        t, nxt = ins[j], ins[j + 1]
        if (t['off'] is None or nxt['off'] is None
                or nxt['off'] != t['off'] + t['nbytes']):
            return None  # t does not fall through to its successor
        op = t['op']
        if op == 'JSR':
            parts = t['src'].split()
            return parts[1] if len(parts) > 1 else 'a subroutine'
        if op in a_local or (op in ('ASL', 'LSR', 'ROL', 'ROR') and t['mode'] == 'implied'):
            return None  # a local instruction set A -> local optimization
        # A branch target that is itself the producer (JSR / local load) is handled
        # above; but to keep walking *past* t we need t to have a single entry.
        if t['labeled']:
            return None
        j -= 1
        steps += 1
    return None


def has_inline_comment(*srcs):
    """A finding counts as *already annotated* when any instruction source line it
    displays carries an inline comment (`;`) -- i.e. someone has already documented
    the redundancy/bug/trade-off at the site. Un-annotated findings are the ones a
    source-annotation sweep still has to reach."""
    return any(';' in (s or '') for s in srcs)


def analyze(prog):
    ins = prog.ins
    out = {k: [] for k in
           ('bugs', 'wrongreg', 'carryshift', 'dead', 'bit7', 'cmp0', 'xfer',
            'reload', 'excluded')}
    out['bugs'] = find_overruns(prog)
    for i, t in enumerate(ins):
        op, mode = t['op'], t['mode']

        # dead instruction: every defined output dead on exit, no side effect
        if op in DEAD_CANDIDATES and not prog.SE[i] and prog.D[i]:
            if prog.D[i] & prog.live_out(i) == 0:
                # A dead `LDX/LDY #imm` immediately before a `STA` is the
                # fingerprint of a wrong-register typo: `LDA #imm` was likely
                # meant, so the store writes the *stale* A instead of #imm.
                # Promote it from a dead instruction to a correctness finding.
                nxt = ins[i + 1] if i + 1 < len(ins) else None
                shift = (carry_discarded_by_shift(prog, i)
                         if op in ('CLC', 'SEC', 'CMP', 'CPX', 'CPY') else None)
                if (op in LOAD_REG and mode == 'immediate' and nxt
                        and nxt['op'] in STORE_REG
                        and nxt['off'] == t['off'] + t['nbytes']
                        and LOAD_REG[op] != STORE_REG[nxt['op']]):
                    r1, r2 = LOAD_REG[op], STORE_REG[nxt['op']]
                    imm = t['src'].split(None, 1)[1]
                    operand = (nxt['src'].split(None, 1) + [''])[1]
                    out['wrongreg'].append({
                        'line': t['line'], 'dead': t['src'], 'store': nxt['src'],
                        'r1': r1, 'r2': r2, 'fix_load': f'LD{r2} {imm}',
                        'fix_store': f'ST{r1} {operand}'.rstrip(),
                        'annotated': has_inline_comment(t['src'], nxt['src'])})
                elif shift is not None:
                    # The dead carry-setter feeds an accumulator ASL/LSR that
                    # discards the carry: the author likely thought the shift folds
                    # carry into bit 0 (that is ROL/ROR). Promote out of "dead".
                    out['carryshift'].append({
                        'line': t['line'], 'setter': t['src'], 'shift': shift['src'],
                        'intended': {'ASL': 'ROL', 'LSR': 'ROR'}[shift['op']],
                        # ASL/ROL vacate bit 0; LSR/ROR vacate bit 7.
                        'bit': '0' if shift['op'] == 'ASL' else '7',
                        'annotated': has_inline_comment(t['src'], shift['src'])})
                else:
                    out['dead'].append({'i': i, 'line': t['line'], 'op': op,
                                        'mode': mode, 'src': t['src'],
                                        'annotated': has_inline_comment(t['src'])})

        # bit-7 test: producer ; AND #$80 ; BNE/BEQ  -> BMI/BPL
        if op == 'AND' and prog.imm(t) == 0x80:
            p = prog.sole_fall_pred(i)
            br = ins[i + 1] if i + 1 < len(ins) else None
            if (p is not None and ins[p]['op'] in A_PRODUCERS
                    and br and br['op'] in ('BNE', 'BEQ') and prog.preds[i + 1] == [i]):
                rewrite = 'BMI' if br['op'] == 'BNE' else 'BPL'
                # The rewrite drops the AND, so it changes both A (masked vs whole
                # byte) and Z (bit 7 vs whole byte); N is unchanged. It is safe
                # only when neither A nor Z is live after the branch.
                unsafe = bool(prog.live_out(i + 1) & (A | Z))
                # Bit 7 of a hardware register is fixed by the hardware (e.g.
                # PPUSTATUS bit 7 = vblank), so the layout-coupling caveat does not
                # apply and the vblank-wait form is idiomatic.
                prod_addr = prog.operand_addr(ins[p])
                rec = {'line': t['line'], 'pred': ins[p]['src'], 'mask': t['src'],
                       'branch': br['src'], 'rewrite': rewrite, 'kind': 'bit-7 mask',
                       'hw': prod_addr in HW, 'ppustatus': prod_addr == 0x2002,
                       'annotated': has_inline_comment(ins[p]['src'], t['src'], br['src'])}
                out['excluded' if unsafe else 'bit7'].append(rec)

        # redundant compare-to-zero: producer ; CMP/CPX/CPY #$00 ; Z/N-branch
        if op in ('CMP', 'CPX', 'CPY') and prog.imm(t) == 0:
            p = prog.sole_fall_pred(i)
            br = ins[i + 1] if i + 1 < len(ins) else None
            if p is not None and br and br['op'] in NZ_BRANCH and prog.preds[i + 1] == [i]:
                pop = ins[p]['op']
                ok = ((op == 'CMP' and pop in A_PRODUCERS and not prog.SE[p]) or
                      (op == 'CPX' and pop in X_PRODUCERS) or
                      (op == 'CPY' and pop in Y_PRODUCERS))
                if ok and (prog.live_out(i) & C) == 0:
                    # A literal `#$00`/`#0` is a clean drop; a named zero-valued
                    # sentinel is a trade-off (only redundant while it == 0, and the
                    # name documents what the branch tests).
                    operand = t['src'].split('#', 1)[-1].split(';')[0].strip()
                    named = not re.match(r'^\$?0+$', operand)
                    out['cmp0'].append({'line': t['line'], 'op': op,
                                        'pred': ins[p]['src'], 'cmp': t['src'],
                                        'branch': br['src'], 'named': named,
                                        'annotated': has_inline_comment(
                                            ins[p]['src'], t['src'], br['src'])})

        # transfer before compare: TXA/TYA ; CMP #imm ; branch  -> CPX/CPY
        if op in ('TXA', 'TYA'):
            c = ins[i + 1] if i + 1 < len(ins) else None
            br = ins[i + 2] if i + 2 < len(ins) else None
            if (c and c['op'] == 'CMP' and c['mode'] == 'immediate'
                    and br and br['op'] in BRANCHES
                    and prog.preds[i + 1] == [i] and prog.preds[i + 2] == [i + 1]):
                reg = 'X' if op == 'TXA' else 'Y'
                a_live = bool(prog.live_out(i + 1) & A)
                rec = {'line': t['line'], 'xfer': t['src'], 'cmp': c['src'],
                       'branch': br['src'], 'kind': 'transfer',
                       'rewrite': f"CP{reg} {c['src'].split(None, 1)[-1]}",
                       'annotated': has_inline_comment(t['src'], c['src'], br['src'])}
                out['excluded' if a_live else 'xfer'].append(rec)

        # redundant reload: ST_ x ; LD_ x (same location), contiguous. Both the
        # store *and* the reload must be *unlabeled*, so the pair has a single
        # fall-through entry. If either is a branch/JMP/JSR target, an incoming
        # flow may reach it with different A (a labeled LD_) or with N/Z set by
        # some other instruction (a labeled ST_, e.g. reached by `BNE`/`BCS`) --
        # then the reload's LD_ is needed to refresh the flags and is not
        # redundant. (Absolute JMP edges are not in the CFG, hence the label test.)
        pair = {'STA': 'LDA', 'STX': 'LDX', 'STY': 'LDY'}
        if op in pair:
            n = ins[i + 1] if i + 1 < len(ins) else None
            if (n and n['op'] == pair[op] and n['mode'] == mode
                    and n['bytes'][1:] == t['bytes'][1:]
                    and prog.preds[i + 1] == [i]
                    and not t['labeled'] and not n['labeled']):
                out['reload'].append({'line': t['line'], 'store': t['src'],
                                      'reload': n['src'],
                                      'jsr': reload_producer_jsr(prog, i),
                                      'annotated': has_inline_comment(t['src'], n['src'])})
    return out


HEADER = """# Static Analysis -- {title}

> Generated by `scripts/static_analysis.py` from xasm's assembled JSON listing
> (commit `{commit}`, {date}). Instruction identity, addressing mode, and operand
> values are the *assembled* truth; every finding is verified by register+flag
> liveness over a control-flow graph. Line numbers are a snapshot and drift as
> passes land.
>
> **Category A** flags correctness/overrun risks (a confirmed wrong-register bug
> vs call-site review candidates); **B--D** are **mod-only**: the canonical
> disassembly must reassemble byte-for-byte, so those rewrites may not be applied
> to `{asm}` -- they are for an article on hand-written-6502 code and for future
> *relocatable mod* builds. Method, confidence rules, and the excluded
> false-positive classes are documented once in
> `agent_playbook/TOOLING.md` (Static-Analysis Scanner), not repeated here.

## Summary

| # | Category | Count | Note |
|---|----------|-------|------|
| A | Correctness / latent bugs | {bugs} | confirmed (typo) vs call-contract review |
| B | Dead instructions | {dead} | mod-only; -1..3 bytes each |
| C | Micro-optimizations (bit-7 / compare-0 / transfer) | {micro} | mod-only; bit-7 is a readability/layout trade-off |
| D | Redundant reload after store | {reload} | mod-only; lower confidence |
"""

def fence(*lines):
    body = '\n'.join('  ' + s for s in lines)
    return "  ```\n" + body + "\n  ```"


def annot(r):
    """Marker appended to an already-annotated finding, so the un-marked findings
    are the source-annotation worklist."""
    return ' *(already annotated in source)*' if r.get('annotated') else ''


def emit(out, title, asm, commit, date):
    bugs, wrongreg, carryshift = out['bugs'], out['wrongreg'], out['carryshift']
    dead, reload_ = out['dead'], out['reload']
    micro = len(out['bit7']) + len(out['cmp0']) + len(out['xfer'])
    doc = HEADER.format(title=title, asm=asm, commit=commit, date=date,
                        bugs=len(bugs) + len(wrongreg) + len(carryshift),
                        dead=len(dead), micro=micro, reload=len(reload_))
    total = (len(bugs) + len(wrongreg) + len(carryshift) + len(dead) + micro
             + len(reload_))
    if total == 0:
        doc += ("\nNo correctness, dead-instruction, optimization, or redundancy "
                "findings under the patterns scanned. The hand-written code here is "
                "already tight.\n")

    # Source-annotation status: a finding is "annotated" when its site already
    # carries an inline comment. The un-annotated set is the sweep worklist; it is
    # the actionable list, so it leads the report.
    all_findings = ([('A', r) for r in bugs + wrongreg + carryshift]
                    + [('B', r) for r in dead]
                    + [('C', r) for r in out['bit7'] + out['cmp0'] + out['xfer']]
                    + [('D', r) for r in reload_])
    todo = [(c, r) for c, r in all_findings if not r.get('annotated')]
    if all_findings:
        done = len(all_findings) - len(todo)
        doc += ("\n## Source-annotation status\n\n"
                f"**{len(todo)} of {len(all_findings)} findings are not yet annotated "
                f"in the source** ({done} already carry an inline comment). Findings "
                "already annotated are marked *(already annotated in source)* below; "
                "the rest are the annotation worklist:\n\n")
        by_cat = {}
        for c, r in todo:
            by_cat.setdefault(c, []).append(r['line'])
        for c in ('A', 'B', 'C', 'D'):
            if by_cat.get(c):
                nums = ', '.join(f"L{n}" for n in sorted(by_cat[c]))
                doc += f"- **{c}:** {nums}\n"
        if not todo:
            doc += "- every finding is already annotated in the source.\n"
        doc += "\n"

    confirmed = [r for r in bugs if r.get('confidence') == 'high']
    review = [r for r in bugs if r.get('confidence') != 'high']
    doc += "\n## A. Correctness / latent bugs\n\n"
    if not bugs and not wrongreg and not carryshift:
        doc += "None detected.\n"
    if carryshift:
        doc += ("### Suspected shift/carry confusion\n\n"
                "A dead carry-setter (`CLC`/`SEC`/`CMP`) is discarded by a following "
                "accumulator `ASL`/`LSR`, which shifts a **0** into the vacated bit "
                "(bit 0 for `ASL`, bit 7 for `LSR`) -- it does *not* fold the carry "
                "in. This is the fingerprint of thinking the shift is `ROL`/`ROR`: "
                "harmless where the carry was never needed, but a real bug where it "
                "was (the carry-dependent path is dead).\n\n")
        for r in carryshift:
            doc += (f"- **L{r['line']}**{annot(r)} -- `{r['setter']}` sets carry that "
                    f"`{r['shift']}` discards; if the shift was meant to fold carry "
                    f"into bit {r['bit']} it should be `{r['intended']}`.\n\n")
    if wrongreg:
        doc += ("### Suspected wrong-register load/store\n\n"
                "A dead immediate load `LD? #imm` sits immediately before a store "
                "`ST?` that reads a **different register** -- the fingerprint of a "
                "register mismatch: the immediate lands in one register but the store "
                "writes another, so `#imm` is discarded and a stale register is "
                "stored. Verify intent (if storing the current register is deliberate, "
                "the dead load is merely cruft).\n\n")
        for r in wrongreg:
            doc += (f"- **L{r['line']}**{annot(r)} -- `{r['dead']}` is dead and precedes "
                    f"`{r['store']}`; the immediate goes into **{r['r1']}** but the "
                    f"store reads **{r['r2']}**, so it writes a stale {r['r2']} -- "
                    f"likely `{r['fix_load']}` or `{r['fix_store']}` was meant.\n\n")
    if bugs:
        doc += ("**Uninitialised-index overrun.** An index register is read by a "
                "fixed-count copy/fill loop before the routine ever writes it. The "
                "scan proves only that the index is unset *inside* the routine; "
                "whether that is a bug depends on the callers, so findings are split "
                "by confidence.\n\n")
    if confirmed:
        doc += ("### Confirmed (wrong-register init)\n\n"
                "The routine initialises the *other* index register -- a typo -- so "
                "this index is left unset regardless of the caller: a real defect in "
                "the shipped ROM (its fix, like any change, is mod-only against the "
                "parity-exact source).\n\n")
        for r in confirmed:
            doc += (f"- **L{r['line']} `{r['routine']}`**{annot(r)} -- index **{r['reg']}** is "
                    f"never initialised (the routine's `{r['typo']}` sets the other "
                    f"register) but drives `{r['store']}` (loop bound `{r['bound']}`).\n\n")
    if review:
        doc += ("### Call-contract review candidates\n\n"
                "The index is read as an **input register**; the routine does not set "
                "it and there is no wrong-register typo, so it is a defect only if a "
                "caller fails to establish a valid base. Verify the call sites -- "
                "**not asserted as a bug**.\n\n")
        for r in review:
            nc, ns = r.get('n_callers', 0), r.get('n_callers_set', 0)
            if nc == 0:
                cc = "no direct `JSR` caller found -- check every entry path"
            elif ns == nc:
                cc = (f"all {nc} direct caller(s) set **{r['reg']}** first (an input "
                      f"contract; verify the value stays within the bound)")
            else:
                cc = (f"{nc} direct caller(s), only {ns} set **{r['reg']}** first -- "
                      f"the rest may overrun")
            doc += (f"- **L{r['line']} `{r['routine']}`**{annot(r)} -- index **{r['reg']}** "
                    f"drives `{r['store']}` (loop bound `{r['bound']}`); {cc}.\n\n")

    if dead:
        doc += "\n## B. Dead instructions\n\n"
        doc += ("Every register/flag the instruction defines is overwritten before "
                "use on every path, and it has no side effect.\n\n")
        for r in dead:
            doc += f"- **L{r['line']}** `{r['op']}`{annot(r)}:\n\n"
            doc += fence(r['src']) + "\n"

    if micro:
        doc += "\n## C. Micro-optimizations\n\n"
        if out['bit7']:
            hw = [r for r in out['bit7'] if r.get('hw')]
            sw = [r for r in out['bit7'] if not r.get('hw')]
            doc += ("### Bit-7 test via `AND #$80` (-> `BMI`/`BPL`)\n\n"
                    "The producing load already sets **N** from bit 7, so the "
                    "`AND #$80` + `BNE`/`BEQ` collapses to one `BMI`/`BPL` (-2 bytes, "
                    "-2 cycles). Whether that is a clean win or a trade-off depends on "
                    "what supplies bit 7.\n\n")
            if hw:
                doc += ("**Hardware register (idiomatic, clean win).** Bit 7 of a "
                        "hardware register is fixed by the hardware and cannot be "
                        "repurposed (`PPUSTATUS` bit 7 = vblank), so there is no layout "
                        "risk and `LDA PPUSTATUS / BPL` is the canonical vblank wait -- "
                        "drop the `AND`; no comment needed.\n\n")
                for r in hw:
                    doc += f"- **L{r['line']}**{annot(r)} -> drop `AND`, use `{r['rewrite']}`:\n\n"
                    doc += fence(r['pred'], r['mask'], r['branch']) + "\n"
            if sw:
                doc += ("\n**Software flag (trade-off).** For a RAM/software flag the "
                        "bit position is a project choice: `BMI`/`BPL` hard-codes bit 7 "
                        "(it breaks silently if the flag's layout moves) and drops the "
                        "named mask, so add a comment naming the bit -- which partly "
                        "offsets the 2-byte saving.\n\n")
                for r in sw:
                    doc += f"- **L{r['line']}**{annot(r)} -> drop `AND`, use `{r['rewrite']}` (add a comment naming the bit):\n\n"
                    doc += fence(r['pred'], r['mask'], r['branch']) + "\n"
        if out['cmp0']:
            lit = [r for r in out['cmp0'] if not r.get('named')]
            named = [r for r in out['cmp0'] if r.get('named')]
            doc += ("\n### Redundant compare-to-zero\n\n"
                    "The preceding load/logic already set **Z**/**N**, so a `#0` "
                    "compare is dead for the following branch.\n\n")
            if lit:
                doc += "A literal `#$00` compare -- a clean drop:\n\n"
                for r in lit:
                    doc += f"- **L{r['line']}**{annot(r)} -- drop `{r['op']}`:\n\n"
                    doc += fence(r['pred'], r['cmp'], r['branch']) + "\n"
            if named:
                doc += ("\nA **named** zero-valued sentinel -- a trade-off, like the "
                        "bit-7 case: the drop is valid only while the constant equals "
                        "`0`, and it removes the name that documents *what* the branch "
                        "tests, so the branch wants a comment naming the sentinel:\n\n")
                for r in named:
                    doc += (f"- **L{r['line']}**{annot(r)} -- drop `{r['op']}` (add a comment "
                            f"naming the sentinel):\n\n")
                    doc += fence(r['pred'], r['cmp'], r['branch']) + "\n"
        if out['xfer']:
            doc += ("\n### Register->A transfer before compare (-> `CPX`/`CPY`)\n\n"
                    "The `TXA`/`TYA` only feeds the compare; the register compare "
                    "does it directly and A is dead afterward on every path.\n\n")
            for r in out['xfer']:
                doc += f"- **L{r['line']}**{annot(r)} -> `{r['rewrite']}`, drop the transfer:\n\n"
                doc += fence(r['xfer'], r['cmp'], r['branch']) + "\n"

    if reload_:
        doc += "\n## D. Redundant reload after store (lower confidence)\n\n"
        doc += ("`ST_ x` then `LD_ x` at the same location -- A already holds the "
                "value; the reload only refreshes **N**/**Z**. Removable only if the "
                "value's producer already left the flags set on it. When that "
                "producer is a `JSR`, this depends on the subroutine's flag-return "
                "contract -- a **non-local** property, not a local optimization -- so "
                "verify the callee, not just the call site.\n\n")
        for r in reload_:
            note = ''
            if r.get('jsr'):
                note = (f" -- **non-local**: the value comes from `JSR {r['jsr']}`, so "
                        f"this is safe only if `{r['jsr']}` returns with N/Z set on A")
            doc += f"- **L{r['line']}**{annot(r)} -- reload{note}:\n\n"
            doc += fence(r['store'], r['reload']) + "\n"
    return doc


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('asm_file')
    ap.add_argument('--doc-out', help='write the markdown catalog here')
    ap.add_argument('--title', help='catalog title (default: asm basename)')
    ap.add_argument('--json', help='write raw findings JSON here')
    ap.add_argument('--commit', default='(working tree)')
    ap.add_argument('--date', default='')
    ap.add_argument('--print', action='store_true', dest='do_print')
    args = ap.parse_args()

    prog = Program(run_xasm_listing(args.asm_file))
    out = analyze(prog)
    counts = {k: len(v) for k, v in out.items()}

    if args.json:
        json.dump(out, open(args.json, 'w'), indent=1)
    if args.doc_out:
        title = args.title or os.path.splitext(os.path.basename(args.asm_file))[0]
        doc = emit(out, title, args.asm_file, args.commit, args.date)
        with open(args.doc_out, 'w', encoding='utf-8') as f:
            f.write(doc)
    if args.do_print or not (args.json or args.doc_out):
        order = ('bugs', 'wrongreg', 'carryshift', 'dead', 'bit7', 'cmp0', 'xfer', 'reload', 'excluded')
        print(f"{args.asm_file}: {len(prog.ins)} instrs  "
              + "  ".join(f"{k}={counts[k]}" for k in order))


if __name__ == '__main__':
    main()
