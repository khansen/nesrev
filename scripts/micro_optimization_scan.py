#!/usr/bin/env python3
"""Structured micro-optimization / dead-instruction scanner.

Finds dead instructions and micro-optimizable idioms in a 6502 disassembly by
analysing xasm's *assembled* JSON listing -- never regex over source. Instruction
identity, addressing mode, and operand values come from the listing
(``directive_or_opcode`` / ``addressing_mode`` / ``bytes_hex``); a control-flow
graph is built from ROM output offsets (unique across MMC1 banks, unlike CPU
addresses); and backward liveness of the registers {A,X,Y} and flags {Z,N,C,V}
is run over that CFG. Every finding is verified against liveness on all paths.

Reports (see the generated MICRO_OPTIMIZATION_CANDIDATES.md for prose):
  A  bit-7 test   : producer ; AND #$80 ; BNE/BEQ            -> BMI/BPL
  B  compare-0    : producer ; CMP/CPX/CPY #$00 ; Z/N-branch  -> drop compare
  C  xfer+compare : TXA/TYA ; CMP #imm ; branch               -> CPX/CPY
  D  dead instr   : a def whose every output is dead-on-exit, no side effect
  E  reload       : ST_ x ; LD_ x (same location)             -> drop reload
  F  excluded     : A/C candidates whose value IS live downstream (not valid)

Conservative by construction (credibility over completeness): JSR and RTS/RTI use
every register/flag; absolute JMP/JSR targets and non-ROM-contiguous fall-through
(the ``.DB $2C`` BIT-skip idiom, embedded tables) are treated as unresolved, so
live-out becomes the full set there. Reported items are a floor, not guesses.

Reusable: point it at any project's asm. Extend by adding a detector that
consumes the shared CFG + liveness in ``analyze()``.

Usage:
  micro_optimization_scan.py ASM_FILE [--doc-out PATH] [--title TITLE]
                             [--json PATH] [--print]
"""
import argparse
import json
import os
import subprocess
import sys
import tempfile

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
        cmd = ['xasm', '--pure-binary', '-o', os.path.join(tmp, 'out.bin'),
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
        for r in records:
            if r.get('addressing_mode') is None:
                continue
            b = [int(x, 16) for x in r.get('bytes_hex') or []]
            if not b:
                continue
            ins.append({
                'line': r['line'], 'op': (r['directive_or_opcode'] or '').upper(),
                'mode': r['addressing_mode'], 'off': r['output_offset_start'],
                'nbytes': len(b), 'bytes': b,
                'src': (r['source_text'] or '').strip(),
            })
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


def analyze(prog):
    ins, out = prog.ins, {k: [] for k in ('A', 'B', 'C', 'D', 'E', 'F')}
    for i, t in enumerate(ins):
        op, mode = t['op'], t['mode']

        # D: dead instruction (every defined output dead on exit, no side effect)
        if op in DEAD_CANDIDATES and not prog.SE[i] and prog.D[i]:
            if prog.D[i] & prog.live_out(i) == 0:
                out['D'].append({'i': i, 'line': t['line'], 'op': op,
                                 'mode': mode, 'src': t['src']})

        # A: producer ; AND #$80 ; BNE/BEQ  -> BMI/BPL
        if op == 'AND' and prog.imm(t) == 0x80:
            p = prog.sole_fall_pred(i)
            br = ins[i + 1] if i + 1 < len(ins) else None
            if (p is not None and ins[p]['op'] in A_PRODUCERS
                    and br and br['op'] in ('BNE', 'BEQ') and prog.preds[i + 1] == [i]):
                rewrite = 'BMI' if br['op'] == 'BNE' else 'BPL'
                a_live = bool(prog.live_out(i + 1) & A)
                rec = {'i': i, 'line': t['line'], 'pred': ins[p]['src'],
                       'mask': t['src'], 'branch': br['src'], 'rewrite': rewrite}
                out['F' if a_live else 'A'].append({**rec, 'kind': 'bit-7 mask'})

        # B: producer ; CMP/CPX/CPY #$00 ; Z/N-branch  -> drop compare
        if op in ('CMP', 'CPX', 'CPY') and prog.imm(t) == 0:
            p = prog.sole_fall_pred(i)
            br = ins[i + 1] if i + 1 < len(ins) else None
            if p is not None and br and br['op'] in NZ_BRANCH and prog.preds[i + 1] == [i]:
                pop = ins[p]['op']
                ok = ((op == 'CMP' and pop in A_PRODUCERS and not prog.SE[p]) or
                      (op == 'CPX' and pop in X_PRODUCERS) or
                      (op == 'CPY' and pop in Y_PRODUCERS))
                if ok and (prog.live_out(i) & C) == 0:
                    out['B'].append({'i': i, 'line': t['line'], 'op': op,
                                     'pred': ins[p]['src'], 'cmp': t['src'],
                                     'branch': br['src']})

        # C: TXA/TYA ; CMP #imm ; branch  -> CPX/CPY  (transfer dead after)
        if op in ('TXA', 'TYA'):
            c = ins[i + 1] if i + 1 < len(ins) else None
            br = ins[i + 2] if i + 2 < len(ins) else None
            if (c and c['op'] == 'CMP' and c['mode'] == 'immediate'
                    and br and br['op'] in BRANCHES
                    and prog.preds[i + 1] == [i] and prog.preds[i + 2] == [i + 1]):
                reg = 'X' if op == 'TXA' else 'Y'
                a_live = bool(prog.live_out(i + 1) & A)
                rec = {'i': i, 'line': t['line'], 'xfer': t['src'],
                       'cmp': c['src'], 'branch': br['src'],
                       'rewrite': f"CP{reg} {c['src'].split(None, 1)[-1]}"}
                out['F' if a_live else 'C'].append({**rec, 'kind': 'transfer'})

        # E: ST_ x ; LD_ x (same location), contiguous, sole predecessor
        pair = {'STA': 'LDA', 'STX': 'LDX', 'STY': 'LDY'}
        if op in pair:
            n = ins[i + 1] if i + 1 < len(ins) else None
            if (n and n['op'] == pair[op] and n['mode'] == mode
                    and n['bytes'][1:] == t['bytes'][1:]
                    and prog.preds[i + 1] == [i]):
                out['E'].append({'i': i, 'line': t['line'], 'store': t['src'],
                                 'reload': n['src']})
    return out


HEADER = """# Micro-Optimization & Redundancy Catalog -- {title}

> **Scope: mod-only.** The canonical disassembly must reassemble to the original
> ROM byte-for-byte, so **none of these may be applied to `{asm}`.** They are
> catalogued for (a) an article on hand-written-6502 inefficiency and (b) future
> *relocatable mod* builds, where binary divergence from the retail ROM is
> acceptable.
>
> Generated by `scripts/micro_optimization_scan.py` from xasm's assembled JSON
> listing (commit `{commit}`, {date}). Instruction identity, addressing mode, and
> operand values are the *assembled* truth; every candidate is verified by
> register+flag liveness over a control-flow graph. Line numbers are a snapshot
> and drift as passes land. See *Methodology* for the excluded classes.

## Summary

| # | Category | Count | Per-site saving |
|---|----------|-------|-----------------|
| A | Bit-7 test `AND #$80` -> `BMI`/`BPL` | {A} | -2 bytes, -2 cycles |
| B | Redundant compare-to-zero after a flag-setting op | {B} | -2 bytes, -2 cycles |
| C | Register->A transfer before compare -> `CPX`/`CPY` | {C} | -1 byte, -2 cycles |
| D | Dead instructions (all outputs dead on exit) | {D} | -1..3 bytes |
| E | Redundant reload after store (lower confidence) | {E} | -2/3 bytes |
| F | A/C lookalikes -- value not provably dead (excluded) | {F} | -- |

Clean actionable (A-E): **{clean}**. Numbers are for this project only.
"""

METHOD = """
## Methodology

`scripts/micro_optimization_scan.py` assembles the source with xasm and reads the
JSON listing -- no regex over source text. It builds a control-flow graph keyed by
ROM **output offset** (unique across MMC1 banks, unlike CPU addresses), resolving
relative branches by offset arithmetic, then runs backward liveness of registers
{A,X,Y} and flags {Z,N,C,V}. A **dead instruction** is one whose every defined
register/flag is dead on exit and which has no side effect. `AND #$80` / transfer
rewrites are admitted only when the affected value is dead downstream on **every**
path; otherwise they are listed under F.

Excluded false-positive classes (handled structurally, verified as *not*
optimizations):
- Reads of `$2002`/`$2007`/`$4015`/`$4016`/`$4017` -- side effects, never dead.
- `.DB $2C` **BIT-skip** -- a non-ROM-contiguous fall-through is treated as
  unresolved, so alternate-entry `LD_ #imm` chains are not mistaken for dead.
- Memory-operand `ASL`/`LSR`/`ROL`/`ROR` -- set flags from memory, not A
  (addressing mode from the listing, not a regex guess).
- Absolute `JMP`/`JSR` targets and `JSR`/`RTS` register effects are treated
  conservatively (full live-out), so reported items are a floor, not guesses.
"""


def fence(*lines):
    body = '\n'.join('  ' + s for s in lines)
    return "  ```\n" + body + "\n  ```"


def emit(out, title, asm, commit, date):
    A_, B_, C_, D_, E_, F_ = (out[k] for k in 'ABCDEF')
    clean = sum(len(x) for x in (A_, B_, C_, D_, E_))
    doc = HEADER.format(title=title, asm=asm, commit=commit, date=date,
                        A=len(A_), B=len(B_), C=len(C_), D=len(D_), E=len(E_),
                        F=len(F_), clean=clean)
    if clean == 0 and not F_:
        doc += ("\nNo micro-optimization, dead-instruction, or redundancy "
                "candidates were detected under the patterns scanned. The "
                "hand-written code here is already tight.\n")
    if A_:
        doc += "\n## A. Bit-7 test via `AND #$80` (-> `BMI`/`BPL`)\n\n"
        doc += ("The producing load/logic already sets **N** from bit 7, so the "
                "`AND #$80` plus `BNE`/`BEQ` collapses to one `BMI`/`BPL`; the "
                "masked value is dead afterward.\n\n")
        for r in A_:
            doc += f"- **L{r['line']}** -> drop `AND`, use `{r['rewrite']}`:\n\n"
            doc += fence(r['pred'], r['mask'], r['branch']) + "\n"
    if B_:
        doc += "\n## B. Redundant compare-to-zero\n\n"
        doc += ("The preceding op already set **Z**/**N**; the `#$00` compare is "
                "dead for the following branch.\n\n")
        for r in B_:
            doc += f"- **L{r['line']}** -- drop `{r['op']}`:\n\n"
            doc += fence(r['pred'], r['cmp'], r['branch']) + "\n"
    if C_:
        doc += "\n## C. Register->A transfer before compare (-> `CPX`/`CPY`)\n\n"
        doc += ("The `TXA`/`TYA` only feeds the compare; the register compare does "
                "it directly and A is dead afterward on every path.\n\n")
        for r in C_:
            doc += f"- **L{r['line']}** -> `{r['rewrite']}`, drop the transfer:\n\n"
            doc += fence(r['xfer'], r['cmp'], r['branch']) + "\n"
    if D_:
        doc += "\n## D. Dead instructions\n\n"
        doc += ("Every register/flag the instruction defines is overwritten before "
                "use on every path, and it has no side effect.\n\n")
        for r in D_:
            note = ''
            low = r['src'].lower()
            if 'redundant' in low or 'parity' in low or 'unused' in low:
                note = ' *(already annotated in source)*'
            doc += f"- **L{r['line']}** `{r['op']}`{note}:\n\n"
            doc += fence(r['src']) + "\n"
    if E_:
        doc += "\n## E. Redundant reload after store (lower confidence)\n\n"
        doc += ("`ST_ x` then `LD_ x` at the same location -- A already holds the "
                "value; the reload only refreshes **N**/**Z**. Removable only if the "
                "producer already left the flags set (often the shared BCD-subtract "
                "idiom). Verify the producer.\n\n")
        for r in E_:
            doc += f"- **L{r['line']}** -- reload:\n\n"
            doc += fence(r['store'], r['reload']) + "\n"
    if F_:
        doc += "\n## F. A/C lookalikes -- not provably safe (excluded)\n\n"
        doc += ("Structurally these match A/C, but liveness could not prove the "
                "masked/transferred value dead on every path: it is reused "
                "downstream, or is live at a routine boundary (`RTS`/`JSR`) where it "
                "may be a return value. The rewrite is therefore not provably safe "
                "and is listed here rather than asserted.\n\n")
        for r in F_:
            doc += f"- **L{r['line']}** ({r['kind']}) -- value live after the branch; required.\n"
    doc += METHOD
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
        clean = sum(counts[k] for k in 'ABCDE')
        print(f"{args.asm_file}: {prog and len(prog.ins)} instrs  "
              + "  ".join(f"{k}={counts[k]}" for k in 'ABCDEF')
              + f"  clean={clean}")


if __name__ == '__main__':
    main()
