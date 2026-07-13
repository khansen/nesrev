#!/usr/bin/env python3
"""Flag pointer-table-named labels whose body is still raw .DB pointer bytes.

A label whose name asserts it is a table/list of pointers (``...PtrTable``,
``...PointerTable``, ``...Pointers``, ``...Ptrs``, ``...PtrList``,
``...PointerList``) should have a symbolic body: ``.DW <label>`` or
``.DB <label,>label``. A raw numeric ``.DB`` run under such a name is an
un-relocated embedded pointer table -- pointers baked in as literal lo/hi bytes,
which do not survive relocation and which the name already proves are pointers.

This is the name-vs-body check that the embedded-pointer *audit* cannot make:
that audit only confirms a run when the table is read by direct symbol-indexed
paired reads, so pointer tables reached through a copied .DW block + indirect
[ZP],Y reads are invisible to it. The label name needs no such consumer proof.

Precision guards (kept low-noise on real projects):
  - skip a body that already contains any symbolic entry (.DW, or .DB with </>);
    a leading .DB header in front of .DW entries is fine.
  - require at least two little-endian words that look like PRG addresses
    ($8000-$FFFF), so headers, sentinels, and misnamed non-pointer tables
    (e.g. packed data whose words are not code/data addresses) are not flagged.

Report mode prints one line per finding and the count, exiting 0. --strict exits
68 when any finding remains; project-verify uses it for opted-in projects.
"""
import re
import sys

NAME_RE = re.compile(r'(PtrTable|PointerTable|PtrTbl|PtrList|PointerList|Pointers|Ptrs)', re.I)
LABEL_RE = re.compile(r'^([A-Za-z_][A-Za-z0-9_]*):')
PRG_LO, PRG_HI = 0x8000, 0xFFFF
MIN_WORDS = 2
PRG_RATIO = 0.6


def _num(tok):
    tok = tok.strip()
    if re.fullmatch(r'\$[0-9A-Fa-f]+', tok):
        return int(tok[1:], 16)
    if re.fullmatch(r'%[01]+', tok):
        return int(tok[1:], 2)
    if re.fullmatch(r'\d+', tok):
        return int(tok)
    return None


def _body(lines, i):
    out = []
    for j in range(i + 1, len(lines)):
        s = lines[j].strip()
        if LABEL_RE.match(s):
            break
        if s and not s.startswith(';'):
            out.append(s)
        if len(out) > 64:
            break
    return out


def analyze(lines, i):
    body = _body(lines, i)
    if not body:
        return None
    has_symbolic = any(re.match(r'\.DW\b', s) or '<' in s or '>' in s for s in body)
    nums = []
    for s in body:
        m = re.match(r'\.DB\s+(.*)', s)
        if not m:
            continue
        for tok in m.group(1).split(';')[0].split(','):
            if tok.strip():
                nums.append(_num(tok))
    words = [nums[k] | (nums[k + 1] << 8)
             for k in range(0, len(nums) - 1, 2)
             if nums[k] is not None and nums[k + 1] is not None]
    prg = [w for w in words if PRG_LO <= w <= PRG_HI]
    flagged = (not has_symbolic and len(words) >= MIN_WORDS
               and len(prg) >= PRG_RATIO * len(words))
    return flagged, len(words), len(prg)


def main(argv):
    strict = '--strict' in argv
    paths = [a for a in argv if not a.startswith('-')]
    if len(paths) != 1:
        print('usage: pointer_table_body_check.py <asm_file> [--strict]', file=sys.stderr)
        return 64
    path = paths[0]
    try:
        lines = open(path).read().split('\n')
    except OSError:
        print(f'error: asm file not found: {path}', file=sys.stderr)
        return 65

    findings = []
    for i, line in enumerate(lines):
        m = LABEL_RE.match(line)
        if not m or not NAME_RE.search(m.group(1)):
            continue
        res = analyze(lines, i)
        if res and res[0]:
            findings.append((i + 1, m.group(1), res[1], res[2]))

    for ln, name, nw, nprg in findings:
        print(f'advisory: {path}:{ln}  {name} has a raw .DB body '
              f'({nw} words, {nprg} in $8000-$FFFF) -- relocate to '
              f'.DW <label> or .DB <label,>label', file=sys.stderr)
    print(f'[pointer-table] raw_pointer_table_bodies={len(findings)}')
    if findings and strict:
        print(f'FAIL: {len(findings)} pointer-table label(s) still hold raw .DB pointer '
              f'bytes; relocate per agent_playbook/QUALITY_REVIEW.md', file=sys.stderr)
        return 68
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
