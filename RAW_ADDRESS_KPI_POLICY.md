# Raw-address KPI

The two raw-address metrics classify active emitted instruction uses from xasm
instruction records v1 through the [validated bundle](ANALYSIS_BUNDLE_SPEC.md).
They are lexical debt counters, not a numeric address-domain or mapper analysis.

## Predicate

Exclude immediate and operandless instructions. Require a pre-fold expression
whose root is an integer, then classify its exact source token:

| Metric | Literal spelling |
|---|---|
| `strict_active_raw_lowaddr` | `$` followed by one or two uppercase hex digits, or three or four uppercase hex digits beginning with `0` |
| `strict_active_raw_absrom` | Exactly four uppercase hex digits from `$C000` through `$FFFF`, excluding `STA`, `STX`, and `STY` |

Thus `$0100` and `$0FFF` qualify as low-address literals, while `$100`, `$FFF`,
`$00002`, and `$0fff` do not. Decimal, binary, character, symbolic/equated,
arithmetic, and projected operands remain excluded even if they resolve to the
same value. Numeric value must not be reformatted to recover literal spelling.
The ROM range and store exclusion are fixed policy, not project configuration.
Read/modify/write instructions remain counted; low-address stores also count.

Direct, indexed, indirect and relative modes are eligible. Grouping, whitespace,
mnemonic case and forced instruction width do not change the decision. Macro
arguments use the substituted integer node's spelling, not the definition's
operand-template text. The consumer does not parse assembly instruction syntax.

## Recognition corrections

The old physical-line scans missed same-line labels, lowercase mnemonics,
some grouped/spaced operands and expanded arguments; they also counted inactive
text and uninvoked macro bodies. The new unit is one active emitted use, including
each repeated macro/include/loop occurrence. Data directives are excluded; a
complete data-only assembly is a measured zero, not unavailable evidence.

The old store exclusion accidentally missed `STA.W`, `STX.W`, and `STY.W`.
The canonical mnemonic now excludes these consistently with unsuffixed stores.
These are explicit recognition corrections; literal radix/case/width policy
is unchanged. Corpus count and site-membership differences require review, never
automatic ratchet widening or semantic project edits.

## Ownership and failures

`bash scripts/raw_address_kpi.sh <asm> [kpis.conf]` retains its interface. With
no descriptor it produces fresh source-only instruction facts once. A supplied
descriptor must contain instructions and satisfy all dependency, schema, byte,
source and policy checks; invalid or explicitly empty evidence refuses without
reassembly. The Python consumer never assembles and validates the whole stream,
including nonmatching instructions, before reporting either count.

Limits retain low-address-first order and exits 68/69. Missing source or refused
evidence uses 65, missing policy 66, missing required limit keys 67, CLI misuse
64. Limits must be nonnegative decimal integers. Operational refusal must not
be interpreted as measured zero or as a threshold failure.

CI, verification, prep, inventory refresh and pending intake calibration reuse
their existing instruction-bearing production. Standalone maturity owns one
ordinary-warning bundle containing the raw, pointer, extent and audit inputs;
standalone summary shares one production between branch and raw metrics.
Bare xref reuse cannot certify instruction freshness. Maturity, refresh, prep
and calibration propagate raw measurement failure; the advisory summary marks
both raw metrics `REFUSED/UNAVAILABLE` instead of displaying stale counts.
Refresh stages all inventories and revalidates before replacement. Calibration
revalidates the original policy before atomic publication; final verification
binds the newly calibrated policy in a new bundle.

No cross-phase verdict cache is introduced. The dashboard's separate lexical
raw-indirect soft inventory and other raw-address-related source scans remain
outside this unit.
