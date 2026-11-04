# Numeric literal proofs: SOL-NL / G08

Status: blocked before proof implementation. This is an audited source inventory,
not completion of checkpoint 1 or of the assignment. No new Lean declarations,
axioms, theorem signatures, or kernel controls exist. All universal proof,
compiler differential and final runtime gates remain open.

Batch: `solidity-sol2-20261104`, lane `numeric-literals`.
Repository: `/workspace/solidity-lean`.
Branch: `codex/solidity-sol2-20261104/numeric-literals`.
Base: `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`.
Fetched `origin/master` equals the base; merge-base ancestry check exited zero.
The starting `work` branch was clean and was preserved. No push or merge.
Exact source SHA256 pins: [source-pins.json](../../tests/sol-numeric-literals/source-pins.json).
Setup commands, exits, durations and decisive outputs:
[setup.json](../../tests/sol-numeric-literals/evidence/setup.json).

## Inventory of the pinned implementation

All byte numbers below are ASCII. `Bytes` is the existing byte list. These
observations transcribe the read-only scanner; they are not proven lemmas.

| Function / case family | Exact behavior |
| --- | --- |
| `isDigit`, `digitsVal` | Bytes 48–57; fold `10*a + (d.toNat-48)` from zero. |
| `digitsTail []` | Empty decoded digits and empty suffix. |
| `digitsTail (b::r)`, digit | Emit b and recurse on r. |
| Non-digit b = underscore, r = c::r′, digit c | Consume underscore and c, emit c, recurse on r′. Thus this helper can start with an underscore; its relation must admit that arm. |
| Underscore followed by non-digit, or terminal underscore | Stop without consuming the underscore; retain the entire suffix. |
| Other non-digit | Stop with unchanged suffix. |
| `digits1 []` or non-digit first byte | None. |
| `digits1` digit head | Emit the head plus `digitsTail` digits, retaining its exact suffix. Single underscores only between emitted digits. |
| `decNumber` integer | Try digits1; on failure use empty integer and the original input. |
| Fraction period arm | Period MUST have digits1 after it. Missing fraction digits returns none, even when an integer exists. |
| No-period arm | Empty fraction and unchanged suffix. |
| Empty integer and fraction | Refuse. A leading-period number with nonempty fraction is admitted. |
| Leading zero | Refuse when decoded integer length > 1 and its first byte is 48, including underscore-separated leading zeros. Applies before exponent interpretation. Fraction-leading zeros and exponent-leading zeros are allowed. |
| Exponent empty suffix | Exponent zero. |
| Exponent e/E, minus | Require digits1 after minus, consuming the entire remaining input; exponent is negative digitsVal. |
| Exponent e/E, unsigned | Require digits1 consuming the entire input. Plus is not a sign arm. |
| Other suffix or exponent leftovers | Refuse. |
| Decimal result | `NumLit.dec (digitsVal (ip ++ fp)) fp.length exp`, with underscores removed from all three digit sequences. |
| `hexDigits [b]` | Require hex digit, emit b. |
| `hexDigits (b::95::r)` | Require hex digit b and nonempty r, recurse on r and prepend b. This arm precedes ordinary cons. |
| `hexDigits (b::r)` | Require hex digit b and recursively valid remainder. |
| `hexDigits []` | None. The helper consumes all input; leading/doubled/trailing underscore fails. |
| `hexNumber` | Exact lowercase `0x` prefix only, then hexDigits. Result keeps `ds.map toFin16` and `eip55 ds`. All other prefixes refuse. |
| `toFin16` | `hexVal b % 16`, not an unchecked cast. HexVal subtracts 48, 55 or 87 in the three ASCII ranges. |
| `eip55` | False outside decoded length 40; at length 40 hash lowercase ASCII with existing Keccak and compare letter case against corresponding hash nibbles. Numeric characters impose no case condition. Uses underscore-erased, case-preserved digits. No cryptographic equality assertion. |

`NumLit.value` in read-only Source/Const interprets a decimal with e ≥ 0 as
numerator m*10^e.toNat and denominator 10^f, and e < 0 as numerator m and
denominator 10^(f+e.natAbs). A hexadecimal folds `acc*16+d.val` from zero,
ignoring its checksum flag. Its rational representation is not normalized.

## Span, mode, word and separation boundaries

`numberSpan` has a 0x arm in both Solidity and Yul. It takes hex digits plus
underscores only outside Yul. The other arm takes decimal digits plus
underscores only outside Yul. Yul immediately returns that integer span.
Solidity then takes a period only when immediately followed by a digit;
subsequent fractional digits/underscores are included. It takes e/E-minus
only when immediately followed by a digit, or e/E immediately followed by a
digit; the subsequent exponent run includes digits/underscores. All leftovers
are obtained by dropping exactly the consumed lengths. These spans admit
malformed underscore runs which classification subsequently rejects.

`split` enters the number arm from a digit, or from period followed by digit
in Solidity, and never in assembly-head mode. It errors if the leftover starts
with `isIdPart` (letters, $, underscore, digits). Otherwise it returns span
and leftover. `scan` must also classify the entire span; malformed numbers
are located errors. A period without following digit can therefore be separate
punctuation after a valid integer: whole-lexeme decNumber refusal of `1.` is
NOT a source-level lex refusal theorem. Similarly `1e+2` leaves e and is
rejected for glue, rather than accepting a plus exponent.

`solTok` tries whole words, punctuation and string forms before numeric
classification; hexNumber has precedence over decNumber. `yulNumber` uses
nonempty underscore-free hex digits after 0x or `canonNat` for decimal, not
the Solidity decimal relation. `classify` and mode transitions must appear
in accepted-token consequences; an unqualified numeric classification converse
across pragma/assembly/Yul modes is not justified.

`solWordTable` assigns whole words wei, gwei, ether, seconds, minutes, hours,
days, weeks, years to denomination tokens. These are separate from numbers:
`1wei` is glued, while whitespace or a comment can separate tokens. Whether a
particular unit is accepted semantically is outside this lexical inventory.
Elementary words also use whole-word classification: int/uint use canonical
widths 8..256 divisible by 8 (default 256), bytes uses 1..32 or dynamic bytes,
bare fixed/ufixed return `.fixed signed none`; their dimensioned forms use canonical MxN with M divisible by 8 in 8..256 and N ≤ 80.
Invalid dimensions fall back to identifiers, not numeric tokens. In particular
fixed N=0 is allowed by this scanner even though the pinned grammar's Fixed
rule uses a nonzero first digit. This existing deviation must be retained.

`Lexed` checks reprinting, classifiedFrom, munchFrom, noGlue and return to
Solidity mode. noGlue tests the immediately following piece's first byte for
numeric tokens in all numeric modes. `locate` offsets count all raw bytes,
including trivia; existing lex_locate proves the sliced range reclassifies
and stop ≤ source.length. Backfill must strengthen exact consumption/range
and denomination separation without modifying these representations.

## Independent relation design ledger (not implemented)

Use an inductive Tail relation indexed by input, emitted digits and leftover:
empty; digit-cons; underscore-plus-digit; stopping non-digit with a condition
that the underscore-plus-digit arm cannot fire. Stop cases must preserve the
whole suffix. A nonempty Digits relation adds the mandatory initial digit.
Do not rule out an underscore at the beginning of Tail. Prove iff for every
input and output, not only suffixes chosen by an extra premise.

Use a separate inductive HexDigits relation with singleton, adjacent digit and
underscore-separated digit constructors and nonempty remainder; preserve case.
Its constructors use byte classes, never hexDigits or hexNumber calls.
Decimal spelling constructors should compose Digits derivations for integer,
fraction and signed exponent, carrying source spellings and exact outputs;
require a nonempty mantissa digit sequence (zero values remain admitted) and
the existing decoded-leading-zero condition.
The boundary between Digits components must account for maximal leftover, not
just an arbitrary concatenation. Hex spelling adds the exact 0x bytes and the
existing deterministic eip55 flag. No correctness relation may be defined by
calling decNumber/hexNumber. These are proposed shapes, not checked definitions.

## Open obligations and acceptance ledger

1. Finish checkpoint 1: independent inductive relations, complete formal arm
   enumeration and inhabited controls. Inventory above alone does not pass.
2. Prove arbitrary-input soundness/completeness for digitsTail, digits1,
   hexDigits, decNumber, hexNumber with exact leftover, digit and value folds.
   Prove underscore erasure and Source value interpretation. Preserve and state
   deviations; do not repair a false converse by introducing an input restriction.
3. Prove accepted numeric classification and arbitrary-length refusal families
   for leading zero/octal-looking, bad underscores, empty hex, missing fraction
   or exponent digits and glued suffixes, distinguishing whole lexeme vs source.
4. Add constructor/arm-complete kernel controls, solc-0.8.38 differential fixtures,
   scope-complete declaration/control/obligation checker and actual axiom pins.
   The frozen baseline-20261028 has not been changed. No differential result exists.
5. Complete the assigned consumption, source-range and denomination backfill.
6. Run all permitted KeySort, target/import closure, trust, fixture and full
   runtime gates under resource policy. No RUNTIME_GATE_PASS is claimed.
7. Independently review all implemented proofs and controls, fix findings,
   commit and seal the final proof packet. Current reviews cover inventory only.

[registration.json](../../tests/sol-numeric-literals/registration.json) has an
empty module list because no Lean files were added. Shared roots, module maps,
trust inventory and all producer/Source modules remain unchanged. A final
acceptance checker must enumerate actual declarations; this ledger is not one.

## Runtime blocker / ESCALATE NL-RUNTIME-01

Sources: assignment VM runtime constraints; AGENTS resource policy; setup.json.
The required hard systemd scope cannot run: user bus environment is absent,
and system scope reports PID 1 is not systemd. PID 1 is `tail`. Cgroup v2
memory controls are root-owned and not delegated to this agent. sudo is absent.
The inherited cgroup limit is 16 GiB, not the required 12 GiB; swap max is
unbounded (current swap usage zero). Version queries and static checks ran;
no Lean elaboration, LSP, Lake build or KeySort check was started. Peak RSS was
not measured for setup probes and is recorded null, never as a proof-run metric.
Assignment H1's 4 GiB reserve remains binding; no cap/reserve was weakened.

Question: How should this VM obtain the mandatory 12 GiB, no-swap hard scope?

- Restore runtime support: provision systemd or delegate a cgroup with the
  exact limits; resume the unchanged assignment on this branch.
- Authorize a concrete equivalent hard-limit mechanism after it is supplied
  for review: validate its enforcement before any Lean work; scope and all
  theorem obligations stay unchanged.
- Pause this lane: retain this audited inventory and all open obligations
  until compliant runtime support is available.

No option is preselected and no new permission is inferred. The active goal
must be blocked, not complete, while this prerequisite is unavailable.

## Independent read-only reviews and static gate boundary

Finder and skeptic reviewed this inventory independently without a Lean server.
Both verified all five source pins and accepted the blocked inventory. Finder
requested the mantissa wording correction; skeptic also requested explicit bare
fixed/ufixed behavior. Both corrections are applied above. Their review covers
only this packet; it is not a review of unimplemented proofs or fixtures.
Verdicts are saved in [reviews.json](../../tests/sol-numeric-literals/evidence/reviews.json).

[static-gates.json](../../tests/sol-numeric-literals/evidence/static-gates.json)
records trust (3672 sources, zero findings), existing axiom pins (6343 theorems,
zero errors/unrecorded changes), reachability (3656 reachable, zero orphaned)
and five matching source pins. Setup evidence also records layer and generated
root checks passing. These are static repository checks, not kernel validation
of new results. No new theorem axiom set exists to report. KeySort, numeric
fixtures, full build and all formal assignment gates remain pending.
