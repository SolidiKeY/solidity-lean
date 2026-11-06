# Numeric literal proofs: SOL-NL / G08

Implementation acceptance passes; the assignment is not complete. The required
full `run-lean.sh` gate stops at generated-root registration. The assignment
reserves roots and module maps for coordinator integration, so this lane has not
edited them. All 42 modules and their proposed rows/imports are listed in
[registration.json](../../tests/sol-numeric-literals/registration.json); the exact
module-map proposal is [registration.module-map.patch](../../tests/sol-numeric-literals/registration.module-map.patch).
All owned root imports are already published; the old root-only patch is empty.
No push, merge, PR, producer edit or source representation change occurred.

Batch `solidity-sol2-20261104`, task `numeric-literals`.
Repository `/workspace/solidity-lean`; branch
`codex/solidity-sol2-20261104/numeric-literals`; base
`6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`. The clean starting `work` branch was
preserved; fetched `origin/master` equals the base and its ancestry check passed.
The final committed head and immutable artifact paths are recorded in the sealed
handoff, rather than using a self-referential hash in this document.

## Results and boundaries

The relations `Tail`, `Digits`, `IntegerPart`, `FractionPart`, `Exponent`,
`Decimal`, `HexDigits` and `Hexadecimal` are independent of `decNumber` and
`hexNumber`. Universal iff theorems cover every byte list and output, with no
extra input restrictions. `Tail` includes its leading underscore-plus-digit
arm and exact unconsumed suffixes. Decimal results retain the exact mantissa,
fractional digit count and signed exponent. Hex results retain exact digits
and the existing deterministic `eip55` flag; there is no cryptographic claim.

Whole decimal/hex underscore erasure preserves every NumLit field. The base-10
accumulator and concatenation identities prove the integer/fraction scale law;
the base-16 proof removes `toFin16`'s modulo on admitted digits. Decoder-to-value
corollaries use the existing Source Q interpretation, including its unnormalised
numerator and denominator. Refusal families are arbitrary-length, including
leading zeros, all underscore positions, invalid hex bytes, empty hex, missing
fraction/exponent digits, plus exponents and glued identifier-character suffixes.
Both digit-headed and leading-period source-number paths are covered.

Backfill proves exact consumed-prefix ranges, exact numeric-span reprinting for
all bytes and both numeric modes, positive located numeric ranges and exact slice
lengths, plus arbitrary-position glue and all-denomination separation. It leaves
Source, lexer and token representations unchanged.

The word-table exclusion needed for classification hit the unchanged 200000
heartbeat budget when generated equation families were requested. A warned
proof partition now uses 439 structural prefix lemmas in 30 small modules,
with targeted outer conditional rewrites. Every tail is arbitrary length. All
modules passed per-file diagnostics. Failed attempts and the unchanged 300-second
diagnostic timeouts remain in evidence; none are passing gates.

## Kernel controls, fixtures and trust

[acceptance.json](../../tests/sol-numeric-literals/acceptance.json) enumerates all
42 modules, 652 authored declarations, imports, source hashes, case families,
constructor witnesses, scanner controls and required theorem names.
[kernel-inventory.json](../../tests/sol-numeric-literals/kernel-inventory.json)
records all 991 persistent declarations in imported owned modules, including
generated constructors/recursors/equations, full signatures, universe parameters,
safety metadata and actual transitive axiom sets. Audit itself has no authored
declarations; `run_cmd` uses Lean's `withoutModifyingEnv` and does not persist its
evaluation auxiliaries. No new axiom or unsafe declaration exists. The only
partial entry is Lean's generated `underscoreOk._unsafe_rec` implementation
helper: `isUnsafe=false`, axiom set empty; the kernel definition is safe.

There are 32 inhabited constructor controls, including generated `below`
constructors and the typed fixture record, 68 scanner-arm/boundary controls,
and kernel checksum controls at lengths 39/40/41 and with mixed-case success and
failure. `fixture_observations_pass` kernel-checks the complete typed Lean result
for every one of the 42 fixed compiler spellings. The acceptance gate also
rejects five concrete inventory mutations: deletion, axiom growth, unsafe flag,
changed signature and duplicate declaration. Additional controls reject forged
completion state and a real uncommitted input. A separate MOCK-only regression
checks auto-removal/resource-stop reporting; it never stops a real container.

The exact solc is `0.8.38+commit.1835d247.Emscripten.clang`, SHA256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
[solc-0.8.38.json](../../tests/sol-numeric-literals/solc-0.8.38.json) fixes all compiler
outcomes. [lean-fixtures.json](../../tests/sol-numeric-literals/lean-fixtures.json)
fixes all typed Lean outcomes. [differential.json](../../tests/sol-numeric-literals/differential.json)
compares all 42 rows and exact values for all 18 compiler-accepted rows. The
frozen upstream baseline-20261028 is unchanged. These bounded external tests do
not establish universal compiler parity or EIP-55 cryptographic correctness.

All five lexical/compiler acceptance differences are retained, not excluded:

| Spelling | Recorded boundary |
| --- | --- |
| `1.` | The lexer admits number then period; the compiler rejects the expression context. |
| `_1` | The lexer admits an identifier; the compiler rejects an undeclared name. |
| `1 uint8` | Separate number/type tokens are lexical; the compiler rejects the expression context. |
| Yul `.1` | Period plus integer tokenize; raw yulNumber and the compiler refuse a numeric literal `.1`. |
| `0x5aaeb6053F3E94C9b9A09f33669435E7Ef1BeAed` | The lexer retains a false checksum flag; the compiler diagnoses the checksum. |

No decoder theorem is restricted to hide these observations. Whole-lexeme
refusal must not be confused with rejection of a source fragment that may split
into several tokens. Existing typing exclusions, including address-width and
unit semantics, remain outside these lexical/value theorems.

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

The pinned ANTLR `DecimalNumber` production uses `DecimalDigits`, while
`OctalNumber` is a separate, disallowed token family. The scanner's leading-zero
refusal applies after underscore erasure, including `0_1`; the `Decimal` relation
retains that existing guard rather than claiming to model the isolated
`DecimalNumber` production. `digitsTail` alone also admits an initial underscore
followed by a digit; `Digits` requires its initial digit. These helper and token
boundaries are explicit, with no converse restriction added to hide them.

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

## Module and theorem map

| Area | Module / headline results |
| --- | --- |
| Decimal digits | `Digits.lean`: `tail_iff`, `digits_iff`, exact consumed prefixes, erasure and appended-stop behavior. |
| Spelling | `Spellings.lean`: `hex_digits_iff`, `decimal_iff`, `hexadecimal_iff`; independent spelling relations and component correspondence. |
| Values | `Values.lean`: whole erasure, `decimal_fold`, `digitsVal_append`, `hex_fold`, decoder-to-Source-value corollaries. |
| Refusal | `Refusals.lean`, `Underscores.lean`: global/part-wise arbitrary-input refusal families. |
| Classification | `WordTable/Part00.lean` through `Part29.lean`, `WordTable.lean`, `Classification.lean`: arbitrary-tail word exclusion and accepted-token spelling consequences. |
| Source backfill | `Backfill.lean`, `Span.lean`: exact consumption/slices, glue errors and denomination separation. |
| Validation | `Controls.lean`, `Fixtures.lean`, `Audit.lean`: inhabited controls, all paired fixture outcomes and environment inventory. |

These short filenames are relative to `Solidity/Frontend/NumericLiteralProofs/`.
Full signatures and actual axiom sets are in the inventory; the coordinator's
registration manifest contains a row for every module.

## Runtime and commands

H26 resolved the historical systemd blocker using the approved Docker envelope.
The setup-evidence commit is retained as honest history. The current worker uses
Docker 28.4.0 / cgroup v2 and image
`ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852`.
Every check asserts memory.max=12884901888 and memory.swap.max=0, overrides
activation's thread setting with LEAN_NUM_THREADS=1, uses explicit -j1 through
the owned Lake configuration, holds the writer lock and monitors both parent
cgroup and VM memory for the unchanged >=4 GiB reserve. No address-space limit
substitutes for cgroup enforcement.

Lean is 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b;
Lake is 5.0.0-src+797c613. The permitted KeySort per-file check passed with zero
errors. No RUNTIME_GATE_PASS is claimed. Each check's exact command, outcome,
wall time, cumulative container peak and minimum parent headroom is recorded in
`tests/sol-numeric-literals/evidence/`. Later checks also stamp every proof source
hash. The timed wrapper records Linux child maximum RSS separately; cumulative
cgroup memory is not mislabeled as process RSS.

The implementation gate is:

```sh
python3 scripts/check-sol-numeric-literals.py --implementation --self-test
```

The default command additionally refuses completion while any required ledger
item remains open. It never updates pins. The private runtime/check.py runs these
commands within the verified owned container. Compiler cache setup downloads the
exact pinned file into ignored runtime/.cache and verifies the hash above.

## Reviews and remaining obligations

Independent read-only finder and skeptic reviews used no Lean server. Initial
reviews accepted scanner fidelity and universal correspondence; they requested
whole-number erasure and raw byte-value bridges, which were implemented and
subsequently accepted. The word-prefix coverage review verified all 439 cases
without missing, extra, duplicate or forward references. Final review records
and their resolutions are maintained in the evidence directory.

[obligations.json](../../tests/sol-numeric-literals/obligations.json) is the complete
ledger. The full runtime gate currently fails before Lake because all new root
imports are intentionally pending coordinator registration. Shared roots,
module-map files, trust inventory and every producer/frozen Source area remain
untouched. The registration proposal is concrete and reviewable; after the
coordinator applies it, the unchanged full gate and remaining integration checks
must pass before the persistent goal can be complete. A partial checkpoint,
implementation-only acceptance or failed full gate is not completion.


## Committed checkpoint handoff

The validated implementation head is
`ebb4d3257694880f45b3591435cb270200d5ed2c`. Subsequent scoped changes add only
reporting regression controls, refreshed evidence and this handoff; all 42 Lean
source hashes are unchanged. The containing final commit and original base are
recorded in the sealed packet's manifest. The committed handoff is
[HANDOFF.md](../../tests/sol-numeric-literals/HANDOFF.md).

The complete unchanged `gate.sh full` run took 2949.590 seconds, exit 1.
Linux maximum child RSS was 5656896 KiB; cumulative container memory peak was
8661929984 bytes. Minimum parent/VM headroom was 7935414272 bytes, above the
unchanged 4 GiB reserve, and no resource stop occurred. The full-suite result is:

| Gate | Result |
| --- | --- |
| touched import closure | pass: all 42 owned modules, 49 jobs |
| source trust | pass: 3714 sources, 285 inventoried sites, zero findings |
| layers | pass: 559 core modules; no elaborator or checked-parser reach |
| documentation paths | pass; existing ambiguous references remain warnings |
| shared axiom pins | pass: 6343 pinned theorems, zero errors or changes |
| TestSuite | pass: 552 derived, 11 refuted, zero pending; existing one exclusion and two skips unchanged |
| corpus | pass: exact pinned probe results and full corpus build |
| automatic strict | pass: classification only; cumulative timing is not checked |
| roots / orphans | fail: 42 imports await coordinator registration |
| run-lean | fail at registration, before default targets or executable checks |
| module map | fail: 42 coordinator-owned rows remain unapplied |

The source trust lint initially flagged the audit metadata string; its documented
raw-string convention fixed that without changing emitted metadata. A missing
adjacent SolKey setup pin was recovered byte-for-byte from the published-base
pin after all 274 snapshot files were verified. Earlier failed runs and the
first failed MOCK harness setup are preserved, not counted as passing gates.
`runtime-versions-actual.log` is the strict successful version probe; the earlier
wrapper version probe printed an error and is not a passing version check.

The owned runtime now captures the container ID before launch and retains a
failure report even if auto-removal makes final peak memory unavailable. The
MOCK control tests that branch; it is external Python testing, not a Lean proof
or evidence of an actual resource stop. The real source-binding control creates
and removes a unique untracked input, and requires its exact path in the refusal.

Coordinator integration must register the concrete root/module-map proposals,
then rerun the unchanged final gates in the approved envelope. The full default
build, examples, CLI and SolKey executable remain unvalidated because run-lean
stopped before those stages. No RUNTIME_GATE_PASS or completed persistent goal
is claimed. The goal state was left unchanged as instructed.

Final runtime review also found F-RUNTIME-01: an exit-0 race after a reserve
breach. The wrapper now preserves the observed process exit separately and
forces effective exit 125 when a resource stop coincides with process exit 0.
The isolated MOCK tests cover both observed exits 137 and 0, with auto-removal;
no real pressure or stop is induced. This does not change any Lean source.


H35 follow-up: VM-owned build,627 exact #print axioms results and controls
pass. Cache shipping preflight fails on absent coordinator routing; the prepared
owned cache asset is not delivered. No new checkpoint is done. See
tests/sol-numeric-literals/h35/HANDOFF.md and evidence/h35-cache-receipt.json.


H41 supersedes the earlier H35 VM-shipping requirement. The verified pack
remains on this VM; its hash matches the coordinator-reported receipt. Delivery
is recorded as coordinator-pending. Never run ship-cache.sh on this VM. The
completion checker now validates the preserved pack and all 42 source mappings
instead of attempting VM delivery. Q-H35-SHIP1 is resolved; no transport choice
remains open. The coordinator receipt path is reported provenance, not a file
read on this VM. Original registration/full-runtime obligations remain open.
See evidence/h41-cache-handoff.json for the exact path, hash and receipt.


## Adoption of published master 8495f1de

The coordinator explicitly authorized adoption. Merge commit
221c2eaee71760bac888cb309645c2afaf90109b has parents the preserved owned head
7dc7de2d8581fd54766318fb20670511acd68ed6 and exact published master
8495f1deb0a95dd6b9301822d8649ab76b217681. A backup ref and byte-hashed copy
preserve the old head and both untracked evidence outputs. No reset occurred.
All 42 owned proofs and seven numeric input pins remain byte-identical. Original
base6f3eedf0 remains the proof/source baseline; adopted-master identity is separately
pinned. Inherited foreign work is accepted only when it exactly matches that
publication. Candidate paths union differences against both baselines, preventing
an upstream-added deletion or reversion to original-base bytes from disappearing.
Real Git object-tree controls exercise both failures without editing foreign files.
F-ADOPT-01 was found by both read-only reviewers and is fixed and re-reviewed.

The post-adoption owned build passes (matching-cache replay,49jobs). Per-file
MCP Audit passes and fresh actual #print axioms covers all808 theorem constants;
all991owned constants and axiom sets still match pins. No proof or budget changed.
The H41 verified pack remains valid, preserved and coordinator-pending; no VM
shipping was invoked and no cache freshness was inferred from the notice.

The unchanged full gate suite took72.553793seconds, maximum childRSS689316KiB,
with no resource stop. Build/trust/layers/docs/axiom pins/TestSuite/corpus/strict
automation pass. Root/orphan/run-lean fail because37owned imports remain pending.
Module-map check separately reports38missing rows, including Part00's row.
Published Part00–04 are reused; their source is not duplicated. Existing map rows
are preserved. Updated proposals are data only and pass temporary-index checks;
no shared root or map was edited after adoption. The protected published Source
and Core ExtCall areas remain exact adopted bytes.

The live assignment remains blocked on coordinator registration and final runtime
validation. The final packet records the containing commit separately, plus both
an original-base full patch and an owned delta against adopted master. Old sealed
packets and verified cache packs remain unchanged. Questions=[]; goal not reset.


Follow-on publication f77cf60d3cea8f7f1db8db29cc027532b0cd3fce adopted by merge d83602fb2b6fc9e94da52a3460b719a06f6e8648 preserving prehead7aabe84a and all 42 proof files/seven source pins. Both independent read-only reviews PASS. Fresh bounded owned build is matching-cache replay (49 jobs; 0.467876s, 59892 KiB max child RSS), controls PASS. Existing complete axiom/KeySort evidence is preserved; no theorem changed. Registration proposals remain 37 imports/38 rows; shared roots/maps untouched. Prior full gate failure remains outstanding; this follow-on does not claim a fresh full runtime pass or fresh cache pack. H41 archive/path/SHA and coordinator-pending handoff remain unchanged; no VM shipping. Original goal remains blocked, not reset.


Publication9584f9e7 adopted by merged9e1e7e preserving b225656c and every owned proof/source pin. Parts05/06 now identically integrated; remaining registration35 root imports/36 map rows. Finder/skeptic PASS. Fresh bounded owned matching-cache build PASS (0.519046s;61940KiB max child RSS), controls PASS; fresh register --check exit1 records missing imports. Complete prior axiom/KeySort evidence retained; no theorem changed. No fresh full-runtime pass/cache freshness claimed. H41 preserved pack/path/SHA unchanged, coordinator-pending, no VM shipping. Original goal unchanged and blocked on coordinator registration/final runtime.


Publishedb86ae456 adopted by merge3c9defec preservingd7cdfb47 and all42proof files/seven source pins. Parts07/08 identically integrated; proposals now33 root imports/34 map rows. Fresh bounded owned matching-cache build and controls PASS; register --check exit1 records missing roots. Finder/skeptic PASS. Prior complete axiom/KeySort evidence retained; no theorem changed. No fresh full-runtime pass/cache freshness claimed. H41 preserved pack/path/SHA unchanged, coordinator-pending; no VM shipping. Original goal unchanged and blocked on registration/final runtime.


The H55-H58 unaffected validation checkpoint is recorded in tests/primitive-packets-1105/Constants/H55-H58-HANDOFF.md. It prepares 34 coordinator-only map rows and validates archived VM-reported Numeric/KeySort/kernel/axiom evidence (raw outcomes are not tracked), and reconciles the two authorized implementation scopes without changing any of 47 proof files or reserved Yul sources. Final registration/runtime obligations remain open.

Published e2c8268ec was initially rebased from 462422d4. The later adoption.json merge 9442e5b6d incorporated 3883c64e and was preserved; all 47 proof sources remained unchanged. Machine/Signed gained additive SAR APIs; existing PUSH/representation definitions are unchanged. Both read-only reviews approved compatibility. Tracked adoption-e2c execution records bind a 13.077s per-file audit and 0.557s matching-cache build (not a clean rebuild):45owned declarations plus1imported continuity equation, each with actual signature/owner/axioms. Old generated helper _proof_1_3 renamed _proof_1_2 with every non-name field equal; sword.eq_1 now belongs to Evm.Signed and remains explicitly checked. Historical46entry inventory is retained by immutable commit pin; current46aggregate is not described as46owned. Numeric991+Constants45owned+1continuity =1037audited entries.34coordinator map rows/final runtime gates remain open. No source theorem, premise, exclusion or budget change. One MCP attempt stopped after setup-file omitted explicit-j1; permitted per-file gate replaced it, failure retained.

The three current audit artifacts are tracked under tests/primitive-packets-1105/Constants/adoption-e2c with SHA256SUMS. Constants/check.py reads these committed paths without SOL_NL_VALIDATION_INPUTS. Historical helper rename is checked field by field; altered dependency_sources, proof_sources and command records are refused for both audit and build. Bulk VM-only packets remain optional for separate archived-evidence scripts, not inputs to this current-audit check.
