# Roadmap G03: constructor-to-theorem ledger

This is the G03 deliverable of the [full compiler roadmap](../coverage-plan.md#wave-0--scope-interfaces-and-measured-baseline-g00g07):
the source-constructor/feature → admission → lowering → backend → EVM →
theorem ledger, including feature combinations and the decision-driven
obligations of the [binding user decisions](../solidity-scope.md#user-decisions-2026-10-29),
and the detailed module/lemma dependency ledger that the roadmap's
"Groups and dependencies" section assigns to G03. It closes no obligation and
changes no feature status: every row is open work.

- **Base revision:** `caf52ecd4dde5d37cbc0098d47de1a01aa218285` ("Record
  resource and environment decisions"). Every line number below is computed
  by the checker at the head it runs on.
- **Deliverables:** this document, `scripts/roadmap-g03-ledger.py` (standard
  library only) and the generated [roadmap-g03-ledger.json](roadmap-g03-ledger.json).
  No Lean file, manifest, generated feature file or TestSuite file changed.
- **Inputs, read only:** G00's owner table and combinations
  (`scripts/roadmap-g00-scope.py`, imported, not edited), the manifest and the
  upstream ledger, G01's contracts (`Solidity/Roadmap/Contracts.lean`), G04's
  restriction ledger ([roadmap-g04-restrictions.md](roadmap-g04-restrictions.md)),
  the decision table, the work-package manifest and VM table of
  `coverage-plan.md`, and the Lean import graph.
- **Result:** 174 in-profile rows plus `fixedPoint` (in scope by decision
  G00 Q6, manifest still `upstream`), 41 named combinations (G00's 17 and 24
  in-profile ones), 122 ledger-symbol combinations, 25 decision-driven
  obligations and all 41 G04 restrictions (every discharging package G04
  names is an owner of a row citing it), each owned by work packages of the
  roadmap manifest (115, plus the three G24 foundation children the user
  approved, 118 in all). 684 existing declarations are cited as partial
  coverage (648 on feature rows, 75 of them fixed-program regressions). The
  dependency ledger adds 23 lemma-level edges and one deferred cross-wave
  check and finds 9 conflicts with the VM schedule and 378 module findings
  (345 import inversions, 32 parallel imports, one shared write). 301 of them
  pass through the shared compiler foundation and are resolved by the
  G24 foundation children (Q1, answered); the other 77, over 28 modules, each
  have a recorded resolution. 11 oversized checkpoints have lemma splits.
- **Decisions after the first draft** (relayed by the batch coordinator,
  2026-10-29; recorded in [solidity-scope.md](../solidity-scope.md#second-round-2026-10-29),
  merged here from master `77f8878f`): Q1 → foundation child
  packages of G24; the settings cover solc's two pipelines only, so the
  other six `EvalOrder` combinations are dropped (D04 revised). The other
  second-round answers extend D07 (fixed-point semantics; shifts refused),
  D09/D20 (Osaka gas caps; "gas exhaustion"), D11 (hash regions), D16
  (empty link map only) and add D23 (forced ether), D24 (the stipend cost
  rule) and D25 (the G24 children). The G01 contract revision is not on
  master, so the ledger cites the base `Contracts.lean`.

## Method and reproduction

```sh
# Regenerate the JSON ledger and the generated block below.
python3 -I scripts/roadmap-g03-ledger.py --write
# Check: owners are manifest work packages (never a split parent such as G18),
# every stage has an owner or a recorded reason, G00's owners survive, every
# G00 combination, G04 restriction and binding decision has a G03 row, every
# cited declaration is declared in its file, every dependency finding is
# resolved, every oversized checkpoint has a lemma split, outputs are current.
python3 -I scripts/roadmap-g03-ledger.py --check
# G00's own check, which this ledger extends (unchanged).
python3 -I scripts/roadmap-g00-scope.py --check
```

**Stages.** `source`: the independent source definition (S-groups);
`admission`: syntax and static checking (G08–G15; G15 owns every row's
classification); `lowering`: source → intrinsic (G16–G23); `backend`:
intrinsic → abstract machine and executable code (G24–G45); `evm`: the bridge
to the pinned EVM (G46.xx, G47); `theorem`: the composition packages
(G48–G51) and the G01 contracts (`Admission`, `Lowering`, `Compilation`,
`Execution`, `PublicCorrectness`, `SpecTransfer`) the row enters.

**Owners.** The source/admission/lowering/backend cells start from G00's
table. A split parent (S03, S04, G18, G22, G27, G29, G35, G36, G37, G42, G44,
G45, G46, G49, G50, G51, G54) is not a work package of the manifest, so each
of its 54 occurrences is refined to the child packages that carry the row
(`REFINE` in the script), and `--check` fails if a G00 owner is dropped. G46
and G47 tokens move from G00's backend column to `evm`; the `evm` and
`theorem` columns are added by category with per-row overrides. A stage
without owner needs a recorded reason (pragmas, comments, `typeValidation`,
`featureDetection`, `identifiers`, `imports`). The composition owners G00
names once (S05, G15, G24, G45, G48–G55) still own every row; the ledger
names them where the row's obligation is specific.

**Existing coverage.** Four read-only research passes (no Lean server)
collected 1–4 declarations per row from the manifest's `localEvidence`, the
module map and the feature documents; the checker verifies each is declared
in its file with the cited qualified name and computes its line. They are
partial evidence only. `--check` enforces where each stage's anchors may
live: an `evm` anchor must be a Bridge agreement with the external EVM
(`Bridge/SolidityBridge/ExternalEvm*`); a `theorem` anchor is a general
calculus, typing or Bridge theorem about source programs, never compiler or
semantics code, and never an instance of a G01 contract (none exists); a
fixed-program corpus, example or test result is a `regression` anchor, shown
as `r` and counted for no stage. The `missing` lines name in-profile cases no stage covers, citing
G04's restriction IDs where they apply; `R` columns are derived from them.

**Combinations.** G00's 17 named combinations (in-profile parts beside
confirmed exclusions) are matched by their ID sets and refined to work
packages. 22 in-profile combinations are new here, mostly the G04
restrictions that bind two constructs together (mixed core/memory programs,
loops that push or pay, aliases across shrinks, recursion with memory frames,
hashed keys under the per-run premise, …). A combination names owners for the
stages where it adds an obligation; G15 always owns its classification, and
any other stage it does not name is owned through its rows (listed as
"through its rows"; `--check` fails if that is empty). G00's owners of its
combinations must survive refinement. G00's 122 ledger-symbol combinations
are derived as in G00 and owned by G15 plus the admission owners of their
in-profile rows; that ownership is structural, not an independent check.

**Dependencies.** Edges transcribe the roadmap (wave order, sub-wave
prerequisites, S-group order and the rule that a G-parent's children run in
listed order); `g03` edges are lemma dependencies found here. The module
ledger assigns each package the existing modules it is expected to extend
(a planning estimate from the module map, G01's reuse map and G04's
restriction sites; `new` means new modules only, which by G01's import
whitelist holds for all S-groups). The checker then derives, from the Lean
import graph: **schedule** findings (a dependency whose prerequisite is not
scheduled first by wave and VM order), **inversions** (a package edits a
module that imports a module a later package edits, so the earlier package's
final check depends on later work), **parallel imports** (the same between
packages the schedule does not order), **shared writes** between unordered
packages, and cycles over the declared edges plus the wave order. A deferred
edge must name the VM that runs the final check after its prerequisite. The
integrated G00 and G04 are excluded from inversions; G01 is not, since its
contracts are not frozen. Inversions are module-level cycles (an earlier
package's final check depends on a later package): each is acknowledged
either per finding, keyed by kind and package pair, or per module, where the
acknowledgement names exactly the packages involved and `--check` fails when
another package appears through that module. Size flags are static proxies for G02's measurements:
more than 60 owned ledger cells, more than 12,000 edited lines, or an edited
module over 2,500 lines.

## Findings

1. **No row has an end-to-end proof.** Of 175 rows, 117 have no existing
   backend anchor, 152 no EVM anchor and 136 no general theorem anchor; the
   16 EVM anchors are all Bridge word-operation or environment-opcode
   agreements with the external EVM. Every row's
   `missing` list is open work for its owners.
2. **New lemma-level dependencies** (`g03` edges): G13 and G14 ← G12; G17 ←
   G16; G19 ← G16, G17; G20 ← G18.06; G21 ← G18.04; G22.04 ← G20; G26 ← G25;
   G31 ← G27.05; G37.01 ← G32; G38 ← G37.01; G40 ← G35.03; G41 ← G38;
   G44.02 ← G45.04; G44.03 ← G43; G45.03 ← G36.02; G46.03 ← G27.05; G48 ←
   G15, G23; G49.03 ← G36.03, G37.02; G52 ← G49.02. One more is
   **cross-wave**: G39 (wave 4) shares transient state through self-calls
   and callbacks, which G42.01/G42.03 (wave 5) compile. Like G36.03 ← G43 it
   is recorded as a deferred final check: G39 exports its transient
   representation, reset and rollback in wave 4, and its self-call/callback
   case is checked after G42.03, proposed in V23. coverage-plan.md (the
   "Groups and dependencies" preamble and the note after the manifest) names
   G36.03 as the only deferred check; that text needs the G39 exception, and
   V23's checkpoint list the G39 final check (handed to G02/the coordinator,
   since this group may not rewrite those lines).
3. **The VM table conflicts with nine dependencies.** V11 (G19, G20) and
   V12 (G21) run beside V09/V10 although they lower expressions and
   aggregates; V17 (G31) beside V15 (G27.05's hash premise); V21 (G38) beside
   V20 (G37.01's frames); V25 (G44) beside V24 (G43) and V26 (G45.04); V30
   (G52) depends only on V27. The resolution column proposes the added VM
   prerequisite or the interface-then-final-check alternative. G02 decides
   when it rebalances assignments.
4. **Module hot spots.** The existing compiler modules are a shared
   foundation edited across waves 3–5: `Evm.Stmt` (G28, G30, G38, G43),
   `Evm.Compile` (G29.01, G37.01), `Evm.Sim` (G43), `Evm.Repr` and
   `Evm.StorageLemmas` (G27), and `Evm.Machine`, whose symbolic `Slot` G27.05
   must replace (G04 R34) under every compiler proof. The resolution: G24
   freezes the shared signatures (including an abstract slot interface),
   later packages extend without changing them, and each edit re-runs the
   dependent final checks; G45 targets a new assembly layer rather than
   editing `Machine`, and G48–G50 compose in new modules rather than in
   `Frontend.Import`, `Evm.Compiler`, `Theorems`, `Lifetime` or
   `ContractWorld` (the module ledger already plans it so). On the frontend
   side, by G01's boundary the checked frontend must not depend on elaborator
   or adapter modules, so G13 and G14 are planned as new modules and G12
   extends only `Frontend.SourceUnits`; G15 owns the adapter route
   (`Admission`, `Source`, `SolcJson.Body`). The remaining
   wave-2 parallel imports (for example G16's `NumericLowering` importing the
   `Storage`/`Heap` modules G18.02/G18.03 edit beside it) are serialized by
   VM order or rechecked, per the module table. As the roadmap asks for cyclic
   interfaces, the shared compiler foundation becomes children of G24
   (Q1, answered): G24.01 freezes the slot interface (`Evm.Machine`), G24.02
   the state relations (`Sim`, `StateRepr`, `Repr`, the allocator), G24.03
   the statement-leaf and certificate signatures (`Stmt`, `Compile`,
   `Correct`, `Expr`, the memory statement modules), and G24.04 keeps G24's
   unified entry. Later packages extend those modules without changing the
   frozen signatures. This resolves 301 findings mechanically (`FROZEN` in
   the script). What remains below the freeze are the wave-0 interfaces
   G01 and G06, rechecked by every build.
5. **No cycle over the declared edges and the wave order.** This only says no
   declared dependency points to a later wave except the deferred checks
   (G36.03 ← G43; G39 ← G42.01, G42.03), each with its final-check VM. The
   module-level cycles are the inversions of finding 4.
6. **Oversized checkpoints.** G10, G13, G15, G46.01, G46.02, G47, G48,
   G49.01–G49.03 and G51.01 own more than 60 ledger cells; each has a lemma
   split in the module table, which refines the checkpoint without changing
   its obligation or adding a VM. G15's planned edit of
   `Frontend/SolcJson/Body.lean` (2,586 lines) is also flagged. No package
   edits more than 12,000 existing lines.
7. **Ownership gaps closed here.** G00's gaps: (1) the settings surface →
   D04/D05 (G05, G15, G49.02); (2) link-settings provenance → D16 (G05);
   (3) static code constants → D06 (the `Artifact` table); (4) external
   reference tooling → D03 (G06, with the g06-osaka-repin lane); (5)
   canonical-rethrow syntax → G11 in its combination row; (6) combinations
   through shared punctuation → the ledger-symbol rows (G15). G04's §3:
   (1) the stale payment disjunct → D18/R32: G24 owns the interim
   restatement of T1/T12/T13/T15 without it (a statement-only strengthening,
   not yet proved), G43 the payment relation; (2) `fault` conflating divergence and malformed code → D09 (G47,
   G49.03); (3) `recDepth = 1024` → D08 (S03.03, G37.02); (4) the missing
   `2^64` bound and `Panic(0x41)` → the allocation-capacity combination
   (S02, S04.01, G33, G38) and R24 (G30); (5) the source-only environment
   keys → confirmed exclusions, no owner needed; (6) stale public
   documentation → G55. One owner had no row: the compiler's **calldata
   representation**; G35.03 owns it and G40 depends on it.
8. **Decision-driven rows** D01–D25 cover every row of both binding decision
   tables and every follow-up label. The assignment's named obligations are
   D11 (per-run hash premise and bound), D14 (`decode` export), D06
   (artifact table), D19/D20 (frame and transaction failure semantics),
   D10 (memory frames for recursion), D04 (the `EvalOrder` settings,
   revised to solc's two pipelines)
   and D07 (fixed point). The in-flight lane that changes each is named in
   the table; none of them is done.

## Ledger

<!-- BEGIN generated by scripts/roadmap-g03-ledger.py -->
175 feature rows (174 in-profile + 1 decision-driven), 41 named combinations (17 from G00, 24 in-profile), 122 ledger-symbol combinations, 25 decision-driven obligations, 118 work packages, 685 existing-coverage anchors (648 on feature rows), 41 G04 restrictions mapped.

Stages with no existing anchor (rows): source 62, admission 114, lowering 56, backend 117, evm 152, theorem 136.

### Feature owners

Columns: owning work packages per stage; `cov` lists the stages with an existing anchor (s source, a admission, l lowering, b backend, e EVM, t theorem), then `r` for fixed-program regressions, which cover no stage; `R` the G04 restrictions cited in the row's missing cases.

| ID | cat | cur | source | admission | lowering | backend | EVM | theorem | cov | R |
|---|---|---|---|---|---|---|---|---|---|---|
| `abiDecode` | abi | partial | S04.02 | G10 G13 G15 | G21 | G40 G41 | G46.02 | G48 G49.02 G49.03 (Lowering, Compilation, Execution, PublicCorrectness) | `··l···r` | R04, R20 |
| `abiEncode` | abi | partial | S04.02 | G10 G13 G15 | G21 | G40 G41 | G46.02 | G48 G49.02 G49.03 (Lowering, Compilation, Execution, PublicCorrectness) | `·al···r` | R04 |
| `abiEncodeCall` | abi | partial | S04.02 | G10 G13 G15 | G21 | G40 G41 | G46.02 | G48 G49.02 G49.03 (Lowering, Compilation, Execution, PublicCorrectness) | `··l···r` | R04 |
| `abiEncodePacked` | abi | partial | S04.02 | G10 G13 G15 | G21 | G40 G41 | G46.02 | G48 G49.02 G49.03 (Lowering, Compilation, Execution, PublicCorrectness) | `·al····` | R04 |
| `abiEncodeWithSelector` | abi | partial | S04.02 | G10 G13 G15 | G21 | G40 G41 | G46.02 | G48 G49.02 G49.03 (Lowering, Compilation, Execution, PublicCorrectness) | `·al····` | R04 |
| `abiEncodeWithSignature` | abi | partial | S04.02 | G10 G13 G15 | G21 | G40 G41 | G46.02 G46.05 | G48 G49.02 G49.03 (Lowering, Compilation, Execution, PublicCorrectness) | `sal····` | R04 |
| `addmodBuiltin` | builtins | partial | S02 | G10 G13 G15 | G16 | G25 | G46.01 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness) | `s·····r` | R10, R37 |
| `assertBuiltin` | builtins | partial | S02 S04.02 | G10 G13 G15 | G21 | G38 | G46.02 G47 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness) | `s··b··r` | R01, R29, R37 |
| `bytesConcat` | builtins | partial | S02 | G10 G13 G15 | G18.03 | G33 G35.03 G35.04 | G46.02 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness) | `··l····` | R10, R28, R31 |
| `ecrecoverBuiltin` | builtins | partial | S04.02 | G10 G13 G15 | G23 | G31 | G46.05 G46.02 G47 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness) | `s·····r` | R10 |
| `erc7201Builtin` | builtins | present | S02 S04.02 | G10 G13 G15 | G23 | G31 | G46.05 G46.01 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness) | `s·l···r` | R10 |
| `keccakBuiltin` | builtins | partial | S04.02 | G10 G13 G15 | G23 | G31 | G46.05 G46.02 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness) | `s·l····` | R10, R34, R35 |
| `mulmodBuiltin` | builtins | partial | S02 | G10 G13 G15 | G16 | G25 | G46.01 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness) | `s·····r` | R10, R37 |
| `requireBuiltin` | builtins | partial | S02 S04.02 | G10 G13 G15 | G21 | G38 | G46.02 G47 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness) | `s·lb··r` | R07, R37 |
| `revertBuiltin` | builtins | partial | S02 S04.02 | G10 G13 G15 | G21 | G38 | G46.02 G47 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness) | `s·l····` | R07, R37 |
| `ripemd160Builtin` | builtins | partial | S04.02 | G10 G13 G15 | G23 | G31 | G46.05 G46.02 G47 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness) | `s·l····` | R10, R13 |
| `sha256Builtin` | builtins | partial | S04.02 | G10 G13 G15 | G23 | G31 | G46.05 G46.02 G47 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness) | `s·l····` | R10 |
| `stringConcat` | builtins | partial | S02 | G10 G13 G15 | G18.03 | G33 G35.03 G35.04 | G46.02 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness) | `··l····` | R28, R31 |
| `wrapUnwrap` | builtins | partial | S02 | G10 G13 G15 | G16 | G25 | G46.01 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness) | `··l···r` | R13 |
| `callbackSemantics` | calls | partial | S03.03 S04.03 | G13 G15 | G22.02 | G42.03 | G47 | G48 G49.02 G50.02 G51.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s····t·` |  |
| `creationTry` | calls | partial | S03.03 S04.04 | G11 G13 G15 | G22.03 | G44.03 | G47 | G48 G49.02 G50.01 G50.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `sa·····` |  |
| `emptyDataValueCall` | calls | partial | S03.03 S04.03 | G10 G13 G15 | G22.02 G22.05 | G43 | G47 | G48 G49.02 G50.02 G51.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·l··t·` | R06, R33 |
| `extensionCalls` | calls | partial | S03.03 | G10 G14 G15 | G20 | G37.01 | G46.01 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `·al···r` |  |
| `externalLibraryCalls` | calls | partial | S03.03 S04.03 | G10 G14 G15 | G22.04 | G42.04 | G47 | G48 G49.02 G50.02 G51.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `sa·····` |  |
| `externalSelfCalls` | calls | partial | S03.03 | G10 G14 G15 | G22.01 | G42.01 | G47 | G48 G49.02 G50.02 G51.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·l···r` | R07 |
| `externalTypedCalls` | calls | partial | S03.03 S04.03 | G10 G14 G15 | G22.01 | G42.02 | G47 | G48 G49.02 G50.02 G51.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·l··t·` | R07, R33 |
| `functionValues` | calls | partial | S03.03 | G10 G13 G15 | G20 | G37.03 G42.05 | G46.01 G47 | G48 G49.02 G50.02 G51.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `··l····` |  |
| `internalCalls` | calls | partial | S03.03 | G10 G14 G15 | G20 | G37.01 G37.02 | G46.01 G46.02 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·lb·t·` | R09, R27 |
| `newContract` | calls | partial | S03.03 S04.04 | G10 G13 G15 | G22.03 | G44.03 | G47 | G48 G49.02 G50.01 G50.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `sa···t·` |  |
| `recursiveCalls` | calls | partial | S03.03 S03.04 | G10 G14 G15 | G20 | G37.02 | G46.02 G46.06 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s····t·` | R08, R27, R39 |
| `sendTransfer` | calls | partial | S03.03 S04.03 | G10 G13 G15 | G22.02 G22.05 | G43 | G47 | G48 G49.02 G50.02 G51.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s··b·t·` | R06, R32, R33 |
| `valueOption` | calls | partial | S03.03 S04.03 | G10 G13 G15 | G22.01 G22.03 G22.05 | G43 | G47 | G48 G49.02 G50.02 G51.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `sal····` | R06 |
| `constants` | declarations | partial | S01 | G09 G13 G15 | G16 | G25 | G46.01 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `··l···r` |  |
| `constructors` | declarations | partial | S03.02 S04.04 | G11 G14 G15 | G19 G22.03 | G44.01 | G47 | G48 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `··l··tr` | R04 |
| `contracts` | declarations | partial | S00 S01 | G11 G14 G15 | G20 | G40 G44.01 G44.02 | G46.02 G47 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `s·l···r` | R04, R05 |
| `enumDeclarations` | declarations | partial | S00 S01 | G09 G15 | G16 | G25 | G46.01 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `s·l···r` | R13 |
| `errorDeclarations` | declarations | partial | S00 S01 S04.02 | G09 G11 G15 | G21 | G38 G41 | G46.02 G47 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `··l···r` | R07 |
| `eventDeclarations` | declarations | partial | S00 S01 | G09 G11 G15 | G23 | G31 | G46.02 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `·al···r` |  |
| `fallbackFunction` | declarations | partial | S03.03 S04.04 | G11 G14 G15 | G20 | G40 | G46.02 G47 | G48 G49.02 G50.02 (Admission, Lowering, Compilation, PublicCorrectness) | `sal····` |  |
| `freeFunctions` | declarations | partial | S00 S01 | G11 G12 G15 | G20 | G37.01 | G46.01 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `s·l···r` | R08, R09 |
| `functions` | declarations | partial | S00 S01 S03.01 S03.03 | G11 G13 G15 | G20 | G37.01 G37.03 G40 | G46.02 G47 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `s·lb··r` | R04, R08, R09 |
| `immutables` | declarations | partial | S01 S04.03 | G09 G13 G15 | G19 | G44.01 | G46.02 G47 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `s·l····` | R04 |
| `imports` | declarations | partial | S00 | G11 G12 G15 | G23 | G44.02 | — | G48 (Admission) | `·al···r` |  |
| `inheritance` | declarations | partial | S01 S03.02 | G11 G14 G15 | G19 G20 | G44.01 | G46.02 G47 | G48 G49.02 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `··l···r` | R04 |
| `interfaces` | declarations | partial | S00 S01 | G11 G14 G15 | G20 | G42.02 G42.05 | G46.02 G47 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `··l···r` | R07 |
| `libraries` | declarations | partial | S00 S01 S03.03 | G11 G14 G15 | G22.04 | G42.04 G44.02 | G46.02 G47 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `s·l···r` | R04, R09 |
| `modifierPlaceholder` | declarations | partial | S03.02 | G11 G15 | G19 | G36.01 | G46.01 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `··l···r` |  |
| `modifiers` | declarations | partial | S03.02 | G11 G14 G15 | G19 | G36.01 G37.01 | G46.01 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `s·l···r` | R01, R08, R09 |
| `operatorAliases` | declarations | partial | S01 | G11 G13 G14 G15 | G16 G20 | G25 G37.01 | G46.01 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `··l···r` |  |
| `overrideDeclarations` | declarations | partial | S01 | G11 G14 G15 | G20 | G37.03 | G46.01 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `s·l····` |  |
| `publicGetters` | declarations | partial | S01 S03.03 | G13 G14 G15 | G20 | G40 G41 | G46.02 G47 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `··l···r` | R07 |
| `receiveFunction` | declarations | partial | S03.03 S04.04 | G11 G14 G15 | G20 | G40 | G46.02 G47 | G48 G49.02 G50.02 (Admission, Lowering, Compilation, PublicCorrectness) | `s·l···r` | R04, R06, R33 |
| `sourceUnits` | declarations | partial | S00 | G11 G12 G15 | G23 | G44.02 | G47 | G48 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `·a····r` |  |
| `stateMutability` | declarations | partial | S01 S03.03 | G11 G13 G15 | G20 G22.01 G22.05 | G40 G42.02 G42.05 | G46.02 G47 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `s···e··` | R32 |
| `stateVariables` | declarations | partial | S01 S04.01 | G09 G11 G15 | G18.02 | G27.01 G27.02 G27.03 G27.05 G44.01 | G46.03 G47 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `s··b···` | R14, R17 |
| `structDeclarations` | declarations | partial | S00 S01 | G09 G15 | G18.01 G18.02 G18.03 G18.04 G18.05 | G27.01 G32 | G46.02 G46.03 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `s·lb···` | R20, R28 |
| `usingFor` | declarations | partial | S01 | G11 G14 G15 | G20 | G37.01 G37.03 | G46.01 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `··l···r` | R09 |
| `valueTypeDeclarations` | declarations | partial | S00 S01 | G09 G13 G15 | G16 | G25 | G46.01 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `s·l···r` |  |
| `visibility` | declarations | partial | S01 | G11 G14 G15 | G20 | G40 | G46.02 G47 | G48 G49.02 G49.03 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `s·l····` | R04 |
| `addressBalance` | environment | partial | S04.02 S04.03 | G10 G13 G15 | G23 | G31 G43 | G46.04 G47 | G48 G49.02 G50.02 (Lowering, Compilation, Execution, PublicCorrectness) | `s··be··` | R11 |
| `blockTimestamp` | environment | present | S04.02 | G10 G13 G15 | G23 | G31 | G46.04 | G48 G49.02 G50.02 (Lowering, Compilation, Execution, PublicCorrectness) | `sa··e··` |  |
| `msgSender` | environment | present | S04.02 | G10 G13 G15 | G23 | G31 | G46.04 | G48 G49.02 G50.02 (Lowering, Compilation, Execution, PublicCorrectness) | `sa·be··` | R27 |
| `msgValue` | environment | partial | S04.02 | G10 G13 G15 | G23 | G31 G43 | G46.04 G47 | G48 G49.02 G50.02 (Lowering, Compilation, Execution, PublicCorrectness) | `s··be··` |  |
| `thisAddress` | environment | partial | S04.02 | G10 G13 G15 | G23 | G31 | G46.04 | G48 G49.02 G50.02 (Lowering, Compilation, Execution, PublicCorrectness) | `sa··e··` | R27 |
| `arithmetic` | expressions | partial | S02 | G10 G13 G15 | G16 | G25 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s··b·t·` | R05, R12, R13, R37 |
| `assignment` | expressions | partial | S02 | G10 G13 G15 | G17 | G26 G28 G34 | G46.01 G46.02 G46.03 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·lb··r` | R17, R19, R20 |
| `bitwise` | expressions | partial | S02 | G10 G13 G15 | G16 | G25 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s··be··` | R12, R13 |
| `callOptions` | expressions | partial | S02 S03.03 | G10 G15 | G22.01 G22.03 G22.05 | G42.02 G43 G44.03 | G47 | G48 G49.02 G50.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `sal····` | R06, R33 |
| `comparisons` | expressions | partial | S02 | G10 G13 G15 | G16 | G25 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s··be··` | R13 |
| `compoundAssignment` | expressions | partial | S02 | G10 G13 G15 | G17 | G26 G28 | G46.01 G46.03 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·lb···` | R18, R29 |
| `conditional` | expressions | partial | S02 | G10 G13 G15 | G17 | G26 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·lb··r` | R28 |
| `deleteExpression` | expressions | partial | S02 S04.01 | G10 G13 G15 | G18.05 | G28 G30 G34 | G46.02 G46.03 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s··b··r` | R21, R28, R29 |
| `explicitConversions` | expressions | partial | S01 S02 | G10 G13 G15 | G16 G18.05 | G25 G35.01 G35.02 G35.03 G35.04 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `·al····` | R13, R27 |
| `functionCalls` | expressions | partial | S02 S03.03 | G10 G13 G15 | G20 | G37.01 G37.03 G42.01 G42.02 G42.04 | G46.01 G47 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·lb··r` | R04, R07, R08, R09 |
| `implicitConversions` | expressions | partial | S01 | G13 G15 | G16 G18.05 | G25 G35.01 G35.02 G35.03 G35.04 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·l····` | R13 |
| `increments` | expressions | partial | S02 | G10 G13 G15 | G17 | G26 G28 | G46.01 G46.03 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·lb···` | R18, R21, R29 |
| `indexAccess` | expressions | partial | S02 | G10 G13 G15 | G17 G18.02 G18.03 G18.04 | G26 G28 G34 | G46.01 G46.02 G46.03 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s··b··r` | R10, R13, R14 |
| `inlineArrays` | expressions | partial | S02 | G10 G13 G15 | G18.03 | G33 | G46.02 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `·al···r` | R28 |
| `memberAccess` | expressions | partial | S02 | G10 G13 G15 | G17 G18.02 G18.03 G18.04 | G26 G28 G34 | G46.01 G46.02 G46.03 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `salb···` | R11 |
| `metaTypeExpression` | expressions | partial | S01 | G10 G13 G15 | G23 | G31 | G46.01 G46.05 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `·al···r` |  |
| `namedArguments` | expressions | partial | S02 | G10 G13 G15 | G20 | G37.01 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `·al···r` |  |
| `names` | expressions | partial | S01 S02 | G10 G12 G15 | G16 G17 | G26 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `salb···` | R04 |
| `newMemory` | expressions | partial | S02 S04.01 | G10 G13 G15 | G18.03 | G33 | G46.02 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·lb···` | R22, R25, R28 |
| `parentheses` | expressions | present | S00 S02 | G10 G15 | G16 | G26 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `··l···r` |  |
| `rangeAccess` | expressions | partial | S02 | G10 G13 G15 | G18.04 G21 | G35.03 | G46.02 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `··l···r` | R04, R20 |
| `shifts` | expressions | partial | S02 | G10 G13 G15 | G16 | G25 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s···e·r` | R12 |
| `shortCircuit` | expressions | partial | S02 | G10 G15 | G17 | G26 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `sa···tr` | R09, R10 |
| `structConstruction` | expressions | partial | S02 | G10 G13 G15 | G18.03 | G33 | G46.02 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `·alb···` | R28 |
| `tupleExpressions` | expressions | partial | S02 | G10 G13 G15 | G17 | G26 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `·al···r` | R09 |
| `unaryArithmetic` | expressions | partial | S02 | G10 G13 G15 | G16 | G25 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s··be··` | R12, R13 |
| `addressLiterals` | lexical | partial | S00 | G08 G15 | G16 | G25 | G46.01 G46.04 | G48 G49.03 (Admission, Lowering) | `sa····r` | R13 |
| `booleanLiterals` | lexical | present | S00 | G08 G15 | G16 | G25 | G46.01 | G48 G49.03 (Admission, Lowering) | `··lbe·r` |  |
| `comments` | lexical | partial | S00 | G08 G15 | — | — | — | G48 (Admission) | `·a····r` |  |
| `etherUnits` | lexical | present | S00 | G08 G15 | G16 | G25 | G46.01 | G48 G49.03 (Admission, Lowering) | `s·l···r` |  |
| `hexLiterals` | lexical | partial | S00 S02 | G08 G15 | G18.03 | G33 | G46.01 | G48 G49.03 (Admission, Lowering) | `s·l···r` | R10, R31 |
| `identifiers` | lexical | partial | S00 S01 | G08 G12 G15 | G16 G17 | G26 | — | G48 (Admission, Lowering) | `·al···r` |  |
| `numericLiterals` | lexical | partial | S00 | G08 G15 | G16 | G25 | G46.01 | G48 G49.03 (Admission, Lowering) | `··lbe··` | R13 |
| `pragmaAbicoder` | lexical | partial | S00 S04.02 | G08 G11 G15 | G21 | G40 G41 | G46.02 | G48 G49.02 (Admission, Lowering, Execution, PublicCorrectness) | `·a·····` | R04 |
| `pragmaOther` | lexical | partial | S00 | G08 G11 G15 | — | — | — | G48 (Admission) | `·a·····` |  |
| `pragmaVersion` | lexical | partial | S00 | G08 G11 G15 | — | — | — | G48 (Admission) | `·a·····` |  |
| `stringLiterals` | lexical | partial | S00 S02 | G08 G15 | G18.03 | G33 | G46.01 | G48 G49.03 (Admission, Lowering) | `s·l···r` | R10, R17 |
| `timeUnits` | lexical | present | S00 | G08 G15 | G16 | G25 | G46.01 | G48 G49.03 (Admission, Lowering) | `s·l···r` |  |
| `unicodeLiterals` | lexical | partial | S00 S02 | G08 G15 | G18.03 | G33 | G46.01 | G48 G49.03 (Admission, Lowering) | `·al···r` | R10, R17 |
| `creationCode` | metadata | partial | S04.02 | G13 G15 | G23 | G44.02 | G46.02 G47 | G48 G49.02 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `·al····` | R05 |
| `errorEventSelector` | metadata | present | S01 S04.02 | G13 G15 | G23 | G31 | G46.01 | G48 G49.02 (Admission, Lowering, Compilation, PublicCorrectness) | `··l···r` | R10 |
| `functionAddress` | metadata | partial | S04.03 | G13 G15 | G22.04 | G42.05 | G46.01 G47 | G48 G49.02 (Admission, Lowering, Compilation, PublicCorrectness) | `··l···r` |  |
| `functionSelector` | metadata | partial | S01 S04.02 | G13 G15 | G23 | G31 G40 | G46.01 | G48 G49.02 (Admission, Lowering, Compilation, PublicCorrectness) | `··l···r` |  |
| `interfaceId` | metadata | present | S01 | G13 G15 | G23 | G31 | G46.01 | G48 G49.02 (Admission, Lowering, Compilation, PublicCorrectness) | `s·l···r` |  |
| `runtimeCode` | metadata | partial | S04.02 | G13 G15 | G23 | G44.02 | G46.02 G47 | G48 G49.02 G50.01 (Admission, Lowering, Compilation, PublicCorrectness) | `·al····` | R05 |
| `typeBounds` | metadata | partial | S01 | G13 G15 | G16 | G25 | G46.01 | G48 G49.02 (Admission, Lowering, Compilation, PublicCorrectness) | `s·l···r` |  |
| `typeName` | metadata | present | S01 | G13 G15 | G23 | G31 | G46.01 | G48 G49.02 (Admission, Lowering, Compilation, PublicCorrectness) | `·al····` | R10, R17 |
| `abiEntryValidation` | semantics | partial | S04.02 | G13 G15 | G21 | G40 | G46.02 G47 | G48 G49.02 G50.02 (Lowering, Compilation, Execution, PublicCorrectness) | `sal····` | R04 |
| `checkedArithmetic` | semantics | partial | S02 | G13 G15 | G16 | G25 | G46.01 | G48 G49.02 G49.03 (Lowering, Compilation, Execution, PublicCorrectness) | `s·l··t·` | R12 |
| `constructorLifetime` | semantics | partial | S04.04 | G14 G15 | G22.03 | G44.01 G44.03 | G47 | G48 G49.02 G50.01 (Lowering, Compilation, Execution, PublicCorrectness) | `s····t·` | R04 |
| `defaultInitialization` | semantics | partial | S02 S04.01 | G13 G15 | G18.02 G18.03 | G30 G33 | G46.02 G46.03 | G48 G49.02 G49.03 (Lowering, Compilation, Execution, PublicCorrectness) | `sa·b···` | R16, R28 |
| `evaluationOrder` | semantics | partial | S02 S03.01 S03.03 | G13 G15 | G16 G17 | G26 | G46.06 | G48 G49.02 G49.03 (Lowering, Compilation, Execution, PublicCorrectness) | `·al····` |  |
| `exactConstants` | semantics | partial | S01 | G13 G15 | G16 | G25 | G46.01 | G48 G49.02 G49.03 (Lowering, Compilation, Execution, PublicCorrectness) | `·al····` |  |
| `featureDetection` | semantics | partial | S05 | G15 | — | — | — | G48 G49.03 (Admission, PublicCorrectness) | `·a·····` |  |
| `nonpayableEntry` | semantics | partial | S04.04 | G13 G15 | G22.05 | G40 G43 | G46.04 G47 | G48 G49.02 G50.02 (Lowering, Compilation, Execution, PublicCorrectness) | `sa··e··` | R04 |
| `panicCodes` | semantics | partial | S04.02 | G13 G15 | G21 | G38 | G46.02 G47 | G48 G49.02 G49.03 (Lowering, Compilation, Execution, PublicCorrectness) | `s····t·` | R24, R25, R37 |
| `referenceCopyRules` | semantics | partial | S04.01 | G13 G15 | G18.05 | G29.01 G29.02 G29.03 G35.01 G35.02 G35.03 G35.04 G35.05 G35.06 | G46.02 G46.03 | G48 G49.02 G49.03 (Lowering, Compilation, Execution, PublicCorrectness) | `s·l··t·` | R19, R20 |
| `revertPayloads` | semantics | partial | S04.02 | G13 G15 | G21 | G38 G41 | G46.02 G47 | G48 G49.02 G49.03 (Lowering, Compilation, Execution, PublicCorrectness) | `s·l··t·` | R07, R37 |
| `rollback` | semantics | partial | S03.04 S04.03 | G13 G15 | G21 G22.01 G22.02 G22.03 G22.05 | G38 G39 | G47 G46.03 | G48 G49.02 G50.02 (Lowering, Compilation, Execution, PublicCorrectness) | `s······` | R07, R41 |
| `staticCallRestriction` | semantics | partial | S03.03 S04.03 | G13 G15 | G22.01 G22.04 | G42.02 G42.05 | G47 | G48 G49.02 G50.02 (Lowering, Compilation, Execution, PublicCorrectness) | `s·l····` | R07 |
| `termination` | semantics | partial | S03.04 | G13 G15 | G19 | G36.03 G37.02 | G46.06 G47 | G49.02 G49.03 G50.02 G51.02 (Compilation, Execution, PublicCorrectness, SpecTransfer) | `s··b·t·` | R08, R38, R39 |
| `typeValidation` | semantics | partial | S01 | G13 G15 | — | — | — | G48 (Admission) | `·a·····` | R15, R16 |
| `uncheckedArithmetic` | semantics | partial | S02 | G13 G15 | G16 | G25 | G46.01 | G48 G49.02 G49.03 (Lowering, Compilation, Execution, PublicCorrectness) | `s·l··t·` | R12 |
| `worldAssumptions` | semantics | partial | S04.03 | G13 G15 | G22.02 G22.05 | G42.02 G43 | G47 | G49.02 G50.02 G51.02 (Execution, PublicCorrectness, SpecTransfer) | `s····t·` | R33 |
| `blocks` | statements | partial | S03.01 | G11 G15 | G19 | G36.01 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `sa·b·t·` | R01, R02, R05 |
| `breakStatement` | statements | present | S03.01 | G11 G15 | G19 | G36.01 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `··l··t·` |  |
| `canonicalRethrow` | statements | partial | S03.01 S04.02 | G11 G15 | G21 | G38 | G46.02 G47 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·l····` | R07, R31, R37 |
| `catchClauses` | statements | partial | S03.03 S04.02 | G11 G15 | G21 | G38 G41 | G46.02 G47 | G48 G49.02 G50.02 G51.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s····t·` | R07 |
| `continueStatement` | statements | partial | S03.01 | G11 G15 | G19 | G36.01 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `··l··t·` |  |
| `doWhileStatement` | statements | partial | S03.01 | G11 G15 | G19 | G36.01 G36.02 G36.03 | G46.01 G46.06 | G48 G49.01 G49.02 G49.03 G51.01 G51.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `sal··t·` | R21, R22, R38 |
| `emitStatement` | statements | partial | S03.01 S04.02 | G11 G15 | G23 | G31 | G46.02 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `··l···r` |  |
| `expressionStatements` | statements | partial | S03.01 | G11 G15 | G17 | G26 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `·alb···` | R09, R29 |
| `forStatement` | statements | partial | S03.01 | G11 G15 | G19 | G36.01 G36.02 G36.03 | G46.01 G46.06 | G48 G49.01 G49.02 G49.03 G51.01 G51.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `··lb·t·` | R21, R22 |
| `ifStatement` | statements | present | S03.01 | G11 G15 | G19 | G36.01 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·lb·t·` | R23, R36 |
| `returnStatement` | statements | partial | S03.01 | G11 G15 | G19 | G36.01 G37.01 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·lb···` | R09, R41 |
| `revertStatement` | statements | partial | S03.01 S04.02 | G11 G15 | G21 | G38 | G46.02 G47 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·l··tr` | R07, R37 |
| `tryStatement` | statements | partial | S03.03 S04.03 | G11 G15 | G21 G22.01 G22.03 | G38 G42.02 G42.06 | G47 | G48 G49.02 G50.02 G51.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·lb·t·` | R07 |
| `uncheckedBlock` | statements | partial | S02 S03.01 | G11 G15 | G16 | G25 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `·alb··r` | R12 |
| `variableDeclarations` | statements | partial | S03.01 | G11 G13 G15 | G17 G19 | G26 | G46.01 | G48 G49.01 G49.02 G49.03 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·lb·t·` | R16, R28 |
| `whileStatement` | statements | partial | S03.01 | G11 G15 | G19 | G36.01 G36.02 G36.03 | G46.01 G46.06 | G48 G49.01 G49.02 G49.03 G51.01 G51.02 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s·lb·t·` | R21, R22, R38 |
| `arrayLength` | storage | partial | S04.01 | G10 G13 G15 | G18.02 G18.03 G18.04 | G28 G34 | G46.03 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `sa·b···` | R24 |
| `arrayPop` | storage | partial | S04.01 | G10 G13 G15 | G18.02 | G30 | G46.03 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s··b·t·` | R21, R36 |
| `arrayPush` | storage | partial | S04.01 | G10 G13 G15 | G18.02 | G30 | G46.03 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s··b·t·` | R18, R21 |
| `arrayPushReference` | storage | partial | S04.01 | G10 G13 G15 | G18.02 | G30 | G46.03 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s····t·` | R18 |
| `danglingReferences` | storage | partial | S04.01 | G13 G15 | G18.05 | G28 G30 | G46.03 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s··b·t·` | R36 |
| `deleteMappingTails` | storage | partial | S04.01 | G13 G15 | G18.05 | G29.02 G30 | G46.03 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s····t·` | R21 |
| `logicalStorageBase` | storage | partial | S04.01 | G09 G13 G15 | G18.02 | G27.05 | G46.03 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `sa·····` | R34 |
| `memoryAliasing` | storage | partial | S04.01 | G13 G15 | G18.03 | G34 | G46.02 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s··b·t·` | R04, R20, R30 |
| `storageAliasing` | storage | partial | S04.01 | G13 G15 | G18.02 | G28 | G46.03 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s··b···` | R09, R36 |
| `storageCopy` | storage | partial | S04.01 | G13 G15 | G18.05 | G29.01 G29.02 G29.03 | G46.03 | G48 G49.01 G49.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `s··b·t·` | R17, R19 |
| `transientState` | storage | partial | S04.03 | G09 G13 G15 | G23 | G39 | G46.03 G47 | G48 G49.02 G50.02 G51.01 (Lowering, Compilation, Execution, PublicCorrectness, SpecTransfer) | `sa·····` |  |
| `addressTypes` | types | partial | S00 S01 | G09 G13 G15 | G16 | G25 G42.02 G42.05 | G46.01 G46.04 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `s·l·e··` | R27 |
| `boolType` | types | present | S00 S01 | G09 G13 G15 | G16 | G25 | G46.01 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `s··be··` | R34 |
| `calldataLocation` | types | partial | S01 S04.01 | G09 G13 G15 | G18.04 | G35.03 G40 | G46.02 G46.01 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `··l····` | R20 |
| `dynamicArrays` | types | partial | S00 S01 S04.01 | G09 G13 G15 | G18.02 G18.03 G18.04 G18.05 | G27.03 G32 | G46.02 G46.03 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `s··b···` | R22, R24, R28 |
| `dynamicBytesType` | types | partial | S00 S01 S04.01 | G09 G13 G15 | G18.02 G18.03 G18.04 G18.05 | G27.03 G32 | G46.02 G46.03 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `s·l····` | R17, R31 |
| `enumTypes` | types | partial | S00 S01 | G09 G13 G15 | G16 | G25 | G46.01 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `·al····` |  |
| `externalFunctionTypes` | types | partial | S00 S01 S04.03 | G09 G13 G15 | G20 G22.04 | G42.05 | G46.01 G47 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `sal··t·` | R07 |
| `fixedArrays` | types | partial | S00 S01 S04.01 | G09 G13 G15 | G18.02 G18.03 G18.04 G18.05 | G27.03 G32 | G46.02 G46.03 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `sa·b···` | R19, R28 |
| `fixedBytesTypes` | types | partial | S00 S01 | G09 G13 G15 | G16 | G25 | G46.01 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `·al····` | R13 |
| `integerTypes` | types | partial | S00 S01 | G09 G13 G15 | G16 | G25 | G46.01 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `·al·et·` | R12, R13 |
| `internalFunctionTypes` | types | partial | S00 S01 | G09 G13 G15 | G20 | G37.03 | G46.01 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `·al····` |  |
| `mappings` | types | partial | S00 S01 S04.01 | G09 G13 G15 | G18.02 | G27.02 | G46.03 G46.05 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `sa·b···` | R14, R34 |
| `memoryLocation` | types | partial | S01 S04.01 | G09 G13 G15 | G18.03 | G32 G34 | G46.02 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `s··b···` | R01, R02, R25, R31 |
| `recursiveTypes` | types | missing | S00 S01 S04.01 | G09 G13 G15 | G18.01 | G27.04 G35.05 | G46.02 G46.03 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `s······` |  |
| `storageLocation` | types | partial | S01 S04.01 | G09 G13 G15 | G18.02 | G27.01 G27.02 G27.03 G27.04 G27.05 G28 | G46.03 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `s··b·t·` | R09, R34 |
| `stringType` | types | partial | S00 S01 S04.01 | G09 G13 G15 | G18.02 G18.03 G18.04 G18.05 | G27.03 G32 | G46.02 G46.03 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `·al····` | R10, R14, R17 |
| `structTypes` | types | partial | S00 S01 S04.01 | G09 G13 G15 | G18.01 G18.02 G18.03 G18.04 G18.05 | G27.01 G32 | G46.02 G46.03 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `salb···` | R19, R20, R28 |
| `tupleTypes` | types | partial | S00 S01 | G09 G13 G15 | G17 | G26 | G46.01 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `salb···` | R09 |
| `valueTypes` | types | partial | S00 S01 | G09 G13 G15 | G16 | G25 | G46.01 | G48 G49.02 G49.03 G51.01 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `·al····` |  |
| `fixedPoint` | upstream | notApplicable | S00 S01 S02 S04.01 S04.02 | G08 G09 G13 G15 | G16 G18.02 G21 | G25 G27.01 G35.03 G40 G41 | G46.01 G46.02 G46.03 | G48 G49.02 G49.03 (Admission, Lowering, Compilation, Execution, PublicCorrectness) | `·······` |  |

Stages with no owner, by recorded reason: `identifiers` evm: names are resolved before code generation; `comments` lowering: no behaviour beyond token separation (G08 owns the lexer); `comments` backend: erased before lowering; `comments` evm: erased before lowering; `pragmaVersion` lowering: acceptance and provenance only; `pragmaVersion` backend: acceptance only; `pragmaVersion` evm: acceptance only; `pragmaOther` lowering: acceptance and provenance only; `pragmaOther` backend: acceptance only; `pragmaOther` evm: acceptance only; `imports` evm: resolved before code generation; linking is G44.02/G47; `typeValidation` lowering: static checking, carried by G13/G15; `typeValidation` backend: static checking only; `typeValidation` evm: static checking only; `featureDetection` lowering: admission classification only (G15); `featureDetection` backend: admission classification only; `featureDetection` evm: admission classification only.

Split parents in G00's cells, refined to child packages (`REFINE`):

| row | parent | children |
|---|---|---|
| `addressTypes` | G42 | G42.02 G42.05 |
| `arrayLength` | G18 | G18.02 G18.03 G18.04 |
| `bytesConcat` | G35 | G35.03 G35.04 |
| `callOptions` | G22 | G22.01 G22.03 G22.05 |
| `callOptions` | G42 | G42.02 |
| `constructorLifetime` | G44 | G44.01 G44.03 |
| `contracts` | G44 | G44.01 G44.02 |
| `defaultInitialization` | G18 | G18.02 G18.03 |
| `deleteMappingTails` | G29 | G29.02 |
| `doWhileStatement` | G36 | G36.01 G36.02 G36.03 |
| `dynamicArrays` | G18 | G18.02 G18.03 G18.04 G18.05 |
| `dynamicBytesType` | G18 | G18.02 G18.03 G18.04 G18.05 |
| `emptyDataValueCall` | G22 | G22.02 G22.05 |
| `evaluationOrder` | S03 | S03.01 S03.03 |
| `explicitConversions` | G35 | G35.01 G35.02 G35.03 G35.04 |
| `extensionCalls` | G37 | G37.01 |
| `fixedArrays` | G18 | G18.02 G18.03 G18.04 G18.05 |
| `forStatement` | G36 | G36.01 G36.02 G36.03 |
| `freeFunctions` | G37 | G37.01 |
| `functionCalls` | G37 | G37.01 G37.03 |
| `functionCalls` | G42 | G42.01 G42.02 G42.04 |
| `functions` | G37 | G37.01 G37.03 |
| `functions` | S03 | S03.01 S03.03 |
| `implicitConversions` | G35 | G35.01 G35.02 G35.03 G35.04 |
| `indexAccess` | G18 | G18.02 G18.03 G18.04 |
| `interfaces` | G42 | G42.02 G42.05 |
| `internalCalls` | G37 | G37.01 G37.02 |
| `memberAccess` | G18 | G18.02 G18.03 G18.04 |
| `modifiers` | G37 | G37.01 |
| `namedArguments` | G37 | G37.01 |
| `operatorAliases` | G37 | G37.01 |
| `overrideDeclarations` | G37 | G37.03 |
| `referenceCopyRules` | G29 | G29.01 G29.02 G29.03 |
| `referenceCopyRules` | G35 | G35.01 G35.02 G35.03 G35.04 G35.05 G35.06 |
| `returnStatement` | G37 | G37.01 |
| `rollback` | G22 | G22.01 G22.02 G22.03 G22.05 |
| `sendTransfer` | G22 | G22.02 G22.05 |
| `sourceUnits` | G44 | G44.02 |
| `stateMutability` | G22 | G22.01 G22.05 |
| `stateMutability` | G42 | G42.02 G42.05 |
| `stateVariables` | G27 | G27.01 G27.02 G27.03 G27.05 |
| `staticCallRestriction` | G22 | G22.01 G22.04 |
| `storageCopy` | G29 | G29.01 G29.02 G29.03 |
| `storageLocation` | G27 | G27.01 G27.02 G27.03 G27.04 G27.05 |
| `stringConcat` | G35 | G35.03 G35.04 |
| `stringType` | G18 | G18.02 G18.03 G18.04 G18.05 |
| `structDeclarations` | G18 | G18.01 G18.02 G18.03 G18.04 G18.05 |
| `structTypes` | G18 | G18.01 G18.02 G18.03 G18.04 G18.05 |
| `tryStatement` | G22 | G22.01 G22.03 |
| `tryStatement` | G42 | G42.02 G42.06 |
| `usingFor` | G37 | G37.01 G37.03 |
| `valueOption` | G22 | G22.01 G22.03 G22.05 |
| `whileStatement` | G36 | G36.01 G36.02 G36.03 |
| `worldAssumptions` | G22 | G22.02 G22.05 |

### Feature detail

#### abi

- **`abiDecode`** (model/partial)
  - lowering: `Solidity.abiDecodeWith` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:1465`) — decode lowering
  - lowering: `Solidity.abiBounds` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:1318`) — offset/length checks before traversal
  - lowering: `Solidity.abiReadGen` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:1340`) — recursive reader, noncanonical offsets accepted
  - regression: `Solidity.Examples.Tactics.AbiFeatures.byte_roundtrip` (Solidity.Examples.Tactics.AbiFeatures, `Solidity/Examples/Tactics/AbiFeatures.lean:229`) — encode/decode roundtrip
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: Enum decoding is refused ('requires nominal cardinality checks'). Lazy/noncanonical aggregate entry decoding is pending.
  - missing: No backend/EVM stage. Calldata/ABI entry is outside the compiler theorems (R04, R20).

- **`abiEncode`** (model/partial)
  - admission: `Solidity.Frontend.Admission.magicMember` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:27`) — abi.encode tagged
  - lowering: `Solidity.abiWriteGen` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:1196`) — head/tail offset writer
  - lowering: `Solidity.abiEncodeNested?` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:1274`) — recursive shape encoding
  - regression: `Solidity.Examples.Tactics.AbiFeatures.byte_roundtrip` (Solidity.Examples.Tactics.AbiFeatures, `Solidity/Examples/Tactics/AbiFeatures.lean:229`) — decode(encode(x)) == x for uint8
  - no existing anchor: source, backend, evm, theorem
  - missing: ABI is absent from the compiler theorems (R04), with no backend/EVM stage.
  - missing: Internal function markers are refused. Struct enum members lose nominal identity, so recursive coverage is partial.

- **`abiEncodeCall`** (model/partial)
  - lowering: `Solidity.Frontend.abiCallComponents?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1444`) — target/tuple components checked vs declaration
  - lowering: `Solidity.encodeCallTypes?` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:1010`) — exact parameter typing
  - lowering: `Solidity.encodeCallArg` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:1316`) — contextual argument conversions
  - regression: `Solidity.Examples.Tactics.AbiHexCall.exact_hex_valid` (Solidity.Examples.Tactics.AbiHexCall, `Solidity/Examples/Tactics/AbiHexCall.lean:108`) — exact-width hex encodeCall assertion
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: Implicit fixed-byte narrowing is refused. ABI identity of inherited renamed function values is left.
  - missing: No backend/EVM stage (R04).

- **`abiEncodePacked`** (model/partial)
  - admission: `Solidity.Frontend.Admission.magicMember` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:27`) — abi.encodePacked tagged
  - lowering: `Solidity.AbiKind.packedWidth` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:814`) — packed widths per kind
  - lowering: `Solidity.abiEncodeWith` (Solidity.Syntax.Elab.Arms, `Solidity/Syntax/Elab/Arms.lean:639`) — packed assembly, struct refused
  - no existing anchor: source, backend, evm, theorem
  - missing: Packed arrays and hex-literal aggregates have only partial contextual coercions.
  - missing: No backend/EVM stage (R04). Packed collisions are only kept, never proved.

- **`abiEncodeWithSelector`** (model/partial)
  - admission: `Solidity.Frontend.Admission.magicMember` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:27`) — encodeWithSelector tagged
  - lowering: `Solidity.encodeSelector?` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:1556`) — selector-prefix lowering
  - lowering: `Solidity.fnSelector?` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:967`) — function selector computation
  - no existing anchor: source, backend, evm, theorem
  - missing: Selector-prefix lowering supports restricted argument shapes only. Full recursive ABI is unestablished.
  - missing: No backend/EVM stage (R04).

- **`abiEncodeWithSignature`** (model/partial)
  - admission: `Solidity.Frontend.Admission.magicMember` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:27`) — encodeWithSignature tagged
  - source: `Solidity.Keccak.selector` (Solidity.Keccak, `Solidity/Keccak.lean:109`) — bytes4(keccak256(sig))
  - lowering: `Solidity.encodeSelector?` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:1556`) — selector-prefix lowering
  - no existing anchor: backend, evm, theorem
  - missing: Only literal signatures are hashed once at elaboration. Argument shapes are restricted.
  - missing: No backend/EVM stage (R04). The hash is computed concretely with no injectivity claim (correct).

#### builtins

- **`addmodBuiltin`** (model/partial)
  - source: `Solidity.ModOp.evalT` (Solidity.Semantics.Ops, `Solidity/Semantics/Ops.lean:130`) — wide intermediate, zero-modulus failure
  - source: `Solidity.Bridge.Arith.modular_exact` (SolidityBridge.Arith.Modular, `Bridge/SolidityBridge/Arith/Modular.lean:6`) — modular op exactness
  - source: `Solidity.Bridge.Arith.addmod_zmod` (SolidityBridge.Arith.Modular, `Bridge/SolidityBridge/Arith/Modular.lean:21`) — addmod equals ZMod sum
  - regression: `Solidity.Corpus.TestSuite.addmodMulmod` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2390`) — addmod/mulmod corpus
  - no existing anchor: admission, lowering, backend, evm, theorem
  - missing: The compiler refuses modular values (R10: valIn rejects modular).
  - missing: The Panic(0x12) code is erased at the machine (R37). Constant-zero-modulus rejection depends on solc admission only.

- **`assertBuiltin`** (model/partial)
  - source: `Solidity.TRun.assert` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:803`) — false raises panic
  - backend: `Solidity.Evm.assert_sim` (Solidity.Evm.Stmt, `Solidity/Evm/Stmt.lean:332`) — assert simulation
  - source: `Solidity.Bridge.Arith.uintGuard_assert` (SolidityBridge.Arith.NarrowChecked, `Bridge/SolidityBridge/Arith/NarrowChecked.lean:66`) — guard via assert
  - regression: `Solidity.Corpus.TestSuite.testSimpleAssert` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:1405`) — assert corpus case
  - no existing anchor: admission, lowering, evm, theorem
  - missing: Revert data is erased: a failed assert (Panic 0x01) matches a plain machine revert (R37).
  - missing: assert is a core-only construct, refused in memory programs (R29, R01).

- **`bytesConcat`** (model/partial)
  - lowering: `Solidity.Frontend.call` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1798`) — bytes.concat rendered
  - lowering: `Solidity.abiEncode` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:201`) — concat as packed byte write
  - lowering: `Solidity.abiEncodeWith` (Solidity.Syntax.Elab.Arms, `Solidity/Syntax/Elab/Arms.lean:639`) — argument-order byte assembly
  - lowering: `Solidity.bytesPure` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:1507`) — bytesN argument kinds
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: No distinct admission tag (memberAccess only).
  - missing: No backend: dynamic bytes memory objects are outside both compilers (R10 readMem, R28, word memory R31).

- **`ecrecoverBuiltin`** (abstract/partial)
  - source: `Solidity.Secp256k1.recover` (Solidity.Secp256k1, `Solidity/Secp256k1.lean:127`) — bounded recovery, zero on failure
  - source: `Solidity.ecrecoverBytes` (Solidity.Semantics.Heap, `Solidity/Semantics/Heap.lean:514`) — ecrecover interpretation over bytes
  - regression: `Solidity.Examples.Tactics.Recovery.recover_address` (Solidity.Examples.Tactics.Recovery, `Solidity/Examples/Tactics/Recovery.lean:16`) — concrete recovery vector
  - no existing anchor: admission, lowering, backend, evm, theorem
  - missing: General group-law and precompile-equivalence proofs are open. Proofs are concrete vectors only.
  - missing: The compiler refuses hash values (R10), so there is no backend/EVM stage. Signer authorization needs separate premises.

- **`erc7201Builtin`** (model/present)
  - source: `Solidity.ERC7201.root` (Solidity.ERC7201, `Solidity/ERC7201.lean:24`) — namespace formula
  - source: `Solidity.ERC7201.root_aligned` (Solidity.ERC7201, `Solidity/ERC7201.lean:31`) — low byte cleared for all ids
  - lowering: `Solidity.hoistERC7201With` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:1613`) — runtime/literal erc7201 lowering
  - regression: `Solidity.Examples.Tactics.AbiFeaturesImport.namespace_property` (Solidity.Examples.Tactics.AbiFeaturesImport, `Solidity/Examples/Tactics/AbiFeaturesImport.lean:59`) — imported namespace property
  - no existing anchor: admission, backend, evm, theorem
  - missing: No backend/EVM stage: hash values are refused by the compiler (R10).
  - missing: The namespace integer is not linked to physical storage layout, which is intentionally out.

- **`keccakBuiltin`** (abstract/partial)
  - source: `Solidity.Keccak.keccak256` (Solidity.Keccak, `Solidity/Keccak.lean:96`) — executable Keccak-256
  - source: `Solidity.keccakBytes` (Solidity.Semantics.Heap, `Solidity/Semantics/Heap.lean:473`) — hash over memory bytes
  - lowering: `Solidity.hoistHashWith` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:1590`) — hash call hoisting
  - source: `Solidity.Heap.hash` (Solidity.Semantics.Heap, `Solidity/Semantics/Heap.lean:530`) — heap hash interpretation
  - no existing anchor: admission, backend, evm, theorem
  - missing: The compiler refuses hash values (R10). KECCAK256 takes stack inputs, not memory (R35).
  - missing: Symbolic storage slots build in global keccak injectivity (R34), which the roadmap forbids.

- **`mulmodBuiltin`** (model/partial)
  - source: `Solidity.ModOp.wide` (Solidity.Semantics.Ops, `Solidity/Semantics/Ops.lean:124`) — arbitrary-precision intermediate
  - source: `Solidity.Bridge.Arith.mulmod_zmod` (SolidityBridge.Arith.Modular, `Bridge/SolidityBridge/Arith/Modular.lean:32`) — mulmod equals ZMod product
  - regression: `Solidity.Corpus.TestSuite.addmodMulmod` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2390`) — addmod/mulmod corpus
  - no existing anchor: admission, lowering, backend, evm, theorem
  - missing: The compiler refuses modular values (R10). There is no backend or MULMOD opcode bridge.
  - missing: The Panic(0x12) distinction is erased (R37).

- **`requireBuiltin`** (model/partial)
  - source: `Solidity.TRun.require` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:799`) — failure reverts with rollback
  - lowering: `Solidity.RawStmt.requireWith` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:254`) — require with reason lowering
  - backend: `Solidity.Evm.Memory.requireValue_correct` (Solidity.Evm.MemoryStatements, `Solidity/Evm/MemoryStatements.lean:57`) — memory-path require correct
  - regression: `Solidity.Corpus.TestSuite.requireFalseLiteral` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:170`) — failing require reverts
  - no existing anchor: admission, evm, theorem
  - missing: The compiler erases Error(string)/custom-error encodings (R37). require with a custom error uses revertData, which is out (R07).
  - missing: No backend theorem that reason arguments are evaluated when the condition succeeds.

- **`revertBuiltin`** (model/partial)
  - source: `Solidity.RevPart` (Solidity.Syntax.Scoped, `Solidity/Syntax/Scoped.lean:315`) — computed revert data parts
  - source: `Solidity.TRun.revertData` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:948`) — revert data semantics
  - lowering: `Solidity.revertErrParts` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:998`) — custom error encoding lowering
  - source: `Solidity.Semantics.errorSelector` (Solidity.RevertBytes, `Solidity/RevertBytes.lean:24`) — Error(string) selector
  - no existing anchor: admission, backend, evm, theorem
  - missing: revertData/catchData are outside the compiler (R07). Machine revert carries no bytes (R37).
  - missing: Custom errors whose identities share a name need a nominal signature adapter and are refused.

- **`ripemd160Builtin`** (abstract/partial)
  - source: `Solidity.Hashes.ripemd160` (Solidity.Hashes, `Solidity/Hashes.lean:178`) — executable RIPEMD-160
  - source: `Solidity.ripemd160Bytes` (Solidity.Semantics.Heap, `Solidity/Semantics/Heap.lean:495`) — 20-byte result over memory
  - lowering: `Solidity.hoistHashWith` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:1590`) — hash call hoisting
  - no existing anchor: admission, backend, evm, theorem
  - missing: The compiler refuses hash values (R10). There is no precompile bridge.
  - missing: The bytes20 result is right-aligned, unlike solc (R13).

- **`sha256Builtin`** (abstract/partial)
  - source: `Solidity.Hashes.sha256` (Solidity.Hashes, `Solidity/Hashes.lean:97`) — executable SHA-256
  - source: `Solidity.sha256Bytes` (Solidity.Semantics.Heap, `Solidity/Semantics/Heap.lean:490`) — SHA-256 over memory bytes
  - lowering: `Solidity.hoistHashWith` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:1590`) — hash call hoisting
  - no existing anchor: admission, backend, evm, theorem
  - missing: The compiler refuses hash values (R10). There is no precompile bridge or EVM stage.
  - missing: Proofs are concrete reductions only, with no precompile-equivalence theorem.

- **`stringConcat`** (model/partial)
  - lowering: `Solidity.Frontend.call` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1798`) — string.concat rendered
  - lowering: `Solidity.stringReason?` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:862`) — string-only argument check
  - lowering: `Solidity.abiEncode` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:201`) — fresh concatenated bytes
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: No distinct admission tag. Function-value arguments are refused.
  - missing: No backend/EVM coverage for dynamic string memory (R28, R31).

- **`wrapUnwrap`** (model/partial)
  - lowering: `Solidity.Frontend.call` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1798`) — wrap/unwrap rendered as underlying cast
  - lowering: `Solidity.Frontend.valueTypeExpr` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:745`) — UDVT expression typing
  - lowering: `Solidity.valueRows?` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:554`) — UDVT range rows
  - regression: `Solidity.Corpus.TestSuite.valueTypeWrapUnwrap` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2380`) — wrap/unwrap corpus case
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: Admission gives no distinct tag (memberAccess only). Multi-argument wrap/unwrap is refused.
  - missing: UDVTs are erased to uint before the compiler (R13), with no nominal-check theorem. Nominal UDVT slices are refused.

#### calls

- **`callbackSemantics`** (abstract/partial)
  - source: `Solidity.Stmt.callsBack` (Solidity.Semantics.Callback, `Solidity/Semantics/Callback.lean:248`) — statements that may call back
  - source: `Solidity.ExecS` (Solidity.Semantics.Callback, `Solidity/Semantics/Callback.lean:493`) — callback execution relation with invariant
  - theorem: `Solidity.Main.callback_soundness` (Solidity.Theorems, `Solidity/Theorems.lean:226`) — callback-modality calculus soundness
  - theorem: `Solidity.Bridge.Adversary.exec_iff_trace` (SolidityBridge.Adversary, `Bridge/SolidityBridge/Adversary.lean:99`) — adversary LTS matches transfer reading
  - no existing anchor: admission, lowering, backend, evm
  - missing: Adversary boundary covers transfer only, not try, send or whole EVM accounts
  - missing: Callback catches and ownership-aware memory frames remain (calls-exceptions Left)
  - missing: Callee preserving the invariant is assumed, not proved

- **`creationTry`** (abstract/partial)
  - source: `Solidity.ContractWorld.World.tryCreate` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:357`) — creation-frame catch boundary
  - source: `Solidity.ContractWorld.World.tryCreate_argument_failure` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:371`) — argument failures outside catch
  - source: `Solidity.ContractWorld.Operation.tryCreate_caught` (Solidity.Semantics.ContractWorldCertificates, `Solidity/Semantics/ContractWorldCertificates.lean:149`) — caught creation certificate
  - admission: `Solidity.Frontend.elabSolcWorldFactory` (Solidity.Frontend.WorldImport, `Solidity/Frontend/WorldImport.lean:245`) — constant-result try-new fragment
  - no existing anchor: lowering, backend, evm, theorem
  - missing: Only bare catch with constant Boolean results; general typed catches and handler code unsupported
  - missing: Divergence/exhaustion not caught; no compiler/EVM stage

- **`emptyDataValueCall`** (abstract/partial)
  - lowering: `Solidity.Frontend.valueCall?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:2031`) — matches only (bool ok,)=r.call{value:v}("")
  - lowering: `Solidity.elabValueCall` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:617`) — send full-gas / self receive try
  - source: `Solidity.TRun.send` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:723`) — bool result, ledger effect
  - theorem: `Solidity.sendStep_sound` (Solidity.Calculus.SoundControl, `Solidity/Calculus/SoundControl.lean:90`) — covers full-gas send
  - no existing anchor: admission, backend, evm
  - missing: Backend refuses send (R06); no EVM bridge
  - missing: Callbacks only via the ExecS callback modality, not real recipient execution (R33)

- **`extensionCalls`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — UsingForDirective tagged usingFor
  - lowering: `Solidity.Frontend.call` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1798`) — attached free function: receiver as first arg
  - regression: `Solidity.Corpus.TestSuite.libraryCallAndUsingFor` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2375`) — corpus regression
  - no existing anchor: source, backend, evm, theorem
  - missing: Receiver-bound-once is not proved; only internal/free attached functions lowered
  - missing: External-library extension calls need the ContractWorld library abstraction (not integrated)

- **`externalLibraryCalls`** (abstract/partial)
  - admission: `Solidity.Frontend.WorldLinked.read` (Solidity.Frontend.WorldImport, `Solidity/Frontend/WorldImport.lean:310`) — solc_world_library fragment reader
  - source: `Solidity.ContractWorld.World.libraryCall` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:334`) — linked run over caller storage
  - source: `Solidity.ContractWorld.Operation.libraryCall_certificate` (Solidity.Semantics.ContractWorldCertificates, `Solidity/Semantics/ContractWorldCertificates.lean:96`) — library-call operation certificate
  - no existing anchor: lowering, backend, evm, theorem
  - missing: Only one storage root with a literal field assignment; general args and aggregate returns unsupported
  - missing: Pure/view library calls and nested external execution refused; no backend/EVM

- **`externalSelfCalls`** (model/partial)
  - lowering: `Solidity.trySelfBody` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:557`) — self callee inlined in own frame
  - lowering: `Solidity.selfReturnAbiCompatible` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:1676`) — self-return ABI kind check
  - source: `Solidity.TRun.tryCall` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:877`) — self flag: sender=this, value 0
  - regression: `Solidity.Examples.Tactics.TryCatch.selfCall_noCallback` (Solidity.Examples.Tactics.TryCatch, `Solidity/Examples/Tactics/TryCatch.lean:288`) — self-call example proof
  - no existing anchor: admission, backend, evm, theorem
  - missing: Self-call frames fix msg.value to 0; value-carrying self-calls not modelled
  - missing: Only callees declared before the caller; no backend/EVM support (R07)

- **`externalTypedCalls`** (abstract/partial)
  - lowering: `Solidity.extCallStmt` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:1687`) — bare call as try that reverts on failure
  - source: `Solidity.ExtCall` (Solidity.Syntax.Scoped, `Solidity/Syntax/Scoped.lean:237`) — addr, fn, args; no value field
  - source: `Solidity.TRun.tryCall` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:877`) — oracle-table outcomes
  - theorem: `Solidity.Stmt.sound_tryCall` (Solidity.Calculus.SoundCalls, `Solidity/Calculus/SoundCalls.lean:1357`) — sound for every table outcome
  - no existing anchor: admission, backend, evm
  - missing: Admission tags all FunctionCalls as internalCalls; no external-call classification
  - missing: Arbitrary callee code not run; no compiler/EVM support (R07, R33)
  - missing: External aggregate return decoding and static-call world semantics remain

- **`functionValues`** (model/partial)
  - lowering: `Solidity.fnTag` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:114`) — tag encoding of internal function values
  - lowering: `Solidity.fnDispatch` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:271`) — dispatch; unset value gives Panic(0x51)
  - lowering: `Solidity.extDispatch` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:361`) — external function value: address/selector dispatch
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: No source-level function type; identity rules rest on the tag encoding with no theorem
  - missing: Reference-valued function types and functions declared after the caller refused
  - missing: No backend or EVM support

- **`internalCalls`** (model/partial)
  - lowering: `Solidity.elabCall` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:444`) — resolved internal call to Stmt.call
  - source: `Solidity.TRun.call` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:810`) — fresh frame; returns via CallRet
  - backend: `Solidity.Evm.callVal_sim` (Solidity.Evm.Correct, `Solidity/Evm/Correct.lean:517`) — inlined value-arg call simulation
  - theorem: `Solidity.Premise.sound_callVal` (Solidity.Calculus.SoundCalls, `Solidity/Calculus/SoundCalls.lean:432`) — internal call rule sound
  - no existing anchor: admission, evm
  - missing: Calls inlined; only value args and none/val returns (R09); callReceiver refused
  - missing: No runtime call frames or stack-limit behaviour on Machine (R27)

- **`newContract`** (abstract/partial)
  - admission: `Solidity.Frontend.WorldCreation.read` (Solidity.Frontend.WorldImport, `Solidity/Frontend/WorldImport.lean:155`) — solc_world_factory fragment reader
  - source: `Solidity.ContractWorld.World.create` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:203`) — alloc, ctor run, payment, install
  - source: `Solidity.ContractWorld.World.create_ok` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:293`) — successful creation characterised
  - theorem: `Solidity.ContractWorld.World.create_post_of_spec` (Solidity.Calculus.ContractWorld, `Solidity/Calculus/ContractWorld.lean:34`) — Spec proof to creation postcondition
  - no existing anchor: lowering, backend, evm
  - missing: General source new C with dynamic args, ABI/memory transfer and callbacks not integrated into Stmt
  - missing: Creator chooses address; CREATE nonce / CREATE2 not modelled
  - missing: No backend/EVM stage

- **`recursiveCalls`** (model/partial)
  - source: `Solidity.recUnroll` (Solidity.Syntax.Scoped, `Solidity/Syntax/Scoped.lean:461`) — unrolled to recDepth; bottom exhausted
  - source: `Solidity.Stmt.run_callRec` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:1323`) — callRec runs as call
  - theorem: `Solidity.RecContract.unroll` (Solidity.Calculus.Recursion, `Solidity/Calculus/Recursion.lean:171`) — recursive contract by unrolling
  - theorem: `Solidity.sound_recursiveCallUnfold` (Solidity.Calculus.SoundControl, `Solidity/Calculus/SoundControl.lean:458`) — unfold rule sound
  - no existing anchor: admission, lowering, backend, evm
  - missing: Compiler refuses callRec (R08); exhausted never appears in compiler theorems (R39)
  - missing: Fixed 1024 fuel is not unbounded recursion and not gas exhaustion (R08/R27)
  - missing: Imports refuse recursive inlined composite calls (Frontend.reach)

- **`sendTransfer`** (abstract/partial)
  - source: `Solidity.TRun.transfer` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:717`) — transfer reverts on refusal
  - theorem: `Solidity.sendStep_sound` (Solidity.Calculus.SoundControl, `Solidity/Calculus/SoundControl.lean:90`) — send rule: both outcomes
  - backend: `Solidity.Evm.transfer_sim` (Solidity.Evm.Stmt, `Solidity/Evm/Stmt.lean:892`) — transfer compiled; refusal asymmetry
  - theorem: `Solidity.Bridge.Adversary.call_step_sound` (SolidityBridge.Adversary, `Bridge/SolidityBridge/Adversary.lean:199`) — adversarial callee at transfer
  - no existing anchor: admission, lowering, evm
  - missing: send not compiled (R06); payment asymmetry disjunct (R32)
  - missing: Recipient code not run; oracle acceptance only (R33)
  - missing: Bare r.send(a); not read

- **`valueOption`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — FunctionCallOptions value tagged valueOption
  - lowering: `Solidity.elabValueCall` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:617`) — call{value:v}("") to send/self receive try
  - source: `Solidity.State.canPay` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:164`) — funding + oracle acceptance
  - source: `Solidity.State.pay` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:172`) — ledger update on success
  - no existing anchor: backend, evm, theorem
  - missing: ExtCall has no value field, so typed a.f{value:v}() is unsupported
  - missing: Backend refuses send/value calls (R06)
  - missing: Self-call frames fix value to 0

#### declarations

- **`constants`** (model/partial)
  - lowering: `Solidity.Frontend.constVal` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:955`) — evaluates constant initializers
  - lowering: `Solidity.RawExpr.foldConst` (Solidity.Syntax.Elab.Context, `Solidity/Syntax/Elab/Context.lean:474`) — folds constants in sol{}
  - regression: `Solidity.Corpus.TestSuite.constantInlined` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2355`) — constant inlined by identity
  - regression: `Solidity.Corpus.TestSuite.contractQualifiedConstantAndEnum` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2360`) — qualified constant resolved
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: Unsupported constant forms (non-foldable, bytes/string) give diagnostics
  - missing: No theorem that folding preserves contextual width

- **`constructors`** (model/partial)
  - lowering: `Solidity.elabCtor` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:664`) — runs initializers then constructor body
  - lowering: `Solidity.Frontend.renderInitializers` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:728`) — state initializers in declaration order
  - theorem: `Solidity.Problem.deploy_of_valid` (Solidity.Calculus.Deploy, `Solidity/Calculus/Deploy.lean:60`) — deployment obligation soundness
  - regression: `Solidity.Examples.Tactics.ContractWorld.failed_constructor_payment_rollback` (Solidity.Examples.Tactics.ContractWorld, `Solidity/Examples/Tactics/ContractWorld.lean:157`) — failed constructor rolls back payment
  - no existing anchor: source, admission, backend, evm
  - missing: No compiled deployment or creation code: compiler theorems exclude constructors (R04)
  - missing: Unsupported initializers leave a refused constructor row
  - missing: Pipeline-specific init ordering is an integration dependency

- **`contracts`** (model/partial)
  - lowering: `Solidity.Frontend.readContract` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:805`) — solc ContractDefinition into intrinsic Contract
  - source: `Solidity.Contract` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:404`) — intrinsic contract: roots, funs, ctor, inits, errors
  - source: `Solidity.State.deploy` (Solidity.Semantics.Deploy, `Solidity/Semantics/Deploy.lean:20`) — deployment state
  - regression: `Solidity.Examples.Tactics.Contracts.callAddOne` (Solidity.Examples.Tactics.Contracts, `Solidity/Examples/Tactics/Contracts.lean:52`) — contract function call obligation
  - no existing anchor: admission, backend, evm, theorem
  - missing: Backend theorems cover Prog only: no contract, dispatch, ABI or transaction (R04)
  - missing: No bytecode-level claim (R05)
  - missing: Abstract vs deployable is checked only at import; abstract .interfaceId refused

- **`enumDeclarations`** (model/partial)
  - source: `Solidity.enumRows` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:548`) — enum ordinal rows
  - lowering: `Solidity.enumLit?` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:50`) — enum member to uint ordinal
  - regression: `IRLocal_checked` (tests.upstream.EnumBounds, `tests/upstream/EnumBounds.lean:30`) — enum conversion bounds checked (viaIR)
  - regression: `Solidity.Examples.Tactics.CallExceptions.exact_enum` (Solidity.Examples.Tactics.CallExceptions, `Solidity/Examples/Tactics/CallExceptions.lean:102`) — exact enum range result
  - no existing anchor: admission, backend, evm, theorem
  - missing: Enums erased to uint (R13); nominal enums Left
  - missing: Composite ABI inputs with enums refused until recursive cardinality checks
  - missing: Enum conversions need identity-safe enum model names

- **`errorDeclarations`** (model/partial)
  - lowering: `Solidity.Frontend.selectErrorDeclarations` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:777`) — selects errors by declaration ID
  - lowering: `Solidity.revertErrParts` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:998`) — encodes custom error revert data
  - regression: `Solidity.Examples.Tactics.SourceUnitsImport.qualified_errors` (Solidity.Examples.Tactics.SourceUnitsImport, `Solidity/Examples/Tactics/SourceUnitsImport.lean:105`) — qualified error signatures kept
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: revert with data out of backend (R07 revertData)
  - missing: Conflicting/nominal errors sharing a short name refused
  - missing: Error ABI with enums gated (errorAbiHasEnum)

- **`eventDeclarations`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — EventDefinition/EmitStatement classified
  - lowering: `Solidity.Frontend.stmt1` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:2202`) — emit checked against resolved event
  - regression: `Solidity.Examples.Tactics.CallExceptions.event_argument_panics` (Solidity.Examples.Tactics.CallExceptions, `Solidity/Examples/Tactics/CallExceptions.lean:49`) — event argument evaluation can panic
  - no existing anchor: source, backend, evm, theorem
  - missing: Logs dropped: no log observation (by design)
  - missing: Indexed/anonymous metadata not kept in the intrinsic model

- **`fallbackFunction`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — fallback kind maps to fallbackFunction
  - source: `Solidity.SourceCallable` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:301`) — fallback callable role
  - lowering: `Solidity.Frontend.tagOf` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:135`) — fallback has no transaction obligation
  - no existing anchor: backend, evm, theorem
  - missing: Byte-oriented fallback(bytes) needs raw calldata/returndata (excluded)
  - missing: Inherited fallback dispatch refused; no world registration
  - missing: No theorem on fallback execution

- **`freeFunctions`** (model/partial)
  - source: `Solidity.SourceLocalVisibility` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:281`) — freeFn visibility without receiver
  - lowering: `Solidity.Frontend.call` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1798`) — resolves free/imported functions by ID
  - regression: `Solidity.Corpus.TestSuite.fileLevelConstantEnumAndFunction` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2365`) — file-level function call proved
  - no existing anchor: admission, backend, evm, theorem
  - missing: Same inline-call backend limits as functions (R08/R09)
  - missing: Namespace-qualified calls need module-alias adapters (sourceUnits gaps)

- **`functions`** (model/partial)
  - source: `Solidity.FunDecl` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:345`) — params, named returns, modifiers, payable
  - lowering: `Solidity.Frontend.SolcFun.member` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:612`) — solc function into model member
  - backend: `Solidity.Evm.call_family` (Solidity.Evm.Correct, `Solidity/Evm/Correct.lean:857`) — inlined internal calls compile correctly
  - regression: `Solidity.Corpus.TestSuite.overloadedInternalCall` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2275`) — overload resolution by solc identity
  - no existing anchor: admission, evm, theorem
  - missing: Backend: value arguments only, return shapes none/val only (R09)
  - missing: Recursive calls out (callRec, R08); source unrolled to depth 1024
  - missing: No external entry/ABI dispatch in compiler theorems (R04)

- **`immutables`** (model/partial)
  - lowering: `Solidity.Frontend.renderInitializers` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:728`) — folds literal immutables, others keep root
  - lowering: `Solidity.Frontend.readContract` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:805`) — refuses unwritten or early-read immutables
  - source: `Solidity.Contract.deployT` (Solidity.Semantics.Deploy, `Solidity/Semantics/Deploy.lean:28`) — deployment writes roots
  - no existing anchor: admission, backend, evm, theorem
  - missing: A logical root does not forbid later writes; no write-once theorem
  - missing: Initializer reaching an uninitialised immutable refused
  - missing: No runtime-code embedding: no deployment backend (R04)

- **`imports`** (model/partial)
  - admission: `Solidity.Frontend.Source.checkTree` (Solidity.Frontend.SourceUnits, `Solidity/Frontend/SourceUnits.lean:31`) — validates resolved import path/source-ID pairs
  - lowering: `Solidity.Frontend.errorAliasScope?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1237`) — resolves import alias scope for errors
  - lowering: `Solidity.Frontend.errorNamespace` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1222`) — module/contract namespace of a declaration
  - regression: `Solidity.Examples.Tactics.SourceUnitsImport.aliased_errors` (Solidity.Examples.Tactics.SourceUnitsImport, `Solidity/Examples/Tactics/SourceUnitsImport.lean:124`) — aliased imported errors keep signature
  - no existing anchor: source, backend, theorem
  - missing: Remapping and resolution are delegated to solc; no Lean model
  - missing: Module-valued expressions outside the checked discard shape refused
  - missing: Conflicting short-named custom errors across imports refused

- **`inheritance`** (model/partial)
  - lowering: `Solidity.Frontend.mergeC3` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:597`) — C3 merge for linearization
  - lowering: `Solidity.Frontend.contractLineage` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:626`) — uses solc linearizedBaseContracts
  - regression: `Solidity.Examples.Tactics.Inheritance.diamond_initialization` (Solidity.Examples.Tactics.Inheritance, `Solidity/Examples/Tactics/Inheritance.lean:21`) — diamond base init order
  - regression: `Solidity.Examples.Tactics.Inheritance.base_constructors` (Solidity.Examples.Tactics.Inheritance, `Solidity/Examples/Tactics/Inheritance.lean:49`) — base constructors run once
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: Inherited receive/fallback/modifier payment dispatch refused
  - missing: Mixed-ABI-coder legacy units with inheritance refused
  - missing: Virtual dispatch resolved statically at import; no backend dispatch (R04)

- **`interfaces`** (model/partial)
  - lowering: `Solidity.Frontend.declarationMetadata` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1059`) — interface metadata (own external selectors)
  - regression: `Solidity.Examples.Tactics.DeclarationMetadata.ownInterface` (Solidity.Examples.Tactics.DeclarationMetadata, `Solidity/Examples/Tactics/DeclarationMetadata.lean:23`) — interfaceId excludes inherited members
  - regression: `Solidity.Examples.Tactics.PublicGetters.interfaceOverride` (Solidity.Examples.Tactics.PublicGetters, `Solidity/Examples/Tactics/PublicGetters.lean:28`) — getter overriding interface function
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: External calls through interfaces are outside the backend fragment (R07 tryCall)
  - missing: No theorem that interface members have no bodies or that inherited members are kept

- **`libraries`** (model/partial)
  - lowering: `Solidity.Frontend.elabSolcWorldLibrary` (Solidity.Frontend.WorldImport, `Solidity/Frontend/WorldImport.lean:405`) — imports linked library into contract world
  - source: `Solidity.ContractWorld.World.libraryCall` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:334`) — linked library call with caller storage
  - source: `Solidity.ContractWorld.Operation.libraryCall_certificate` (Solidity.Semantics.ContractWorldCertificates, `Solidity/Semantics/ContractWorldCertificates.lean:96`) — library call certificate
  - regression: `Solidity.Corpus.TestSuite.libraryCallAndUsingFor` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2375`) — inlined internal library call proved
  - no existing anchor: admission, backend, evm, theorem
  - missing: ContractWorld library execution has no compiler/EVM bridge (R04)
  - missing: Receiver-style library calls (callReceiver) out of backend (R09)
  - missing: Direct library calls and `new Library` rejected (examples library_direct_call_rejected/library_new_rejected)

- **`modifierPlaceholder`** (model/partial)
  - lowering: `Solidity.RawStmt.fillHole` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:550`) — substitutes function body at each _
  - lowering: `Solidity.RawStmt.hasHole` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:545`) — requires a placeholder
  - regression: `Solidity.Corpus.TestSuite.modifierSkippedPlaceholder` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2435`) — placeholder that is not run
  - regression: `Solidity.Tests.ModifierFrameProofs.multi_ir` (tests.upstream.ModifierFrameProofs, `tests/upstream/ModifierFrameProofs.lean:23`) — repeated placeholder frames (viaIR)
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: The no-placeholder-in-unchecked rule is solc's alone
  - missing: Multiple placeholders duplicate inlined code; no correctness theorem for it

- **`modifiers`** (model/partial)
  - source: `Solidity.ModApp` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:268`) — modifier application: params, args, body
  - lowering: `Solidity.wrapMods` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:646`) — inlines modifiers, first listed outermost
  - lowering: `Solidity.modifierFrame` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:611`) — separate per-application frames (viaIR)
  - regression: `Solidity.Corpus.TestSuite.modifierFirstListedOutermost` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2290`) — modifier nesting order proved
  - no existing anchor: admission, backend, evm, theorem
  - missing: Receive modifiers refused
  - missing: Inlined bodies with loops/calls hit backend limits (R01/R08/R09)
  - missing: No general theorem that wrapMods preserves semantics

- **`operatorAliases`** (model/partial)
  - lowering: `Solidity.Frontend.operatorAlias?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:762`) — resolves UDVT operator to pure free function
  - regression: `Solidity.Examples.Tactics.OperatorAliasesImport.legacy_numeric` (Solidity.Examples.Tactics.OperatorAliasesImport, `Solidity/Examples/Tactics/OperatorAliasesImport.lean:39`) — aliased numeric ops (legacy)
  - regression: `Solidity.Examples.Tactics.OperatorAliasesImport.viaIR_order` (Solidity.Examples.Tactics.OperatorAliasesImport, `Solidity/Examples/Tactics/OperatorAliasesImport.lean:133`) — evaluation order (viaIR)
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: Aggregate/UDVT-field shapes and general dispatch Left
  - missing: Failure order outside argument lists unchanged

- **`overrideDeclarations`** (model/partial)
  - lowering: `Solidity.Frontend.overrideAliases` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:583`) — maps overridden declarations to their selected body
  - source: `Solidity.SourceSelection` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:291`) — selected vs retained base bodies
  - lowering: `Solidity.Frontend.isSuperMember` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1311`) — super calls reach retained base body
  - no existing anchor: admission, backend, evm, theorem
  - missing: Override validity is solc's; no Lean check
  - missing: Renamed inherited external function values refused (model-name hashing)
  - missing: No theorem on selected implementation

- **`publicGetters`** (model/partial)
  - lowering: `Solidity.Frontend.publicGetterPlan` (Solidity.Frontend.SolcJson.Getters, `Solidity/Frontend/SolcJson/Getters.lean:243`) — synthesizes getter params/results
  - lowering: `Solidity.Frontend.publicGetterIdentity` (Solidity.Frontend.SolcJson.Getters, `Solidity/Frontend/SolcJson/Getters.lean:252`) — getter ABI identity
  - regression: `Solidity.Examples.Tactics.PublicGetters.scalar_exec` (Solidity.Examples.Tactics.PublicGetters, `Solidity/Examples/Tactics/PublicGetters.lean:288`) — scalar getter execution
  - regression: `Solidity.Examples.Tactics.PublicGetters.storedGetterSelector` (Solidity.Examples.Tactics.PublicGetters, `Solidity/Examples/Tactics/PublicGetters.lean:137`) — getter selector stored
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: Enum-valued, contract/function, bytes/string, nested aggregate results refused
  - missing: Reference-valued getters need world return interface
  - missing: Getters run via external self calls, outside backend (R07)

- **`receiveFunction`** (model/partial)
  - lowering: `Solidity.Frontend.tagOf` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:135`) — receive/fallback classified as internal entries
  - source: `Solidity.SourceCallable` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:301`) — receive callable role
  - lowering: `Solidity.receiveSelfBody` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:590`) — self-payment runs receive body
  - regression: `Solidity.Examples.Tactics.SelfCall.receiveRuns` (Solidity.Examples.Tactics.SelfCall, `Solidity/Examples/Tactics/SelfCall.lean:185`) — receive body runs on self-payment
  - no existing anchor: admission, backend, evm, theorem
  - missing: Inherited receive and receive modifiers refused
  - missing: No transaction entry/dispatch in backend (R04); send/value calls out (R06)
  - missing: Recipient code not run by the machine oracle (R33)

- **`sourceUnits`** (model/partial)
  - admission: `Solidity.Frontend.Source.readCompilationUnit` (Solidity.Frontend.SourceUnits, `Solidity/Frontend/SourceUnits.lean:63`) — reads multi-source compilation unit
  - admission: `Solidity.Frontend.Source.checkTree` (Solidity.Frontend.SourceUnits, `Solidity/Frontend/SourceUnits.lean:31`) — checks source IDs and import pairs
  - admission: `Solidity.Frontend.Source.SourceFile` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:106`) — per-file SHA and pragma metadata
  - regression: `Solidity.Examples.Tactics.SourceUnitsImport.normal_legacy` (Solidity.Examples.Tactics.SourceUnitsImport, `Solidity/Examples/Tactics/SourceUnitsImport.lean:44`) — multi-unit import executes (legacy)
  - no existing anchor: source, lowering, backend, evm, theorem
  - missing: Schema 2 requires multiple units; one-source self-import provenance unfinished
  - missing: Schema-2 static compiler-code artifacts unfinished
  - missing: File-local spec namespace adapter missing

- **`stateMutability`** (model/partial)
  - source: `Solidity.SourceMutability` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:295`) — nonpayable/pure/view/payable
  - source: `Solidity.Mutability` (Solidity.AST, `Solidity/AST.lean:1240`) — intrinsic mutability
  - source: `Solidity.nonpayable_of_within'` (Solidity.Semantics.RunFrame, `Solidity/Semantics/RunFrame.lean:208`) — nonpayable payment guard
  - evm: `Solidity.Evm.External.callvalue_upstream` (SolidityBridge.ExternalEvm.Environment, `Bridge/SolidityBridge/ExternalEvm/Environment.lean:114`) — CALLVALUE agrees with upstream
  - no existing anchor: admission, lowering, backend, theorem
  - missing: Mutability erased in function types (declarations-metadata Left)
  - missing: Payment asymmetry: pays and revert disjunct; bridge needs pays=false (R32)
  - missing: view/pure are not statically checked in Lean

- **`stateVariables`** (model/partial)
  - source: `Solidity.Contract` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:404`) — typed storage roots with okDeep defaults
  - backend: `Solidity.Evm.rootSlot` (Solidity.Evm.Layout, `Solidity/Evm/Layout.lean:78`) — root slot layout
  - backend: `Solidity.Evm.initStorage_repr` (Solidity.Evm.Repr, `Solidity/Evm/Repr.lean:1016`) — zero-initialised storage is represented
  - backend: `Solidity.Evm.compile_storage` (Solidity.Evm.Correct, `Solidity/Evm/Correct.lean:1197`) — compiled storage effects correct
  - no existing anchor: admission, lowering, evm, theorem
  - missing: Logical slot layout, not solc slots/packing (T21 no_injective_slot_encoding)
  - missing: Mapping keys uint only (R14); dynamic copies (R17)
  - missing: Initializers run only via the source constructor, not compiled

- **`structDeclarations`** (model/partial)
  - lowering: `Solidity.Frontend.readStructs` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:493`) — imports struct members in order
  - source: `Solidity.TypeGraph.Schema.no_inline_cycle` (Solidity.TypeGraph, `Solidity/TypeGraph.lean:143`) — no inline recursive struct cycle
  - backend: `Solidity.Evm.size_struct` (Solidity.Evm.Layout, `Solidity/Evm/Layout.lean:130`) — storage struct layout size
  - backend: `Solidity.Evm.Memory.readField_correct` (Solidity.Evm.MemoryStruct, `Solidity/Evm/MemoryStruct.lean:75`) — memory field read correct
  - no existing anchor: admission, evm, theorem
  - missing: Recursive struct shapes are ordinary-model exclusions
  - missing: Reference-member struct construction/defaults absent (R28); limited copies (R20)
  - missing: UDVT struct fields and aggregate shapes Left

- **`usingFor`** (model/partial)
  - lowering: `Solidity.Frontend.call` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1798`) — attached calls bind receiver once
  - regression: `Solidity.Corpus.TestSuite.libraryCallAndUsingFor` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2375`) — using-for call proved
  - regression: `Solidity.Corpus.TestSuite.fileLevelStructThroughLibrary` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2370`) — file struct through library
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: Broader using-for (global, type-specific) Left
  - missing: Receiver-style calls out of backend (R09 callReceiver)
  - missing: Ambiguous same-scope overloads rejected

- **`valueTypeDeclarations`** (model/partial)
  - lowering: `Solidity.Frontend.valueTypeExpr` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:745`) — UDVT wrap/unwrap lowering
  - source: `Solidity.valueRows?` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:554`) — underlying width/sign rows
  - regression: `Solidity.Corpus.TestSuite.valueTypeWrapUnwrap` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2380`) — wrap/unwrap proved
  - no existing anchor: admission, backend, evm, theorem
  - missing: Nominal identity erased below lowering; no type-preservation theorem
  - missing: UDVT fields and aggregate shapes Left; UDVT compound assignment rejected

- **`visibility`** (model/partial)
  - source: `Solidity.SourceAbiVisibility` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:286`) — public vs external
  - source: `Solidity.SourceFunction.externalEntry` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:333`) — selected ABI entries only
  - lowering: `Solidity.Frontend.tagOf` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:135`) — visibility decides obligation tag
  - no existing anchor: admission, backend, evm, theorem
  - missing: Access enforcement is solc's; no Lean check
  - missing: No external dispatch in backend (R04)
  - missing: Remaining visibility distinctions listed as Left in declarations-metadata.md

#### environment

- **`addressBalance`** (abstract/partial)
  - source: `Solidity.State.envVal` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:155`) — address(this).balance from selfBalance
  - source: `Solidity.ContractWorld.World.balance` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:72`) — arbitrary-address balance at world API
  - backend: `Solidity.Evm.simpleIn` (Solidity.Evm.Compile, `Solidity/Evm/Compile.lean:104`) — compiler refuses selfBalance read (R11)
  - evm: `Solidity.Evm.External.selfbalance_upstream` (SolidityBridge.ExternalEvm.Environment, `Bridge/SolidityBridge/ExternalEvm/Environment.lean:72`) — SELFBALANCE agrees with EvmYul
  - no existing anchor: admission, lowering, theorem
  - missing: address(this).balance not compiled (R11, selfBalance_out)
  - missing: Arbitrary-address balances not in source expressions; world API only
  - missing: Compiler theorems assume balance = bal self and balance < W

- **`blockTimestamp`** (abstract/present)
  - admission: `Solidity.Frontend.Admission.magicMember` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:27`) — block.timestamp tagged
  - source: `Solidity.State.envVal` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:155`) — reads tx.timestamp
  - source: `Solidity.ContractWorld.World.atTime` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:75`) — world timestamp setter
  - evm: `Solidity.Evm.External.timestamp_upstream` (SolidityBridge.ExternalEvm.Environment, `Bridge/SolidityBridge/ExternalEvm/Environment.lean:80`) — TIMESTAMP agrees with EvmYul
  - no existing anchor: lowering, backend, theorem
  - missing: No monotonicity/accuracy premises exist; timestamp is an unconstrained word
  - missing: compile_storage fixes timestamp to 0 at fresh start (T6)

- **`msgSender`** (abstract/present)
  - admission: `Solidity.Frontend.Admission.magicMember` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:27`) — msg.sender tagged msgSender
  - source: `Solidity.State.envVal` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:155`) — reads tx.msgSender
  - backend: `Solidity.Evm.Sim.env` (Solidity.Evm.Sim, `Solidity/Evm/Sim.lean:1119`) — env word simulation (CALLER)
  - evm: `Solidity.Evm.External.caller_upstream` (SolidityBridge.ExternalEvm.Environment, `Bridge/SolidityBridge/ExternalEvm/Environment.lean:102`) — CALLER agrees with EvmYul
  - no existing anchor: lowering, theorem
  - missing: compile_storage fixes caller to 0 at the fresh start state (T6)
  - missing: Addresses are 256-bit words, not 160-bit truncated (R27)

- **`msgValue`** (abstract/partial)
  - source: `Solidity.State.transactionEntry` (Solidity.Semantics.State, `Solidity/Semantics/State.lean:155`) — transaction entry state
  - source: `Solidity.ContractWorld.Context.value` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:97`) — per-frame value in world
  - backend: `Solidity.Evm.Sim.env` (Solidity.Evm.Sim, `Solidity/Evm/Sim.lean:1119`) — CALLVALUE word simulation
  - evm: `Solidity.Evm.External.callvalue_upstream` (SolidityBridge.ExternalEvm.Environment, `Bridge/SolidityBridge/ExternalEvm/Environment.lean:114`) — CALLVALUE agrees with EvmYul
  - no existing anchor: admission, lowering, theorem
  - missing: Self-call frames set value to 0; value-carrying self/callback frames unmodelled
  - missing: Payable entry check and ledger assumptions only at the ContractWorld API

- **`thisAddress`** (abstract/partial)
  - admission: `Solidity.Frontend.Admission.builtinFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:87`) — this tagged thisAddress
  - source: `Solidity.TTx` (Solidity.Semantics.State, `Solidity/Semantics/State.lean:105`) — selfAddress field
  - source: `Solidity.ContractWorld.Address` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:28`) — 160-bit bounded addresses in world
  - evm: `Solidity.Evm.External.address_upstream` (SolidityBridge.ExternalEvm.Environment, `Bridge/SolidityBridge/ExternalEvm/Environment.lean:90`) — ADDRESS agrees with EvmYul
  - no existing anchor: lowering, backend, theorem
  - missing: Contract value vs external dispatch only via the selector encoding (extDispatch)
  - missing: Machine addresses not truncated to 160 bits (R27)

#### expressions

- **`arithmetic`** (model/partial)
  - source: `Solidity.BinOp.evalNum` (Solidity.Semantics.Ops, `Solidity/Semantics/Ops.lean:74`) — checked/wrapping/signed div-mod semantics
  - backend: `Solidity.Evm.val_sim` (Solidity.Evm.Expr, `Solidity/Evm/Expr.lean:255`) — compiled expression simulation
  - source: `Solidity.Bridge.Arith.uint_checked_all_widths` (SolidityBridge.Arith.NarrowChecked, `Bridge/SolidityBridge/Arith/NarrowChecked.lean:274`) — checked uint ops all widths
  - theorem: `Solidity.Main.compiler_correct` (Solidity.Theorems, `Solidity/Theorems.lean:269`) — public compiler correctness
  - no existing anchor: admission, lowering, evm
  - missing: Signed `**` is refused by the source (R12). Narrow widths reach the compiler as uint, so correctness rests on lowering (R13).
  - missing: Target is the word-level macro Machine, not EVM bytecode (R05). Panic codes are erased (R37).

- **`assignment`** (model/partial)
  - lowering: `Solidity.hoistAssign` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:126`) — rhs/lhs capture scheduling
  - source: `Solidity.TRun.assign` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:640`) — typed assignment semantics
  - backend: `Solidity.Evm.assign_sim` (Solidity.Evm.Stmt, `Solidity/Evm/Stmt.lean:191`) — storage assignment simulation
  - regression: `Solidity.Corpus.TestSuite.storageAssignmentValueRhsBeforeIndex` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:300`) — rhs before index order
  - no existing anchor: admission, evm, theorem
  - missing: Storage-to-storage copies are compiled only for static types (R17). Memory→storage and fixed copies are out (R19).
  - missing: Memory-path copies are limited to primitive-member storage structs (R20).

- **`bitwise`** (model/partial)
  - source: `Solidity.Semantics.uintBitwise` (Solidity.Semantics.Ops, `Solidity/Semantics/Ops.lean:39`) — finite-width bitwise semantics
  - backend: `Solidity.Evm.binInFrag` (Solidity.Evm.Layout, `Solidity/Evm/Layout.lean:410`) — & | ^ compiled only at uint
  - source: `Solidity.Bridge.Arith.int_band_all_widths` (SolidityBridge.Arith.NarrowBitwise, `Bridge/SolidityBridge/Arith/NarrowBitwise.lean:33`) — signed AND all widths
  - evm: `Solidity.Evm.External.and_step` (SolidityBridge.ExternalEvm, `Bridge/SolidityBridge/ExternalEvm.lean:98`) — AND agrees with reference EVM
  - no existing anchor: admission, lowering, theorem
  - missing: The compiler refuses signed &,|,^ although the source accepts them (R12).
  - missing: bytesN is right-aligned, unlike solc (R13), so bytesN-vs-integer typing is not preserved at the backend.

- **`callOptions`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — splits gas/salt/value options
  - lowering: `Solidity.Frontend.valueCall?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:2031`) — R.call{value:V}("") recognized
  - source: `Solidity.TRun.send` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:723`) — value transfer semantics
  - no existing anchor: backend, evm, theorem
  - missing: The compiler refuses send and value calls (R06).
  - missing: Only the empty-calldata {value:} call shape is lowered. Value on general external calls is not modelled.
  - missing: Recipient code is not run, and acceptance is an oracle (R33).

- **`comparisons`** (model/partial)
  - source: `Solidity.BinOp.evalBool` (Solidity.Semantics.Ops, `Solidity/Semantics/Ops.lean:102`) — typed comparison semantics
  - backend: `Solidity.Evm.scmp_tail` (Solidity.Evm.Signed, `Solidity/Evm/Signed.lean:160`) — signed compare code tail
  - source: `Solidity.Bridge.Arith.int_lt_all_widths` (SolidityBridge.Arith.Comparison, `Bridge/SolidityBridge/Arith/Comparison.lean:77`) — signed < all widths
  - evm: `Solidity.Evm.External.slt_step` (SolidityBridge.ExternalEvm.SignedOps, `Bridge/SolidityBridge/ExternalEvm/SignedOps.lean:42`) — SLT agrees with reference EVM
  - no existing anchor: admission, lowering, theorem
  - missing: Comparisons of address/bytesN/enum/function values rest on uint lowering (R13), with no nominal legality theorem.

- **`compoundAssignment`** (model/partial)
  - source: `Solidity.compoundT` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:225`) — old value read, declared width
  - lowering: `Solidity.elabOpTarget` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:661`) — target captured once
  - backend: `Solidity.Evm.opStore_sim` (Solidity.Evm.Stmt, `Solidity/Evm/Stmt.lean:364`) — storage op-assign simulation
  - backend: `Solidity.Evm.Memory.compoundAssign_eq_write` (Solidity.Evm.MemoryCompound, `Solidity/Evm/MemoryCompound.lean:75`) — memory compound as write
  - no existing anchor: admission, evm, theorem
  - missing: Intrinsic opAssign covers only + - * / % (BinOp.hasCompoundAssign). &=, |=, <<=, >>= have no intrinsic form.
  - missing: pushOpAssign (arr.push() += 1) is refused (R18). Compound storage updates inside memory programs are refused (R29).

- **`conditional`** (model/partial)
  - source: `Solidity.Val` (Solidity.Syntax.Scoped, `Solidity/Syntax/Scoped.lean:77`) — Val.ternary evaluates one arm
  - lowering: `Solidity.mobileTy` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:1145`) — inferred mobile type of arms
  - backend: `Solidity.Evm.Memory.conditionalValue_correct` (Solidity.Evm.MemoryExpr, `Solidity/Evm/MemoryExpr.lean:167`) — conditional code correct
  - regression: `Solidity.Corpus.TestSuite.mappingPointerTernary` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:1560`) — reference-valued arms
  - no existing anchor: admission, evm, theorem
  - missing: Reference-valued ternary arms are not compiled (Val.ternary is primitive-only, memory reference paths R28).
  - missing: Side-effecting arms rely on hoisting to if/else. There is no backend theorem for that lowering.

- **`deleteExpression`** (model/partial)
  - source: `Solidity.TRun.clearT` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:762`) — typed reset of target
  - backend: `Solidity.Evm.delete_sim` (Solidity.Evm.Stmt, `Solidity/Evm/Stmt.lean:867`) — storage delete simulation
  - backend: `Solidity.Evm.Memory.deleteStruct_correct` (Solidity.Evm.MemoryStructDefault, `Solidity/Evm/MemoryStructDefault.lean:155`) — memory struct delete correct
  - regression: `Solidity.Corpus.TestSuite.testDeleteKeepsMappingElementEntries` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:1320`) — mappings survive delete
  - no existing anchor: admission, lowering, evm, theorem
  - missing: Core loops that delete or shrink are refused (R21). Storage delete inside memory programs is refused (R29).
  - missing: Delete of reference-element memory arrays is outside the memory path (R28).

- **`explicitConversions`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — typeConversion tagged explicitConversions
  - lowering: `Solidity.Frontend.sourceCast` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:282`) — renders solc casts
  - lowering: `Solidity.castCapture` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:1823`) — truncation/sign-extension capture
  - lowering: `Solidity.Bridge.Arith.castCapture_typed` (SolidityBridge.Arith.Lowering, `Bridge/SolidityBridge/Arith/Lowering.lean:87`) — cast lowering typed/correct
  - no existing anchor: source, backend, evm, theorem
  - missing: Enum conversions without validated native declaration identity are refused.
  - missing: bytesN alignment differs from solc (R13). Addresses are not truncated to 160 bits (R27).

- **`functionCalls`** (model/partial)
  - lowering: `Solidity.hoistCallArgs` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:209`) — arguments evaluated once, left to right
  - source: `Solidity.TRun.call` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:810`) — fresh call frame semantics
  - backend: `Solidity.Evm.compileStmt` (Solidity.Evm.Compile, `Solidity/Evm/Compile.lean:433`) — inline-call compilation
  - regression: `Solidity.Corpus.TestSuite.internalCallInExpression` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2150`) — call in expression proved
  - no existing anchor: admission, evm, theorem
  - missing: Calls compile inline with value arguments only, and receiver calls are out (R09). Recursion is out (R08).
  - missing: External calls/try (R07) and whole-contract dispatch (R04) have no backend theorem.

- **`implicitConversions`** (model/partial)
  - lowering: `Solidity.Frontend.tyOf` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:417`) — reads solc resolved types
  - lowering: `Solidity.intTyOf` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:1157`) — operand width inference
  - lowering: `Solidity.widenBytes` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:1457`) — fixed-bytes widening
  - source: `Solidity.Bridge.Arith.Widths.unsigned_widen` (SolidityBridge.Arith.Widths, `Bridge/SolidityBridge/Arith/Widths.lean:571`) — unsigned widening preserved
  - no existing anchor: admission, backend, evm, theorem
  - missing: No theorem that elaborated widths equal solc's resolved type before enclosing operations. Correctness rests on lowering (R13).
  - missing: Implicit fixed-byte narrowing in encodeCall and aggregate contextual coercions (hex arrays) are refused.

- **`increments`** (model/partial)
  - source: `Solidity.OpLoc.bumpT` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:430`) — old/new value bump at lvalue
  - lowering: `Solidity.elabIncTarget` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:688`) — target captured once
  - backend: `Solidity.Evm.bumpStore_sim` (Solidity.Evm.Stmt, `Solidity/Evm/Stmt.lean:447`) — storage increment simulation
  - backend: `Solidity.Evm.Memory.incrementMemory_eq_compound` (Solidity.Evm.MemoryCompound, `Solidity/Evm/MemoryCompound.lean:117`) — memory increment as compound write
  - no existing anchor: admission, evm, theorem
  - missing: arr.push()++ (pushIncDec) and x = arr.push() forms are refused by the core compiler (R18).
  - missing: Mixed storage/memory programs are refused (R29). Loops with pushes are refused (R21).

- **`indexAccess`** (model/partial)
  - source: `Solidity.IndexTy` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:758`) — mapping/array index typing
  - source: `Solidity.Loc.resolveT` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:271`) — index resolution with bounds failure
  - backend: `Solidity.Evm.Memory.readArray_correct` (Solidity.Evm.Memory, `Solidity/Evm/Memory.lean:102`) — memory array index read correct
  - regression: `Solidity.Corpus.TestSuite.storageIndexArrayReadOutOfBoundsReverts` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:70`) — out-of-bounds read reverts
  - no existing anchor: admission, lowering, evm, theorem
  - missing: Compiler mapping keys are uint only (R14). Hashed string/bytes keys are refused through R10.
  - missing: Memory reads on the core path are refused (R10 readMem). Bytes indexing relies on uint lowering (R13).

- **`inlineArrays`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — isInlineArray TupleExpression tagged inlineArrays
  - lowering: `Solidity.inlineArrayTy` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:149`) — infers fixed memory array type independent of target
  - lowering: `Solidity.inlineExprTy` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:86`) — mobile/common element type inference
  - regression: `Solidity.Examples.Tactics.AggregatesImport.literals_valid` (Solidity.Examples.Tactics.AggregatesImport, `Solidity/Examples/Tactics/AggregatesImport.lean:51`) — imported inline-array literals validated
  - no existing anchor: source, backend, evm, theorem
  - missing: Enum/nominal element identities are refused ('enum array literal without its resolved declaration identity'). Recursive shapes are partial.
  - missing: Fixed memory arrays and reference-element arrays are outside the memory compiler (R28), so there is no backend/EVM coverage.

- **`memberAccess`** (model/partial)
  - admission: `Solidity.Frontend.Admission.magicMember` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:27`) — classifies block/msg/tx/abi/address/type members
  - lowering: `Solidity.extMember?` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:779`) — external member r.g classification
  - source: `Solidity.Heap.field` (Solidity.Semantics.Heap, `Solidity/Semantics/Heap.lean:220`) — memory struct field read
  - backend: `Solidity.Evm.Memory.readField_correct` (Solidity.Evm.MemoryStruct, `Solidity/Evm/MemoryStruct.lean:75`) — memory field read code correct
  - no existing anchor: evm, theorem
  - missing: bytes.concat/string.concat/wrap/unwrap get no distinct admission tag (memberAccess only).
  - missing: Members of pushed elements (x.push().f) other than assignments are refused. Extension methods are partial.
  - missing: Address members (code, codehash, balance) have no backend: selfBalance refused (R11).

- **`metaTypeExpression`** (model/partial)
  - admission: `Solidity.Frontend.Admission.builtinFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:87`) — type builtin tagged metaTypeExpression
  - lowering: `Solidity.Frontend.typeBound?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1118`) — integer type(T).max/min folded
  - lowering: `Solidity.typeBoundExpr` (Solidity.Syntax.Grammar, `Solidity/Syntax/Grammar.lean:576`) — only max/min modelled
  - regression: `Solidity.Corpus.TestSuite.typeBounds` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2385`) — type bounds proved
  - no existing anchor: source, backend, evm, theorem
  - missing: Contract/interface metatype members (creationCode, runtimeCode, interfaceId, name) get separate tags and are not modelled.
  - missing: Enum type(E).min/max is partial (enumLit?). There is no backend stage beyond constants.

- **`namedArguments`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — names on FunctionCall tagged
  - lowering: `Solidity.Frontend.isNamedCall` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:2021`) — detects named calls
  - lowering: `Solidity.RawExpr.orderNamed` (Solidity.Syntax.Elab.Context, `Solidity/Syntax/Elab/Context.lean:380`) — binds by formal name
  - regression: `Solidity.Corpus.TestSuite.namedArgumentsBindByName` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2415`) — name binding proved
  - no existing anchor: source, backend, evm, theorem
  - missing: Named arguments to callees whose parameters the import does not know are refused.
  - missing: No theorem that the reordered evaluation matches the actual compiler (legacy vs viaIR) order.

- **`names`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — Identifier/IdentifierPath nodes tagged identifiers+names
  - lowering: `Solidity.Frontend.mergeC3` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:597`) — C3 order picks retained base implementations
  - source: `Solidity.Loc` (Solidity.Syntax.Scoped, `Solidity/Syntax/Scoped.lean:56`) — typed state roots vs locals resolved intrinsically
  - backend: `Solidity.Evm.loc_sim` (Solidity.Evm.Expr, `Solidity/Evm/Expr.lean:106`) — compiled storage-location simulation
  - no existing anchor: evm, theorem
  - missing: Type members and using-for extension methods are only partly resolved (operatorAlias?, base/super members refuse some cases).
  - missing: Compiler theorems are per-Prog with no contract or dispatch (R04), so contract-level name resolution has no backend proof.

- **`newMemory`** (model/partial)
  - source: `Solidity.newArrT` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:242`) — fresh defaulted array allocation
  - lowering: `Solidity.elabNewTy` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:1053`) — new T\[\](n) typing
  - backend: `Solidity.Evm.Memory.newArray_correct` (Solidity.Evm.MemoryAllocSource, `Solidity/Evm/MemoryAllocSource.lean:122`) — allocation code correct
  - backend: `Solidity.Evm.Memory.compile_correct` (Solidity.Evm.MemoryCompile, `Solidity/Evm/MemoryCompile.lean:1245`) — memory compiler GrowingResult
  - no existing anchor: admission, evm, theorem
  - missing: Memory capacity is a premise, and the generated code has no capacity check or Panic(0x41) (R25).
  - missing: Nested/reference-element arrays (new uint\[\]\[\](n)) are outside the memory path (R28). Memory loops are out (R22).

- **`parentheses`** (model/present)
  - lowering: `Solidity.Frontend.unparen` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1187`) — strips grouping from solc nodes
  - lowering: `Solidity.Frontend.operand` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1794`) — re-parenthesises operator operands when rendering
  - regression: `Solidity.Corpus.TestSuite.parenthesizedRightOperand` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:1805`) — grouping preserved in proof corpus
  - regression: `Solidity.Corpus.TestSuite.parenthesizedCondition` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:1815`) — parenthesised condition corpus case
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: No theorem that unparen/operand rendering preserves evaluation order. Correctness is checked only syntactically.
  - missing: Telling a parenthesised single value apart from a 1-tuple depends on the solc AST alone.

- **`rangeAccess`** (model/partial)
  - lowering: `Solidity.sliceViewOf?` (Solidity.Syntax.Elab.Context, `Solidity/Syntax/Elab/Context.lean:1002`) — calldata slice view construction
  - lowering: `Solidity.sliceElementCopy` (Solidity.Syntax.Elab.SliceCopy, `Solidity/Syntax/Elab/SliceCopy.lean:13`) — slice element copies
  - regression: `Solidity.Examples.Tactics.AggregateSlices.successful_run` (Solidity.Examples.Tactics.AggregateSlices, `Solidity/Examples/Tactics/AggregateSlices.lean:67`) — successful slice run
  - regression: `Solidity.Examples.Tactics.SliceReferenceCopies.legacy.invalidRange_run` (Solidity.Examples.Tactics.SliceReferenceCopies, `Solidity/Examples/Tactics/SliceReferenceCopies.lean:153`) — invalid endpoints fail
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: Slices of nominal UDVT/enum elements are refused (need declaration identity and range premises).
  - missing: No backend/EVM stage: calldata copies (R20) and ABI entry (R04) are outside the compiler theorems.

- **`shifts`** (model/partial)
  - source: `Solidity.BinOp.evalNum` (Solidity.Semantics.Ops, `Solidity/Semantics/Ops.lean:74`) — shift semantics, left type preserved
  - source: `Solidity.Bridge.Arith.int_shr_all_widths` (SolidityBridge.Arith.NarrowShifts, `Bridge/SolidityBridge/Arith/NarrowShifts.lean:15`) — sign-extending SAR all widths
  - evm: `Solidity.Evm.External.shr_step` (SolidityBridge.ExternalEvm.WordOps, `Bridge/SolidityBridge/ExternalEvm/WordOps.lean:82`) — SHR agrees with reference EVM
  - regression: `Solidity.Corpus.TestSuite.testShiftRightNegativeRoundsDown` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2600`) — negative >> rounds down
  - no existing anchor: admission, lowering, backend, theorem
  - missing: The compiler refuses signed `>>` (R12). The source refuses signed `<<`.
  - missing: `>>>` is tagged unsignedRightShift and is not modelled.

- **`shortCircuit`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — &&/|| tagged shortCircuit
  - source: `Solidity.BinOp.shortT` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:218`) — lazy second operand
  - theorem: `Solidity.BinOp.shortT_none` (Solidity.Calculus.SoundLocal, `Solidity/Calculus/SoundLocal.lean:49`) — calculus soundness lemma for short-circuit
  - regression: `Solidity.Corpus.TestSuite.logicalAndShortCircuitRhs` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:285`) — RHS skipped when not needed
  - no existing anchor: lowering, backend, evm
  - missing: No dedicated backend/EVM lemma for the lazy RHS was found. The backend relies on generic val_sim.
  - missing: RHS effects in the compiled path are limited to the core fragment (no calls or hashes, R09/R10).

- **`structConstruction`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — structConstructorCall tagged
  - lowering: `Solidity.Frontend.call` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1798`) — struct constructor rendered by declaration
  - lowering: `Solidity.expandStmt` (Solidity.Syntax.Grammar, `Solidity/Syntax/Grammar.lean:686`) — T memory t = T(a,b) desugaring
  - backend: `Solidity.Evm.Memory.allocateStructCode` (Solidity.Evm.MemoryStructGrow, `Solidity/Evm/MemoryStructGrow.lean:131`) — memory struct allocation code
  - no existing anchor: source, evm, theorem
  - missing: Reference-member struct construction is outside the memory compiler (R28).
  - missing: Struct constructors in loop conditions are refused. Evaluation order follows the selected compiler order only through EvalOrder lowering, with no theorem.

- **`tupleExpressions`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — non-inline TupleExpression tagged tupleExpressions
  - lowering: `Solidity.Frontend.explicitTupleAssignment` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:2109`) — tuple assignment leaves with empty targets
  - lowering: `Solidity.elabTuple` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:747`) — elaborates tuple assignment/declaration
  - regression: `Solidity.Corpus.TestSuite.tupleAssignmentRotates` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2185`) — commit-order rotation proved
  - no existing anchor: source, backend, evm, theorem
  - missing: Tuple/reference returns of internal calls are outside the compiler (R09: CallRetIn only .none/.val).
  - missing: Mixed storage tuple calls outside their validated declaration context are refused by the importer.

- **`unaryArithmetic`** (model/partial)
  - source: `Solidity.UnOp.evalT` (Solidity.Semantics.Ops, `Solidity/Semantics/Ops.lean:139`) — neg/not/bnot semantics
  - backend: `Solidity.Evm.Memory.unaryValue_correct` (Solidity.Evm.MemoryExpr, `Solidity/Evm/MemoryExpr.lean:115`) — unary code correct (memory path)
  - source: `Solidity.Bridge.Arith.int_neg_checked_all_widths` (SolidityBridge.Arith.NarrowChecked, `Bridge/SolidityBridge/Arith/NarrowChecked.lean:305`) — checked min-int negation, all widths
  - evm: `Solidity.Evm.External.not_step` (SolidityBridge.ExternalEvm.WordOps, `Bridge/SolidityBridge/ExternalEvm/WordOps.lean:47`) — NOT agrees with reference EVM
  - no existing anchor: admission, lowering, theorem
  - missing: The source refuses signed `~` (R12). `~` on bytesN is not told apart from uint (R13).

#### lexical

- **`addressLiterals`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — number literal typed address maps to addressLiterals
  - source: `Solidity.addressRows` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:544`) — address width rows (160-bit)
  - regression: `Solidity.Examples.Tactics.SourceLiteralsImport.address_context_initial` (Solidity.Examples.Tactics.SourceLiteralsImport, `Solidity/Examples/Tactics/SourceLiteralsImport.lean:14`) — address literal context preserved
  - regression: `Solidity.Corpus.TestSuite.returnDefaultAddressIsZero` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2230`) — address default is zero
  - no existing anchor: lowering, backend, evm, theorem
  - missing: Checksum and length checks are solc's alone; no Lean check
  - missing: address reaches backend as uint (R13); no proved 160-bit bound at the compiler

- **`booleanLiterals`** (model/present)
  - lowering: `Solidity.Frontend.expr` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1522`) — renders bool Literal nodes
  - backend: `Solidity.Evm.compileVal` (Solidity.Evm.Compile, `Solidity/Evm/Compile.lean:351`) — compiles bool values as words
  - evm: `Solidity.Evm.External.decode_bool` (SolidityBridge.ExternalEvm.WordOps, `Bridge/SolidityBridge/ExternalEvm/WordOps.lean:6`) — bool word decoding agrees with EVM
  - regression: `Solidity.Corpus.TestSuite.requireTrueLiteral` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:165`) — require(true) obligation proved
  - no existing anchor: source, admission, theorem
  - missing: No stated theorem that numeric-to-bool coercion is impossible (rests on typing)

- **`comments`** (model/partial)
  - admission: `Solidity.Frontend.scanSpecifications` (Solidity.Frontend.Import, `Solidity/Frontend/Import.lean:493`) — scans NatSpec spec annotations by lexical binders
  - lowering: `Solidity.Frontend.specCommentTokens` (Solidity.Frontend.Import, `Solidity/Frontend/Import.lean:264`) — tokenizes spec comments; ordinary comments stay data
  - lowering: `Solidity.Frontend.docText` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:21`) — reads documentation nodes for clauses
  - regression: `Solidity.Examples.Tactics.SourceIdentifiersImport.escaped_spec_valid` (Solidity.Examples.Tactics.SourceIdentifiersImport, `Solidity/Examples/Tactics/SourceIdentifiersImport.lean:21`) — spec with escaped identifiers is valid
  - no existing anchor: source, theorem
  - missing: Multi-source NatSpec @custom:key and loopSpec refused (compilationUnitSpecifications)
  - missing: No end-to-end proof that comments carry no meaning or that spans are kept

- **`etherUnits`** (model/present)
  - source: `Solidity.unitFactor?` (Solidity.Syntax.Grammar, `Solidity/Syntax/Grammar.lean:416`) — wei/gwei/ether factors
  - lowering: `Solidity.Frontend.constVal` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:955`) — multiplies subdenomination before range check
  - regression: `Solidity.Corpus.TestSuite.numberLiteralForms` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:1585`) — 1 gwei and other literal forms proved
  - no existing anchor: admission, backend, evm, theorem
  - missing: No theorem that the folded factor matches solc for every unit and rational case

- **`hexLiterals`** (model/partial)
  - lowering: `Solidity.Frontend.validHexBytes` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1369`) — checks hex digits of solc hexValue
  - source: `Solidity.hexBytes?` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:608`) — decodes hex literal into bytes
  - lowering: `Solidity.Frontend.abiHexLiteral?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1430`) — hex literals as ABI call payloads
  - regression: `Solidity.Examples.Tactics.AbiHexCall.exact_hex_valid` (Solidity.Examples.Tactics.AbiHexCall, `Solidity/Examples/Tactics/AbiHexCall.lean:108`) — exact hex payload property holds
  - no existing anchor: admission, backend, evm, theorem
  - missing: A hex literal without solc bytes is refused (Body.lean:1390)
  - missing: Byte-memory backend absent: word-addressed memory (R31), no hashes (R10)

- **`identifiers`** (model/partial)
  - admission: `Solidity.Frontend.Admission.scan` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:418`) — admission walk; declarations keyed by compiler IDs
  - lowering: `Solidity.Frontend.identText` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:22`) — quotes raw source names, including $ names and keywords
  - lowering: `Solidity.freshenStmt` (Solidity.Syntax.Elab.Context, `Solidity/Syntax/Elab/Context.lean:1229`) — renames locals so shadowed names stay apart
  - regression: `Solidity.Examples.Tactics.SourceIdentifiersImport.shadow_execution` (Solidity.Examples.Tactics.SourceIdentifiersImport, `Solidity/Examples/Tactics/SourceIdentifiersImport.lean:12`) — imported shadowing runs correctly
  - no existing anchor: source, backend, theorem
  - missing: No general theorem that lowering keeps declaration identity or scope; only regressions
  - missing: Qualified names across modules rely on import adapters with no proof (see sourceUnits)

- **`numericLiterals`** (model/partial)
  - lowering: `Solidity.Frontend.parseRational` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:900`) — exact rational parse of solc literal
  - lowering: `Solidity.Frontend.constVal` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:955`) — folds rational constant expressions before typing
  - backend: `Solidity.Evm.val_sim` (Solidity.Evm.Expr, `Solidity/Evm/Expr.lean:255`) — compiled values, literals included, simulate source
  - evm: `Solidity.Evm.External.push_agrees` (SolidityBridge.ExternalEvm.Dispatch, `Bridge/SolidityBridge/ExternalEvm/Dispatch.lean:195`) — PUSH constant agrees with upstream EVM
  - no existing anchor: source, admission, theorem
  - missing: Contextual literal promotion and nested numeric positions not done (numeric-operators.md Left)
  - missing: Narrow widths reach compiler as uint (R13); width correctness rests on unproved lowering
  - missing: No theorem that folding matches solc's arbitrary-precision semantics

- **`pragmaAbicoder`** (model/partial)
  - admission: `Solidity.Frontend.Source.AbiCoder` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:35`) — ABI coder selection recorded
  - admission: `Solidity.Frontend.Source.Pragmas` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:56`) — per-source pragma record incl. abicoder
  - admission: `Solidity.Frontend.Source.ScopeScan.within` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:299`) — admitted features lie in selected profile
  - no existing anchor: source, lowering, backend, evm, theorem
  - missing: Legacy ABI-v1 decoding is an implementation diagnostic
  - missing: Legacy-pipeline unit with mixed ABI coders plus inheritance refused (compilationUnitAbiModes)
  - missing: No ABI decode reaches backend: no dispatch or ABI (R04)

- **`pragmaOther`** (model/partial)
  - admission: `Solidity.Frontend.Source.validateSettings` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:169`) — rejects unknown settings/modes
  - admission: `Solidity.Frontend.Source.Gate` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:47`) — admission gate kinds
  - admission: `Solidity.Frontend.Source.Pipeline` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:41`) — legacy vs viaIR pipeline recorded
  - lowering: `Solidity.EvalOrder.viaIR` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:400`) — viaIR operand order kept in contract
  - no existing anchor: source, theorem
  - missing: Experimental/unknown modes only refused, not modeled
  - missing: Manual evalOrder override on modern imports refused

- **`pragmaVersion`** (model/partial)
  - admission: `Solidity.Frontend.Source.readPragmas` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:63`) — reads and checks per-source pragma records
  - admission: `Solidity.Frontend.Source.parseCompiler` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:154`) — pins the compiler version
  - admission: `Solidity.Frontend.Source.Provenance` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:117`) — records compiler/settings provenance
  - admission: `Solidity.Frontend.Admission.pragmaFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:108`) — classifies PragmaDirective
  - no existing anchor: source, theorem
  - missing: Provenance does not authenticate handwritten JSON (source-admission Decisions)
  - missing: Historical four-field fixtures load with admissionChecked=false
  - missing: No theorem linking the version range to the semantics used

- **`stringLiterals`** (model/partial)
  - lowering: `Solidity.Frontend.byteLiteralText` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1375`) — renders exact string/unicode/hex bytes from solc
  - lowering: `Solidity.strLit` (Solidity.Syntax.Grammar, `Solidity/Syntax/Grammar.lean:436`) — sol{} string literal expansion
  - source: `Solidity.litBytes` (Solidity.Syntax.Scoped, `Solidity/Syntax/Scoped.lean:1215`) — intrinsic byte literal
  - regression: `Solidity.Examples.Tactics.ComputedRevert.unicode_hex_reason_exact` (Solidity.Examples.Tactics.ComputedRevert, `Solidity/Examples/Tactics/ComputedRevert.lean:159`) — exact revert-reason bytes from literals
  - no existing anchor: admission, backend, evm, theorem
  - missing: bytes/string values excluded from core backend (R10 hashes, R17 dynamic copies)
  - missing: Direct string conversions refused (declarations-metadata.md)
  - missing: No proof of escape decoding or adjacent-literal concatenation; solc's value is trusted

- **`timeUnits`** (model/present)
  - source: `Solidity.unitFactor?` (Solidity.Syntax.Grammar, `Solidity/Syntax/Grammar.lean:416`) — seconds..weeks factors
  - lowering: `Solidity.Frontend.constVal` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:955`) — folds time subdenomination
  - regression: `Solidity.Corpus.TestSuite.numberLiteralForms` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:1585`) — 2 days folded and proved
  - no existing anchor: admission, backend, evm, theorem
  - missing: Only literal factor folding; no general folding theorem

- **`unicodeLiterals`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — unicodeString literal maps to unicodeLiterals
  - lowering: `Solidity.Frontend.byteLiteralText` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1375`) — unicode literal keeps solc-validated UTF-8 bytes
  - regression: `Solidity.Examples.Tactics.AbiFeatures.utf8_namespace` (Solidity.Examples.Tactics.AbiFeatures, `Solidity/Examples/Tactics/AbiFeatures.lean:35`) — UTF-8 namespace bytes exact
  - no existing anchor: source, backend, evm, theorem
  - missing: UTF-8 validity is checked only by solc and the input helper; no Lean check or proof
  - missing: No backend or EVM path for dynamic byte values (R10/R17)

#### metadata

- **`creationCode`** (model/partial)
  - admission: `Solidity.Frontend.Source.readCompilerCode` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:360`) — reads bound, linked code artifacts with provenance
  - admission: `Solidity.Frontend.Source.ScopeScan.requireCompilerCode` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:287`) — requires matching artifact
  - lowering: `Solidity.Frontend.staticCompilerBytes?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1203`) — static creationCode bytes
  - lowering: `Solidity.Frontend.staticCompilerLength_agrees` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1197`) — folded length matches emitted bytes
  - no existing anchor: source, backend, evm, theorem
  - missing: Deployed account code, unresolved linking, oversized materialization unsupported
  - missing: Schema-2 artifact inputs unfinished; no compiler-correctness link (R05)

- **`errorEventSelector`** (model/present)
  - lowering: `Solidity.Frontend.declarationMetadata` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1059`) — error bytes4 / event bytes32; anonymous refused
  - regression: `Solidity.Examples.Tactics.DeclarationMetadata.errorSelectors` (Solidity.Examples.Tactics.DeclarationMetadata, `Solidity/Examples/Tactics/DeclarationMetadata.lean:27`) — error selectors
  - regression: `Solidity.Examples.Tactics.DeclarationMetadata.eventSelector` (Solidity.Examples.Tactics.DeclarationMetadata, `Solidity/Examples/Tactics/DeclarationMetadata.lean:31`) — event selector
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: Selectors come from solc ABI metadata, not recomputed in Lean
  - missing: bytes32 hash values excluded from backend (R10)

- **`functionAddress`** (model/partial)
  - lowering: `Solidity.Frontend.storedFunctionMemberType?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:312`) — .address typed address
  - regression: `Solidity.Examples.Tactics.FunctionTypes.addressOfValue` (Solidity.Examples.Tactics.FunctionTypes, `Solidity/Examples/Tactics/FunctionTypes.lean:228`) — address of function value
  - regression: `Solidity.Examples.Tactics.SourceAdmissionImport.boundSelf_iff` (Solidity.Examples.Tactics.SourceAdmissionImport, `Solidity/Examples/Tactics/SourceAdmissionImport.lean:242`) — bound self receiver projection
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: Effectful C(receiver()).f.address refused
  - missing: Not all declaration contexts validated

- **`functionSelector`** (model/partial)
  - lowering: `Solidity.fnSelector?` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:967`) — selector of external function value
  - lowering: `Solidity.Frontend.declarationSelector` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1031`) — static declaration selectors fold
  - lowering: `Solidity.Frontend.storedFunctionMemberType?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:312`) — .selector typed bytes4
  - regression: `Solidity.Examples.Tactics.FunctionTypes.selectorOfValue` (Solidity.Examples.Tactics.FunctionTypes, `Solidity/Examples/Tactics/FunctionTypes.lean:236`) — selector of function value
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: Effectful stored-member receivers refused (read twice)
  - missing: Not all declaration contexts validated; no uniqueness (by design)

- **`interfaceId`** (model/present)
  - lowering: `Solidity.Frontend.declarationMetadata` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1059`) — XOR of own external selectors
  - source: `Solidity.Keccak.selector` (Solidity.Keccak, `Solidity/Keccak.lean:109`) — 4-byte selector
  - regression: `Solidity.Examples.Tactics.DeclarationMetadata.ownInterface` (Solidity.Examples.Tactics.DeclarationMetadata, `Solidity/Examples/Tactics/DeclarationMetadata.lean:23`) — interfaceId value
  - no existing anchor: admission, backend, evm, theorem
  - missing: Abstract-contract interfaceId refused
  - missing: No general XOR theorem

- **`runtimeCode`** (model/partial)
  - admission: `Solidity.Frontend.Source.readCompilerCode` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:360`) — runtime artifact with provenance
  - lowering: `Solidity.Frontend.staticCompilerBytes?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1203`) — static runtimeCode bytes
  - lowering: `Solidity.Frontend.staticCompilerLength_agrees` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1197`) — length agreement
  - no existing anchor: source, backend, evm, theorem
  - missing: Same gaps as creationCode; immutables are not reflected in runtime bytes
  - missing: No link between the artifact and the verified machine (R05)

- **`typeBounds`** (model/partial)
  - lowering: `Solidity.Frontend.typeBound?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1118`) — type(T).min/max incl. signed minimum
  - source: `Solidity.typeBoundExpr` (Solidity.Syntax.Grammar, `Solidity/Syntax/Grammar.lean:576`) — sol{} type bounds
  - regression: `Solidity.Corpus.TestSuite.typeBounds` (Solidity.Corpus.TestSuite, `Solidity/Corpus/TestSuite.lean:2385`) — type bounds proved
  - no existing anchor: admission, backend, evm, theorem
  - missing: Enum min/max cardinality not shown in typeBound? (integers only)
  - missing: No general theorem on bounds

- **`typeName`** (model/present)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — type(C).name maps to typeName
  - lowering: `Solidity.Frontend.declarationMetadata` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1059`) — folds name to UTF-8 literal
  - no existing anchor: source, backend, evm, theorem
  - missing: No dedicated theorem; resulting bytes hit bytes/string backend limits (R10/R17)

#### semantics

- **`abiEntryValidation`** (abstract/partial)
  - source: `Solidity.Binders.decodeT` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:483`) — typed decoding of returned words
  - source: `Solidity.PrimTy.ofWord?` (Solidity.Semantics.Value, `Solidity/Semantics/Value.lean:89`) — range-checked word-to-value conversion
  - lowering: `Solidity.abiDecodeWith` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:1465`) — ABI decoding lowered to typed reads
  - admission: `Solidity.Frontend.obligation` (Solidity.Frontend.Problems, `Solidity/Frontend/Problems.lean:140`) — entry premises from ABI decoder ranges
  - no existing anchor: backend, evm, theorem
  - missing: Compiler theorems have no ABI or dispatch (R04)
  - missing: Legacy ABI-v1 decoding refused; enum composite inputs refused

- **`checkedArithmetic`** (model/partial)
  - lowering: `Solidity.Prog.checkOF` (Solidity.Syntax.Checked, `Solidity/Syntax/Checked.lean:379`) — inserts overflow guards per intermediate op
  - source: `Solidity.Checked.add_uint_exact` (Solidity.Syntax.CheckedExact, `Solidity/Syntax/CheckedExact.lean:22`) — checked uint addition guard exact
  - theorem: `Solidity.Bridge.Arith.narrowCheck_full` (SolidityBridge.Arith.Lowering, `Bridge/SolidityBridge/Arith/Lowering.lean:176`) — narrow-width checked lowering correct
  - theorem: `Solidity.Main.compiler_checked` (Solidity.Theorems, `Solidity/Theorems.lean:297`) — compiler correctness for checked programs
  - no existing anchor: admission, backend, evm
  - missing: Overflow is plain .revert, not Panic 0x11 (solc-alignment)
  - missing: Signed bitwise/arith >> refused by compiler (R12)

- **`constructorLifetime`** (abstract/partial)
  - source: `Solidity.Contract.deployT` (Solidity.Semantics.Deploy, `Solidity/Semantics/Deploy.lean:28`) — typed constructor deployment
  - source: `Solidity.Lifetime.Reachable` (Solidity.Semantics.Lifetime, `Solidity/Semantics/Lifetime.lean:162`) — constructor-reachable states
  - theorem: `Solidity.Lifetime.post_of_deploy_box` (Solidity.Calculus.Lifetime, `Solidity/Calculus/Lifetime.lean:69`) — deploy obligations give reachable invariants
  - theorem: `Solidity.Problem.deploy_of_valid` (Solidity.Calculus.Deploy, `Solidity/Calculus/Deploy.lean:60`) — valid deploy problem implies deployment property
  - no existing anchor: admission, lowering, backend, evm
  - missing: Compiler theorems quantify over arbitrary represented states, no constructor (R04)
  - missing: Unsupported state initializers keep a refused constructor row

- **`defaultInitialization`** (model/partial)
  - source: `Solidity.SVal.defaultOf` (Solidity.Semantics.Storage.Ops, `Solidity/Semantics/Storage/Ops.lean:233`) — type-directed storage defaults
  - source: `Solidity.Heap.allocDefault` (Solidity.Semantics.Heap, `Solidity/Semantics/Heap.lean:389`) — default memory objects
  - backend: `Solidity.Evm.initStorage_repr` (Solidity.Evm.Repr, `Solidity/Evm/Repr.lean:1016`) — zero storage represents defaults
  - admission: `Solidity.Frontend.defaultLiteral` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1023`) — default literals for imported declarations
  - no existing anchor: lowering, evm, theorem
  - missing: Unset storage pointers are dead/unreadable, not modelled (R16)
  - missing: Reference-member struct defaults absent on memory path (R28)

- **`evaluationOrder`** (model/partial)
  - lowering: `Solidity.EvalOrder` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:392`) — selected compiler pipeline order
  - admission: `Solidity.Frontend.Source.Pipeline` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:41`) — legacy/via-IR pipeline recorded from settings
  - lowering: `Solidity.RawExpr.orderNamed` (Solidity.Syntax.Elab.Context, `Solidity/Syntax/Elab/Context.lean:380`) — named-argument evaluation order
  - lowering: `Solidity.wrapMods` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:646`) — modifier placeholder frames (legacy order)
  - no existing anchor: source, backend, evm, theorem
  - missing: Via-IR modifier re-initialisation at each _; not followed (solc-alignment)
  - missing: Reference sources not right-hand-side first remains a known divergence

- **`exactConstants`** (model/partial)
  - admission: `Solidity.Frontend.Q` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:858`) — exact rational constant values
  - admission: `Solidity.Frontend.constVal` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:955`) — constant folding at import
  - lowering: `Solidity.RawExpr.constRat?` (Solidity.Syntax.Elab.Context, `Solidity/Syntax/Elab/Context.lean:457`) — exact rational folding in the elaborator
  - lowering: `Solidity.mobileTy` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:1145`) — mobile literal type selection
  - no existing anchor: source, backend, evm, theorem
  - missing: Rational remainder, signed bit ops, arithmetic >> on literals refused
  - missing: No theorem relating folding to solc's rational semantics

- **`featureDetection`** (model/partial)
  - admission: `Solidity.Frontend.Admission.scan` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:418`) — whole-AST feature scan
  - admission: `Solidity.Frontend.Admission.declarationClosure` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:396`) — features from reachable declarations
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — per-node feature table, unknown nodes rejected
  - admission: `Solidity.Frontend.Admission.builtinFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:87`) — features of builtin uses
  - no existing anchor: source, theorem
  - missing: No theorem that scan covers initializers/modifiers/inherited bodies/specs
  - missing: Payment dispatch via inherited receive/fallback still refused

- **`nonpayableEntry`** (model/partial)
  - source: `Solidity.ContractWorld.World.enter` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:134`) — nonpayable/static entry refuses nonzero value
  - admission: `Solidity.Frontend.obligation` (Solidity.Frontend.Problems, `Solidity/Frontend/Problems.lean:140`) — msg.value = 0 premise for nonpayable
  - source: `Solidity.nonpayable_of_within'` (Solidity.Semantics.RunFrame, `Solidity/Semantics/RunFrame.lean:208`) — frame lemma for nonpayable mutability
  - evm: `Solidity.Evm.External.callvalue_upstream` (SolidityBridge.ExternalEvm.Environment, `Bridge/SolidityBridge/ExternalEvm/Environment.lean:114`) — CALLVALUE agrees with external EVM
  - no existing anchor: lowering, backend, theorem
  - missing: No compiled dispatcher callvalue check (R04)
  - missing: Single-contract Prog runs treat value refusal only as a premise

- **`panicCodes`** (model/partial)
  - source: `Solidity.Semantics.encodePanic` (Solidity.RevertBytes, `Solidity/RevertBytes.lean:54`) — Panic(uint256) payload encoding
  - source: `Solidity.TRun.selfPanicCode` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:862`) — panic code data in self-call frames
  - theorem: `Solidity.Semantics.decodeError_encodePanic` (Solidity.Calculus.SoundCatch, `Solidity/Calculus/SoundCatch.lean:28`) — panic payload decoding round-trips
  - source: `Solidity.Prog.run_noPanic` (Solidity.Semantics.NoPanic, `Solidity/Semantics/NoPanic.lean:544`) — assert-free programs never panic
  - no existing anchor: admission, lowering, backend, evm
  - missing: Outside self frames, 0x11/0x12/0x31/0x32 collapse to .revert (solc-alignment)
  - missing: Compiler erases panic: failing assert is a plain revert (R37)
  - missing: 0x41 array/memory panics absent (R24/R25)

- **`referenceCopyRules`** (model/partial)
  - source: `Solidity.FixedCopy` (Solidity.AST, `Solidity/AST.lean:89`) — fixed-array copy compatibility evidence
  - lowering: `Solidity.checkStorageCopy` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:397`) — checks allowed storage copy location pairs
  - source: `Solidity.MVal.copyMToSt` (Solidity.Semantics.Heap, `Solidity/Semantics/Heap.lean:446`) — memory-to-storage deep copy
  - theorem: `Solidity.assignFromMemStep_sound` (Solidity.Calculus.SoundStore, `Solidity/Calculus/SoundStore.lean:360`) — memory-to-storage assignment rule sound
  - no existing anchor: admission, backend, evm
  - missing: Byte-width widening in snapshot copies refused (aggregates.md)
  - missing: Compiler excludes copyMem/fixedCopy/fixedCopyMem (R19/R20)

- **`revertPayloads`** (model/partial)
  - source: `Solidity.TRun.revertData` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:948`) — revert with computed byte data
  - source: `Solidity.Semantics.encodeError` (Solidity.RevertBytes, `Solidity/RevertBytes.lean:50`) — Error(string) payload encoding
  - lowering: `Solidity.revertErrParts` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:998`) — custom-error argument encoding
  - theorem: `Solidity.Stmt.sound_catchData` (Solidity.Calculus.SoundCatch, `Solidity/Calculus/SoundCatch.lean:278`) — catch-with-data rule sound
  - no existing anchor: admission, backend, evm
  - missing: revertData/catchData excluded from compiler (R07); Out.revert carries no bytes (R37)
  - missing: Computed-data proofs limited by current modalities

- **`rollback`** (model/partial)
  - source: `Solidity.TRun.tryCall` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:877`) — try/catch frame boundary with rollback
  - source: `Solidity.ContractWorld.atomic_failure` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:387`) — failed operation restores the world
  - source: `Solidity.Transient.Program.attempt_rollback` (Solidity.Semantics.Transient, `Solidity/Semantics/Transient.lean:204`) — caught failure rolls back transient cells
  - source: `Solidity.ContractWorld.World.transact_failure` (Solidity.Semantics.TransientWorld, `Solidity/Semantics/TransientWorld.lean:65`) — transaction failure rolls back fully
  - no existing anchor: admission, lowering, backend, evm, theorem
  - missing: No compiled try/catch, so no EVM-level rollback theorem (R07)
  - missing: Rollback of returndata/outputs not observed (R41)

- **`staticCallRestriction`** (abstract/partial)
  - source: `Solidity.ContractWorld.Context.isStatic` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:103`) — static call context flag
  - source: `Solidity.Transient.Program.static_preserves` (Solidity.Semantics.Transient, `Solidity/Semantics/Transient.lean:222`) — static frames preserve transient state
  - lowering: `Solidity.roStmt` (Solidity.Syntax.Elab.Context, `Solidity/Syntax/Elab/Context.lean:696`) — view/pure write checking in elaborator
  - no existing anchor: admission, backend, evm, theorem
  - missing: No transitive static enforcement for arbitrary external callees
  - missing: Static-context payments/writes not in compiler (external calls excluded, R07)

- **`termination`** (model/partial)
  - source: `Solidity.Stmt.loop_terminates_of_wellFounded` (Solidity.Semantics.Termination, `Solidity/Semantics/Termination.lean:82`) — loop termination from well-founded measure
  - source: `Solidity.Prog.runF_approx` (Solidity.Semantics.RunFuel, `Solidity/Semantics/RunFuel.lean:449`) — fuel evaluator approximates semantic run
  - backend: `Solidity.Evm.compile_terminates_iff` (SolidityBridge.Evm, `Bridge/SolidityBridge/Evm.lean:171`) — compiled code terminates iff source does
  - theorem: `Solidity.TLoop.run_correct_of_wellFounded_on` (SolidityBridge.LoopFixpoint, `Bridge/SolidityBridge/LoopFixpoint.lean:65`) — loop fixpoint correctness under well-foundedness
  - no existing anchor: admission, lowering, evm
  - missing: Divergence matched classically to .fault; no gas-indexed prefixes (R38)
  - missing: Recursion depth fixed fuel 1024 (R08); exhausted never in compiler theorem (R39)

- **`typeValidation`** (model/partial)
  - admission: `Solidity.Frontend.Source.validateSettings` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:169`) — pinned compiler/settings validation
  - admission: `Solidity.Frontend.Source.read` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:203`) — reads validated compiler output with provenance
  - admission: `Solidity.Frontend.Source.checkTree` (Solidity.Frontend.SourceUnits, `Solidity/Frontend/SourceUnits.lean:31`) — checks compilation unit tree shape
  - admission: `Solidity.Frontend.Source.ScopeScan.certify` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:313`) — certifies scan against compiler code
  - no existing anchor: source, theorem
  - missing: Provenance records solc analysis but does not authenticate it (source-admission.md)
  - missing: No theorem that admission implies layout side conditions (R15/R16)

- **`uncheckedArithmetic`** (model/partial)
  - source: `Solidity.OFMode` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:138`) — lexical checked/unchecked mode
  - lowering: `Solidity.Prog.ignoreOF` (Solidity.Syntax.Checked, `Solidity/Syntax/Checked.lean:382`) — unchecked blocks skip overflow guards
  - lowering: `Solidity.uncheckStmts` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:705`) — lowers unchecked statement blocks
  - theorem: `Solidity.Bridge.Arith.narrowWrap_uint` (SolidityBridge.Arith.Lowering, `Bridge/SolidityBridge/Arith/Lowering.lean:74`) — narrow wrapping lowering correct
  - no existing anchor: admission, backend, evm
  - missing: Signed unchecked lowered via uint casts; signed bitwise not compiled (R12)
  - missing: No theorem that callees keep their own lexical mode

- **`worldAssumptions`** (abstract/partial)
  - theorem: `Solidity.Bridge.Adversary.holdsC_iff_all_callees` (SolidityBridge.Adversary, `Bridge/SolidityBridge/Adversary.lean:250`) — properties hold for all callee interpretations
  - theorem: `Solidity.Main.callback_soundness` (Solidity.Theorems, `Solidity/Theorems.lean:226`) — soundness under explicit callback invariant
  - source: `Solidity.ContractWorld.reachable_invariant` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:452`) — multi-contract world invariant over reachable states
  - no existing anchor: admission, lowering, backend, evm
  - missing: Not approved (G00 Q2): the premise must be replaced by the callee semantics of D02/D12, not discharged as stated
  - missing: Compiler world is balances only; recipient code not run (R33)
  - missing: msg.sender != this premise not imposed (solc-alignment)

#### statements

- **`blocks`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — Block node tagged .blocks
  - source: `Solidity.TRun.block` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:923`) — block scope; locals dropped on exit
  - backend: `Solidity.Evm.block_sim` (Solidity.Evm.Correct, `Solidity/Evm/Correct.lean:174`) — core compiler block simulation
  - theorem: `Solidity.sound_block` (Solidity.Calculus.SoundControl, `Solidity/Calculus/SoundControl.lean:452`) — calculus block rule sound
  - no existing anchor: lowering, evm
  - missing: Blocks that mix core and memory constructs compile on neither path (R01/R02)
  - missing: No lowering-correctness theorem for the solc-JSON to sol text step (Frontend.block) or for shadowing renames
  - missing: EVM side is the word-level Machine only, not bytecode (R05)

- **`breakStatement`** (model/present)
  - lowering: `Solidity.Abrupt` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:339`) — brk/cnt/ret abrupt kinds
  - lowering: `Solidity.LoopFlags` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:350`) — fresh per-loop break flag
  - theorem: `Solidity.breakTest_loopBreak` (Solidity.Calculus.SoundLoops, `Solidity/Calculus/SoundLoops.lean:250`) — break-flag condition test
  - theorem: `Solidity.Premise.sound_whileInvBoxB` (Solidity.Calculus.SoundLoops, `Solidity/Calculus/SoundLoops.lean:264`) — invariant rule for break-lowered loops
  - no existing anchor: source, admission, backend, evm
  - missing: No theorem that the flag encoding exits only the innermost loop and skips its condition/post
  - missing: No native break at source, backend or EVM; exactness rests on lowering

- **`canonicalRethrow`** (abstract/partial)
  - lowering: `Solidity.Frontend.memoryRethrow?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:2147`) — only whole-buffer revert(add(p,32),mload(p))
  - source: `Solidity.RevPart` (Solidity.Syntax.Scoped, `Solidity/Syntax/Scoped.lean:315`) — RevPart.mem raw buffer payload
  - source: `Solidity.RevPart.evalT_mem` (Solidity.Semantics.RevertMemory, `Solidity/Semantics/RevertMemory.lean:17`) — memory payload evaluation
  - source: `Solidity.TRun.catchBytes_self_data` (Solidity.Semantics.RevertMemory, `Solidity/Semantics/RevertMemory.lean:67`) — bytes transported to catch
  - no existing anchor: admission, backend, evm, theorem
  - missing: Backend/EVM refuse revertData; raw bytes unobservable (R07/R37)
  - missing: Machine memory is word-addressed, so the byte-level revert(ptr,len) is not modelled (R31)

- **`catchClauses`** (model/partial)
  - source: `Solidity.TRun.catchData` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:1020`) — catch binds reason/raw bytes
  - source: `Solidity.CatchKind.decode` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:995`) — Error(string) decode vs raw
  - theorem: `Solidity.Stmt.sound_catchData` (Solidity.Calculus.SoundCatch, `Solidity/Calculus/SoundCatch.lean:278`) — catch-data rule soundness
  - source: `Solidity.TRun.catchData_self_data` (Solidity.Semantics.RevertMemory, `Solidity/Semantics/RevertMemory.lean:83`) — self-call bytes reach typed catch
  - no existing anchor: admission, lowering, backend, evm
  - missing: Non-self catch data comes from the oracle table; malformed-payload dispatch only for Error/Panic/raw kinds
  - missing: Typed custom-error catches unsupported; compiler refuses catchData (R07)

- **`continueStatement`** (model/partial)
  - lowering: `Solidity.Abrupt` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:339`) — cnt flag kind
  - lowering: `Solidity.lowerLoop` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:481`) — continue guards rest; for-post kept
  - theorem: `Solidity.Stmt.sound_loop` (Solidity.Calculus.SoundLoops, `Solidity/Calculus/SoundLoops.lean:555`) — applies after lowering
  - no existing anchor: source, admission, backend, evm
  - missing: No proof continue reaches the right post/condition for for and do-while
  - missing: Effectful while conditions are re-run as head statements; that routing is unverified

- **`doWhileStatement`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — DoWhileStatement tagged
  - lowering: `Solidity.lowerLoop` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:481`) — do-while to while via a first flag
  - source: `Solidity.Stmt.run_loop` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:1327`) — semantics only via the lowered loop
  - theorem: `Solidity.Stmt.sound_loop` (Solidity.Calculus.SoundLoops, `Solidity/Calculus/SoundLoops.lean:555`) — lowered loop rule
  - no existing anchor: backend, evm
  - missing: Stmt has no native do-while; body-first execution and continue-to-condition rest on the unproved lowering
  - missing: Inherits R21/R22/R38 loop restrictions

- **`emitStatement`** (model/partial)
  - lowering: `Solidity.Frontend.stmt1` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:2202`) — resolved positional emit; named args refused
  - lowering: `Solidity.eagerArgsWith` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:1958`) — operands evaluated in order, log dropped
  - regression: `Solidity.Examples.Tactics.CallExceptions.event_argument_panics` (Solidity.Examples.Tactics.CallExceptions, `Solidity/Examples/Tactics/CallExceptions.lean:49`) — erased event argument still panics
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: Logs not observable anywhere (no LOG at source or Machine); erasure valid only for log-blind properties
  - missing: Named event arguments and qualified event names refused
  - missing: No general erasure-soundness theorem

- **`expressionStatements`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — ExpressionStatement tagged
  - lowering: `Solidity.Frontend.stmt1` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:2202`) — ExpressionStatement printed; prefix captures hoisted
  - lowering: `Solidity.elabStmt1With` (Solidity.Syntax.Elab.Arms, `Solidity/Syntax/Elab/Arms.lean:1537`) — statement elaboration incl. discarded calls
  - backend: `Solidity.Evm.stmt_sim` (Solidity.Evm.Correct, `Solidity/Evm/Correct.lean:985`) — per-statement simulation for admitted forms
  - no existing anchor: source, evm, theorem
  - missing: Bare `r.send(a);` with result discarded is not read (RawStmt.send docstring)
  - missing: No theorem that hoisting keeps every effect/failure of a discarded value
  - missing: Call or memory effects in expression statements often fall outside the compiler fragment (R09, R29)

- **`forStatement`** (model/partial)
  - lowering: `Solidity.Frontend.loopSpec` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:2559`) — ForStatement with loop spec import
  - lowering: `Solidity.lowerLoop` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:481`) — for to while; continue runs post
  - backend: `Solidity.Evm.loop_sim` (Solidity.Evm.Correct, `Solidity/Evm/Correct.lean:296`) — after lowering, compiled as core loop
  - theorem: `Solidity.Stmt.sound_loop` (Solidity.Calculus.SoundLoops, `Solidity/Calculus/SoundLoops.lean:555`) — applies to lowered while
  - no existing anchor: source, admission, evm
  - missing: No proof that omitted clauses, init scope and continue-through-post survive lowerLoop
  - missing: Same R21/R22 restrictions: memory or paying for-loops (e.g. transfer in body) not compiled

- **`ifStatement`** (model/present)
  - lowering: `Solidity.Frontend.stmt1` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:2202`) — IfStatement to sol ite
  - source: `Solidity.TRun.ite` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:793`) — evaluates condition once, runs one branch
  - backend: `Solidity.Evm.ite_sim` (Solidity.Evm.Correct, `Solidity/Evm/Correct.lean:127`) — branch simulation
  - theorem: `Solidity.iteStep_sound` (Solidity.Calculus.SoundControl, `Solidity/Calculus/SoundControl.lean:332`) — if rule soundness
  - no existing anchor: admission, evm
  - missing: Branches are joined with fragment meet; a fragile alias is forgotten after pop/delete in a branch (R36)
  - missing: EVM link uses structured relative jumps, not absolute bytecode jumps (R23)

- **`returnStatement`** (model/partial)
  - lowering: `Solidity.lowerReturns` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:285`) — early returns inlined into guarded code
  - lowering: `Solidity.wrapMods` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:646`) — modifier continuation around body
  - source: `Solidity.CallRet.leaveT` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:518`) — returned values copied to the caller frame
  - backend: `Solidity.Evm.CallRetIn` (Solidity.Evm.Compile, `Solidity/Evm/Compile.lean:153`) — only none/val return shapes compile
  - no existing anchor: admission, evm, theorem
  - missing: Tuple/reference returns not compiled (R09); no return values or returndata observed at EVM (R41)
  - missing: No theorem for lowerReturns/wrapMods frame isolation

- **`revertStatement`** (model/partial)
  - lowering: `Solidity.revertErrParts` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:998`) — custom error selector/word parts
  - source: `Solidity.TRun.revertData` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:948`) — revert with byte payload
  - theorem: `Solidity.sound_revertData` (Solidity.Calculus.SoundArms, `Solidity/Calculus/SoundArms.lean:1369`) — revertData rule soundness
  - regression: `Solidity.Examples.Tactics.CallExceptions.revert_argument_panics` (Solidity.Examples.Tactics.CallExceptions, `Solidity/Examples/Tactics/CallExceptions.lean:44`) — operands evaluated before revert
  - no existing anchor: admission, backend, evm
  - missing: Revert data erased at backend: Out.revert has no bytes; revertData refused (R07, R37)
  - missing: Exact bytes retained only in self frames or with retainFailureData; otherwise a plain revert

- **`tryStatement`** (abstract/partial)
  - lowering: `Solidity.Frontend.stmt1` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:2202`) — TryStatement import
  - source: `Solidity.TRun.tryCall` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:877`) — outcome table; self frame variant
  - theorem: `Solidity.Stmt.sound_tryCall` (Solidity.Calculus.SoundCalls, `Solidity/Calculus/SoundCalls.lean:1357`) — try rule soundness
  - backend: `Solidity.Evm.inFrag_tryCall` (Solidity.Evm.Correct, `Solidity/Evm/Correct.lean:945`) — compiler refuses tryCall (R07)
  - no existing anchor: admission, evm
  - missing: Backend and EVM refuse try entirely (R07)
  - missing: Typed contract creation try only through ContractWorld factory fragments, not Stmt
  - missing: Callback catches and external aggregate return decoding remain (calls-exceptions Left)

- **`uncheckedBlock`** (model/partial)
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — UncheckedBlock tagged uncheckedBlock/uncheckedArithmetic
  - lowering: `Solidity.uncheckStmts` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:705`) — + - * ** to wrapping ops; callees stay checked
  - backend: `Solidity.Evm.binInFrag` (Solidity.Evm.Layout, `Solidity/Evm/Layout.lean:410`) — addW/subW/mulW/powW compiled at uint only
  - regression: `Solidity.Examples.Tactics.Checked.uncheckedWrap` (Solidity.Examples.Tactics.Checked, `Solidity/Examples/Tactics/Checked.lean:75`) — regression example only
  - no existing anchor: source, evm, theorem
  - missing: No general theorem that uncheckStmts keeps division/index checks and leaves callees checked
  - missing: Signed unchecked goes through uint wrapping and casts; signed bitwise ops refused by compiler (R12)

- **`variableDeclarations`** (model/partial)
  - lowering: `Solidity.Frontend.declText` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:2119`) — solc VariableDeclaration to sol text
  - source: `Solidity.TRun.declLocal` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:653`) — declLocal with default/initializer
  - backend: `Solidity.Evm.declLocal_sim` (Solidity.Evm.Stmt, `Solidity/Evm/Stmt.lean:229`) — core local declaration simulation
  - theorem: `Solidity.sound_localValueDeclInitDrop` (Solidity.Calculus.SoundControl, `Solidity/Calculus/SoundControl.lean:420`) — declaration-with-initializer rule sound
  - no existing anchor: admission, evm
  - missing: Unset storage aliases are dead and unreadable (R16); reference-element/nested memory declarations off the memory path (R28)
  - missing: Tuple declarations (elabTuple) and memory declarations do not compile on the core path (declMem => none)
  - missing: No proof that declaration identity/initializer capture order survives import lowering

- **`whileStatement`** (model/partial)
  - lowering: `Solidity.lowerLoop` (Solidity.Syntax.Elab.Lower, `Solidity/Syntax/Elab/Lower.lean:481`) — break/continue/return to flags, to RawStmt.loop
  - source: `Solidity.TRun.loop` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:917`) — classical while run, divergence possible
  - backend: `Solidity.Evm.loop_sim` (Solidity.Evm.Correct, `Solidity/Evm/Correct.lean:296`) — loop simulation; divergence maps to fault
  - theorem: `Solidity.Stmt.sound_loop` (Solidity.Calculus.SoundLoops, `Solidity/Calculus/SoundLoops.lean:555`) — loop rule soundness (invariant/variant)
  - no existing anchor: admission, evm
  - missing: Loop bodies that push, pay, pop or change fragment flags are rejected (R21); no loops on memory path (R22)
  - missing: Divergence is matched classically against machine fault; no gas-bounded prefix theorem (R38)
  - missing: No correctness theorem for the lowerLoop flag encoding

#### storage

- **`arrayLength`** (model/partial)
  - source: `Solidity.Storage.len` (Solidity.Semantics.Storage.Ops, `Solidity/Semantics/Storage/Ops.lean:908`) — exact storage array length
  - source: `Solidity.Heap.len` (Solidity.Semantics.Heap, `Solidity/Semantics/Heap.lean:242`) — memory array length
  - backend: `Solidity.Evm.Sto.len_eq` (Solidity.Evm.StorageLemmas, `Solidity/Evm/StorageLemmas.lean:188`) — compiled length read agrees
  - admission: `Solidity.Frontend.solcArrayLength?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:332`) — static lengths from solc metadata
  - no existing anchor: lowering, evm, theorem
  - missing: Length bound 2^256 instead of 2^64 (R24)
  - missing: Calldata .length only through lowered slice views

- **`arrayPop`** (model/partial)
  - source: `Solidity.Storage.pop` (Solidity.Semantics.Storage.Ops, `Solidity/Semantics/Storage/Ops.lean:961`) — fail on empty, shorten, clear element
  - backend: `Solidity.Evm.pop_sim` (Solidity.Evm.Stmt, `Solidity/Evm/Stmt.lean:826`) — compiled pop simulates the source
  - theorem: `Solidity.popStep_sound` (Solidity.Calculus.SoundStore, `Solidity/Calculus/SoundStore.lean:566`) — calculus pop rule sound
  - no existing anchor: admission, lowering, evm
  - missing: Empty pop is .revert, not Panic 0x31 (solc-alignment)
  - missing: pop inside loops refused (R21); aliases dropped after pop (R36)

- **`arrayPush`** (model/partial)
  - source: `Solidity.Storage.push` (Solidity.Semantics.Storage.Ops, `Solidity/Semantics/Storage/Ops.lean:923`) — grow length and initialize the new element
  - backend: `Solidity.Evm.push_sim` (Solidity.Evm.Stmt, `Solidity/Evm/Stmt.lean:641`) — compiled push simulates the source
  - theorem: `Solidity.pushStep_sound` (Solidity.Calculus.SoundStore, `Solidity/Calculus/SoundStore.lean:504`) — calculus push rule sound
  - no existing anchor: admission, lowering, evm
  - missing: Compiler admits push() only of primitives, push(v) of static elems (R18)
  - missing: Pushes of dynamic/memory values and pushes inside loops refused (R18/R21)
  - missing: push of a struct over a recycled slot drops shadow data (solc-alignment)

- **`arrayPushReference`** (model/partial)
  - source: `Solidity.Storage.pushPlace` (Solidity.Semantics.Storage.Ops, `Solidity/Semantics/Storage/Ops.lean:934`) — append default and return its storage place
  - source: `Solidity.Storage.push_of_pushPlace` (Solidity.Semantics.Storage.Ops, `Solidity/Semantics/Storage/Ops.lean:955`) — pushPlace agrees with push
  - theorem: `Solidity.sound_pushReferenceCapture` (Solidity.Calculus.SoundStore, `Solidity/Calculus/SoundStore.lean:452`) — calculus rule for pushed reference capture sound
  - no existing anchor: admission, lowering, backend, evm
  - missing: x = arr.push(), arr.push() += 1, T storage p = arr.push() refused by compiler (R18)

- **`danglingReferences`** (model/partial)
  - source: `Solidity.SVal.findLive` (Solidity.Semantics.Storage.Ops, `Solidity/Semantics/Storage/Ops.lean:122`) — live-element lookup versus shadow slots
  - theorem: `Solidity.dangling_slot_reachable` (Solidity.Typing.Constructibility, `Solidity/Typing/Constructibility.lean:1280`) — dangling post-pop slot state is reachable
  - backend: `Solidity.Evm.Frag.dropFragile` (Solidity.Evm.Compile, `Solidity/Evm/Compile.lean:87`) — compiler forgets fragile aliases at shrink
  - no existing anchor: admission, lowering, evm
  - missing: Compiler rejects alias use after pop/delete rather than modelling it (R36)
  - missing: Scope decision Q2 on dangling behaviour open (g04 section 6)

- **`deleteMappingTails`** (model/partial)
  - source: `Solidity.Storage.delete` (Solidity.Semantics.Storage.Ops, `Solidity/Semantics/Storage/Ops.lean:972`) — delete keeps mapping entries in place
  - source: `Solidity.Storage.CleanTail` (Solidity.Typing.CleanTail, `Solidity/Typing/CleanTail.lean:74`) — explicit clean-tail predicate on storage
  - theorem: `Solidity.Prog.run_cleanTail` (Solidity.Typing.CleanTailRun, `Solidity/Typing/CleanTailRun.lean:1777`) — runs preserve clean tails
  - no existing anchor: admission, lowering, backend, evm
  - missing: Compiled delete covered only for its fragment; pop/delete in loops refused (R21)
  - missing: Dirty-tail semantics only via the clean/arbitrary tail mode, no compiler link

- **`logicalStorageBase`** (model/partial)
  - admission: `Solidity.Frontend.Admission.validateNode` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:264`) — validates StorageLayoutSpecifier base expressions
  - admission: `Solidity.Frontend.Admission.nodeFeatures` (Solidity.Frontend.SolcJson.Admission, `Solidity/Frontend/SolcJson/Admission.lean:116`) — maps layout specifier to logicalStorageBase feature
  - source: `Solidity.Storage.RegionRoot.persistent_write` (Solidity.Semantics.Storage.Anon, `Solidity/Semantics/Storage/Anon.lean:425`) — persistent writes leave the transient region
  - source: `Solidity.ERC7201.root_aligned` (Solidity.ERC7201, `Solidity/ERC7201.lean:31`) — ERC-7201 namespace root alignment
  - no existing anchor: lowering, backend, evm, theorem
  - missing: Base has no numeric slot effect; raw slots, offsets, packing excluded
  - missing: No compiler theorem relating a base to EVM slot numbers (R34)

- **`memoryAliasing`** (model/partial)
  - source: `Solidity.State.copyStToM` (Solidity.Semantics.State, `Solidity/Semantics/State.lean:173`) — storage-to-memory creates fresh objects
  - source: `Solidity.MVal.copyAt` (Solidity.Semantics.Heap, `Solidity/Semantics/Heap.lean:419`) — memory copy boundaries
  - theorem: `Solidity.rebindMemStep_sound` (Solidity.Calculus.SoundMem, `Solidity/Calculus/SoundMem.lean:56`) — memory rebinding rule sound
  - backend: `Solidity.Evm.Memory.copiedStruct_fresh` (Solidity.Evm.MemoryStructCopy, `Solidity/Evm/MemoryStructCopy.lean:122`) — compiled struct copy allocates fresh object
  - no existing anchor: admission, lowering, evm
  - missing: Deep memory→memory and storage-array→memory copies not compiled (R20)
  - missing: Overlapping heap objects excluded by StateRepr premises (R30)
  - missing: External ABI boundary copies unmodelled at compiler level (R04)

- **`storageAliasing`** (model/partial)
  - source: `Solidity.TRun.rebind` (Solidity.Semantics.Run, `Solidity/Semantics/Run.lean:646`) — rebinding a storage reference, distinct from writes
  - source: `Solidity.SVal.findM_saveM_diverges` (Solidity.Semantics.Storage.Ops, `Solidity/Semantics/Storage/Ops.lean:1078`) — writes to diverging paths do not interfere
  - backend: `Solidity.Evm.bindFl` (Solidity.Evm.Compile, `Solidity/Evm/Compile.lean:162`) — alias liveness flags in the compiler
  - no existing anchor: admission, lowering, evm, theorem
  - missing: Storage reference arguments to internal calls refused (R09)
  - missing: Aliases through array indices forgotten after pop/delete (R36)

- **`storageCopy`** (model/partial)
  - source: `Solidity.SVal.overlay` (Solidity.Semantics.Storage.Ops, `Solidity/Semantics/Storage/Ops.lean:498`) — deep copy keeping mapping members in place
  - backend: `Solidity.Evm.copy_sim` (Solidity.Evm.Stmt, `Solidity/Evm/Stmt.lean:593`) — compiled static storage copy simulates source
  - theorem: `Solidity.copyStep_sound` (Solidity.Calculus.SoundStore, `Solidity/Calculus/SoundStore.lean:91`) — calculus copy rule sound
  - source: `Solidity.TypeGraph.Value.overlay_tail` (Solidity.Semantics.RecursiveStorage.Copy, `Solidity/Semantics/RecursiveStorage/Copy.lean:148`) — graph copy tail cleanup
  - no existing anchor: admission, lowering, evm
  - missing: Compiler copies only static types; dynamic arrays/bytes/string refused (R17)
  - missing: Memory→storage and fixed-array copies excluded from core path (R19)

- **`transientState`** (model/partial)
  - source: `Solidity.Storage.RegionRoot.disjoint` (Solidity.Semantics.Storage.Anon, `Solidity/Semantics/Storage/Anon.lean:417`) — persistent/transient roots disjoint
  - source: `Solidity.Transient.Program.attempt_rollback` (Solidity.Semantics.Transient, `Solidity/Semantics/Transient.lean:204`) — failure rolls back the transient product
  - source: `Solidity.ContractWorld.World.resetTransient_persistent` (Solidity.Semantics.TransientWorld, `Solidity/Semantics/TransientWorld.lean:107`) — transaction reset keeps persistent storage
  - admission: `Solidity.Frontend.elabSolcWorldFactory` (Solidity.Frontend.WorldImport, `Solidity/Frontend/WorldImport.lean:245`) — closed factory targets with transient roots
  - no existing anchor: lowering, backend, evm, theorem
  - missing: General source-world statement lowering and transient factory owners unsupported
  - missing: Physical transient layout, raw tload/tstore absent; no compiler support

#### types

- **`addressTypes`** (model/partial)
  - source: `Solidity.ContractWorld.Address` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:28`) — logical address domain in the contract world
  - source: `Solidity.ContractWorld.Address.ofWord?` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:31`) — partial conversion from words to addresses
  - lowering: `Solidity.addressRows` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:544`) — address/address payable erased to uint rows
  - evm: `Solidity.Evm.External.address_upstream` (SolidityBridge.ExternalEvm.Environment, `Bridge/SolidityBridge/ExternalEvm/Environment.lean:90`) — ADDRESS opcode agrees with the external EVM
  - no existing anchor: admission, backend, theorem
  - missing: The machine keeps addresses as 256-bit words, not 160-bit (R27)
  - missing: No proof that payable-conversion rules are validated before erasure

- **`boolType`** (model/present)
  - source: `Solidity.PrimTy` (Solidity.AST, `Solidity/AST.lean:30`) — bool is a distinct primitive sort beside uint/int
  - source: `Solidity.BinOp.evalBool` (Solidity.Semantics.Ops, `Solidity/Semantics/Ops.lean:102`) — typed Boolean operator evaluation
  - backend: `Solidity.Evm.bword` (Solidity.Evm.Machine, `Solidity/Evm/Machine.lean:180`) — Boolean-to-word encoding on the abstract machine
  - evm: `Solidity.Evm.External.decode_bool` (SolidityBridge.ExternalEvm.WordOps, `Bridge/SolidityBridge/ExternalEvm/WordOps.lean:6`) — word decoding of Booleans agrees with the external EVM
  - no existing anchor: admission, lowering, theorem
  - missing: No end-to-end theorem tying ABI bool decoding (non-0/1 words) to a revert at entry
  - missing: Bool storage packing is not modelled: words are symbolic slots (R34)

- **`calldataLocation`** (model/partial)
  - lowering: `Solidity.calldataCheck` (Solidity.Syntax.Elab.Context, `Solidity/Syntax/Elab/Context.lean:743`) — enforces immutability of calldata parameters
  - lowering: `Solidity.SliceView` (Solidity.Syntax.Elab.Context, `Solidity/Syntax/Elab/Context.lean:863`) — typed calldata slice views with bounds
  - lowering: `Solidity.FunDecl.calldataParams` (Solidity.Syntax.Elab.Context, `Solidity/Syntax/Elab/Context.lean:660`) — identifies calldata parameters
  - lowering: `Solidity.RawExpr.calldataPlace` (Solidity.Syntax.Elab.Context, `Solidity/Syntax/Elab/Context.lean:899`) — calldata place resolution
  - no existing anchor: source, admission, backend, evm, theorem
  - missing: No intrinsic calldata location in Scoped/State; views are lowered away
  - missing: Calldata→memory copies out of memory compiler (R20)
  - missing: Reference-element slices, writable whole-calldata copies left (aggregates.md)

- **`dynamicArrays`** (model/partial)
  - source: `Solidity.Storage.checkIndex` (Solidity.Semantics.Storage.Ops, `Solidity/Semantics/Storage/Ops.lean:902`) — bounds check against live length
  - source: `Solidity.Heap.len` (Solidity.Semantics.Heap, `Solidity/Semantics/Heap.lean:242`) — memory array length
  - backend: `Solidity.Evm.Sto.checkIndex_dyn` (Solidity.Evm.StorageLemmas, `Solidity/Evm/StorageLemmas.lean:170`) — compiled dynamic bounds check agrees
  - backend: `Solidity.Evm.Memory.readArray_correct` (Solidity.Evm.Memory, `Solidity/Evm/Memory.lean:102`) — memory array read correctness
  - no existing anchor: admission, lowering, evm, theorem
  - missing: Lengths bounded by 2^256 not 2^64, no Panic 0x41 (R24)
  - missing: Reference-element memory arrays outside the memory compiler (R28)
  - missing: No loops on the memory path (R22)

- **`dynamicBytesType`** (model/partial)
  - lowering: `Solidity.dynBytesTy` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:541`) — bytes/string mapped to a byte-element array
  - source: `Solidity.bytesR` (Solidity.Syntax.Scoped, `Solidity/Syntax/Scoped.lean:309`) — intrinsic byte-array reference type
  - source: `Solidity.TRun.litBytesT_alloc` (Solidity.Semantics.AllocBytes, `Solidity/Semantics/AllocBytes.lean:254`) — byte-literal allocation run lemma
  - lowering: `Solidity.dynamicBytesExpr` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:875`) — elaborates dynamic bytes expressions
  - no existing anchor: admission, backend, evm, theorem
  - missing: Storage copies of dynamic bytes are refused by the compiler (R17)
  - missing: No byte-addressed memory or calldata representation (R31)
  - missing: Packed short/long storage encoding not modelled

- **`enumTypes`** (model/partial)
  - lowering: `Solidity.enumRows` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:548`) — enum members as bounded uint rows
  - lowering: `Solidity.enumCapture` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:1860`) — conversion range check, Panic 0x21 data in self frames
  - admission: `Solidity.Frontend.resolveSpecEnums` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:654`) — enum values resolved in specifications
  - no existing anchor: source, backend, evm, theorem
  - missing: Composite ABI inputs containing enums remain refused (source-admission.md)
  - missing: Outside self-call frames enum failure is plain revert, not Panic 0x21

- **`externalFunctionTypes`** (abstract/partial)
  - admission: `Solidity.Frontend.externalFunctionType` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:291`) — imports external function types
  - lowering: `Solidity.fnExternalValue` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:77`) — address plus selector external function values
  - source: `Solidity.ExtCall` (Solidity.Syntax.Scoped, `Solidity/Syntax/Scoped.lean:237`) — explicit typed external-call relation
  - theorem: `Solidity.Main.callback_soundness` (Solidity.Theorems, `Solidity/Theorems.lean:226`) — calculus sound for external calls under invariant
  - no existing anchor: backend, evm
  - missing: tryCall/external calls excluded from the compiler (R07)
  - missing: External calls with reference arguments left (aggregates.md)

- **`fixedArrays`** (model/partial)
  - source: `Solidity.FixedCopy` (Solidity.AST, `Solidity/AST.lean:89`) — fixed-to-dynamic/fixed copy compatibility evidence
  - admission: `Solidity.Frontend.staticCompilerLength_agrees` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:1197`) — constant length evaluation agrees with solc metadata
  - backend: `Solidity.Evm.size_fixed` (Solidity.Evm.Layout, `Solidity/Evm/Layout.lean:145`) — fixed-array layout size
  - backend: `Solidity.Evm.Sto.checkIndex_fixed` (Solidity.Evm.StorageLemmas, `Solidity/Evm/StorageLemmas.lean:179`) — compiled fixed bounds check agrees
  - no existing anchor: lowering, evm, theorem
  - missing: fixedCopy sources excluded from the core compiler (R19)
  - missing: No fixed memory arrays in the memory compiler (R28)

- **`fixedBytesTypes`** (model/partial)
  - lowering: `Solidity.bytesTy?` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:533`) — bytesN recognized and erased to a uint width
  - lowering: `Solidity.valueRows?` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:554`) — primitive-shape rows for value-like types
  - admission: `Solidity.Frontend.tyOf` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:417`) — solc type strings mapped to model types
  - no existing anchor: source, backend, evm, theorem
  - missing: bytesN is right-aligned, unlike solc's left alignment (R13, semantic-gaps)
  - missing: No semantics or theorem for bytesN indexing, padding or bitwise ops at bytesN

- **`integerTypes`** (model/partial)
  - admission: `Solidity.Frontend.narrowShape` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:459`) — imports nested narrow-width shapes from solc types
  - lowering: `Solidity.narrowTy?` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:498`) — narrow widths carried by the elaborator, erased to uint/int
  - theorem: `Solidity.Bridge.Arith.narrowCheck_full` (SolidityBridge.Arith.Lowering, `Bridge/SolidityBridge/Arith/Lowering.lean:176`) — checked narrow-width guard lowering is correct
  - evm: `Solidity.Evm.External.slt_step` (SolidityBridge.ExternalEvm.SignedOps, `Bridge/SolidityBridge/ExternalEvm/SignedOps.lean:42`) — signed comparison agrees with the external EVM
  - no existing anchor: source, backend
  - missing: PrimTy has only uint/int: width correctness rests entirely on lowering (R13)
  - missing: The compiler refuses signed &,|,^,>> (binInFrag, R12)

- **`internalFunctionTypes`** (model/partial)
  - lowering: `Solidity.fnTag` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:114`) — declaration-identity tags for function values
  - lowering: `Solidity.fnDispatch` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:271`) — finite dispatch table; unset value yields Panic 0x51
  - admission: `Solidity.Frontend.FiniteDispatch.inspect` (Solidity.Frontend.SolcJson.Contract, `Solidity/Frontend/SolcJson/Contract.lean:504`) — finite callee candidates for function values
  - admission: `Solidity.Frontend.storedFunctionMemberType?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:312`) — stored function member types
  - no existing anchor: source, backend, evm, theorem
  - missing: Effectful receivers of stored function members refused (source-admission.md)
  - missing: No compiler support: function values only reach Prog as inlined dispatch

- **`mappings`** (model/partial)
  - source: `Solidity.Ty.isMapping` (Solidity.AST, `Solidity/AST.lean:134`) — mapping reference type with primitive key
  - source: `Solidity.Semantics.tyHasMapping` (Solidity.AST, `Solidity/AST.lean:760`) — guards mapping-carrying copies as undefined
  - admission: `Solidity.Frontend.publicGetterPlan` (Solidity.Frontend.SolcJson.Getters, `Solidity/Frontend/SolcJson/Getters.lean:243`) — named getter components for mapping state
  - backend: `Solidity.Evm.size_mapping` (Solidity.Evm.Layout, `Solidity/Evm/Layout.lean:142`) — mapping layout occupies one root slot
  - no existing anchor: lowering, evm, theorem
  - missing: Compiler admits only uint keys; bool/int keys refused (R14)
  - missing: Slots are symbolic terms with built-in keccak injectivity (R34)

- **`memoryLocation`** (model/partial)
  - source: `Solidity.Heap.Keeps` (Solidity.Semantics.Heap, `Solidity/Semantics/Heap.lean:154`) — heap extension preserves existing object identity
  - source: `Solidity.Heap.alloc` (Solidity.Semantics.Heap, `Solidity/Semantics/Heap.lean:144`) — fresh typed heap allocation
  - backend: `Solidity.Evm.Memory.compile_correct` (Solidity.Evm.MemoryCompile, `Solidity/Evm/MemoryCompile.lean:1245`) — memory-path compiler correctness
  - backend: `Solidity.Evm.Compiler.Compilation.correct` (Solidity.Evm.Compiler, `Solidity/Evm/Compiler.lean:86`) — unified compiler correctness, either path
  - no existing anchor: admission, lowering, evm, theorem
  - missing: Core and memory paths cannot mix in one program (R01/R02)
  - missing: Memory capacity is a premise; no 0x41 panic (R25)
  - missing: Word-addressed headerless memory, not EVM bytes (R31)

- **`recursiveTypes`** (model/missing)
  - source: `Solidity.TypeGraph.Schema.no_inline_cycle` (Solidity.TypeGraph, `Solidity/TypeGraph.lean:143`) — graph schema has no inline cycles
  - source: `Solidity.TypeGraph.Path.read_save` (Solidity.Semantics.RecursiveStorage.Paths, `Solidity/Semantics/RecursiveStorage/Paths.lean:107`) — graph storage read-after-write
  - source: `Solidity.TypeGraph.Legacy.KeyPath.observe_encode` (Solidity.Semantics.RecursiveStorage.Legacy, `Solidity/Semantics/RecursiveStorage/Legacy.lean:158`) — legacy layout encoding observationally faithful
  - source: `Solidity.TypeGraph.CopyPermit.no_mapping` (Solidity.Semantics.RecursiveStorage.Admission, `Solidity/Semantics/RecursiveStorage/Admission.lean:48`) — copy permits exclude mappings
  - no existing anchor: admission, lowering, backend, evm, theorem
  - missing: solc_import, scoped syntax, State, heap and calculus reject recursive structs
  - missing: Graph foundation not connected to the ordinary pipeline or compiler

- **`storageLocation`** (model/partial)
  - source: `Solidity.SRef` (Solidity.Semantics.Storage.Ops, `Solidity/Semantics/Storage/Ops.lean:824`) — typed logical storage paths, no slot numbers
  - source: `Solidity.Storage.find_save_same` (Solidity.Semantics.Storage.Ops, `Solidity/Semantics/Storage/Ops.lean:1300`) — read-after-write along a logical path
  - backend: `Solidity.Evm.save_repr` (Solidity.Evm.Repr, `Solidity/Evm/Repr.lean:444`) — compiled storage write preserves representation
  - theorem: `Solidity.assignStep_sound` (Solidity.Calculus.SoundStore, `Solidity/Calculus/SoundStore.lean:237`) — calculus storage assignment rule sound
  - no existing anchor: admission, lowering, evm
  - missing: Storage reference parameters/arguments refused by the compiler (R09)
  - missing: Slot representation symbolic, not numeric (R34)

- **`stringType`** (model/partial)
  - lowering: `Solidity.stringReason?` (Solidity.Syntax.Elab.Values, `Solidity/Syntax/Elab/Values.lean:862`) — refuses string indexing/length with a reason
  - lowering: `Solidity.dynBytesTy` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:541`) — string shares the byte-array representation
  - admission: `Solidity.Frontend.sourceType` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:269`) — imports string-typed source declarations
  - no existing anchor: source, backend, evm, theorem
  - missing: string storage copies refused by the compiler (R17, string\[\] example)
  - missing: string-keyed mappings route through hashing refused at valIn (R10/R14)

- **`structTypes`** (model/partial)
  - source: `Solidity.Semantics.structDef_rank_lt` (Solidity.AST, `Solidity/AST.lean:734`) — struct graph well-founded via rank, non-recursive
  - admission: `Solidity.Frontend.readStructs` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:493`) — imports struct declarations with identity
  - lowering: `Solidity.Contract.root_okDeep` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:468`) — contract root types deeply valid
  - backend: `Solidity.Evm.offsetIn_disjoint` (Solidity.Evm.Layout, `Solidity/Evm/Layout.lean:172`) — struct field layout offsets disjoint
  - no existing anchor: evm, theorem
  - missing: Reference-member struct construction/defaults absent from memory path (R28)
  - missing: Memory→storage struct copies excluded from core compiler (R19/R20)

- **`tupleTypes`** (model/partial)
  - admission: `Solidity.Frontend.explicitTupleAssignment` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:2109`) — imports simultaneous tuple assignment
  - lowering: `Solidity.elabTuple` (Solidity.Syntax.Elab.Stmt, `Solidity/Syntax/Elab/Stmt.lean:747`) — tuple capture order lowered to sequential stores
  - source: `Solidity.CallRet` (Solidity.Syntax.Scoped, `Solidity/Syntax/Scoped.lean:224`) — multi-value call return binders
  - backend: `Solidity.Evm.CallRetIn` (Solidity.Evm.Compile, `Solidity/Evm/Compile.lean:153`) — compiler admits only none/val return shapes
  - no existing anchor: evm, theorem
  - missing: Tuple/reference returns refused by compiler (R09)
  - missing: Multiple nonlocal/effectful/duplicate tuple targets refused (aggregates.md)
  - missing: Heterogeneous reference-return tuples left

- **`valueTypes`** (model/partial)
  - admission: `Solidity.Frontend.valueTypeSupported` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:739`) — UDVT admission after solc nominal checks
  - admission: `Solidity.Frontend.operatorAlias?` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:762`) — resolves user-defined operators before erasure
  - lowering: `Solidity.Frontend.valueTypeExpr` (Solidity.Frontend.SolcJson.Body, `Solidity/Frontend/SolcJson/Body.lean:745`) — wrap/unwrap erased to primitive shape
  - no existing anchor: source, backend, evm, theorem
  - missing: Nominal UDVT element identities in aggregates left (aggregates.md)
  - missing: No theorem that erasure preserves the primitive width

#### upstream

- **`fixedPoint`** (upstream/notApplicable) — G00 Q6 (full fixed-point support beyond pinned solc); the manifest still scopes it `upstream` until the g00-manifest-rev change lands
  - no existing anchor: source, admission, lowering, backend, evm, theorem
  - missing: no lexer, type, semantics, lowering or compiler support (decision D07)
  - missing: until the manifest change lands, G15 must still refuse it as `upstream`
  - missing: no reference semantics beyond solc 0.8.38's acceptance boundary
  - missing: manifest scope is still `upstream`

### Named combinations

| combination | in-profile IDs | excluded IDs | owners (stage: packages) | R |
|---|---|---|---|---|
| `f{value:v,gas:g}(…)` | callOptions, valueOption | gasOption | source: S00; admission: G10 G15; lowering: G22.01; backend: G43 | R06 |
| `new C{salt:s,value:v}(…)` | callOptions, newContract, valueOption | create2Salt | source: S00; admission: G10 G15; lowering: G22.03; backend: G44.03 |  |
| byte-oriented `fallback(bytes calldata) returns (bytes memory)` | fallbackFunction | rawCalldata, rawReturndata | source: S00; admission: G11 G15; lowering: G20; backend: G40 |  |
| `emit E(args)` under a log-observing property | emitStatement, eventDeclarations | eventLog | source: S04.02; admission: G15; lowering: G23; backend: G31; theorem: G51.02 |  |
| `assembly { revert(add(d,32), mload(d)) }` vs any other assembly | canonicalRethrow | inlineAssembly | source: S00; admission: G11 G15; lowering: G21; backend: G38; evm: G46.02 G47 | R07, R37 |
| `(bool ok,) = a.call{value:v}("")` vs `a.call(data)` | emptyDataValueCall, callOptions, valueOption | lowLevelCall, rawReturndata | source: S00 S04.03; admission: G10 G15; lowering: G22.05; backend: G43; evm: G47 | R06 |
| literal `layout at` base vs physical layout | logicalStorageBase | storageLayout | source: S04.01; admission: G09 G15; backend: G27.05 | R34 |
| `T transient x` vs physical transient slots | transientState | transientLayout | source: S04.03; admission: G15; lowering: G23; backend: G39; evm: G46.03 |  |
| loops/recursion vs gas/stack exhaustion | termination, recursiveCalls | machineResources | source: S03.04; backend: G36.03 G37.02; evm: G46.06 G47; theorem: G49.03; interface: G01 G06; admission: G15 | R08, R27, R38, R39 |
| `send`/`transfer` vs exact stipend | sendTransfer | gasOption, machineResources | source: S04.03; admission: G15; lowering: G22.05; backend: G43; evm: G47 | R32, R33 |
| `type(C).creationCode`/`runtimeCode` vs `address.code` | creationCode, runtimeCode | addressCode, addressCodehash | source: S04.02; admission: G15; lowering: G23; backend: G44.02 |  |
| `block.timestamp` vs other `block.*`/`tx.*` members and hashes | blockTimestamp | blockCoinbase, blockDifficulty, blockPrevrandao, blockNumber, blockGaslimit, blockChainid, blockBasefee, blockBlobbasefee, blockSlotnum, txOrigin, txGasprice, blockhashBuiltin, blobhashBuiltin | source: S04.02; admission: G10 G15; lowering: G23 |  |
| `msg.sender`/`msg.value` vs `msg.data`/`msg.sig` | msgSender, msgValue | rawCalldata | source: S04.02; admission: G10 G15; lowering: G23 |  |
| `msg.data[4:]` (slice of raw calldata) | rangeAccess, calldataLocation | rawCalldata | source: S00; admission: G10 G15; lowering: G21 |  |
| `catch (bytes memory d)` vs raw low-level return bytes | catchClauses, revertPayloads | rawReturndata | source: S04.02; admission: G15; lowering: G21; backend: G38 G41 | R07, R37 |
| `view` external call vs low-level `staticcall` | staticCallRestriction, externalTypedCalls | lowLevelStaticcall | source: S03.03; admission: G15; lowering: G22.01; backend: G42.02 G42.05 |  |
| linked library call vs `delegatecall` | externalLibraryCalls | delegatecall | source: S03.03; admission: G15; lowering: G22.04; backend: G42.04; evm: G47 |  |
| mixed core/memory programs | memoryLocation, storageLocation, whileStatement, internalCalls, sendTransfer, assertBuiltin | — | backend: G24.01 G24.02 G24.03 G24.04 G36.02 G37.01 G37.02 G37.03 G38 G43; theorem: G48 G49.01 G49.03; admission: G15 | R01, R02, R03, R29 |
| whole contracts: dispatch, ABI entry, deployment and sessions | contracts, functions, abiEntryValidation, constructors | — | backend: G40 G41 G44.01; evm: G46.03 G46.04 G46.05 G47; theorem: G49.02 G50.01 G50.02; admission: G15 | R04, R05, R40, R41 |
| loops whose bodies push, pop, delete or pay | whileStatement, forStatement, arrayPush, arrayPop, deleteExpression, sendTransfer | — | lowering: G19; backend: G24.01 G24.02 G24.03 G24.04 G30 G36.02 G36.03 G43; admission: G15 | R21, R22, R24 |
| recursion with memory frames and reference results | recursiveCalls, memoryLocation, returnStatement, internalFunctionTypes | — | source: S03.03; backend: G32 G37.01 G37.02 G37.03 G45.02; evm: G46.02; admission: G15 | R08, R09, R26, R30 |
| storage aliases across pop/delete and pushes | storageAliasing, danglingReferences, arrayPop, arrayPushReference, deleteExpression | — | source: S04.01; lowering: G18.05; backend: G27.03 G28 G30 G35.02; admission: G15 | R16, R18, R36 |
| runtime-length storage copies with nested mappings | storageCopy, dynamicArrays, stringType, mappings, deleteMappingTails | — | lowering: G18.05; backend: G29.01 G29.02 G29.03; admission: G15 | R15, R17 |
| cross-location copies of nested aggregates | referenceCopyRules, memoryLocation, calldataLocation, storageLocation, structTypes, fixedArrays | — | lowering: G18.05 G18.06; backend: G35.01 G35.02 G35.03 G35.04 G35.05 G35.06; evm: G46.02; admission: G15 | R19, R20, R28, R30, R31 |
| hashed mapping keys and dynamic-array bases under the per-run hash premise | mappings, keccakBuiltin, stringType, dynamicBytesType, dynamicArrays | — | lowering: G18.01; backend: G27.02 G27.05 G31; evm: G46.03 G46.05; admission: G15 | R10, R14, R15, R34, R35 |
| checked/unchecked arithmetic at every width, sign and operator | checkedArithmetic, uncheckedArithmetic, integerTypes, bitwise, shifts, compoundAssignment, panicCodes | — | lowering: G16; backend: G25 G27.01; evm: G46.01; admission: G15 | R12, R13 |
| modular and hash builtins on the core path | addmodBuiltin, mulmodBuiltin, keccakBuiltin, sha256Builtin, ripemd160Builtin | — | backend: G25 G31; evm: G46.05; admission: G15 | R10 |
| own balance and payments | addressBalance, sendTransfer, msgValue, nonpayableEntry | — | source: S04.03 S04.04; lowering: G22.05; backend: G24.04 G31 G36.03 G42.03 G43; evm: G46.04 G47; admission: G15 | R11, R32, R33 |
| try/catch over custom errors, panics and revert payloads | tryStatement, catchClauses, errorDeclarations, revertPayloads, panicCodes | — | lowering: G21 G22.01; backend: G38 G41 G42.02 G42.03 G42.06; evm: G47; admission: G15 | R07, R37 |
| transient state through self-calls, callbacks and rollback | transientState, externalSelfCalls, callbackSemantics, rollback | — | source: S04.03; lowering: G23; backend: G39 G42.01 G42.03; evm: G46.03 G47; admission: G15 |  |
| divergence and finite-prefix correspondence | termination, whileStatement, recursiveCalls | — | source: S03.04; backend: G36.03; evm: G47; theorem: G49.03 G50.02; admission: G15 | R38, R39, R40 |
| memory allocation with capacity and `Panic(0x41)` | newMemory, dynamicArrays, panicCodes | — | source: S02 S04.01; backend: G33 G38; evm: G46.02; admission: G15 | R24, R25 |
| calls with storage/memory reference arguments and tuple returns | internalCalls, storageLocation, memoryLocation, tupleTypes, extensionCalls | — | lowering: G17 G20; backend: G37.01 G37.03; admission: G15 | R09 |
| modifiers with repeated placeholders, early returns and constructors | modifiers, modifierPlaceholder, returnStatement, constructors, inheritance | — | source: S03.02; lowering: G19; backend: G36.01 G44.01; admission: G15 |  |
| executable bytecode for every lowered program | contracts, functions, arithmetic, whileStatement | — | backend: G45.01 G45.02 G45.03 G45.04 G45.05 G45.06; evm: G46.01 G46.02 G46.03 G46.04 G46.05 G46.06; theorem: G49.02; admission: G15 | R05 |
| recursive type graphs across storage paths, copies and ABI | recursiveTypes, structTypes, mappings, dynamicArrays, storageCopy, abiEncode | — | source: S04.01; lowering: G18.01 G18.06; backend: G27.04 G35.05; evm: G46.03; admission: G15 |  |
| fixed-point values in arithmetic, storage, ABI and conversions | fixedPoint, explicitConversions, storageLocation, abiEncode, abiDecode | — | source: S02 S04.01 S04.02; lowering: G16 G21; backend: G25 G27.01 G40 G41; evm: G46.01 G46.02; admission: G15 |  |
| structured control realized as EVM jumps | whileStatement, ifStatement, breakStatement | — | backend: G45.03; evm: G46.01 G46.06; admission: G15 | R23 |
| abstract machine vs pinned EVM resources | termination, addressTypes | — | evm: G46.04 G46.06 G47; interface: G01 G06; admission: G15 | R27 |
| getters and ABI of nested aggregates | publicGetters, mappings, structTypes, abiEncode, abiDecode | — | lowering: G18.06 G20 G21; backend: G40 G41; evm: G46.02; admission: G15 |  |
| payable creation and failed-constructor rollback | newContract, creationTry, valueOption, constructorLifetime, rollback | — | source: S04.04; lowering: G22.03; backend: G43 G44.03; evm: G47; theorem: G50.01; admission: G15 |  |

- **`f{value:v,gas:g}(…)`**
  - through its rows: evm: G47; theorem: G48 G49.02 G50.02 G51.02
  - missing: refuse exactly the `gas` part while `{value:}` on typed calls is admitted; `ExtCall` has no value field
- **`new C{salt:s,value:v}(…)`**
  - through its rows: evm: G47; theorem: G48 G49.02 G50.01 G50.02 G51.02
  - missing: salted creation refused while `new C{value:}` is admitted; no compiled creation at all
- **byte-oriented `fallback(bytes calldata) returns (bytes memory)`**
  - through its rows: evm: G46.02 G47; theorem: G48 G49.02 G50.02
  - missing: the parameterless fallback is admitted, the byte-oriented form refused, by a checked classification
- **`emit E(args)` under a log-observing property**
  - through its rows: evm: G46.02
  - missing: no erasure-soundness theorem: argument effects kept, logs dropped, log-observing specs refused
- **`assembly { revert(add(d,32), mload(d)) }` vs any other assembly**
  - through its rows: theorem: G48 G49.01 G49.02 G49.03 G51.01
  - missing: the 20 Yul symbols of the idiom have no wave-1 parser (G00 gap 5; owned here by G11)
  - missing: byte-level `revert(ptr, len)` needs byte memory (G04 R31)
- **`(bool ok,) = a.call{value:v}("")` vs `a.call(data)`**
  - through its rows: theorem: G48 G49.02 G50.02 G51.02
  - missing: empty-data value call is not compiled (R06); arbitrary data must be refused exactly
- **literal `layout at` base vs physical layout**
  - through its rows: lowering: G18.02; evm: G46.03; theorem: G48 G49.01 G49.02 G51.01
  - missing: no theorem relating a logical base to the internal representation
- **`T transient x` vs physical transient slots**
  - through its rows: theorem: G48 G49.02 G50.02 G51.01
  - missing: no compiled transient state; TLOAD/TSTORE bridge absent
- **loops/recursion vs gas/stack exhaustion**
  - through its rows: lowering: G19 G20
  - source: `Solidity.recDepth` (Solidity.Syntax.Scoped, `Solidity/Syntax/Scoped.lean:469`) — fixed source recursion depth
  - missing: resource exhaustion must be an allowed failure (D09), not an observation; no resource-indexed theorem
- **`send`/`transfer` vs exact stipend**
  - through its rows: theorem: G48 G49.02 G50.02 G51.02
  - missing: stipend-dependent recipient behaviour is over-approximated (D15, D18); `send` not compiled
- **`type(C).creationCode`/`runtimeCode` vs `address.code`**
  - through its rows: evm: G46.02 G47; theorem: G48 G49.02 G50.01
  - missing: the artifact-table parameter (D06) is not in the contracts; no code observation of deployed accounts
- **`block.timestamp` vs other `block.*`/`tx.*` members and hashes**
  - through its rows: backend: G31; evm: G46.04; theorem: G48 G49.02 G50.02
  - missing: refusal is by solc member names; the checked frontend must classify each member
- **`msg.sender`/`msg.value` vs `msg.data`/`msg.sig`**
  - through its rows: backend: G31 G43; evm: G46.04 G47; theorem: G48 G49.02 G50.02
  - missing: exact member classification by the checked frontend
- **`msg.data[4:]` (slice of raw calldata)**
  - through its rows: backend: G35.03 G40; evm: G46.01 G46.02; theorem: G48 G49.01 G49.02 G49.03 G51.01
  - missing: typed calldata slices admitted, slices of raw calldata refused, by checked classification
- **`catch (bytes memory d)` vs raw low-level return bytes**
  - through its rows: evm: G46.02 G47; theorem: G48 G49.02 G49.03 G50.02 G51.02
  - missing: caught revert bytes are not compiled (R07); returndata of other calls refused
- **`view` external call vs low-level `staticcall`**
  - through its rows: evm: G47; theorem: G48 G49.02 G50.02 G51.02
  - missing: no static-context enforcement for arbitrary callees
- **linked library call vs `delegatecall`**
  - through its rows: theorem: G48 G49.02 G50.02 G51.02
  - missing: the library call is itself a DELEGATECALL in the bytecode: the bridge must admit exactly the compiler-emitted linked form
- **mixed core/memory programs**
  - through its rows: source: S01 S02 S03.01 S03.03 S04.01 S04.02 S04.03; lowering: G18.02 G18.03 G19 G20 G21 G22.02 G22.05; evm: G46.01 G46.02 G46.03 G46.06 G47
  - backend: `Solidity.Evm.Compiler.Compilation.correct` (Solidity.Evm.Compiler, `Solidity/Evm/Compiler.lean:86`) — unified entry, one path per program
  - missing: one compiler per whole program; a core prefix cannot feed a memory suffix
- **whole contracts: dispatch, ABI entry, deployment and sessions**
  - through its rows: source: S00 S01 S03.01 S03.02 S03.03 S04.02 S04.04; lowering: G19 G20 G21 G22.03
  - missing: the compiler theorems relate one program from a represented state; no contract-level statement
- **loops whose bodies push, pop, delete or pay**
  - through its rows: source: S02 S03.01 S03.03 S04.01 S04.03; evm: G46.01 G46.02 G46.03 G46.06 G47; theorem: G48 G49.01 G49.02 G49.03 G50.02 G51.01 G51.02
  - backend: `Solidity.Evm.Examples.loop_push_rejected` (Solidity.Evm.Examples, `Solidity/Evm/Examples.lean:386`) — kernel-checked rejection of a pushing loop
  - missing: core loop bodies must not push/pay/shrink; no loops on the memory path
- **recursion with memory frames and reference results**
  - through its rows: lowering: G18.03 G19 G20; theorem: G48 G49.01 G49.02 G49.03 G51.01
  - missing: inline calls, value arguments only, fixed source depth; frames in memory per D10
- **storage aliases across pop/delete and pushes**
  - through its rows: evm: G46.02 G46.03; theorem: G48 G49.01 G49.02 G49.03 G51.01
  - backend: `Solidity.Evm.Examples.rejected` (Solidity.Evm.Examples, `Solidity/Evm/Examples.lean:354`) — kernel-checked rejections incl. dangling alias
  - missing: fragile aliases forgotten at a shrink; `T storage p = arr.push()` refused
- **runtime-length storage copies with nested mappings**
  - through its rows: source: S00 S01 S04.01; evm: G46.02 G46.03 G46.05; theorem: G48 G49.01 G49.02 G49.03 G51.01
  - missing: copies only for static types; tail clearing and mapping preservation unproved for runtime lengths
- **cross-location copies of nested aggregates**
  - through its rows: source: S00 S01 S04.01; theorem: G48 G49.02 G49.03 G51.01
  - missing: memory path: primitive-member storage struct → memory only
- **hashed mapping keys and dynamic-array bases under the per-run hash premise**
  - through its rows: source: S00 S01 S04.01 S04.02; theorem: G48 G49.01 G49.02 G49.03 G51.01
  - missing: uint keys only; symbolic slots with global injectivity; KECCAK256 from the stack
- **checked/unchecked arithmetic at every width, sign and operator**
  - through its rows: source: S00 S01 S02 S04.02; theorem: G48 G49.01 G49.02 G49.03 G51.01
  - missing: signed bitwise/arithmetic `>>` refused by the compiler; width rests on lowering
- **modular and hash builtins on the core path**
  - through its rows: source: S02 S04.02; lowering: G16 G23; theorem: G48 G49.01 G49.02 G51.01
  - missing: `valIn` refuses `modular` and `hash` values
- **own balance and payments**
  - through its rows: theorem: G48 G49.02 G50.02 G51.02
  - backend: `Solidity.Evm.compile_net` (Solidity.Evm.Correct, `Solidity/Evm/Correct.lean:1157`) — net payments on machine success
  - missing: `address(this).balance` refused; payment asymmetry; recipient code not run
- **try/catch over custom errors, panics and revert payloads**
  - through its rows: source: S00 S01 S03.03 S04.02 S04.03; theorem: G48 G49.02 G49.03 G50.01 G50.02 G51.02
  - missing: `tryCall`/`revertData`/`catchData` out of the compiler; revert bytes erased
- **transient state through self-calls, callbacks and rollback**
  - through its rows: theorem: G48 G49.02 G50.02 G51.01 G51.02
  - source: `Solidity.ContractWorld.World.resetTransient_persistent` (Solidity.Semantics.TransientWorld, `Solidity/Semantics/TransientWorld.lean:107`) — transaction reset keeps persistent storage
  - missing: no compiled transient state; sharing across frames needs G42 (deferred check of G39)
- **divergence and finite-prefix correspondence**
  - through its rows: lowering: G19 G20
  - backend: `Solidity.Evm.compile_terminates_iff` (SolidityBridge.Evm, `Bridge/SolidityBridge/Evm.lean:171`) — successful trace iff source success (pays = false)
  - missing: divergence matched classically to `.fault`; the Bridge LTS relates successful boundaries only
- **memory allocation with capacity and `Panic(0x41)`**
  - through its rows: lowering: G18.02 G18.03 G18.04 G18.05 G21; theorem: G48 G49.01 G49.02 G49.03 G51.01
  - missing: capacity is a theorem premise; no `0x41` panic at `2^64` lengths or memory exhaustion
- **calls with storage/memory reference arguments and tuple returns**
  - through its rows: source: S00 S01 S03.03 S04.01; evm: G46.01 G46.02 G46.03; theorem: G48 G49.01 G49.02 G49.03 G51.01
  - missing: value arguments and `.none`/`.val` returns only; `callReceiver` refused
- **modifiers with repeated placeholders, early returns and constructors**
  - through its rows: evm: G46.01 G46.02 G47; theorem: G48 G49.01 G49.02 G49.03 G50.01 G51.01
  - missing: no theorem for `wrapMods`/`lowerReturns`; via-IR re-initialisation at each `_` not followed
- **executable bytecode for every lowered program**
  - through its rows: source: S00 S01 S02 S03.01 S03.03; lowering: G16 G19 G20
  - missing: the target is the word-level `Machine` with macro instructions; no instruction selection, assembler or byte encoding
- **recursive type graphs across storage paths, copies and ABI**
  - through its rows: theorem: G48 G49.01 G49.02 G49.03 G51.01
  - missing: the graph foundation (`TypeGraph`, `RecursiveStorage`) is not connected to import, `State` or the compiler; recursive ABI shapes are refused
- **fixed-point values in arithmetic, storage, ABI and conversions**
  - through its rows: theorem: G48 G49.01 G49.02 G49.03 G51.01
  - missing: no fixed-point support at any stage (D07)
- **structured control realized as EVM jumps**
  - through its rows: source: S03.01; lowering: G19; theorem: G48 G49.01 G49.02 G49.03 G51.01 G51.02
  - missing: structured `LOOP` and relative jumps; `checked_exp_helper` unrolled 255 times
- **abstract machine vs pinned EVM resources**
  - through its rows: source: S00 S01 S03.04; lowering: G16 G19; backend: G25 G36.03 G37.02 G42.02 G42.05; theorem: G48 G49.02 G49.03 G50.02 G51.01 G51.02
  - missing: no gas, no stack limit, 256-bit addresses, `CALL` without forwarded gas
- **getters and ABI of nested aggregates**
  - through its rows: source: S00 S01 S03.03 S04.01 S04.02; theorem: G48 G49.02 G49.03 G50.01 G51.01
  - missing: enum/bytes/nested aggregate getter results refused; no ABI in the compiler theorems
- **payable creation and failed-constructor rollback**
  - missing: creation through ContractWorld fragments only; no compiled initcode

### Ledger-symbol combinations

Upstream symbols mapped to in-profile and non-profile rows (G00's `combination-*`). Each is owned by G15 (extraction) plus the admission owners of its in-profile rows; `--check` fails if one of those rows is unowned.

- **AddressTypeMembers**, combination-unresolved (1): `call` — owners G10 G13 G15
- **astClasses**, combination-unresolved (3): `FunctionCallOptions`, `InlineAssembly`, `StorageLayoutSpecifier` — owners G09 G10 G11 G13 G15
- **astClasses**, combination-upstream (5): `ElementaryTypeName`, `Literal`, `ModifierDefinition`, `PlaceholderStatement`, `TypeName` — owners G08 G09 G11 G13 G14 G15
- **compilerTokens**, combination-unresolved (16): `Abstract`, `Anonymous`, `Assembly`, `Comma`, `Contract`, `Event`, `External`, `Fallback`, `Indexed`, `LBrace`, `LParen`, `RBrace`, `RParen`, `Returns`, `Semicolon`, `Virtual` — owners G09 G10 G11 G12 G13 G14 G15
- **compilerTokens**, combination-upstream (17): `Address`, `Assign`, `AssignAdd`, `AssignBitAnd`, `AssignBitOr`, `AssignBitXor`, `AssignDiv`, `AssignMod`, `AssignMul`, `AssignSub`, `Bool`, `Bytes`, `Fixed`, `LBrack`, `Payable`, `RBrack`, `String` — owners G09 G10 G11 G13 G14 G15
- **expressionAlternatives**, combination-unresolved (2): `FunctionCallOptions`, `NewExpr` — owners G10 G13 G15
- **expressionAlternatives**, combination-upstream (1): `ShiftOperation` — owners G10 G13 G15
- **functionKinds**, combination-unresolved (3): `BareCall`, `Creation`, `Event` — owners G10 G11 G13 G15
- **functionKinds**, combination-upstream (1): `SetValue` — owners G10 G13 G15
- **globalNames**, combination-unresolved (2): `block`, `msg` — owners G10 G13 G15
- **lexerRules**, combination-unresolved (27): `Abstract`, `Anonymous`, `Assembly`, `AssemblyLBrace`, `At`, `Comma`, `Contract`, `Event`, `External`, `Fallback`, `Indexed`, `LBrace`, `LParen`, `Layout`, `RBrace`, `RParen`, `Returns`, `Semicolon`, `Virtual`, `YulComma`, `YulDecimalNumber`, `YulEVMBuiltin`, `YulIdentifier`, `YulLParen`, `YulRBrace`, `YulRParen`, `YulWS` — owners G08 G09 G10 G11 G12 G13 G14 G15
- **lexerRules**, combination-upstream (22): `Address`, `Assign`, `AssignAdd`, `AssignBitAnd`, `AssignBitOr`, `AssignBitXor`, `AssignDiv`, `AssignMod`, `AssignMul`, `AssignSub`, `Bool`, `Bytes`, `Fixed`, `FixedBytes`, `LBrack`, `Payable`, `RBrack`, `SignedIntegerType`, `String`, `SubDenomination`, `Ufixed`, `UnsignedIntegerType` — owners G08 G09 G10 G11 G13 G14 G15
- **nativeMemberOwners**, combination-unresolved (1): `AddressType` — owners G10 G13 G15
- **nativeMemberOwners**, combination-upstream (1): `FunctionType` — owners G13 G15
- **parserRules**, combination-unresolved (12): `assemblyFlags`, `assemblyStatement`, `contractDefinition`, `eventDefinition`, `eventParameter`, `fallbackFunctionDefinition`, `yulBlock`, `yulExpression`, `yulFunctionCall`, `yulLiteral`, `yulPath`, `yulStatement` — owners G09 G11 G13 G14 G15
- **parserRules**, combination-upstream (5): `assignOp`, `elementaryTypeName`, `literalWithSubDenomination`, `modifierDefinition`, `typeName` — owners G08 G09 G10 G11 G13 G14 G15
- **yulBuiltins**, combination-unresolved (3): `add`, `mload`, `revert` — owners G11 G15

### G04 restrictions

| R | G04 discharging groups | G03 rows |
|---|---|---|
| R01 | G24 (unified entry), G49.01, G49.03. ⟳ memory-loops, memory-internal-calls | `modifiers`, `memoryLocation`, `blocks`, `assertBuiltin`, mixed core/memory programs |
| R02 | G24 | `memoryLocation`, `blocks`, mixed core/memory programs |
| R03 | G49.03 (coverage and non-vacuity), G48 | mixed core/memory programs |
| R04 | G40, G41, G44, G49.02, G50 | `pragmaAbicoder`, `contracts`, `libraries`, `inheritance`, `functions`, `constructors`, `receiveFunction`, `visibility`, `immutables`, `names`, `rangeAccess`, `functionCalls`, `abiEncode`, `abiEncodePacked`, `abiEncodeWithSelector`, `abiEncodeWithSignature`, `abiEncodeCall`, `abiDecode`, `memoryAliasing`, `abiEntryValidation`, `constructorLifetime`, `nonpayableEntry`, whole contracts: dispatch, ABI entry, deployment and sessions |
| R05 | G45, G46, G47, G49.02. ⟳ evm-control-flow, evm-byte-memory, evm-storage-slots | `contracts`, `arithmetic`, `blocks`, `creationCode`, `runtimeCode`, whole contracts: dispatch, ABI entry, deployment and sessions, executable bytecode for every lowered program |
| R06 | G43, G42.02 | `receiveFunction`, `callOptions`, `valueOption`, `sendTransfer`, `emptyDataValueCall`, `f{value:v,gas:g}(…)`, `(bool ok,) = a.call{value:v}("")` vs `a.call(data)` |
| R07 | G42, G38, G21, G41. ⟳ diamond-try, revert-outcome-specs, readonly-external | `interfaces`, `publicGetters`, `errorDeclarations`, `externalFunctionTypes`, `functionCalls`, `tryStatement`, `catchClauses`, `revertStatement`, `canonicalRethrow`, `requireBuiltin`, `revertBuiltin`, `externalTypedCalls`, `externalSelfCalls`, `revertPayloads`, `rollback`, `staticCallRestriction`, `assembly { revert(add(d,32), mload(d)) }` vs any other assembly, `catch (bytes memory d)` vs raw low-level return bytes, try/catch over custom errors, panics and revert payloads |
| R08 | G37.02, S03.03 (no fixed inlining or fuel), S03.04 | `functions`, `freeFunctions`, `modifiers`, `functionCalls`, `recursiveCalls`, `termination`, loops/recursion vs gas/stack exhaustion, recursion with memory frames and reference results |
| R09 | G37.01, G37.03, G20. ⟳ memory-internal-calls, function-ref-args | `libraries`, `functions`, `freeFunctions`, `modifiers`, `usingFor`, `tupleTypes`, `storageLocation`, `tupleExpressions`, `shortCircuit`, `functionCalls`, `expressionStatements`, `returnStatement`, `internalCalls`, `storageAliasing`, recursion with memory frames and reference results, calls with storage/memory reference arguments and tuple returns |
| R10 | G25 (modular), G31 + G46.05 (hashes), G23 | `stringLiterals`, `unicodeLiterals`, `hexLiterals`, `stringType`, `indexAccess`, `shortCircuit`, `addmodBuiltin`, `mulmodBuiltin`, `keccakBuiltin`, `sha256Builtin`, `ripemd160Builtin`, `ecrecoverBuiltin`, `erc7201Builtin`, `bytesConcat`, `typeName`, `errorEventSelector`, hashed mapping keys and dynamic-array bases under the per-run hash premise, modular and hash builtins on the core path |
| R11 | G31, G46.04 | `memberAccess`, `addressBalance`, own balance and payments |
| R12 | G25 (compiler); S02/G16 for the source-refused signed `<<`/`~`, if in profile | `integerTypes`, `unaryArithmetic`, `arithmetic`, `bitwise`, `shifts`, `uncheckedBlock`, `checkedArithmetic`, `uncheckedArithmetic`, checked/unchecked arithmetic at every width, sign and operator |
| R13 | G16, G25, G27.01 | `numericLiterals`, `addressLiterals`, `enumDeclarations`, `integerTypes`, `fixedBytesTypes`, `indexAccess`, `unaryArithmetic`, `arithmetic`, `bitwise`, `comparisons`, `explicitConversions`, `implicitConversions`, `ripemd160Builtin`, `wrapUnwrap`, checked/unchecked arithmetic at every width, sign and operator |
| R14 | G27.02 (and R10's owners for hashed keys) | `stateVariables`, `stringType`, `mappings`, `indexAccess`, hashed mapping keys and dynamic-array bases under the per-run hash premise |
| R15 | G27.05, G18.01 | `typeValidation`, runtime-length storage copies with nested mappings, hashed mapping keys and dynamic-array bases under the per-run hash premise |
| R16 | G28 (confirm via G13 admission) | `variableDeclarations`, `defaultInitialization`, `typeValidation`, storage aliases across pop/delete and pushes |
| R17 | G29.01–G29.03 | `stringLiterals`, `unicodeLiterals`, `stateVariables`, `dynamicBytesType`, `stringType`, `assignment`, `typeName`, `storageCopy`, runtime-length storage copies with nested mappings |
| R18 | G30, G28, G35.02, G27.03 | `increments`, `compoundAssignment`, `arrayPush`, `arrayPushReference`, storage aliases across pop/delete and pushes |
| R19 | G35.02, G35.04. ⟳ memory-storage-copy | `fixedArrays`, `structTypes`, `assignment`, `storageCopy`, `referenceCopyRules`, cross-location copies of nested aggregates |
| R20 | G35.01–G35.06, G18.05. ⟳ memory-storage-copy, abi-lazy-calldata | `structDeclarations`, `structTypes`, `calldataLocation`, `rangeAccess`, `assignment`, `abiDecode`, `memoryAliasing`, `referenceCopyRules`, cross-location copies of nested aggregates |
| R21 | G36.02, G36.03 (after G43), G19. ⟳ memory-loops | `increments`, `deleteExpression`, `whileStatement`, `forStatement`, `doWhileStatement`, `arrayPush`, `arrayPop`, `deleteMappingTails`, loops whose bodies push, pop, delete or pay |
| R22 | G36.02, G24. ⟳ memory-loops | `dynamicArrays`, `newMemory`, `whileStatement`, `forStatement`, `doWhileStatement`, loops whose bodies push, pop, delete or pay |
| R23 | G45.03. ⟳ evm-control-flow | `ifStatement`, structured control realized as EVM jumps |
| R24 | S04.01 / S02 (source length bound and `0x41`), G30, G38 | `dynamicArrays`, `arrayLength`, `panicCodes`, loops whose bodies push, pop, delete or pay, memory allocation with capacity and `Panic(0x41)` |
| R25 | G33, G38 (`0x41`). ⟳ evm-byte-memory | `memoryLocation`, `newMemory`, `panicCodes`, memory allocation with capacity and `Panic(0x41)` |
| R26 | G32, G37.01, G45.02 | recursion with memory frames and reference results |
| R27 | G01/G06 (definition), G46.04, G46.06, G47 | `addressTypes`, `explicitConversions`, `msgSender`, `thisAddress`, `internalCalls`, `recursiveCalls`, loops/recursion vs gas/stack exhaustion, abstract machine vs pinned EVM resources |
| R28 | G18.03, G33, G34. ⟳ memory-reference-arrays, memory-reference-structs | `structDeclarations`, `dynamicArrays`, `fixedArrays`, `structTypes`, `inlineArrays`, `deleteExpression`, `conditional`, `structConstruction`, `newMemory`, `variableDeclarations`, `bytesConcat`, `stringConcat`, `defaultInitialization`, cross-location copies of nested aggregates |
| R29 | G24, G28, G37, G38, G43. ⟳ memory-internal-calls | `increments`, `deleteExpression`, `compoundAssignment`, `expressionStatements`, `assertBuiltin`, mixed core/memory programs |
| R30 | G32 | `memoryAliasing`, recursion with memory frames and reference results, cross-location copies of nested aggregates |
| R31 | G32, G46.02. ⟳ evm-byte-memory | `hexLiterals`, `dynamicBytesType`, `memoryLocation`, `canonicalRethrow`, `bytesConcat`, `stringConcat`, cross-location copies of nested aggregates |
| R32 | Exact agreement on success and refusal of every payment, with the same history-dependent recipient strategy read by source and machine. No proof constructs the stale disjunct, so the interim statement-only strengthening (§3 item 1) is still open. | `stateMutability`, `sendTransfer`, `send`/`transfer` vs exact stipend, own balance and payments |
| R33 | Replace `Machine.accepts`/`Sim.oracle`'s per-transaction table by: untyped recipients answer any outcome, depending on history; recipients in the compiled system run their code; any recipient frame may fail with a revert its caller sees. Precompile addresses follow their EVM definitions, never environment code. | `receiveFunction`, `callOptions`, `externalTypedCalls`, `sendTransfer`, `emptyDataValueCall`, `worldAssumptions`, `send`/`transfer` vs exact stipend, own balance and payments |
| R34 | Numeric slots under a per-run hypothesis that the preimages hashed by the execution prefix do not collide, plus a random-oracle lemma bounding its failure probability (about q²/2²⁵⁷). The hash is a fixed parameter instantiated by keccak. `no_injective_slot_encoding` (T21) stays as the evidence that no global premise is possible. The second-round decision (on `origin/master` after this base) extends the premise to regions of length at most L based at hashed slots (about q²·L/2²⁵⁶), which covers the offsets `Slot.add` adds. | `boolType`, `mappings`, `storageLocation`, `keccakBuiltin`, `logicalStorageBase`, literal `layout at` base vs physical layout, hashed mapping keys and dynamic-array bases under the per-run hash premise |
| R35 | Osaka `KECCAK256` over memory bytes; the per-run premise ranges over those byte preimages. | `keccakBuiltin`, hashed mapping keys and dynamic-array bases under the per-run hash premise |
| R36 | Compile alias use after `pop`/`delete` with solc's logical slot behaviour by relating the source's past-the-end `shadow` slots in `ReprAt`. Physical packing stays unobservable. The same relation unblocks `push()` of a struct (R18). The source must first keep what solc keeps when `push(v)` lands on a recycled slot (`SVal.strip`). | `ifStatement`, `arrayPop`, `storageAliasing`, `danglingReferences`, storage aliases across pop/delete and pushes |
| R37 | G38, G21, G41. ⟳ revert-outcome-specs | `arithmetic`, `revertStatement`, `canonicalRethrow`, `assertBuiltin`, `requireBuiltin`, `revertBuiltin`, `addmodBuiltin`, `mulmodBuiltin`, `panicCodes`, `revertPayloads`, `assembly { revert(add(d,32), mload(d)) }` vs any other assembly, `catch (bytes memory d)` vs raw low-level return bytes, try/catch over custom errors, panics and revert payloads |
| R38 | G01 (definition), G36.03, G47, G49.03 | `whileStatement`, `doWhileStatement`, `termination`, loops/recursion vs gas/stack exhaustion, divergence and finite-prefix correspondence |
| R39 | S03.04, G01/G06 resource abstraction | `recursiveCalls`, `termination`, loops/recursion vs gas/stack exhaustion, divergence and finite-prefix correspondence |
| R40 | G49.03, G50.02 | whole contracts: dispatch, ABI entry, deployment and sessions, divergence and finite-prefix correspondence |
| R41 | G41, G49.02 | `returnStatement`, `rollback`, whole contracts: dispatch, ABI entry, deployment and sessions |

### Decision-driven obligations

`in-flight` names the parallel lanes (sibling sessions of this batch or Codex lanes) that change the row; they are not repository paths.

| ID | obligation | decisions | owners (stage: packages) | in-flight |
|---|---|---|---|---|
| D01 | Precise refusal of the 30 confirmed exclusions | G00 Q1 — the 30 recorded exclusions | source: S00; admission: G07 G08 G11 G15; theorem: G48 G49.03 | — |
| D02 | Approved abstract premises: opaque hashes and `ecrecover` as fixed parameters, `msg`/`block`/`this`/balance as quantified inputs; replace `worldAssumptions` and the payment boolean; no-callback reading as a proved special case | G00 Q2 — premises of the 23 `abstract` rows; Readings | source: S04.02 S04.03; lowering: G22.02 G23; backend: G31 G43; evm: G46.04 G46.05 G47; theorem: G49.02 G51.02 | diamond-payments; readonly-external |
| D03 | Osaka fork pin for the pinned EVM semantics and the compiled bytecode | G00 Q3 — EVM fork; Pins (G00, G05, G06) | evm: G06 G46.06 G47; theorem: G49.02; validation: G54.01 | g06-osaka-repin; g06-evm-interface |
| D04 | Public theorem over solc's two pipelines: the legacy and via-IR `EvalOrder` settings (revised 2026-10-29: the other six flag combinations are dropped) | G00 Q4 — settings; G00 Q4 (revised) / G05 Q2 — settings; Pins (G00, G05, G06) | source: S02 S03.01 S03.02 S03.03 S04.02; admission: G05 G15; lowering: G16 G17 G19; backend: G26; theorem: G49.02 G49.03 | g05-frontend; g01-contracts-rev |
| D05 | Frozen profile solc 0.8.38; 0.8.34 fixtures only as SolKey compatibility checks | G00 Q4 — settings; Pins (G00, G05, G06) | admission: G05 G15; theorem: G48; validation: G53 G54.02 | g05-frontend |
| D06 | Artifact table: `creationCode`/`runtimeCode` read from G01's whole-input `Artifact` table, a source-semantics parameter | G00 Q5 — `creationCode`/`runtimeCode`; Contracts (G01) | source: S04.02; lowering: G23; backend: G44.02; evm: G47; theorem: G49.02 G50.01; interface: G01 G07 | g01-contracts-rev |
| D07 | Full fixed-point types beyond pinned solc's acceptance boundary | G00 Q6 — fixed-point types; Manifest; Fixed point — `*` and `/`; Fixed point — implicit conversions; Fixed point — explicit conversions out of range; Fixed point — rounding; Fixed point — shifts; Fixed point — unary minus on `ufixed`; Fixed point — `++`/`--`; Fixed point — explicit fixed/integer and `bytesM` conversions; Fixed point | source: S00 S01 S02; admission: G08 G09 G13 G15; lowering: G16; backend: G25; evm: G46.01; theorem: G49.02 G49.03 | g00-manifest-rev; fixed-point-semantics |
| D08 | Idealized source resources: unbounded fuel and recursion | G01 Q1 — source resources | source: S03.03 S03.04; lowering: G20; backend: G37.02; theorem: G49.03 | — |
| D09 | Resource exhaustion as an allowed failure; code-size limits (EIP-170/3860) idealized | G01 Q2 — fixed EVM limits; G06 Q2 — Osaka gas caps; Resources in the contracts; Contracts (G01) | source: S03.04 S04.04; backend: G44.02; evm: G06 G46.06 G47; theorem: G49.03 G50.02; interface: G01 | g01-contracts-rev |
| D10 | Memory frames for recursion: internal calls keep their frames in memory, depth bounded by gas only | G01 Q2 — fixed EVM limits | backend: G32 G37.01 G37.02 G45.02; evm: G46.02 G46.06; theorem: G49.03 | memory-internal-calls |
| D11 | Per-run hash premise and bound: the preimages hashed by an execution prefix do not collide, plus a random-oracle collision bound (about q²/2²⁵⁷) | G01 Q3 / G04 Q1 — hash collisions; Hash regions; Hash bound; Contracts (G01) | source: S04.02; backend: G27.05 G31; evm: G46.03 G46.05; theorem: G49.02 G50.02; interface: G01 | hash-collision-bound; g01-contracts-rev; evm-storage-slots |
| D12 | History-dependent callee strategies with unbounded reentrancy; address 0 has no code | G01 Q4 — environment | source: S03.03 S04.03; lowering: G22.02; backend: G42.03; evm: G47; theorem: G50.02 G51.02 | — |
| D13 | Observation: the full `Event` list with exact ABI and revert bytes, `Panic` codes included | G01 Q5 — observation | source: S04.02; lowering: G21; backend: G38 G41 G42.02 G44.03; evm: G46.02 G47; theorem: G49.02 G50.02 | revert-outcome-specs |
| D14 | `decode : EvmWorld → Option IntrinsicWorld` exported by the public theorem | G01 Q6 — state transfer; Contracts (G01) | backend: G24.02 G27.05; evm: G46.02 G46.03 G47; theorem: G49.02 G50.02; interface: G01 | g01-contracts-rev |
| D15 | Gas over-approximation: callee answers range over all outcomes regardless of forwarded gas | G01 Q7 — gas and the environment | source: S04.03; backend: G42.02; evm: G47; theorem: G50.02 | — |
| D16 | System boundary: the whole input, every contract and linked library, is compiled | G01 Q8 — system boundary; G05 Q1 — library addresses; Frontend (G05); Pins (G00, G05, G06) | admission: G05 G12 G15; lowering: G22.04; backend: G42.04 G44.02; evm: G47; theorem: G49.02 G50.01 | g05-frontend |
| D17 | Storage aliases after `pop`/`delete` in profile, with solc's logical slot behaviour | G04 Q2 — storage aliases after `pop`/`delete`; Readings | source: S04.01; lowering: G18.05; backend: G28 G30; theorem: G49.02 | — |
| D18 | Payment acceptance: any outcome for untyped recipients, history-dependent; typed recipients run their own code | G04 Q3 — payment acceptance | source: S04.03; lowering: G22.02 G22.05; backend: G24.04 G43; evm: G47; theorem: G50.02 | diamond-payments |
| D19 | Frame failure semantics: any external call frame may fail with a revert its caller sees (1024 depth, forwarded-gas exhaustion in callbacks) | Follow-up — nested-frame failures; Resources in the contracts | source: S03.03 S04.03; lowering: G22.01 G22.02; backend: G42.02 G42.03 G42.06; evm: G47; theorem: G50.02 | — |
| D20 | Transaction failure semantics: any transaction may revert from gas exhaustion and the session continues | Follow-up — gas exhaustion; G06 Q2 — Osaka gas caps; Resources in the contracts | source: S04.04; evm: G47; theorem: G50.02; interface: G01 | g01-contracts-rev |
| D21 | Sender funds: `msg.value` bounded by the sender's ledger balance; unaffordable transactions never execute | Follow-up — sender funds | source: S04.04; backend: G43; evm: G46.04 G47; theorem: G50.02 | — |
| D22 | Precompile addresses behave as their Osaka definitions, never as environment code | Follow-up — precompile addresses | source: S04.03; backend: G42.02; evm: G46.05 G47; theorem: G50.02 | — |
| D23 | Forced ether: the environment may credit the system's balance between transactions and during environment frames; the ledger records the credits | G06 Q1 — forced ether | source: S04.03 S04.04; lowering: G22.05; backend: G43; evm: G46.04 G47; theorem: G50.02; interface: G01 | g01-contracts-rev |
| D24 | Stipend payments to our own instances: a compiler-independent source cost rule decides which `receive`/fallback bodies fit 2300 gas; the compiler is proved to fit every admitted body | G06 Q3 — stipend payments to our own instances | source: S04.03; lowering: G22.05; backend: G43 G45.06; evm: G46.06 G47; theorem: G50.02; interface: G01 | — |
| D25 | Shared compiler foundation: frozen slot, state and statement interfaces as children of G24 ahead of wave 3 | G03 Q1 — shared compiler foundation; Roadmap (G03) | backend: G24.01 G24.02 G24.03 G24.04 | — |

- **D01 Precise refusal of the 30 confirmed exclusions**
  - admission: `Solidity.Language.Feature.exclusion_complete` (Solidity.Language.Features, `Solidity/Language/Features.lean:1936`) — every excluded feature has a structured diagnostic
  - admission: `Solidity.Language.Unmodelled.excluded` (Solidity.Language.Features, `Solidity/Language/Features.lean:1910`) — every diagnostic denotes an excluded feature
  - admission: `Solidity.Frontend.Source.ScopeScan.within` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:299`) — a successful scan's feature list is within the profile
  - missing: refusal is decided on solc's JSON AST (`ScopeScan`), not by a checked parser against S00's grammar
  - missing: no theorem that `Admission.sound` rejects exactly the excluded IDs and their G00 combinations
  - missing: G07 controls for each excluded family (malformed/excluded source rejected) are not written
- **D02 Approved abstract premises: opaque hashes and `ecrecover` as fixed parameters, `msg`/`block`/`this`/balance as quantified inputs; replace `worldAssumptions` and the payment boolean; no-callback reading as a proved special case**
  - theorem: `Solidity.Main.noCallback_iff` (Solidity.Theorems, `Solidity/Theorems.lean:239`) — no-callback validity agrees for callback-free formulas
  - theorem: `Solidity.Bridge.Adversary.holdsC_iff_all_policies` (SolidityBridge.Adversary, `Bridge/SolidityBridge/Adversary.lean:146`) — callback modality equals quantification over adversary policies
  - missing: the payment-acceptance boolean (`Machine.accepts`, tied by `Sim.oracle`) is still a premise of the core theorem (G04 R33)
  - missing: `noCallback_iff` proves agreement only for formulas without callbacks; the no-callback reading is not derived from the history-dependent callee semantics
  - missing: `this` from deployment and the own balance following the ledger are not stated in any contract
- **D03 Osaka fork pin for the pinned EVM semantics and the compiled bytecode**
  - missing: the vector scripts and the bridge are pinned to Cancun (g06-osaka-repin re-pins the scripts)
  - missing: no `EvmSpec` instance names a fork; G06's interface must fix Osaka
  - missing: reference-EVM versions unlocked (G00 disagreement 5)
  - missing: the code-size idealization (D09) means the reference EVM used for vectors must be configured or patched to skip EIP-170/EIP-3860, or such vectors kept below the limits
- **D04 Public theorem over solc's two pipelines: the legacy and via-IR `EvalOrder` settings (revised 2026-10-29: the other six flag combinations are dropped)**
  - lowering: `Solidity.EvalOrder` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:392`) — the three evaluation-order flags
  - lowering: `Solidity.EvalOrder.viaIR` (Solidity.Syntax.Raw, `Solidity/Syntax/Raw.lean:400`) — the via-IR combination
  - missing: the public theorem's settings type must range over exactly the two pipelines and map each to its `EvalOrder` (`{}` for legacy, `EvalOrder.viaIR`); admission must refuse the other six flag combinations (manual `evalOrder` overrides)
  - missing: no source semantics parameterized by the pipeline independently of the elaborator
  - missing: lowering (`hoist`/`captureExpr`, `wrapMods`) has regressions but no theorem for either order
  - missing: each pipeline fixes its ABI coder: legacy with the pragma's coder (v1 or v2), via-IR with v2; legacy ABI-v1 decoding is today an implementation diagnostic (`pragmaAbicoder`)
- **D05 Frozen profile solc 0.8.38; 0.8.34 fixtures only as SolKey compatibility checks**
  - missing: CI downloads only solc 0.8.34 (G00 pins); the frozen 0.8.38 pin must reach `Source.Provenance`
  - missing: the 0.8.34 fixture boundary is not recorded per fixture (G05)
- **D06 Artifact table: `creationCode`/`runtimeCode` read from G01's whole-input `Artifact` table, a source-semantics parameter**
  - theorem: `Solidity.Roadmap.Artifact` (Solidity.Roadmap.Contracts, `Solidity/Roadmap/Contracts.lean:373`) — whole-input table of code units
  - theorem: `Solidity.Roadmap.CodeUnit` (Solidity.Roadmap.Contracts, `Solidity/Roadmap/Contracts.lean:364`) — initcode, runtime and link sites
  - missing: `SourceSpec` does not yet take the `Artifact` table as a parameter (g01-contracts-rev)
  - missing: the G07 non-circularity whitelist must admit exactly this compiler-output parameter
  - missing: no compiled artifact exists for any contract: `type(C).creationCode` has no producer
- **D07 Full fixed-point types beyond pinned solc's acceptance boundary**
  - missing: the manifest scopes `fixedPoint` as `upstream` (g00-manifest-rev moves it into the profile)
  - missing: no reference semantics for fixed-point arithmetic/rounding/conversions beyond solc 0.8.38 (fixed-point-semantics)
  - missing: no lexer, type, lowering or compiler support at all
  - missing: the reference semantics must encode the second-round answers: exact product/quotient truncated toward zero, range-contained implicit conversions only, explicit out-of-range conversions wrap (constants are compile errors), `++`/`--` by 1, unary minus on `ufixed` panics `0x11` unless 0, integer/`bytesM` conversions by value/bit pattern
  - missing: shifts are rejected as solc's checker reaches an internal assertion: G15 must refuse them (narrows G00 Q6)
- **D08 Idealized source resources: unbounded fuel and recursion**
  - source: `Solidity.recDepth` (Solidity.Syntax.Scoped, `Solidity/Syntax/Scoped.lean:469`) — fixed 1024-frame unrolling to remove
  - source: `Solidity.Prog.runF_approx` (Solidity.Semantics.RunFuel, `Solidity/Semantics/RunFuel.lean:449`) — fuel approximation of the classical run
  - theorem: `Solidity.Roadmap.typedRunPrefixes` (Solidity.Roadmap.Contracts, `Solidity/Roadmap/Contracts.lean:455`) — intrinsic prefix family plug
  - missing: intrinsic recursion is unrolled to `recDepth = 1024` with an `exhausted` bottom (G04 R08)
  - missing: `SourceSpec.Idealized` has no instance; `Prefixes.Consistent` of `Prog.runF` is unproved
- **D09 Resource exhaustion as an allowed failure; code-size limits (EIP-170/3860) idealized**
  - theorem: `Solidity.Roadmap.EvmSpec` (Solidity.Roadmap.Contracts, `Solidity/Roadmap/Contracts.lean:382`) — pinned EVM language with resources
  - theorem: `Solidity.Roadmap.Prefixes.Consistent` (Solidity.Roadmap.Contracts, `Solidity/Roadmap/Contracts.lean:85`) — consistency of resourced prefix families
  - missing: `EvmSpec` resources still list code size (g01-contracts-rev drops it)
  - missing: `Lang.Res` ends a session at gas exhaustion; the decision requires the session to continue
  - missing: machine `.fault` conflates divergence with malformed code (G04 R38)
- **D10 Memory frames for recursion: internal calls keep their frames in memory, depth bounded by gas only**
  - backend: `Solidity.Evm.Memory.frameNeedProg` (Solidity.Evm.MemoryCompile, `Solidity/Evm/MemoryCompile.lean:51`) — peak frame need: a static frame, not a call stack
  - missing: internal calls are compiled inline (G04 R09); there is no runtime frame
  - missing: the 1024-slot EVM stack is not separated from call depth: frames must live in memory so that only gas bounds recursion
  - missing: no frame-allocation resource bound (`need`) for recursive calls
- **D11 Per-run hash premise and bound: the preimages hashed by an execution prefix do not collide, plus a random-oracle collision bound (about q²/2²⁵⁷)**
  - evm: `Solidity.Evm.External.no_injective_slot_encoding` (SolidityBridge.ExternalEvm.Obstructions, `Bridge/SolidityBridge/ExternalEvm/Obstructions.lean:15`) — symbolic slots admit no injective encoding
  - backend: `Solidity.Evm.Slot` (Solidity.Evm.Machine, `Solidity/Evm/Machine.lean:99`) — symbolic slot terms (to replace)
  - missing: storage slots are symbolic terms that never collide (`Slot`, G04 R34) — global injectivity in the type
  - missing: `PublicCorrectness` has no per-run premise yet (g01-contracts-rev); the bound lemma is new (hash-collision-bound)
  - missing: the premise must quantify over the prefix's actual preimages, including mapping keys and dynamic-array bases
  - missing: the core has no probability library: the bound must be stated combinatorially, as a count over oracle functions in the idealized random-oracle model the decision names, not about keccak itself
  - missing: the premise extends to hashed regions: no region of length at most L based at a hashed slot overlaps another or a root region (bound about q²·L/2²⁵⁶); the region predicate and its counting bound are new
- **D12 History-dependent callee strategies with unbounded reentrancy; address 0 has no code**
  - theorem: `Solidity.Bridge.Adversary.holdsC_iff_all_callees` (SolidityBridge.Adversary, `Bridge/SolidityBridge/Adversary.lean:250`) — callback modality over all callees at a payment boundary
  - source: `Solidity.TTx` (Solidity.Semantics.State, `Solidity/Semantics/State.lean:105`) — static response table to generalize
  - missing: `TTx.ext` is a static response table: identical calls read the same entry (G01 reuse map)
  - missing: the Bridge adversary covers a payment boundary only
  - missing: no transaction-level quantification over strategies in a contract
- **D13 Observation: the full `Event` list with exact ABI and revert bytes, `Panic` codes included**
  - theorem: `Solidity.Roadmap.Event` (Solidity.Roadmap.Contracts, `Solidity/Roadmap/Contracts.lean:258`) — shared observable events
  - theorem: `Solidity.Roadmap.Outcome` (Solidity.Roadmap.Contracts, `Solidity/Roadmap/Contracts.lean:245`) — outcomes with bytes
  - source: `Solidity.Prog.withPanics` (Solidity.Syntax.Checked, `Solidity/Syntax/Checked.lean:587`) — solc panic codes in callees
  - missing: revert data is erased in the compiler theorem (G04 R37); `THalt` loses panic codes
  - missing: the call, creation and callee-answer events of the `Event` list have no producer: typed calls and creation are not compiled (G42.02, G44.03)
  - missing: function results are not observed (G04 R41)
- **D14 `decode : EvmWorld → Option IntrinsicWorld` exported by the public theorem**
  - backend: `Solidity.Evm.Sim` (Solidity.Evm.Sim, `Solidity/Evm/Sim.lean:574`) — core state relation (not a decoder)
  - backend: `Solidity.Evm.compile_storage` (Solidity.Evm.Correct, `Solidity/Evm/Correct.lean:1197`) — live uint storage paths equal machine slots
  - missing: `PublicCorrectness` has no `decode` field (g01-contracts-rev)
  - missing: the core relation `Sim` is a relation, not a computable decoder; memory `StateRepr` likewise
  - missing: decoding symbolic slots back from numeric EVM storage needs the D11 hash premise
- **D15 Gas over-approximation: callee answers range over all outcomes regardless of forwarded gas**
  - missing: `CALL` takes only address and value in the machine; forwarded gas is absent (G04 R27)
- **D16 System boundary: the whole input, every contract and linked library, is compiled**
  - admission: `Solidity.Frontend.Source.validateSettings` (Solidity.Frontend.Source, `Solidity/Frontend/Source.lean:169`) — rejects `libraries` today
  - missing: `validateSettings` must admit exactly the empty link map; a pre-assigned map is refused and the session deploys and links every library itself (G05 Q1, resolving G00 disagreement 6)
  - missing: no link-settings provenance (G00 ownership gap 2; G05)
- **D17 Storage aliases after `pop`/`delete` in profile, with solc's logical slot behaviour**
  - backend: `Solidity.Evm.Examples.rejected` (Solidity.Evm.Examples, `Solidity/Evm/Examples.lean:354`) — kernel-checked rejection of a dangling alias
  - missing: fragile aliases are dropped at every shrink and later use is rejected (G04 R36)
  - missing: source semantics of a dangling alias (logical slot reuse, not packing) is not defined
- **D18 Payment acceptance: any outcome for untyped recipients, history-dependent; typed recipients run their own code**
  - missing: acceptance is the oracle `Machine.accepts` (G04 R33); recipient code is never run
  - missing: the payment disjunct (iii) of `compile_correct` is a stale weakening (G04 R32); G24.04 owns the interim restatement of T1/T12/T13/T15 without it (G04 §3.1), G43 the payment relation
- **D19 Frame failure semantics: any external call frame may fail with a revert its caller sees (1024 depth, forwarded-gas exhaustion in callbacks)**
  - source: `Solidity.ContractWorld.Step` (Solidity.Semantics.ContractWorld, `Solidity/Semantics/ContractWorld.lean:431`) — multi-instance world steps with rollback
  - missing: the source semantics lets typed calls fail only through the response table
  - missing: no theorem relates a callee-side out-of-gas or depth failure to the caller's observed revert
- **D20 Transaction failure semantics: any transaction may revert from gas exhaustion and the session continues**
  - source: `Solidity.Lifetime.System` (Solidity.Semantics.Lifetime, `Solidity/Semantics/Lifetime.lean:87`) — deploy-then-call sessions, no exhaustion transition
  - missing: `Lang.Res` ends a session at gas exhaustion (contract revision needed)
  - missing: `Lifetime.System` and `ContractWorld.Step` have no exhaustion transition
- **D21 Sender funds: `msg.value` bounded by the sender's ledger balance; unaffordable transactions never execute**
  - backend: `Solidity.Evm.Sim.init` (Solidity.Evm.Correct, `Solidity/Evm/Correct.lean:1181`) — fresh start state with zero caller/value
  - missing: the core start state fixes caller, value and timestamp to 0 (`compile_storage`, G04 T6)
  - missing: no transaction validity predicate on the sender's balance
- **D22 Precompile addresses behave as their Osaka definitions, never as environment code**
  - missing: `sha256`/`ripemd160`/`ecrecover` are source builtins computed in Lean, not calls to addresses 1–3
  - missing: typed calls to a precompile address are environment calls in `ContractWorld`
- **D23 Forced ether: the environment may credit the system's balance between transactions and during environment frames; the ledger records the credits**
  - backend: `Solidity.Evm.compile_net` (Solidity.Evm.Correct, `Solidity/Evm/Correct.lean:1157`) — machine success gives net payments; no external credit
  - missing: the core `Sim`/ledger relation fixes balances between steps; credits by beneficiary rewards, foreign `SELFDESTRUCT` or withdrawals have no source transition
  - missing: the own balance must be allowed to grow in the source (`address(this).balance` reads)
- **D24 Stipend payments to our own instances: a compiler-independent source cost rule decides which `receive`/fallback bodies fit 2300 gas; the compiler is proved to fit every admitted body**
  - missing: no source cost rule exists; it must assume cold (EIP-2929) access costs and be independent of the compiler
  - missing: the compiler must be proved to fit every admitted body within the stipend, and to fail the payment for every body the rule rejects
  - missing: carve-out from 'Follow-up — nested-frame failures' for these payments only; gas stays unobserved
- **D25 Shared compiler foundation: frozen slot, state and statement interfaces as children of G24 ahead of wave 3**
  - missing: the child rows are not yet in coverage-plan.md's manifest and VM table (integration step 1); the checker applies them from `PROPOSED_PACKAGES` until they land
  - missing: no frozen interface exists: `Slot`, `Sim`/`StateRepr` and `StmtOut` are concrete today

### Dependency ledger

Edges `package ← prerequisite`. `roadmap` edges transcribe coverage-plan.md; `g03` edges are new lemma-level dependencies found here; `deferred` edges are final checks after a later package (the G36.03 pattern), not scheduling prerequisites.

| package | prerequisites | kind | why |
|---|---|---|---|
| G03 | G00 G01 | roadmap | wave 0: G03 follows G00/G01 |
| G05 | G00 G01 | roadmap | wave 0: G05 follows G00/G01 |
| G06 | G00 G01 | roadmap | wave 0: G06 follows G00/G01 |
| G07 | G02 G03 G04 G05 G06 | roadmap | wave 0: G07 follows G02–G06 |
| G11 | G08 G09 G10 | roadmap | G11 follows G08–G10 |
| G13 | G12 | g03 | overload selection and constant typing need resolved declarations and signatures |
| G14 | G12 | g03 | inheritance/override/using-for resolution needs declaration identity across units |
| G15 | G11 G12 G13 G14 | roadmap | G15 follows G11–G14 |
| G17 | G16 | g03 | effectful expressions lower their scalar operands through G16's relation |
| G18.02 | G18.01 | roadmap | G-parent children in listed order |
| G18.03 | G18.02 | roadmap | G-parent children in listed order |
| G18.04 | G18.03 | roadmap | G-parent children in listed order |
| G18.05 | G18.04 | roadmap | G-parent children in listed order |
| G18.06 | G18.05 | roadmap | G-parent children in listed order |
| G19 | G16 G17 | g03 | loop conditions, returns and modifier arguments are expressions |
| G20 | G18.06 | g03 | getters and signatures of aggregate parameters lower through aggregate lowering |
| G21 | G18.04 | g03 | ABI/calldata lowering of nested values uses the calldata aggregate relation |
| G22.02 | G22.01 | roadmap | G-parent children in listed order |
| G22.03 | G22.02 | roadmap | G-parent children in listed order |
| G22.04 | G20 | g03 | linked libraries and function values reuse callable lowering |
| G22.04 | G22.03 | roadmap | G-parent children in listed order |
| G22.05 | G22.04 | roadmap | G-parent children in listed order |
| G23 | G16 G17 G18.06 G19 G20 G21 G22.05 | roadmap | G23's whole-source composition follows G16–G22 |
| G24.02 | G24.01 | roadmap | G-parent children in listed order (proposed G24 children) |
| G24.03 | G24.02 | roadmap | G-parent children in listed order (proposed G24 children) |
| G24.04 | G24.03 | roadmap | G-parent children in listed order (proposed G24 children) |
| G25 | G24.04 | roadmap | G25–G31 follow G24 |
| G26 | G25 | g03 | expression code composes primitive operator code |
| G26 | G24.04 | roadmap | G25–G31 follow G24 |
| G27.01 | G24.04 | roadmap | G25–G31 follow G24 |
| G27.02 | G27.01 | roadmap | G-parent children in listed order |
| G27.03 | G27.02 | roadmap | G-parent children in listed order |
| G27.04 | G27.03 | roadmap | G-parent children in listed order |
| G27.05 | G27.04 | roadmap | G-parent children in listed order |
| G28 | G27.05 | roadmap | G28 follows G27 |
| G29.01 | G28 | roadmap | G29/G30 follow G28 |
| G29.02 | G29.01 | roadmap | G-parent children in listed order |
| G29.03 | G29.02 | roadmap | G-parent children in listed order |
| G30 | G28 | roadmap | G29/G30 follow G28 |
| G31 | G27.05 | g03 | hash builtins share the per-run hash premise of the storage representation (D11) |
| G31 | G24.04 | roadmap | G25–G31 follow G24 |
| G33 | G32 | roadmap | G33/G34/G38/G39 follow G32 |
| G34 | G32 | roadmap | G33/G34/G38/G39 follow G32 |
| G35.01 | G33 G34 | roadmap | G35 follows G33/G34 |
| G35.02 | G35.01 | roadmap | G-parent children in listed order |
| G35.03 | G35.02 | roadmap | G-parent children in listed order |
| G35.04 | G35.03 | roadmap | G-parent children in listed order |
| G35.05 | G35.04 | roadmap | G-parent children in listed order |
| G35.06 | G35.05 | roadmap | G-parent children in listed order |
| G36.02 | G36.01 | roadmap | G-parent children in listed order |
| G36.03 | G43 | deferred | G36.03's final check follows G43 |
| G36.03 | G36.02 G37.03 | roadmap | G36's call cases follow G37 |
| G37.01 | G32 | g03 | runtime internal-call frames live in memory (decision G01 Q2, D10) |
| G37.02 | G37.01 | roadmap | G-parent children in listed order |
| G37.03 | G37.02 | roadmap | G-parent children in listed order |
| G38 | G37.01 | g03 | local unwind and rollback across internal runtime frames |
| G38 | G32 | roadmap | G33/G34/G38/G39 follow G32 |
| G39 | G42.01 G42.03 | deferred | transient sharing through self-calls and callbacks; final check after G42 |
| G39 | G32 | roadmap | G33/G34/G38/G39 follow G32 |
| G40 | G35.03 | g03 | ABI decoding validates into the compiler's calldata representation |
| G41 | G38 | g03 | catch dispatch decodes the exact failure classes and bytes |
| G42.01 | G40 G41 | roadmap | G42 follows G40/G41 |
| G42.02 | G42.01 | roadmap | G-parent children in listed order |
| G42.03 | G42.02 | roadmap | G-parent children in listed order |
| G42.04 | G42.03 | roadmap | G-parent children in listed order |
| G42.05 | G42.04 | roadmap | G-parent children in listed order |
| G42.06 | G42.05 | roadmap | G-parent children in listed order |
| G43 | G42.06 | roadmap | G43/G44 follow G42 |
| G44.01 | G42.06 | roadmap | G43/G44 follow G42 |
| G44.02 | G45.04 | g03 | initcode/runtime artifacts and link references are assembled by the assembler |
| G44.02 | G44.01 | roadmap | G-parent children in listed order |
| G44.03 | G43 | g03 | `new C{value: v}` and try-new move funds through the payment relation |
| G44.03 | G44.02 | roadmap | G-parent children in listed order |
| G45.02 | G45.01 | roadmap | G-parent children in listed order |
| G45.03 | G36.02 | g03 | LOOP/backedge realization of general loops |
| G45.03 | G45.02 | roadmap | G-parent children in listed order |
| G45.04 | G45.03 | roadmap | G-parent children in listed order |
| G45.05 | G45.04 | roadmap | G-parent children in listed order |
| G45.06 | G45.05 | roadmap | G-parent children in listed order |
| G46.02 | G46.01 | roadmap | G-parent children in listed order |
| G46.03 | G27.05 | g03 | EVM storage bridge discharges the symbolic paths with the D11 hash premise |
| G46.03 | G46.02 | roadmap | G-parent children in listed order |
| G46.04 | G46.03 | roadmap | G-parent children in listed order |
| G46.05 | G46.04 | roadmap | G-parent children in listed order |
| G46.06 | G46.05 | roadmap | G-parent children in listed order |
| G47 | G42.06 G43 G44.03 G45.06 G46.06 | roadmap | G47 follows G42–G46 |
| G48 | G15 G23 | g03 | frontend composition of admission and source-unit lowering |
| G49.01 | G48 | roadmap | G49 follows G48 |
| G49.02 | G49.01 | roadmap | G-parent children in listed order |
| G49.03 | G36.03 G37.02 | g03 | termination/divergence correspondence of loops and recursion |
| G49.03 | G49.02 | roadmap | G-parent children in listed order |
| G50.01 | G49.03 | roadmap | G50 follows G49 |
| G50.02 | G50.01 | roadmap | G-parent children in listed order |
| G51.01 | G50.02 | roadmap | G51 follows G50 |
| G51.02 | G51.01 | roadmap | G-parent children in listed order |
| G52 | G49.02 | g03 | whole-pipeline differential tests need the composed runtime pipeline |
| G54.01 | G48 G49.03 G50.02 G51.02 G52 G53 | roadmap | G54 follows G48–G53 |
| G54.02 | G54.01 | roadmap | G-parent children in listed order |
| G54.03 | G54.02 | roadmap | G-parent children in listed order |
| G55 | G54.03 | roadmap | G55 follows G54 |
| S01 | S00 | roadmap | S00 precedes S01 |
| S02 | S01 S04.01 S04.02 S04.03 | roadmap | S02 follows S01 and S04.01–S04.03 |
| S03.01 | S02 | roadmap | S03.01–S03.03 follow S02 |
| S03.02 | S02 | roadmap | S03.01–S03.03 follow S02 |
| S03.03 | S02 | roadmap | S03.01–S03.03 follow S02 |
| S03.04 | S03.01 S03.02 S03.03 | roadmap | S03.04 composes them |
| S04.01 | S00 | roadmap | S00 precedes the state/value definitions |
| S04.02 | S00 | roadmap | S00 precedes the state/value definitions |
| S04.03 | S00 | roadmap | S00 precedes the state/value definitions |
| S04.04 | S03.04 | roadmap | S04.04 composes transactions after S03.04 |
| S05 | S00 S01 S02 S03.04 S04.04 | roadmap | S05 follows all S-groups |

#### Findings

`schedule`: a dependency whose prerequisite is not scheduled first (wave, then VM order); `inversion`: a package edits a module importing one that a later package edits; `shared-write`: two unordered packages edit one module. Each needs a recorded resolution.

Schedule findings (each with its resolution):

| package | prerequisite | evidence | resolution |
|---|---|---|---|
| G19 | G16 | loop conditions, returns and modifier arguments are expressions | V11 (G19, G20) runs beside V09 (G16, G17): add V09 to V11's prerequisites, or let G19 prepare against the expression-lowering relation and pass its final check after V09 integrates |
| G19 | G17 | loop conditions, returns and modifier arguments are expressions | V11 runs beside V09: as G19 ← G16 |
| G20 | G18.06 | getters and signatures of aggregate parameters lower through aggregate lowering | V11 runs beside V10 (G18): add V10 to V11's prerequisites, or prepare against the G18.06 interface with the final check after V10 |
| G21 | G18.04 | ABI/calldata lowering of nested values uses the calldata aggregate relation | V12 runs beside V10: add V10 to V12's prerequisites, or prepare against the G18.04 relation with the final check after V10 |
| G31 | G27.05 | hash builtins share the per-run hash premise of the storage representation (D11) | V17 runs beside V15: add V15 to V17's prerequisites so the per-run hash premise (D11) is shared, not duplicated |
| G38 | G37.01 | local unwind and rollback across internal runtime frames | V21 runs beside V20: add V20 to V21's prerequisites, or prove unwind against the G37.01 frame interface with the final check after V20 |
| G44.02 | G45.04 | initcode/runtime artifacts and link references are assembled by the assembler | V25 runs beside V26: add V26 to V25's prerequisites, or split artifact layout (G44.02) from relocation (G45.04) with a deferred final check |
| G44.03 | G43 | `new C{value: v}` and try-new move funds through the payment relation | V25 runs beside V24: add V24 to V25's prerequisites; G43's payment relation must not wait on G44 |
| G52 | G49.02 | whole-pipeline differential tests need the composed runtime pipeline | V30 depends on V27 only: add V28 to V30's prerequisites for whole-pipeline differential tests |

Resolved by the foundation children (G03 Q1, answered): findings through a module whose interface a G24 child freezes, between packages scheduled after that child.

| child | modules | findings resolved | packages |
|---|---|---|---|
| G24.01 | `Solidity.Evm.Machine` | 26 | G24.01 G24.02 G24.03 G24.04 G25 G26 G27.01 G27.02 G27.05 |
| G24.02 | `Solidity.Evm.Sim`, `Solidity.Evm.SimLemmas`, `Solidity.Evm.Repr`, `Solidity.Evm.StorageLemmas`, `Solidity.Evm.MemorySource`, `Solidity.Evm.MemoryHeap`, `Solidity.Evm.MemoryAlloc`, `Solidity.Evm.MemoryGrowResult` | 122 | G24.02 G24.03 G24.04 G26 G27.01 G27.02 G27.03 G28 G30 G31 G32 G33 G34 G35.01 G36.01 G36.02 G38 G43 |
| G24.03 | `Solidity.Evm.Stmt`, `Solidity.Evm.Compile`, `Solidity.Evm.Correct`, `Solidity.Evm.Expr`, `Solidity.Evm.Layout`, `Solidity.Evm.Exp`, `Solidity.Evm.Signed`, `Solidity.Evm.MemoryCompile`, `Solidity.Evm.MemoryPaths`, `Solidity.Evm.MemoryRefWrite`, `Solidity.Evm.MemoryStructCopy` | 153 | G24.02 G24.03 G24.04 G25 G26 G28 G29.01 G30 G32 G33 G34 G35.01 G36.01 G36.02 G37.01 G38 G43 |

Module hot spots: the remaining inversions, parallel imports and shared writes, grouped by the module through which they arise, each with one resolution.

| module | findings | packages | resolution |
|---|---|---|---|
| `Solidity.Evm.Compile` | 3 inversion | G06 G24.03 G29.01 G37.01 | after the G24 foundation freeze (G03 Q1) only the earlier wave-0 interfaces sit below these edits: G06's Bridge seed (and, for `Machine`, G01's contracts) imports the module, so `check-bridge.sh` and the default build recheck them after each freeze child and each later extension; the extensions may not change the frozen signatures |
| `Solidity.Evm.Correct` | 2 inversion | G06 G24.03 G36.01 | after the G24 foundation freeze (G03 Q1) only the earlier wave-0 interfaces sit below these edits: G06's Bridge seed (and, for `Machine`, G01's contracts) imports the module, so `check-bridge.sh` and the default build recheck them after each freeze child and each later extension; the extensions may not change the frozen signatures |
| `Solidity.Evm.Exp` | 2 inversion | G06 G24.03 G25 | after the G24 foundation freeze (G03 Q1) only the earlier wave-0 interfaces sit below these edits: G06's Bridge seed (and, for `Machine`, G01's contracts) imports the module, so `check-bridge.sh` and the default build recheck them after each freeze child and each later extension; the extensions may not change the frozen signatures |
| `Solidity.Evm.Expr` | 2 inversion | G06 G24.03 G26 | after the G24 foundation freeze (G03 Q1) only the earlier wave-0 interfaces sit below these edits: G06's Bridge seed (and, for `Machine`, G01's contracts) imports the module, so `check-bridge.sh` and the default build recheck them after each freeze child and each later extension; the extensions may not change the frozen signatures |
| `Solidity.Evm.Layout` | 2 inversion | G06 G24.03 G25 | after the G24 foundation freeze (G03 Q1) only the earlier wave-0 interfaces sit below these edits: G06's Bridge seed (and, for `Machine`, G01's contracts) imports the module, so `check-bridge.sh` and the default build recheck them after each freeze child and each later extension; the extensions may not change the frozen signatures |
| `Solidity.Evm.Machine` | 4 inversion | G01 G06 G24.01 G27.05 | after the G24 foundation freeze (G03 Q1) only the earlier wave-0 interfaces sit below these edits: G06's Bridge seed (and, for `Machine`, G01's contracts) imports the module, so `check-bridge.sh` and the default build recheck them after each freeze child and each later extension; the extensions may not change the frozen signatures |
| `Solidity.Evm.Repr` | 3 inversion | G06 G24.02 G27.01 G27.02 | after the G24 foundation freeze (G03 Q1) only the earlier wave-0 interfaces sit below these edits: G06's Bridge seed (and, for `Machine`, G01's contracts) imports the module, so `check-bridge.sh` and the default build recheck them after each freeze child and each later extension; the extensions may not change the frozen signatures |
| `Solidity.Evm.Signed` | 2 inversion | G06 G24.03 G25 | after the G24 foundation freeze (G03 Q1) only the earlier wave-0 interfaces sit below these edits: G06's Bridge seed (and, for `Machine`, G01's contracts) imports the module, so `check-bridge.sh` and the default build recheck them after each freeze child and each later extension; the extensions may not change the frozen signatures |
| `Solidity.Evm.Sim` | 2 inversion | G06 G24.02 G43 | after the G24 foundation freeze (G03 Q1) only the earlier wave-0 interfaces sit below these edits: G06's Bridge seed (and, for `Machine`, G01's contracts) imports the module, so `check-bridge.sh` and the default build recheck them after each freeze child and each later extension; the extensions may not change the frozen signatures |
| `Solidity.Evm.SimLemmas` | 2 inversion | G06 G24.02 G31 | after the G24 foundation freeze (G03 Q1) only the earlier wave-0 interfaces sit below these edits: G06's Bridge seed (and, for `Machine`, G01's contracts) imports the module, so `check-bridge.sh` and the default build recheck them after each freeze child and each later extension; the extensions may not change the frozen signatures |
| `Solidity.Evm.Stmt` | 5 inversion | G06 G24.03 G28 G30 G38 G43 | after the G24 foundation freeze (G03 Q1) only the earlier wave-0 interfaces sit below these edits: G06's Bridge seed (and, for `Machine`, G01's contracts) imports the module, so `check-bridge.sh` and the default build recheck them after each freeze child and each later extension; the extensions may not change the frozen signatures |
| `Solidity.Evm.StorageLemmas` | 2 inversion | G06 G24.02 G27.03 | after the G24 foundation freeze (G03 Q1) only the earlier wave-0 interfaces sit below these edits: G06's Bridge seed (and, for `Machine`, G01's contracts) imports the module, so `check-bridge.sh` and the default build recheck them after each freeze child and each later extension; the extensions may not change the frozen signatures |
| `Solidity.Frontend.Source` | 3 inversion | G05 G12 G15 | provenance and pins: G05 fixes the certificate interface first; G12/G15 extend it; untrusted solc adapter (G01 frontend boundary): the checked frontend of G08–G15 lives in new modules, so edits here only re-run the adapter's regressions; wave-1 packages may not depend on adapter internals for their certificates |
| `Solidity.Frontend.SourceUnits` | 1 inversion | G05 G12 | untrusted solc adapter (G01 frontend boundary): the checked frontend of G08–G15 lives in new modules, so edits here only re-run the adapter's regressions; wave-1 packages may not depend on adapter internals for their certificates |
| `Solidity.RevertBytes` | 2 inversion, 13 parallel-import | G01 G06 G16 G17 G18.01 G18.02 G18.03 G18.04 G18.05 G19 G21 | intrinsic semantics: later edits are conservative extensions (new constructors or lemmas); each edit re-runs the dependent lowering proofs and the Bridge in the integrated build |
| `Solidity.Semantics.ContractWorldCertificates` | 1 inversion | G22.03 G22.04 | G22 children in listed order within V13; intrinsic semantics: later edits are conservative extensions (new constructors or lemmas); each edit re-runs the dependent lowering proofs and the Bridge in the integrated build |
| `Solidity.Semantics.Deploy` | 2 inversion | G01 G22.01 G22.03 | G22 children in listed order within V13; intrinsic semantics: later edits are conservative extensions (new constructors or lemmas); each edit re-runs the dependent lowering proofs and the Bridge in the integrated build |
| `Solidity.Semantics.Heap` | 2 inversion, 1 parallel-import | G01 G06 G16 G18.03 | intrinsic semantics: later edits are conservative extensions (new constructors or lemmas); each edit re-runs the dependent lowering proofs and the Bridge in the integrated build |
| `Solidity.Semantics.RecursiveStorage.Copy` | 1 inversion | G18.01 G18.05 | G18 children in listed order within V10; G18.01's admission is rechecked after G18.02/G18.05 |
| `Solidity.Semantics.RecursiveStorage.Paths` | 1 inversion | G18.01 G18.02 | G18 children in listed order within V10; G18.01's admission is rechecked after G18.02/G18.05 |
| `Solidity.Semantics.RevertData` | 2 inversion, 1 parallel-import | G01 G06 G16 G21 | intrinsic semantics: later edits are conservative extensions; each edit re-runs the dependent lowering proofs and the Bridge in the integrated build |
| `Solidity.Semantics.RunFuel` | 1 inversion | G01 G24.04 | None |
| `Solidity.Semantics.Storage` | 2 inversion, 1 parallel-import | G01 G06 G16 G18.02 | intrinsic semantics: later edits are conservative extensions (new constructors or lemmas); each edit re-runs the dependent lowering proofs and the Bridge in the integrated build |
| `Solidity.Syntax.Checked` | 2 inversion, 2 parallel-import | G01 G06 G16 G18.01 G18.05 | elaborator (layer L5 producer): wave-1 static checking must not reach it (G01: L0→L2 does not use L5); wave-2 lowering packages own the edits, serialized in VM order (V09 before V11) |
| `Solidity.Syntax.Elab.Context` | 4 parallel-import | G16 G17 G18.04 G19 | elaborator (layer L5 producer): wave-1 static checking must not reach it (G01: L0→L2 does not use L5); wave-2 lowering packages own the edits, serialized in VM order (V09 before V11) |
| `Solidity.Syntax.Elab.Lower` | 1 parallel-import, 1 shared-write | G17 G19 | elaborator (layer L5 producer): wave-1 static checking must not reach it (G01: L0→L2 does not use L5); wave-2 lowering packages own the edits, serialized in VM order (V09 before V11) |
| `Solidity.Syntax.Elab.SliceCopy` | 1 parallel-import | G17 G18.04 | elaborator (layer L5 producer): wave-1 static checking must not reach it (G01: L0→L2 does not use L5); wave-2 lowering packages own the edits, serialized in VM order (V09 before V11) |
| `SolidityBridge.ExternalEvm` | 1 inversion | G06 G46.01 | G06 fixes the EVM interface; G46.01 extends it and re-runs G06's checks |

No cycle over the declared (roadmap and G03, non-deferred) edges and the wave order; module-induced edges are the inversions above, not cycle edges.

#### Module ledger and checkpoint sizes

Planned edits of existing modules per package (`new` = new modules only). Flags: more than 60 owned ledger cells, more than 12000 edited lines, or an edited module over 2500 lines. Static proxies for G02's measurements, not timings.

| package | VM | cells | edited modules | lines | flag | lemma split |
|---|---|---|---|---|---|---|
| G00 | V00 | 0 | new | 0 | — | — |
| G01 | V00 | 9 | `Solidity.Roadmap.Contracts` | 467 | — | — |
| G02 | V01 | 0 | new | 0 | — | — |
| G03 | V02 | 0 | new | 0 | — | — |
| G04 | V01 | 0 | new | 0 | — | — |
| G05 | V02 | 3 | `Solidity.Frontend.Source`, `Solidity.Frontend.SourceUnits` | 557 | — | — |
| G06 | V02 | 4 | `SolidityBridge.ExternalEvm` | 255 | — | — |
| G07 | V03 | 2 | new | 0 | — | — |
| S00 | V03 | 51 | new | 0 | — | — |
| S01 | V03 | 53 | new | 0 | — | — |
| S02 | V04 | 46 | new | 0 | — | — |
| S05 | V04 | 1 | new | 0 | — | — |
| G08 | V05 | 16 | new | 0 | — | — |
| G09 | V05 | 32 | new | 0 | — | — |
| G10 | V06 | 70 | new | 0 | 70 owned cells > 60 | (a) primary and postfix forms: names, member/index/range access, calls, named arguments and call options; (b) operator precedence and associativity, one lemma per binding level; (c) tuples, inline arrays, conditional and `new`; compose into whole-expression parse correspondence |
| G11 | V06 | 44 | new | 0 | — | — |
| G12 | V07 | 6 | `Solidity.Frontend.SourceUnits` | 143 | — | — |
| G13 | V07 | 116 | new | 0 | 116 owned cells > 60 | (a) elementary types, literals, units and exact constants; (b) conversions and implicit widening; (c) aggregate and data-location typing; (d) overload selection and UDVT operators; (e) function/ABI metadata typing; then the static-semantics certificate |
| G14 | V08 | 20 | new | 0 | — | — |
| G15 | V08 | 221 | `Solidity.Frontend.SolcJson.Admission`, `Solidity.Frontend.Source`, `Solidity.Frontend.SolcJson.Body` | 3449 | 221 owned cells > 60; modules over 2500 lines: Solidity.Frontend.SolcJson.Body | one admission lemma per manifest category (12), each proving exact classification of its rows; a combination lemma for the named and ledger-symbol combinations; an exclusion lemma refusing the 30 excluded IDs (D01); then extraction coverage over all execution roots; the `SolcJson.Body` adapter edit (2,586 lines) is split by AST node class (declarations, expressions, statements) before it starts |
| G16 | V09 | 39 | `Solidity.Syntax.Elab.Values`, `Solidity.Syntax.Checked`, `Solidity.Semantics.NumericLowering` | 2950 | — | — |
| G17 | V09 | 16 | `Solidity.Syntax.Elab.Stmt`, `Solidity.Syntax.Elab.Lower` | 2525 | — | — |
| G19 | V11 | 18 | `Solidity.Syntax.Elab.Lower` | 1698 | — | — |
| G20 | V11 | 25 | `Solidity.Frontend.SolcJson.Getters`, `Solidity.Frontend.SolcJson.Contract` | 2268 | — | — |
| G21 | V12 | 28 | `Solidity.Semantics.RevertData`, `Solidity.RevertBytes` | 99 | — | — |
| G23 | V13 | 30 | `Solidity.Semantics.Transient`, `Solidity.Semantics.TransientWorld` | 485 | — | — |
| G25 | V14 | 35 | `Solidity.Evm.Layout`, `Solidity.Evm.Signed`, `Solidity.Evm.Exp` | 1163 | — | — |
| G26 | V14 | 16 | `Solidity.Evm.Expr` | 452 | — | — |
| G28 | V15 | 12 | `Solidity.Evm.Stmt` | 980 | — | — |
| G30 | V16 | 10 | `Solidity.Evm.Stmt` | 980 | — | — |
| G31 | V17 | 23 | `Solidity.Evm.SimLemmas` | 874 | — | — |
| G32 | V18 | 9 | `Solidity.Evm.MemoryHeap`, `Solidity.Evm.MemorySource` | 359 | — | — |
| G33 | V18 | 10 | `Solidity.Evm.MemoryAlloc`, `Solidity.Evm.MemoryGrowResult` | 405 | — | — |
| G34 | V18 | 7 | `Solidity.Evm.MemoryPaths`, `Solidity.Evm.MemoryRefWrite` | 438 | — | — |
| G38 | V21 | 17 | `Solidity.Evm.Stmt` | 980 | — | — |
| G39 | V21 | 4 | new | 0 | — | — |
| G40 | V22 | 23 | new | 0 | — | — |
| G41 | V22 | 18 | new | 0 | — | — |
| G43 | V24 | 20 | `Solidity.Evm.Sim`, `Solidity.Evm.Stmt` | 2137 | — | — |
| G47 | V27 | 81 | new | 0 | 81 owned cells > 60 | (a) CALL/STATICCALL frames, returndata and the frame-failure rule (D19); (b) CREATE and initcode installation; (c) REVERT and persistent/transient/balance rollback; (d) transactions, sender funds (D21) and gas-exhaustion failures (D20); (e) precompiles (D22); compose under the resource abstraction |
| G48 | V28 | 176 | new | 0 | 176 owned cells > 60 | (a) admission → resolved graph; (b) resolved → intrinsic per area: declarations, expressions/statements, aggregates, world/calls; (c) whole-unit coverage over compilation units; each a `Cert` composed by `Cert.comp` |
| G52 | V30 | 0 | `Solidity.Tools.DiffTest` | 358 | — | — |
| G53 | V30 | 1 | new | 0 | — | — |
| G55 | V31 | 0 | new | 0 | — | — |
| S03.01 | V04 | 17 | new | 0 | — | — |
| S03.02 | V04 | 6 | new | 0 | — | — |
| S03.03 | V04 | 32 | new | 0 | — | — |
| S03.04 | V04 | 7 | new | 0 | — | — |
| S04.01 | V03 | 32 | new | 0 | — | — |
| S04.02 | V03 | 44 | new | 0 | — | — |
| S04.03 | V03 | 28 | new | 0 | — | — |
| S04.04 | V04 | 13 | new | 0 | — | — |
| G18.01 | V10 | 5 | `Solidity.TypeGraph`, `Solidity.Semantics.RecursiveStorage.Admission` | 234 | — | — |
| G18.02 | V10 | 19 | `Solidity.Semantics.Storage`, `Solidity.Semantics.RecursiveStorage.Paths` | 184 | — | — |
| G18.03 | V10 | 20 | `Solidity.Semantics.Heap` | 537 | — | — |
| G18.04 | V10 | 11 | `Solidity.Syntax.Elab.Context`, `Solidity.Syntax.Elab.SliceCopy` | 1552 | — | — |
| G18.05 | V10 | 17 | `Solidity.Semantics.RecursiveStorage.Copy` | 187 | — | — |
| G18.06 | V10 | 3 | new | 0 | — | — |
| G22.01 | V13 | 12 | `Solidity.Semantics.ContractWorld` | 461 | — | — |
| G22.02 | V13 | 9 | `Solidity.Semantics.Callback` | 1611 | — | — |
| G22.03 | V13 | 10 | `Solidity.Semantics.Deploy`, `Solidity.Frontend.WorldImport` | 476 | — | — |
| G22.04 | V13 | 7 | `Solidity.Semantics.ContractWorldCertificates` | 174 | — | — |
| G22.05 | V13 | 14 | new | 0 | — | — |
| G27.01 | V15 | 7 | `Solidity.Evm.Repr` | 1023 | — | — |
| G27.02 | V15 | 4 | `Solidity.Evm.Repr` | 1023 | — | — |
| G27.03 | V15 | 7 | `Solidity.Evm.StorageLemmas` | 214 | — | — |
| G27.04 | V15 | 3 | new | 0 | — | — |
| G27.05 | V15 | 7 | `Solidity.Evm.Machine` | 685 | — | — |
| G29.01 | V16 | 3 | `Solidity.Evm.Compile` | 487 | — | — |
| G29.02 | V16 | 4 | new | 0 | — | — |
| G29.03 | V16 | 3 | new | 0 | — | — |
| G35.01 | V19 | 4 | `Solidity.Evm.MemoryStructCopy` | 128 | — | — |
| G35.02 | V19 | 5 | new | 0 | — | — |
| G35.03 | V19 | 9 | new | 0 | — | — |
| G35.04 | V19 | 6 | new | 0 | — | — |
| G35.05 | V19 | 4 | new | 0 | — | — |
| G35.06 | V19 | 2 | new | 0 | — | — |
| G36.01 | V20 | 11 | `Solidity.Evm.Correct` | 1232 | — | — |
| G36.02 | V20 | 5 | `Solidity.Evm.MemoryCompile` | 1254 | — | — |
| G36.03 | V24 | 8 | new | 0 | — | — |
| G37.01 | V20 | 14 | `Solidity.Evm.Compile` | 487 | — | — |
| G37.02 | V20 | 8 | new | 0 | — | — |
| G37.03 | V20 | 9 | new | 0 | — | — |
| G42.01 | V23 | 3 | new | 0 | — | — |
| G42.02 | V23 | 15 | new | 0 | — | — |
| G42.03 | V23 | 6 | new | 0 | — | — |
| G42.04 | V23 | 5 | new | 0 | — | — |
| G42.05 | V23 | 8 | new | 0 | — | — |
| G42.06 | V23 | 3 | new | 0 | — | — |
| G44.01 | V25 | 8 | new | 0 | — | — |
| G44.02 | V25 | 10 | new | 0 | — | — |
| G44.03 | V25 | 7 | new | 0 | — | — |
| G45.01 | V26 | 1 | new | 0 | — | — |
| G45.02 | V26 | 3 | new | 0 | — | — |
| G45.03 | V26 | 2 | new | 0 | — | — |
| G45.04 | V26 | 1 | new | 0 | — | — |
| G45.05 | V26 | 1 | new | 0 | — | — |
| G45.06 | V26 | 2 | new | 0 | — | — |
| G46.01 | V27 | 80 | `SolidityBridge.ExternalEvm`, `SolidityBridge.ExternalEvm.WordOps` | 354 | 80 owned cells > 60 | (a) arithmetic, comparison and bitwise opcodes (seed: `ExternalEvm.simulation`); (b) signedness, narrow truncation and casts; (c) PUSH constants and control primitives JUMP/JUMPI/JUMPDEST |
| G46.02 | V27 | 71 | new | 0 | 71 owned cells > 60 | (a) MLOAD/MSTORE/MSTORE8 against the byte-addressed representation; (b) CALLDATALOAD/CALLDATACOPY against the calldata representation; (c) memory expansion and its resource bound; (d) RETURN/REVERT byte ranges |
| G46.03 | V27 | 38 | new | 0 | — | — |
| G46.04 | V27 | 15 | `SolidityBridge.ExternalEvm.Environment` | 128 | — | — |
| G46.05 | V27 | 15 | `SolidityBridge.ExternalEvm.Obstructions` | 82 | — | — |
| G46.06 | V27 | 14 | `SolidityBridge.ExternalEvm.Dispatch` | 258 | — | — |
| G49.01 | V28 | 66 | new | 0 | 66 owned cells > 60 | one composition lemma per pass family: expressions, statements/control, calls and frames, aggregates and copies, world and ABI; then their `Cert.comp` with the closure hypotheses |
| G49.02 | V28 | 170 | new | 0 | 170 owned cells > 60 | (a) runtime refinement per deployed contract; (b) observation mapping incl. return/revert bytes and panics (D13); (c) the `decode` export (D14); (d) threading the per-run hash premise (D11); (e) the quantifier over the two pipelines (D04) |
| G49.03 | V28 | 116 | `SolidityBridge.CompilerSimulation` | 77 | 116 owned cells > 60 | (a) compiler totality on admitted input; (b) non-vacuity controls (success with data, revert, divergence); (c) failure preservation (no always-revert); (d) resource-indexed progress and finite-prefix families |
| G50.01 | V29 | 33 | new | 0 | — | — |
| G50.02 | V29 | 42 | new | 0 | — | — |
| G51.01 | V29 | 85 | `Solidity.Calculus.Sound` | 45 | 85 owned cells > 60 | one soundness bridge per rule family: storage, memory, control/loops, internal calls, external calls/callbacks, arithmetic/checked guards; each against the composed runtime theorem |
| G51.02 | V29 | 18 | `Solidity.Calculus.CorrectCallback` | 104 | — | — |
| G54.01 | V31 | 1 | new | 0 | — | — |
| G54.02 | V31 | 1 | new | 0 | — | — |
| G54.03 | V31 | 0 | new | 0 | — | — |
| G24.01 | V14 | 3 | `Solidity.Evm.Machine` | 685 | — | — |
| G24.02 | V14 | 4 | `Solidity.Evm.Sim`, `Solidity.Evm.SimLemmas`, `Solidity.Evm.Repr`, `Solidity.Evm.StorageLemmas`, `Solidity.Evm.MemorySource`, `Solidity.Evm.MemoryHeap`, `Solidity.Evm.MemoryAlloc`, `Solidity.Evm.MemoryGrowResult` | 4032 | — | — |
| G24.03 | V14 | 3 | `Solidity.Evm.Stmt`, `Solidity.Evm.Compile`, `Solidity.Evm.Correct`, `Solidity.Evm.Expr`, `Solidity.Evm.Layout`, `Solidity.Evm.Exp`, `Solidity.Evm.Signed`, `Solidity.Evm.MemoryCompile`, `Solidity.Evm.MemoryPaths`, `Solidity.Evm.MemoryRefWrite`, `Solidity.Evm.MemoryStructCopy` | 6134 | — | — |
| G24.04 | V14 | 5 | `Solidity.Evm.Compiler`, `Solidity.Semantics.RunFuel` | 571 | — | — |

No feature cell, by reason: G00: scope freeze (integrated, wave 0); G02: build measurement, no feature obligation; G03: this ledger; G04: restriction audit (integrated, wave 0); G52: differential tests supplement every row; they discharge no stage; G54.03: trust/axiom audit of the composed theorems, not of a row; G55: final audit of the whole ledger.
<!-- END generated by scripts/roadmap-g03-ledger.py -->

## Integration steps (for the coordinator)

These change shared lines this group may not rewrite; the checker applies
them from its own data until they land.

1. **Manifest (`coverage-plan.md`, "Proof work-package manifest").** Insert
   these rows before `G27.01`, and change "There are **115 proof work
   packages**" to 118 and "The rows cover all 115 work packages" to 118:

   ```
   | G24.01 — Slot interface | Freeze an abstract storage-slot interface (root, mapping-key and array-element images, offsets) under every compiler proof, so G27.05 replaces the symbolic `Slot` behind it without changing its signatures. |
   | G24.02 — State interface | Freeze the typed core/memory state relations (`Sim`, `StateRepr`, the allocator input) as one relation interface that every backend pass and the `decode` export use. |
   | G24.03 — Statement interface | Freeze the statement-leaf outcome and pass-certificate signatures (`StmtOut`, the per-statement compile entry, `Cert` instances) that G25–G44 extend by new cases only. |
   | G24.04 — Unified entry | Unify the core/memory compiler entry on the frozen interfaces so mixed programs compose; restate T1/T12/T13/T15 without the unreachable payment disjunct. |
   ```

   When they land, delete `PROPOSED_PACKAGES` from the script: `--check` asks
   for that.
2. **VM table.** V14 keeps "G24, G25, G26". G24 now names its four children,
   which run first in listed order. The nine schedule conflicts above propose
   added VM prerequisites (V09 → V11, V10 → V11 and V12, V15 → V17, V20 → V21,
   V24 and V26 → V25, V28 → V30), and V23 gains G39's deferred final check.
3. **Deferred checks.** The "Groups and dependencies" preamble and the
   paragraph after the manifest name G36.03 as the only deferred check. Add
   G39 ← G42.01/G42.03, with its final check in V23.
4. **Wave 3 prerequisite row.** "G25–G31 follow G24" stays: it now means
   G24.04.

## Remaining child obligations

Every row stays open; the ledger assigns, it does not discharge. Handed on:

- **Each owner package:** the cells of its rows, combinations and decision
  rows, against the `missing` lists; packages flagged oversized follow their
  lemma split.
- **G02:** decide the nine VM-schedule conflicts (add the proposed VM
  prerequisites, or keep the interface-then-final-check alternative) and
  replace the static size proxies by measurements.
- **G24.01–G24.04:** freeze the slot, state and statement interfaces of
  the modules in `FROZEN` and rebuild the unified entry on them; after
  that, later packages may only extend those modules.
- **G39, G42:** the new deferred check of transient sharing through
  self-calls and callbacks.
- **G01 revision (g01-contracts-rev):** the contract changes D06, D09, D11,
  D14 and D20 require; this ledger cites the base declarations and must be
  regenerated (`--write`) after that lane merges, since line numbers move.
- **g00-manifest-rev:** when `fixedPoint` enters the profile, the G00 owner
  table supplies its four columns and the `FEATURE_EXTRA` substitute here
  becomes redundant (the checker keeps the row either way).
- **G48:** close the in-profile combinations listed here and any combination
  found later; add each to `COMBINATIONS` before scheduling.

## Limitations

- The module ledger is a planning estimate: which existing module a future
  package edits is a design choice, and the inversions, parallel imports,
  shared writes and sizes are as good as that estimate. A changed estimate
  that brings a new package through an acknowledged module fails `--check`;
  one that moves edits into unlisted modules is caught only if those modules
  import or are imported by other packages' modules.
- Several ownership checks are structural: the `evm` and `theorem` columns
  and G15's admission cell come from category defaults, the ledger-symbol
  ownership is derived, and a `missing` list or a REFINE choice is checked
  for presence and shape, not for content. The refinements are printed
  for review.
- Existing-coverage anchors come from read-only research passes. The checker
  proves each declaration exists where cited, not that it is the strongest
  or only relevant one; the `missing` text summarizes the feature documents
  and G04 rather than re-auditing every theorem.
- Owners of the `evm` and `theorem` columns are assigned by category with
  overrides; they are obligations to discharge, not evidence.
- No Lean file was added, so no new theorem exists; the Lean gates were run
  on the unchanged tree.
- The lane names in the decision table are this batch's sibling sessions and
  the Codex lanes, as given in the assignment; the checker does not validate
  them.

## Scope questions

### Q1. Shared compiler foundation (answered)

The existing compiler modules are imported by every backend proof and edited
by packages in waves 3–5. In the first draft this gave 106 inversions; the
roadmap's rule is to split cyclic interfaces into shared-foundation
children. The question offered three options: foundation children of G24,
freezing within G24 with rebase obligations, or new modules only. **The user
chose foundation children** (relayed by the coordinator, 2026-10-29). They
are applied as `PROPOSED_PACKAGES` and `FROZEN`. Integration step 1 below
lists the exact rows coverage-plan.md needs, since this group may not
rewrite those lines.

## Review

A read-only finder and a separate skeptic review ran after the first draft
(`54217502`). Both used git, grep and Python only, without the Lean server.
The skeptic tested the checker by mutating its data in a copy. Confirmed
findings and their fixes:

1. **Mis-staged anchors.** 10 `evm` anchors were not EVM bridges (the
   `Bridge.Arith` lemmas, `observe_encode`, `compile_terminates_iff`, the
   Adversary LTS). 25 `theorem` anchors were compiler or semantics lemmas,
   and 75 were fixed-program regressions counted as theorem coverage.
   *Fix:* 116 anchors were restaged. `--check` now enforces where each
   stage's anchors may live, and adds the `regression` stage, which counts
   for no stage. The summary counts were corrected.
2. **Unordered import pairs were ignored.** *Fix:* a new `parallel-import`
   kind (32 findings), each acknowledged.
3. **G01 was treated as integrated** although its contracts are not frozen.
   *Fix:* G01 was removed from `INTEGRATED`. Its RunFuel/Machine dependency
   is acknowledged with the revision obligation.
4. **Deferred edges bypassed every check.** Any later-wave edge could be
   declared `deferred`, and G39's check had no VM. *Fix:* every deferred edge
   must name a final-check VM after its prerequisite (`DEFERRED_CHECKS`). The
   G39 exception and the coverage-plan wording were handed to G02.
5. **The cycle sentence was false or tautological.** *Fix:* it now says what
   the graph contains. The prose states that inversions are module-level
   cycles. Q1 records the roadmap rule that applies.
6. **Blanket acknowledgements.** Module acknowledgements matched on the
   module only, and pair acknowledgements were symmetric and ignored the
   finding kind. *Fix:* pair acknowledgements are now keyed by kind and pair.
   A module acknowledgement must name exactly the packages its findings
   involve, so a new package appearing through it fails `--check`.
7. **The module ledger contradicted its resolutions.** G13 and G14 edited
   elaborator and adapter modules, S05 edited the generated catalog, and
   `SolcJson.Body` was unassigned. *Fix:* G13, G14 and S05 are `new`, and
   G15 owns `Body`, which is now flagged over 2,500 lines and covered by
   G15's split.
8. **Combinations had no per-stage ownership, and G00's combination owners
   were never compared** (G01 was dropped from loops/recursion). *Fix:* G15
   is always added. Unnamed stages are owned through the combination's rows
   and must be non-empty. G00 owners must survive refinement. G01 was
   restored.
9. **G04 restrictions accepted any one discharging package, and en-dash
   ranges were not expanded.** *Fix:* every discharging package must be an
   owner of a row citing the restriction (owners were added to 11
   combinations), or carry a recorded waiver. Ranges are now expanded.
10. **The "G00 owner dropped" check compared the refinement with itself.**
    *Fix:* it now checks against G00's raw tokens (a parent is satisfied by
    any of its children), and the refinement table is printed for review.
    The `R` columns are now derived from the missing cases.
11. **Decision rows** (D04 was later revised by the user's second-round answer). Several owners were missing: S03.02 for D04, G42.03
    for D19, G44.02 for D09, G42.02/G44.03 for D13 (call and creation
    events) and G27.05 for D14. Decision theorem columns named G01, G07, G53
    and G54. *Fix:* the owners were added. Stage-token checks now apply to
    feature, combination and decision rows, with the separate `interface`
    (G01, G05–G07) and `validation` (G52–G55) stages. D03, D04 and D11
    record the reference-EVM configuration, the six combinations solc cannot
    produce, and the combinatorial form the random-oracle bound needs
    without a probability library.
12. **Ownership-gap claim.** G04 §3.1's interim restatement was said to be
    "closed" while it was unowned. *Fix:* G24 owns it (D18, payments
    combination).
13. **Under-owned or contradicting rows.** *Fix:* `fixedPoint` gained
    storage, ABI and conversion owners, a combination row, and the interim
    refusal note. The precompile builtins gained G47 (D22). A
    recursive-type combination was added (G18.06 asks for it).
    `worldAssumptions` now states that its premise is not approved.
    `cleanTail_holds` was removed from `deleteMappingTails`. G49.03 moved
    from `termination`'s backend to its theorem column.
14. **Minor.** Markdown link brackets in generated notes are now escaped,
    vendored Bridge modules are excluded from the import graph, the anchor
    count includes combination and decision anchors, and lane names are
    explained as sibling sessions.

Not changed, after inspection: the reading of G01 Q5's `Event` list (Roadmap
events, not the excluded logs; both reviews agree); the 23 `g03` edges, the
nine schedule conflicts, the parsing of coverage-plan.md, decisions and
restrictions (both reviews re-derived them); and fixedPoint's consistency
with the manifest, whose scope is unchanged. The skeptic's points that the
`evm`/`theorem` defaults, G15's admission cell and the ledger-symbol
ownership are structural are recorded under Limitations rather than turned
into checks. Lane-name validation was not added. Q1 went to the user, who
chose the foundation children.

## Handoff

- **Base** `caf52ecd4dde5d37cbc0098d47de1a01aa218285`; branch
  `cloud/roadmap-w1-20261029/g03-ledger`, with master `77f8878f` merged in (the
  second-round decisions, g05, fixed-point, hash, g06 and g02). After that
  merge `--check` passes; the Lean build ran before it, and the merge
  touches no Lean file of this group.
- **Done:**
  - this document;
  - `scripts/roadmap-g03-ledger.py`;
  - the generated `roadmap-g03-ledger.json`;
  - one G03 status paragraph in `coverage-plan.md`;
  - one row in `docs/README.md`.

  No Lean module was added or changed (so there are no module-map or
  `Solidity.lean` lines), and no manifest, generated feature file or feature
  status changed.
- **Theorems and definitions:** none new. The ledger cites existing
  declarations only (684 anchors, each checked to be declared in its file).
  The obligations it assigns are the G01 contracts `Admission`/`CheckedFrontend`,
  `Lowering`, `Compilation`, `Execution`, `PublicCorrectness` and `SpecTransfer`
  (`Solidity/Roadmap/Contracts.lean`). Their premises are as G01 states them,
  plus the decision rows D01–D25 (for example, the per-run hash premise D11
  and the `decode` export D14 are not yet in `PublicCorrectness`).
- **Checked:**
  - `python3 -I scripts/roadmap-g03-ledger.py --check`: 0 errors. Ten
    data mutations (an unknown owner, a missing owner, a combination without
    owner, a dropped G00 combination, a parent as owner, a bad anchor, an
    unrefined parent, an empty stage, a dropped decision row) each fail it.
  - `roadmap-g00-scope.py --check` and `solidity-feature-audit.py --check`:
    pass.
  - `check-layers.mjs`: 155 core modules, 0 reach the elaborator.
  - `check-orphans.mjs`: 0 orphaned.
  - `check-trust.sh`: 0 findings.
  - `check-doc-paths.sh`: 46 missing, all at the base; none new.
  - `./run-lean.sh`, cold, on this unchanged Lean tree: `lake build`
    "Build completed successfully (718 jobs)". `SolkeyTestSuite` lost
    `TestSuite.Derived17` to exit 137 (memory under parallel jobs, as in
    G01's run; the memory-loops lane owns that file). The warm re-run built
    it: "Build completed successfully (262 jobs)". Its last step,
    `check-solkey.sh`, reports "37 mismatch(es)", the base count.
- **Elapsed and memory:** about 1 h 35 min wall time (12:14–13:50 UTC). The
  cold build took 69 min 30 s (user 182 min), the warm re-run 3 min 38 s.
  The lowest available memory was 1.74 GB of 15.7 GB, so peak use was about
  14 GB system-wide, sampled every 15 s, during the cold run.
- **Remaining:** the integration steps and remaining child obligations
  above. Every ledger row stays open.
