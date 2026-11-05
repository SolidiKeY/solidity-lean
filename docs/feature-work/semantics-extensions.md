# Semantics extensions

Status (2026-11-05): **authorized; not yet implemented.** Six structural
additions beside [full-scope.md](full-scope.md), which covers the language (X),
the optimizer (O) and solc validation (T). These groups add metatheory that
X, O and T state separately today. Every lane starts with an inventory of
`Bridge/`, `Solidity/Tools/` and `docs/`, so it reuses what exists.

## Groups

Each group follows the [VM execution contract](../coverage-plan.md#vm-execution-contract):
code, kernel-checked proofs, inhabited witnesses, negative controls,
finder/skeptic review, handoff in this document.

### S1 — contextual equivalence at the ABI boundary

| Group | Deliverable | Depends on |
|---|---|---|
| S1.1 | **Definition.** One relation `CtxEquiv c₁ c₂`: for every caller, callback strategy and transaction sequence (the G50 adversary), both deployed contracts give the same outputs, revert data, logs and final observable state. A preorder `CtxRefines` for nondeterministic sides. Reflexivity, transitivity, congruence under sequencing. | G50 adversary interface |
| S1.2 | **Unification.** Prove that each existing notion implies (or equals) it: O's D6 relation, T's `Refines`, G49/G50 compiler correctness, `Semantics/RecursiveStorage/Observations.lean`, and the VY3 assembly notes. Restate the public theorems through `CtxEquiv`/`CtxRefines`; old names become corollaries. | S1.1, O01 and T07 interfaces (stubs) |
| S6.2 | **Revert data in formulas.** Revert bytes and (once X07 lands) logs readable in `dl{…}` formulas, with printers; closes the open row in `docs/semantic-gaps.md`. | S1.1 |

### S3 — mutability soundness

| Group | Deliverable | Depends on |
|---|---|---|
| S3.1 | **Metatheorems over all well-typed programs.** A `view` body leaves storage, transient storage and balances unchanged in every outcome; a `pure` body's result does not depend on state; a non-payable function reverts whenever `msg.value > 0`. | typed source semantics |
| S3.2 | **`assignable` soundness.** The frame of [function-specs.md](../function-specs.md) follows from the same theorem. | S3.1 |
| S3.3 | **Closer frame facts.** The closer gets the frame facts for free; replace the per-example checks (`Examples/Tactics/TransientStorage.lean`) with uses of the theorem. | S3.1, S3.2 |

### S4 — type soundness (progress)

| Group | Deliverable | Depends on |
|---|---|---|
| S4.1 | **Progress.** A well-typed program never gets stuck: every run returns, reverts, panics, or runs out of fuel or gas. | typed source semantics |
| S4.2 | **Tuples and remaining constructs.** Progress for tuple declarations and assignments (today "without a progress theorem") and every construct X adds, stated so X08 can cite it. | S4.1; X lanes add cases as they land |

### S5 — environment vs compiler nondeterminism

| Group | Deliverable | Depends on |
|---|---|---|
| S5.1 | **Split.** Environment nondeterminism (callers, callbacks, block fields, transaction order) stays universally quantified; compiler nondeterminism becomes an explicit parameter: legacy vs via-IR evaluation order (O9) and gas values under D1. | D1 (X01 contracts) |
| S5.2 | **Both pipelines.** Theorems may state "holds under both pipelines"; D1's non-circularity argument is checked against the parameter. | S5.1 |
| S6.1 | **Fork parameter.** A fork/version parameter, so D2's Osaka choices and `block.slotnum` are not hardcoded; Osaka becomes one instance. | S5.1, X02/X03 interfaces |

### S2 — upgradeability

| Group | Deliverable | Depends on |
|---|---|---|
| S2.1 | **Layout extension check.** A decidable check that V2's storage layout extends V1's, using D3's layout and the ERC-7201 namespaces already evaluated. Proved sound. | X06, S1.1 |
| S2.2 | **Upgrade step.** Proxy over `delegatecall` (X04): swap the implementation, keep storage. | X04, S2.1 |
| S2.3 | **Upgrade theorem.** An upgrade preserves V1's invariant, or meets V2's initializer precondition; stated through `CtxRefines`. | S1.2, S2.2 |

## Lanes

One 16 GiB VM, eight to ten hours, a dependency chain of groups; push each
finished step.

| Lane | Checkpoints, in order | Starts after |
|---|---|---|
| VS1 | inventory, S1.1, S1.2, S6.2 | — (against O/T interface stubs; final check after they land) |
| VS2 | inventory, S3.1, S3.2, S3.3 | — |
| VS3 | inventory, S4.1, S4.2 | — |
| VS4 | inventory, S5.1, S5.2, S6.1 | X01 contracts (VX1) for the final check |
| VS5 | inventory, S2.1, S2.2, S2.3 | VS1's S1.1, X04 (VX3), X06 (VX4) |

Wave 1: VS1–VS4 in parallel. Wave 2: VS5. Owned files: VS1 new
`Solidity/Semantics/CtxEquiv/**`; VS2 new `Solidity/Theory/Mutability/**`;
VS3 new `Solidity/Theory/Progress/**`; VS4 new
`Solidity/Semantics/Nondeterminism/**` and the fork parameter's module; VS5 new
`Solidity/Theory/Upgrade/**`. Edits to files that X, O or T lanes own go to
their owner as requests. Register new modules with
`scripts/coord-tools/register.sh` and add `docs/module-map/` rows.

## Handoffs

### VS2 — mutability soundness (S3.1, S3.2, S3.3)

Branch `cloud/semantics-20261105/mutability`. Modules
`Solidity/Theory/Mutability/{View,Pure,Payable,Assignable,Closer}.lean`;
witnesses, negative controls and axiom pins in
`Solidity/Examples/Tactics/Mutability.lean`.

**Step 0, inventory.** Reused, not restated:

- `Prog.within μ` (`Calculus/Blocks.lean`) is the mutability classifier on the
  intrinsic syntax (`Val.readsState`, `OpLoc.writableIn`, `ARhs.pathIn`):
  the premise of every theorem here. Nothing in `Bridge/` or `Solidity/Tools/`
  defines another one.
- `Prog.run_frame` / `TGFrame` (`Semantics/RunFrame.lean`) and
  `ExecP.frame` (`Semantics/CallbackFrame.lean`): a body within `μ` keeps the
  heap, transaction and, unless `μ` is `nonpayable`, storage, ledger and
  balance on success.  `Prog.run_keeps` / `FrameKeeps` / `Prog.storeAt`: the
  root-granular modifies set; `Storage.Framed.find_eq` reads it per word.
- Transient storage has two models: transient roots inside the one typed
  `Storage` (`Storage.RegionRoot`, `resetTransient`, `Semantics/Storage/Anon.lean`),
  so "storage kept" covers them; and the explicit layer
  `Semantics/Transient.lean` (`Transient.Program`, typed cells beside a state),
  which had `static_preserves` (cells only, success only).
- `Examples/Tactics/TransientStorage.lean` checked the read-only and static
  restrictions per example (`rfl`/`decide` on one state).
- `assignable` (`docs/function-specs.md`): clauses are `SpecLoc` data;
  `assignableFml` (`Calculus/SurfaceSpec.lean`, a `partial def`) builds the
  formula `A`; no semantic counterpart existed.
- Payable: every entry point guards `!payable && msg.value ≠ 0`
  (`Lifetime.System.run`, `Contract.deployT`, `ContractWorld.World.enter`,
  `Transient.Program.transact`); `Lowering/V08/Payable*` prove the compiled
  side.  The H16 source semantics (`Solidity/Source/**`, owned by VY5) has
  `Source.Mutability` with `payable` but no mutability check of bodies; it was
  not touched.

**S3.1.**
- View: `Prog.committed_view` / `Prog.committed_readOnly` — what a run commits
  (`committed`: the end state's `Globals`, the entry's on a halt) is the
  entry's storage (both regions), ledger and balance; with callbacks
  `ExecP.committed_readOnly`; on the transient layer
  `Transient.Program.static_preserves_all` (static or read-only context: cells
  and globals) with `readOnly_preserves`, `write_readOnly`, `write_static`,
  `read_pure`, `selfCall_nonpayable_readOnly`, `ordinary_static`.
- Pure: `Prog.run_withOutside` — replacing a state's `Outside` (storage,
  ledger, balance, transaction) commutes with a pure run, by structural
  recursion over `Stmt`/`Prog` (loops through `TLoop.run_map`); corollaries
  `Prog.pure_independent`, `pure_halt_independent`, `pure_local_independent`,
  `pure_outside`; on the transient layer `Transient.Program.run_withOutsideCells`
  and `Transient.Program.pure_independent` (outside and transient cells).
- Payable: `System.run_nonpayable`, `deployT_nonpayable`,
  `transact_nonpayable`, `ContractWorld.World.enter_nonpayable`,
  `World.enter_static`, `World.callFrame_nonpayable`.

**S3.2.** `Frames L σ τ` (every word of a root outside `L` unchanged, ledger
and balance kept), `assignableRoots`, the decidable `assignableCheck`
(read-only body, or modifies set inside the clause's roots) and
`assignableCheck_sound`; from S3.1, `Prog.frames_readOnly` (every clause,
`\nothing` included) and `Prog.storage_readOnly`; from the modifies set
`Prog.frames_of_storeAt`; every outcome `committed_frames`.

**S3.3.** `Closer.lean`: `holds_modal_readOnly` (scoped `holds` of a box or
diamond), `Spec.box_readOnly`, `Transient.holds_readOnly`,
`Transient.holds_frame` add the frame to a proved modal fact.
`Examples/Tactics/TransientStorage.lean` now proves `static_write`,
`view_write`, `pure_read`, `view_mutable_call` by the theorems (for every
cell, value and state where they take one), adds `static_ordinary_write_all`
and `view_reentry_frame` (frame from `holds_frame`); its remaining run checks
are unchanged and still pass.

**Evidence.** Each theorem has a decided premise on a concrete program and a
negative control in `Examples/Tactics/Mutability.lean` (`put5_changes`,
`peek_depends`, payable/value-free entries that commit, `setA_check_b`,
`setA_changes_a`); axiom pins: only `propext`, `Classical.choice`,
`Quot.sound`.

**Gates.** Lean MCP diagnostics clean on every touched file;
`./run-lean.sh` (2026-11-05): `Build completed successfully (3841 jobs)`
(default targets, examples, `SolkeyTestSuite`), then `check-solkey.sh` fails
with `57 mismatch(es)` against `../solkey` at `69e251f`, not the pinned
`473da8944c` (`docs/solkey-migration.md`): environmental, and this lane
touches no rule, taclet or sort annotation. Layers, roots and axiom pins
passed in the earlier `gate.sh` run.

**Reviews** (read-only finder and skeptic, no Lean server). Fixed:
static frames were uncovered (now `static_preserves_all`,
`ordinary_static`, `enter_static`); the payable docstring overclaimed
coverage (narrowed, gaps listed below); misleading names
(`readOnly_view` → `view_ne_nonpayable`); missing witnesses and controls for
`assignable` and the transient payable entry; missing docstrings.  Recorded
as limitations:

- "Every outcome" is proved content only for successful runs; a halt commits
  the entry state by construction (`TRes` carries no state), which is the
  semantics' rollback, not a theorem about it.  Covered runs: `Prog.run`,
  `ExecP`, `Transient.Program.run`; not the `Lifetime`/`ContractWorld` drivers.
- The premise is `Prog.within`, not a declared `view`/`pure`: the elaborator
  does not check declared mutability, and no theorem says a solc-accepted
  `view` body passes `within .view`.  `within` is stricter than solc: no
  memory locals or writes, no external `view` call (`callReceiver`), no
  `catchData`/`new`; `pure` also rejects memory reads, memory `.length` and
  hashing, which solc allows.  Independence is over storage, ledger, balance
  and transaction (and, on the transient layer, the transient cells); heap
  and locals are inputs.
- Payable: the theorems state each entry point's guard.  Not covered:
  `World.create` (its frame is private; it enters through `World.enter`),
  `World.deployLibrary`, and ABI dispatch (`Semantics/Dispatch.lean`,
  `AbiEntry*`), which models no `callvalue` check.  The `payable` flag of a
  `Lifetime.System` action or `ContractWorld.Entry` is the model's; it is not
  proved to equal `FunDecl.payable` (the constructor's is read directly).
- S3.2 is root-granular: `s.f`, `m[e]` coarsen to their root; transient roots
  are framed too.  That `Frames` implies the formula `A` (`assignableFml`, a
  `partial def`) is argued, not proved.  `assignableCheck` rejects bodies
  whose modifies set is `none` (payments, memory, aliases).
- S3.3 gives lemmas for proofs; `sol_close` itself does not use them.

**Interfaces requested from other owners.** To close the payable gap at the
source level: VY5 (`Solidity/Source/**`) or the ABI dispatch owner — a
`callvalue` check in dispatch keyed by the declared mutability, and a
function-to-entry constructor carrying `FunDecl.payable`.  To lift the
`within` gaps: the Calculus owner of `Calculus/Blocks.lean` — admitting memory
reads in `Val.readsIn .pure` (the heap is already fixed by
`Prog.run_withOutside`'s statement, so the pure proof would extend).
### VS4 — S5.1, S5.2, S6.1 (nondeterminism split, fork parameter)

Branch `cloud/semantics-20261105/nondeterminism`. New modules under
`Solidity/Semantics/Nondeterminism/` (rows in `docs/module-map/language.md`).
X01 and X02 were not on master at the base commit, so the work follows the
frozen D1–D6 text in [full-scope.md](full-scope.md).

**Step 0, inventory.** What already exists, and what this lane reuses:

| Concern | Where it is today | Reused as |
|---|---|---|
| Callers, transaction order, callbacks, balances, code existence | G01 `SessionEnv` (`Roadmap/Contracts.lean`: `requests` by history and index, `callee : Strategy`, `balance`, `hasCode`), universally quantified by `Lang.Allowed` and `PublicCorrectness.refines` | the environment of every split language |
| Callbacks at the intrinsic level | `TransferSem`, `ValidT`/`ValidC` (`docs/options.md` O1, O3) | unchanged; an option of the theorem, as before |
| Block fields | Source: `Glob.timestamp`, fixed to `0` by `SrcProg.glob`; Yul: `Yul/Views/Inputs.lean` (`Environment`, `EnvRead`, Osaka `blockhash`); the backend slice (`Backend/Environment/Observations.lean`) keeps six opcodes; `Language.BlockField` lists the excluded `block.*` members, `slotnum` included | `BlockEnv F` mirrors `EnvRead` and maps `BlockField` |
| Evaluation order (O9) | `EvalOrder`, `Contract.evalOrder` (`Syntax/Raw.lean`); `Pipeline.order` (`Roadmap/TypedRun.lean`); in the source `Glob.pipeline` (`Source/Eval.lean`), `SrcProg.pipeline` | `CompilerChoice.pipeline` |
| Artifact table (G00 Q5) | `Artifact`, `SourceSpec.meaning : … → Artifact → lang.Prog` | `CompilerChoice.artifact` |
| Gas values (D1) | none: `gasleft` is refused (`Language/Features.lean`; `Lowering/Readonly/SourceReadBuiltinControls.lean`); `EvmSpec.gas` is a resource | `GasOracle` (new) |
| Both pipelines | `pipelines`, `SourceSpec.AllPipelines`, `PublicCorrectness.bothPipelines` | `holdsBoth_iff_pipelines`, `holdsBoth_iff_settings` |
| D1 non-circularity | the G07 gate (`roadmap-g01-interfaces.md`, "Non-circularity as a checkable gate"; `scripts/check-noncircular.mjs`), argued for the artifact table only | `Confined`, `SoundAtOracle` |
| Osaka choices (D2) | `Evm.Fork` (one constructor), `Evm.osaka`, `Evm.pinned`, `allButOne64`, `Evm.Precompile`; `Stipend.osakaCold` and `pinned.stipend` (`Stipend/Rule.lean`) | `ForkSpec.osaka` agrees with each by `rfl` |

Nothing in `Bridge/` or `Solidity/Tools/` defines these notions.

**S5.1** (`Solidity/Semantics/Nondeterminism/Split.lean`, `Solidity/Semantics/Nondeterminism/Source.lean`). `CompilerChoice` is the
pipeline, the artifact table and a `GasOracle`, which answers D1's
`gasleft`, `gas`, `msize` and `pc` after a history. `SplitSpec` is G01's
language family indexed by the choice. Each language declares which programs
read a D1 value (`readsD1`).

- `Holds c p Φ` quantifies the environment and the bound at a fixed choice.
- `HoldsFor q art` quantifies every oracle.
- `HoldsBoth` quantifies both pipelines, each at its artifact. In these
  user-facing forms the choice is quantified universally too. The split has
  content where the compiler fixes the choice: refinement at its output,
  and the oracle its target run reports.

`sourceSplit` is the source semantics with the choice's pipeline, and
`sourceSplit_own` makes it `sourceLang` at the program's own pipeline. The
source reads no D1 value yet, so it declares none and is confined
(`sourceSplit_confined`). `Solidity/Semantics/Nondeterminism/SourceWitness.lean` runs `sourceSplit` itself
at an allowed environment (`envA_allowed`). A constant hash makes the
creation address computable (`createAddress_zero`). In the run, `g()`
returns `++x + x` after `x = 1`: `3` under legacy and `4` via IR
(`order_legacy`, `order_viaIR`). So "completes with 3 or not at all" holds
for the legacy run but is not a `HoldsBoth` statement (`order_not_both`).
The contract is deployed at address `0`, the creation address under the
constant hash. The split source is non-vacuous at
every choice (`sourceSplit_nonVacuous`), so no choice rescues an
always-reverting target (`sourceSplit_refutes`).

**S5.2** (`Solidity/Semantics/Nondeterminism/Pipelines.lean`). The statement form is `HoldsBoth`. It reduces
to the two cases (`holdsBoth_iff_pair`). `holdsBoth_iff_settings` is only
bookkeeping over `SourceSpec.setPipeline`. D1's non-circularity is checked
against the parameter in two parts.

1. `Confined` says the artifact and oracle change nothing for any program
   the language declares D1-free.
   - Under it a wrong compiler stays wrong at every choice
     (`Confined.refutes`).
   - Plain-choice witnesses for each pipeline lift to every choice
     (`Confined.nonVacuous`).
   - `NonVacuous.refutes` refutes an always-reverting target at every
     choice.
2. An `OracleTarget` carries the oracle its own runs report, and
   `SoundAtOracle` states soundness at that oracle.
   - For oracle-blind programs the oracle drops out
     (`soundAtOracle_iff_fixed`).
   - An oracle-reading language still refutes a wrong target at the
     target's own oracle (`circular_refuted`).

Negative controls:

- `circular` reads the oracle for a program it declares D1-free, and is not
  confined (`circular_not_confined`). Declaring the read passes vacuously
  (`circularHonest_confined`).
- A target that may come with any oracle makes both an always-success and
  an always-revert target sound (`circular_rescues`). This is why the oracle
  must be part of the target's definition.
- `orderToy_not_both` shows `HoldsBoth` is strictly stronger than one
  pipeline.
- `envToy_each` and `envToy_no_choice` show the choice may not depend on the
  environment.

**S6.1** (`Solidity/Semantics/Nondeterminism/Fork.lean`, `Solidity/Semantics/Nondeterminism/ForkAgreement.lean`, `Solidity/Semantics/Nondeterminism/ForkStipend.lean`).
`ForkSpec` carries:

- the block fields (`has`), with two invariants: `number` and `timestamp`
  exist, and the field `block.difficulty` reads exists;
- the precompile table;
- the code-size, gas-cap, block-gas, depth and stack limits;
- the gas constants;
- the `blockhash` window;
- the stipend constants.

Osaka is `ForkSpec.osaka`. It agrees with:

- `Evm.osaka` (`osaka_pin`);
- `Evm.pinned` after the four G01/G06 idealizations
  (`osaka_idealized_pin`);
- D2's reading, which keeps the code-size limits (`osaka_d2_pin`);
- `allButOne64` and the precompile table;
- the Yul views (`ofViews_field`, `osaka_blockhash`, `osaka_blobhash`);
- `Stipend.rule` (`osaka_stipendRule`).

`BlockEnv F` reads a field only with a proof that `F` has it, and gates
`blobhash?` on `blobbasefee`. So `block.slotnum` has no reading under Osaka
(`field?_slotnum_osaka`) and reads the environment under `osakaWithSlotnum`.
`EnvChoice F` adds the block of each action to `SessionEnv`, indexed like
`requests`, so the block cannot change inside a transaction. Its `Allowed`
includes the chain premise `EnvChoice.Chain`: non-decreasing number and
timestamp, and constant chain id. `SplitSpec.forked` and the controls
adopt that premise, but `ForkedSplit.Allowed` is a field, so a language may
state less. `ForkedSplit` takes the fork as a
parameter, and `HoldsOn` quantifies a list of forks. Controls:

- `slotnum_osaka` and `slotnum_withSlotnum_not` give one statement that
  holds at Osaka and fails once the slotnum fork is in the list;
- `difficulty_control` and `control_difficulty` are a pre-Paris-like fork;
- `prague_differs`;
- `noStipend_rejects_empty`.

`Fork.lean` imports only `Split.lean` (G01 contracts and G06 interface), so
G07 can whitelist it for source modules. The Yul and `Language` agreements
are in `ForkAgreement.lean`.

**Axioms.** Every new theorem is pinned with `#guard_msgs` on
`#print axioms`. They use at most `propext`, `Classical.choice` and
`Quot.sound`. There is no `sorry`, no new axiom and no `maxHeartbeats`
change.

**Reviews.** A read-only re-check after the fixes confirmed the first
four items below and the docstring fixes. It found wording residue (fixed:
the `prague` tag, the `order_not_both` reading, the address-`0` remark) and
two notes now listed as limitations (the free oracle field, the
timestamps). Before that, a read-only finder and a skeptic (no Lean server) reviewed the
first push. Their confirmed findings were fixed as follows:

- The read predicate of `Confined` was free, so the check could not fail.
  It is now the language's declared `readsD1`.
- The oracle in `SoundAtOracle` was a free argument. It is now part of an
  `OracleTarget`, with a refutation control.
- The source witness ran at a disallowed environment, outside
  `sourceSplit`. It now runs `sourceSplit` itself at an allowed environment
  (still at address `0`, which `sessionAt` computes there), with
  `order_not_both` and non-vacuity.
- `Fork.lean` imported Yul and `Lean` modules. It now imports neither, and
  the agreements moved to `ForkAgreement.lean`.
- Drafts and controls carried the `osaka` or `amsterdam` tag. They are now
  tagged `custom`.
- The difficulty reading was unconstrained. It is now an invariant, with a
  real pre-Paris-like control.
- `blobhash` was ungated. It is now gated on `blobbasefee`.
- Blocks were keyed by history. They are now keyed per action, with the
  chain premise.
- D2's code-size reading was missing. `d2` and `osaka_d2_pin` add it.
- Docstrings that claimed more than the theorems proved were corrected
  (`holdsBoth_iff_settings`, `Confined.nonVacuous`, the quantifier claim,
  the `prague` instance).

Findings kept as limitations are listed below.

**Interfaces needed from other lanes** (not edited here):

- X01 (`Roadmap/Contracts.lean`): add the oracle beside `Artifact` in
  `SourceSpec.meaning`, and a D1-read predicate with `Confined` as a
  `SourceSpec` field. Identify `CompilerChoice.artifact` with
  `SourceSpec.meaning`'s artifact, which is today a second, unrelated
  parameter. Move the pipeline out of the program (`SrcProg.pipeline` is
  overridden by `sourceSplit`). The G07 script
  (`scripts/check-noncircular.mjs`) should whitelist `Solidity.Semantics.Nondeterminism.Split`
  and `.Fork` for source modules.
- X02: route `EnvChoice.block` into the source's `Glob`, where
  `Glob.timestamp` is the constant `0` today, and into the lowering. Then
  `sourceForked_blind` stops holding for programs that read block fields.
- X03/X07: the D1 reads read `CompilerChoice.oracle` and `.artifact`,
  `readsD1` becomes the syntactic predicate, and they owe `Confined` again.
  They also owe a substitution lemma: the oracle affects a run only through
  the values of the read expressions. On the EVM side, `EvmSpec` defines
  the oracle of a run, as an `OracleTarget`. D2's schedule beyond the
  recorded constants also belongs to X03: memory expansion, refunds, code
  deposit, creation and intrinsic costs, precompile gas, and opcode
  availability such as `CLZ`. X03 should also read the cold and warm costs
  and the `SSTORE` sentry from `ForkSpec.gas`.
- G06 (`Roadmap/Evm.lean`): `Evm.Fork` has only `osaka`, so `ForkSpec.pin?`
  is `none` elsewhere. `Evm.pinned` idealizes the code-size limits that D2
  keeps (`osaka_d2_pin`).

**Limitations.**

- `OracleTarget.oracle` is a field. Nothing ties it to the target's runs
  until the EVM side defines it (X03), and `circular_rescues` shows what a
  freely chosen oracle allows.
- `EnvChoice.Chain` does not relate timestamps within one block number.
  `EnvChoice.block`'s timestamp is not related to G01's
  `Request.timestamp`; X02 chooses one.

- The intrinsic layer is not split: `Contract.evalOrder` is chosen at
  elaboration.
- `Confined` says nothing about programs that read a D1 value. The
  substitution lemma is X03's.
- `SoundAtOracle` covers soundness only. Adequacy at a target-supplied
  oracle needs X03's gas model.
- `GasOracle` is unconstrained: `gasleft` need not decrease and `msize`
  need not be a multiple of 32. `HoldsFor` therefore cannot prove facts
  that depend on such properties.
- The real source reads none of the artifact, the oracle or the fork. The
  parameter is wired into the source only through the pipeline.
- `prague` and `osakaWithSlotnum` are contrast instances only. Forks before
  Prague have no instance. EIP-7843 and solc's Amsterdam gate for
  `block.slotnum` are taken from `docs/solidity-scope.md` and
  `Yul/ReservedNames.lean`, not from an external source in this repository.
- The fork data is checked against the repository's own Osaka definitions,
  not an external specification.
