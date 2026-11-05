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
