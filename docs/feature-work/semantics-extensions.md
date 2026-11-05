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

### VS1 — contextual equivalence (2026-11-05)

Branch `cloud/semantics-20261105/ctx-equiv`.  Modules: `Solidity/Semantics/CtxEquiv/{Behav,Basic,Unify,StorageObs,Source,Controls,AdversaryControls,RevertFml}.lean`,
`Solidity/Calculus/SurfaceRevert.lean`, `Solidity/Examples/Tactics/RevertFormulas.lean`,
and one printer case in `Solidity/Calculus/PrintStmt.lean`.

**Step 0 (inventory).**
- G49/G50 are statements only: `Roadmap/Contracts.lean` (G01) gives the
  observation `Prefix Event Outcome`, languages `Lang`, two-sided `Refines`
  and `RefinesUnder` (hash premise), pass certificates `Cert` with
  `Cert.comp`, the G50 adversary `SessionEnv` (`requests` and `callee` read the
  whole history, unbounded reentrancy, `Allowed`, `NoCallback`) and
  `PublicCorrectness`/`SpecTransfer`.  `Roadmap/Controls.lean` (G07) has a toy
  source, EVM and compiler meeting it; `Roadmap/V16/*` are fixture consumers,
  no G50 theorem.  Reused, not redefined.
- `Source/Session.lean`'s `sourceLangEvents` is a real G01 `Lang` over
  `SessionEnv`; reused as `srcContract`.
- O's D6 and T07 `Refines`/`solc_validated`: prose only
  (`full-scope.md`); no `Solidity/Optimizer/**` or `Solidity/SolcValidation/**`
  on master.  Stubs stated here (below).
- `Semantics/RecursiveStorage/Observations.lean`: `Value.ObsEq` (path
  observations), a state relation not read by any Source module.
- VY3 assembly notes (`inline-assembly-vy3.md`): statement-level
  Scalar/machine agreement (success and fault equivalences per block), no
  session-level relation.  Not unified here: the block-level equivalences
  could be restated as `CtxEquivOn` over a block-input adversary, as
  `StorageObs` restates `ObsEq`; the session-level route is a `Cert` of the
  assembly pass (`Cert.ctxRefines_*`).  Open.
- `Bridge/`, `Solidity/Tools/`: no contextual or observational relation.
- Revert data: `THalt.revertWith`, `Stmt.revertData`, `RevertBytes.lean`
  encodings; no formula reads it (`semantic-gaps.md`).

**S1.1.**  `Behav` (prefix sets) with the simulation preorder `Below`
(completion and safety transfer) and a history-reading sequencing
`Behav.seq` with its congruence.  `Deployed A E O` (program, adversary
reading, counted bounds), `CtxRefinesOn`/`CtxEquivOn`, the G50 instance
`CtxRefines`/`CtxEquiv` over allowed `SessionEnv`s; preorder, equivalence,
adversary weakening (`noCallback`), `Contract.Faithful` (env injective and
allowedness-preserving; a check on the instances, not a hypothesis of the
relations, and it does not constrain `Counts` or whether `sem` reads the
environment), vacuity made explicit (`CtxRefinesOn.of_empty`).  Controls on the toy (`Solidity/Semantics/CtxEquiv/Controls.lean`) and on a
session-reading toy (`Solidity/Semantics/CtxEquiv/AdversaryControls.lean`: a request reads stored
state, a callback separates a guard so the no-callback reading is strictly
weaker, sequencing reads the history).

**S1.2.**  Exact: `refines_iff`, `refinesUnder_iff`, `ctxEquivOn_iff_refines`,
`artifactRefines_iff` (the public refinement shape is exactly backward plus
forward contextual refinement), `preserves_iff`.  Implications:
`Cert.ctxRefines_back/_forward/ctxEquiv`, `Cert.preserves`,
`PublicCorrectness.ctxRefines_back/_forward`, `transfer'` (SpecTransfer from
the two refinements and `envAbs_eq`), `ctx_succeeds` (the unguarded bytes
show a success; non-vacuity of the guarded side, which `ctxRefines_back`
counts, is open: `RefinesUnder`'s forward half gives no target premise), `Validator.ctxRefines_back/_forward`, `obsEq_iff_ctxEquiv`
(restatement over path adversaries), `srcContract_ctxEquiv_iff`.

**S6.2.**  `RFml` with the revert-reading modality `dl!{ [ P ] φ ↯ ψ }`
over `Prog.runFrames`, data predicates (`Error("m")`, `Panic(c)`, bytes,
selectors, Boolean combinations), conservativity, `revert(bytes)` laws,
notation and printers, `revert(hex"…")` printed back.  The
`semantic-gaps.md` row is partly closed: the formula layer reads revert
data semantically, but the calculus has no taclet for it, the model's data
outside a self-call frame is less than solc's (recorded in
`solc-alignment.md`, "Revert data read in formulas"), and logs are not
modelled (X07).

**Gates.**  Lean server diagnostics clean on every touched file; axiom
guards (`#guard_msgs in #print axioms`) on each main theorem, all within
`propext`, `Classical.choice`, `Quot.sound`; no `sorry`, axiom or
`maxHeartbeats`.  `./run-lean.sh`: `node scripts/check-layers.mjs` (0 core
modules reach the elaborator), `register.sh --check`, and `lake build`
of the default targets and `SolkeyTestSuite` ("Build completed
successfully (3845 jobs)") pass.  Its last step, `scripts/check-solkey.sh`,
reports 57 sort/read drifts against the sibling `../solkey` checkout, which
is at `69e251f`, not the pin `473da8944c` (`docs/solkey-migration.md`; the
pinned commit is not in this container); this branch changes nothing that
check reads (`SortCheck/**`, `Calculus/Rules.lean`, `Calculus/KeyTaclets.lean`).
One earlier full run was stopped by the session's 2-hour limit and one
OOM-killed `Examples/Tactics/OpenLoops.lean` (code 137) beside the Lean
server; the resumed run built it.  Checking time: the `PrintStmt` printer
case rebuilds the printer layer and examples once; it adds no measurable
cost to any file.

**Second review (S6.2 and fixes).**  Fixed: `↯` on a non-modal formula is
now refused; the false notation example; byte literals ≥ 256 in the
printer; `revModal_not_panic` with negative controls (top-level `assert`,
`↯ none` stronger than the box, `↯ _` weaker than the diamond, read-back);
adversary controls for a two-transaction read and an event-only difference;
docs narrowed: the `semantic-gaps.md` row is partly closed, the model's
reduced revert data is a `solc-alignment.md` row, `ctx_succeeds` is about
the unguarded bytes, D6's stub is restricted and not compositional,
`Faithful` is a check on instances, the ABI link is not a theorem, VY3
block equivalences remain open.

**Interfaces requested.**
- X01 (`Roadmap/Contracts.lean`): restate `PublicCorrectness.transfer` as
  `transfer'` (old name a corollary); add `hashed_consistent` to `EvmSpec`
  (the guarded EVM behaviour is otherwise not downward closed in the
  horizon); `DecidableEq` for `CodeUnit`/`Artifact`; a log constructor in
  `Event` (X07) — the relations then observe logs unchanged.
- O01: `Preserves π p h` is D6 restricted to forward, premise-meeting runs
  over G01 observations (no logs, raw call bytes or code hash yet); it is
  not compositional (the middle language's premises are not carried), so a
  pipeline still needs `Cert` per pass, from which `Cert.preserves` gives
  `Preserves`.  D1's artifact clause needs X01's artifact parameter.
- T07: implement `Validator` (computable `validate`, soundness to
  `ArtifactRefines`), keep `Validator.ctxRefines_back/_forward`.  The toy
  validator compares the main runtime only, which is sound only because the
  toy EVM loads nothing else.

**Review (finder and skeptic, read-only).**  Fixed: history-blind and
overclaimed sequencing (now `List E → O → Behav`, documented as behaviour
sequencing); no control exercised the adversary or events
(`Solidity/Semantics/CtxEquiv/AdversaryControls.lean`); D6 stub's shape (now per pass, under both
premises); noncomputable T07 witness (now a computable check plus
`validator_rejects_altered`); unconstrained `env`/`Counts` (now
`Contract.Faithful`, `CtxRefinesOn.of_empty`); docs: refinement direction,
partial-correctness/may-equivalence reading (`failEmpty_ctxEquiv_loop`),
logs unobserved, final-state limits (own balances and code hash not
observed), `Cert.ctxEquiv` needs no forward restriction, `transfer'` uses
`envAbs_eq`, StorageObs is a restatement, Source stuck/divergent prefixes
coincide; missing axiom guards (Source, transfer lemmas).
