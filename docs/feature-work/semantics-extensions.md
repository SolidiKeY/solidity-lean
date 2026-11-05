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

### VS3 — type soundness (progress), 2026-11-05

**Step 0: inventory.** Reused, not redefined:

- *Typing judgment.* Two semantics. The core `Stmt C Γ Γ'`/`Prog C Γ Γ'`
  (`Solidity/Syntax.lean`) is intrinsically typed and its run
  (`Prog.run`, `Prog.runF`, `Semantics/Run.lean`, `Semantics/RunFuel.lean`)
  is total into `TRes`, whose `THalt` has no `stuck`. The source
  interpreter (`Source/Eval.lean`) runs intrinsically typed resolved terms
  (`RExpr`/`RStmt`, `Source/Resolved.lean`, from S01 derivations
  `Typed`/`StmtD` by `toR`) but keeps `Halt.stuck` for run-time mismatches.
- *Progress so far.* `NS`/`NSP` (`Source/ExprProgress.lean`); the value
  fragment `RExpr.ValFragC`/`RStmt.ValFragC` with the joint induction
  `FragAt`/`fragAt` under `CallsOK` (`Source/StmtProgress.lean`);
  `CallsOK` derived for checked elaborated programs
  (`Lowering/P9/FunctionCatalog.lean`, `Source/Progress/CheckedPrograms.lean`);
  direct-node adapters for builtins and `emit`
  (`Source/Progress/{BuiltinAdmission,BuiltinStatements,EmitBuiltins}.lean`,
  `argsFragment_ns`, `builtinFragment_ns`, `encodeVals_key_ns`).
- *Fuel/gas outcomes.* Source: `Halt.revert data` (panics are
  `panicData c`, `Source/Observe.lean`), `Halt.timeout` (the horizon). Core:
  `revert`, `revertWith`, `panic`, `diverge` (fuel), `exhausted`. No gas
  is charged in either (D2, lane X03).
- *Tuple constructs without a progress theorem.* `RStmt.declTuple`
  (lane FU2-B, `docs/semantic-gaps.md`). A tuple *assignment* has no source
  typing rule (`LVal` has no tuple form; `docs/solc-alignment.md`, "Returns
  and tuples"), so it is a typing gap; in the core it is a `Prog` and
  progresses by construction.
- Nothing in `Bridge/` or `Solidity/Tools/` defines progress.

**Delivered** (`Solidity/Theory/Progress/**`, `docs/module-map/theories.md`):

| Checkpoint | Theorems |
|---|---|
| S4.1 | `Ends` and `ns_iff_ends` (never stuck = returns, panics, reverts, out of fuel); `CoreEnds`, `Prog.run_ends`, `Prog.runF_ends` (core, by construction); the closure `SFrag`/`IFrag`, `fragXAt` (joint induction with internal calls over `CallsOKX`, `CallsOK.toX`); `expr_progress`, `stmt_progress`, `items_progress`, `body_progress`, `call_progress`, `elaborated_call_progress`, `elaborated_stmt_progress` |
| S4.2 | `Val.not_tuple`, `RVal.untuple_ok`, `pushVals_ns`, `tupleInit_ns`, `declTuple_ns`, `tuple_stmt_progress`, `StmtD.declTuple_frag` (from S01 derivations); the extension shape `StmtExt.Sound` with sub-blocks; leaf extensions `emitExt_sound`, `revertErrorExt_sound`, `effectExt_sound` (every program), `builtinExt_sound`, `leafExt_sound` (given expression progress at every horizon), `elaborated_leafExt_sound` |

**The extension lemma shape X08 cites** (`Theory/Progress/Fragment.lean`):

```lean
structure Blk (E : Env) (R : List STy) (M : Bool) where
  k : SCtx
  Γ : RCtx
  Γ' : RCtx
  b : RItems E R M k Γ Γ'

structure StmtExt (E : Env) where
  P : ∀ {R M k Γ Γ'}, RStmt E R M k Γ Γ' → List (Blk E R M) → Prop

def StmtExt.Sound (X : StmtExt E) (G : Glob E) (A : Decl → Prop) (Q : String → Prop) : Prop :=
  ∀ Z : StmtExt E, X.Le Z → ∀ n, StmtNSAtX G Z A Q n →
    (∀ m, m ≤ n → ∀ F, Q F.contract → ExprNSAt A G F m) →
    ∀ F, Q F.contract → ∀ nps ph {R M k Γ Γ'} (s : RStmt E R M k Γ Γ') (bs : List (Blk E R M)) l,
      X.P s bs → (∀ b ∈ bs, IFrag Z A b.b) → s.OpsOK → BodyFrame nps R Γ →
      NSP (execS G F (n + 1) nps ph s l)
        (fun o => (s.Simple → ∃ l', o = .normal l') ∧ (k.loop = false → o.esc = false))
```

A statement construct lane X adds proves its one-node step in this form:
`P s bs` admits the node and names the sub-blocks `bs` it hands to the
closure (a `try`'s success and catch blocks); the hypothesis over any
enclosing closure `Z` runs those blocks, so nodes nest, and lanes that
prove their cases separately combine by `StmtExt.Sound.or`.
`stmt_progress`/`call_progress` then give progress for every block, loop
and called body containing the node. `blockExt_sound`/`nestedDecl_ends`
(`Controls.lean`) exercise the sub-block path.

**Interface requests** (files not edited here):

- Source lane (`Source/ValueProgress.lean`, `Source/StmtProgress.lean`): a
  new `RStmt` constructor needs its `RStmt.OpsOK` arm and, if it binds
  locals, its `RStmt.ext` arm.
- Source lane (`Source/ExprProgress.lean`): this closure does not extend
  *expressions*; a new `RExpr` constructor needs an arm in `RExpr.ValFragC`
  and in `exprNSAt_step`. A parametric expression hook there (mirroring
  `StmtExt`) would let X lanes add expression cases the same way.
- Source lane (`Source/TypingExamples.lean`): `stmtCoverage`/`exprCoverage`
  list `.assign` and `.tuple` as typed, but a tuple *assignment*
  `(a, b) = (b, a);` has no `LVal` form; the coverage table should record
  it as deferred.
- Source lane (`Source/Value.lean`, `Halt.stuck`'s docstring): "a
  well-formed program never reaches one" is false while `stuck` also marks
  unmodelled features (`Source/Eval.lean`: dynamic ABI decoding, `new` of
  some types, getters).

**Gates.** MCP diagnostics clean on the seven modules; `#print axioms` on
every main theorem and control: `propext`, `Classical.choice`, `Quot.sound`
only; `./run-lean.sh`: `lake build` of the default targets and the
SolkeyTestSuite completed (3842 jobs; two earlier runs lost unrelated
modules to out-of-memory kills, code 137, and were resumed); its last step,
`check-solkey.sh`, reports 57 mismatches against the container's `../solkey`
checkout (69e251f, newer than the pin `473da8944c`) and passes against the
pinned snapshot `tests/migration/solkey` (`solkeycheck --key …`: OK). No `sorry`, no
axiom, no `maxHeartbeats`, no Source or Core module edited.

**Witnesses and controls** (`Theory/Progress/Controls.lean`): a tuple
declaration (`pairDecl_ends`, actual run `pairDecl_run`, timeout
`pairDecl_timeout`), the same in a `while` loop (`loopDecl_ends`,
`loopDecl_timeout`), a block with a tuple declaration and `assert(false)`
ending by `Panic(0x01)` (`blockDecl_ends`, `blockDecl_run`,
`blockDecl_panics`), nested blocks through the hook (`nestedDecl_ends`),
S01's `w_declTuple` (`elaborated_declTuple_ends`). Negative:
`retPair_unframed_in_frag` + `retPair_unframed_not_ends` (in the fragment
and the domains, stuck without its frame), `all_unsound` (an extension
admitting `_` outside a modifier is unsound), `stuck_not_ends`.

**Reviews** (read-only finder and skeptic subagents, no Lean server).
Fixed: module docs overclaiming "a well-typed program" for the source
interpreter and gas "subsumed" (`Outcome.lean`); `CoreEnds.outOfFuel`
renamed `diverges`; "the hashes" narrowed to string-literal hashes;
the call-site remark for builtins made a theorem
(`elaborated_leafExt_sound`); wrong names in module docs
(`pairDecl_frag`, `CallsOKX` placement) and module-map rows; missing
docstrings; the frame control now shows the other premises hold
(`retPair_unframed_in_frag`); `slotsOK_refuses_reference` and
`no_tuple_local` reclassified as boundaries; the extension shape could not
carry statements with sub-blocks (`try`) and separately proved extensions
did not combine over sub-blocks — `StmtExt.P` now takes the sub-blocks and
`StmtExt.Sound` quantifies over enclosing closures; `emit`/custom-error
reverts split off without the every-horizon premise (`effectExt_sound`);
`panics` documented as read from the data. Confirmed limitations, kept
below.

**Limitations.** Progress holds for the fragment, not for every well-typed
program; the interpreter itself is stuck on well-typed programs using
unmodelled features. Outside `SFrag`: expressions beyond
`RExpr.ValFragC` (strings, memory and reference values, arrays,
`member`, `structNew`, explicit conversions, `delete`, `length`,
`balance`, `magic`, `payable`, external calls, `transfer`/`send`,
`abi.*`, slices, inline arrays, `new`, builtins inside expressions),
the statements `placeholder` (modifiers), `rethrow` and `tryCall` (no
instance yet; the shape admits one), and the transaction layer (dispatch,
ABI decoding, deployment, callbacks). Membership in `SFrag` is a premise;
only tuple declarations (`StmtD.declTuple_frag`) and the existing
`ValFragC` witnesses connect S01 derivations to it. Builtin statements
need expression progress at every horizon, so with calls they are
admitted at call sites of checked elaborated programs, not inside called
bodies (which `CallsOK` keeps in the value fragment). Tuple-declaration
slots must be of value types from value types or constants (`SlotsOK`).
A tuple assignment has no source typing rule (typing gap, recorded above).
`Ends` tells panics from reverts by their data. Every public theorem is
for frames of one contract (`Q = (· = c)`). Gas is not modelled (D2);
the resource ends are `timeout` (source) and `diverge`/`exhausted`
(core). The core statement is by construction.
