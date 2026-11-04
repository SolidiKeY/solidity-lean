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

**S5.1** (`Solidity/Semantics/Nondeterminism/Split.lean`, `Solidity/Semantics/Nondeterminism/Source.lean`). `CompilerChoice` is the pipeline,
the artifact table and a `GasOracle`, which answers D1's `gasleft`, `gas`,
`msize` and `pc` after a history. `SplitSpec` is G01's language family
indexed by the choice. `Holds c p Φ` quantifies the environment and the bound
at a fixed choice, `HoldsFor q art` quantifies every oracle, and `HoldsBoth`
quantifies both pipelines, each at its artifact. `sourceSplit` is the source
semantics with the choice's pipeline, and `sourceSplit_own` makes it
`sourceLang` at the program's own pipeline. The source reads no D1 value yet
(`sourceSplit_confined`). The witness `OrderWitness` is a kernel-checked
session: `g()` returns `++x + x` after `x = 1`, which is `3` under legacy and
`4` via IR (`order_legacy`, `order_viaIR`, `order_differs`).

**S5.2** (`Solidity/Semantics/Nondeterminism/Pipelines.lean`). The statement form is `HoldsBoth`. It reduces to
the two cases (`holdsBoth_iff_pair`) and reads through the input settings
(`holdsBoth_iff_settings`, by `SourceSpec.pipeline_set`). D1's
non-circularity is checked against the parameter in two parts.
`Confined R` says the artifact and oracle change only programs that read a
D1 value (`R`). Under it a wrong compiler stays wrong at every choice
(`Confined.refutes`), and one witness program per kind lifts to every choice
(`Confined.nonVacuous`). `NonVacuous.refutes` refutes an always-reverting
target at every choice. `SoundAtOracle` states soundness at the oracle the
target run supplies, and `soundAtOracle_iff_fixed` shows the oracle drops
out for oracle-blind programs. Negative controls: `circular` (reads the
oracle for a program claiming no D1 read) is not confined, and per-run
oracles make an always-success and an always-revert target both sound
(`circular_not_confined`, `circular_rescues`). `orderToy_not_both` shows
`HoldsBoth` is strictly stronger than one pipeline. `envToy_each` and
`envToy_no_choice` show that an environment input cannot be turned into a
compiler choice: each environment has a working choice, but no single one
works for all.

**S6.1** (`Solidity/Semantics/Nondeterminism/Fork.lean`, `Solidity/Semantics/Nondeterminism/ForkStipend.lean`). `ForkSpec` carries the block
fields (`has`, with `number` and `timestamp` required), the `difficulty`
reading, the precompile table, the code-size, gas-cap and depth limits, the
gas constants, the `blockhash` window and the stipend cost model. Osaka is
`ForkSpec.osaka`. It agrees with `Evm.osaka` (`osaka_pin`), with `Evm.pinned`
after the four idealizations (`osaka_idealized_pin`), with `allButOne64`,
with the precompile table, with the Yul views (`ofViews_field`,
`osaka_blockhash`, `osaka_blobhash`) and with `Stipend.rule`
(`osaka_stipendRule`). `BlockEnv F` reads a field only with a proof that `F`
has it, so `block.slotnum` has no reading under Osaka
(`BlockEnv.field?_slotnum_osaka`) and reads the environment under
`osakaWithSlotnum` (`field?_slotnum_withSlotnum`). `EnvChoice F` adds the
block environment after each history to `SessionEnv`. `ForkedSplit` is a
split language with the fork as a parameter; `HoldsOn` quantifies a list of
forks; `holdsOn_of_forkBlind` reduces fork-blind programs to Osaka.
Controls: `ForkControls.slotnum_osaka` and `slotnum_withSlotnum_not` give one
statement that holds at Osaka and fails once the slotnum fork is in the
list; `prague_differs`, `preParis_difficulty` and `noStipend_rejects_empty`
separate other instances from Osaka.

**Axioms.** Every new theorem is pinned with `#guard_msgs` on
`#print axioms`. They use at most `propext`, `Classical.choice` and
`Quot.sound`. No `sorry`, no new axiom, no `maxHeartbeats` change.

**Interfaces needed from other lanes** (not edited here):

- X01 (`Roadmap/Contracts.lean`): add `GasOracle` (or this module's type)
  to `SourceSpec.meaning` beside `Artifact`, and state D1's confinement as a
  `SourceSpec` field (`Confined` with the D1-read predicate). The G07 script
  should whitelist `Solidity.Semantics.Nondeterminism.Split` for source
  modules, since it imports only `Solidity.Roadmap.Contracts`.
- X02: route `EnvChoice.block` into the source's `Glob` (today
  `Glob.timestamp` is the constant `0`) and the lowering. Then
  `sourceForked_blind` stops holding for programs that read block fields.
- X03/X07: the D1 reads (`gasleft`, `gas`, `msize`, `pc`, `codesize`,
  `codecopy`, `type(C)` code) read `CompilerChoice.oracle` and
  `.artifact`. They owe `Confined` for programs that do not read them, and
  the composition owes `SoundAtOracle` at the target run's own oracle.
- G06 (`Roadmap/Evm.lean`): `Evm.Fork` has only `osaka`; `ForkSpec.pin?`
  returns `none` for other forks until `Evm.Fork` gains constructors.

**Limitations.**

- The intrinsic layer is not split: `Contract.evalOrder` is chosen at
  elaboration, so an intrinsic program family over `Pipeline` is not stated.
- `SoundAtOracle` covers soundness only. The forward (adequacy) direction at
  a target-supplied oracle needs X03's gas model.
- `prague` and `osakaWithSlotnum` are instances for contrast only.
  `osakaWithSlotnum` is not Amsterdam: only EIP-7843 is added. Forks before
  Prague have no instance, and opcode availability by fork (for example
  `CLZ`, EIP-7939) is not a field.
- The source witness uses `sessionFrom` at address `0`. As with
  `session_runs`, the kernel does not reduce `sessionAt`'s creation address.

