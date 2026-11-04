# Calculus modes O10–O13

Status (2026-11-05): **authorized; not yet implemented.** Ideas from a
comparison with verity (Profile, `--deny-*` gates, AdversaryModel,
EntryPointInvariants). Rule ([options.md](../options.md)): a mode is an
argument of the validity statement, as `ValidT`/`ValidTail` are, never a global
setting. SolKey has only `transferSemantics`, so solkey's readings stay the
defaults and TestSuite counts must not move; each new mode gets an options.md
row marked Lean-only. Every lane starts with an inventory of `Bridge/`,
`Solidity/Tools/` and `docs/`.

Existing pieces: `TailMode`/`ValidTail` (`Calculus/TailMode.lean`), `ValidT`
(`Calculus/CallbackHolds.lean`), `StateInv` (`Semantics/Callback.lean`),
`StateInv.cleanTail` (`Calculus/CleanTailBoundary.lean`), `CallMode`
(`Syntax/Scoped.lean`), `Mode.readOnly` (`Semantics/ContractWorld.lean`),
`Contract.evalOrder` (`Syntax/Raw.lean`), the CLI in `scripts/solidity-lean.mjs`.

## Groups

| Group | Deliverable | Depends on |
|---|---|---|
| O10 | **Assumption policy.** Each `verify` row records the modes it was proved under (callback reading, overflow default/checked/ignoringOverflow, TailMode, evaluation order, opaque hash, address 0 has no code). `--require`/`--deny` flags: a row that holds only under a refused mode is reported not-proved. Per-row JSON assumption report. Docs: cli.md, options.md. | — (mode record `Calculus/Assumptions.lean` owned here; O11–O13 add fields by request) |
| O11 | **Caller-model lattice** `none < staticOnly < nonReentrant < any`, generalizing noCallback/withCallback; `staticOnly` reuses `CallMode.static`/`Mode.readOnly`; `nonReentrant` allows callbacks only into functions outside the reentrancy lock. Weakening theorem (valid under a stronger attacker ⇒ valid under a weaker one) over `StateInv`; separating examples in the `Tactics/Callback.lean` style. | — |
| O12 | **Reachable starting states.** A `reachable` mode: storage from deployment plus a finite sequence of public calls; a contract invariant proved once by induction over entry points (rollback on revert); `TailMode.clean` follows. Orthogonal to O11: callbacks inside the sequence follow the chosen caller model. | O11 interface (stub) |
| O13 | **Target profile.** One named bundle of solc version, legacy/via-IR (selects O9 order) and EVM fork, carried in result rows. Built over VS4's compiler and fork parameters (S5.1/S6.1 in [semantics-extensions.md](semantics-extensions.md)); no second fork parameter. | O10, VS4 S5.1/S6.1 |

Out of scope: gas or optimizer modes, a collision-free hash mode (a premise
where needed, never an axiom), more overflow modes.

## Lanes

| Lane | Checkpoints | Owned files |
|---|---|---|
| VC1 | inventory, O10, O13 | `Calculus/Assumptions.lean`, `scripts/solidity-lean*.mjs`, docs/cli.md |
| VC2 | inventory, O11 | new `Calculus/CallerModel*.lean`, `Theory/CallerModel/**`; sole editor of `Semantics/Callback.lean` and `Calculus/CallbackHolds.lean` in this batch |
| VC3 | inventory, O12 | new `Theory/Reachable/**`; sole editor of `Calculus/TailMode.lean`, `Calculus/CleanTailBoundary.lean` |

All three run in parallel; each adds only its own section to options.md and
correctness.md. VC3 states its O11 needs against a stub and adapts after VC2
lands; VC1's O13 waits for VS4's S5.1/S6.1 and otherwise backfills.

## Handoffs

### VC2 — O11 caller-model lattice (2026-11-05)

**Inventory (step 0).** `Bridge/` has no callback or attacker notion.
`Solidity/Tools/` has none either (its counterexample `Tri` reads runs, not
callers). Reused: `StateInv`, `ExecS`/`ExecP`/`ExecF`, `Prog.exec_run`,
`ExecS.eq_run` (`Semantics/Callback.lean`); `holdsC`, `ValidT`,
`TransferSem`, `validT_noCallback_iff` (`Calculus/CallbackHolds.lean`);
`Upd.afterT_imp`, `Modality.forallB`. `CallMode.static` and `Mode.readOnly`
name the `STATICCALL` restriction but no callback run reads them (O1 "not
done", H22), so `staticOnly` is a model of the callee, documented against
them, not a reading of `ExtCall.mode`. `Semantics/Lifetime.lean`'s
`System` (entries as `Prog C [] []`) shaped `Reentry`; it reads the
deterministic run, so it is not reused for re-entry. The reentrancy-lock
examples in the repository are prose only (`Examples/Tactics/Callback.lean`
has no lock); no lock judgment existed. `docs/options.md` O1/O3/O4 fixed
the orthogonality: the transfer semantics says whether a payment calls back,
the caller model what a callee that does may do.

**Interface for VC3 (stable): `Solidity.Calculus.CallerModel`** —
`CallerModel C` (`none | staticOnly | nonReentrant (R : Reentry C) | any`),
`CallerModel.Allows`, `CallerModel.Le`, `Reentry` (`Entry`, `body`,
`guarded`, `held`; `Call`, `Reach`, `Guards`, `KeepsHeld`), the runs
`ExecSM M J`/`ExecPM`/`ExecFM`, `holdsR M I pay`, `ValidM M ts φ`
(`⊨ᶠₘ[M; ts] φ`). Theorems: `Calculus/CallerModelRun.lean`
(`ExecPM.mono`, `ExecPM.toExecP`, `ExecP.ofExecPM`, `Prog.execM_run`),
`Calculus/CallerModelValid.lean` (`validM_any`, `validM_none`,
`validM_none_iff_noCallback`, `ValidM.weaken`, `ValidM.of_validT`,
`Reentry.reachAny_iff`). For O12, a reachable-states mode under model `M`
should read callbacks inside its transaction sequence by `ExecPM M`.

**Done.** Lattice and lock judgment; `any`/`none` coincide with today's
readings (`validM_any` exact; `validM_none` is `Fml.Valid`, equal to
`ValidT .noCallback` without `try`/value call); weakening theorem; one
separating example per adjacent pair (`Examples/Tactics/CallerModel.lean`),
each with its `#print axioms` pinned. Docs: options.md O11, correctness.md
"Caller models (O11)", module-map rows.

**Design note.** `ExecSM` is a model-indexed copy of `ExecS` (41
constructors, three with an `Allows` premise more), not an edit of `ExecS`:
an extra premise on `ExecS` would change the arity of `transferResume`,
`sendResume` and `tryOk` in about twenty modules outside this lane
(`CallbackWk`, `CallbackUnwk`, `CallbackFrame`, `CapturePayments`, …). The
copy's agreement with `ExecS` is proved both ways (`toExecS`, `ofExecSM`).

**Limitations.** No `ProvesC`-style calculus for `staticOnly` or
`nonReentrant`: a proof there is a `ValidT` proof weakened, a `Fml.Valid`
proof where callees change nothing (`Theory/CallerModel/Static.lean`), or by
the runs. A re-entrant call carries no value, and its own callees read as
`any`. The weakening theorem needs positive modalities. The `none <
staticOnly` example separates by the invariant owed on exit; the sharper
separation (two equal calls answered alike only under `none`) is true but
not provable by `sol_close`, which forgets the oracle's correlation.
The separating examples live in `Examples/Tactics/CallerModel.lean`, not
under `Theory/CallerModel/`: they use `dl!{ … }` and `sol_symex`, which
the core library may not reach (`scripts/check-layers.mjs`); the file is
new and no other lane's. Other lanes' needs: none.
