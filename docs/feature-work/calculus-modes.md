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

None yet.
