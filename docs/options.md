# Calculus options (branch `options`)

solkey selects calculus variants with KeY options (`\withOptions`, `-O
category:choice`, `optionsDeclarations.key`): `transferSemantics:
noCallback | withCallback` is the one about the semantics, and integers are
KeY's unbounded `int` with no option. Its own `docs/semantics-bugs-fix-ideas.md`
lists the two gaps this lane closes in Lean: bug 5 (a `try` and a
`call{value}` read as callees that keep the caller's storage) and bug 6
(no overflow semantics: KeY Java's `intRules` has three).

Lean states an option in the theorem, not in a setting: the reading is an
argument of the validity the theorem proves (`ValidT ts φ`, `ValidC I φ pay`,
the notations `⊨[I]`, `⊨ₙ[I]` of `Theorems.lean`), so a proof under one option
can never be read as one under another.

| Milestone | What | Status |
|---|---|---|
| O1 | bug 5: `try` and `call{value}` call back under `noCallback` | done |
| O2 | `checkingOF`: an overflow fails both modalities | planned |
| O3 | the strategy under callbacks (`sol_symex`, `sol_prove` on `ValidT`) | planned |
| O4 | the diamonds of the payments; the invariant from the spec | planned |
| O5 | `ignoringOF`: an overflowing run proves anything | planned |

## O1. Who calls back (bug 5)

**Decision.** `transferSemantics` is about `transfer` and `send`, which
forward the 2300-gas stipend and so cannot call back under `noCallback`. A
`try` and a value call `(bool ok, ) = r.call{value: v}("")` forward all the
gas: their callee may call back under either option. This is solkey's fix
5A, with `CInv` defaulting to `⊤` under `noCallback` (a callee keeping
nothing in particular): `TransferSem.noCallback (I := .top)`.

**The readings.** The callback runs (`ExecS`, `Semantics/Callback.lean`)
take the flag from what the callee may do (`StateInv.pay`): a statement
forks where `Stmt.forksIn pay` says, a `transfer` or a `send` only when
`pay` is set or the send is a value call (`Stmt.send`'s `full`), and runs as
`Stmt.run` otherwise (`ExecS.det`). `holdsC I pay` reads the modalities over
those runs (`Calculus/CallbackHolds.lean`), and `holdsT ts` is `holdsC` at the
semantics' invariant and flag. `ValidT .noCallback φ` is therefore no longer
`Valid φ`: it is when `φ` has no `try` and no value call
(`validT_noCallback_iff`, `Fml.callsBack`).

`Valid` (`holds`, the deterministic run) keeps its meaning: every callee
keeps the contract's state. It is solkey's `noCallback` reading, bug 5
included, and what `Proves` is sound for; `Examples/Tactics/TryCatch.lean`
(`selfCall_valid`, `selfCall_noCallback`) and
`Examples/Tactics/Callback.lean` (`withdrawCall_valid`,
`withdrawCall_noCallback`) state one formula under both and refute it under
`noCallback` with a typed run.

**The calculus.** `ProvesC I pay` (`Calculus/Callback.lean`) is sound for
`ValidC I φ pay` (`ProvesC.valid`, `ProvesC.validT`): its ordinary rules fire
on a statement that does not fork under `pay`, so a gas-limited payment uses
`transferNoCallbackBox`/`sendNoCallbackBox` there, and `plain` hands a goal
with nothing calling back to `Proves`. Its sequent prints as
`⟹ᶜ[I; noCallback]` when `pay` is unset. The callback taclets are sound under
either flag (`holdsC_transferCb`, `holdsC_sendCb`: a run that does not call
back is a resumption that changed nothing).

**The value call.** `Stmt.send` carries `full`; the solc import keeps
`(bool ok, ) = R.call{value: V}("")` as written (it lowered it to
`bool ok = R.send(V)`, as solkey does), and `sol{ … }` reads and prints it.
The send rules match either kind: the deterministic run is the same.

**Not done.** solkey's 5D (a `view`/`pure` callee keeps storage): an
`ExtCall` names its function, not its mutability. The oracle answers a call
by its key alone (`ExtKey`), so two equal calls return the same in a
deterministic run; the callback runs have no such restriction.
