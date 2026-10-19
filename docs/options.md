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
| O2 | `checked { … }` (`checkingOF`): an overflow fails both modalities | done |
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

## O2. `checked { … }`: an overflow fails the proof (`checkingOF`)

**Decision.** KeY Java's `arithmeticSemanticsCheckingOF` owes a range goal
per arithmetic operation. Here it is a block, the dual of `unchecked`, and a
program transformation rather than a reading: inside `checked { … }` every
statement is preceded by `assert` of the ranges its checked operations need
(`Prog.checkOF`, `Syntax/Checked.lean`), and a narrow type's check, which
the elaborator writes as a `require` after the write (`narrowCheck`), is an
`assert`. A failing `assert` is a panic, which neither modality accepts, so
a proof of a `checked` program says that no checked operation in it
overflows; outside the block an overflow is a revert, which the box accepts
(solc's `Panic(0x11)`, read as solkey reads its `outOfBounds`).

The run, the rules and the readings are unchanged, and nothing below the
elaborator: the asserts are ordinary statements, and the strategy takes
them by `assertSimple`. The theorem shows them (`assert(x <= x +% 1)`), so
it states what it proves.

**What is guarded**, in evaluation order: `+ - *` at `uint`, `+ - * /` and
unary `-` at `int`, `x ⊕= e`, `x++`, `x−−` on the target's current value,
`push() ⊕= e` on the default `0`; the right operand of `&&`/`||` only where
it is evaluated, a conditional's branches under its condition, a loop's
condition at its head and again at the end of its body, a deferred push's
source at the end of its prefix. `**` is not (no closed bound: it reverts,
as outside), nor division by zero (`Panic(0x12)`, a revert), nor the
wrapping operators of `unchecked`. The guards cannot fail themselves (at
`uint` they use `+%`/`*%`, `a <= a +% b`; at `int`, `MAX - b` under
`b >= 0`), and they are exact: `Syntax/CheckedExact.lean` proves each one
holds exactly when its operation stays in range, at any bound.

**Why not a reading.** The calculus reads a failing term of an update as
the modality's halt (`Upd.afterT`), with no cause attached: a reading in
which an overflow fails both modalities would need every rule to owe the
range of its terms, and every soundness proof to tell an overflow from a
revert. The block gets the same proofs from the existing `assert` rule.
