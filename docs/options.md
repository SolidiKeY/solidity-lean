# Calculus options (branch `options`)

solkey selects calculus variants with KeY options (`\withOptions`, `-O
category:choice`, `optionsDeclarations.key`): `transferSemantics:
noCallback | withCallback` is the one about the semantics, and integers are
KeY's unbounded `int` with no option. Its own `docs/semantics-bugs-fix-ideas.md`
lists the two gaps this lane closes in Lean: bug 5 (a `try` and a
`call{value}` read as callees that keep the caller's storage) and bug 6
(no overflow semantics: KeY Java's `intRules` has three: `javaSemantics`,
`arithmeticSemanticsCheckingOF`, `arithmeticSemanticsIgnoringOF`; O2 and O5
are the last two, the run outside both blocks the first).

Lean states an option in the theorem, not in a setting: the reading is an
argument of the validity the theorem proves (`ValidT ts φ`, `ValidC I φ pay`,
the notations `⊨[I]`, `⊨ₙ[I]`, `⊨ₜ[m]` of `Theorems.lean`), so a proof under one option
can never be read as one under another.

| Milestone | What | Status |
|---|---|---|
| O1 | bug 5: `try` and `call{value}` call back under `noCallback` | done |
| O2 | `checked { … }` (`checkingOF`): an overflow fails both modalities | done |
| O3 | the strategy under callbacks (`sol_prove`, `sol_derive` on `ValidT`/`ValidC`) | done |
| O4 | the send diamonds; calls with callbacks; the invariant from the spec | done |
| O5 | `ignoringOverflow { … }` (`ignoringOF`): an overflowing run is assumed away | done |
| O6 | clean array tails: the starting storage's shadows assumed ordinary defaults (`ValidTail .clean`) | done |

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
wrapping operators of `unchecked`, nor the source of a push on a getter's
array (`f().push(v)`: it is read after the getter's body, which may change
what it reads). A statement's right-hand side is guarded before its target,
as the run evaluates them (`TRun.assign`), and a binary operator's left
operand that may halt (a read, `/`, `**`, …, `Val.mayHalt`) is read
(`a == a`, `Checked.touch`) before the right operand's guards.

The guards' own operators cannot overflow (at `uint` they use `+%`/`*%`,
`a <= a +% b`; at `int`, `MAX - b` under `b >= 0`); they read the operands
again, so a guard halts where reading them halts, in the state the
statement reads them in. Each guard's formula holds exactly when its
operation stays in range, at any bound: `Syntax/CheckedExact.lean` proves
that of the formulas restated over `Int`, not of `rangeU`/`rangeI` as
terms. One order is not followed: an operand whose read may halt that
comes before another operand's guarded operation other than as a binary
operator's left operand (a path's base before its index, an earlier
argument, `addmod`'s first operands) is not read first, so where the run
reverts at that read the block asserts the guard first, failing inside
`checked` and assuming the run away inside `ignoringOverflow`.

**Why not a reading.** The calculus reads a failing term of an update as
the modality's halt (`Upd.afterT`), with no cause attached: a reading in
which an overflow fails both modalities would need every rule to owe the
range of its terms, and every soundness proof to tell an overflow from a
revert. The block gets the same proofs from the existing `assert` rule.

## O3. The strategy with callbacks

**Decision.** `sol_prove`, `sol_derive` and `sol_derive?` take a goal read
with callbacks (`ValidT ts φ`, `ValidC I φ pay`, a `ProvesC` sequent) and run
`ProvesC`'s walk (`Calculus/CallbackDerive.lean`), one `apply` per rule as
`sol_derive`'s walk of `Proves` is: `plain` wherever nothing in the sequent
calls back, and `Proves`' walk from there; a callback taclet where a
statement calls back; the rule `Stmt.step` fires on any other statement,
as `Proves` takes it. `sol_prove` closes a `Proves` leaf by
`Proves.assumeInv`, by `sol_leaf; sol_close`, or by them after
`Proves.openInv`; `sol_derive?` writes the walk with those lines
(`Examples/Tactics/CallbackStrategy.lean` pins one: the hand-written
`withdrawSafe`, rule for rule).

`Proves` was not merged into `ProvesC`, nor given an option index: the
merge would make every `Proves` soundness proof one against the callback
reading, and `sol_prove`'s kernel-evaluated walk (`Seq.residue`) would carry
the index. The walk is a sibling instead, and shares the leaves.

**The rules added on the way** (`Calculus/Callback.lean`, sound by
`Calculus/CallbackSound.lean`): `ProvesC.done` (a closing taclet, by the
premise's own soundness at `false`, `holdsC_done`), `ProvesC.assert`
(`assertSimple`), `ProvesC.sendDet` (`sendNoCallbackBox` for a gas-limited
send under `noCallback`: no `{havoc}`), `ProvesC.block` (a block that calls
back, by `ExecS.block`).

**Not covered** (while something in the sequent calls back; where nothing
does, `plain` hands the goal to `Proves`, which covers all of them): a loop
by its invariant or at its unwinding bound (`Proves.inv`, `Proves.check`
have no `ProvesC` counterpart), a loop unwound whose body calls back, an
internal call that returns one value (`y = f(x)`: `Stmt.forksIn` counts
every call as forking, and O4's call rules take only `CallRet.none` and
`.rets`), and a transfer or a send whose operands are not simple (their
capture rules fire only where the statement does not call back).  These stay
leaves.

## O4. Diamonds, calls, and the invariant a specification declares

**The diamonds.** A send's refusal is an outcome of the run (`TRun.send`,
the oracle), so a send under the diamond is the run's:
`CallbackTaclet.sendWithCallbackDiamond` (solkey's, read by `ProvesC.sendD`)
and `ProvesC.sendDetD` (`sendNoCallbackDiamond` for a gas-limited send), sound
over any modality (`holdsC_sendCb`, `holdsC_sendDet`). A `transfer` stays
without a diamond, by the earlier decision: the run books it whatever the
funds, and a refused payment reverts the machine alone (`Evm.compile_correct`),
so `⟨ transfer ⟩` would claim a termination the compiler theorem does not
back. solkey's `transferNoCallbackDiamond` and `transferWithCallbackDiamond`
stay unclaimed (`RuleShapes.unclaimedTaclets`).

**Calls with callbacks.** An internal call whose body calls back is inlined
as `Stmt.step` inlines it (`ProvesC.callNone`, `ProvesC.callRets`: the
parameters declared, the return variables at their defaults, the body under
the caller's locals as a block). Their soundness relates the call's callback
run, its body in its own frame (`ExecS.callBody`), to the inlined block's
(`ExecS.callNone_inline`, `ExecS.callRets_inline`), by forward callback
weakening (`Prog.exec_wk`), as the deterministic `Stmt.runSt_callNone` does by
`Prog.run_wk`. A call that returns one value (`y = f(x)`) or a memory or
storage one has no rule yet (O3, "Not covered"); a specification's
obligation calls by `.rets`, so `spec[C]{f}` is covered.

**The invariant a specification declares.** `invariant[C]` is `C`'s
`invariant` clauses compiled as `spec[C]{f}` compiles them (`specInv`,
`Calculus/Spec.lean`), a closed first-order formula of the storage, as the
`Invariant C` a callee keeps. `ValidC invariant[C] spec[C]{f}` is solkey's
specified problem under `transferSemantics:withCallback`: the invariant
assumed on entry, owed on exit, and owed and assumed again at every payment
and `try`; `ValidT (.noCallback invariant[C]) spec[C]{f}` its honest
`noCallback` reading. `sol_prove` proves `Examples/Tactics/CallbackStrategy.lean`'s
`withdraw_spec`. The invariant does not include the layout premises the
obligation assumes (`layoutFmls`), so a property of the storage's shape is
not known after a callee returns unless the invariant states it.

## O5. `ignoringOverflow { … }`: an overflow assumed away (`ignoringOF`)

**Decision.** KeY Java's `arithmeticSemanticsIgnoringOF` reads the
program's integers as mathematical ones: an operation that overflows goes
on with its unbounded result, which proves of a program what the machine
does not do. The typed state cannot hold that result (a `uint` local is a
256-bit value, `PrimTy.Denote`; only a specification's KeY `int`, `Srt.kint`,
is unbounded), and a second, unbounded state would be a second run. So the
block reads the option soundly instead: where a checked operation would
leave its range, the run is assumed away and satisfies every formula. It is
O2's transformation with another guard statement (`Prog.withOF`,
`OFMode.guardStmt`, `Syntax/Checked.lean`): every statement is preceded by
`if (g) {} else { assume(false); }`, and a narrow type's check by the same.

**`assume(false);`** (`Stmt.assumeFalse`) is a statement of the model, not
of Solidity: its run halts as exhaustion does (`THalt.exhausted`), which both
modalities accept (decision 15), and its rule is `LeanTaclet.assumeFalse`,
`⟨[ assume(false); ]⟩ ⇝ true`. It is outside `⊢ₖ` (`Stmt.keyStep`) and
outside the EVM fragment (`inFrag`): the compiler theorem says nothing of a
program that holds it.

**What it changes.** Only diamonds: the box accepted the revert of an
overflow already. Where a guard is false or halts, the statement it precedes
halts too, by a revert, and where it holds the statement runs as without
it; so a program `p` and its blocks are ordered, `[checked p]φ` implying
`[p]φ`, which is `[ignoringOverflow p]φ`, and `⟨checked p⟩φ`, which is
`⟨p⟩φ`, implying `⟨ignoringOverflow p⟩φ`.  This is argued, not a theorem
here.
`Examples/Tactics/CheckedBlock.lean` §4 proves
`∀ uint a; ⟨ uint y; ignoringOverflow { y = a + 1; }; ⟩ y > a` and refutes
it without the block. The two blocks do not nest in each other (an
elaboration error): the guards are written once, by the outermost; nor does
`checked { … }` inside `unchecked { … }`, whose operations wrap.  The mode
reaches into the functions the block calls, whose bodies are inlined and
guarded with the caller's (KeY Java's option is global), where `unchecked`
stops at a call as solc's does; so a function that holds one block, called
from inside the other, is the same nesting error.

## O6. Clean array tails

**Decision.** A storage array keeps the slots past its live end
(`SVal.array`'s shadow), and an empty `push` on an array of references
exposes the first of them as it is (`pushSlot`), as solc does: a write
through an alias left dangling by a `pop` comes back
(`reused_slot_retains_value`, `Examples/Tactics/CleanTail.lean`), and such a
storage is reachable (`Tokens.dangling`, `dangling_slot_reachable`). So
nothing tells what a recycled slot of the starting storage holds, and
`tokens.push(); assert(tokens[tokens.length - 1].value == 0);` is refuted at
that storage (`pushRead_solc_refuted`, `Examples/Tactics/TailMode.lean`).
Whether to assume the tails clean is an option: `TailMode.solc` assumes
nothing (the reading of `Valid`), `TailMode.clean` assumes every shadow an
ordinary default (`Storage.CleanTail`, `Typing/CleanTail.lean`: a word at
its default, a dynamic array of length `0` whose shadow is one too, a
mapping anything, since no clearing reaches a mapping's entries).

**The reading.** `ValidTail .solc φ` is `Valid φ`; `ValidTail .clean φ` is
`Valid (cleanTail(storage) = true → φ)` (`Calculus/TailMode.lean`), a
formula, so `Proves.valid` proves it unchanged and the premise enters the
sequent by `impRight`. `cleanTail(s)` is a symbol (`Op1.cleanTail`, Lean
only): the interpreter's test, a fold the kernel evaluates
(`Storage.cleanTailB`, `Semantics/StorageWt.lean`, deciding
`Storage.CleanTail`: `Storage.cleanTailB_iff`), `true` on a clean storage
and undefined on any other, as `wt(storage)` is; the Theory reads it by what
the observations show (`TSto.CleanTails`: a read past a dynamic array's
live end, along no mapping key, shows the default word and length `0`),
which the typed property implies (`Storage.cleanTails_obs`). So what
`.clean` proves holds in every state with clean tails
(`ValidTail.holds_of_clean`, `cleanTail_holds` in `Theorems.lean`), the
initial one among them (`ValidTail.holds_init`), and `.solc` implies it
(`ValidTail.clean_of_solc`).

**An assumption, not a kept property.** Clean tails are not an invariant
of the contract: a program that pops an aliased element and writes through
the alias leaves a dirty tail behind (`leaveDirty_boundary_rejected`), and a
callback in the middle of a program that repairs it observes the dirty
storage (`interruptRepair_callback_boundary_rejected`;
`Calculus/CleanTailBoundary.lean` states the boundary conditions, refuted).
So the option is a premise on the starting storage only; what the program
itself writes past an end is read as written, under either option
(`recycledWrite_solc`).

**The closer.** The reduction leaves the starting storage's reads as atoms
(`obsW`, `obsL`), and a read past a live end reads the shadow slot as it is.
Where a leaf assumes the premise (`Fml.assumesCT`: on its spine of
implications, conjunctions and quantifiers), `Seq.checkCore` folds the
eliminated reduction (`LFml.decideMemCT`, `Calculus/DecideCleanTail.lean`):
each atom whose path enters a dynamic array by an unchecked index `q[i]`,
with no mapping key step after it, is read `q; (i < obsL(q) ? obsW(p) : 0)`
(`0` for a length), and `false` where `i` is the live length itself
(`lenOf`: `obsL(q)` or `obsL(q) + 1 - 1`, its guards dropped), since the
closer does not fold `a < a`. A checked index and a member pass, a mapping
key stops the fold. Sound by `LTm.ctFold_eval` where the storage shows clean
tails, and by vacuity where it does not (`Fml.assumesCT_holds`). Such a
leaf is offered the plain closer too (`decideMemCT || decideMem`), so the
premise never loses a leaf `decideMem` closes; without the premise
`checkCore` is unchanged. So `sol_decide`, and `sol_prove`'s
leaves, prove the recycled slot's default (`pushRead_clean`,
`pushRead_clean_box`, `pushAlias_clean`).

| Option | `ValidTail` | The starting storage | Proved of a recycled slot |
|---|---|---|---|
| `solc` | `Valid φ` | any typed storage | what the program wrote there, nothing of the start |
| `clean` | `Valid (cleanTail(storage) = true → φ)` | its shadows ordinary defaults | the default, unless the program wrote it |

**Not done.** `next(b)` (the alias of an empty `push`, `p[p.length]`)
reaches the closer as the index `obsL(q)` and is handled so; a `nextIn`
over another storage term, and indices that equal the live length only by
arithmetic other than `+ 1 - 1`, are left as atoms (still exact, only not
read as the default). `sol_close` (the `simp` closer) does not read the
premise.

## Review

One read-only pass after O5, a finder per area, each finding checked
against the code; fixed on the branch:

* O2/O5: the guards of `x = e`, `x ⊕= e`, the memory assignments and
  `push() ⊕= e` were asserted target first, where the run evaluates the
  right side first; a getter's push source was guarded before the getter
  ran; a binary operator's halting left operand was read after the right
  one's guards (`Checked.touch`, `haltsFirst`); `checked` inside
  `unchecked` checked nothing silently (now an error); the docs claimed the
  guards could not halt and the ordering held exactly.
* O3/O4: the walk took `transferWithCallbackBox` (a `{havoc}`) for a
  gas-limited transfer under `noCallback`, before `transferNoCallbackBox`
  (`transferThenTry`); a `Proves` leaf written `· sorry` under a bullet was
  not paired with its goal; the `Proves` sub-walk caught no timeout and did
  not charge its steps to the walk's budget; the uncovered shapes were
  understated (one-value calls, loops by invariant); the rule map's header
  counts were stale.
* Not changed: a call with non-simple arguments under callbacks is inlined
  without `functionCallArgCapture` first (sound; the walk's rule names
  differ from `Proves`').
