# Calculus options

solkey selects calculus variants with KeY options (`\withOptions`, `-O
category:choice`, `optionsDeclarations.key`): `transferSemantics:
noCallback | withCallback` is the one about the semantics, and integers are
KeY's unbounded `int` with no option. Its own `docs/semantics-bugs-fix-ideas.md`
lists the two gaps these options close in Lean: bug 5 (a `try` and a
`call{value}` read as callees that keep the caller's storage) and bug 6
(no overflow semantics: KeY Java's `intRules` has three: `javaSemantics`,
`arithmeticSemanticsCheckingOF`, `arithmeticSemanticsIgnoringOF`; O2 and O5
are the last two, the run outside both blocks the first).

Lean states a calculus option in the theorem, not in a setting: the reading is an
argument of the validity the theorem proves (`ValidT ts φ`, `ValidC I φ pay`,
the notations `⊨ᶠ[I]`, `⊨ᶠₙ[I]`, `⊨ᶠₜ[m]` of `Theorems.lean`), so a proof under one option
can never be read as one under another.

| Milestone | What | Status |
|---|---|---|
| O1 | bug 5: `try` and `call{value}` call back under `noCallback` | done |
| O2 | `checked { … }` (`checkingOF`): an overflow fails both modalities | done |
| O3 | the strategy under callbacks (`sol_prove`, `sol_derive` on `ValidT`/`ValidC`) | done |
| O4 | the send diamonds; calls with callbacks; the invariant from the spec | done |
| O5 | `ignoringOverflow { … }` (`ignoringOF`): an overflowing run is assumed away | done |
| O6 | clean array tails: the starting storage's shadows assumed ordinary defaults (`ValidTail .clean`) | done |
| O7 | the solc test runner states a calling-back obligation under `ValidT .noCallback` | done |
| O8 | a `try` whose receiver is the contract itself runs its callee; no code at address `0`; a value call to `this` runs `receive` | done |
| O9 | configurable expression order: legacy and Solidity via IR | done |

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
`Fml.Valid φ`: it is when `φ` has no `try` and no value call
(`validT_noCallback_iff`, `Fml.callsBack`).  A recursive call's
`callsBack` is its body's, every frame of the unrolling: proved off one
frame (`sol_no_callback`, `Prog.callsBack_recUnroll`), never evaluated.

`Fml.Valid` (`holds`, the deterministic run) keeps its meaning: every callee
keeps the contract's state. It is solkey's `noCallback` reading, bug 5
included, and what `Proves` is sound for; `Examples/Tactics/TryCatch.lean`
(`selfCall_valid`, `selfCall_noCallback`) and
`Examples/Tactics/Callback.lean` (`withdrawCall_valid`,
`withdrawCall_noCallback`) state one formula under both and refute it under
`noCallback` with a typed run.

**The calculus.** `ProvesC I pay` (`Calculus/Callback.lean`) is sound for
`ValidC I φ pay` (`ProvesC.fmlValid`, `ProvesC.validT`): its ordinary rules fire
on a statement that does not fork under `pay`, so a gas-limited payment uses
`transferNoCallbackBox`/`sendNoCallbackBox` there, and `plain` hands a goal
with nothing calling back to `Proves`. Its sequent prints as
`⟹ᶜ[I; noCallback]` when `pay` is unset. The callback taclets are sound under
either flag (`holdsC_transferCb`, `holdsC_sendCb`: a run that does not call
back is a resumption that changed nothing).

**The value call.** `Stmt.send` carries `full`; the solc import keeps
`(bool ok, ) = R.call{value: V}("")` as written (solkey lowers it to
`bool ok = R.send(V)`), and `sol{ … }` reads and prints it.
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
source at the end of its prefix. Unsigned `**` is not (no closed bound: it reverts,
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
terms. One order is not followed: a path's base whose read may halt before
its index's guarded operation is not read first, so where the run
reverts at that read the block asserts the guard first, failing inside
`checked` and assuming the run away inside `ignoringOverflow`.

The supported signed-power lowering uses existing value operations. Its final
signed-range overflow witness is an overflowing signed add, so this extension
can guard that witness; overflow of the intermediate unsigned magnitude power
still reverts. This does not add a general power guard. See
[the numeric milestone](feature-work/numeric-operators.md#group-04-signed-shifts-powers-and-literal-typing).

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

Before expanding more calls, `sol_prove` also checks a newly assumed
premise and up to eight earlier typed context layers with the existing
bounded scoped refutation (`Seq.refuteS`), including a prefix before havoc. When
the complete context proves `false` and its wrapped contradiction contains
no callback, `ProvesC.closeFalse` closes the branch. Thus an impossible
`address(this) != address(this)` branch does not expand later self-calls.
The context is kept intact: in particular, a diamond update that cannot
land cannot be pruned by simply projecting the condition. Failed checks
restore tactic state and continue the walk. `sol_derive?` offers the
fixed `sol_prefix_false 8` replay, with the refutation and both full-context
guards checked synchronously by the kernel. Set
`sol.prove.pruneFalse` to `false` to compare proof-search costs; it changes
no theorem's semantic reading.
The metaprogram's evaluated Boolean only selects an attempt. The resulting
`refutePrefix_sound` application and its modal-free and callback-free
guards are checked by the kernel, and the probe is recorded in the trust
inventory.

After `plain` has produced an ordinary `Proves` goal, closing mode tries
one compiled `Seq.prove` stage of at most 128 steps, capped by the callback
walk's remaining fuel. A successful attempt charges the entire bound;
its exact ordinary leaves still use the invariant-aware `closeLeaf`.
Failure restores the original goal before the structural walk continues.
The replay records `sol_prove (steps := n)` and the selected leaf closers,
so it repeats no stage search. This route never applies to a `ProvesC`
goal and never changes the callback reading. The nonclosing `sol_derive`
walk remains structural. Set `sol.prove.compiledPlain` to `false` to
compare this optimization with the structural route.

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

**Recursive calls** (`Calculus/RecursionCallback.lean`): `plain` is not
tried on a sequent with a recursive call (or a `{havoc}`, which `Proves` has
no rule for; `ProvesC.havocIntro` takes it into the context): the walk
stops at the call, which `rec_auto_c` proves by `ProvesC.recValid` where
nothing calls back, else by a contract over the callback runs
(`ProvesC.recContract`; `docs/kernel-port.md`, "Recursion").

**Captures whose rest calls back** (`ProvesC.capture`,
`Semantics/CallbackCapture.lean`, `Calculus/CapturePayments.lean`).
`ProvesC.unfold` and `ProvesC.bind` ask that neither the statement nor the
program it unfolds to call back: their soundness reads both as their
deterministic runs.  That is too strict for a capture, whose captured part
declares a value and hands control to nobody: `if (nse) S` with a branch
that calls back, a loop unwound whose body calls back, a payment whose
receiver or amount is not simple.  `ProvesC.capture` puts the side
condition on the capture alone: `Stmt.CapturesAs pay m s P e`, every run of
`s` with callbacks is one of the captured program `P`'s, its fresh locals
popped, or a halt `m` accepts that is no panic.  One lemma per shape proves
it, from the forward weakening of callback runs (`Prog.exec_wk`): `.ite`
(`ifElseUnfold`), `.loop` (`whileUnwind`, a body that calls back: the loop
may diverge, so under the box only), `.transferAmt`, `.transferRecv`,
`.sendAmt`, `.sendRecv` (`transfer_unfold_…`, `send_unfold_…`, where the
payment calls back: `pay`, or a value call's `full`).  The walk tries
`ProvesC.capture` after `ProvesC.unfold` (`CallbackWalk.captureLemmas`).
A `require`'s, an `assert`'s and a ternary's captures leave a statement
that calls nobody, so `ProvesC.unfold` already took them.

`ProvesC.loopExit` is `loopExit` with callbacks, under the box: a loop at
its unwinding bound ends there or, its body calling back, diverges
(`holdsC_loopExit`).  So a bounded loop whose body calls back is proved
by unwinding (`Examples/Tactics/CallbackStrategy.lean`, `pingTwice`).

**Calls** fork where their body does (`Stmt.forksIn`, `Stmt.forks`): a
call whose callee calls nobody back runs as `Stmt.run` (`ExecS.det`), and
its callback runs are still the body's in its frame (`ExecS.call_cases`).
One whose callee calls back is inlined under callbacks as
`internalCallExpand` inlines it, whatever it returns: none
(`ProvesC.callNone`), a tuple's targets (`ProvesC.callRets`), one value
(`ProvesC.callVal`, `y = f(x)`: the result assigned past the body,
`Prog.callResult`), a storage reference (`ProvesC.callStorage`) or a memory
one (`ProvesC.callMem`), each sound by its callback runs
(`ExecS.callVal_inline`, `callStorage_inline`, `callMem_inline`).  A callee
read by its contract under callbacks is a recursive one's
(`ProvesC.recContract`); an internal call's contract (`FunContractC`) is not
used by the walk, which inlines.

**A loop by its invariant** (`ProvesC.invBox`, `whileInvariantBox`'s goals,
under the box): the body's goal is read over its callback runs, from every
state the body's frame allows (`{anon(xs)}`, `{havoc}`): a body that calls
back has no modifies set (`Stmt.storeAt` is `none`, so its frame is
`{havoc}`), and a callback replaces only the storage and the ledger, which
that frame may write (`ExecP.frame`, `Semantics/CallbackFrame.lean`); a
body with a modifies set calls nobody back (`Prog.callsBack_of_storeAt`), so
its callback run is its run, and only the roots it names are anonymised
(`docs/loops.md`, "Modifies sets").  The invariant is the loop's own: what the
callee may change it does not keep unless it restates the contract's
invariant (`Examples/Tactics/CallbackStrategy.lean`, `pingNInv`).  Sound by
`holdsC_invBox`, by induction over the iterations (`ExecS.loop_box`).  A
body with a `try` has a frame (`Stmt.within`): a `try` pays (its callee may
write the storage and the ledger, and call back), so it is within
`nonpayable` only, when its clauses and a self-call's callee are, and it
writes the caller's locals its clauses write (`Stmt.run_frame`,
`ExecS.frame`; `tests/solc/CallbackCalls.sol`, `loopOfTries`).  A clause
that binds the data (`catchData`) allocates, so it has none (`whileClose`).

**No diamond over a loop that calls back**: its callback runs include a
divergence (`ExecS.loopDiverge`, an over-approximation: the relation is
inductive and does not tell a loop that ends from one that does not), so a
diamond over it never holds (`holdsC_diamond_loop`), at its unwinding bound
or by an invariant and a variant (`decreases`) alike.  This is correct, not
a gap of the rules: no diamond rule over such a loop could be sound.  A
variant would be read only by a divergence clause that asks for an
unbounded chain of iterations (or a fuel-indexed run), a change to
`ExecS` and to every lemma by cases on it.

**Not covered** (while something in the sequent calls back; where nothing
does, `plain` hands the goal to `Proves`, which covers all of them): a
diamond over a loop whose body calls back (above), and a recursive call
returning a reference (`CallRet.isValues`; `docs/kernel-port.md`,
"Recursion").  These stay leaves.

## O4. Diamonds, calls, and the invariant a specification declares

**The diamonds.** A send's refusal is an outcome of the run (`TRun.send`,
the oracle), so a send under the diamond is the run's:
`CallbackTaclet.sendWithCallbackDiamond` (solkey's, read by `ProvesC.sendD`)
and `ProvesC.sendDetD` (`sendNoCallbackDiamond` for a gas-limited send), sound
over any modality (`holdsC_sendCb`, `holdsC_sendDet`). Transfer diamonds now
have conditional formula rules `ProvesC.transferD` and `transferDetD`:
`¬ [r.transfer(a);] false` supplies actual runtime acceptance for the same
simple operands. The callback rule separately requires the booked exit
invariant and continuation after arbitrary invariant-preserving storage,
ledger and balance havoc; the deterministic rule requires only the booked
continuation. `CallbackDerive` recognizes this exact conditional shape.
These are sufficient Lean adaptations, not equivalences or unconditional
SolKey taclet ports. The bare `LeanTaclet.transferDiamond` remains false:
funding and recipient acceptance cannot be inferred from uint nonnegativity.
The semantic exactness results remain in `PaymentWitness`; see the
[payment handoff](feature-work/diamond-payments.md).

The human-approved payment account keeps these semantics. Exact funding/recipient,
refusal-state and deterministic/callback send conditions are in
`Calculus/PaymentConditions.lean`: callback failure remains mandatory even after
acceptance. This does not replace the unconditional transfer refutation or claim
source-world/gas correspondence.

**Calls with callbacks.** An internal call whose body calls back is inlined
as `Stmt.step` inlines it (`ProvesC.callNone`, `ProvesC.callRets`: the
parameters declared, the return variables at their defaults, the body under
the caller's locals as a block). Their soundness relates the call's callback
run, its body in its own frame (`ExecS.callBody`), to the inlined block's
(`ExecS.callNone_inline`, `ExecS.callRets_inline`), by forward callback
weakening (`Prog.exec_wk`), as the deterministic `Stmt.runSt_callNone` does by
`Prog.run_wk`. Calls returning one value, a storage or a memory reference
are O3's `ProvesC.callVal`, `callStorage`, `callMem`; a specification's
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
nothing (the reading of `Fml.Valid`), `TailMode.clean` assumes every shadow an
ordinary default (`Storage.CleanTail`, `Typing/CleanTail.lean`: a word at
its default, a dynamic array of length `0` whose shadow is one too, a
mapping anything, since no clearing reaches a mapping's entries).

**The reading.** `ValidTail .solc φ` is `Fml.Valid φ`; `ValidTail .clean φ` is
`Fml.Valid (cleanTail(storage) = true → φ)` (`Calculus/TailMode.lean`), a
formula, so `Proves.fmlValid` proves it unchanged and the premise enters the
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

**An assumption, and a contract's invariant where nothing is exposed.**
Clean tails are not kept by every program: one that pops an aliased element
and writes through the alias leaves a dirty tail behind
(`leaveDirty_boundary_rejected`), and a callback in the middle of a program
that repairs it observes the dirty storage
(`interruptRepair_callback_boundary_rejected`;
`Calculus/CleanTailBoundary.lean` states the boundary conditions, refuted).
So the option is a premise on the starting storage; what the program itself
writes past an end is read as written, under either option
(`recycledWrite_solc`).  They are kept by a program that **exposes nothing**
(`Prog.exposesNone`, `Typing/CleanTailRun.lean`): one that shrinks an array
of references (an assignment or a `delete` of a reference, a copy out of
memory, a `pop` of references) only where no storage alias is in scope, in
its own frame or a caller's, and has no recursive call (not unfolded).
Then every alias stays at live slots and every write lands at live slots
(`CTInv`, `Stmt.keeps_ct`: the invariant is the clean storage and every
alias local live, `Storage.LiveAll`; where an alias may be held around a
statement it also keeps every live reference live, `Storage.Grows`), and a
clear is all that lands past an end.  A contract all of whose transactions
expose nothing has clean tails in every storage it reaches from its
deployment (`ReachableBy.cleanTail`), so what `.clean` proves holds there
(`ValidTail.holds_reachable`, `pushRead_reachable` in
`Examples/Tactics/TailMode.lean`).  The reading is the deterministic run's
(`Fml.Valid`): under the callback reading a callee's own run is not checked.

**The runner.** `scripts/test-solidity.mjs` states a contract's plain
obligations (neither a specification nor one that calls back, O7) under
`.clean`, `⊢ cleanTail(storage) = true → N.f.problem`, where every function
of the contract but an internal one elaborated, takes no storage reference
and exposes nothing (`contractTailMode`, `Frontend/Testing.lean`; the
premise justified by `ReachableBy.cleanTail`); under `.solc` otherwise.
Each JSON row says which (`reading`, `docs/solidity-testing.md`).

**The closer.** The reduction leaves the starting storage's reads as atoms
(`obsW`, `obsL`), and a read past a live end reads the shadow slot as it is.
Where a leaf assumes the premise (`Fml.assumesCT`: on its spine of
implications, conjunctions and quantifiers), `Seq.checkCore` folds the
eliminated reduction (`LFml.decideMemCT`, `Calculus/DecideCleanTail.lean`):
each atom whose path enters a dynamic array by an unchecked index `q[i]`,
with no mapping key step after it, is read `q; (i < obsL(q) ? obsW(p) : 0)`
(`0` for a length), and `false` where `i` is the live length itself
(`lenOf`: `obsL(q)` or `obsL(q) + 1 - 1`, its guards dropped), since the
closer does not fold `a < a`.  Each guard is a key comparison the closer
splits on (`LTm.pick`), and a guard the test of an enclosing `ite` decides
is dropped (`LTm.ctFoldK`): a read through a `delete` tests the same
`i < obsL(q)` before it reads the starting slot. A checked index and a member pass, a mapping
key stops the fold. Sound by `LTm.ctFold_eval` where the storage shows clean
tails, and by vacuity where it does not (`Fml.assumesCT_holds`). Such a
leaf is offered the plain closer too (`decideMemCT || decideMem`), so the
premise never loses a leaf `decideMem` closes; without the premise
`checkCore` is unchanged. So `sol_decide`, and `sol_prove`'s
leaves, prove the recycled slot's default (`pushRead_clean`,
`pushRead_clean_box`, `pushAlias_clean`).

| Option | `ValidTail` | The starting storage | Proved of a recycled slot |
|---|---|---|---|
| `solc` | `Fml.Valid φ` | any typed storage | what the program wrote there, nothing of the start |
| `clean` | `Fml.Valid (cleanTail(storage) = true → φ)` | its shadows ordinary defaults | the default, unless the program wrote it |

**Not done.** `next(b)` (the alias of an empty `push`, `p[p.length]`)
reaches the closer as the index `obsL(q)` and is handled so; a `nextIn`
over another storage term, and indices that equal the live length only by
arithmetic other than `+ 1 - 1`, are left as atoms (still exact, only not
read as the default). `sol_close` (the `simp` closer) does not read the
premise.

## O7. The test runner reads callbacks

**Decision.** `scripts/test-solidity.mjs` reports `proved` for a
kernel-checked statement, and `⊢ N.f.problem` states `Fml.Valid`, bug 5
included, which would prove `trySuccessKeepsStorageUnsound` and
`callKeepsStorageUnsound` (`tests/solc/open`), false on the EVM where the
callee is the contract itself. So `testObligation` (`Frontend/Testing.lean`) states
the actual obligation, plain or specified, as callback validity whenever
`Fml.callsBack false` is true (a value that does not reduce counts as true).
`SolcFun.writingCall` records bare high-level external calls as well as
`try` and low-level calls, but metadata cannot override the obligation's
operational semantics.

It is proved by `sol_prove` (O3), the goal read at the obligation's value
and the declaration stated at `N.f.problem`; one with a recursive call by
`rec_auto_c`, whether it calls back read off one frame of each unrolling
(`sol_no_callback`), a recursive storage or memory return by its contract
over the callback runs (`ProvesC.recContract`, `ProvesC.recContractM`,
`docs/kernel-port.md` "Recursion"). Elsewhere it stays
`⊢ N.f.problem`: with nothing calling back `Fml.Valid` is the reading
(`validT_noCallback_iff`).

**Callee mutability.** The operational `ExtCall` does not yet record static
call restrictions (O1, 5D). Consequently even a `view` or `pure` external
call receives the conservative callback reading. Static-call rows may stay pending until that restriction is represented
and proved; metadata alone does not justify plain validity.

**Where it lives.** In the runner alone: `N.f.problem` is still one table
of formulas (`solc_scoped_problems`), the reading the statement's type. The
TestSuite's derived theorems (`Solidity/TestSuite/Derived*.lean`) and
`#solkey_derive?` stay `⊢ N.f.problem`, solkey's reading, as their
documents say; `tests/solc/CallbackReading.sol` pins the four cases.

## O8. Self-calls and address `0` 

**Why.** solkey's solc/open ports `trySuccessRunsCallee`,
`tryCatchExactReturn`, … call the contract itself
(`try this.setIx() { assert(ix == 42); } catch {}`), which is true on the
EVM; `Stmt.run` read every callee as the transaction's oracle (`TTx.ext`).
And `callWithoutCodeReverts` relies on address `0` having no code.

**The run** (`TRun.tryCall`, `Semantics/Run.lean`), in this order:

1. the receiver is `0`: the caller reverts (no code there; a modelling
   assumption, `docs/solc-alignment.md`);
2. the receiver is `address(this)` and the statement carries the callee
   (`Stmt.tryCall`'s `self`): its body runs as an inlined call with targets
   (`TRun.call … (.rets rets)`), in a frame of its own; on success the
   success clause runs from the callee's state with the returned values
   bound; a revert runs the `Error` clause when its data decodes as
   `Error(string)`, the `Panic` clause when it decodes as `Panic(uint256)`,
   the catch-all otherwise (`docs/semantic-gaps.md`, "Revert data": the
   callee's copy keeps its reasons, a named clause binds them);
   a panic runs the `Panic` clause with the entry's code, `1` without one;
   exhaustion and divergence halt the caller.  Storage, ledger and heap are
   the caller's on every failure: a halted run has no state to keep;
3. otherwise the oracle, as before.

A callee whose reason is not a literal (`revert(string.concat(…))`, a
rethrown `bytes`) is refused by `sol{}`; what reading it would take (a
revert-outcome modality) is `docs/semantic-gaps.md`, "Revert data", "Left
open".

**The frame.** The elaborator (`trySelfBody`, `Syntax/Elab.lean`) inlines
the callee as an internal call with targets and rewrites its environment
(`RawStmt.selfFrame`): `msg.sender` is `address(this)`, `msg.value` is `0`
(a `try` sends nothing), in the calls it inlines too.  The run needs no
change of `TTx`.

**Termination.** The callee is a function declared before the caller (the
elaborator's `funs`, as for an internal call), whose parameter types are the
arguments' and whose return types are the `try`'s binders, or whose returns
a `try` that binds none ignores (`try this.id(x) { … }`: the callee called
as a statement, `Stmt.selfCall?`); any other callee is the oracle's.  So the body is a subterm of the statement and `Stmt.run`
stays structural, with no fuel.  A self-call of a later function, or of
itself, is not run (reported as left).

**The rule** (`LeanTaclet.tryCallSelfBox`, `trySelfStep`,
`Calculus/Blocks.lean`; sound by `Premise.sound_trySelfBox`,
`Calculus/SoundCalls.lean`).  solkey has none: its `try` never runs a
callee.  Five goals, the run's case split written as `require`s:

1. `require(a != 0); require(a == address(this)); f(args) → rets; ok`: the
   callee inlined as a call with targets (`functionBodyExpand`), then the
   success block;
2. `∀ rets. require(a != 0); require(a != address(this)); ok`: the oracle;
3.–5. each `catch` block from the caller's state, behind `fails(call)`:
   `¬⟨ require(a == address(this)); f(args) → rets; ⟩ true`
   (`ExtCall.selfFails`, the branch's `Branch.hyp`).  A `catch` is reached
   from another contract's callee, where that `require` reverts, or from
   the contract's own callee when it reverts or panics.

`tryCallNoCallbackBox` (and its callback twin) now match only a `try` with
no self body (`self = false`, the taclet notation writes it); it does not
split on address `0`, which only makes its goals stronger.  The diamond is
`false` either way (`tryCallSelfDiamond`).

**The `catch` goals.** A box goal over the callee accepts its revert, so
no goal of the five says that the callee ends normally: the `catch`
goals carry it as a premise instead (`fails(call)` above), and the walks
(`Seq.run`, `Walk.walk`, `CallbackWalk.walk`) take a premise `¬X` whose `X`
reads a program by proving `X` in the goal's place (`Proves.notLeft`, KeY's
`impRight; notLeft`), where the walk closes `X`, and drop it otherwise
(`Proves.hideLeft`, `hide_left`): the closer reads no program in a
context.  So `uint r; try this.g() returns (uint a) { r = a; } catch { r =
9; } assert(r == 13);` proves where `g` always returns `13`
(`tryCatchExactReturn`, `Examples/Tactics/SelfCall.lean`'s `gOneExact`).
Soundness: `Premise.sound_trySelfBox` reads `fails(call)` off the run (the
callee's `TRun.call` halted, or the receiver is another);
`holdsC_trySelfCb` off the callback run, whose `catch` constructors now
say why they are reached: `tryError`, `tryPanic`, `tryOther` only at
another address for a self-call, `trySelfError`, `trySelfPanic`,
`trySelfOther` after the callee's run halts (`Semantics/Callback.lean`).

**The `Panic` goal per code.** The `Panic` block is behind the codes its
callee may panic with (`CodeBinder.guard`, `Prog.panicCodes`,
`Calculus/Blocks.lean`; printed `panics(selfBody) →`): `require(a !=
address(this) || c == k₁ || …);` in front of it, the `kᵢ` the `Panic` codes
of the data the callee lists (`Stmt.revertDatas`: `0x01` for a failed
`assert`, `0x11` for an overflow in `checked { … }`), `require(a !=
address(this));` where the clause binds no code and the callee panics with
none.  The codes are known where the callee raises no panic of its own
(`Prog.asserts`), pays nobody (`Prog.hasTransfer`), lists its data and none
of its data known in part may be `Panic`'s (`Pat.notPanic`); elsewhere the
goal binds any code, as before.  At another receiver the code is the
oracle's, which the `a != address(this)` disjunct admits.  Sound by
`Prog.panicCodes_call` (`Prog.run_dataS`, `Prog.run_noPanic`) in
`Premise.sound_trySelfBox` (`holds_tryPanicG`), and with callbacks by
`Prog.panicCodes_exec` (a callee that pays nobody runs as its run,
`ExecS.eq_run`) in `holdsC_trySelfCb` (`holdsC_tryPanicG`):
`ExecS.trySelfPanic` binds the code its data carries
(`Semantics.decodePanic`), any code only after a panic of the callee's own.
`Examples/Tactics/RevertData.lean`'s `assertCode` proves `c == 1` in
`catch Panic(uint c)` of a callee with `assert(x < 3)`, `overflowCode`
`c == 17` of an overflow in `checked { … }`.

**A value call to `this`.** `(bool ok, ) = r.call{value: v}("")` with the
contract's `receive` declared before the caller is elaborated as `bool se =
r == address(this); if (se) { try this.receive{value: v}() { ok = true; }
catch { ok = false; } } else { (ok, ) = r.call{value: v}(""); }`
(`elabValueCall`, `receiveSelfBody`, `Syntax/Elab.lean`): `receive` inlined
in a frame of its own whose `msg.sender` is the contract and whose
`msg.value` is a parameter the call passes `v` (`ElabScope.selfValue`); every
failure is `ok = false` with the caller's state, and a payment to oneself
moves no ether (`State.pay` books nothing at `address(this)`), so the
self-call books nothing.  The rules are `tryCallSelfBox`'s (`ProvesC.trySelf`
with callbacks), whose soundness covers it; `Stmt.send` is unchanged.  A
`receive` whose body calls a function that reads `msg.value` is not run (its
frame has no such parameter): the call is then the oracle's, as before.
`callRunsReceive` proves; `callKeepsStorageUnsound` stays open (false on the
EVM: `Examples/Tactics/SelfCall.lean`'s `keepsStorage_invalid`).

**The callback reading.** `ExecS` has three more constructors
(`trySelfOk`, `trySelfHalt`, `trySelfViolated`): the callee's run as an
inlined call, then the success block; its other outcomes are the existing
`tryError`/`tryPanic`/`tryOther`.  So the deterministic run is still one
of the callback runs (`Stmt.exec_run`).  A self-call reaches the oracle's
`tryOk` (any state the callee may leave) only where the run does: at an
address other than `0` and the contract's (`tryOk`'s last premise).

`ProvesC.trySelf` (`Calculus/Callback.lean`, sound by `holdsC_trySelfCb`,
`Calculus/CallbackSound.lean`; Lean only) is `tryCallSelfBox` read with
callbacks, as `ProvesC.tryCall` reads `tryCallNoCallbackBox`: the invariant
where control leaves ("invariant on exit"); `tryCallSelfBox`'s self goal,
the callee inlined, whose own `try`s and payments may call back; the other
receiver's goal, at an address other than `0` and the contract's (both
premises, as `tryOk` has them), after `{havoc}` with the invariant assumed; each `catch`
goal from the caller's state.  `sol_prove`'s walk tries it before
`tryCallWithCallbackBox` (`Calculus/CallbackDerive.lean`), so the runner's
`ValidT .noCallback` reading (O7) proves a self-call `try` whose callee
writes storage.

**The runner.** `scripts/test-solidity.mjs --self-address A` declares every
obligation with the premise `address(this) == A` (`Problem.selfPre`,
`solc_scoped_problems N decl self A`), for solkey's ports, which pin a
parameter to the harness's address instead of writing `this`.
`tests/solc/SelfCalls.sol` writes the same claims with `this`.

**Left.** A self-call of a function declared after the caller, or of
itself; a `receive` whose callees read `msg.value`.

**Speed.** A `try` of a function declared before the caller now carries a
second copy of the callee's body (the elaborator inlines it once more), so
such programs elaborate and kernel-check larger terms.  Each `catch` goal
carries a third copy, in `fails(call)`, and the walk symbolically executes
the callee once more per `catch` goal to prove it; a value call in a
contract with a `receive` carries `receive`'s body and splits on the
receiver.

## O9. Expression evaluation order

`Contract.evalOrder : EvalOrder` selects the schedule used while elaborating
expressions. Its default preserves the legacy schedule. To select Solidity's
IR code generator's source-order expressions, define a named contract:

```lean
def IR : Contract := { MyContract with evalOrder := .viaIR }
```

Use `IR` in `sol[IR]{ … }`, `dl[IR]{ … }` or the local `InContract` instance.
For imported functions, append `evalOrder .viaIR` to `solc_import`, after
`testing` when present. The imported contract retains that configuration.

The preset is two flags: `binaryLeftToRight` and `modularLeftToRight`.
`hoistPair` shares the capture policy between binary schedules, preserving
operand positions and saving an earlier read before a later effect. The
modular flag uses the existing argument-capture pass in source order; the
legacy branch retains its early zero-modulus guard. Ordinary calls and indices
remain left to right, assignments evaluate their source before their target,
and short-circuit operators and conditional branches retain their conditional
evaluation. Inlined callees inherit the configuration.

This is an expression-order choice, not all of `--via-ir`: constructor and
modifier differences remain as documented in [solc-alignment.md](solc-alignment.md).
Solidity [describes source order as an intention, not a guarantee](https://docs.soliditylang.org/en/latest/ir-breaking-changes.html#semantic-only-changes).
Yul itself evaluates function arguments right to left; that is a different
schedule from Solidity source compiled through IR.

`Examples/Tactics/EvaluationOrder.lean` pins both schedules by kernel-checked
runs, including nested calls, modular arguments, failure priority, conditional
evaluation, a calculus proof and an imported contract.

A failing read is saved before later explicit guards (`captureBefore`),
for binary operands and argument lists in either schedule.
