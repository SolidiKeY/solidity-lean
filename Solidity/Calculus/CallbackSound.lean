import Solidity.Calculus.CallbackSound.Rules
import Solidity.Calculus.CallbackSound.Calls

/-!
# The calculus with callbacks is sound

`ProvesC I pay H φ` (`Calculus/Callback.lean`) proves `φ` with callbacks:
what it derives holds, its context in front, when every `try` and value call,
and with `pay` every payment, may call back into the contract and the callee
leaves the invariant as it found it
(`holdsC`, `ValidC`, `Calculus/CallbackHolds.lean`).  `ProvesC.sound_of`
and `ProvesC.fmlValid` take the invariant first-order (`Fml.FO`, a contract
invariant of the storage and the ledger; `Invariant.fo` carries it): "the invariant holds" is then a
fact of what the state's terms read (`State.ReadsAs`: its global part and
its locals erased), which the callee's run and the updates preserve.

* A rule of the calculus fires on a statement that runs no other by a
  choice and pays nothing (`ProvesC.update`, `unfold`, `bind`): such a
  statement has one callback run, its typed run, and what its premise asks
  of that run (`Premise.Runs`, the arms' statement, `Stmt.runs`) carries
  the premise over every callback run of the rest.
* A split (`ifElseSplit`, `requireSimple`) runs with callbacks as the branch
  its condition picks (`Premise.Runs`' split clause, which the `if` arm
  proves of `ExecS`'s `ite` runs).
* The callback taclets read `ExecS`'s runs of a payment and a `try`: halted
  (a payment of simple operands never halts), the invariant broken on exit
  (refuted by "invariant on exit"), or resumed from a state the callee may
  leave, the invariant holding (the premise "resume after callback", "send
  succeeded", "call succeeded"); a send that fails and a `try` whose call
  reverts run their clause from where they were made.

`Frames.popsOnly`, `Fml.reclose?` and the `openInv`s use
`match` on the indexed families, against Gate G0's first condition: an
exemption, timed (`docs/intrinsic.md`, W3c `tactics`), since they run once
a rule.

The module is split by topic, each piece importing the one before
(`Calculus/CallbackSound/Rules.lean`, `Calculus/CallbackSound/Calls.lean`);
this module imports them all.
-/
