import Solidity.Semantics.Callback
import Solidity.Calculus.Callback
import Solidity.Calculus.CallbackHolds
import Solidity.Calculus.CallbackSound
import Solidity.Calculus.Notation
import Solidity.Calculus.WalkSyntax

/-!
# The callback reading on typed runs

`Semantics/Callback.lean` used: a program that pays has, among its
callback runs, the deterministic one, unless the invariant breaks on the way
(`Prog.exec_run`); a program that pays nothing has only the deterministic
one, so a fact of every callback run is decided by running it
(`ExecP.forall_iff`).

The reading with callbacks over the typed state (`holdsC`, `ValidC`,
`Calculus/CallbackHolds.lean`): a formula with no payment reads as
without callbacks, and `pre → [ P ] post` true with callbacks is true
without, when only `P` pays.

The calculus with callbacks (`ProvesC`, `Calculus/Callback.lean`) on a
send: solkey's three goals of `sendWithCallbackBox`, each closed in the
plain calculus, the invariant `true`, read as `ValidC` by `ProvesC.fmlValid`
(`Calculus/CallbackSound.lean`).
-/

namespace Solidity.Examples.Tactics.CallbackRuns

open Solidity Solidity

private def paysCore := (sol[StandardExample]{
  uint to = 9; to.transfer(2); } : Prog StandardExample [] _)

/-- The program pays. -/
example : Prog.hasTransfer paysCore = true := rfl

/-- Its deterministic run is a callback run, whatever the invariant, unless
the invariant breaks at the payment. -/
example (J : StateInv StandardExample) (σ : State StandardExample []) :
    ExecP J σ paysCore (.ofRes (Prog.run σ paysCore)) ∨ ExecP J σ paysCore .violated :=
  Prog.exec_run J paysCore σ

/-- A failing guard pays nothing, so every callback run of it reverts, as
its deterministic run does (by the kernel). -/
example (J : StateInv StandardExample) :
    ∀ o, ExecP J (State.ofStorage Storage.standardExample) guardLowCore o →
      o.halt? = some .revert :=
  (ExecP.forall_iff rfl (fun o => o.halt? = some .revert)).2 (by decide +kernel)

local instance : InContract := ⟨StandardExample⟩

/-! ## The reading with callbacks -/

/-- With no payment the two readings agree (`holdsC_iff_holds`), whatever
the invariant. -/
example (I : Invariant StandardExample) :
    ValidC I cdl!{ [ uint x = 1; ] x == 1 } ↔ Fml.Valid cdl!{ [ uint x = 1; ] x == 1 } :=
  ⟨fun h σ => (holdsC_iff_holds _ rfl σ).1 (h σ), fun h σ => (holdsC_iff_holds _ rfl σ).2 (h σ)⟩

/-- KeY's `transferSemantics` option: under `noCallback` only a `try` and a
value call call back (`validT_noCallback`), under `withCallback I` a payment
too; with neither in it, a formula reads under `noCallback` as the typed
reading. -/
example (I : Invariant StandardExample) (φ : Fml StandardExample []) :
    (ValidT (.noCallback I) φ ↔ ValidC I φ false) ∧ (ValidT (.withCallback I) φ ↔ ValidC I φ) :=
  ⟨validT_noCallback, validT_withCallback⟩

example : ValidT .noCallback cdl!{ [ uint x = 1; ] x == 1 } ↔
    Fml.Valid cdl!{ [ uint x = 1; ] x == 1 } :=
  validT_noCallback_iff rfl

/-- A payment true with callbacks is true without: the deterministic run
is a callback run (`valid_of_validC`, from `Prog.exec_run`). -/
example (I : Invariant StandardExample) (a : Fml StandardExample []) (P : Prog StandardExample [] [])
    (H : ValidC I (.imp a (.modal .box P .nil .tt))) (ha : a.hasTransfer = false) :
    Fml.Valid (.imp a (.modal .box P .nil .tt)) :=
  valid_of_validC H (Fml.callsBack_of_hasTransfer a ha) rfl

/-! ## The calculus with callbacks -/

/--
trace: case h.h.exit
⊢ dl{ ∀ uint to ⟹ᶜ[Fml.tt] { pay(to,5) } true }

case h.h.ok
⊢ dl{ ∀ uint to, { pay(to,5) ‖ ok := true }, { havoc }, true ⟹ᶜ[Fml.tt] true }

case h.h.failed
⊢ dl{ ∀ uint to, { ok := false } ⟹ᶜ[Fml.tt] true }
-/
#guard_msgs in
example : ProvesC .tt true [] .nil cdl!{ [ ok = to.send(5); ] true } := by
  apply ProvesC.allIntro
  apply ProvesC.bindIntro
  apply ProvesC.send .sendWithCallbackBox
  trace_state
  case exit => exact .plain (.updIntro (.updIntro (.closeTrue rfl))) rfl
  all_goals exact .plain (.closeTrue rfl) rfl

/-- The derivation proves the send valid with callbacks, whatever a callee
that keeps the invariant does (`ProvesC.fmlValid`). -/
example : ValidC ⟨.tt, rfl⟩ cdl!{ [ ok = to.send(5); ] true } := by
  apply ProvesC.fmlValid
  apply ProvesC.allIntro
  apply ProvesC.bindIntro
  apply ProvesC.send .sendWithCallbackBox
  case exit => exact .plain (.updIntro (.updIntro (.closeTrue rfl))) rfl
  all_goals exact .plain (.closeTrue rfl) rfl

/-! Under `transferSemantics:noCallback` the send runs as its typed run: the
ordinary rule fires (`sendNoCallbackBox`), and the sequent says which
reading it is in. -/

/--
trace: case h.h
⊢ dl{ ∀ uint to ⟹ᶜ[Fml.tt; noCallback] [ ok = to .send(5); ] true }
-/
#guard_msgs in
example : ProvesC .tt false [] .nil cdl!{ [ ok = to.send(5); ] true } := by
  apply ProvesC.allIntro
  apply ProvesC.bindIntro
  trace_state
  apply ProvesC.plain _ rfl
  sol_derive

end Solidity.Examples.Tactics.CallbackRuns
