import Solidity.Semantics.Core.Callback
import Solidity.Calculus.Core.Callback
import Solidity.Calculus.Core.CallbackHolds
import Solidity.Calculus.Core.CallbackSound
import Solidity.Calculus.Core.Notation

/-!
# The callback reading on typed runs

`Semantics/Core/Callback.lean` used: a program that pays has, among its
callback runs, the deterministic one, unless the invariant breaks on the way
(`Prog.exec_run`); a program that pays nothing has only the deterministic
one, so a fact of every callback run is decided by running it
(`ExecP.forall_iff`).

The reading with callbacks over the typed state (`holdsC`, `ValidC`,
`Calculus/Core/CallbackHolds.lean`): a formula with no payment reads as
without callbacks, and `pre → [ P ] post` true with callbacks is true
without, when only `P` pays.

The calculus with callbacks (`ProvesC`, `Calculus/Core/Callback.lean`) on a
send: solkey's three goals of `sendWithCallbackBox`, each closed in the
plain calculus, the invariant `true`, read as `ValidC` by `ProvesC.valid`
(`Calculus/Core/CallbackSound.lean`).
-/

namespace Solidity.Examples.Tactics.CoreCallback

open Solidity Core

private def pays : Solidity.Prog StandardExample := sol[StandardExample]{
  uint to = 9; to.transfer(2); }

open Lean Elab Command in
run_cmd liftCoreM do
  if let some e ← Prog.defineCore `Solidity.Examples.Tactics.CoreCallback.paysCore
      ``StandardExample [] pays then
    throwError "paysCore: {e}"

/-- The program pays. -/
example : Prog.hasTransfer paysCore = true := rfl

/-- Its deterministic run is a callback run, whatever the invariant, unless
the invariant breaks at the payment. -/
example (J : StateInv StandardExample) (σ : TState StandardExample []) :
    ExecP J σ paysCore (.ofRes (Prog.trun σ paysCore)) ∨ ExecP J σ paysCore .violated :=
  Prog.exec_run J paysCore σ

/-- A failing guard pays nothing, so every callback run of it reverts, as
its deterministic run does (by the kernel). -/
example (J : StateInv StandardExample) :
    ∀ o, ExecP J (TState.ofStorage Storage.standardExample) guardLowCore o →
      o.halt? = some .revert :=
  (ExecP.forall_iff rfl (fun o => o.halt? = some .revert)).2 (by decide +kernel)

local instance : InContract := ⟨StandardExample⟩

/-! ## The reading with callbacks -/

/-- With no payment the two readings agree (`holdsC_iff_holds`), whatever
the invariant. -/
example (I : Invariant StandardExample) :
    ValidC I cdl!{ [ uint x = 1; ] x == 1 } ↔ Core.Valid cdl!{ [ uint x = 1; ] x == 1 } :=
  ⟨fun h σ => (holdsC_iff_holds _ rfl σ).1 (h σ), fun h σ => (holdsC_iff_holds _ rfl σ).2 (h σ)⟩

/-- KeY's `transferSemantics` option: `noCallback` is the typed reading
(`validT_noCallback`), `withCallback I` the one with callbacks. -/
example (I : Invariant StandardExample) (φ : Core.Fml StandardExample []) :
    (ValidT .noCallback φ ↔ Core.Valid φ) ∧ (ValidT (.withCallback I) φ ↔ ValidC I φ) :=
  ⟨validT_noCallback, validT_withCallback⟩

/-- A payment true with callbacks is true without: the deterministic run
is a callback run (`valid_of_validC`, from `Prog.exec_run`). -/
example (I : Invariant StandardExample) (a : Core.Fml StandardExample []) (P : Core.Prog StandardExample [] [])
    (H : ValidC I (.imp a (.modal .box P .nil .tt))) (ha : a.hasTransfer = false) :
    Core.Valid (.imp a (.modal .box P .nil .tt)) :=
  valid_of_validC H ha rfl

/-! ## The calculus with callbacks -/

/--
trace: case h.h.exit
⊢ dl{ ∀ uint to ⟹ᶜ[Core.Fml.tt] { net := if(to = this) then net else store(net, at(to), net(to) - 5) } true }

case h.h.ok
⊢ dl{ ∀ uint to, { net := if(to = this) then net else store(net, at(to), net(to) - 5) ‖ ok := true }, { havoc },
    true ⟹ᶜ[Core.Fml.tt] true }

case h.h.failed
⊢ dl{ ∀ uint to, { ok := false } ⟹ᶜ[Core.Fml.tt] true }
-/
#guard_msgs in
example : ProvesC .tt [] .nil cdl!{ [ ok = to.send(5); ] true } := by
  apply ProvesC.allIntro
  apply ProvesC.bindIntro
  apply ProvesC.send .sendWithCallbackBox
  trace_state
  case exit => exact .plain (.updIntro (.updIntro (.closeTrue rfl))) rfl
  all_goals exact .plain (.closeTrue rfl) rfl

/-- The derivation proves the send valid with callbacks, whatever a callee
that keeps the invariant does (`ProvesC.valid`). -/
example : ValidC ⟨.tt, rfl⟩ cdl!{ [ ok = to.send(5); ] true } := by
  apply ProvesC.valid rfl
  apply ProvesC.allIntro
  apply ProvesC.bindIntro
  apply ProvesC.send .sendWithCallbackBox
  case exit => exact .plain (.updIntro (.updIntro (.closeTrue rfl))) rfl
  all_goals exact .plain (.closeTrue rfl) rfl

end Solidity.Examples.Tactics.CoreCallback
