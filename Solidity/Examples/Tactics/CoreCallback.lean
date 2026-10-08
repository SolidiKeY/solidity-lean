import Solidity.Semantics.Core.Callback
import Solidity.Calculus.Core.Callback
import Solidity.Calculus.Core.Notation

/-!
# The callback reading on typed runs

`Semantics/Core/Callback.lean` used: a program that pays has, among its
callback runs, the deterministic one, unless the invariant breaks on the way
(`Prog.exec_run`); a program that pays nothing has only the deterministic
one, so a fact of every callback run is decided by running it
(`ExecP.forall_iff`).

The calculus with callbacks (`ProvesC`, `Calculus/Core/Callback.lean`) on a
send: solkey's three goals of `sendWithCallbackBox`, each closed in the
plain calculus, the invariant `true`.
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

/-! ## The calculus with callbacks -/

local instance : InContract := ⟨StandardExample⟩

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

end Solidity.Examples.Tactics.CoreCallback
