import Solidity.Semantics.Core.Callback

/-!
# The callback reading on typed runs

`Semantics/Core/Callback.lean` used: a program that pays has, among its
callback runs, the deterministic one, unless the invariant breaks on the way
(`Prog.exec_run`); a program that pays nothing has only the deterministic
one, so a fact of every callback run is decided by running it
(`ExecP.forall_iff`).
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

end Solidity.Examples.Tactics.CoreCallback
