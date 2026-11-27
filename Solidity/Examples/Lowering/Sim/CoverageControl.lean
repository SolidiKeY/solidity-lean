import Solidity.Correctness.Lowering.Sim.CoverageControl

/-!
Actual-producer execution checks. These executable assertions exercise the
production recursive callbacks, not a fabricated callback record. They are
external evaluation checks, not proofs of kernel totality or loop coverage.
-/
namespace Solidity.Examples.Lowering.Sim.CoverageControl

private def C : Contract := { vars := [] }
private def sc : ElabScope := { funs := [], top := false, unchecked := true }
private def memo : CallMemo := { starts := [("sentinel", 11)] }

/-- `if (true) { require(true); } else { revert(); }`: both nonempty branches
must survive elaboration, with the initial fresh counter and memo preserved. -/
private def conditionalExecution : Bool :=
  match (((elabStmt1 C (.ite (.bool true) [.require (.bool true)] [.revert])).run sc).run
      ([], 17)).run memo with
  | .ok (([⟨[], _, .ite (.simple (.bool true))
      (.cons (.require (.simple (.bool true))) .nil) (.cons .revert .nil)⟩], ([], 17)), m) =>
    m.starts == [("sentinel", 11)] && m.bodies.isEmpty
  | _ => false

#guard conditionalExecution

/-- `loop(false) { require(true); }`: even a false loop condition elaborates
its nonempty body and selects the default `auto` annotation. -/
private def loopExecution : Bool :=
  match (((elabStmt1 C (.loop {} (.bool false) [.require (.bool true)])).run sc).run
      ([], 23)).run memo with
  | .ok (([⟨[], _, .loop .auto (.simple (.bool false))
      (.cons (.require (.simple (.bool true))) .nil)⟩], ([], 23)), m) =>
    m.starts == [("sentinel", 11)] && m.bodies.isEmpty
  | _ => false

#guard loopExecution

open Solidity.Correctness.Lowering.Sim.CoverageControl

/-- A checked use of the conditional helper with concrete child receipts.
Kernel totality is explicit; neither branch receipt is assumed. -/
example (hk : Solidity.Goals.elabKernelTotal) (k : Nat) (m : CallMemo) :
    (((elabStmt1 C (.ite (.bool true) [] [])).run sc).run ([], k)).run m =
      .ok (([.of [] (.ite (.simple (.bool true)) .nil .nil)], ([], k)), m) := by
  apply producer_ite_success C hk (.bool true) [] [] sc
    ([], k) ([], k) ([], k) ([], k) m m m m (.simple (.bool true)) ⟨[], .nil⟩ ⟨[], .nil⟩
  · simp [checkIn, check, checkVia, synth, TExpr.toVal?, ElabM.lift]
    rfl
  · rfl
  · rfl

/-- A checked use of the default-loop helper. Its literal condition receipt
is derived from the kernel's actual hoist equation, rather than assumed. -/
example (hk : Solidity.Goals.elabKernelTotal) (k : Nat) (m : CallMemo) :
    (((elabStmt1 C (.loop {} (.bool false) [])).run sc).run ([], k)).run m =
      .ok (([.of [] (.loop .auto (.simple (.bool false)) .nil)], ([], k)), m) := by
  apply producer_loop_default_success C hk (.bool false) [] sc
    ([], k) ([], k) ([], k) m m m (.simple (.bool false)) ⟨[], .nil⟩
  · obtain ⟨⟨-, -, -, -, -, hhoist⟩, ⟨nhoist, _⟩, _⟩ := hk.1 C
    have hh : hoist C = hoistWith C (elabRec C ()) := nhoist ▸ hhoist
    rw [loopExpr, loopExprWith, hh]
    change (((checkIn C [] .bool (.bool false)).run sc).run ([], k)).run m = _
    simp [checkIn, check, checkVia, synth, TExpr.toVal?, ElabM.lift]
    rfl
  · rfl

end Solidity.Examples.Lowering.Sim.CoverageControl
