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

end Solidity.Examples.Lowering.Sim.CoverageControl
