import Solidity.Yul.HorizonAdapter
import Solidity.Yul.Checks.ClosedRun

namespace Solidity.Yul.Checks.Horizons
open Solidity.Yul.Closed
open Solidity.Yul.Checks.ClosedRun
open Solidity.Yul.Checks.ClosedFunctions
open Solidity.Yul.Checks.ClosedPure

/-- Existing S03 firstDone sees this concrete infinite recursion at no bound. -/
theorem diverge_firstDone_none (bound : Nat) :
    Solidity.Source.firstDone
      (fun fuel => sourceResult
        (evalExpr fuel divergeEnv divergeEnvD.profile divergeCall divergeCallD.profile Fin.elim0))
      bound = none :=
  (firstDone_none_iff _).mpr (fun fuel => diverge_all fuel Fin.elim0) bound

example : (Solidity.Source.firstDone
    (fun fuel => sourceResult (evalStmt fuel recursiveEnv recursiveD.profile
      countdownCall countdownCallD.profile (fun _ => word 999))) 18).isNone = true := by decide
example : (Solidity.Source.firstDone
    (fun fuel => sourceResult (evalStmt fuel recursiveEnv recursiveD.profile
      countdownCall countdownCallD.profile (fun _ => word 999))) 19).map
    (fun selected => selected.1) = some 19 := by decide
example : (Solidity.Source.firstDone
    (fun fuel => sourceResult (evalStmt fuel recursiveEnv recursiveD.profile
      countdownCall countdownCallD.profile (fun _ => word 999))) 30).map
    (fun selected => selected.1) = some 19 := by decide

/-- General stability is instantiated on an inhabited recursive environment. -/
theorem countdown_completion_stable {lo hi : Nat} (hle : lo ≤ hi)
    {result : Outcome ⟨false, false⟩ 1}
    (done : evalStmt lo recursiveEnv recursiveD.profile countdownCall
      countdownCallD.profile (fun _ => word 999) = some result) :
    evalStmt hi recursiveEnv recursiveD.profile countdownCall
      countdownCallD.profile (fun _ => word 999) = some result :=
  evalStmt_stable hle recursiveEnv recursiveD.profile countdownCall
    countdownCallD.profile (fun _ => word 999) done

end Solidity.Yul.Checks.Horizons
