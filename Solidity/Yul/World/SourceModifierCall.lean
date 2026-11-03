import Solidity.Yul.World.SourceModifierBoundary

/-! Actual ordinary invocation of the selected modifier/placeholder input.
This is not frontend, deployment, physical or universal-callee adequacy. -/
namespace Solidity.Yul.World.SourceModifierCall
open Solidity.Source
open Solidity.Yul.World.SourceModifierBoundary

/-- Real virtual lookup, empty return-frame initialization and modifier execution.
The resulting halt is derived from the concrete registered body. -/
theorem actual {failed} (G : Glob (env failed)) (F : Fr) (s : EMState (env failed) [])
    (code : F.contract="Guarded") :
    (Source.callInternal (glob G) F 8 functionDecl .nil []).run s=
      ((if failed then .error (.revert (data G)) else .ok (Source.mkRet [] .nil)),s) := by
  cases F with
  | mk owner sender amount static contract checked depth cd =>
    change contract="Guarded" at code
    subst contract
    cases failed <;> cases G with
    | mk program pipeline fixed balance hasCode strategy timestamp => cases pipeline <;> rfl

/-- Actual entered modifier exhaustion propagated by ordinary callInternal. -/
theorem entered_timeout {failed} (G : Glob (env failed)) (F : Fr) (s : EMState (env failed) [])
    (code : F.contract="Guarded") :
    (Source.callInternal (glob G) F 5 functionDecl .nil []).run s=
      (.error .timeout,s) := by
  cases F with
  | mk owner sender amount static contract checked depth cd =>
    change contract="Guarded" at code
    subst contract
    cases failed <;> cases G with
    | mk program pipeline fixed balance hasCode strategy timestamp => cases pipeline <;> rfl

end Solidity.Yul.World.SourceModifierCall
