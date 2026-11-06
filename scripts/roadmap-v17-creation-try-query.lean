import Lean
import Solidity.Examples.Tactics.CreationTrySourceIR
-- V17_CREATION_BODY
/-! Above-core observation only; all programs, worlds and replay are published. -/
open Lean Lean.Meta Lean.Elab
namespace Solidity.Roadmap.V17.CreationTry
open Solidity Solidity.ContractWorld
open Solidity.Examples.Tactics.CreationTrySource
open Solidity.Examples.Tactics.CreationTrySourceIR

/-- Obtain the exact expected option from the checked producer statement.
No locally reconstructed byte oracle or new source semantics. -/
elab "v17Expected% " n:ident : term => do
  let name ← resolveGlobalConstNoOverload n
  let info ← getConstInfo name
  unless info.type.isAppOfArity ``Eq 3 do throwError "expected a published equality"
  pure info.type.getAppArgs[2]!

def expectedLegacy : Option (List Nat × List Nat) := v17Expected% original_outputs
def expectedIR : Option (List Nat × List Nat) := v17Expected% original_outputs_ir

def job : Json := Json.mkObj [("hostContext", host), ("vectors", toJson [
  vector "f()" ((expectedLegacy.getD ([], [])).1),
  vector "g()" ((expectedLegacy.getD ([], [])).2)])]

def outcome : Json := match collision with
  | .ok bytes => Json.mkObj [("kind", toJson "return"), ("bytes", toJson bytes)]
  | .error .revert => Json.mkObj [("kind", toJson "bare-revert"), ("bytes", toJson ([] : List Nat))]
  | .error _ => Json.mkObj [("kind", toJson "other-error")]

#eval IO.println ("V17_CREATION_BEGIN\n" ++ (Json.mkObj [
  ("schema", toJson (1 : Nat)),
  ("orderedSignatures", toJson ["f()", "g()"]),
  ("legacy", toJson both.toOption), ("ordinary", toJson bothOrdinary.toOption),
  ("viaIR", toJson bothIR.toOption),
  ("expectedLegacy", toJson expectedLegacy), ("expectedIR", toJson expectedIR),
  ("collision", outcome), ("installations", toJson installations.toOption),
  ("arguments", toJson argumentValues.toOption), ("hostContext", host),
  ("first", toJson (toString first.1.1)), ("second", toJson (toString second.1.1)),
  ("nativeLegacy", Tools.CreationTryReplay.replay Original.contracts Original.deploy Original.run job),
  ("nativeIR", Tools.CreationTryReplay.replay OriginalIR.contracts OriginalIR.deploy OriginalIR.run job),
  ("semanticPremisesDischarged", toJson false), ("releaseClosed", toJson false)]).compress ++ "\nV17_CREATION_END")
end Solidity.Roadmap.V17.CreationTry
