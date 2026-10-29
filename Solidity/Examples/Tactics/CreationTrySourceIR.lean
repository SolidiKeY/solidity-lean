import Solidity.Examples.Tactics.CreationTrySource

/-! The same complete original source under its separately compiled viaIR
settings; no changed fixture observations, constructor bytes or model profile. -/
namespace Solidity.Examples.Tactics.CreationTrySourceIR
open Solidity.Frontend.CreationTry Solidity.ContractWorld Semantics
open Solidity.Examples.Tactics.CreationTrySource
solc_creation_try "../../../tests/solc/CreationTryIR.ast.json" hash 0x344c89cf834dcc10
  from_contract "C" as OriginalIR

def initialIR := World.empty OriginalIR.contracts initial.funds

def bothIR : TRes (List Nat × List Nat) := do
  let (w, self) ← OriginalIR.deploy initialIR factory { sender }
  let (w, caught) ← OriginalIR.run w self { sender } first "f()"
  let (_, succeeded) ← OriginalIR.run w self { sender } second "g()"
  pure (caught, succeeded)

/-- Actual success/caught outputs in both ordered original IR observations. -/
theorem original_outputs_ir : bothIR.toOption = some
    (expected 0 [116,101,115,116,32,109,101,115,115,97,103,101,46],
     expected 1 [115,117,99,99,101,115,115]) := by decide +kernel

end Solidity.Examples.Tactics.CreationTrySourceIR
