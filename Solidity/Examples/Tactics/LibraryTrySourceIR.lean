import Solidity.Examples.Tactics.LibraryTrySource

/-! Separately compiled via-IR original library source, unchanged runtime
settings and observations. Compiled EVM correspondence is separately replayed. -/
namespace Solidity.Examples.Tactics.LibraryTrySourceIR
open ContractWorld Semantics
open Solidity.Examples.Tactics.LibraryTrySource
solc_library_try "../../../tests/solc/LibraryTryIR.ast.json" hash 0xce73e5f0cfa5a668
  from_contract "C" as OriginalIR

def initialIR := World.empty OriginalIR.contracts initial.funds OriginalIR.roles

def orderedIR : TRes (List Nat × List Nat × List Nat × List Nat) := do
  let (w,linked) ← OriginalIR.deployLibrary initialIR libraryAddress { sender }
  let (w,self) ← OriginalIR.deployCaller w callerAddress { sender }
  let (w,a) ← OriginalIR.m0.run w self { sender } linked.address true
  let (w,b) ← OriginalIR.m0.run w self { sender } linked.address false
  let (w,c) ← OriginalIR.m1.run w self { sender } linked.address true
  let (_,d) ← OriginalIR.m1.run w self { sender } linked.address false
  pure (a,b,c,d)

/-- Every original ordered IR output comes from the actual typed source run. -/
theorem original_outputs_ir : orderedIR.toOption = some
    (expected 8 [], expected 18 [102,97,105,108,117,114,101],
     expected 9 [], expected 19 [102,97,105,108,117,114,101]) := by decide +kernel

end Solidity.Examples.Tactics.LibraryTrySourceIR
