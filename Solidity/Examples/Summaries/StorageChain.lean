import Solidity.Examples.Summaries.Support
namespace Solidity.Examples.Summaries.StorageChain
open Solidity.Automation.Summary Solidity.Examples.Summaries.Support
/-- Solidity: three call edges, with each intermediate callee certified once. -/
def Chain : Contract := contract!{
  uint total;
  function seed() { total = 1; }
  function middle() { seed(); }
  function outer() { middle(); }
  function first() { outer(); }
  function twice() { outer(); outer(); }
  function version() pure returns (uint r) { r = 1; }
}
local instance : InContract := ⟨Chain⟩
open scoped Solidity.Scoped
def specification (body : Prog Chain [] []) (m : Modality) : Specification Chain [] [] [] :=
  { body, requires := cdlIn![]{ true }, ensures := cdlIn![old, oldNet]{ total == 1 }, modality := m }
def seedSpec (m : Modality) := specification (summary_body dl!{ [ seed(); ] true }) m
def middleSpec (m : Modality) := specification (summary_body dl!{ [ middle(); ] true }) m
def outerSpec (m : Modality) := specification (summary_body dl!{ [ outer(); ] true }) m
/-- Solidity: `seed()` sets total, for every state and call target. -/
theorem seedCertified (m : Modality) : (seedSpec m).Certified := by
  apply certifyVoid _ .nil ?_ rfl rfl
  cases m <;> (sol_prove; all_goals (sol_leaf; sol_close))
/-- Solidity: `middle()` consumes the one seed certificate. -/
theorem middleCertified (m : Modality) : (middleSpec m).Certified := by
  apply certifyVoid _ .nil ?_ rfl rfl
  cases m <;> summary_calls 1 (seedSpec _) (seedCertified _)
/-- Solidity: `outer()` consumes the one middle certificate. -/
theorem outerCertified (m : Modality) : (outerSpec m).Certified := by
  apply certifyVoid _ .nil ?_ rfl rfl
  cases m <;> summary_calls 1 (middleSpec _) (middleCertified _)
def keyFor (C : Contract) : Key :=
  { leafKey C "outer" "true -> total=1; nonpayable; box and diamond" with
    dependencies := ["middle", "seed"].map (fun f =>
      "true -> total=1; nonpayable; both/" ++ reprStr (Semantics.lookupBy f C.funs)) }
private def checked : CheckedSummary (keyFor Chain) (∀ m, (outerSpec m).Certified) := ⟨outerCertified⟩
/-- Solidity: retrieve the stored `outer` certificate. -/
private theorem cached : ∀ m, (outerSpec m).Certified := checked.fromCache
#guard checked.edits (keyFor (editUnrelated Chain))
  (keyFor (editFunction Chain "seed" (contract!{ function seed() { total = 2; } })))
/-- Solidity: `first()` follows three edges using the cached outer certificate. -/
theorem firstVerified : ⊨ᶠ dl!{ [ first(); ] total == 1 } := by
  summary_calls 1 (outerSpec .box) (cached .box)
/-- Solidity: `twice()` uses that same outer certificate twice. -/
theorem twiceVerified : ⊨ᶠ dl!{ [ twice(); ] total == 1 } := by
  summary_calls 2 (outerSpec .box) (cached .box)
end Solidity.Examples.Summaries.StorageChain
