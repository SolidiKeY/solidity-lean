import Solidity.Calculus.Closers
import Solidity.Automation.SummaryCache

/-!
# Pricing arithmetic through a shared math helper

The symbolic-call rule summarizes value computations. The verdict cache below
is a separate, explicitly encoded consumer: it does not claim that the current
front end extracts canonical keys or consumes `Specification.Certified`.
-/
namespace Solidity.Examples.Summaries.Pricing
open Solidity.Automation.Summary

def Pricing : Contract := contract!{
  function quote(uint units) pure returns (uint r) { r = units + 7; }
  function buy(uint units) pure returns (uint r) { r = quote(units); }
  function estimate(uint units) pure returns (uint r) { r = quote(units); }
  function version() pure returns (uint r) { r = 1; }
}
local instance : InContract := ⟨Pricing⟩
open scoped Solidity.Scoped

/-- The helper returns its specified result for every input below 1000. -/
def calleeGoal : Fml Pricing [] := dl!{ a < 1000 → ⟨ uint y = quote(a); ⟩ y == a + 7 }

/-- Solidity: `function quote(uint units) { return units + 7; }`. -/
theorem quoteVerified : Fml.Valid calleeGoal := by
  unfold calleeGoal
  sol_prove

/-- Solidity: `buy(4)` reuses the symbolic summary of `quote`. -/
theorem buyVerified : ⊨ᶠ dl!{ [ uint y = buy(4); ] y == 11 } := by
  sol_prove

/-- Solidity: `estimate(4)` uses the same helper body at another call site. -/
theorem estimateVerified : ⊨ᶠ dl!{ [ uint y = estimate(4); ] y == 11 } := by
  sol_prove

/-- The helper has no calls; all other semantic metadata is retained in context.
`reprStr` is only a fixture encoding, not a canonical serialization theorem. -/
def keyFor (C : Contract) : Key :=
  ⟨reprStr (Semantics.lookupBy "quote" C.funs), "a < 1000 -> <uint y = quote(a);> y == a + 7",
    reprStr { C with funs := [] }, []⟩
def key : Key := keyFor Pricing

private def unrelatedEdit : Contract := { Pricing with
  funs := Pricing.funs.map (fun (n, f) => if n == "version" then
    (n, (contract!{ function version() pure returns (uint r) { r = 2; } }).funs.head!.2)
    else (n, f)) }
private def calleeEdit : Contract := { Pricing with
  funs := Pricing.funs.map (fun (n, f) => if n == "quote" then
    (n, (contract!{ function quote(uint units) pure returns (uint r) { r = units + 8; } }).funs.head!.2) else (n, f)) }

private def valid (k : Key) : Prop := k = key ∧ Fml.Valid calleeGoal
private def verdict : Verdict valid key := .proved ⟨rfl, quoteVerified⟩
private def saved : Cache valid := ({} : Cache valid).insert key verdict

/-- Reusing the saved helper verdict invokes no checker. -/
theorem cachedVerdictReused (verify : (k : Key) → Option (Verdict valid k)) :
    saved.check key verify = (some verdict, saved, false) :=
  Cache.check_hit _ _ _ _ (Cache.lookup_insert _ _ _)

-- Real source fixtures: change the unrelated declaration, then the helper body.
#guard keyFor unrelatedEdit == key
#guard (saved.lookup (keyFor unrelatedEdit)).isSome
#guard (saved.check (keyFor unrelatedEdit) (fun _ => none)).2.2 == false
#guard (saved.lookup (keyFor calleeEdit)).isNone
#guard (saved.check (keyFor calleeEdit) (fun _ => none)).2.2 == true

end Solidity.Examples.Summaries.Pricing
