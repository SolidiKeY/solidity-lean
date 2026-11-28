import Solidity.Calculus.Closers
import Solidity.Automation.SummaryCache

/-!
# Recursion-free library-style contract with shared value summaries

The symbolic-call rule summarizes value computations. The verdict cache below
is a separate, explicitly encoded consumer: it does not claim that the current
front end extracts canonical keys or consumes `Specification.Certified`.
-/
namespace Solidity.Examples.Summaries.Library
open Solidity.Automation.Summary

def Library : Contract := contract!{
  function increment(uint x) pure returns (uint r) { r = x + 1; }
  function left(uint x) pure returns (uint r) { r = increment(increment(x)); }
  function right(uint x) pure returns (uint r) { r = increment(increment(x)); }
  function version() pure returns (uint r) { r = 1; }
}
local instance : InContract := ⟨Library⟩
open scoped Solidity.Scoped

/-- `increment(4)` computes the checked result. This is the callee verdict saved below. -/
def calleeGoal : Fml Library [] := dl!{ [ uint y = increment(4); ] y == 5 }

/-- Solidity: `function increment(uint x) { return x + 1; }`. -/
theorem incrementVerified : Fml.Valid calleeGoal := by
  unfold calleeGoal
  sol_prove

/-- Solidity: `left(4)` reuses the symbolic summary of `increment`. -/
theorem leftVerified : ⊨ᶠ dl!{ [ uint y = left(4); ] y == 6 } := by
  sol_prove

/-- Solidity: `right(4)` uses the same helper body at another call site. -/
theorem rightVerified : ⊨ᶠ dl!{ [ uint y = right(4); ] y == 6 } := by
  sol_prove

/-- The helper has no calls; all other semantic metadata is retained in context.
`reprStr` is only a fixture encoding, not a canonical serialization theorem. -/
def keyFor (C : Contract) : Key :=
  ⟨reprStr (Semantics.lookupBy "increment" C.funs), "[uint y = increment(4);] y == 5",
    reprStr { C with funs := [] }, []⟩
def key : Key := keyFor Library

private def unrelatedEdit : Contract := { Library with
  funs := Library.funs.map (fun (n, f) => if n == "version" then
    (n, (contract!{ function version() pure returns (uint r) { r = 2; } }).funs.head!.2)
    else (n, f)) }
private def calleeEdit : Contract := { Library with
  funs := Library.funs.map (fun (n, f) => if n == "increment" then
    (n, (contract!{ function increment(uint x) pure returns (uint r) { r = x + 2; } }).funs.head!.2) else (n, f)) }

private def valid (k : Key) : Prop := k = key ∧ Fml.Valid calleeGoal
private def verdict : Verdict valid key := .proved ⟨rfl, incrementVerified⟩
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

end Solidity.Examples.Summaries.Library
