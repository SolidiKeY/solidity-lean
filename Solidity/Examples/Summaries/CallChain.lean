import Solidity.Calculus.Closers
import Solidity.Automation.SummaryCache

/-!
# CallChain with shared value summaries

The symbolic-call rule summarizes value computations. The verdict cache below
is a separate, explicitly encoded consumer: it does not claim that the current
front end extracts canonical keys or consumes `Specification.Certified`.
-/
namespace Solidity.Examples.Summaries.CallChain
open Solidity.Automation.Summary

def CallChain : Contract := contract!{
  function seed(uint x) pure returns (uint r) { r = x + 1; }
  function middle(uint x) pure returns (uint r) { r = seed(x); }
  function outer(uint x) pure returns (uint r) { r = middle(x); }
  function first(uint x) pure returns (uint r) { r = outer(x); }
  function twice(uint x) pure returns (uint r) { r = middle(middle(x)); }
  function version() pure returns (uint r) { r = 1; }
}
local instance : InContract := ⟨CallChain⟩
open scoped Solidity.Scoped

/-- `seed(2)` computes the checked result. This is the callee verdict saved below. -/
def calleeGoal : Fml CallChain [] := dl!{ [ uint y = seed(2); ] y == 3 }

/-- Solidity: `function seed(uint x) { return x + 1; }`. -/
theorem seedVerified : Fml.Valid calleeGoal := by
  unfold calleeGoal
  sol_prove

/-- Solidity: `first(2)` reuses the symbolic summary of `seed`. -/
theorem firstVerified : ⊨ᶠ dl!{ [ uint y = first(2); ] y == 3 } := by
  sol_prove

/-- Solidity: `middle(2)` uses the same helper body at another call site. -/
theorem middleVerified : ⊨ᶠ dl!{ [ uint y = middle(2); ] y == 3 } := by
  sol_prove

/-- Solidity: `twice(2)` calls the same intermediate helper twice. -/
theorem twiceVerified : ⊨ᶠ dl!{ [ uint y = twice(2); ] y == 4 } := by
  sol_prove

/-- The helper has no calls; all other semantic metadata is retained in context.
`reprStr` is only a fixture encoding, not a canonical serialization theorem. -/
def keyFor (C : Contract) : Key :=
  ⟨reprStr (Semantics.lookupBy "seed" C.funs), "[uint y = seed(2);] y == 3",
    reprStr { C with funs := [] }, []⟩
def key : Key := keyFor CallChain

private def unrelatedEdit : Contract := { CallChain with
  funs := CallChain.funs.map (fun (n, f) => if n == "version" then
    (n, (contract!{ function version() pure returns (uint r) { r = 2; } }).funs.head!.2)
    else (n, f)) }
private def calleeEdit : Contract := { CallChain with
  funs := CallChain.funs.map (fun (n, f) => if n == "seed" then
    (n, (contract!{ function seed(uint x) pure returns (uint r) { r = x + 2; } }).funs.head!.2) else (n, f)) }

private def valid (k : Key) : Prop := k = key ∧ Fml.Valid calleeGoal
private def verdict : Verdict valid key := .proved ⟨rfl, seedVerified⟩
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

end Solidity.Examples.Summaries.CallChain
