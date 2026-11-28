import Solidity.Calculus.Closers
import Solidity.Automation.SummaryCache

/-!
# Vault arithmetic through a shared math helper

The symbolic-call rule summarizes value computations. The verdict cache below
is a separate, explicitly encoded consumer: it does not claim that the current
front end extracts canonical keys or consumes `Specification.Certified`.
-/
namespace Solidity.Examples.Summaries.Vault
open Solidity.Automation.Summary

def Vault : Contract := contract!{
  function shares(uint assets) pure returns (uint r) { r = assets * 2; }
  function deposit(uint assets) pure returns (uint r) { r = shares(assets); }
  function preview(uint assets) pure returns (uint r) { r = shares(assets); }
  function version() pure returns (uint r) { r = 1; }
}
local instance : InContract := ⟨Vault⟩
open scoped Solidity.Scoped

/-- The helper returns its specified result for every input below 1000. -/
def calleeGoal : Fml Vault [] := dl!{ a < 1000 → ⟨ uint y = shares(a); ⟩ y == a + a }

/-- Solidity: `function shares(uint assets) { return assets * 2; }`. -/
theorem sharesVerified : Fml.Valid calleeGoal := by
  unfold calleeGoal
  sol_prove
  sol_leaf
  sol_close

/-- Solidity: `deposit(4)` reuses the symbolic summary of `shares`. -/
theorem depositVerified : ⊨ᶠ dl!{ [ uint y = deposit(4); ] y == 8 } := by
  sol_prove

/-- Solidity: `preview(4)` uses the same helper body at another call site. -/
theorem previewVerified : ⊨ᶠ dl!{ [ uint y = preview(4); ] y == 8 } := by
  sol_prove

/-- The helper has no calls; all other semantic metadata is retained in context.
`reprStr` is only a fixture encoding, not a canonical serialization theorem. -/
def keyFor (C : Contract) : Key :=
  ⟨reprStr (Semantics.lookupBy "shares" C.funs), "a < 1000 -> <uint y = shares(a);> y == a + a",
    reprStr { C with funs := [] }, []⟩
def key : Key := keyFor Vault

private def unrelatedEdit : Contract := { Vault with
  funs := Vault.funs.map (fun (n, f) => if n == "version" then
    (n, (contract!{ function version() pure returns (uint r) { r = 2; } }).funs.head!.2)
    else (n, f)) }
private def calleeEdit : Contract := { Vault with
  funs := Vault.funs.map (fun (n, f) => if n == "shares" then
    (n, (contract!{ function shares(uint assets) pure returns (uint r) { r = assets * 3; } }).funs.head!.2) else (n, f)) }

private def valid (k : Key) : Prop := k = key ∧ Fml.Valid calleeGoal
private def verdict : Verdict valid key := .proved ⟨rfl, sharesVerified⟩
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

end Solidity.Examples.Summaries.Vault
