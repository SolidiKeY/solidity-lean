import Solidity.Calculus.Closers

/-! # Default call sharing through the closer-only import
The walk still uses the existing internalCallSummary rule. No Tools import
or explicit sharing command is needed for the default entry points.
-/
namespace Solidity.Examples.Tactics.CallSharingDefault
private def Affine : Contract := contract!{
  function f0(uint x) returns (uint r) { r = x * 3 + 1; }
  function f1(uint x) returns (uint r) { r = f0(f0(x)); }
  function f2(uint x) returns (uint r) { r = f1(f1(x)); }
  function f3(uint x) returns (uint r) { r = f2(f2(x)); }
  function f4(uint x) returns (uint r) { r = f3(f3(x)); }
  function f5(uint x) returns (uint r) { r = f4(f4(x)); }
  function f6(uint x) returns (uint r) { r = f5(f5(x)); }
  function f7(uint x) returns (uint r) { r = f6(f6(x)); }
}
local instance : InContract := ⟨Affine⟩
open scoped Solidity.Scoped

/-- An actual formerly open non-offset leaf closes through sol_close. -/
theorem defaultSix : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f6(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

theorem defaultSeven : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f7(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

/-- Already named semantic leaves are consumed without another emission. -/
theorem alreadyShared : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f6(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_share_calls
  sol_close

/-- Both successful and failing executions keep the box observation. -/
theorem defaultBox : ⊨ᶠ dl!{ [ uint y = f6(a); ] y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

/-- A conditional prefix composes with checked call sharing; both updates
retain their original checked evaluation before the call is consumed. -/
theorem joinedCall : ⊨ᶠ dl!{ a < 997 → ⟨ uint x = a;
    if (c == 1) { x = x + 1; } else { x = x + 2; };
    uint y = f6(x); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close
end Solidity.Examples.Tactics.CallSharingDefault
