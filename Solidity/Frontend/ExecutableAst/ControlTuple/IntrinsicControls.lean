import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.ProvesDerive

/-! Intrinsic model controls for the lowering reused by the adapter. These do not
claim compiler/source equivalence or producer registration. -/
namespace Solidity.Frontend.ExecutableAst.ControlTuple.IntrinsicControls
open Semantics
open scoped Scoped
local instance : InContract := ⟨StandardExample⟩

theorem doOnceDiamond : ⊨ᶠ dl!{ ⟨ uint i = 0;
    /// @custom:key unwind 1
    do { i = i + 1; } while (false); assert(i == 1); ⟩ true } := by
  sol_symex
  sol_close

theorem whileZeroBox : ⊨ᶠ dl!{ [ uint i = 0;
    /// @custom:key unwind 1
    while (false) { i = i + 1; }; assert(i == 0); ] true } := by
  sol_symex
  sol_close

theorem continueTestsCondition : ⊨ᶠ dl!{ ⟨ uint i = 0;
    /// @custom:key unwind 2
    do { i = i + 1; continue; } while (i < 2); assert(i == 2); ⟩ true } := by
  sol_symex
  sol_close

theorem breakStopsLoop : ⊨ᶠ dl!{ ⟨ uint i = 0;
    /// @custom:key unwind 1
    do { i = i + 1; break; } while (true); assert(i == 1); ⟩ true } := by
  sol_symex
  sol_close

theorem simultaneousSwap : ⊨ᶠ dl!{ ⟨ uint a = 1; uint b = 2;
    (a, b) = (b, a); assert(a == 2); assert(b == 1); ⟩ true } := by
  sol_symex
  sol_close

theorem repeatedPrimitiveWrites : ⊨ᶠ dl!{ ⟨ uint a = 0;
    (a, a) = (1, 2); assert(a == 1); ⟩ true } := by
  sol_symex
  sol_close

theorem holePreservesPosition : ⊨ᶠ dl!{ ⟨ uint a = 0;
    (, a) = (9, 5); assert(a == 5); ⟩ true } := by
  sol_symex
  sol_close

theorem tupleDeclaration : ⊨ᶠ dl!{ ⟨
    (uint a, , bool b) = (3, 4, true); assert(a == 3); assert(b); ⟩ true } := by
  sol_symex
  sol_close

theorem discardedEffectRetained : ⊨ᶠ dl!{ ⟨ uint a = 0; uint b = 0;
    (, b) = (a++, a); assert(a == 1); assert(b == 1); ⟩ true } := by
  sol_symex
  sol_close

theorem discardedFailureBox : ⊨ᶠ dl!{ [ uint a = 0;
    (, a) = (8 / 0, 2); ] false } := by
  sol_symex
  sol_close

theorem discardedFailureNotDiamond : ¬ (⊨ᶠ dl!{ ⟨ uint a = 0;
    (, a) = (8 / 0, 2); ⟩ true }) := fun h => Modality.afterRunTR_diamond_fail
  (h (State.init _)) (by decide +kernel)

theorem wrongSwapBoxRefuted : ¬ (⊨ᶠ dl!{ [ uint a = 1; uint b = 2;
    (a, b) = (b, a); assert(a == 1); ] true }) := fun h => Modality.afterRunTR_not_panic
  (h (State.init _)) (by decide +kernel)

def Returns : Contract := contract!{
  function early() returns (uint r) {
    /// @custom:key unwind 1
    do { return 7; } while (true);
    r = 9;
  }
  function pair() returns (uint a, uint b) { return (3, 4); }
}

theorem earlyReturnEscapes : ⊨ᶠ dl[Returns]{ ⟨ uint a = early(); ⟩ a == 7 } := by
  sol_symex
  sol_close

theorem tupleReturn : ⊨ᶠ dl[Returns]{ ⟨ uint a; uint b;
    (a, b) = pair(); ⟩ a == 3 && b == 4 } := by
  sol_symex
  sol_close

end Solidity.Frontend.ExecutableAst.ControlTuple.IntrinsicControls
