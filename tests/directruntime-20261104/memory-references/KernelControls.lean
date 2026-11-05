import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-! Kernel development controls only; these do not establish compiler transport,
source equivalence or native/browser acceptance. No ordinary request imports this
file or constructs a Lean environment. The existing calculus and run are reused. -/
namespace Solidity.Frontend.ExecutableAst.Memory.KernelControls
def EmptyContract : Contract := { vars := [] }
local instance : InContract := ⟨EmptyContract⟩

theorem identityDiamond :
    ⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); m[0] = 1; assert(m[0] == 1); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove

theorem identityBox :
    ⊨ᶠ dl!{ [ int[] memory m = new int[](1); m[0] = 1; assert(m[0] == 1); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove

theorem defaultDiamond :
    ⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); assert(m[0] == 0); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove

theorem aliasDiamond :
    ⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); int[] memory a = m;
      a[0] = 1; assert(m[0] == 1); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove

theorem distinctDiamond :
    ⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); int[] memory a = new int[](1);
      a[0] = 1; assert(m[0] == 0); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove

theorem falseBox :
    ¬ (⊨ᶠ dl!{ [ int[] memory m = new int[](1); m[0] = 1; assert(m[0] == 2); ] true }) :=
  fun h => Modality.afterRunTR_not_panic (h (State.init _)) (by decide +kernel)

theorem falseDiamond :
    ¬ (⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); m[0] = 1; assert(m[0] == 2); ⟩ true }) :=
  fun h => Modality.afterRunTR_not_panic (h (State.init _)) (by decide +kernel)

theorem aliasIsNotCopy :
    ¬ (⊨ᶠ dl!{ [ int[] memory m = new int[](1); int[] memory a = m;
      a[0] = 1; assert(m[0] == 0); ] true }) :=
  fun h => Modality.afterRunTR_not_panic (h (State.init _)) (by decide +kernel)

theorem zeroBox :
    ⊨ᶠ dl!{ [ int[] memory m = new int[](0); assert(m[0] == 0); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove

theorem zeroDiamond :
    ¬ (⊨ᶠ dl!{ ⟨ int[] memory m = new int[](0); assert(m[0] == 0); ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)

theorem oobBox :
    ⊨ᶠ dl!{ [ int[] memory m = new int[](1); m[1] = 1; assert(false); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove

theorem oobDiamond :
    ¬ (⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); m[1] = 1; assert(false); ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)

#print axioms identityDiamond
#print axioms identityBox
#print axioms defaultDiamond
#print axioms aliasDiamond
#print axioms distinctDiamond
#print axioms falseBox
#print axioms falseDiamond
#print axioms aliasIsNotCopy
#print axioms zeroBox
#print axioms zeroDiamond
#print axioms oobBox
#print axioms oobDiamond
end Solidity.Frontend.ExecutableAst.Memory.KernelControls
