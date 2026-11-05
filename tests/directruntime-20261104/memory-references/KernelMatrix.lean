import KernelControls
/-! Exact fixture bodies in the existing intrinsic calculus. These kernel
controls are development validation, not native/browser source acceptance. -/
namespace Solidity.Frontend.ExecutableAst.Memory.KernelMatrix
def StoredContract : Contract := { vars := [("stored", .array (.prim .int))] }
def MappingContract : Contract := { vars := [("unused", .mapping .uint (.prim .int))] }

namespace identity_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ int[] memory m = new int[](1); m[0] = 1; assert(m[0] == 1); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end identity_box

namespace identity_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); m[0] = 1; assert(m[0] == 1); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end identity_diamond

namespace false_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ¬ (⊨ᶠ dl!{ [ int[] memory m = new int[](1); m[0] = 1; assert(m[0] == 2); ] true }) :=
  fun h => Modality.afterRunTR_not_panic (h (State.init _)) (by decide +kernel)
#print axioms checked
end false_box

namespace false_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ¬ (⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); m[0] = 1; assert(m[0] == 2); ⟩ true }) :=
  fun h => Modality.afterRunTR_not_panic (h (State.init _)) (by decide +kernel)
#print axioms checked
end false_diamond

namespace default_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ int[] memory m = new int[](1); assert(m[0] == 0); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end default_box

namespace default_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); assert(m[0] == 0); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end default_diamond

namespace alias_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ int[] memory m = new int[](1); int[] memory a = m; a[0] = -1; assert(m[0] == -1); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end alias_box

namespace alias_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); int[] memory a = m; a[0] = -1; assert(m[0] == -1); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end alias_diamond

namespace aliasIsNotCopy_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ¬ (⊨ᶠ dl!{ [ int[] memory m = new int[](1); int[] memory a = m; a[0] = 1; assert(m[0] == 0); ] true }) :=
  fun h => Modality.afterRunTR_not_panic (h (State.init _)) (by decide +kernel)
#print axioms checked
end aliasIsNotCopy_box

namespace aliasIsNotCopy_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ¬ (⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); int[] memory a = m; a[0] = 1; assert(m[0] == 0); ⟩ true }) :=
  fun h => Modality.afterRunTR_not_panic (h (State.init _)) (by decide +kernel)
#print axioms checked
end aliasIsNotCopy_diamond

namespace distinctAllocations_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ int[] memory m = new int[](1); int[] memory a = new int[](1); a[0] = 1; assert(m[0] == 0); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end distinctAllocations_box

namespace distinctAllocations_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); int[] memory a = new int[](1); a[0] = 1; assert(m[0] == 0); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end distinctAllocations_diamond

namespace zeroRead_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ int[] memory m = new int[](0); assert(m[0] == 0); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end zeroRead_box

namespace zeroRead_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ¬ (⊨ᶠ dl!{ ⟨ int[] memory m = new int[](0); assert(m[0] == 0); ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)
#print axioms checked
end zeroRead_diamond

namespace zeroWrite_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ int[] memory m = new int[](0); m[0] = 1; assert(false); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end zeroWrite_box

namespace zeroWrite_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ¬ (⊨ᶠ dl!{ ⟨ int[] memory m = new int[](0); m[0] = 1; assert(false); ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)
#print axioms checked
end zeroWrite_diamond

namespace oobRead_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ int[] memory m = new int[](1); assert(m[1] == 0); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end oobRead_box

namespace oobRead_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ¬ (⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); assert(m[1] == 0); ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)
#print axioms checked
end oobRead_diamond

namespace oobWrite_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ int[] memory m = new int[](1); m[1] = 1; assert(false); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end oobWrite_box

namespace oobWrite_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ¬ (⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); m[1] = 1; assert(false); ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)
#print axioms checked
end oobWrite_diamond

namespace emptySuccess_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ int[] memory m = new int[](0); assert(m.length == 0); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end emptySuccess_box

namespace emptySuccess_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ ⟨ int[] memory m = new int[](0); assert(m.length == 0); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end emptySuccess_diamond

namespace uintIdentity_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ uint[] memory m = new uint[](1); m[0] = 1; assert(m[0] == 1); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end uintIdentity_box

namespace uintIdentity_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ ⟨ uint[] memory m = new uint[](1); m[0] = 1; assert(m[0] == 1); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end uintIdentity_diamond

namespace boolDefault_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ bool[] memory m = new bool[](1); assert(!m[0]); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end boolDefault_box

namespace boolDefault_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ ⟨ bool[] memory m = new bool[](1); assert(!m[0]); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end boolDefault_diamond

namespace boolAlias_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ bool[] memory m = new bool[](1); bool[] memory a = m; a[0] = true; assert(m[0]); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end boolAlias_box

namespace boolAlias_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ ⟨ bool[] memory m = new bool[](1); bool[] memory a = m; a[0] = true; assert(m[0]); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end boolAlias_diamond

namespace fixedDefault_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ int[1] memory m; assert(m[0] == 0); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end fixedDefault_box

namespace fixedDefault_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ ⟨ int[1] memory m; assert(m[0] == 0); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end fixedDefault_diamond

namespace fixedAlias_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ int[1] memory m; int[1] memory a = m; a[0] = 1; assert(m[0] == 1); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end fixedAlias_box

namespace fixedAlias_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ ⟨ int[1] memory m; int[1] memory a = m; a[0] = 1; assert(m[0] == 1); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end fixedAlias_diamond

namespace referenceAlias_box
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ [ int[][] memory m = new int[][](1); m[0] = new int[](1); int[] memory a = m[0]; a[0] = 1; assert(m[0][0] == 1); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end referenceAlias_box

namespace referenceAlias_diamond
local instance : InContract := ⟨KernelControls.EmptyContract⟩
theorem checked : ⊨ᶠ dl!{ ⟨ int[][] memory m = new int[][](1); m[0] = new int[](1); int[] memory a = m[0]; a[0] = 1; assert(m[0][0] == 1); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end referenceAlias_diamond

namespace mappingRoot_box
local instance : InContract := ⟨MappingContract⟩
theorem checked : ⊨ᶠ dl!{ [ int[] memory m = new int[](1); m[0] = 1; assert(m[0] == 1); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end mappingRoot_box

namespace mappingRoot_diamond
local instance : InContract := ⟨MappingContract⟩
theorem checked : ⊨ᶠ dl!{ ⟨ int[] memory m = new int[](1); m[0] = 1; assert(m[0] == 1); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end mappingRoot_diamond

namespace storageAlias_box
local instance : InContract := ⟨StoredContract⟩
theorem checked : ⊨ᶠ dl!{ [ int[] storage a = stored; a[0] = 1; assert(stored[0] == 1); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end storageAlias_box

namespace storageAlias_diamond
local instance : InContract := ⟨StoredContract⟩
theorem checked : ¬ (⊨ᶠ dl!{ ⟨ int[] storage a = stored; a[0] = 1; assert(stored[0] == 1); ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)
#print axioms checked
end storageAlias_diamond

namespace copyAfterPush_box
local instance : InContract := ⟨StoredContract⟩
theorem checked : ⊨ᶠ dl!{ [ stored.push(0); uint i = stored.length - 1; int[] memory m = stored; m[i] = 1; assert(stored[i] == 0); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end copyAfterPush_box

namespace copyAfterPush_diamond
local instance : InContract := ⟨StoredContract⟩
theorem checked : ⊨ᶠ dl!{ ⟨ stored.push(0); uint i = stored.length - 1; int[] memory m = stored; m[i] = 1; assert(stored[i] == 0); ⟩ true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end copyAfterPush_diamond

namespace storageCopy_box
local instance : InContract := ⟨StoredContract⟩
theorem checked : ⊨ᶠ dl!{ [ require(stored.length == 1); require(stored[0] == 0); int[] memory m = stored; m[0] = 1; assert(stored[0] == 0); ] true } := by
  apply Proves.fmlValid (R := .all)
  sol_prove
#print axioms checked
end storageCopy_box

namespace storageCopy_diamond
local instance : InContract := ⟨StoredContract⟩
theorem checked : ¬ (⊨ᶠ dl!{ ⟨ require(stored.length == 1); require(stored[0] == 0); int[] memory m = stored; m[0] = 1; assert(stored[0] == 0); ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)
#print axioms checked
end storageCopy_diamond
end Solidity.Frontend.ExecutableAst.Memory.KernelMatrix
