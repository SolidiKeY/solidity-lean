import Solidity.Yul.Views.RetainedCallerCoverage
import Solidity.Yul.Views.RetainedForLoopPost

/-! Actual retained loop inventories feed the existing checked array-image
selection. Scope/account/path evidence selects a packed child; image computation
and Source/frame agreement remain separate requirements, not invented producers. -/
namespace Solidity.Yul.Views.RetainedLoopImage

theorem scope_visit {E τ b child active a} (layout : @RetainedArrayLayout E τ b child active a)
    (history : RetainedIndexHistory layout) (scopes : List (EntryReferenceScope E))
    (scope : EntryReferenceScope E) (present : scope∈scopes) (account : scope.account=a)
    (path : Source.SPath) (inside : path∈scope.paths) (i : Nat)
    (index : entryPathIndex layout.root path=some i) (length : Nat) :
    i∈capturedVisitIndices layout history scopes length := by
  apply (capturedVisitIndices_mem layout history scopes length i).mpr
  exact Or.inr (Or.inr (RetainedCallerCoverage.scope_index layout scopes scope present account path inside i index))

/-- A real computed image contains the pack selected by an observed path.
This does not construct an image or imply that an unobserved path was captured. -/
theorem scope_element {E τ b child active a} (layout : @RetainedArrayLayout E τ b child active a)
    (fixed : Roadmap.Evm.Fixed) (history : RetainedIndexHistory layout)
    (scopes : List (EntryReferenceScope E)) (length : Roadmap.Word)
    (image : CapturedArrayImage layout fixed history scopes length)
    (scope : EntryReferenceScope E) (present : scope∈scopes) (account : scope.account=a)
    (path : Source.SPath) (inside : path∈scope.paths) (i : Nat)
    (index : entryPathIndex layout.root path=some i) :
    ∃ element∈image.elements, element.1=i := by
  have visit := scope_visit layout history scopes scope present account path inside i index length.val
  rw [← image.visited] at visit
  exact List.mem_map.mp visit

end Solidity.Yul.Views.RetainedLoopImage
