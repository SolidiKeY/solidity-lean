import Solidity.Yul.Views.RetainedEntryImage

/-! Saved-caller path observations select actual checked child packs, even on
callee halt and with no current callee aliases. These are finite traversal and
packing facts, not initial reachability, arbitrary evaluator instrumentation
or a claim that every Source reference fits this root/layout profile. -/
namespace Solidity.Yul.Views.RetainedCallerCoverage

theorem scope_index {E τ b child active a} (layout : @RetainedArrayLayout E τ b child active a)
    (scopes : List (EntryReferenceScope E)) (scope : EntryReferenceScope E)
    (present : scope ∈ scopes) (account : scope.account=a) (path : Source.SPath)
    (inside : path ∈ scope.paths) (i : Nat) (index : entryPathIndex layout.root path=some i) :
    i ∈ scopedEntryIndices layout scopes := by
  first | (simp only;done) | skip
  apply List.mem_flatMap.mpr
  refine ⟨scope,present,?_⟩
  rw [if_pos account]
  exact (entryPathIndices_member _ _ _).mpr ⟨path,inside,index⟩

theorem caller_visit {E τ b child active Γ Δ σ} (F : Source.Fr)
    (layout : @RetainedArrayLayout E τ b child active F.this)
    (history : RetainedIndexHistory layout) (prior : List (EntryReferenceScope E))
    (caller : Source.Locals E.layout Γ) (callee : Source.Locals E.layout Δ)
    (m : Source.EM E Δ (Source.Val E.layout σ)) (state : Source.St E)
    (path : Source.SPath) (inside : path ∈ localStoragePaths caller)
    (i : Nat) (index : entryPathIndex layout.root path=some i) (length : Nat) :
    i ∈ capturedVisitIndices layout history (captureSubValueRun F prior caller callee m state).2 length := by
  first | (simp only;done) | skip
  apply (capturedVisitIndices_mem _ _ _ _ _).mpr
  exact Or.inr (Or.inr (scope_index layout _ (entryLocalScope F caller)
    (captureSubValueRun_caller F prior caller callee m state) rfl path inside i index))

theorem caller_element {E τ b child active Γ Δ σ} (F : Source.Fr)
    (layout : @RetainedArrayLayout E τ b child active F.this) (fixed : Roadmap.Evm.Fixed)
    (history : RetainedIndexHistory layout) (prior : List (EntryReferenceScope E))
    (caller : Source.Locals E.layout Γ) (callee : Source.Locals E.layout Δ)
    (m : Source.EM E Δ (Source.Val E.layout σ)) (state : Source.St E) (length : Roadmap.Word)
    (image : CapturedArrayImage layout fixed history (captureSubValueRun F prior caller callee m state).2 length)
    (path : Source.SPath) (inside : path ∈ localStoragePaths caller)
    (i : Nat) (index : entryPathIndex layout.root path=some i) :
    ∃ element ∈ image.elements, element.1=i := by
  first | (simp only;done) | skip
  have visit := caller_visit F layout history prior caller callee m state path inside i index length.val
  rw [←image.visited] at visit
  exact List.mem_map.mp visit

/-- A genuine typed incoming alias needs no fabricated historical index event. -/
theorem typed_caller_element {E τ b child active Γ Δ σ ρ} (F : Source.Fr)
    (layout : @RetainedArrayLayout E τ b child active F.this) (fixed : Roadmap.Evm.Fixed)
    (history : RetainedIndexHistory layout) (prior : List (EntryReferenceScope E))
    (caller : Source.Locals E.layout Γ) (callee : Source.Locals E.layout Δ)
    (m : Source.EM E Δ (Source.Val E.layout σ)) (state : Source.St E) (length : Roadmap.Word)
    (image : CapturedArrayImage layout fixed history (captureSubValueRun F prior caller callee m state).2 length)
    (H : Source.HeapTy) (ok : Source.LocalsOK E H caller) (idx : Source.Idx Γ ρ)
    (storage : ρ.loc?=some .storage) (path : Source.SPath)
    (found : caller.get idx=Source.Val.storRef storage path)
    (i : Nat) (index : entryPathIndex layout.root path=some i) :
    E.pathTy path=some ρ ∧ ∃ element ∈ image.elements, element.1=i := by
  first | (simp only;done) | skip
  have typed := typedEntryReference H caller idx storage path found ok
  exact ⟨typed.1,caller_element F layout fixed history prior caller callee m state length image path typed.2 i index⟩
end Solidity.Yul.Views.RetainedCallerCoverage
