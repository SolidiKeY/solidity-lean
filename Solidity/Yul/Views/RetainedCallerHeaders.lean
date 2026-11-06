import Solidity.Yul.Views.RetainedCallerCoverage

/-! Declaration-traced dynamic headers of saved-caller-selected child packs
belong to the actual prepared source inventory. Static trace membership is
kept distinct from arbitrary descendant-path or reachability completeness. -/
namespace Solidity.Yul.Views.RetainedCallerHeaders

theorem element_registration {E τ b child active a r fixed history scopes length}
    (image : @CapturedArrayImage E τ b child active a r fixed history scopes length)
    (element : RetainedElementPack r fixed) (inside : element ∈ image.elements)
    (c : ScalarPath E.layout (E.lay a)) (member : c ∈ element.2.registrations) : c ∈ image.registrations := by
  first | (simp only;done) | skip
  apply List.mem_cons_of_mem
  exact List.mem_flatMap.mpr ⟨element,inside,member⟩

theorem caller_header {E τ b child active Γ Δ σ} (F : Source.Fr)
    (layout : @RetainedArrayLayout E τ b child active F.this) (fixed : Roadmap.Evm.Fixed)
    (history : RetainedIndexHistory layout) (prior : List (EntryReferenceScope E))
    (caller : Source.Locals E.layout Γ) (callee : Source.Locals E.layout Δ)
    (m : Source.EM E Δ (Source.Val E.layout σ)) (state : Source.St E) (length : Roadmap.Word)
    (image : CapturedArrayImage layout fixed history (captureSubValueRun F prior caller callee m state).2 length)
    (path : Source.SPath) (inside : path ∈ localStoragePaths caller)
    (i : Nat) (index : entryPathIndex layout.root path=some i)
    (entry : {entry // entry ∈ child.headers (layout.path.go (.index i)) (layout.childCursor fixed i)}) :
    ∃ header : PathPrimitiveHeader E entry.val.1 entry.val.2.1 entry.val.2.2,
      header.registration F.this ∈ image.registrations := by
  first | (simp only;done) | skip
  obtain ⟨⟨j,pack⟩,present,same⟩ := RetainedCallerCoverage.caller_element F layout fixed history prior
    caller callee m state length image path inside i index
  dsimp only at same
  subst j
  exact ⟨pack.header entry,element_registration image ⟨i,pack⟩ present _ (pack.header_member entry)⟩

/-- Source traversal success supplies the real inventory, never a desired
membership/view law. Every traced saved-child header is in that output. -/
theorem caller_source_header {E τ b child active Γ Δ σ Ξ} (F : Source.Fr)
    (layout : @RetainedArrayLayout E τ b child active F.this) (fixed : Roadmap.Evm.Fixed)
    (history : RetainedIndexHistory layout) (prior : List (EntryReferenceScope E))
    (caller : Source.Locals E.layout Γ) (callee : Source.Locals E.layout Δ)
    (m : Source.EM E Δ (Source.Val E.layout σ)) (state : Source.St E) (length : Roadmap.Word)
    (image : CapturedArrayImage layout fixed history (captureSubValueRun F prior caller callee m state).2 length)
    (path : Source.SPath) (inside : path ∈ localStoragePaths caller)
    (i : Nat) (index : entryPathIndex layout.root path=some i)
    (entry : {entry // entry ∈ child.headers (layout.path.go (.index i)) (layout.childCursor fixed i)})
    (source : Source.EMState E Ξ) (inventory)
    (computed : image.sourceInventory? (F:=F) source=some inventory) :
    ∃ header : PathPrimitiveHeader E entry.val.1 entry.val.2.1 entry.val.2.2,
      header.registration F.this ∈ inventory := by
  first | (simp only;done) | skip
  obtain ⟨header,member⟩ := caller_header F layout fixed history prior caller callee m state length image path inside i index entry
  exact ⟨header,image.source_roots source inventory computed _ member⟩
end Solidity.Yul.Views.RetainedCallerHeaders
