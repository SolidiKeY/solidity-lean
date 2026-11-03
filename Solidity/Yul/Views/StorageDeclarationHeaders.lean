import Solidity.Yul.Views.StorageDeclarationSpec
import Solidity.Yul.Views.DynamicHeader

namespace Solidity.Yul.Views

/-- Compatibility selector for the original uint256-header API. Properly
packed unsigned families use the separate typed unsignedHeaders trace. -/
def StorageDeclaration.isDynamic {E τ} (d : StorageDeclaration E τ) : Bool :=
  StorageDeclaration.casesOn (motive := fun _ _ => Bool) d (fun _ => false) true (fun _ _ _ => false) (fun _ _ => false) (fun _ => false)

/-- Legacy uint256 dynamic declaration heads are recorded, at the ACTUAL incoming
cursor of the same typed traversal. This is metadata, not another state. -/
def StorageDeclarations.headers {E ds} (d : StorageDeclarations E ds) : Nat → List (Source.DeclName × Nat) :=
  StorageDeclarations.casesOn (motive := fun _ _ => Nat → List (Source.DeclName × Nat)) d
    (fun _ => [])
    (fun {root _ _} head tail cursor =>
      let rest := tail.headers (head.endByte cursor)
      if head.isDynamic then (root,cursor)::rest else rest)

/-- Every enumerated dynamic header is backed by the REAL successful
packing output and actual source declaration. No readback law is assumed. -/
theorem StorageDeclarations.headers_sound {E ds} (d : StorageDeclarations E ds) (a : Roadmap.Address)
    (cursor cs stop) (success : d.pack a cursor = .ok (cs,stop))
    (root incoming) (member : (root,incoming) ∈ d.headers cursor) :
    ∃ h : DynamicHeader E root incoming, h.registration a ∈ cs := by
  induction d generalizing cursor cs stop with
  | nil => cases member
  | @cons name τ rest head tail ih =>
    simp only [StorageDeclarations.pack_cons] at success
    split at success
    · rename_i typed
      cases first : head.pack ⟨name,[]⟩ a cursor with
      | error reason => simp only [first,Except.bind] at success; cases success
      | ok result =>
        rcases result with ⟨left,middle⟩
        cases second : tail.pack a middle with
        | error reason => simp only [first,second,Except.bind,Except.map] at success; cases success
        | ok result =>
          rcases result with ⟨right,last⟩
          simp only [first,second,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
          obtain ⟨rfl,rfl⟩ := success
          have next : middle = head.endByte cursor := head.pack_end _ _ _ _ _ first
          cases head with
          | fixed fixed =>
            change (root,incoming) ∈ tail.headers (fixed.endByte cursor) at member
            change middle = fixed.endByte cursor at next
            rw [← next] at member
            obtain ⟨h,hm⟩ := ih _ _ _ second member
            exact ⟨h,List.mem_append.mpr (Or.inr hm)⟩
          | packedUnsignedArray t unsigned packed =>
            change (root,incoming) ∈ tail.headers ((StorageDeclaration.packedUnsignedArray (E := E) t unsigned packed).endByte cursor) at member
            rw [← next] at member
            obtain ⟨h,hm⟩ := ih _ _ _ second member
            exact ⟨h,List.mem_append.mpr (Or.inr hm)⟩
          | signedArray t signed =>
            change (root,incoming) ∈ tail.headers ((StorageDeclaration.signedArray (E := E) t signed).endByte cursor) at member
            rw [← next] at member
            obtain ⟨h,hm⟩ := ih _ _ _ second member
            exact ⟨h,List.mem_append.mpr (Or.inr hm)⟩
          | scalarArray kind =>
            change (root,incoming) ∈ tail.headers ((StorageDeclaration.scalarArray (E := E) kind).endByte cursor) at member
            rw [← next] at member
            obtain ⟨h,hm⟩ := ih _ _ _ second member
            exact ⟨h,List.mem_append.mpr (Or.inr hm)⟩
          | uintArray =>
            change (root,incoming) ∈ (name,cursor)::tail.headers ((StorageDeclaration.uintArray (E := E)).endByte cursor) at member
            rcases List.mem_cons.mp member with same | member
            · have pair := Prod.mk.inj same
              obtain ⟨rfl,rfl⟩ := pair
              obtain ⟨h,eq,_⟩ := dynamic_header_of_packed typed first
              exact ⟨h,List.mem_append.mpr (Or.inl (by rw [eq]; exact List.mem_singleton_self _))⟩
            · rw [← next] at member
              obtain ⟨h,hm⟩ := ih _ _ _ second member
              exact ⟨h,List.mem_append.mpr (Or.inr hm)⟩
    · cases success

end Solidity.Yul.Views
