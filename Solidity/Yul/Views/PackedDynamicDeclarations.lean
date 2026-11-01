import Solidity.Yul.Views.PackedDynamicHeader

namespace Solidity.Yul.Views

def StorageDeclaration.unsignedType? {E τ} (d : StorageDeclaration E τ) : Option Source.IntTy :=
  StorageDeclaration.casesOn (motive := fun _ _ => Option Source.IntTy) d
    (fun _ => none) (some .u256) (fun t _ _ => some t)

/-- Typed header metadata from the ONE original ordered packing cursor. -/
def StorageDeclarations.unsignedHeaders {E ds} (d : StorageDeclarations E ds) :
    Nat → List (Source.DeclName × Source.IntTy × Nat) :=
  StorageDeclarations.casesOn (motive := fun _ _ => Nat → List (Source.DeclName × Source.IntTy × Nat)) d
    (fun _ => []) (fun {root _ _} head tail cursor =>
      let rest := tail.unsignedHeaders (head.endByte cursor)
      match head.unsignedType? with | none => rest | some t => (root,t,cursor)::rest)

theorem StorageDeclarations.unsignedHeaders_sound {E ds} (d : StorageDeclarations E ds) (a : Roadmap.Address)
    (cursor cs stop) (success : d.pack a cursor = .ok (cs,stop))
    (root t incoming) (member : (root,t,incoming) ∈ d.unsignedHeaders cursor) :
    ∃ h : PackedDynamicHeader E root t incoming, h.registration a ∈ cs := by
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
            change (root,t,incoming) ∈ tail.unsignedHeaders (fixed.endByte cursor) at member
            change middle = fixed.endByte cursor at next
            rw [← next] at member
            obtain ⟨h,hm⟩ := ih _ _ _ second member
            exact ⟨h,List.mem_append.mpr (Or.inr hm)⟩
          | uintArray =>
            change (root,t,incoming) ∈ (name,Source.IntTy.u256,cursor)::tail.unsignedHeaders _ at member
            rcases List.mem_cons.mp member with same | member
            · obtain ⟨rfl,pair⟩ := Prod.mk.inj same
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj pair
              obtain ⟨h,eq,_⟩ := packed_header_of_packed rfl typed first
              exact ⟨h,List.mem_append.mpr (Or.inl (by rw [eq]; exact List.mem_singleton_self _))⟩
            · rw [← next] at member
              obtain ⟨h,hm⟩ := ih _ _ _ second member
              exact ⟨h,List.mem_append.mpr (Or.inr hm)⟩
          | packedUnsignedArray int unsigned packed =>
            change (root,t,incoming) ∈ (name,int,cursor)::tail.unsignedHeaders _ at member
            rcases List.mem_cons.mp member with same | member
            · obtain ⟨rfl,pair⟩ := Prod.mk.inj same
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj pair
              obtain ⟨h,eq,_⟩ := packed_header_of_packed unsigned typed first
              exact ⟨h,List.mem_append.mpr (Or.inl (by rw [eq]; exact List.mem_singleton_self _))⟩
            · rw [← next] at member
              obtain ⟨h,hm⟩ := ih _ _ _ second member
              exact ⟨h,List.mem_append.mpr (Or.inr hm)⟩
    · cases success

def ComputedStorage.unsignedTrace {E ds d active a} (r : @ComputedStorage E ds d active a) :=
  d.unsignedHeaders (r.origin.persistent.val*32)

def ComputedStorage.unsignedHeader {E ds d active a} (r : @ComputedStorage E ds d active a)
    (entry : {entry // entry ∈ r.unsignedTrace}) : PackedDynamicHeader E entry.val.1 entry.val.2.1 entry.val.2.2 :=
  let found := d.unsignedHeaders_sound a _ _ _ r.packed _ _ _ entry.property
  ⟨by obtain ⟨h,_⟩ := found; exact h.unsigned,
   by obtain ⟨h,_⟩ := found; exact h.declared,
   by obtain ⟨h,_⟩ := found; exact h.bounded⟩

theorem PackedDynamicHeader.proof_irrel {E root t cursor} (h k : PackedDynamicHeader E root t cursor) : h = k := by
  cases h; cases k; rfl

theorem ComputedStorage.unsignedHeader_member {E ds d active a} (r : @ComputedStorage E ds d active a)
    (entry : {entry // entry ∈ r.unsignedTrace}) : (r.unsignedHeader entry).registration a ∈ r.registrations := by
  obtain ⟨h,member⟩ := d.unsignedHeaders_sound a _ _ _ r.packed _ _ _ entry.property
  rw [h.proof_irrel (r.unsignedHeader entry)] at member
  exact member

end Solidity.Yul.Views
