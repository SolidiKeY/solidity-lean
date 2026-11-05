import Solidity.Yul.Views.ScalarDynamicHeader

namespace Solidity.Yul.Views

def StorageDeclaration.scalarFamilyType? {E τ} (d : StorageDeclaration E τ) : Option DynamicScalarKind :=
  StorageDeclaration.casesOn (motive := fun _ _ => Option DynamicScalarKind) d
    (fun _ => none) none (fun _ _ _ => none) (fun _ _ => none) (fun k => some k)

/-- Typed header metadata from the ONE original ordered packing cursor. -/
def StorageDeclarations.scalarFamilyHeaders {E ds} (d : StorageDeclarations E ds) :
    Nat → List (Source.DeclName × DynamicScalarKind × Nat) :=
  StorageDeclarations.casesOn (motive := fun _ _ => Nat → List (Source.DeclName × DynamicScalarKind × Nat)) d
    (fun _ => []) (fun {root _ _} head tail cursor =>
      let rest := tail.scalarFamilyHeaders (head.endByte cursor)
      match head.scalarFamilyType? with | none => rest | some t => (root,t,cursor)::rest)

theorem StorageDeclarations.scalarFamilyHeaders_sound {E ds} (d : StorageDeclarations E ds) (a : Roadmap.Address)
    (cursor cs stop) (success : d.pack a cursor = .ok (cs,stop))
    (root t incoming) (member : (root,t,incoming) ∈ d.scalarFamilyHeaders cursor) :
    ∃ h : ScalarDynamicHeader E root t incoming, h.registration a ∈ cs := by
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
          | fixed f =>
            change (root,t,incoming) ∈ tail.scalarFamilyHeaders (f.endByte cursor) at member
            change middle = f.endByte cursor at next
            rw [← next] at member
            obtain ⟨h,hm⟩ := ih _ _ _ second member
            exact ⟨h,List.mem_append.mpr (Or.inr hm)⟩
          | uintArray =>
            change (root,t,incoming) ∈ tail.scalarFamilyHeaders ((StorageDeclaration.uintArray (E := E)).endByte cursor) at member
            change middle = (StorageDeclaration.uintArray (E := E)).endByte cursor at next
            rw [← next] at member
            obtain ⟨h,hm⟩ := ih _ _ _ second member
            exact ⟨h,List.mem_append.mpr (Or.inr hm)⟩
          | packedUnsignedArray int u p =>
            change (root,t,incoming) ∈ tail.scalarFamilyHeaders ((StorageDeclaration.packedUnsignedArray (E := E) int u p).endByte cursor) at member
            change middle = (StorageDeclaration.packedUnsignedArray (E := E) int u p).endByte cursor at next
            rw [← next] at member
            obtain ⟨h,hm⟩ := ih _ _ _ second member
            exact ⟨h,List.mem_append.mpr (Or.inr hm)⟩
          | signedArray int u =>
            change (root,t,incoming) ∈ tail.scalarFamilyHeaders ((StorageDeclaration.signedArray (E := E) int u).endByte cursor) at member
            change middle = (StorageDeclaration.signedArray (E := E) int u).endByte cursor at next
            rw [← next] at member
            obtain ⟨h,hm⟩ := ih _ _ _ second member
            exact ⟨h,List.mem_append.mpr (Or.inr hm)⟩
          | scalarArray kind =>
            change (root,t,incoming) ∈ (name,kind,cursor)::tail.scalarFamilyHeaders _ at member
            rcases List.mem_cons.mp member with same | member
            · obtain ⟨rfl,pair⟩ := Prod.mk.inj same
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj pair
              obtain ⟨h,eq,_⟩ := scalarFamily_header_of_packed typed first
              exact ⟨h,List.mem_append.mpr (Or.inl (by rw [eq]; exact List.mem_singleton_self _))⟩
            · rw [← next] at member
              obtain ⟨h,hm⟩ := ih _ _ _ second member
              exact ⟨h,List.mem_append.mpr (Or.inr hm)⟩
    · cases success

def ComputedStorage.scalarFamilyTrace {E ds d active a} (r : @ComputedStorage E ds d active a) :=
  d.scalarFamilyHeaders (r.origin.persistent.val*32)

def ComputedStorage.scalarFamilyHeader {E ds d active a} (r : @ComputedStorage E ds d active a)
    (entry : {entry // entry ∈ r.scalarFamilyTrace}) : ScalarDynamicHeader E entry.val.1 entry.val.2.1 entry.val.2.2 :=
  let found := d.scalarFamilyHeaders_sound a _ _ _ r.packed _ _ _ entry.property
  ⟨by obtain ⟨h,_⟩ := found; exact h.declared,
   by obtain ⟨h,_⟩ := found; exact h.bounded⟩

theorem ScalarDynamicHeader.proof_irrel {E root t cursor} (h k : ScalarDynamicHeader E root t cursor) : h = k := by
  cases h; cases k; rfl

theorem ComputedStorage.scalarFamilyHeader_member {E ds d active a} (r : @ComputedStorage E ds d active a)
    (entry : {entry // entry ∈ r.scalarFamilyTrace}) : (r.scalarFamilyHeader entry).registration a ∈ r.registrations := by
  obtain ⟨h,member⟩ := d.scalarFamilyHeaders_sound a _ _ _ r.packed _ _ _ entry.property
  rw [h.proof_irrel (r.scalarFamilyHeader entry)] at member
  exact member

end Solidity.Yul.Views
