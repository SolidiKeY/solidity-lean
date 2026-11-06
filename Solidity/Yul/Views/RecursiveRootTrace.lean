import Solidity.Yul.Views.RecursiveComputedStorage

namespace Solidity.Yul.Views

def RecursiveRootDeclarations.headers {E ds} (d : RecursiveRootDeclarations E ds) : Nat → List PathHeaderEntry :=
  RecursiveRootDeclarations.casesOn (motive := fun _ _ => Nat → List PathHeaderEntry) d
    (fun _ => []) (fun {root _ _ _} head tail cursor => head.headers ⟨root,[]⟩ cursor ++ tail.headers (head.endByte cursor))

theorem RecursiveRootDeclarations.headers_sound {E ds} (d : RecursiveRootDeclarations E ds) (a : Roadmap.Address)
    (cursor cs stop) (success : d.pack a cursor = .ok (cs,stop)) (entry : PathHeaderEntry)
    (member : entry ∈ d.headers cursor) :
    ∃ h : PathPrimitiveHeader E entry.1 entry.2.1 entry.2.2, h.registration a ∈ cs := by
  induction d generalizing cursor cs stop with
  | nil => cases member
  | @cons name τ rest b head tail ih =>
    simp only [RecursiveRootDeclarations.pack_cons] at success
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
          change entry ∈ head.headers ⟨name,[]⟩ cursor ++ tail.headers (head.endByte cursor) at member
          rcases List.mem_append.mp member with here | rest
          · have pathTyped : E.pathTy ⟨name,[]⟩ = some τ := typed
            obtain ⟨h,hm⟩ := head.headers_sound _ _ _ _ _ pathTyped first entry here
            exact ⟨h,List.mem_append_left _ hm⟩
          · rw [← next] at rest
            obtain ⟨h,hm⟩ := ih _ _ _ second rest
            exact ⟨h,List.mem_append_right _ hm⟩
    · cases success

def RecursiveComputedStorage.headerTrace {E ds d active a} (r : @RecursiveComputedStorage E ds d active a) :=
  d.headers (r.origin.persistent.val*32)

def RecursiveComputedStorage.header {E ds d active a} (r : @RecursiveComputedStorage E ds d active a)
    (entry : {entry // entry ∈ r.headerTrace}) : PathPrimitiveHeader E entry.val.1 entry.val.2.1 entry.val.2.2 := by
  obtain ⟨h,_⟩ := d.headers_sound a _ _ _ r.packed entry.val entry.property
  exact h

theorem RecursiveComputedStorage.header_member {E ds d active a} (r : @RecursiveComputedStorage E ds d active a)
    (entry : {entry // entry ∈ r.headerTrace}) : (r.header entry).registration a ∈ r.registrations := by
  obtain ⟨h,member⟩ := d.headers_sound a _ _ _ r.packed entry.val entry.property
  rw [h.proof_irrel (r.header entry)] at member
  exact member

end Solidity.Yul.Views
