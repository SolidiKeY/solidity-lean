import Solidity.Yul.Views.RecursiveStorageExtent

namespace Solidity.Yul.Views

mutual
theorem RecursiveStorageDeclaration.headers_sound {E τ b} (d : RecursiveStorageDeclaration E τ b)
    (p a cursor cs stop) (typed : E.pathTy p = some τ)
    (success : d.pack p a cursor = .ok (cs,stop)) (entry : PathHeaderEntry)
    (member : entry ∈ d.headers p cursor) :
    ∃ h : PathPrimitiveHeader E entry.1 entry.2.1 entry.2.2, h.registration a ∈ cs := by
  cases d with
  | leaf old => exact old.pathHeaders_sound _ _ _ _ _ typed success entry member
  | strct name fields found members =>
    change (members.pack 0 p a (roundSlot cursor)).map (fun out => (out.1,roundSlot out.2)) = _ at success
    cases packed : members.pack 0 p a (roundSlot cursor) with
    | error reason => simp only [packed,Except.map] at success; cases success
    | ok result =>
      rcases result with ⟨out,last⟩
      simp only [packed,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
      obtain ⟨rfl,rfl⟩ := success
      exact members.headers_sound _ _ _ _ _ _ packed entry member
theorem RecursiveStorageFields.headers_sound {E τs b} (d : RecursiveStorageFields E τs b)
    (index p a cursor cs stop) (success : d.pack index p a cursor = .ok (cs,stop))
    (entry : PathHeaderEntry) (member : entry ∈ d.headers index p cursor) :
    ∃ h : PathPrimitiveHeader E entry.1 entry.2.1 entry.2.2, h.registration a ∈ cs := by
  cases d with
  | nil => cases member
  | cons head tail =>
    change (packFixedField (checkedRecursivePack head) tail.pack index p a cursor) = _ at success
    unfold packFixedField packFixedRow at success
    cases first : checkedRecursivePack head (p.go (.field index)) a cursor with
    | error reason => simp only [first,Except.bind] at success; cases success
    | ok result =>
      rcases result with ⟨left,middle⟩
      cases second : tail.pack (index+1) p a middle with
      | error reason => simp only [first,second,Except.bind,Except.map] at success; cases success
      | ok result =>
        rcases result with ⟨right,last⟩
        simp only [first,second,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
        obtain ⟨rfl,rfl⟩ := success
        obtain ⟨typed,packed⟩ := checkedRecursivePack_success head _ _ _ _ _ first
        have next : middle = head.endByte cursor := head.pack_end _ _ _ _ _ packed
        change entry ∈ head.headers (p.go (.field index)) cursor ++ tail.headers (index+1) p (head.endByte cursor) at member
        rcases List.mem_append.mp member with here | rest
        · obtain ⟨h,hm⟩ := head.headers_sound _ _ _ _ _ typed packed entry here
          exact ⟨h,List.mem_append_left _ hm⟩
        · rw [← next] at rest
          obtain ⟨h,hm⟩ := tail.headers_sound _ _ _ _ _ _ second entry rest
          exact ⟨h,List.mem_append_right _ hm⟩

end

end Solidity.Yul.Views
