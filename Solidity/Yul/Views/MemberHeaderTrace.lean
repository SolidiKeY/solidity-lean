import Solidity.Yul.Views.PathPrimitive

namespace Solidity.Yul.Views

abbrev PathHeaderEntry := Source.SPath × PathPrimitiveKind × Nat

def StorageDeclaration.pathHeaders {E τ} (d : StorageDeclaration E τ) (p : Source.SPath) (cursor : Nat) : List PathHeaderEntry :=
  match d.pathPrimitive? with
  | none => []
  | some kind => [(p,kind,cursor)]

theorem StorageDeclaration.pathHeaders_sound {E τ} (d : StorageDeclaration E τ)
    (p a cursor cs stop) (typed : E.pathTy p = some τ)
    (success : d.pack p a cursor = .ok (cs,stop)) (entry : PathHeaderEntry)
    (member : entry ∈ d.pathHeaders p cursor) :
    ∃ h : PathPrimitiveHeader E entry.1 entry.2.1 entry.2.2, h.registration a ∈ cs := by
  unfold pathHeaders at member
  cases selected : d.pathPrimitive? with
  | none => rw [selected] at member; cases member
  | some k =>
    rw [selected] at member
    have same := List.mem_singleton.mp member
    subst entry
    obtain ⟨h,equal⟩ := d.pathPrimitive_sound p a cursor cs stop k typed success selected
    exact ⟨h,by rw [equal]; exact List.mem_singleton_self _⟩

def MemberStorageDeclarations.headers {E τs} (d : MemberStorageDeclarations E τs) :
    Nat → Source.SPath → Nat → List PathHeaderEntry :=
  MemberStorageDeclarations.casesOn (motive := fun _ _ => Nat → Source.SPath → Nat → List PathHeaderEntry) d
    (fun _ _ _ => []) (fun head tail index p cursor =>
      head.pathHeaders (p.go (.field index)) cursor ++ tail.headers (index+1) p (head.endByte cursor))

theorem MemberStorageDeclarations.headers_sound {E τs} (d : MemberStorageDeclarations E τs)
    (index p a cursor cs stop) (success : d.pack index p a cursor = .ok (cs,stop))
    (entry : PathHeaderEntry) (member : entry ∈ d.headers index p cursor) :
    ∃ h : PathPrimitiveHeader E entry.1 entry.2.1 entry.2.2, h.registration a ∈ cs := by
  induction d generalizing index cursor cs stop with
  | nil => cases member
  | cons head tail ih =>
    change (packFixedField (checkedMemberPack head) tail.pack index p a cursor) = _ at success
    unfold packFixedField packFixedRow at success
    cases first : checkedMemberPack head (p.go (.field index)) a cursor with
    | error reason => simp only [first,Except.bind] at success; cases success
    | ok result =>
      rcases result with ⟨left,middle⟩
      cases second : tail.pack (index+1) p a middle with
      | error reason => simp only [first,second,Except.bind,Except.map] at success; cases success
      | ok result =>
        rcases result with ⟨right,last⟩
        simp only [first,second,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
        obtain ⟨rfl,rfl⟩ := success
        obtain ⟨typed,packed⟩ := checkedMemberPack_success head _ _ _ _ _ first
        have next : middle = head.endByte cursor := head.pack_end _ _ _ _ _ packed
        change entry ∈ head.pathHeaders (p.go (.field index)) cursor ++ tail.headers (index+1) p (head.endByte cursor) at member
        rcases List.mem_append.mp member with here | rest
        · obtain ⟨h,hm⟩ := head.pathHeaders_sound _ _ _ _ _ typed packed entry here
          exact ⟨h,List.mem_append_left _ hm⟩
        · rw [← next] at rest
          obtain ⟨h,hm⟩ := ih _ _ _ _ second rest
          exact ⟨h,List.mem_append_right _ hm⟩

def RootStorageDeclaration.headers {E τ} (d : RootStorageDeclaration E τ) : Source.SPath → Nat → List PathHeaderEntry :=
  RootStorageDeclaration.casesOn (motive := fun _ _ => Source.SPath → Nat → List PathHeaderEntry) d
    (fun old => old.pathHeaders) (fun _ _ _ members _ p cursor => members.headers 0 p (roundSlot cursor))

theorem RootStorageDeclaration.headers_sound {E τ} (d : RootStorageDeclaration E τ)
    (p a cursor cs stop) (typed : E.pathTy p = some τ)
    (success : d.pack p a cursor = .ok (cs,stop)) (entry : PathHeaderEntry)
    (member : entry ∈ d.headers p cursor) :
    ∃ h : PathPrimitiveHeader E entry.1 entry.2.1 entry.2.2, h.registration a ∈ cs := by
  cases d with
  | leaf old => exact old.pathHeaders_sound _ _ _ _ _ typed success entry member
  | strct name fields found members dynamic =>
    change (members.pack 0 p a (roundSlot cursor)).map (fun out => (out.1,roundSlot out.2)) = _ at success
    cases packed : members.pack 0 p a (roundSlot cursor) with
    | error reason => simp only [packed,Except.map] at success; cases success
    | ok result =>
      rcases result with ⟨out,last⟩
      simp only [packed,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
      obtain ⟨rfl,rfl⟩ := success
      exact members.headers_sound _ _ _ _ _ _ packed entry member

end Solidity.Yul.Views
