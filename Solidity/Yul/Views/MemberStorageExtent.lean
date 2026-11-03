import Solidity.Yul.Views.MemberStorageDeclaration

namespace Solidity.Yul.Views

theorem MemberStorageDeclarations.pack_cons {E τ τs} (head : StorageDeclaration E τ) (tail : MemberStorageDeclarations E τs)
    (i p a cursor) :
    (MemberStorageDeclarations.cons head tail).pack i p a cursor =
      (checkedMemberPack head (p.go (.field i)) a cursor).bind (fun first =>
        (tail.pack (i+1) p a first.2).map (fun rest => (first.1++rest.1,rest.2))) := rfl

theorem MemberStorageDeclarations.pack_end {E τs} (d : MemberStorageDeclarations E τs)
    (i p a cursor cs stop) (success : d.pack i p a cursor = .ok (cs,stop)) : stop = d.endByte cursor := by
  induction d generalizing i cursor cs stop with
  | nil => cases success; rfl
  | @cons τ τs head tail ih =>
    rw [pack_cons] at success
    cases first : checkedMemberPack head (p.go (.field i)) a cursor with
    | error reason => simp only [first,Except.bind] at success; cases success
    | ok result =>
      rcases result with ⟨left,middle⟩
      cases second : tail.pack (i+1) p a middle with
      | error reason => simp only [first,second,Except.bind,Except.map] at success; cases success
      | ok result =>
        rcases result with ⟨right,last⟩
        simp only [first,second,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
        obtain ⟨rfl,rfl⟩ := success
        have start := (checkedMemberPack_success head _ _ _ _ _ first).2
        have middleEq := head.pack_end _ _ _ _ _ start
        change last = tail.endByte (head.endByte cursor)
        rw [ih _ _ _ _ second,middleEq]

theorem RootStorageDeclaration.pack_end {E τ} (d : RootStorageDeclaration E τ)
    (p a cursor cs stop) (success : d.pack p a cursor = .ok (cs,stop)) : stop = d.endByte cursor := by
  cases d with
  | leaf old => exact old.pack_end _ _ _ _ _ success
  | strct name fields found members dynamic =>
    change (alignFixedPack (members.pack 0)) p a cursor = .ok (cs,stop) at success
    unfold alignFixedPack at success
    cases first : members.pack 0 p a (roundSlot cursor) with
    | error reason => simp only [first,Except.map] at success; cases success
    | ok result =>
      rcases result with ⟨left,middle⟩
      simp only [first,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
      obtain ⟨rfl,rfl⟩ := success
      change roundSlot middle = roundSlot (members.endByte (roundSlot cursor))
      rw [members.pack_end _ _ _ _ _ _ first]

end Solidity.Yul.Views
