import Solidity.Yul.Views.RecursiveStorageSpec

namespace Solidity.Yul.Views

theorem RecursiveStorageFields.pack_cons {E τ τs hb tb} (head : RecursiveStorageDeclaration E τ hb) (tail : RecursiveStorageFields E τs tb)
    (i p a cursor) :
    (RecursiveStorageFields.cons head tail).pack i p a cursor =
      (checkedRecursivePack head (p.go (.field i)) a cursor).bind (fun first =>
        (tail.pack (i+1) p a first.2).map (fun rest => (first.1++rest.1,rest.2))) := rfl

mutual
theorem RecursiveStorageDeclaration.pack_end {E τ b} (d : RecursiveStorageDeclaration E τ b)
    (p a cursor cs stop) (success : d.pack p a cursor = .ok (cs,stop)) : stop = d.endByte cursor := by
  cases d with
  | leaf old => exact old.pack_end _ _ _ _ _ success
  | strct name fields found members =>
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
theorem RecursiveStorageFields.pack_end {E τs b} (d : RecursiveStorageFields E τs b)
    (i p a cursor cs stop) (success : d.pack i p a cursor = .ok (cs,stop)) : stop = d.endByte cursor := by
  cases d with
  | nil => cases success; rfl
  | cons head tail =>
    rw [RecursiveStorageFields.pack_cons] at success
    cases first : checkedRecursivePack head (p.go (.field i)) a cursor with
    | error reason => simp only [first,Except.bind] at success; cases success
    | ok result =>
      rcases result with ⟨left,middle⟩
      cases second : tail.pack (i+1) p a middle with
      | error reason => simp only [first,second,Except.bind,Except.map] at success; cases success
      | ok result =>
        rcases result with ⟨right,last⟩
        simp only [first,second,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
        obtain ⟨rfl,rfl⟩ := success
        have start := (checkedRecursivePack_success head _ _ _ _ _ first).2
        have middleEq := head.pack_end _ _ _ _ _ start
        change last = tail.endByte (head.endByte cursor)
        rw [tail.pack_end _ _ _ _ _ _ second,middleEq]

end

end Solidity.Yul.Views
