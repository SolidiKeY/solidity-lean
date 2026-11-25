import Solidity.Yul.Views.StorageDeclarations

namespace Solidity.Yul.Views

theorem StorageDeclarations.pack_spec {E ds} (d : StorageDeclarations E ds)
    (distinct : (ds.map Prod.fst).Nodup) (a : Roadmap.Address) (cursor cs stop)
    (success : d.pack a cursor = .ok (cs,stop)) :
    cursor ≤ stop ∧ (cursor ≤ (2^256)*32 → stop ≤ (2^256)*32) ∧ finiteSeparated cs ∧
    ∀ c ∈ cs, cursor ≤ declarationStart c ∧ declarationEnd c ≤ stop ∧ c.path.root ∈ ds.map Prod.fst := by
  induction d generalizing cursor cs stop with
  | nil => cases success; exact ⟨Nat.le_refl _,(fun h => h),(by constructor),by intro c h; cases h⟩
  | @cons root τ rest head tail ih =>
    have nodup := List.nodup_cons.mp distinct
    simp only [StorageDeclarations.pack_cons] at success
    split at success
    · cases first : head.pack ⟨root,[]⟩ a cursor with
      | error reason => simp only [first,Except.bind] at success; cases success
      | ok result =>
        rcases result with ⟨left,middle⟩
        cases second : tail.pack a middle with
        | error reason => simp only [first,second,Except.bind,Except.map] at success; cases success
        | ok result =>
          rcases result with ⟨right,last⟩
          simp only [first,second,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
          obtain ⟨rfl,rfl⟩ := success
          obtain ⟨lo,lb,ls,lm⟩ := head.pack_good _ _ _ _ _ first
          obtain ⟨hi,rb,rs,rm⟩ := ih nodup.2 _ _ _ second
          have leftRoots (c) (hc : c ∈ left) : c.path.root = root := by
            obtain ⟨suffix,equal⟩ := (lm c hc).2.2
            exact congrArg Source.SPath.root equal
          exact rootPack_append_spec root (rest.map Prod.fst) left right cursor middle last
            lo hi lb rb ls rs (fun c hc => ⟨(lm c hc).1,(lm c hc).2.1⟩) rm leftRoots nodup.1
    · cases success

theorem StorageDeclarations.pack_paths {E ds} (d : StorageDeclarations E ds) (a : Roadmap.Address)
    (cursor cs stop) (success : d.pack a cursor = .ok (cs,stop)) : cs.map ScalarPath.path = d.paths := by
  induction d generalizing cursor cs stop with
  | nil => cases success; rfl
  | @cons root τ rest head tail ih =>
    simp only [StorageDeclarations.pack_cons] at success
    split at success
    · cases first : head.pack ⟨root,[]⟩ a cursor with
      | error reason => simp only [first,Except.bind] at success; cases success
      | ok result =>
        rcases result with ⟨left,middle⟩
        cases second : tail.pack a middle with
        | error reason => simp only [first,second,Except.bind,Except.map] at success; cases success
        | ok result =>
          rcases result with ⟨right,last⟩
          simp only [first,second,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
          obtain ⟨rfl,rfl⟩ := success
          rw [List.map_append,head.pack_paths _ _ _ _ _ first,ih _ _ _ second]
          rfl
    · cases success

theorem StorageDeclarations.pack_end {E ds} (d : StorageDeclarations E ds) (a : Roadmap.Address)
    (cursor cs stop) (success : d.pack a cursor = .ok (cs,stop)) : stop = d.endByte cursor := by
  induction d generalizing cursor cs stop with
  | nil => cases success; rfl
  | @cons root τ rest head tail ih =>
    simp only [StorageDeclarations.pack_cons] at success
    split at success
    · cases first : head.pack ⟨root,[]⟩ a cursor with
      | error reason => simp only [first,Except.bind] at success; cases success
      | ok result =>
        rcases result with ⟨left,middle⟩
        cases second : tail.pack a middle with
        | error reason => simp only [first,second,Except.bind,Except.map] at success; cases success
        | ok result =>
          rcases result with ⟨right,last⟩
          simp only [first,second,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
          obtain ⟨rfl,rfl⟩ := success
          change last = tail.endByte (head.endByte cursor)
          rw [ih _ _ _ second,head.pack_end _ _ _ _ _ first]
    · cases success

end Solidity.Yul.Views
