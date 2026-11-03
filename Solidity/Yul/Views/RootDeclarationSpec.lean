import Solidity.Yul.Views.RootDeclarations

namespace Solidity.Yul.Views

theorem RootDeclarations.pack_spec {E ds} (d : RootDeclarations E ds)
    (distinct : (ds.map Prod.fst).Nodup) (a : Roadmap.Address) (cursor cs stop)
    (success : d.pack a cursor = .ok (cs,stop)) :
    cursor ≤ stop ∧ (cursor ≤ (2^256)*32 → stop ≤ (2^256)*32) ∧ finiteSeparated cs ∧
    ∀ c ∈ cs, cursor ≤ declarationStart c ∧ declarationEnd c ≤ stop ∧ c.path.root ∈ ds.map Prod.fst := by
  induction d generalizing cursor cs stop with
  | nil => cases success; exact ⟨Nat.le_refl _,(fun h => h),(by constructor),by intro c h; cases h⟩
  | @cons root τ rest head tail ih =>
    have nodup := List.nodup_cons.mp distinct
    simp only [RootDeclarations.pack_cons] at success
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
          refine ⟨by omega,(fun bound => rb (lb bound)),?_,?_⟩
          · apply List.pairwise_append.mpr
            refine ⟨ls,rs,?_⟩
            intro c hc e he
            obtain ⟨cl,ch,_⟩ := lm c hc
            obtain ⟨el,eh,er⟩ := rm e he
            refine ⟨?_,pathsApart_of_span c e (by omega)⟩
            intro same
            have roots := congrArg Source.SPath.root same
            rw [leftRoots c hc] at roots
            exact nodup.1 (roots ▸ er)
          · intro c member
            rcases List.mem_append.mp member with hc | hc
            · obtain ⟨cl,ch,_⟩ := lm c hc
              exact ⟨cl,by omega,List.mem_cons.mpr (Or.inl (leftRoots c hc))⟩
            · obtain ⟨cl,ch,cr⟩ := rm c hc
              exact ⟨by omega,ch,List.mem_cons_of_mem root cr⟩
    · cases success

theorem RootDeclarations.pack_paths {E ds} (d : RootDeclarations E ds) (a : Roadmap.Address)
    (cursor cs stop) (success : d.pack a cursor = .ok (cs,stop)) : cs.map ScalarPath.path = d.paths := by
  induction d generalizing cursor cs stop with
  | nil => cases success; rfl
  | @cons root τ rest head tail ih =>
    simp only [RootDeclarations.pack_cons] at success
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

theorem RootDeclarations.pack_end {E ds} (d : RootDeclarations E ds) (a : Roadmap.Address)
    (cursor cs stop) (success : d.pack a cursor = .ok (cs,stop)) : stop = d.endByte cursor := by
  induction d generalizing cursor cs stop with
  | nil => cases success; rfl
  | @cons root τ rest head tail ih =>
    simp only [RootDeclarations.pack_cons] at success
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
