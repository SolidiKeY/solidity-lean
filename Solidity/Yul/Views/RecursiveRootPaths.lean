import Solidity.Yul.Views.RecursiveRootTrace

namespace Solidity.Yul.Views

def RecursiveRootDeclarations.paths {E ds} (d : RecursiveRootDeclarations E ds) : List Source.SPath :=
  RecursiveRootDeclarations.casesOn (motive := fun _ _ => List Source.SPath) d []
    (fun {root _ _ _} head tail => head.paths ⟨root,[]⟩ ++ tail.paths)

theorem RecursiveRootDeclarations.pack_paths {E ds} (d : RecursiveRootDeclarations E ds) (a : Roadmap.Address)
    (cursor cs stop) (success : d.pack a cursor = .ok (cs,stop)) : cs.map ScalarPath.path = d.paths := by
  induction d generalizing cursor cs stop with
  | nil => cases success; rfl
  | @cons root τ rest b head tail ih =>
    simp only [RecursiveRootDeclarations.pack_cons] at success
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

theorem RecursiveRootDeclarations.pack_end {E ds} (d : RecursiveRootDeclarations E ds) (a : Roadmap.Address)
    (cursor cs stop) (success : d.pack a cursor = .ok (cs,stop)) : stop = d.endByte cursor := by
  induction d generalizing cursor cs stop with
  | nil => cases success; rfl
  | @cons root τ rest b head tail ih =>
    simp only [RecursiveRootDeclarations.pack_cons] at success
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

namespace Solidity.Yul.Views

theorem RecursiveComputedStorage.coverage {E ds d active a} (r : @RecursiveComputedStorage E ds d active a) :
    r.registrations.map ScalarPath.path = d.paths := d.pack_paths a _ _ _ r.packed

theorem RecursiveComputedStorage.paths_unique {E ds d active a} (r : @RecursiveComputedStorage E ds d active a) :
    d.paths.Nodup := by
  rw [← r.coverage]
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (fun separated => separated.1) r.separated

theorem RecursiveComputedStorage.end_exact {E ds d active a} (r : @RecursiveComputedStorage E ds d active a) :
    r.endByte = d.endByte (r.origin.persistent.val*32) := d.pack_end a _ _ _ r.packed

end Solidity.Yul.Views
