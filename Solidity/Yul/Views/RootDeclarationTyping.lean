import Solidity.Yul.Views.RootDeclarationChecked

namespace Solidity.Yul.Views

theorem RootDeclarations.pack_typed {E ds} (d : RootDeclarations E ds) (a : Roadmap.Address)
    (cursor cs stop) (success : d.pack a cursor = .ok (cs,stop)) :
    ∀ c ∈ cs, (E.pathTy c.path).isSome := by
  induction d generalizing cursor cs stop with
  | nil => cases success; intro c member; cases member
  | @cons root τ rest head tail ih =>
    simp only [RootDeclarations.pack_cons] at success
    split at success
    · rename_i typed
      cases first : head.pack ⟨root,[]⟩ a cursor with
      | error reason => simp only [first,Except.bind] at success; cases success
      | ok result =>
        rcases result with ⟨left,middle⟩
        cases second : tail.pack a middle with
        | error reason => simp only [first,second,Except.bind,Except.map] at success; cases success
        | ok result =>
          rcases result with ⟨right,last⟩
          simp only [first,second,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
          obtain ⟨rfl,rfl⟩ := success
          intro c member
          rcases List.mem_append.mp member with member | member
          · have enumerated : c.path ∈ left.map ScalarPath.path := List.mem_map.mpr ⟨c,member,rfl⟩
            rw [head.pack_paths _ _ _ _ _ first] at enumerated
            exact head.paths_typed ⟨root,[]⟩ typed c.path enumerated
          · exact ih _ _ _ second c member
    · cases success

theorem CheckedRootDeclarations.paths_typed {E ds d scope tr a origin}
    (r : @CheckedRootDeclarations E ds d scope tr a origin)
    (c : ScalarPath E.layout (E.lay a)) (member : c ∈ r.registrations) : (E.pathTy c.path).isSome :=
  d.pack_typed _ _ _ _ r.packed c member

end Solidity.Yul.Views
