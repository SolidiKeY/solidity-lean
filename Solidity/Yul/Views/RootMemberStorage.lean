import Solidity.Yul.Views.MemberStorageExtent

namespace Solidity.Yul.Views

/-- Additive root certificates. Source declarations and the old root API stay
unchanged; a new struct root uses actual field metadata, not a fictitious scalar. -/
inductive RootMemberDeclarations (E : Source.Env) : List (Source.DeclName × Source.STy) → Type where
  | nil : RootMemberDeclarations E []
  | cons {root τ rest} (head : RootStorageDeclaration E τ) (tail : RootMemberDeclarations E rest) : RootMemberDeclarations E ((root,τ)::rest)

def RootMemberDeclarations.pack {E ds} (d : RootMemberDeclarations E ds) : RootPackFn E :=
  RootMemberDeclarations.casesOn (motive := fun _ _ => RootPackFn E) d
    (fun _ cursor => .ok ([],cursor))
    (fun {root τ _} head tail a cursor =>
      if E.rootTy root = some τ then
        (head.pack ⟨root,[]⟩ a cursor).bind (fun first =>
          (tail.pack a first.2).map (fun rest => (first.1++rest.1,rest.2)))
      else .error .missingRoot)

theorem RootMemberDeclarations.pack_cons {E root τ rest} (head : RootStorageDeclaration E τ) (tail : RootMemberDeclarations E rest)
    (a cursor) : (RootMemberDeclarations.cons (root := root) head tail).pack a cursor =
      if E.rootTy root = some τ then
        (head.pack ⟨root,[]⟩ a cursor).bind (fun first =>
          (tail.pack a first.2).map (fun out => (first.1++out.1,out.2)))
      else .error .missingRoot := rfl

def RootMemberDeclarations.endByte {E ds} (d : RootMemberDeclarations E ds) : Nat → Nat :=
  RootMemberDeclarations.casesOn (motive := fun _ _ => Nat → Nat) d id
    (fun head tail cursor => tail.endByte (head.endByte cursor))

theorem RootMemberDeclarations.pack_spec {E ds} (d : RootMemberDeclarations E ds)
    (distinct : (ds.map Prod.fst).Nodup) (a : Roadmap.Address) (cursor cs stop)
    (success : d.pack a cursor = .ok (cs,stop)) :
    cursor ≤ stop ∧ (cursor ≤ (2^256)*32 → stop ≤ (2^256)*32) ∧ finiteSeparated cs ∧
    ∀ c ∈ cs, cursor ≤ declarationStart c ∧ declarationEnd c ≤ stop ∧ c.path.root ∈ ds.map Prod.fst := by
  induction d generalizing cursor cs stop with
  | nil => cases success; exact ⟨Nat.le_refl _,(fun h => h),(by constructor),by intro c h; cases h⟩
  | @cons root τ rest head tail ih =>
    have nodup := List.nodup_cons.mp distinct
    simp only [RootMemberDeclarations.pack_cons] at success
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


end Solidity.Yul.Views
