import Solidity.Yul.Views.DeclarationPacking

namespace Solidity.Yul.Views

theorem packDeclarationFields_spec (E : Source.Env) (root : Source.DeclName) (a : Roadmap.Address)
    (fields : List (String × Source.STy)) (index cursor : Nat)
    (cs : List (ScalarPath E.layout (E.lay a))) (stop : Nat)
    (success : packDeclarationFields E root a index fields cursor = .ok (cs,stop)) :
    cursor ≤ stop ∧ finiteSeparated cs ∧
      ∀ c ∈ cs, ∃ j, index ≤ j ∧ c.path = declarationFieldPath root j ∧
        cursor ≤ declarationStart c ∧ declarationEnd c ≤ stop := by
  induction fields generalizing index cursor cs stop with
  | nil =>
    cases success
    exact ⟨Nat.le_refl _,.nil,fun _ member => by cases member⟩
  | cons head rest ih =>
    rcases head with ⟨name,τ⟩
    cases scalar : declarationScalar? E.layout τ with
    | none => simp only [packDeclarationFields,scalar] at success; cases success
    | some seed =>
      simp only [packDeclarationFields,scalar] at success
      split at success
      · rename_i typed
        split at success
        · rename_i bound
          cases packed : packDeclarationFields E root a (index+1) rest
              ((seed.position cursor).start+(seed.position cursor).field.width) with
          | error reason => simp only [packed,Except.map] at success; cases success
          | ok result =>
            rcases result with ⟨tail,finish⟩
            simp only [packed,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
            obtain ⟨rfl,rfl⟩ := success
            have tailSpec := ih (index+1) _ tail finish packed
            let c := (seed.position cursor).registration (declarationFieldPath root index) typed a bound
            have coordinate : declarationStart c = (seed.position cursor).start :=
              DeclPosition.registration_start _ _ _ _ _
            have afterHead : declarationEnd c = (seed.position cursor).start+(seed.position cursor).field.width := by
              unfold declarationEnd
              rw [coordinate]
              rfl
            have lower := (seed.position_bounds cursor).1
            refine ⟨by omega,?_,?_⟩
            · apply List.pairwise_cons.mpr
              refine ⟨?_,tailSpec.2.1⟩
              intro d member
              obtain ⟨j,hj,path,start,lastBound⟩ := tailSpec.2.2 d member
              constructor
              · intro same
                have steps := congrArg Source.SPath.steps same
                change [Source.Step.field index] = d.path.steps at steps
                rw [path] at steps
                simp only [declarationFieldPath,List.cons.injEq,Source.Step.field.injEq] at steps
                omega
              · by_cases different : c.slot ≠ d.slot
                · exact Or.inl different
                · have equal : c.slot = d.slot := Decidable.byContradiction different
                  have slots := congrArg Fin.val equal
                  apply Or.inr ∘ Or.inl
                  change c.field.offset+c.field.width ≤ d.field.offset
                  have order : declarationEnd c ≤ declarationStart d := by rw [afterHead]; exact start
                  unfold declarationEnd declarationStart at order
                  omega
            · intro d member
              rcases List.mem_cons.mp member with same | member
              · subst d
                exact ⟨index,Nat.le_refl _,rfl,by rw [coordinate]; exact lower,by rw [afterHead]; exact tailSpec.1⟩
              · obtain ⟨j,hj,path,start,lastBound⟩ := tailSpec.2.2 d member
                exact ⟨j,by omega,path,by omega,lastBound⟩
        · cases success
      · cases success

theorem PackedDeclaration.separated {E root a base} (d : PackedDeclaration E root a base) :
    finiteSeparated d.registrations := (packDeclarationFields_spec E root a d.fields 0 (base.val*32)
      d.registrations d.endByte d.packed).2.1

theorem PackedDeclaration.owned_bounds {E root a base} (d : PackedDeclaration E root a base)
    (c : ScalarPath E.layout (E.lay a)) (member : c ∈ d.registrations) :
    base.val*32 ≤ declarationStart c ∧ declarationEnd c ≤ d.endByte := by
  obtain ⟨_,_,_,bounds⟩ := (packDeclarationFields_spec E root a d.fields 0 (base.val*32)
    d.registrations d.endByte d.packed).2.2 c member
  exact bounds

end Solidity.Yul.Views
