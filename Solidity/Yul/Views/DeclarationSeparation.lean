import Solidity.Yul.Views.DeclarationPathSeparation

namespace Solidity.Yul.Views

theorem packDeclarationFields_spec (E : Source.Env) (root : Source.DeclName) (a : Roadmap.Address)
    (fields : List (String × Source.STy)) (index cursor : Nat)
    (cs : List (ScalarPath E.layout (E.lay a))) (stop : Nat)
    (success : packDeclarationFields E root a index fields cursor = .ok (cs,stop)) :
    cursor ≤ stop ∧ finiteSeparated cs ∧
      ∀ c ∈ cs, ∃ j, index ≤ j ∧ c.path = declarationFieldPath root j ∧
        cursor ≤ declarationStart c ∧ declarationEnd c ≤ stop := by
  have injective : ∀ i j, declarationFieldPath root i = declarationFieldPath root j → i = j := by
    intro i j same
    have steps := congrArg Source.SPath.steps same
    exact Source.Step.field.inj (List.cons.inj steps).1
  have spec := packDeclarationPaths_spec E (declarationFieldPath root) injective a fields index cursor cs stop success
  refine ⟨spec.1,spec.2.1,?_⟩
  intro c member
  obtain ⟨j,lower,_,path,bounds⟩ := spec.2.2 c member
  exact ⟨j,lower,path,bounds⟩

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
