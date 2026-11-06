import Solidity.Yul.Views.DeclarationBoundary
import Solidity.Yul.Views.DeclarationPathExtent

/-! Actual nested source paths, using the ONE declaration packing traversal.
The supported shape is checked by DeclaredArrayStruct; source references stay
references. No whole Source.Data representation or compiler adequacy is assumed. -/
namespace Solidity.Yul.Views

def nestedArrayPath (root : Source.DeclName) (i : Nat) : Source.SPath := ⟨root,[.field 0,.index i]⟩
def nestedStructPath (root : Source.DeclName) (i : Nat) : Source.SPath := ⟨root,[.field 1,.field i]⟩

theorem nestedArrayPath_injective (root : Source.DeclName) (i j : Nat)
    (same : nestedArrayPath root i = nestedArrayPath root j) : i = j := by
  have steps := congrArg Source.SPath.steps same
  exact Source.Step.index.inj (List.cons.inj (List.cons.inj steps).2).1

theorem nestedStructPath_injective (root : Source.DeclName) (i j : Nat)
    (same : nestedStructPath root i = nestedStructPath root j) : i = j := by
  have steps := congrArg Source.SPath.steps same
  exact Source.Step.field.inj (List.cons.inj (List.cons.inj steps).2).1

structure NestedDeclaration {E root base} (d : DeclaredArrayStruct E root base) (a : Roadmap.Address) where
  arrayRegistrations : List (ScalarPath E.layout (E.lay a))
  arrayEnd : Nat
  arrayPacked : packDeclarationPaths E (nestedArrayPath root) a 0 (List.replicate d.count ("",d.element))
    (base.val*32) = .ok (arrayRegistrations,arrayEnd)
  structRegistrations : List (ScalarPath E.layout (E.lay a))
  structEnd : Nat
  structPacked : packDeclarationPaths E (nestedStructPath root) a 0 d.fields
    (roundSlot arrayEnd) = .ok (structRegistrations,structEnd)

def prepareNestedDeclaration {E root base} (d : DeclaredArrayStruct E root base) (a : Roadmap.Address) :
    Except DeclarationPackingError (NestedDeclaration d a) :=
  match arrayPacked : packDeclarationPaths E (nestedArrayPath root) a 0
      (List.replicate d.count ("",d.element)) (base.val*32) with
  | .error reason => .error reason
  | .ok (arrayRegistrations,arrayEnd) =>
    match structPacked : packDeclarationPaths E (nestedStructPath root) a 0 d.fields (roundSlot arrayEnd) with
    | .error reason => .error reason
    | .ok (structRegistrations,structEnd) =>
      .ok ⟨arrayRegistrations,arrayEnd,arrayPacked,structRegistrations,structEnd,structPacked⟩

def NestedDeclaration.registrations {E root base d a} (r : @NestedDeclaration E root base d a) :=
  r.arrayRegistrations ++ r.structRegistrations

theorem NestedDeclaration.arrayEnd_eq {E root base d a} (r : @NestedDeclaration E root base d a) :
    r.arrayEnd = d.first.endByte (base.val*32) := by
  have prepared : (declarationMembers? E.layout ((List.replicate d.count ("",d.element)).map Prod.snd)).isSome := by
    rw [List.map_replicate,declarationMembers_replicate d.scalar d.scalarFound]
    rfl
  have extent := packDeclarationPaths_end_option E (nestedArrayPath root) a _ _ _ _ _ prepared r.arrayPacked
  rw [List.map_replicate,declarationMembers_replicate d.scalar d.scalarFound,Option.map_some] at extent
  exact (Option.some.inj extent).symm

theorem NestedDeclaration.structEnd_eq {E root base d a} (r : @NestedDeclaration E root base d a) :
    r.structEnd = d.members.endByte d.nextByte := by
  have extent := packDeclarationPaths_end E (nestedStructPath root) a _ _ _ _ _ d.members d.membersFound r.structPacked
  rw [r.arrayEnd_eq] at extent
  exact extent

theorem NestedDeclaration.array_spec {E root base d a} (r : @NestedDeclaration E root base d a) :
    base.val*32 ≤ r.arrayEnd ∧ finiteSeparated r.arrayRegistrations ∧
    ∀ c ∈ r.arrayRegistrations, ∃ i, i < d.count ∧ c.path = nestedArrayPath root i ∧
      base.val*32 ≤ declarationStart c ∧ declarationEnd c ≤ r.arrayEnd := by
  have spec := packDeclarationPaths_spec E (nestedArrayPath root) (nestedArrayPath_injective root) a _ _ _ _ _ r.arrayPacked
  refine ⟨spec.1,spec.2.1,?_⟩
  intro c member
  obtain ⟨i,_,bound,path,span⟩ := spec.2.2 c member
  simp only [List.length_replicate,Nat.zero_add] at bound
  exact ⟨i,bound,path,span⟩

theorem NestedDeclaration.struct_spec {E root base d a} (r : @NestedDeclaration E root base d a) :
    roundSlot r.arrayEnd ≤ r.structEnd ∧ finiteSeparated r.structRegistrations ∧
    ∀ c ∈ r.structRegistrations, ∃ i, i < d.fields.length ∧ c.path = nestedStructPath root i ∧
      roundSlot r.arrayEnd ≤ declarationStart c ∧ declarationEnd c ≤ r.structEnd := by
  have spec := packDeclarationPaths_spec E (nestedStructPath root) (nestedStructPath_injective root) a _ _ _ _ _ r.structPacked
  refine ⟨spec.1,spec.2.1,?_⟩
  intro c member
  obtain ⟨i,_,bound,path,span⟩ := spec.2.2 c member
  exact ⟨i,by simpa only [Nat.zero_add] using bound,path,span⟩

theorem pathsApart_of_span {D L} (c d : ScalarPath D L) (span : declarationEnd c ≤ declarationStart d) : pathsApart c d := by
  by_cases different : c.slot ≠ d.slot
  · exact Or.inl different
  · have equal : c.slot = d.slot := Decidable.byContradiction different
    have slots := congrArg Fin.val equal
    unfold declarationEnd declarationStart at span
    exact Or.inr (Or.inl (by omega))

theorem NestedDeclaration.separated {E root base d a} (r : @NestedDeclaration E root base d a) : finiteSeparated r.registrations := by
  apply List.pairwise_append.mpr
  refine ⟨r.array_spec.2.1,r.struct_spec.2.1,?_⟩
  intro c cm e em
  obtain ⟨i,_,cp,_,ce⟩ := r.array_spec.2.2 c cm
  obtain ⟨j,_,ep,es,_⟩ := r.struct_spec.2.2 e em
  refine ⟨?_,pathsApart_of_span c e (by have := (roundSlot_spec r.arrayEnd).1; omega)⟩
  intro same
  rw [cp,ep] at same
  have steps := congrArg Source.SPath.steps same
  have impossible : (0:Nat) = 1 := Source.Step.field.inj (List.cons.inj steps).1
  omega

theorem NestedDeclaration.paths {E root base d a} (r : @NestedDeclaration E root base d a) :
    r.registrations.map ScalarPath.path =
      (List.range' 0 d.count).map (nestedArrayPath root) ++
      (List.range' 0 d.fields.length).map (nestedStructPath root) := by
  rw [NestedDeclaration.registrations,List.map_append,
    packDeclarationPaths_paths E (nestedArrayPath root) a _ _ _ _ _ r.arrayPacked,
    packDeclarationPaths_paths E (nestedStructPath root) a _ _ _ _ _ r.structPacked,List.length_replicate]

theorem NestedDeclaration.owned_spans {E root base d a} (r : @NestedDeclaration E root base d a)
    (c : ScalarPath E.layout (E.lay a)) (member : c ∈ r.registrations) :
    (base.val*32 ≤ declarationStart c ∧ declarationEnd c ≤ r.arrayEnd) ∨
    (roundSlot r.arrayEnd ≤ declarationStart c ∧ declarationEnd c ≤ r.structEnd) := by
  rcases List.mem_append.mp member with first | second
  · obtain ⟨_,_,_,span⟩ := r.array_spec.2.2 c first
    exact Or.inl span
  · obtain ⟨_,_,_,span⟩ := r.struct_spec.2.2 c second
    exact Or.inr span

theorem NestedDeclaration.physical_bound {E root base d a} (r : @NestedDeclaration E root base d a) :
    roundSlot r.structEnd ≤ (2^256)*32 := by
  have input : base.val*32 ≤ (2^256)*32 := by have := base.isLt; omega
  have arrayBound := packDeclarationPaths_bound E (nestedArrayPath root) a _ _ _ _ _ input r.arrayPacked
  have structBound := packDeclarationPaths_bound E (nestedStructPath root) a _ _ _ _ _
    (roundSlot_bounded _ arrayBound) r.structPacked
  exact roundSlot_bounded _ structBound

end Solidity.Yul.Views
