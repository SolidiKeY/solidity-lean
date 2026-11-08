import Solidity.Frontend.Admission.SyntaxOccurrenceLaws
import Solidity.Frontend.Admission.NameResolutionRoots

/-! Canonical declaration-aware Source syntax enumeration.
Regression purpose: unused declarations and their nested syntax must not be
silently omitted when building the versioned admission feature inventory.
The existing intrinsic occurrence visitor is reused without fuel or a supplied
roster. Each site retains its actual root declaration; that root identity is
not an assertion of the innermost lexical scope. Feature classification,
profile activation and operational admission remain separate obligations. -/
namespace Solidity.Frontend.Admission
open Solidity.Source

/-- Metadata only: the actual declaration and one intrinsic syntax site. -/
abbrev DeclarationOccurrence := Decl × SyntaxOccurrence

/-- Includes every carried declaration, including unused bodies. The caller
cannot replace the environment roster with a selected list of roots. -/
def declarationOccurrences (E : Env) : List DeclarationOccurrence :=
  E.decls.flatMap fun d => (syntaxOccurrences d.node).map (fun x => (d,x))

/-- Independent declaration membership and source-subterm relation. -/
def DeclarationOccurrence.Occurs (E : Env) (site : DeclarationOccurrence) : Prop :=
  site.1 ∈ E.decls ∧ Syn.Sub site.2 ⟨site.1.kind.cat site.1.top, site.1.node⟩

/-- Exactness concerns the whole declaration syntax, not just executed roots. -/
theorem declarationOccurrences_iff (E : Env) (site : DeclarationOccurrence) :
    site ∈ declarationOccurrences E ↔ site.Occurs E := by
  rcases site with ⟨d,x⟩
  simp only [declarationOccurrences, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨other, member, inner, occurs, equality⟩
    have declarations := congrArg Prod.fst equality
    have sites := congrArg Prod.snd equality
    dsimp only at declarations sites
    cases declarations
    cases sites
    exact ⟨member, (syntaxOccurrences_iff d.node x).mp occurs⟩
  · rintro ⟨member, subterm⟩
    exact ⟨d,member,x,(syntaxOccurrences_iff d.node x).mpr subterm,rfl⟩

/-- An unused declaration is still a root of the canonical inventory. -/
theorem declaration_root_covered (E : Env) (d : Decl) (member : d ∈ E.decls) :
    (d,⟨d.kind.cat d.top,d.node⟩) ∈ declarationOccurrences E :=
  (declarationOccurrences_iff E _).mpr ⟨member,.refl _⟩

/-- Every typed descendant of an actual declaration is retained. -/
theorem declaration_subterm_covered (E : Env) (d : Decl) (member : d ∈ E.decls)
    (site : SyntaxOccurrence) (subterm : Syn.Sub site ⟨d.kind.cat d.top,d.node⟩) :
    (d,site) ∈ declarationOccurrences E :=
  (declarationOccurrences_iff E _).mpr ⟨member,subterm⟩

/-- Actual name resolution supplies roster membership; no additional target
coverage hypothesis is added to the source resolver. -/
theorem resolved_declaration_subterm_covered {E : Env} {locals : List String}
    {scope : Option String} {name : String} {ds : List Decl} {d : Decl}
    (resolved : E.resolve locals scope name = some (.decls ds)) (chosen : d ∈ ds)
    (site : SyntaxOccurrence) (subterm : Syn.Sub site ⟨d.kind.cat d.top,d.node⟩) :
    (d,site) ∈ declarationOccurrences E :=
  declaration_subterm_covered E d
    (NameResolutionRoots.resolved_registered resolved chosen) site subterm

/-- The Source singleton overload rule also feeds the same inventory. -/
theorem selected_function_subterm_covered (Γ : Ctx) (name : String)
    (filter : Decl → Bool) (d : Decl) (selected : (Γ.functions name).filter filter = [d])
    (site : SyntaxOccurrence) (subterm : Syn.Sub site ⟨d.kind.cat d.top,d.node⟩) :
    (d,site) ∈ declarationOccurrences Γ.env :=
  declaration_subterm_covered Γ.env d
    (NameResolutionRoots.selected_function_membership Γ name filter d selected) site subterm

/-- info: 'Solidity.Frontend.Admission.declarationOccurrences_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declarationOccurrences_iff

/-- info: 'Solidity.Frontend.Admission.declaration_root_covered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declaration_root_covered

/-- info: 'Solidity.Frontend.Admission.declaration_subterm_covered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declaration_subterm_covered

/-- info: 'Solidity.Frontend.Admission.resolved_declaration_subterm_covered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_declaration_subterm_covered

/-- info: 'Solidity.Frontend.Admission.selected_function_subterm_covered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_function_subterm_covered

/-! Source-unit headers must remain available separately from the declaration
inventory. Regression: inserting a pragma changes source syntax while leaving
the Source resolution environment unchanged. These laws justify neither a
feature classification nor reconstruction of lexical input. -/

/-- Declaration collection erases a leading pragma for every remaining unit. -/
theorem pragma_env_unchanged (words : List String) (rest : Syn (.list .top)) :
    (Syn.unit (.cons (.pragma words) rest)).env = (Syn.unit rest).env := rfl

/-- The canonical intrinsic syntax visitor still retains that pragma. -/
theorem pragma_syntax_preserved (words : List String) (rest : Syn (.list .top)) :
    (⟨.top, .pragma words⟩ : SyntaxOccurrence) ∈
      syntaxOccurrences (Syn.unit (.cons (.pragma words) rest)) := by
  apply (syntaxOccurrences_iff _ _).mpr
  exact .child (List.mem_singleton_self _)
    (.child (List.mem_cons_self ..) (.refl _))

/-- No decoder of only the declaration environment can recover every source
unit. A header-sensitive extractor must retain the required header information
separately, for example in the original unit. -/
theorem source_unit_not_recoverable_from_env :
    ¬ ∃ recover : Env → Syn .unit, ∀ u : Syn .unit, recover u.env = u := by
  rintro ⟨recover,correct⟩
  have empty := correct (Syn.unit .nil)
  have header := correct (Syn.unit (.cons (.pragma ["solidity", "^0.8.38"]) .nil))
  have same : Syn.unit .nil =
      Syn.unit (.cons (.pragma ["solidity", "^0.8.38"]) .nil) :=
    empty.symm.trans header
  cases Syn.unit.inj same

/-- info: 'Solidity.Frontend.Admission.pragma_env_unchanged' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms pragma_env_unchanged

/-- info: 'Solidity.Frontend.Admission.pragma_syntax_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pragma_syntax_preserved

/-- info: 'Solidity.Frontend.Admission.source_unit_not_recoverable_from_env' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms source_unit_not_recoverable_from_env

/-- Compose the existing intrinsic subterm relation without replacing its
representation or its immediate-child relation. -/
theorem syntaxSub_trans {a b c : SyntaxOccurrence}
    (ab : Syn.Sub a b) (bc : Syn.Sub b c) : Syn.Sub a c := by
  induction bc with
  | refl => exact ab
  | child member sub ih => exact .child member ih

/-- Every declaration returned by the actual collector retains its original
syntax position. No separate declaration roster or coverage premise is used. -/
theorem collected_declaration_subterm (scope : Option String) {c : Cat} (s : Syn c) :
    ∀ d ∈ s.collect scope,
      Syn.Sub ⟨d.kind.cat d.top,d.node⟩ ⟨c,s⟩ := by
  fun_induction Syn.collect scope s <;> intro d member
  all_goals first
    | exact False.elim (List.not_mem_nil member)
    | (have same := List.mem_singleton.mp member
       cases same
       exact .refl _)
    | (rename_i ih
       exact .child (List.mem_singleton_self _) (ih d member))
    | (rename_i ihLeft ihRight
       rcases List.mem_append.mp member with left | right
       · exact .child (List.mem_cons_self ..) (ihLeft d left)
       · exact .child (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (ihRight d right))
    | (rcases List.mem_cons.mp member with same | nested
       · cases same
         exact .refl _
       · rename_i ih
         first
           | exact .child (List.mem_singleton_self _) (ih d nested)
           | exact .child (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (ih d nested)
           | exact .child (List.mem_cons_of_mem _
               (List.mem_cons_of_mem _ (List.mem_singleton_self _))) (ih d nested))

/-- Declaration inventory sites are genuine sites of their original source
unit. The converse is deliberately absent: headers also occur in the unit. -/
theorem declaration_occurrence_in_source_unit (u : Syn .unit)
    (site : DeclarationOccurrence) (present : site ∈ declarationOccurrences u.env) :
    site.2 ∈ syntaxOccurrences u := by
  have occurs := (declarationOccurrences_iff u.env site).mp present
  have root := collected_declaration_subterm Option.none u site.1 occurs.1
  exact (syntaxOccurrences_iff u site.2).mpr (syntaxSub_trans occurs.2 root)

/-- info: 'Solidity.Frontend.Admission.syntaxSub_trans' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms syntaxSub_trans

/-- info: 'Solidity.Frontend.Admission.collected_declaration_subterm' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms collected_declaration_subterm

/-- info: 'Solidity.Frontend.Admission.declaration_occurrence_in_source_unit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declaration_occurrence_in_source_unit

/-! Metadata classifiers share one declaration traversal. Regression: adding
another direct-field classifier must not silently select only executed roots or
lose the original declaration/site. Classifier completeness remains a separate
obligation; these laws establish exactly the supplied classifier's occurrences. -/

universe u

/-- Retain each actual declaration and syntax site alongside a classified field.
The classifier sees the intrinsic syntax category; it cannot replace the roster. -/
def declarationFieldUses {α : Type u} (E : Env)
    (fields : ∀ {c : Cat}, Syn c → List α) : List (DeclarationOccurrence × α) :=
  (declarationOccurrences E).flatMap fun site =>
    (fields site.2.2).map fun value => (site,value)

/-- Exactness for any direct metadata-field classifier, without a coverage
premise or a second traversal implementation. -/
theorem declarationFieldUses_iff {α : Type u} (E : Env)
    (fields : ∀ {c : Cat}, Syn c → List α)
    (site : DeclarationOccurrence) (value : α) :
    (site,value) ∈ declarationFieldUses E fields ↔
      site.Occurs E ∧ value ∈ fields site.2.2 := by
  simp only [declarationFieldUses, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨other, member, field, present, equality⟩
    have sites := congrArg Prod.fst equality
    have values := congrArg Prod.snd equality
    dsimp only at sites values
    cases sites
    cases values
    exact ⟨(declarationOccurrences_iff E site).mp member,present⟩
  · rintro ⟨occurs,present⟩
    exact ⟨site,(declarationOccurrences_iff E site).mpr occurs,value,present,rfl⟩

/-- A reported field has both its original source-unit syntax site and its
classifier membership. This does not assert that the classifier reports every
language feature or that every source-unit site belongs to a declaration. -/
theorem declarationFieldUses_source_witness {α : Type u} (unit : Syn .unit)
    (fields : ∀ {c : Cat}, Syn c → List α)
    (site : DeclarationOccurrence) (value : α)
    (present : (site,value) ∈ declarationFieldUses unit.env fields) :
    site.2 ∈ syntaxOccurrences unit ∧ value ∈ fields site.2.2 := by
  have found := (declarationFieldUses_iff unit.env fields site value).mp present
  exact ⟨declaration_occurrence_in_source_unit unit site
    ((declarationOccurrences_iff unit.env site).mpr found.1),found.2⟩

/-- info: 'Solidity.Frontend.Admission.declarationFieldUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declarationFieldUses_iff

/-- info: 'Solidity.Frontend.Admission.declarationFieldUses_source_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declarationFieldUses_source_witness

end Solidity.Frontend.Admission
