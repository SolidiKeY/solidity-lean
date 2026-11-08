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

end Solidity.Frontend.Admission
