import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Source.Decls

/-!
Guarded regression: a declaration's syntax category alone does not establish
that its node constructor matches its claimed kind. Full imported telescopes
retain actual membership in nonempty collected declarations. A deliberately
mislabeled enum node tests rejection; it is not a feasibility witness. Nested
collection retains contract scope and source order. No compiler-totality or
historical ownership claim is made.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.SourceDeclWitness
open Solidity.Source

def memberSyntax : Syn (.part false) :=
  .struct "S" (.structMember (.elem .bool) "flag") .nil
def memberDecl : Decl := ⟨.struct, "S", some "C", false, memberSyntax⟩
def unitSyntax : Syn .unit :=
  .unit (.cons (.contract false "C" .none .nil (.cons memberSyntax .nil)) .nil)

theorem collect_full : hypotheses_of% Syn.collect_ctor := by
  exact ⟨some "C", .part false, memberSyntax, memberDecl, List.mem_cons_self, True.intro⟩
#verify_hypotheses collect_full for Solidity.Source.Syn.collect_ctor
#print axioms collect_full

theorem declarations_full : hypotheses_of% Syn.decls_ctor := by
  exact ⟨unitSyntax, memberDecl, List.mem_cons_of_mem _ List.mem_cons_self, True.intro⟩
#verify_hypotheses declarations_full for Solidity.Source.Syn.decls_ctor
#print axioms declarations_full

/-- Constructor mismatches cannot occur in any actual collection. -/
theorem kind_mismatch_excluded (scope : Option String) {c : Cat} (s : Syn c)
    (d : Decl) (different : d.node.ctor ≠ d.kind.ctor) : d ∉ s.collect scope := by
  intro present
  exact different (s.collect_ctor scope d present)

-- Both kinds inhabit the same syntax category; this is intentionally mislabeled.
def mislabeled : Decl := ⟨.struct, "S", some "C", false, .enum "S" "First" []⟩

example : mislabeled ∉ unitSyntax.decls :=
  kind_mismatch_excluded none unitSyntax mislabeled (by decide)
example : [mislabeled] ≠ unitSyntax.decls := by
  intro same
  have present : mislabeled ∈ unitSyntax.decls := by
    rw [← same]
    exact List.mem_cons_self
  exact kind_mismatch_excluded none unitSyntax mislabeled (by decide) present

example : unitSyntax.decls.map (fun d => (d.kind, d.name, d.scope)) =
    [(.contract, "C", none), (.struct, "S", some "C")] := rfl
example : unitSyntax.decls ≠ [] := by
  intro impossible
  cases impossible

#print axioms kind_mismatch_excluded
end Solidity.H62.AuditLanguage.SourceDeclWitness
