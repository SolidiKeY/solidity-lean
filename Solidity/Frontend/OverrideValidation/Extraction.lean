import Solidity.Frontend.OverrideValidation.Graph

/-! Typed equality and exact reconstruction of the existing Source declaration
list. No erased or second syntax is introduced. -/
namespace Solidity.Frontend.OverrideValidation
open Solidity.Source

deriving instance DecidableEq for Syn
deriving instance DecidableEq for Decl

theorem syntax_equality_reflect {c : Cat} {a b : Syn c} : decide (a = b) = true ↔ a = b := by
  simp only [decide_eq_true_eq]

theorem declaration_equality_reflect {a b : Decl} : decide (a = b) = true ↔ a = b := by
  simp only [decide_eq_true_eq]

def rootDeclarations (E : Env) : List Decl := E.decls.filter (·.top)

def reconstructed (E : Env) : List Decl :=
  (rootDeclarations E).flatMap fun d => d.node.collect none

/-- Exact typed list equality preserves every member and original body. -/
def ExtractionOK (E : Env) : Prop := E.decls = reconstructed E

def extractionB (E : Env) : Bool := decide (E.decls = reconstructed E)

theorem extractionB_iff {E : Env} : extractionB E = true ↔ ExtractionOK E := by
  simp only [extractionB, ExtractionOK, decide_eq_true_eq]

theorem complete_collected_member {E : Env} (h : ExtractionOK E)
    {root d : Decl} (hr : root ∈ rootDeclarations E) (hd : d ∈ root.node.collect none) : d ∈ E.decls := by
  rw [h]
  exact List.mem_flatMap.mpr ⟨root, hr, hd⟩

theorem collected_member_position {E : Env} (h : ExtractionOK E)
    {root d : Decl} (hr : root ∈ rootDeclarations E) (hd : d ∈ root.node.collect none) :
    ∃ n : Node E, n.decl = d := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp (complete_collected_member h hr hd)
  exact ⟨⟨i, hi⟩, he⟩

end Solidity.Frontend.OverrideValidation
