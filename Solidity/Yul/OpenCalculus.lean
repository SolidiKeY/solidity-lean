import Solidity.Yul.OpenComposition
import Solidity.Yul.WordAdapterLogic

/-! Lean-only derived calculus bridge for the independent full-AST runner.
The existing twenty word rules and actual root model are reused. This does
not claim Source/G51 normalization, total correctness or compiler refinement. -/
namespace Solidity.Yul.OpenRun
def holds {X c n} (mode : Solidity.Modality) (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (post : WordAdapter.Outcome X c n → Prop)
    (state : WordState X n) : Prop :=
  match mode with
  | .box => ∀ fuel result, OpenRun.statement fuel .nil code policy state = some result → post result
  | .diamond => ∃ fuel result, OpenRun.statement fuel .nil code policy state = some result ∧ post result

theorem holds_iff_raw {X c n} (mode : Solidity.Modality) (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (post : WordAdapter.Outcome X c n → Prop) (state : WordState X n) :
    holds mode code policy post state ↔ WordAdapter.rawHolds mode code policy post state := by
  cases mode <;> simp only [holds,WordAdapter.rawHolds,OpenRun.run_agrees]

def formula {X c n} (mode : Solidity.Modality) (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (post : WordAdapter.Outcome X c n → Prop) :
    Logic.Fml (n+wordCellCount X) := WordAdapter.formula mode code policy post

theorem formula_iff {X c n} (mode : Solidity.Modality) (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (post : WordAdapter.Outcome X c n → Prop) (state : WordState X n) :
    (formula mode code policy post).holds state.pack ↔ holds mode code policy post state :=
  (WordAdapter.formula_iff mode code policy post state).trans (holds_iff_raw mode code policy post state).symm

theorem rule_exists {X c n} (mode : Solidity.Modality) (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (post : WordAdapter.Outcome X c n → Prop) :
    ∃ premise, Nonempty (Logic.Rule (formula mode code policy post) premise) :=
  WordAdapter.rule_exists mode code policy post

/-- The word logic is shallow (`atom` takes a Lean predicate), so this existence
form is met by `.atom (holds …)`; the concrete rule premise comes from
`rule_exists`. -/
theorem rule_sound {X c n} (mode : Solidity.Modality) (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (post : WordAdapter.Outcome X c n → Prop) :
    ∃ premise : Logic.Fml (n+wordCellCount X), ∀ state : WordState X n,
      holds mode code policy post state ↔ premise.holds state.pack := by
  obtain ⟨premise,sound⟩ := WordAdapter.rule_sound mode code policy post
  exact ⟨premise,fun state => (holds_iff_raw mode code policy post state).trans (sound state)⟩
end Solidity.Yul.OpenRun
