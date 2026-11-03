import Solidity.Yul.WordAdapter
import Solidity.Yul.WordCoverage
/-! Exact raw-state interpretation of the existing Lean-only word calculus.
Boxes quantify completed horizons; diamonds require actual completion.
Every raw cell/word and the legal control transfer remains observable.
This is not total correctness, independent Source semantics or G51 dispatch. -/
namespace Solidity.Yul.WordAdapter

def rawHolds {X c n} (mode : Solidity.Modality) (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (post : Outcome X c n → Prop)
    (state : WordState X n) : Prop :=
  match mode with
  | .box => ∀ fuel result, run code policy fuel state = some result → post result
  | .diamond => ∃ fuel result, run code policy fuel state = some result ∧ post result

def formula {X c n} (mode : Solidity.Modality) (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (post : Outcome X c n → Prop) :
    Logic.Fml (n + wordCellCount X) :=
  .modal mode model (program code policy)
    (fun flow => .atom (fun vars => post ⟨WordState.unpack vars,flow⟩))

theorem formula_iff {X c n} (mode : Solidity.Modality) (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (post : Outcome X c n → Prop)
    (state : WordState X n) :
    (formula mode code policy post).holds state.pack ↔
      rawHolds mode code policy post state := by
  cases mode with
  | box =>
    change (∀ fuel packed, Closed.evalStmt fuel model.environment model.words
      (program code policy).code (program code policy).words state.pack = some packed →
      post (Outcome.decode packed)) ↔
      ∀ fuel result, run code policy fuel state = some result → post result
    constructor
    · intro valid fuel result done
      obtain ⟨packed,finished,decoded⟩ := (run_some_iff code policy fuel state result).mp done
      have preserved := valid fuel packed finished
      rw [decoded] at preserved
      exact preserved
    · intro valid fuel packed finished
      exact valid fuel (Outcome.decode packed)
        ((run_some_iff code policy fuel state _).mpr ⟨packed,finished,rfl⟩)
  | diamond =>
    change (∃ fuel packed, Closed.evalStmt fuel model.environment model.words
      (program code policy).code (program code policy).words state.pack = some packed ∧
      post (Outcome.decode packed)) ↔
      ∃ fuel result, run code policy fuel state = some result ∧ post result
    constructor
    · rintro ⟨fuel,packed,finished,valid⟩
      exact ⟨fuel,Outcome.decode packed,
        (run_some_iff code policy fuel state _).mpr ⟨packed,finished,rfl⟩,valid⟩
    · rintro ⟨fuel,result,done,valid⟩
      obtain ⟨packed,finished,decoded⟩ := (run_some_iff code policy fuel state result).mp done
      exact ⟨fuel,packed,finished,decoded.symm ▸ valid⟩

/-- A concrete existing rule for every actual raw-state formula. No rule,
model or termination oracle appears in the premises. -/
theorem rule_exists {X c n} (mode : Solidity.Modality) (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (post : Outcome X c n → Prop) :
    ∃ premise, Nonempty (Logic.Rule (formula mode code policy post) premise) :=
  Logic.program_rule_exists mode model (program code policy) _

/-- The word logic is shallow (`atom` takes a Lean predicate), so this existence
form is met by `.atom (holds …)`; the concrete rule premise comes from
`rule_exists`. -/
theorem rule_sound {X c n} (mode : Solidity.Modality) (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (post : Outcome X c n → Prop) :
    ∃ premise : Logic.Fml (n + wordCellCount X), ∀ state : WordState X n,
      rawHolds mode code policy post state ↔ premise.holds state.pack := by
  obtain ⟨premise,sound⟩ := Logic.sound_program_rule_exists mode model
    (program code policy) (fun flow => .atom (fun vars => post ⟨WordState.unpack vars,flow⟩))
  exact ⟨premise,fun state => (formula_iff mode code policy post state).symm.trans
    (sound state.pack)⟩

end Solidity.Yul.WordAdapter

namespace Solidity.Yul.WordAdapter

/-- Soundness for the displayed premise of a concrete Rule. Atoms/substitutions
remain shallow Lean functions; this is not a deep syntax calculus. -/
theorem rule_premise_sound : ∀ {X c n} (mode : Solidity.Modality) (code : Solidity.Yul.Stmt [] X c n)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Solidity.Yul.WordAdapter.Outcome X c n → Prop)
 {premise : Solidity.Yul.Logic.Fml (n + Solidity.Yul.wordCellCount X)},
 Solidity.Yul.Logic.Rule (Solidity.Yul.WordAdapter.formula mode code policy post) premise →
 ∀ state : Solidity.Yul.WordState X n,
 Solidity.Yul.WordAdapter.rawHolds mode code policy post state ↔ premise.holds state.pack := by
  intro X c n mode code policy post premise rule state
  exact (Solidity.Yul.WordAdapter.formula_iff mode code policy post state).symm.trans
    (Solidity.Yul.Logic.Rule.sound rule state.pack)

end Solidity.Yul.WordAdapter
