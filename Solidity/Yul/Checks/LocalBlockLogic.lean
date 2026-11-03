import Solidity.Yul.LocalBlockLogic
import Solidity.Yul.Checks.LocalBlock
namespace Solidity.Yul.Checks.LocalBlockLogic
open Solidity.Yul.LocalBlockLogic
export Checks.LocalBlock (ctx code policy initial completed snapshot)

def expected : List Nat := [2,2^256-1,2309737967,257,22136,2^256-1,171*2^248]
def post (result : LocalBlockOutcome ctx ⟨false,false⟩) : Prop :=
  snapshot result.state = expected ∧ result.state.2 = initial.2

theorem done : runLocalBlock ctx code policy 32 initial = some completed :=
  (Option.some_get Checks.LocalBlock.code_completes).symm
theorem completed_post : post completed := by
  constructor
  · decide
  · exact runLocalBlock_world ctx code policy 32 initial done

theorem box_post : holds .box code policy post initial := by
  intro fuel result finished
  have same := completed_unique code policy initial finished done
  cases same
  exact completed_post

theorem diamond_post : holds .diamond code policy post initial :=
  ⟨32,completed,done,completed_post⟩

example : ¬ holds .box code policy (fun _ => False) initial := by
  intro impossible
  exact impossible 32 completed done
example : ¬ holds .diamond code policy (fun _ => False) initial := by
  rintro ⟨fuel,result,finished,impossible⟩
  exact impossible
example :
    (formula .box code policy post initial).holds
      (WordState.pack (n := 0) ⟨Fin.elim0,localWordCells ctx initial.1⟩) :=
  (formula_iff .box code policy post initial).mpr box_post
example :
    (formula .diamond code policy post initial).holds
      (WordState.pack (n := 0) ⟨Fin.elim0,localWordCells ctx initial.1⟩) :=
  (formula_iff .diamond code policy post initial).mpr diamond_post
example : ∃ premise, Nonempty (Logic.Rule (formula .box code policy post initial) premise) :=
  rule_exists .box code policy post initial
example : ∃ premise : Logic.Fml (0+wordCellCount (localExternalTypes ctx)),
    holds .box code policy post initial ↔ premise.holds
      (WordState.pack (n := 0) ⟨Fin.elim0,localWordCells ctx initial.1⟩) :=
  rule_sound .box code policy post initial

def ruleWitness : ∃ premise, Nonempty (Logic.Rule (formula .diamond code policy post initial) premise) :=
  rule_exists .diamond code policy post initial
#check @Solidity.Yul.LocalBlockLogic.holds_iff_raw
#check @Solidity.Yul.LocalBlockLogic.formula_iff
#check @Solidity.Yul.LocalBlockLogic.rule_sound
#print axioms Solidity.Yul.LocalBlockLogic.rule_sound
#print axioms box_post
theorem completed_modalities (mode : Solidity.Modality) :
    holds mode code policy post initial ↔ post completed :=
  completion_iff mode code policy post initial done

theorem completed_formula (mode : Solidity.Modality) :
    (formula mode code policy post initial).holds
      (WordState.pack (n := 0) ⟨Fin.elim0, localWordCells ctx initial.1⟩) :=
  (formula_completion_iff mode code policy post initial done).mpr completed_post

theorem completed_rule (mode : Solidity.Modality) :
    ∃ premise : Logic.Fml (0 + wordCellCount (localExternalTypes ctx)),
    ∃ _rule : Logic.Rule (formula mode code policy post initial) premise,
      premise.holds (WordState.pack (n := 0) ⟨Fin.elim0, localWordCells ctx initial.1⟩) := by
  obtain ⟨premise, rule, exactPost⟩ := rule_completion mode code policy post initial done
  exact ⟨premise, rule, exactPost.mpr completed_post⟩

example (mode : Solidity.Modality) :
    ¬ holds mode code policy (fun _ => False) initial := by
  intro impossible
  exact (completion_iff mode code policy (fun _ => False) initial done).mp impossible
#print axioms completed_modalities
#print axioms completed_formula
#print axioms completed_rule

end Solidity.Yul.Checks.LocalBlockLogic
