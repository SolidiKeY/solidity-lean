import Solidity.Yul.WordAdapterLogic
import Solidity.Yul.Checks.WordAdapterFixtures
set_option Elab.async false
namespace Solidity.Yul.Checks.RawWordLogic
open Solidity.Yul.Checks.WordAdapter

def code : Stmt [] types ClosedSyntax.rootControl 0 :=
  .assign (fun _ : Fin 1 => .external x.writeRef) (.literal (word 257))
def policy : Policy.StmtP .A code := ⟨fun _ => True.intro,True.intro⟩
def initialState : WordState types 0 := ⟨Fin.elim0,initial⟩
theorem completed : (Solidity.Yul.WordAdapter.run code policy 2 initialState).isSome = true := by decide
def result := (Solidity.Yul.WordAdapter.run code policy 2 initialState).get completed
theorem finished : Solidity.Yul.WordAdapter.run code policy 2 initialState = some result :=
  (Option.some_get completed).symm
theorem dirty_x : result.state.cells x = word 257 := by decide
theorem dirty_flag : result.state.cells flag = word 2 := by decide
theorem address_zero : result.state.cells (.address ptr) = word 0 := by decide
theorem selector_zero : result.state.cells (.selector ptr) = word 0 := by decide
def post (out : Solidity.Yul.WordAdapter.Outcome types ClosedSyntax.rootControl 0) : Prop :=
  out.state.cells x = word 257 ∧ out.state.cells flag = word 2 ∧
  out.state.cells (.address ptr) = word 0 ∧ out.state.cells (.selector ptr) = word 0
theorem valid : post result := ⟨dirty_x,dirty_flag,address_zero,selector_zero⟩
theorem diamond : Solidity.Yul.WordAdapter.rawHolds .diamond code policy post initialState :=
  ⟨2,result,finished,valid⟩
theorem box_ : Solidity.Yul.WordAdapter.rawHolds .box code policy post initialState := by
  intro fuel out done
  have same := Solidity.Yul.WordAdapter.run_completed_unique code policy initialState done finished
  rw [same]
  exact valid
example : (Solidity.Yul.WordAdapter.formula .box code policy post).holds initialState.pack :=
  (Solidity.Yul.WordAdapter.formula_iff .box code policy post initialState).mpr box_
example : (Solidity.Yul.WordAdapter.formula .diamond code policy post).holds initialState.pack :=
  (Solidity.Yul.WordAdapter.formula_iff .diamond code policy post initialState).mpr diamond
example : ¬ Solidity.Yul.WordAdapter.rawHolds .box code policy (fun _ => False) initialState :=
  fun invalid => invalid 2 result finished
example : ¬ Solidity.Yul.WordAdapter.rawHolds .diamond code policy (fun _ => False) initialState := by
  rintro ⟨_,_,_,bad⟩
  exact bad
example (mode : Solidity.Modality) :
    ∃ premise, Nonempty (Logic.Rule (Solidity.Yul.WordAdapter.formula mode code policy post) premise) :=
  Solidity.Yul.WordAdapter.rule_exists mode code policy post
example (mode : Solidity.Modality) :
    ∃ premise : Logic.Fml (0+wordCellCount types), ∀ state : WordState types 0,
      Solidity.Yul.WordAdapter.rawHolds mode code policy post state ↔
        premise.holds state.pack :=
  Solidity.Yul.WordAdapter.rule_sound mode code policy post

def witness : Nonempty (Solidity.Yul.WordAdapter.Outcome types ClosedSyntax.rootControl 0) := ⟨result⟩
end Solidity.Yul.Checks.RawWordLogic
