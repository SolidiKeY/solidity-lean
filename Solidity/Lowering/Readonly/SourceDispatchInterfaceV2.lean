import Solidity.Lowering.Readonly.SourceDispatchEffects

/-! H69 reachable dispatch interface V2. V1 remains frozen in
SourceDispatchEffects; no Source evaluator or admission rule changes here. -/
namespace Solidity.Lowering.Readonly.SourceDispatchV2
open Solidity.Source Solidity.Roadmap
variable {E : Env}

theorem selector_length (G : Glob E) (signature : List Char) :
    (G.selector signature).length = 4 := by
  simp only [Glob.selector, List.length_take, wordBytes_length]
  rfl

theorem selector_ne_empty (G : Glob E) (signature : List Char) :
    G.selector signature ≠ [] := by
  intro same
  have length := congrArg List.length same
  rw [selector_length] at length
  exact Nat.noConfusion length

theorem pickFn_empty (G : Glob E) (F : Fr) : G.pickFn F [] = none := by
  apply List.find?_eq_none.mpr
  intro d member selected
  have matched := (Bool.and_eq_true_iff.mp selected).2
  cases sig : d.fnSig E with
  | none => simp only [sig, Bool.false_eq_true] at matched
  | some signature =>
    simp only [sig, List.take_nil] at matched
    exact selector_ne_empty G _ (beq_iff_eq.mp matched)

theorem pickGetter_empty (G : Glob E) (F : Fr) : G.pickGetter F [] = none := by
  apply List.find?_eq_none.mpr
  intro d member selected
  rcases d with ⟨declaration, parameters, returns⟩
  have nonempty : false = true := (Bool.and_eq_true_iff.mp selected).1
  exact Bool.noConfusion nonempty

/-- Every constructor corresponds to a reachable evaluator branch. Empty
input has only the special-function branch; selection/ABI failure remains in it. -/
inductive Selection (G : Glob E) (F : Fr) (input : Bytes) where
  | function (declaration : Decl) (selected : G.pickFn F input = some declaration)
      (nonempty : input.isEmpty = false)
  | getter (declaration : Decl) (parameters : List STy) (returns : STy)
      (noFunction : G.pickFn F input = none)
      (selected : G.pickGetter F input = some (declaration, parameters, returns))
  | special (noFunction : G.pickFn F input = none)
      (noGetter : G.pickGetter F input = none)

/-- A real function selection proves the input is nonempty. -/
theorem selected_nonempty (G : Glob E) (F : Fr) (input : Bytes) (d : Decl)
    (selected : G.pickFn F input = some d) : input.isEmpty = false := by
  cases input with
  | nil => rw [pickFn_empty] at selected; cases selected
  | cons byte rest => rfl

def classify (G : Glob E) (F : Fr) (input : Bytes) : Selection G F input := by
  cases selected : G.pickFn F input with
  | some d => exact .function d selected (selected_nonempty G F input d selected)
  | none =>
    cases getter : G.pickGetter F input with
    | some result => exact .getter result.1 result.2.1 result.2.2 selected getter
    | none => exact .special selected getter

/-- V2 consumer uses only inhabited branch shapes, never V1 empty-selected cases. -/
theorem dispatch_succ (G : Glob E) (F : Fr) (n : Nat)
    (history : SourceHistory.At G n) (input : Bytes) :
    SourceHistory.Effect F.static (dispatch G F (n+1) input) := by
  cases classify G F input with
  | function d selected nonempty =>
    exact SourceHistory.dispatch_function_succ G F n history input d selected nonempty
  | getter d ps r absent selected =>
    exact SourceHistory.dispatch_getter_no_function_succ G F n history input d ps r absent selected
  | special absent selected =>
    exact SourceHistory.dispatch_special_no_function_succ G F n history input absent selected

end Solidity.Lowering.Readonly.SourceDispatchV2
