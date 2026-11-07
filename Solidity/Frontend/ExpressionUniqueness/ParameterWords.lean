import Solidity.Frontend.ExpressionUniqueness.ParameterIdentity
import Solidity.Frontend.ExpressionUniqueness.ArgumentWords
import Solidity.Frontend.ExpressionUniqueness.ExpressionMode

/-!
# Actual parameter words are nonempty at arbitrary list lengths

An empty type word cannot finish an operand from an unfinished state. This
existing unconditional printer invariant supplies parameter nonemptiness, so
function-type comma vectors require no additional producer premise.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem type_yield_nonemptyWord (ty : Syn .typeName) (initial final : List Choice)
    (items : List (List Tok)) (hy : ty.yield initial = some (items, final)) : items.flatten ≠ [] := by
  have done : ModeDone items.flatten := type_yield_modeDone ty initial items final hy
  intro empty
  have wrong := done false
  rw [empty] at wrong
  cases wrong

theorem word_append_nonempty_left (before after : List Tok) (h : before ≠ []) : before ++ after ≠ [] := by
  cases before with
  | nil => exact (h rfl).elim
  | cons t ts => intro empty; cases empty

theorem parameter_yield_nonemptyWord (param : Syn .param) (initial final : List Choice)
    (items : List (List Tok)) (hy : param.yield initial = some (items, final)) : items.flatten ≠ [] := by
  cases param with
  | param ty loc name =>
    obtain ⟨xs, hx, shape⟩ := parameter_yield_parts ty loc name initial final items hy
    rw [shape]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    exact word_append_nonempty_left _ _ (word_append_nonempty_left _ _
      (type_yield_nonemptyWord ty initial final xs hx))

def ParameterVectorProperty {c : Cat} (e : Syn c) : Prop :=
  match c with
  | .list .param => Produces e.yield NonemptyWords
  | _ => True

theorem parameter_vector_property {c : Cat} (e : Syn c) : ParameterVectorProperty e := by
  induction e with
  | @nil c =>
    cases c <;> first
      | trivial
      | exact produces_pure _ _ (by intro word member; cases member)
  | @cons c head tail ihHead ihTail =>
    cases c with
    | param =>
      apply produces_bind head.yield _ (fun items => items.flatten ≠ []) NonemptyWords
        (fun initial items final hy => parameter_yield_nonemptyWord head initial final items hy)
      intro first hf
      apply produces_bind tail.yield _ NonemptyWords NonemptyWords ihTail
      intro rest hr
      apply produces_pure
      intro word member
      rcases List.mem_cons.mp member with equal | inside
      · exact equal ▸ hf
      · exact hr word inside
    | _ => trivial
  | _ => trivial

theorem parameterList_yield_nonemptyWords (params : Syn (.list .param)) (initial final : List Choice)
    (items : List (List Tok)) (hy : params.yield initial = some (items, final)) : NonemptyWords items :=
  parameter_vector_property params initial items final hy

end Solidity.Frontend.ExpressionUniqueness
