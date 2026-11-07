import Solidity.Source.Ctor
import Solidity.Frontend.ExpressionUniqueness.TypeYieldSplit

/-!
# Actual type yields decompose into an existing atom and square payload words

The atom is an existing intrinsic typeName node. The list stores only delimiter
payload token words, not an alternative syntax tree. Every payload's balance
and the atom's successful execution are derived from the actual original yield.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def isTypeAtom (ty : Syn .typeName) : Bool :=
  match ty.ctor with
  | .array => false
  | _ => true

def TypeSpineProperty {c : Cat} (e : Syn c) : Prop :=
  match c with
  | .typeName => ∀ initial items final, e.yield initial = some (items, final) →
      ∃ atom atomItems atomFinal payloads,
        isTypeAtom atom = true ∧ atom.yield initial = some (atomItems, atomFinal) ∧
        BalancedItems payloads ∧ items.flatten = atomItems.flatten ++ squareWords payloads
  | _ => True

theorem type_spine_property {c : Cat} (e : Syn c) : TypeSpineProperty e := by
  induction e with
  | elem value =>
    intro initial items final hy
    exact ⟨Syn.elem value, items, final, [], rfl, hy, balancedItems_nil, by rw [squareWords_nil, List.append_nil]⟩
  | userType path =>
    intro initial items final hy
    exact ⟨Syn.userType path, items, final, [], rfl, hy, balancedItems_nil, by rw [squareWords_nil, List.append_nil]⟩
  | mapping key keyName value valueName ih =>
    intro initial items final hy
    exact ⟨Syn.mapping key keyName value valueName, items, final, [], rfl, hy, balancedItems_nil,
      by rw [squareWords_nil, List.append_nil]⟩
  | fnType params vis mu returns ihParams ihReturns =>
    intro initial items final hy
    exact ⟨Syn.fnType params vis mu returns, items, final, [], rfl, hy, balancedItems_nil,
      by rw [squareWords_nil, List.append_nil]⟩
  | array base length ihBase ihLength =>
    intro initial items final hy
    obtain ⟨xs, ys, middle, hb, hl, shape⟩ := array_type_yield_parts base length initial final items hy
    obtain ⟨atom, atomItems, atomFinal, payloads, atomKind, atomYield, payloadBalance, baseWord⟩ :=
      ihBase initial xs middle hb
    have lengthBalance : Balanced ys.flatten := balancedItems_flatten
      (expressionCategory_yield_balanced length rfl middle ys final hl)
    refine ⟨atom, atomItems, atomFinal, payloads ++ [ys.flatten], atomKind, atomYield, ?_, ?_⟩
    · intro word hw
      rcases List.mem_append.mp hw with old | last
      · exact payloadBalance word old
      · exact (List.mem_singleton.mp last) ▸ lengthBalance
    · rw [shape]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [baseWord, squareWords_append, squareWords_cons, squareWords_nil]
      simp only [List.append_nil, List.append_assoc]
  | _ => trivial

theorem type_yield_spine (e : Syn .typeName) (initial final : List Choice) (items : List (List Tok))
    (hy : e.yield initial = some (items, final)) :
    ∃ atom atomItems atomFinal payloads,
      isTypeAtom atom = true ∧ atom.yield initial = some (atomItems, atomFinal) ∧
      BalancedItems payloads ∧ items.flatten = atomItems.flatten ++ squareWords payloads :=
  type_spine_property e initial items final hy

end Solidity.Frontend.ExpressionUniqueness
