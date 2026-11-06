import Solidity.Frontend.ExpressionUniqueness.PostfixYieldSplit
import Solidity.Frontend.ExpressionUniqueness.UnaryRoot

/-!
# Member and named-argument names and child words reconstruct

The existing special member spelling for address is injective, including all
arbitrary identifier strings. Actual child state executions are recovered.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def memberToken (name : String) : Tok :=
  if name = "address" then .elem .address else .ident name

theorem member_word_single (name : String) :
    (if name == "address" then [.elem .address] else idt name) = [memberToken name] := by
  by_cases h : name = "address" <;> simp only [memberToken, idt, beq_iff_eq, h, ↓reduceIte]

theorem memberToken_injective (name name' : String) (h : memberToken name = memberToken name') :
    name = name' := by
  by_cases ha : name = "address"
  · by_cases hb : name' = "address"
    · exact ha.trans hb.symm
    · simp only [memberToken, ha, hb, ↓reduceIte] at h
      cases h
  · by_cases hb : name' = "address"
    · simp only [memberToken, ha, hb, ↓reduceIte] at h
      cases h
    · simp only [memberToken, ha, hb, ↓reduceIte] at h
      exact Tok.ident.inj h

theorem member_yield_parts (base : Syn .expr) (name : String)
    (initial final : List Choice) (items : List (List Tok))
    (h : (Syn.member base name).yield initial = some (items, final)) :
    ∃ xs, base.yield initial = some (xs, final) ∧
      items = [xs.flatten ++ pu .period ++ [memberToken name]] := by
  obtain ⟨xs, hx, shape⟩ := one_pure_success_split base.yield
    (fun xs => [xs.flatten ++ pu .period ++ (if name == "address" then [.elem .address] else idt name)])
    initial final items h
  exact ⟨xs, hx, by simpa only [member_word_single] using shape⟩

theorem member_child_spans (base base' : Syn .expr) (name name' : String)
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (hy : (Syn.member base name).yield initial = some (items, final))
    (hy' : (Syn.member base' name').yield initial' = some (items', final'))
    (he : items.flatten = items'.flatten) :
    name = name' ∧ UnaryChildSpans base base' initial final initial' final' := by
  obtain ⟨xs, hx, shape⟩ := member_yield_parts base name initial final items hy
  obtain ⟨ys, hyb, shape'⟩ := member_yield_parts base' name' initial' final' items' hy'
  rw [shape, shape'] at he
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] at he
  have lengths : xs.flatten.length = ys.flatten.length := by
    have total := congrArg List.length he
    simp only [List.length_append, List.length_cons, List.length_nil] at total
    exact Nat.add_right_cancel total
  obtain ⟨child, names⟩ := List.append_inj he lengths
  have token : memberToken name = memberToken name' := (List.cons.inj (List.cons.inj names).2).1
  exact ⟨memberToken_injective name name' token, xs, ys, hx, hyb, child⟩

theorem namedArg_child_spans (name name' : String) (value value' : Syn .expr)
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (hy : (Syn.namedArg name value).yield initial = some (items, final))
    (hy' : (Syn.namedArg name' value').yield initial' = some (items', final'))
    (he : items.flatten = items'.flatten) :
    name = name' ∧ UnaryChildSpans value value' initial final initial' final' := by
  obtain ⟨xs, hx, shape⟩ := namedArg_yield_parts name value initial final items hy
  obtain ⟨ys, hyb, shape'⟩ := namedArg_yield_parts name' value' initial' final' items' hy'
  rw [shape, shape'] at he
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu, idt,
    List.cons_append, List.nil_append] at he
  obtain ⟨token, rest⟩ := List.cons.inj he
  exact ⟨Tok.ident.inj token, xs, ys, hx, hyb, (List.cons.inj rest).2⟩

end Solidity.Frontend.ExpressionUniqueness
