import Solidity.Frontend.ExpressionUniqueness.Refusals
import Solidity.Frontend.Checked.Print

/-!
# Arbitrary-size inhabited expression controls

Unbounded negative-prefix and grouping families use the original intrinsic
syntax, with exact token yields and whole-certificate precedence witnesses.
They are controls for the uniqueness project, not a proof of its main target.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def negFamily : Nat → String → Syn .expr
  | 0, name => .ident name
  | n + 1, name => .unaryPrefix .neg (negFamily n name)

def negTokens : Nat → String → List Tok
  | 0, name => [.ident name]
  | n + 1, name => .punct .sub :: negTokens n name

theorem negFamily_prec (n : Nat) (name : String) : (negFamily n name).prec = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ha : (negFamily n name).all Syn.precNode = true := by
      have hi := ih
      simp only [Syn.prec, Bool.and_eq_true] at hi
      exact hi.2
    have hr : (Syn.unaryPrefix .neg (negFamily n name)).precNode = true := by
      cases n <;> rfl
    change (Syn.unaryPrefix .neg (negFamily n name)).prec = true
    simp only [Syn.prec, Syn.all, hr, ha, Bool.and_self]

theorem prefix_yield (op : PrefixOp) (e : Syn .expr) (L rest : List Choice)
    (items : List (List Tok)) (h : e.yield L = some (items, rest)) :
    (Syn.unaryPrefix op e).yield L = some ([op.punct ++ items.flatten], rest) := by
  change ((e.yield L).bind fun r => some ([op.punct ++ r.1.flatten], r.2)) = _
  rw [h]
  rfl

theorem negFamily_yield (n : Nat) (name : String) (rest : List Choice) :
    (negFamily n name).yield rest = some ([negTokens n name], rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Syn.unaryPrefix .neg (negFamily n name)).yield rest = _
    simpa only [PrefixOp.punct, pu, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.singleton_append, negTokens] using
      prefix_yield .neg (negFamily n name) rest rest [negTokens n name] ih

theorem negFamily_toks (n : Nat) (name : String) :
    (negFamily n name).toks [] = some (negTokens n name) := by
  simp only [Syn.toks, negFamily_yield, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem negFamily_certified (n : Nat) (name : String) :
    (negFamily n name).Derives (negTokens n name) ∧ (negFamily n name).prec = true :=
  ⟨⟨[], negFamily_toks n name⟩, negFamily_prec n name⟩

theorem negTokens_length (n : Nat) (name : String) : (negTokens n name).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [negTokens, List.length_cons, ih]

theorem negFamily_injective (name : String) {n m : Nat}
    (h : negFamily n name = negFamily m name) : n = m := by
  have ht := congrArg (fun e => e.toks []) h
  change (negFamily n name).toks [] = (negFamily m name).toks [] at ht
  rw [negFamily_toks, negFamily_toks] at ht
  have hl := congrArg List.length (Option.some.inj ht)
  rw [negTokens_length, negTokens_length] at hl
  exact Nat.add_right_cancel hl

def group (e : Syn .expr) : Syn .expr := .tuple (.some e) .nil

theorem group_prec {e : Syn .expr} (h : e.prec = true) : (group e).prec = true := by
  have ha : e.all Syn.precNode = true := by
    have hi := h
    simp only [Syn.prec, Bool.and_eq_true] at hi
    exact hi.2
  simp only [group, Syn.prec, Syn.precNode, Syn.all, ha, Bool.and_self]

def groupFamily : Nat → Syn .expr → Syn .expr
  | 0, e => e
  | n + 1, e => group (groupFamily n e)

theorem groupFamily_prec (n : Nat) {e : Syn .expr} (h : e.prec = true) :
    (groupFamily n e).prec = true := by
  induction n with
  | zero => exact h
  | succ n ih => exact group_prec ih

end Solidity.Frontend.ExpressionUniqueness
