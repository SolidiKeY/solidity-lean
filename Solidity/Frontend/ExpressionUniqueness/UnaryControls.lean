import Solidity.Frontend.ExpressionUniqueness.UnaryRoot
import Solidity.Frontend.ExpressionUniqueness.Grouping

/-!
# Inhabited arbitrary unary-chain controls

Every prefix operator has arbitrary direct nesting. Every suffix operator has
arbitrary nesting with the grouping required by the original certificate. No
frozen ungrouped refusal is relaxed. Exact tokens and nonvacuous markers follow.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def prefixChain (op : PrefixOp) : Nat → Syn .expr
  | 0 => .ident "a"
  | n + 1 => .unaryPrefix op (prefixChain op n)

def prefixChainTokens (op : PrefixOp) : Nat → List Tok
  | 0 => [.ident "a"]
  | n + 1 => prefixToken op :: prefixChainTokens op n

theorem prefixChain_prec (op : PrefixOp) (n : Nat) : (prefixChain op n).prec = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hall : (prefixChain op n).all Syn.precNode = true := (Bool.and_eq_true_iff.mp ih).2
    have root : (Syn.unaryPrefix op (prefixChain op n)).precNode = true := by cases n <;> rfl
    change (Syn.unaryPrefix op (prefixChain op n)).prec = true
    simp only [Syn.prec, Syn.all, root, hall, Bool.and_self]

theorem prefixChain_yield (op : PrefixOp) (n : Nat) (rest : List Choice) :
    (prefixChain op n).yield rest = some ([prefixChainTokens op n], rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [prefixChain, prefixChainTokens, prefix_word_single, List.singleton_append,
      List.flatten_cons, List.flatten_nil, List.append_nil] using
      prefix_yield op (prefixChain op n) rest rest [prefixChainTokens op n] ih

theorem prefixChain_certified (op : PrefixOp) (n : Nat) :
    (prefixChain op n).Derives (prefixChainTokens op n) ∧ (prefixChain op n).prec = true :=
  ⟨⟨[], (expr_toks_iff _ [] _).mpr (prefixChain_yield op n [])⟩, prefixChain_prec op n⟩

theorem prefixChain_marker (op : PrefixOp) (n : Nat) :
    firstTop unaryMarker [] (prefixChainTokens op (n + 1)) = some (0, prefixToken op) := by
  cases op <;> rfl

def suffixChain (op : SuffixOp) : Nat → Syn .expr
  | 0 => .ident "a"
  | n + 1 => .unarySuffix op (group (suffixChain op n))

def suffixChainTokens (op : SuffixOp) : Nat → List Tok
  | 0 => [.ident "a"]
  | n + 1 => parens (suffixChainTokens op n) ++ pu op.punct

theorem suffixChain_prec (op : SuffixOp) (n : Nat) : (suffixChain op n).prec = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hall : (group (suffixChain op n)).all Syn.precNode = true :=
      (Bool.and_eq_true_iff.mp (group_prec ih)).2
    have root : (Syn.unarySuffix op (group (suffixChain op n))).precNode = true := rfl
    change (Syn.unarySuffix op (group (suffixChain op n))).prec = true
    simp only [Syn.prec, Syn.all, root, hall, Bool.and_self]

theorem suffixChain_yield (op : SuffixOp) (n : Nat) (rest : List Choice) :
    (suffixChain op n).yield rest = some ([suffixChainTokens op n], rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have grouped : (group (suffixChain op n)).yield rest = some ([parens (suffixChainTokens op n)], rest) := by
      rw [group_yield_map, ih]
      simp only [Option.map_some, List.flatten_cons, List.flatten_nil, List.append_nil]
    change ((group (suffixChain op n)).yield rest).bind (fun r =>
      some ([r.1.flatten ++ pu op.punct], r.2)) = _
    rw [grouped]
    simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil, suffixChainTokens]

theorem suffixChain_certified (op : SuffixOp) (n : Nat) :
    (suffixChain op n).Derives (suffixChainTokens op n) ∧ (suffixChain op n).prec = true :=
  ⟨⟨[], (expr_toks_iff _ [] _).mpr (suffixChain_yield op n [])⟩, suffixChain_prec op n⟩

theorem suffixChainTokens_length (op : SuffixOp) (n : Nat) :
    (suffixChainTokens op n).length = 3 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [suffixChainTokens, parens, pu, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem suffixChain_marker (op : SuffixOp) (n : Nat) :
    ∃ position, 0 < position ∧ firstTop unaryMarker [] (suffixChainTokens op (n + 1)) =
      some (position, .punct op.punct) := by
  have result := suffix_yield_firstUnary op (group (suffixChain op n)) [] []
    [suffixChainTokens op (n + 1)] (suffixChain_prec op (n + 1)) (suffixChain_yield op (n + 1) [])
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using result

theorem ungrouped_suffix_chain_refused (op op' : SuffixOp) (a : Syn .expr) :
    (Syn.unarySuffix op (Syn.unarySuffix op' a)).prec = false := by
  rfl

end Solidity.Frontend.ExpressionUniqueness
