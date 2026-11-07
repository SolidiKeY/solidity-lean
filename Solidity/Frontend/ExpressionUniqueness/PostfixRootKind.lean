import Solidity.Source.Ctor
import Solidity.Frontend.ExpressionUniqueness.PostfixSpans
import Solidity.Frontend.ExpressionUniqueness.MemberSpans

/-!
# The five postfix constructor families reconstruct from actual words

Trailing punctuation separates calls, options, members and square postfixes.
The established conditional-colon theorem separates index from slice. These
natural-number tags classify existing intrinsic roots; they contain no AST.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def postfixRootKind (e : Syn .expr) : Nat :=
  match e.ctor with
  | .index => 0 | .slice => 1 | .member => 2
  | .callOptions => 3 | .call => 4 | _ => 5

def postfixEndCode : Nat → Nat
  | 0 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | _ => 4

def tokenEndClass : Tok → Nat
  | .punct .rbrack => 0 | .punct .rbrace => 1 | .punct .rparen => 2
  | .ident _ | .elem .address => 3 | _ => 4

def PostfixEnd (tag : Nat) (items : List (List Tok)) : Prop :=
  ∃ prefixWord token, items.flatten = prefixWord ++ [token] ∧ tokenEndClass token = tag

theorem final_token_unique (xs ys : List Tok) (t u : Tok) (he : xs ++ [t] = ys ++ [u]) : t = u := by
  have lengths : xs.length = ys.length := by
    have total := congrArg List.length he
    simp only [List.length_append, List.length_cons, List.length_nil] at total
    exact Nat.add_right_cancel total
  exact (List.cons.inj (List.append_inj he lengths).2).1

theorem postfixEnd_unique (tag tag' : Nat) (items items' : List (List Tok))
    (h : PostfixEnd tag items) (h' : PostfixEnd tag' items')
    (words : items.flatten = items'.flatten) : tag = tag' := by
  obtain ⟨prefixWord, token, shape, code⟩ := h
  obtain ⟨prefixWord', token', shape', code'⟩ := h'
  rw [shape, shape'] at words
  have tokens : token = token' := final_token_unique prefixWord prefixWord' token token' words
  exact code.symm.trans ((congrArg tokenEndClass tokens).trans code')

theorem index_yield_postfixEnd (base : Syn .expr) (index : Syn (.opt .expr))
    (initial final : List Choice) (items : List (List Tok))
    (hy : (Syn.index base index).yield initial = some (items, final)) : PostfixEnd 0 items := by
  obtain ⟨xs, ys, middle, hx, hi, shape⟩ := index_yield_parts base index initial final items hy
  refine ⟨xs.flatten ++ pu .lbrack ++ ys.flatten, .punct .rbrack, ?_, rfl⟩
  rw [shape]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu]

theorem slice_yield_postfixEnd (base : Syn .expr) (start stop : Syn (.opt .expr))
    (initial final : List Choice) (items : List (List Tok))
    (hy : (Syn.slice base start stop).yield initial = some (items, final)) : PostfixEnd 0 items := by
  obtain ⟨xs, ys, zs, middle, next, hx, hs, ht, shape⟩ := slice_yield_parts base start stop initial final items hy
  refine ⟨xs.flatten ++ pu .lbrack ++ ys.flatten ++ pu .colon ++ zs.flatten, .punct .rbrack, ?_, rfl⟩
  rw [shape]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu]

theorem member_yield_postfixEnd (base : Syn .expr) (name : String)
    (initial final : List Choice) (items : List (List Tok))
    (hy : (Syn.member base name).yield initial = some (items, final)) : PostfixEnd 3 items := by
  obtain ⟨xs, hx, shape⟩ := member_yield_parts base name initial final items hy
  refine ⟨xs.flatten ++ pu .period, memberToken name, ?_, ?_⟩
  · rw [shape]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  · unfold memberToken
    split <;> rfl

theorem options_yield_postfixEnd (base : Syn .expr) (first : Syn .namedArg) (args : Syn (.list .namedArg))
    (initial final : List Choice) (items : List (List Tok))
    (hy : (Syn.callOptions base first args).yield initial = some (items, final)) : PostfixEnd 1 items := by
  obtain ⟨xs, ys, zs, middle, next, hx, hf, ha, shape⟩ := options_yield_parts base first args initial final items hy
  refine ⟨xs.flatten ++ pu .lbrace ++ commaSep (ys.flatten :: zs), .punct .rbrace, ?_, rfl⟩
  rw [shape]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, braces, pu,
    List.append_assoc, List.singleton_append]

theorem call_yield_postfixEnd (base : Syn .expr) (args : Syn .callArgs)
    (initial final : List Choice) (items : List (List Tok))
    (hy : (Syn.call base args).yield initial = some (items, final)) : PostfixEnd 2 items := by
  obtain ⟨xs, ys, middle, hx, ha, shape⟩ := call_yield_parts base args initial final items hy
  obtain ⟨payload, argShape, bal⟩ := callArgs_yield_parens args middle final ys ha
  refine ⟨xs.flatten ++ pu .lparen ++ payload, .punct .rparen, ?_, rfl⟩
  rw [shape, argShape]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, parens, pu,
    List.append_assoc, List.singleton_append]

theorem expr_level_fifteen_cases (e : Syn .expr) (hl : e.level = 15) :
    (∃ base index, e = Syn.index base index) ∨
    (∃ base start stop, e = Syn.slice base start stop) ∨
    (∃ base name, e = Syn.member base name) ∨
    (∃ base first args, e = Syn.callOptions base first args) ∨
    (∃ base args, e = Syn.call base args) := by
  cases e with
  | index base index => exact Or.inl ⟨base, index, rfl⟩
  | slice base start stop => exact Or.inr (Or.inl ⟨base, start, stop, rfl⟩)
  | member base name => exact Or.inr (Or.inr (Or.inl ⟨base, name, rfl⟩))
  | callOptions base first args => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨base, first, args, rfl⟩)))
  | call base args => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨base, args, rfl⟩)))
  | payableConv => exact ((by decide : 16 ≠ 15) hl).elim
  | metaType => exact ((by decide : 16 ≠ 15) hl).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 15) hl).elim
  | unarySuffix => exact ((by decide : 14 ≠ 15) hl).elim
  | exp => exact ((by decide : 12 ≠ 15) hl).elim
  | mulDivMod => exact ((by decide : 11 ≠ 15) hl).elim
  | addSub => exact ((by decide : 10 ≠ 15) hl).elim
  | shift => exact ((by decide : 9 ≠ 15) hl).elim
  | bitAnd => exact ((by decide : 8 ≠ 15) hl).elim
  | bitXor => exact ((by decide : 7 ≠ 15) hl).elim
  | bitOr => exact ((by decide : 6 ≠ 15) hl).elim
  | order => exact ((by decide : 5 ≠ 15) hl).elim
  | equality => exact ((by decide : 4 ≠ 15) hl).elim
  | and => exact ((by decide : 3 ≠ 15) hl).elim
  | or => exact ((by decide : 2 ≠ 15) hl).elim
  | cond => exact ((by decide : 1 ≠ 15) hl).elim
  | assign => exact ((by decide : 0 ≠ 15) hl).elim
  | new => exact ((by decide : 16 ≠ 15) hl).elim
  | tuple => exact ((by decide : 16 ≠ 15) hl).elim
  | inlineArray => exact ((by decide : 16 ≠ 15) hl).elim
  | ident => exact ((by decide : 16 ≠ 15) hl).elim
  | lit => exact ((by decide : 16 ≠ 15) hl).elim
  | litUnit => exact ((by decide : 16 ≠ 15) hl).elim
  | elemType => exact ((by decide : 16 ≠ 15) hl).elim

theorem postfix_yield_end (e : Syn .expr) (initial final : List Choice) (items : List (List Tok))
    (hl : e.level = 15) (hy : e.yield initial = some (items, final)) :
    PostfixEnd (postfixEndCode (postfixRootKind e)) items := by
  rcases expr_level_fifteen_cases e hl with ⟨base, index, rfl⟩ | ⟨base, start, stop, rfl⟩ |
    ⟨base, name, rfl⟩ | ⟨base, first, args, rfl⟩ | ⟨base, args, rfl⟩
  · exact index_yield_postfixEnd base index initial final items hy
  · exact slice_yield_postfixEnd base start stop initial final items hy
  · exact member_yield_postfixEnd base name initial final items hy
  · exact options_yield_postfixEnd base first args initial final items hy
  · exact call_yield_postfixEnd base args initial final items hy

theorem partial_postfix_root_kinds_equal (a b : Syn .expr)
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (ha : a.level = 15) (hb : b.level = 15)
    (hy : a.yield initial = some (items, final)) (hy' : b.yield initial' = some (items', final'))
    (words : items.flatten = items'.flatten) : postfixRootKind a = postfixRootKind b := by
  have ends : postfixEndCode (postfixRootKind a) = postfixEndCode (postfixRootKind b) :=
    postfixEnd_unique _ _ items items' (postfix_yield_end a initial final items ha hy)
      (postfix_yield_end b initial' final' items' hb hy') words
  rcases expr_level_fifteen_cases a ha with ⟨base, index, rfl⟩ | ⟨base, start, stop, rfl⟩ |
    ⟨base, name, rfl⟩ | ⟨base, first, args, rfl⟩ | ⟨base, args, rfl⟩ <;>
    rcases expr_level_fifteen_cases b hb with ⟨base', index', rfl⟩ | ⟨base', start', stop', rfl⟩ |
      ⟨base', name', rfl⟩ | ⟨base', first', args', rfl⟩ | ⟨base', args', rfl⟩
  all_goals first | rfl | (cases ends; done) | skip
  all_goals first
    | exact False.elim (index_slice_yields_disjoint _ _ _ _ _ _ _ _ _ _ _ hy hy' words)
    | exact False.elim (index_slice_yields_disjoint _ _ _ _ _ _ _ _ _ _ _ hy' hy words.symm)

end Solidity.Frontend.ExpressionUniqueness
