import Solidity.Source.Ctor
import Solidity.Frontend.Checked.Prec
import Solidity.Frontend.ExpressionUniqueness.PrimaryPrefixParts

/-!
# Actual primary first-token classes

The existing unindexed constructor enumeration distinguishes primary families.
Literal and unit primaries share a header class; their follower-sensitive
separation is proved separately, rather than assumed by this classifier.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def primaryRootKind (e : Syn .expr) : Nat :=
  match e.ctor with
  | .new => 0 | .metaType => 1 | .payableConv => 2 | .tuple => 3
  | .inlineArray => 4 | .ident => 5 | .elemType => 6 | .lit | .litUnit => 7 | _ => 8

def primaryTokenKind : Tok → Nat
  | .kw .new => 0 | .kw .type_ => 1 | .kw .payable => 2
  | .punct .lparen => 3 | .punct .lbrack => 4 | .ident _ => 5 | .elem _ => 6
  | .bool _ | .num _ | .str _ | .hexStr _ | .unicodeStr _ => 7 | _ => 8

def PrimaryStart (tag : Nat) (items : List (List Tok)) : Prop :=
  ∃ token rest, items.flatten = token :: rest ∧ primaryTokenKind token = tag

theorem literalToken_primaryKind (token : Tok) (kind : Nat)
    (h : tokenLiteralKind token = some kind) : primaryTokenKind token = 7 := by
  cases token <;> first | rfl | cases h

theorem primary_yield_start (e : Syn .expr) (initial final : List Choice)
    (items : List (List Tok)) (hl : e.level = 16)
    (hy : e.yield initial = some (items, final)) : PrimaryStart (primaryRootKind e) items := by
  cases e with
  | new ty =>
    obtain ⟨payload, hx, shape⟩ := new_yield_parts ty initial final items hy
    unfold PrimaryStart
    rw [shape]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, tk, List.singleton_append]
    exact ⟨.kw .new, _, rfl, rfl⟩
  | metaType ty =>
    obtain ⟨payload, bal, shape⟩ := meta_actual_parens ty initial final items hy
    unfold PrimaryStart
    rw [shape]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, tk, List.singleton_append]
    exact ⟨.kw .type_, _, rfl, rfl⟩
  | payableConv args =>
    obtain ⟨payload, bal, shape⟩ := payable_actual_parens args initial final items hy
    unfold PrimaryStart
    rw [shape]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, tk, List.singleton_append]
    exact ⟨.kw .payable, _, rfl, rfl⟩
  | tuple first rest =>
    obtain ⟨payload, bal, shape⟩ := tuple_actual_parens first rest initial final items hy
    unfold PrimaryStart
    rw [shape]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, parens, pu, List.singleton_append]
    exact ⟨.punct .lparen, _, rfl, rfl⟩
  | inlineArray first rest =>
    obtain ⟨payload, bal, shape⟩ := inline_actual_square first rest initial final items hy
    unfold PrimaryStart
    rw [shape]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pu, List.singleton_append]
    exact ⟨.punct .lbrack, _, rfl, rfl⟩
  | ident name =>
    have shape : items = [idt name] := (pure_success_split [idt name] items initial final hy).1
    unfold PrimaryStart
    rw [shape]
    exact ⟨.ident name, [], rfl, rfl⟩
  | elemType ty allowed =>
    have shape : items = [[.elem ty]] := (pure_success_split [[Tok.elem ty]] items initial final hy).1
    unfold PrimaryStart
    rw [shape]
    exact ⟨.elem ty, [], rfl, rfl⟩
  | lit l =>
    obtain ⟨token, rest, shape, kind⟩ := literal_head_kind l items.flatten
      (expression_partial_derives _ initial final items hy)
    exact ⟨token, rest, shape, literalToken_primaryKind token (literalKind l) kind⟩
  | litUnit n u =>
    have shape : items = [[.num n, .denom u]] :=
      (pure_success_split [[Tok.num n, .denom u]] items initial final hy).1
    unfold PrimaryStart
    rw [shape]
    exact ⟨.num n, [.denom u], rfl, rfl⟩
  | index => exact ((by decide : 15 ≠ 16) hl).elim
  | slice => exact ((by decide : 15 ≠ 16) hl).elim
  | member => exact ((by decide : 15 ≠ 16) hl).elim
  | callOptions => exact ((by decide : 15 ≠ 16) hl).elim
  | call => exact ((by decide : 15 ≠ 16) hl).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 16) hl).elim
  | unarySuffix => exact ((by decide : 14 ≠ 16) hl).elim
  | exp => exact ((by decide : 12 ≠ 16) hl).elim
  | mulDivMod => exact ((by decide : 11 ≠ 16) hl).elim
  | addSub => exact ((by decide : 10 ≠ 16) hl).elim
  | shift => exact ((by decide : 9 ≠ 16) hl).elim
  | bitAnd => exact ((by decide : 8 ≠ 16) hl).elim
  | bitXor => exact ((by decide : 7 ≠ 16) hl).elim
  | bitOr => exact ((by decide : 6 ≠ 16) hl).elim
  | order => exact ((by decide : 5 ≠ 16) hl).elim
  | equality => exact ((by decide : 4 ≠ 16) hl).elim
  | and => exact ((by decide : 3 ≠ 16) hl).elim
  | or => exact ((by decide : 2 ≠ 16) hl).elim
  | cond => exact ((by decide : 1 ≠ 16) hl).elim
  | assign => exact ((by decide : 0 ≠ 16) hl).elim

theorem primary_prefix_kinds_equal (a b : Syn .expr)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (ha : a.level = 16) (hb : b.level = 16)
    (hy : a.yield initial = some (items, final)) (hy' : b.yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') : primaryRootKind a = primaryRootKind b := by
  obtain ⟨token, rest, shape, code⟩ := primary_yield_start a initial final items ha hy
  obtain ⟨token', rest', shape', code'⟩ := primary_yield_start b initial' final' items' hb hy'
  rw [shape, shape'] at words
  have tokens : token = token' := (List.cons.inj words).1
  exact code.symm.trans ((congrArg primaryTokenKind tokens).trans code')

end Solidity.Frontend.ExpressionUniqueness
