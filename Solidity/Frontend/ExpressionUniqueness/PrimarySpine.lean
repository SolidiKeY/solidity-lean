import Solidity.Frontend.ExpressionUniqueness.PostfixFollowers
import Solidity.Frontend.ExpressionUniqueness.MemberSpans

/-!
# Certified high expressions expose an existing primary and actual postfix word

The primary is an existing Syn.expr node with level16, never a second AST.
Every child execution is recovered from the actual parent success. The original
not-new checks derive the first follower restriction internally. Empty postfix
words occur only at the primary itself.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def PrimarySpine (e : Syn .expr) (initial : List Choice) (items : List (List Tok)) : Prop :=
  ∃ primary primaryItems primaryFinal suffix,
    primary.level = 16 ∧ primary.prec = true ∧ primary.yield initial = some (primaryItems, primaryFinal) ∧
    items.flatten = primaryItems.flatten ++ suffix ∧ PostfixFollower primary.isNew suffix ∧
    (suffix = [] → e = primary)

def PrimarySpineProperty {c : Cat} (e : Syn c) : Prop :=
  match c with
  | .expr => e.prec = true → 15 ≤ e.level → ∀ initial items final,
      e.yield initial = some (items, final) → PrimarySpine e initial items
  | _ => True

theorem primary_spine_property {c : Cat} (e : Syn c) : PrimarySpineProperty e := by
  induction e with
  | payableConv args ih =>
    intro hp _ initial items final hy
    exact ⟨Syn.payableConv args, items, final, [], rfl, hp, hy, by rw [List.append_nil],
      postfixFollower_nil _, by intro _; rfl⟩
  | metaType ty ih =>
    intro hp _ initial items final hy
    exact ⟨Syn.metaType ty, items, final, [], rfl, hp, hy, by rw [List.append_nil],
      postfixFollower_nil _, by intro _; rfl⟩
  | new ty ih =>
    intro hp _ initial items final hy
    exact ⟨Syn.new ty, items, final, [], rfl, hp, hy, by rw [List.append_nil],
      postfixFollower_nil _, by intro _; rfl⟩
  | tuple first rest ihFirst ihRest =>
    intro hp _ initial items final hy
    exact ⟨Syn.tuple first rest, items, final, [], rfl, hp, hy, by rw [List.append_nil],
      postfixFollower_nil _, by intro _; rfl⟩
  | inlineArray first rest ihFirst ihRest =>
    intro hp _ initial items final hy
    exact ⟨Syn.inlineArray first rest, items, final, [], rfl, hp, hy, by rw [List.append_nil],
      postfixFollower_nil _, by intro _; rfl⟩
  | ident name =>
    intro hp _ initial items final hy
    exact ⟨Syn.ident name, items, final, [], rfl, hp, hy, by rw [List.append_nil],
      postfixFollower_nil _, by intro _; rfl⟩
  | lit l =>
    intro hp _ initial items final hy
    exact ⟨Syn.lit l, items, final, [], rfl, hp, hy, by rw [List.append_nil],
      postfixFollower_nil _, by intro _; rfl⟩
  | litUnit n u =>
    intro hp _ initial items final hy
    exact ⟨Syn.litUnit n u, items, final, [], rfl, hp, hy, by rw [List.append_nil],
      postfixFollower_nil _, by intro _; rfl⟩
  | elemType ty allowed =>
    intro hp _ initial items final hy
    exact ⟨Syn.elemType ty allowed, items, final, [], rfl, hp, hy, by rw [List.append_nil],
      postfixFollower_nil _, by intro _; rfl⟩
  | index base index ihBase ihIndex =>
    intro hp _ initial items final hy
    have basePrec : base.prec = true := by
      apply all_prec_implies_prec base
      have hall : (Syn.index base index).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have baseLevel : 15 ≤ base.level := by
      have root : (Syn.index base index).precNode = true := Syn.prec_root hp
      simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at root
      exact root.1
    have notNew : base.isNew = false := by
      cases hn : base.isNew with
      | false => rfl
      | true =>
        have bad : (Syn.index base index).precNode = true := Syn.prec_root hp
        simp only [Syn.precNode, hn, Bool.not_true, Bool.and_false] at bad
        cases bad
    obtain ⟨baseItems, indexItems, middle, baseYield, indexYield, shape⟩ :=
      index_yield_parts base index initial final items hy
    obtain ⟨primary, primaryItems, primaryFinal, suffix, primaryLevel, primaryPrec, primaryYield,
      baseWord, follower, noFrames⟩ := ihBase basePrec baseLevel initial baseItems middle baseYield
    let frame : List Tok := pu .lbrack ++ indexItems.flatten ++ pu .rbrack
    have frameNonempty : frame ≠ [] := by
      intro empty
      change Tok.punct .lbrack :: _ = [] at empty
      cases empty
    have parentWord : items.flatten = baseItems.flatten ++ frame := by
      rw [shape]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, frame, List.append_assoc]
    refine ⟨primary, primaryItems, primaryFinal, suffix ++ frame, primaryLevel, primaryPrec,
      primaryYield, ?_, ?_, ?_⟩
    · rw [parentWord, baseWord, List.append_assoc]
    · apply postfixFollower_append _ suffix frame follower
      intro empty
      have same : base = primary := noFrames empty
      have primaryNotNew : primary.isNew = false := by rw [← same]; exact notNew
      exact postfixFollower_square _ _ primaryNotNew
    · intro empty
      exact False.elim (word_append_nonempty_right suffix frame frameNonempty empty)
  | slice base start stop ihBase ihStart ihStop =>
    intro hp _ initial items final hy
    have basePrec : base.prec = true := by
      apply all_prec_implies_prec base
      have hall : (Syn.slice base start stop).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.1.2
    have baseLevel : 15 ≤ base.level := by
      have root : (Syn.slice base start stop).precNode = true := Syn.prec_root hp
      simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at root
      exact root.1
    have notNew : base.isNew = false := by
      cases hn : base.isNew with
      | false => rfl
      | true =>
        have bad : (Syn.slice base start stop).precNode = true := Syn.prec_root hp
        simp only [Syn.precNode, hn, Bool.not_true, Bool.and_false] at bad
        cases bad
    obtain ⟨baseItems, startItems, stopItems, middle, next, baseYield, startYield, stopYield, shape⟩ :=
      slice_yield_parts base start stop initial final items hy
    obtain ⟨primary, primaryItems, primaryFinal, suffix, primaryLevel, primaryPrec, primaryYield,
      baseWord, follower, noFrames⟩ := ihBase basePrec baseLevel initial baseItems middle baseYield
    let frame : List Tok := pu .lbrack ++ (startItems.flatten ++ pu .colon ++ stopItems.flatten) ++ pu .rbrack
    have frameNonempty : frame ≠ [] := by
      intro empty
      change Tok.punct .lbrack :: _ = [] at empty
      cases empty
    have parentWord : items.flatten = baseItems.flatten ++ frame := by
      rw [shape]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, frame, List.append_assoc]
    refine ⟨primary, primaryItems, primaryFinal, suffix ++ frame, primaryLevel, primaryPrec,
      primaryYield, ?_, ?_, ?_⟩
    · rw [parentWord, baseWord, List.append_assoc]
    · apply postfixFollower_append _ suffix frame follower
      intro empty
      have same : base = primary := noFrames empty
      have primaryNotNew : primary.isNew = false := by rw [← same]; exact notNew
      exact postfixFollower_square _ _ primaryNotNew
    · intro empty
      exact False.elim (word_append_nonempty_right suffix frame frameNonempty empty)
  | member base name ihBase =>
    intro hp _ initial items final hy
    have basePrec : base.prec = true := by
      apply all_prec_implies_prec base
      have hall : (Syn.member base name).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.2
    have baseLevel : 15 ≤ base.level := by
      have root : (Syn.member base name).precNode = true := Syn.prec_root hp
      simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at root
      exact root.1
    have notNew : base.isNew = false := by
      cases hn : base.isNew with
      | false => rfl
      | true =>
        have bad : (Syn.member base name).precNode = true := Syn.prec_root hp
        simp only [Syn.precNode, hn, Bool.not_true, Bool.and_false] at bad
        cases bad
    obtain ⟨baseItems, baseYield, shape⟩ := member_yield_parts base name initial final items hy
    obtain ⟨primary, primaryItems, primaryFinal, suffix, primaryLevel, primaryPrec, primaryYield,
      baseWord, follower, noFrames⟩ := ihBase basePrec baseLevel initial baseItems final baseYield
    let frame : List Tok := pu .period ++ [memberToken name]
    have frameNonempty : frame ≠ [] := by
      intro empty
      change Tok.punct .period :: _ = [] at empty
      cases empty
    have parentWord : items.flatten = baseItems.flatten ++ frame := by
      rw [shape]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, frame, List.append_assoc]
    refine ⟨primary, primaryItems, primaryFinal, suffix ++ frame, primaryLevel, primaryPrec,
      primaryYield, ?_, ?_, ?_⟩
    · rw [parentWord, baseWord, List.append_assoc]
    · apply postfixFollower_append _ suffix frame follower
      intro empty
      have same : base = primary := noFrames empty
      have primaryNotNew : primary.isNew = false := by rw [← same]; exact notNew
      exact postfixFollower_period _ _ primaryNotNew
    · intro empty
      exact False.elim (word_append_nonempty_right suffix frame frameNonempty empty)
  | callOptions base first rest ihBase ihFirst ihRest =>
    intro hp _ initial items final hy
    have basePrec : base.prec = true := by
      apply all_prec_implies_prec base
      have hall : (Syn.callOptions base first rest).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.1.2
    have baseLevel : 15 ≤ base.level := of_decide_eq_true (Syn.prec_root hp)
    obtain ⟨baseItems, firstItems, restItems, middle, next, baseYield, firstYield, restYield, shape⟩ :=
      options_yield_parts base first rest initial final items hy
    obtain ⟨primary, primaryItems, primaryFinal, suffix, primaryLevel, primaryPrec, primaryYield,
      baseWord, follower, noFrames⟩ := ihBase basePrec baseLevel initial baseItems middle baseYield
    let frame : List Tok := braces (commaSep (firstItems.flatten :: restItems))
    have frameNonempty : frame ≠ [] := by
      intro empty
      change Tok.punct .lbrace :: _ = [] at empty
      cases empty
    have parentWord : items.flatten = baseItems.flatten ++ frame := by
      rw [shape]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, frame]
    refine ⟨primary, primaryItems, primaryFinal, suffix ++ frame, primaryLevel, primaryPrec,
      primaryYield, ?_, ?_, ?_⟩
    · rw [parentWord, baseWord, List.append_assoc]
    · apply postfixFollower_append _ suffix frame follower
      intro _
      exact postfixFollower_braces _ _
    · intro empty
      exact False.elim (word_append_nonempty_right suffix frame frameNonempty empty)
  | call base args ihBase ihArgs =>
    intro hp _ initial items final hy
    have basePrec : base.prec = true := by
      apply all_prec_implies_prec base
      have hall : (Syn.call base args).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
      simp only [Syn.all, Bool.and_eq_true] at hall
      exact hall.1.2
    have baseLevel : 15 ≤ base.level := of_decide_eq_true (Syn.prec_root hp)
    obtain ⟨baseItems, argsItems, middle, baseYield, argsYield, shape⟩ :=
      call_yield_parts base args initial final items hy
    obtain ⟨payload, argsShape, payloadBalance⟩ := callArgs_yield_parens args middle final argsItems argsYield
    obtain ⟨primary, primaryItems, primaryFinal, suffix, primaryLevel, primaryPrec, primaryYield,
      baseWord, follower, noFrames⟩ := ihBase basePrec baseLevel initial baseItems middle baseYield
    let frame : List Tok := parens payload
    have frameNonempty : frame ≠ [] := by
      intro empty
      change Tok.punct .lparen :: _ = [] at empty
      cases empty
    have parentWord : items.flatten = baseItems.flatten ++ frame := by
      rw [shape, argsShape]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, frame]
    refine ⟨primary, primaryItems, primaryFinal, suffix ++ frame, primaryLevel, primaryPrec,
      primaryYield, ?_, ?_, ?_⟩
    · rw [parentWord, baseWord, List.append_assoc]
    · apply postfixFollower_append _ suffix frame follower
      intro _
      exact postfixFollower_parens _ _
    · intro empty
      exact False.elim (word_append_nonempty_right suffix frame frameNonempty empty)
  | unaryPrefix op value ih =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 13) impossible)
  | unarySuffix op value ih =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 14) impossible)
  | exp a b ihA ihB =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 12) impossible)
  | mulDivMod op a b ihA ihB =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 11) impossible)
  | addSub op a b ihA ihB =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 10) impossible)
  | shift op a b ihA ihB =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 9) impossible)
  | bitAnd a b ihA ihB =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 8) impossible)
  | bitXor a b ihA ihB =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 7) impossible)
  | bitOr a b ihA ihB =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 6) impossible)
  | order op a b ihA ihB =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 5) impossible)
  | equality op a b ihA ihB =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 4) impossible)
  | and a b ihA ihB =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 3) impossible)
  | or a b ihA ihB =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 2) impossible)
  | cond c a b ihC ihA ihB =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 1) impossible)
  | assign op a b ihA ihB =>
    intro _ impossible
    exact False.elim ((by decide : ¬ 15 ≤ 0) impossible)
  | _ => trivial

theorem high_expr_primary_spine (e : Syn .expr) (initial final : List Choice) (items : List (List Tok))
    (hp : e.prec = true) (hl : 15 ≤ e.level) (hy : e.yield initial = some (items, final)) :
    PrimarySpine e initial items := primary_spine_property e hp hl initial items final hy

end Solidity.Frontend.ExpressionUniqueness
