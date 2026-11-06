import Solidity.Frontend.ExpressionUniqueness.PrimaryLeafIdentity
import Solidity.Frontend.ExpressionUniqueness.MappingKeyIdentity

/-!
# Recursive primary expression identity steps

Keyword/enclosure shapes and comma vectors come from actual original yields.
Tuple holes remain full optional/list item components. Only structural identity
for actual children is recursive; no primary split or uniqueness is assumed.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem commaSep_head_tail (first : List Tok) (rest : List (List Tok)) :
    commaSep (first :: rest) = first ++ rest.flatMap (pu .comma ++ ·) := by
  induction rest generalizing first with
  | nil => simpa only [List.flatMap_nil, List.append_nil] using commaSep_single first
  | cons next rest ih =>
    rw [commaSep_cons_cons, ih]
    simp only [List.flatMap_cons, pu, List.cons_append, List.nil_append]

theorem surround_word_injective (left right : Tok) (xs ys : List Tok)
    (words : left :: (xs ++ [right]) = left :: (ys ++ [right])) : xs = ys := by
  have tails : xs ++ [right] = ys ++ [right] := (List.cons.inj words).2
  simpa only [List.append_cancel_right_eq] using tails

theorem new_prec_child (ty : Syn .typeName) (hp : (Syn.new ty).prec = true) : ty.prec = true := by
  have hall : (Syn.new ty).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.new ty).precNode && ty.all Syn.precNode) = true at hall
  exact all_prec_implies_prec ty (Bool.and_eq_true_iff.mp hall).2

theorem new_word_unique (ty : Syn .typeName) (ih : WordUnique ty) : WordUnique (Syn.new ty) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  obtain ⟨level, kind⟩ := primary_competitor_kind (Syn.new ty) other
    initial final initial' final' items items' rfl hp hp' hy hy' words
  rcases expr_level_sixteen_cases other level with ⟨ty', rfl⟩ | ⟨ty', rfl⟩ | ⟨args', rfl⟩ | ⟨first', rest', rfl⟩ |
    ⟨first', rest', rfl⟩ | ⟨name', rfl⟩ | ⟨value', allowed', rfl⟩ | ⟨literal', rfl⟩ | ⟨number', unit', rfl⟩
  all_goals first | (cases kind; done) | skip
  obtain ⟨xs, hx, shape⟩ := new_yield_parts ty initial final items hy
  obtain ⟨ys, hyb, shape'⟩ := new_yield_parts ty' initial' final' items' hy'
  rw [shape, shape'] at words
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, tk, List.singleton_append] at words
  have childWords : xs.flatten = ys.flatten := (List.cons.inj words).2
  have childEq : ty = ty' := ih ty' initial final initial' final' xs ys
    (new_prec_child ty hp) (new_prec_child ty' hp') hx hyb childWords
  rw [childEq]

theorem metaType_prec_child (ty : Syn .typeName) (hp : (Syn.metaType ty).prec = true) : ty.prec = true := by
  have hall : (Syn.metaType ty).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.metaType ty).precNode && ty.all Syn.precNode) = true at hall
  exact all_prec_implies_prec ty (Bool.and_eq_true_iff.mp hall).2

theorem metaType_word_unique (ty : Syn .typeName) (ih : WordUnique ty) : WordUnique (Syn.metaType ty) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  obtain ⟨level, kind⟩ := primary_competitor_kind (Syn.metaType ty) other
    initial final initial' final' items items' rfl hp hp' hy hy' words
  rcases expr_level_sixteen_cases other level with ⟨ty', rfl⟩ | ⟨ty', rfl⟩ | ⟨args', rfl⟩ | ⟨first', rest', rfl⟩ |
    ⟨first', rest', rfl⟩ | ⟨name', rfl⟩ | ⟨value', allowed', rfl⟩ | ⟨literal', rfl⟩ | ⟨number', unit', rfl⟩
  all_goals first | (cases kind; done) | skip
  obtain ⟨xs, hx, shape⟩ := meta_yield_parts ty initial final items hy
  obtain ⟨ys, hyb, shape'⟩ := meta_yield_parts ty' initial' final' items' hy'
  rw [shape, shape'] at words
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, tk, List.singleton_append] at words
  have childWords : xs.flatten = ys.flatten := parens_word_injective _ _ (List.cons.inj words).2
  have childEq : ty = ty' := ih ty' initial final initial' final' xs ys
    (metaType_prec_child ty hp) (metaType_prec_child ty' hp') hx hyb childWords
  rw [childEq]

theorem payableConv_prec_child (args : Syn .callArgs) (hp : (Syn.payableConv args).prec = true) : args.prec = true := by
  have hall : (Syn.payableConv args).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.payableConv args).precNode && args.all Syn.precNode) = true at hall
  exact all_prec_implies_prec args (Bool.and_eq_true_iff.mp hall).2

theorem payableConv_word_unique (args : Syn .callArgs) (ih : WordUnique args) : WordUnique (Syn.payableConv args) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  obtain ⟨level, kind⟩ := primary_competitor_kind (Syn.payableConv args) other
    initial final initial' final' items items' rfl hp hp' hy hy' words
  rcases expr_level_sixteen_cases other level with ⟨ty', rfl⟩ | ⟨ty', rfl⟩ | ⟨args', rfl⟩ | ⟨first', rest', rfl⟩ |
    ⟨first', rest', rfl⟩ | ⟨name', rfl⟩ | ⟨value', allowed', rfl⟩ | ⟨literal', rfl⟩ | ⟨number', unit', rfl⟩
  all_goals first | (cases kind; done) | skip
  obtain ⟨xs, hx, shape⟩ := payable_yield_parts args initial final items hy
  obtain ⟨ys, hyb, shape'⟩ := payable_yield_parts args' initial' final' items' hy'
  rw [shape, shape'] at words
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, tk, List.singleton_append] at words
  have childWords : xs.flatten = ys.flatten := (List.cons.inj words).2
  have childEq : args = args' := ih args' initial final initial' final' xs ys
    (payableConv_prec_child args hp) (payableConv_prec_child args' hp') hx hyb childWords
  rw [childEq]

theorem tuple_prec_children (first : Syn (.opt .expr)) (rest : Syn (.list (.opt .expr)))
    (hp : (Syn.tuple first rest).prec = true) : first.prec = true ∧ rest.prec = true := by
  have hall : (Syn.tuple first rest).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.tuple first rest).precNode && first.all Syn.precNode && rest.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec first (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec rest (Bool.and_eq_true_iff.mp hall).2⟩

theorem tuple_word_unique (first : Syn (.opt .expr)) (rest : Syn (.list (.opt .expr)))
    (ihFirst : WordUnique first) (ihRest : VectorUnique rest) : WordUnique (Syn.tuple first rest) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  obtain ⟨level, kind⟩ := primary_competitor_kind (Syn.tuple first rest) other
    initial final initial' final' items items' rfl hp hp' hy hy' words
  rcases expr_level_sixteen_cases other level with ⟨ty', rfl⟩ | ⟨ty', rfl⟩ | ⟨args', rfl⟩ | ⟨first', rest', rfl⟩ |
    ⟨first', rest', rfl⟩ | ⟨name', rfl⟩ | ⟨value', allowed', rfl⟩ | ⟨literal', rfl⟩ | ⟨number', unit', rfl⟩
  all_goals first | (cases kind; done) | skip
  obtain ⟨xs, ys, middle, hx, hyr, shape⟩ := tuple_yield_parts first rest initial final items hy
  obtain ⟨xs', ys', middle', hx', hyr', shape'⟩ := tuple_yield_parts first' rest' initial' final' items' hy'
  rw [shape, shape'] at words
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words
  have bodies : xs.flatten ++ ys.flatMap (pu .comma ++ ·) = xs'.flatten ++ ys'.flatMap (pu .comma ++ ·) :=
    parens_word_injective _ _ words
  have commaWords : commaSep (xs.flatten :: ys) = commaSep (xs'.flatten :: ys') := by
    rw [commaSep_head_tail, commaSep_head_tail]
    exact bodies
  have free : CommaFreeItems (xs.flatten :: ys) := commaFreeItems_cons
    (commaFreeItems_flatten (expressionCategory_yield_commaFree first rfl initial xs middle hx))
    (expressionCategory_yield_commaFree rest rfl middle ys final hyr)
  have free' : CommaFreeItems (xs'.flatten :: ys') := commaFreeItems_cons
    (commaFreeItems_flatten (expressionCategory_yield_commaFree first' rfl initial' xs' middle' hx'))
    (expressionCategory_yield_commaFree rest' rfl middle' ys' final' hyr')
  have vectors : xs.flatten :: ys = xs'.flatten :: ys' :=
    commaSep_nonempty_unique xs.flatten xs'.flatten ys ys' free free' commaWords
  obtain ⟨firstWords, restWords⟩ := List.cons.inj vectors
  obtain ⟨hpf, hpr⟩ := tuple_prec_children first rest hp
  obtain ⟨hpf', hpr'⟩ := tuple_prec_children first' rest' hp'
  have firstEq : first = first' := ihFirst first' initial middle initial' middle' xs xs' hpf hpf' hx hx' firstWords
  have restEq : rest = rest' := ihRest rest' middle final middle' final' ys ys' hpr hpr' hyr hyr' restWords
  rw [firstEq, restEq]

theorem inlineArray_prec_children (first : Syn .expr) (rest : Syn (.list .expr))
    (hp : (Syn.inlineArray first rest).prec = true) : first.prec = true ∧ rest.prec = true := by
  have hall : (Syn.inlineArray first rest).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.inlineArray first rest).precNode && first.all Syn.precNode && rest.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec first (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec rest (Bool.and_eq_true_iff.mp hall).2⟩

theorem inlineArray_word_unique (first : Syn .expr) (rest : Syn (.list .expr))
    (ihFirst : WordUnique first) (ihRest : VectorUnique rest) : WordUnique (Syn.inlineArray first rest) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  obtain ⟨level, kind⟩ := primary_competitor_kind (Syn.inlineArray first rest) other
    initial final initial' final' items items' rfl hp hp' hy hy' words
  rcases expr_level_sixteen_cases other level with ⟨ty', rfl⟩ | ⟨ty', rfl⟩ | ⟨args', rfl⟩ | ⟨first', rest', rfl⟩ |
    ⟨first', rest', rfl⟩ | ⟨name', rfl⟩ | ⟨value', allowed', rfl⟩ | ⟨literal', rfl⟩ | ⟨number', unit', rfl⟩
  all_goals first | (cases kind; done) | skip
  obtain ⟨xs, ys, middle, hx, hyr, shape⟩ := inline_yield_parts first rest initial final items hy
  obtain ⟨xs', ys', middle', hx', hyr', shape'⟩ := inline_yield_parts first' rest' initial' final' items' hy'
  rw [shape, shape'] at words
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words
  have commaWords : commaSep (xs.flatten :: ys) = commaSep (xs'.flatten :: ys') :=
    surround_word_injective (.punct .lbrack) (.punct .rbrack) _ _ words
  have free : CommaFreeItems (xs.flatten :: ys) := commaFreeItems_cons
    (commaFreeItems_flatten (expressionCategory_yield_commaFree first rfl initial xs middle hx))
    (expressionCategory_yield_commaFree rest rfl middle ys final hyr)
  have free' : CommaFreeItems (xs'.flatten :: ys') := commaFreeItems_cons
    (commaFreeItems_flatten (expressionCategory_yield_commaFree first' rfl initial' xs' middle' hx'))
    (expressionCategory_yield_commaFree rest' rfl middle' ys' final' hyr')
  have vectors : xs.flatten :: ys = xs'.flatten :: ys' :=
    commaSep_nonempty_unique xs.flatten xs'.flatten ys ys' free free' commaWords
  obtain ⟨firstWords, restWords⟩ := List.cons.inj vectors
  obtain ⟨hpf, hpr⟩ := inlineArray_prec_children first rest hp
  obtain ⟨hpf', hpr'⟩ := inlineArray_prec_children first' rest' hp'
  have firstEq : first = first' := ihFirst first' initial middle initial' middle' xs xs' hpf hpf' hx hx' firstWords
  have restEq : rest = rest' := ihRest rest' middle final middle' final' ys ys' hpr hpr' hyr hyr' restWords
  rw [firstEq, restEq]

end Solidity.Frontend.ExpressionUniqueness
