import Solidity.Frontend.ExpressionUniqueness.PostfixYieldSplit
import Solidity.Frontend.ExpressionUniqueness.LastEnclosure
import Solidity.Frontend.ExpressionUniqueness.ConditionalSpans
import Solidity.Frontend.ExpressionUniqueness.ExpressionCommaFree

/-!
# Actual bracketed postfix children have unique token spans

Balanced trailing enclosures reconstruct the existing base and payload words.
Slice colons and option commas then reconstruct their component words. All
balance/separator properties follow from actual child executions. General child
tree identity and postfix-versus-primary root reconstruction remain separate.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def PairYieldSpans {c d : Cat} (a : Syn c) (b : Syn d) (a' : Syn c) (b' : Syn d)
    (initial final initial' final' : List Choice) : Prop :=
  ∃ xs ys xs' ys' middle middle', a.yield initial = some (xs, middle) ∧
    b.yield middle = some (ys, final) ∧ a'.yield initial' = some (xs', middle') ∧
    b'.yield middle' = some (ys', final') ∧ xs.flatten = xs'.flatten ∧ ys.flatten = ys'.flatten

def TripleYieldSpans {c d e : Cat} (a : Syn c) (b : Syn d) (v : Syn e)
    (a' : Syn c) (b' : Syn d) (v' : Syn e) (initial final initial' final' : List Choice) : Prop :=
  ∃ xs ys zs xs' ys' zs' middle next middle' next',
    a.yield initial = some (xs, middle) ∧ b.yield middle = some (ys, next) ∧
    v.yield next = some (zs, final) ∧ a'.yield initial' = some (xs', middle') ∧
    b'.yield middle' = some (ys', next') ∧ v'.yield next' = some (zs', final') ∧
    xs.flatten = xs'.flatten ∧ ys.flatten = ys'.flatten ∧ zs.flatten = zs'.flatten

theorem index_child_spans (base base' : Syn .expr) (index index' : Syn (.opt .expr))
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (hy : (Syn.index base index).yield initial = some (items, final))
    (hy' : (Syn.index base' index').yield initial' = some (items', final'))
    (he : items.flatten = items'.flatten) :
    PairYieldSpans base index base' index' initial final initial' final' := by
  obtain ⟨xs, ys, middle, hx, hi, shape⟩ := index_yield_parts base index initial final items hy
  obtain ⟨xs', ys', middle', hx', hi', shape'⟩ := index_yield_parts base' index' initial' final' items' hy'
  have payload : Balanced ys.flatten := balancedItems_flatten
    (expressionCategory_yield_balanced index rfl middle ys final hi)
  have payload' : Balanced ys'.flatten := balancedItems_flatten
    (expressionCategory_yield_balanced index' rfl middle' ys' final' hi')
  rw [shape, shape'] at he
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at he
  obtain ⟨baseWord, indexWord⟩ := last_square_cut_unique xs.flatten ys.flatten xs'.flatten ys'.flatten
    payload payload' he
  exact ⟨xs, ys, xs', ys', middle, middle', hx, hi, hx', hi', baseWord, indexWord⟩

theorem slice_child_spans (base base' : Syn .expr) (start stop start' stop' : Syn (.opt .expr))
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (hy : (Syn.slice base start stop).yield initial = some (items, final))
    (hy' : (Syn.slice base' start' stop').yield initial' = some (items', final'))
    (he : items.flatten = items'.flatten) :
    TripleYieldSpans base start stop base' start' stop' initial final initial' final' := by
  obtain ⟨xs, ys, zs, middle, next, hx, hs, ht, shape⟩ := slice_yield_parts base start stop initial final items hy
  obtain ⟨xs', ys', zs', middle', next', hx', hs', ht', shape'⟩ :=
    slice_yield_parts base' start' stop' initial' final' items' hy'
  have startBal : Balanced ys.flatten := balancedItems_flatten
    (expressionCategory_yield_balanced start rfl middle ys next hs)
  have stopBal : Balanced zs.flatten := balancedItems_flatten
    (expressionCategory_yield_balanced stop rfl next zs final ht)
  have startBal' : Balanced ys'.flatten := balancedItems_flatten
    (expressionCategory_yield_balanced start' rfl middle' ys' next' hs')
  have stopBal' : Balanced zs'.flatten := balancedItems_flatten
    (expressionCategory_yield_balanced stop' rfl next' zs' final' ht')
  rw [shape, shape'] at he
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at he
  obtain ⟨baseWord, payload⟩ := last_square_cut_unique xs.flatten (ys.flatten ++ pu .colon ++ zs.flatten)
    xs'.flatten (ys'.flatten ++ pu .colon ++ zs'.flatten)
    (balanced_append (balanced_append startBal (balanced_atom rfl)) stopBal)
    (balanced_append (balanced_append startBal' (balanced_atom rfl)) stopBal')
    (by simpa only [List.append_assoc] using he)
  have colonWords : ys.flatten ++ .punct .colon :: zs.flatten =
      ys'.flatten ++ .punct .colon :: zs'.flatten := by
    simpa only [pu, List.append_assoc, List.singleton_append] using payload
  obtain ⟨startWord, stopWord⟩ := slice_payload_colon_unique start start' middle next middle' next'
    ys ys' zs.flatten zs'.flatten hs hs' colonWords
  exact ⟨xs, ys, zs, xs', ys', zs', middle, next, middle', next',
    hx, hs, ht, hx', hs', ht', baseWord, startWord, stopWord⟩

theorem index_slice_yields_disjoint (base base' : Syn .expr) (index start stop : Syn (.opt .expr))
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (hy : (Syn.index base index).yield initial = some (items, final))
    (hy' : (Syn.slice base' start stop).yield initial' = some (items', final')) :
    items.flatten ≠ items'.flatten := by
  intro he
  obtain ⟨xs, ys, middle, hx, hi, shape⟩ := index_yield_parts base index initial final items hy
  obtain ⟨xs', ys', zs', middle', next', hx', hs', ht', shape'⟩ :=
    slice_yield_parts base' start stop initial' final' items' hy'
  have indexBal : Balanced ys.flatten := balancedItems_flatten
    (expressionCategory_yield_balanced index rfl middle ys final hi)
  have startBal : Balanced ys'.flatten := balancedItems_flatten
    (expressionCategory_yield_balanced start rfl middle' ys' next' hs')
  have stopBal : Balanced zs'.flatten := balancedItems_flatten
    (expressionCategory_yield_balanced stop rfl next' zs' final' ht')
  rw [shape, shape'] at he
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at he
  obtain ⟨baseWord, payload⟩ := last_square_cut_unique xs.flatten ys.flatten
    xs'.flatten (ys'.flatten ++ pu .colon ++ zs'.flatten) indexBal
    (balanced_append (balanced_append startBal (balanced_atom rfl)) stopBal)
    (by simpa only [List.append_assoc] using he)
  apply index_slice_payload_disjoint index start middle final middle' next' ys ys' zs'.flatten hi hs'
  simpa only [pu, List.append_assoc, List.singleton_append] using payload

theorem call_child_spans (base base' : Syn .expr) (args args' : Syn .callArgs)
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (hy : (Syn.call base args).yield initial = some (items, final))
    (hy' : (Syn.call base' args').yield initial' = some (items', final'))
    (he : items.flatten = items'.flatten) :
    PairYieldSpans base args base' args' initial final initial' final' := by
  obtain ⟨xs, ys, middle, hx, ha, shape⟩ := call_yield_parts base args initial final items hy
  obtain ⟨xs', ys', middle', hx', ha', shape'⟩ := call_yield_parts base' args' initial' final' items' hy'
  obtain ⟨payload, argShape, bal⟩ := callArgs_yield_parens args middle final ys ha
  obtain ⟨payload', argShape', bal'⟩ := callArgs_yield_parens args' middle' final' ys' ha'
  rw [shape, shape', argShape, argShape'] at he
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at he
  obtain ⟨baseWord, argumentWord⟩ := last_parens_cut_unique xs.flatten payload xs'.flatten payload' bal bal' he
  refine ⟨xs, ys, xs', ys', middle, middle', hx, ha, hx', ha', baseWord, ?_⟩
  rw [argShape, argShape', argumentWord]

theorem options_child_spans (base base' : Syn .expr) (first first' : Syn .namedArg)
    (args args' : Syn (.list .namedArg)) (initial final initial' final' : List Choice)
    (items items' : List (List Tok))
    (hy : (Syn.callOptions base first args).yield initial = some (items, final))
    (hy' : (Syn.callOptions base' first' args').yield initial' = some (items', final'))
    (he : items.flatten = items'.flatten) :
    ∃ xs ys zs xs' ys' zs' middle next middle' next',
      base.yield initial = some (xs, middle) ∧ first.yield middle = some (ys, next) ∧
      args.yield next = some (zs, final) ∧ base'.yield initial' = some (xs', middle') ∧
      first'.yield middle' = some (ys', next') ∧ args'.yield next' = some (zs', final') ∧
      xs.flatten = xs'.flatten ∧ ys.flatten = ys'.flatten ∧ zs = zs' := by
  obtain ⟨xs, ys, zs, middle, next, hx, hf, ha, shape⟩ := options_yield_parts base first args initial final items hy
  obtain ⟨xs', ys', zs', middle', next', hx', hf', ha', shape'⟩ :=
    options_yield_parts base' first' args' initial' final' items' hy'
  have freeFirst : CommaFree ys.flatten := commaFreeItems_flatten
    (expressionCategory_yield_commaFree first rfl middle ys next hf)
  have freeArgs : CommaFreeItems zs := expressionCategory_yield_commaFree args rfl next zs final ha
  have freeFirst' : CommaFree ys'.flatten := commaFreeItems_flatten
    (expressionCategory_yield_commaFree first' rfl middle' ys' next' hf')
  have freeArgs' : CommaFreeItems zs' := expressionCategory_yield_commaFree args' rfl next' zs' final' ha'
  have free : CommaFreeItems (ys.flatten :: zs) := commaFreeItems_cons freeFirst freeArgs
  have free' : CommaFreeItems (ys'.flatten :: zs') := commaFreeItems_cons freeFirst' freeArgs'
  rw [shape, shape'] at he
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at he
  obtain ⟨baseWord, payload⟩ := last_braces_cut_unique xs.flatten (commaSep (ys.flatten :: zs))
    xs'.flatten (commaSep (ys'.flatten :: zs')) (balanced_commaSep (commaFreeItems_balanced free))
    (balanced_commaSep (commaFreeItems_balanced free')) he
  have vectors : ys.flatten :: zs = ys'.flatten :: zs' :=
    commaSep_nonempty_unique _ _ _ _ free free' payload
  exact ⟨xs, ys, zs, xs', ys', zs', middle, next, middle', next',
    hx, hf, ha, hx', hf', ha', baseWord, (List.cons.inj vectors).1, (List.cons.inj vectors).2⟩

end Solidity.Frontend.ExpressionUniqueness
