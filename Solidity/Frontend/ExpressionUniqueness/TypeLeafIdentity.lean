import Solidity.Frontend.ExpressionUniqueness.TypeArrayIdentity
import Solidity.Frontend.ExpressionUniqueness.FunctionTypeIdentity

/-!
# Actual type atom classification and intrinsic leaf identity

Array disjointness and actual token heads reconstruct atom families internally.
All elementary dimensions and arbitrary identifier paths remain quantified.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem same_yield_type_atom (a b : Syn .typeName)
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (atom : isTypeAtom a = true)
    (hy : a.yield initial = some (items, final)) (hy' : b.yield initial' = some (items', final'))
    (words : items.flatten = items'.flatten) : isTypeAtom b = true := by
  cases b with
  | elem => rfl
  | userType => rfl
  | mapping => rfl
  | fnType => rfl
  | array base length =>
    exact (array_atom_yields_disjoint base length a initial' final' initial final items' items atom hy' hy words.symm).elim

theorem same_yield_type_atom_kind (a b : Syn .typeName)
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (atom : isTypeAtom a = true)
    (hy : a.yield initial = some (items, final)) (hy' : b.yield initial' = some (items', final'))
    (words : items.flatten = items'.flatten) : typeAtomKind a = typeAtomKind b := by
  have atom' := same_yield_type_atom a b initial final initial' final' items items' atom hy hy' words
  exact typeAtom_prefix_kinds_equal a b initial final initial' final' items items' [] [] atom atom' hy hy'
    (by simpa only [List.append_nil] using words)

theorem elementary_tokens_injective (a b : Elem) (words : a.toks = b.toks) : a = b := by
  rcases elem_tokens_shape a with rfl | single
  · rcases elem_tokens_shape b with rfl | single'
    · rfl
    · rw [single'] at words
      have tail : [Tok.kw .payable] = [] := (List.cons.inj words).2
      cases tail
  · rcases elem_tokens_shape b with rfl | single'
    · rw [single] at words
      have tail : [] = [Tok.kw .payable] := (List.cons.inj words).2
      cases tail
    · rw [single, single'] at words
      exact Tok.elem.inj (List.cons.inj words).1

theorem path_tail_tokens_injective (xs ys : List String)
    (words : xs.flatMap (fun s => [Tok.punct .period, .ident s]) =
      ys.flatMap (fun s => [Tok.punct .period, .ident s])) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => cases words
  | cons x xs ih =>
    cases ys with
    | nil => cases words
    | cons y ys =>
      have names : x = y := Tok.ident.inj (List.cons.inj (List.cons.inj words).2).1
      have tails := ih ys (List.cons.inj (List.cons.inj words).2).2
      rw [names, tails]

theorem path_tokens_injective (a b : IdPath) (words : a.toks = b.toks) : a = b := by
  cases a with
  | mk head tail =>
    cases b with
    | mk head' tail' =>
      have heads : head = head' := Tok.ident.inj (List.cons.inj words).1
      have tails := path_tail_tokens_injective tail tail' (List.cons.inj words).2
      rw [heads, tails]

theorem elementary_type_word_unique (value : Elem) : WordUnique (Syn.elem value) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have atom := same_yield_type_atom (.elem value) other initial final initial' final' items items' rfl hy hy' words
  have kind := same_yield_type_atom_kind (.elem value) other initial final initial' final' items items' rfl hy hy' words
  rcases typeAtom_cases other atom with ⟨value', rfl⟩ | ⟨path, rfl⟩ | ⟨key, kn, ty, vn, rfl⟩ |
    ⟨params, vis, mu, returns, rfl⟩
  · have shape : items = [value.toks] := (pure_success_split [value.toks] items initial final hy).1
    have shape' : items' = [value'.toks] := (pure_success_split [value'.toks] items' initial' final' hy').1
    rw [shape, shape'] at words
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words
    rw [elementary_tokens_injective value value' words]
  · cases kind
  · cases kind
  · cases kind

theorem user_type_word_unique (path : IdPath) : WordUnique (Syn.userType path) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have atom := same_yield_type_atom (.userType path) other initial final initial' final' items items' rfl hy hy' words
  have kind := same_yield_type_atom_kind (.userType path) other initial final initial' final' items items' rfl hy hy' words
  rcases typeAtom_cases other atom with ⟨value, rfl⟩ | ⟨path', rfl⟩ | ⟨key, kn, ty, vn, rfl⟩ |
    ⟨params, vis, mu, returns, rfl⟩
  · cases kind
  · have shape : items = [path.toks] := (pure_success_split [path.toks] items initial final hy).1
    have shape' : items' = [path'.toks] := (pure_success_split [path'.toks] items' initial' final' hy').1
    rw [shape, shape'] at words
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words
    rw [path_tokens_injective path path' words]
  · cases kind
  · cases kind

theorem fn_type_word_unique (params returns : Syn (.list .param)) (vis : Option Visibility) (mu : Option Mutability)
    (ihParams : VectorUnique params) (ihReturns : VectorUnique returns) : WordUnique (Syn.fnType params vis mu returns) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have atom := same_yield_type_atom (.fnType params vis mu returns) other initial final initial' final' items items' rfl hy hy' words
  have kind := same_yield_type_atom_kind (.fnType params vis mu returns) other initial final initial' final' items items' rfl hy hy' words
  rcases typeAtom_cases other atom with ⟨value, rfl⟩ | ⟨path, rfl⟩ | ⟨key, kn, ty, vn, rfl⟩ |
    ⟨params', vis', mu', returns', rfl⟩
  · cases kind
  · cases kind
  · cases kind
  · exact fn_type_same_constructor_unique params returns params' returns' vis vis' mu mu' ihParams ihReturns
      initial final initial' final' items items' hp hp' hy hy' words

end Solidity.Frontend.ExpressionUniqueness
