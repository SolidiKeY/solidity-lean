import Solidity.Frontend.ExpressionUniqueness.PostfixFollowers
import Solidity.Frontend.ExpressionUniqueness.LayoutBoundary
import Solidity.Frontend.ExpressionUniqueness.Primary

/-!
# Literal primary words reconstruct their maximal prefix

Arbitrary string fragments form a maximal same-kind token run. Numeric units
cannot be consumed as postfix followers. Concrete follower conditions are derived
by the certified primary-spine theorem, not added to the original target.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def literalTokenSelect (kind : Nat) (t : Tok) : Bool := decide (tokenLiteralKind t = some kind)

theorem fragsP_allTokens (p : Tok → Bool) (mk : Bytes → Tok) (hm : ∀ bs, p (mk bs) = true)
    (bs : Bytes) : Produces (fragsP mk bs) (AllTokens p) := by
  intro initial word final hy
  obtain ⟨pieces, chunks, shape, nonempty⟩ := fragsP_spec mk bs initial final word hy
  rw [shape]
  intro t ht
  obtain ⟨piece, member, rfl⟩ := List.mem_map.mp ht
  exact hm piece

theorem literalP_allTokens (l : Lit) : Produces (litP l) (AllTokens (literalTokenSelect (literalKind l))) := by
  cases l with
  | bool b =>
    apply produces_pure
    intro t ht
    cases (List.mem_singleton.mp ht)
    rfl
  | num n =>
    apply produces_pure
    intro t ht
    cases (List.mem_singleton.mp ht)
    rfl
  | str bs => exact fragsP_allTokens _ Tok.str (fun _ => rfl) bs
  | hexStr bs => exact fragsP_allTokens _ Tok.hexStr (fun _ => rfl) bs
  | unicodeStr bs => exact fragsP_allTokens _ Tok.unicodeStr (fun _ => rfl) bs

theorem literal_yield_allTokens (l : Lit) :
    Produces (Syn.lit l).yield (fun items => AllTokens (literalTokenSelect (literalKind l)) items.flatten) := by
  intro initial items final hy
  obtain ⟨word, hw, shape⟩ := one_pure_success_split (litP l) (fun word => [word]) initial final items hy
  rw [shape]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  exact literalP_allTokens l initial word final hw

theorem literal_prefix_kinds_equal (a b : Lit) (initial final initial' final' : List Choice)
    (items items' : List (List Tok)) (tail tail' : List Tok)
    (hy : (Syn.lit a).yield initial = some (items, final))
    (hy' : (Syn.lit b).yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') : literalKind a = literalKind b := by
  obtain ⟨token, rest, shape, kind⟩ := literal_head_kind a items.flatten
    (expression_partial_derives _ initial final items hy)
  obtain ⟨token', rest', shape', kind'⟩ := literal_head_kind b items'.flatten
    (expression_partial_derives _ initial' final' items' hy')
  rw [shape, shape'] at words
  have tokens : token = token' := (List.cons.inj words).1
  exact Option.some.inj (kind.symm.trans ((congrArg tokenLiteralKind tokens).trans kind'))

theorem literal_yield_prefix_unique (a b : Lit) (initial final initial' final' : List Choice)
    (items items' : List (List Tok)) (tail tail' : List Tok)
    (hb : PostfixFollower false tail) (hb' : PostfixFollower false tail')
    (hy : (Syn.lit a).yield initial = some (items, final))
    (hy' : (Syn.lit b).yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  have kind : literalKind a = literalKind b := literal_prefix_kinds_equal a b initial final initial' final'
    items items' tail tail' hy hy' words
  have allA : AllTokens (literalTokenSelect (literalKind a)) items.flatten :=
    literal_yield_allTokens a initial items final hy
  have allB : AllTokens (literalTokenSelect (literalKind a)) items'.flatten := by
    rw [kind]
    exact literal_yield_allTokens b initial' items' final' hy'
  exact maximal_token_run_unique (literalTokenSelect (literalKind a)) items.flatten items'.flatten tail tail'
    allA allB (postfixFollower_tokenBoundary _ false tail rfl rfl rfl rfl hb)
    (postfixFollower_tokenBoundary _ false tail' rfl rfl rfl rfl hb') words

def isDenomToken : Tok → Bool
  | .denom _ => true
  | _ => false

theorem literal_unit_prefix_disjoint (l : Lit) (n : NumLit) (u : Denom)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (hb : PostfixFollower false tail)
    (hy : (Syn.lit l).yield initial = some (items, final))
    (hy' : (Syn.litUnit n u).yield initial' = some (items', final')) :
    items.flatten ++ tail ≠ items'.flatten ++ tail' := by
  intro words
  have unitItems : items' = [[.num n, .denom u]] :=
    (pure_success_split [[Tok.num n, .denom u]] items' initial' final' hy').1
  have unitWord : items'.flatten = [.num n, .denom u] := by
    rw [unitItems]
    rfl
  obtain ⟨token, rest, shape, kind⟩ := literal_head_kind l items.flatten
    (expression_partial_derives _ initial final items hy)
  have expanded := words
  rw [shape, unitWord] at expanded
  have first : token = .num n := (List.cons.inj expanded).1
  have numeric : literalKind l = 1 := by
    rw [first] at kind
    exact (Option.some.inj kind).symm
  cases l with
  | bool b => cases numeric
  | str bs => cases numeric
  | hexStr bs => cases numeric
  | unicodeStr bs => cases numeric
  | num value =>
    have numberWord : items.flatten = [.num value] :=
      (derives_number value items.flatten).mp (expression_partial_derives _ initial final items hy)
    rw [numberWord, unitWord] at words
    have following : tail = .denom u :: tail' := (List.cons.inj words).2
    exact tokenBoundary_not_selected isDenomToken tail
      (postfixFollower_tokenBoundary _ false tail rfl rfl rfl rfl hb) (.denom u) rfl tail' following

theorem unit_yield_prefix_unique (n m : NumLit) (u v : Denom)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (hy : (Syn.litUnit n u).yield initial = some (items, final))
    (hy' : (Syn.litUnit m v).yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  have shape : items = [[.num n, .denom u]] :=
    (pure_success_split [[Tok.num n, .denom u]] items initial final hy).1
  have shape' : items' = [[.num m, .denom v]] :=
    (pure_success_split [[Tok.num m, .denom v]] items' initial' final' hy').1
  rw [shape, shape'] at words ⊢
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append] at words ⊢
  obtain ⟨number, remaining⟩ := List.cons.inj words
  obtain ⟨unitToken, following⟩ := List.cons.inj remaining
  exact ⟨by rw [number, unitToken], following⟩

end Solidity.Frontend.ExpressionUniqueness
