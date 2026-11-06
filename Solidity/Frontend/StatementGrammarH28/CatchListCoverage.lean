import Solidity.Frontend.StatementGrammarH28.CatchCoverage
import Solidity.Frontend.StatementGrammarH28.ListMeasures

/-! Syntax-derived catch-list coverage for the actual many combinator.
The terminal boundary is explicit because a following catch is greedily read.
This is restricted catch-fragment coverage, not whole-try completeness. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def NoFollowingCatch (s : St) : Prop :=
  s.ts.head?.map (fun t : Located => t.tok) ≠ some (.kw .catch_)

theorem statement_no_following_catch {k : SCtx} (t : Syn (.stmt k))
    (L M : List Choice) (parts : List (List Tok))
    (hy : t.yield L = some (parts, M)) (s : St) :
    NoFollowingCatch (locatedInput parts.flatten s) := by
  obtain ⟨a, tail, ht, ha⟩ := statement_boundary_head t L parts M hy
  rw [ht]
  change some a ≠ some (.kw .catch_)
  intro bad
  have eq : a = .kw .catch_ := Option.some.inj bad
  subst a
  cases ha

/-- Definitionally the step used by stmt's try branch. -/
def catchStep (fuel : Nat) (k : SCtx) : P (Option (Syn (.catchClause k))) := do
  if ← isK .catch_ then return some (← catchClause fuel k) else return none

theorem catch_step_stop (fuel : Nat) (k : SCtx) (s : St) (h : NoFollowingCatch s) :
    catchStep fuel k s = .ok (none, s) := by
  have hb : (s.ts.head?.map (fun t : Located => t.tok) == some (Tok.kw .catch_)) = false :=
    beq_eq_false_iff_ne.mpr h
  unfold catchStep isK isTok peek peekN
  change (if s.ts.head?.map (fun t : Located => t.tok) == some (Tok.kw .catch_) then
    (do return some (← catchClause fuel k)) else pure none) s = _
  rw [hb]
  rfl

theorem catch_fragment_head {k : SCtx} {c : Syn (.catchClause k)} {ts : List Tok} {b : Nat}
    (h : BooleanCatch c ts b) : ts.head? = some (.kw .catch_) := by
  cases h <;> rfl

theorem catch_step_start (fuel : Nat) (k : SCtx) (ts : List Tok) (s : St)
    (h : ts.head? = some (.kw .catch_)) :
    catchStep fuel k (locatedInput ts s) =
      (catchClause fuel k (locatedInput ts s)).map (fun p => (some p.1, p.2)) := by
  cases ts with
  | nil => cases h
  | cons t ts =>
    have ht : t = .kw .catch_ := Option.some.inj h
    subst t
    rfl

theorem boolean_catch_step {k : SCtx} {c : Syn (.catchClause k)} {ts : List Tok} {b : Nat}
    (h : BooleanCatch c ts b) (fuel : Nat) (hf : b ≤ fuel) (s : St) :
    catchStep fuel k (locatedInput ts s) = .ok (some c, s) := by
  have parsed := boolean_catch_coverage h (fuel - b) s
  have enough : fuel - b + b = fuel := Nat.sub_add_cancel hf
  rw [enough] at parsed
  rw [catch_step_start fuel k ts s (catch_fragment_head h), parsed]
  rfl

inductive BooleanCatchList : {k : SCtx} → Syn (.list (.catchClause k)) →
    List (List Tok) → Nat → Prop where
  | nil {k : SCtx} : BooleanCatchList (Syn.nil (c := .catchClause k)) [] 0
  | cons {k : SCtx} {c : Syn (.catchClause k)} {cs : Syn (.list (.catchClause k))}
      {ts : List Tok} {parts : List (List Tok)} {d b : Nat} :
      BooleanCatch c ts d → BooleanCatchList cs parts b →
      BooleanCatchList (.cons c cs) (ts :: parts) (max d b)

theorem boolean_catch_list_yield {k : SCtx} {cs : Syn (.list (.catchClause k))}
    {parts : List (List Tok)} {b : Nat} (h : BooleanCatchList cs parts b) (L : List Choice) :
    cs.yield L = some (parts, L) := by
  induction h with
  | nil => rfl
  | @cons c cs ts parts d b hc ht ih =>
    have result := list_yield_cons_of c cs L L L [ts] parts (boolean_catch_yield hc L) ih
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using result

theorem catch_yield_head {k : SCtx} (c : Syn (.catchClause k)) :
    PrEnsures c.yield (fun parts => parts.flatten.head? = some (.kw .catch_)) := by
  cases c with
  | catchPlain body =>
    rw [Syn.yield]
    apply ensures_bind
    intro chunks
    apply ensures_pure
    rfl
  | catchSig name param params body =>
    rw [Syn.yield]
    apply ensures_bind
    intro p
    apply ensures_bind
    intro ps
    apply ensures_bind
    intro b
    apply ensures_pure
    rfl

theorem catch_yield_nonempty {k : SCtx} (c : Syn (.catchClause k))
    (L M : List Choice) (parts : List (List Tok))
    (hy : c.yield L = some (parts, M)) : parts.flatten ≠ [] := by
  have head := catch_yield_head c L parts M hy
  change parts.flatten.head? = some (.kw .catch_) at head
  intro empty
  rw [empty] at head
  cases head

theorem catch_list_yield_token_bound {k : SCtx} (cs : Syn (.list (.catchClause k)))
    (L M : List Choice) (parts : List (List Tok))
    (hy : cs.yield L = some (parts, M)) : g0ListLength cs ≤ parts.flatten.length :=
  list_yield_token_bound catch_yield_nonempty cs L M parts hy

theorem boolean_catch_list_count_le {k : SCtx} {cs : Syn (.list (.catchClause k))}
    {parts : List (List Tok)} {b : Nat} (h : BooleanCatchList cs parts b) :
    g0ListLength cs ≤ parts.flatten.length :=
  catch_list_yield_token_bound cs [] [] parts (boolean_catch_list_yield h [])

theorem boolean_catch_list_many_aux {k : SCtx} {cs : Syn (.list (.catchClause k))}
    {parts : List (List Tok)} {b : Nat} (h : BooleanCatchList cs parts b)
    (fuel : Nat) (hf : b ≤ fuel) (extra : Nat) (s : St) (hs : NoFollowingCatch s) :
    manyAux (catchStep fuel k) (extra + g0ListLength cs + 1)
      (locatedInput parts.flatten s) = .ok (g0ListValues cs, s) := by
  induction h generalizing extra with
  | nil =>
    simp only [g0ListLength_nil, g0ListValues_nil, List.flatten_nil, Nat.add_zero]
    change manyAux _ (extra + 1) s = _
    exact many_aux_none (catch_step_stop fuel k s hs)
  | @cons c cs ts parts d b hc ht ih =>
    simp only [g0ListLength_cons, g0ListValues_cons, List.flatten_cons]
    have head : catchStep fuel k (locatedInput ts (locatedInput parts.flatten s)) =
        .ok (some c, locatedInput parts.flatten s) :=
      boolean_catch_step hc fuel (by omega) _
    rw [locatedInput_append]
    change manyAux _ ((extra + g0ListLength cs + 1) + 1) _ = _
    exact many_aux_cons head (ih (by omega) extra)

/-- This theorem explicitly connects the syntax-derived bound to actual many,
including its token-length-derived counter and its terminating branch. -/
theorem boolean_catch_list_many {k : SCtx} {cs : Syn (.list (.catchClause k))}
    {parts : List (List Tok)} {b : Nat} (h : BooleanCatchList cs parts b)
    (fuel : Nat) (hf : b ≤ fuel) (s : St) (hs : NoFollowingCatch s) :
    many (catchStep fuel k) (locatedInput parts.flatten s) = .ok (g0ListValues cs, s) := by
  have count := boolean_catch_list_count_le h
  have length : (locatedInput parts.flatten s).ts.length = parts.flatten.length + s.ts.length := by
    simp only [locatedInput, List.length_append, List.length_map]
  let extra := (locatedInput parts.flatten s).ts.length - g0ListLength cs
  have counter : (locatedInput parts.flatten s).ts.length + 1 = extra + g0ListLength cs + 1 := by
    omega
  change manyAux _ ((locatedInput parts.flatten s).ts.length + 1) _ = _
  rw [counter]
  exact boolean_catch_list_many_aux h fuel hf extra s hs

theorem boolean_catch_list_token_unique {k : SCtx} {cs ds : Syn (.list (.catchClause k))}
    {parts qs : List (List Tok)} {b e : Nat} (hc : BooleanCatchList cs parts b)
    (hd : BooleanCatchList ds qs e) (he : parts.flatten = qs.flatten) : cs = ds := by
  let s : St := ⟨[], [], 0⟩
  have stop : NoFollowingCatch s := by intro bad; cases bad
  have pc := boolean_catch_list_many hc (b + e) (by omega) s stop
  have pd := boolean_catch_list_many hd (b + e) (by omega) s stop
  rw [he] at pc
  have values : g0ListValues cs = g0ListValues ds :=
    congrArg Prod.fst (Except.ok.inj (pc.symm.trans pd))
  change itemsAsList cs = itemsAsList ds at values
  have trees := congrArg toSynList values
  rw [itemsAsList_inverse, itemsAsList_inverse] at trees
  exact trees

#print axioms statement_no_following_catch
#print axioms catch_yield_head
#print axioms catch_yield_nonempty
#print axioms catch_list_yield_token_bound
#print axioms catch_step_stop
#print axioms catch_fragment_head
#print axioms catch_step_start
#print axioms boolean_catch_step
#print axioms boolean_catch_list_yield
#print axioms boolean_catch_list_count_le
#print axioms boolean_catch_list_many_aux
#print axioms boolean_catch_list_many
#print axioms boolean_catch_list_token_unique
end Solidity.Frontend.StatementGrammarH28
