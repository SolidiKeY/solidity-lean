import Solidity.Frontend.StatementGrammarH28.CatchListCoverage

/-! Constructive try coverage: fixed empty-argument identifier call, no return
parameters, empty success block, recursive BooleanCatchList clauses. No general
expression uniqueness or Solidity semantic validity is claimed. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def tryCallInput (name : String) (s : St) : St :=
  locatedInput [.kw .try_, .ident name, .punct .lparen, .punct .rparen,
    .punct .lbrace, .punct .rbrace] s

theorem try_empty_body_prefix (n : Nat) (k : SCtx) (name : String) (s : St) :
    stmt (n + 10) k (tryCallInput name (locatedInput [Tok.kw .catch_] s)) =
      ((do let cs ← many (catchStep (n + 9) k)
           match cs with
           | c :: rest => return Syn.tryStmt (.call (.ident name) (.positional .nil)) .nil (.block .nil) c (toSynList rest)
           | [] => P.fail "expected a catch clause") : P (Syn (.stmt k)))
        (locatedInput [Tok.kw .catch_] s) := by
  rfl

theorem try_empty_body_prefix_head (n : Nat) (k : SCtx) (name : String) (s : St)
    (hs : s.ts.head?.map (fun t : Located => t.tok) = some (.kw .catch_)) :
    stmt (n + 10) k (tryCallInput name s) =
      ((do let cs ← many (catchStep (n + 9) k)
           match cs with
           | c :: rest => return Syn.tryStmt (.call (.ident name) (.positional .nil)) .nil (.block .nil) c (toSynList rest)
           | [] => P.fail "expected a catch clause") : P (Syn (.stmt k))) s := by
  cases s with
  | mk tokens ch eof =>
    cases tokens with
    | nil => cases hs
    | cons first rest =>
      cases first with
      | mk tok start stop =>
        have ht : tok = .kw .catch_ := Option.some.inj hs
        subst tok
        rfl

theorem boolean_try_coverage {k : SCtx} {c : Syn (.catchClause k)}
    {cs : Syn (.list (.catchClause k))} {ts : List Tok} {parts : List (List Tok)}
    {d b : Nat} (hc : BooleanCatch c ts d) (ht : BooleanCatchList cs parts b)
    (name : String) (n : Nat) (s : St) (hs : NoFollowingCatch s) :
    stmt (n + max d b + 10) k
      (tryCallInput name (locatedInput (ts ++ parts.flatten) s)) =
      .ok (.tryStmt (.call (.ident name) (.positional .nil)) .nil (.block .nil) c cs, s) := by
  have start : (locatedInput (ts ++ parts.flatten) s).ts.head?.map
      (fun t : Located => t.tok) = some (.kw .catch_) := by
    cases hc <;> rfl
  rw [try_empty_body_prefix_head (n + max d b) k name _ start]
  change (many (catchStep (n + max d b + 9) k)
    (locatedInput (ts ++ parts.flatten) s)).bind (fun p =>
      ((match p.1 with
        | first :: rest => pure (Syn.tryStmt (.call (.ident name) (.positional .nil))
            .nil (.block .nil) first (toSynList rest))
        | [] => P.fail "expected a catch clause") : P (Syn (.stmt k))) p.2) = _
  have parsed := boolean_catch_list_many (BooleanCatchList.cons hc ht)
    (n + max d b + 9) (by omega) s hs
  simp only [List.flatten_cons] at parsed
  rw [parsed]
  change Except.ok
    (Syn.tryStmt (.call (.ident name) (.positional .nil)) .nil (.block .nil) c
      (toSynList (itemsAsList cs)), s) = _
  rw [itemsAsList_inverse]

theorem boolean_try_yield {k : SCtx} {c : Syn (.catchClause k)}
    {cs : Syn (.list (.catchClause k))} {ts : List Tok} {parts : List (List Tok)}
    {d b : Nat} (hc : BooleanCatch c ts d) (ht : BooleanCatchList cs parts b)
    (name : String) (L : List Choice) :
    (Syn.tryStmt (.call (.ident name) (.positional .nil)) .nil (.block .nil) c cs).yield L =
      some ([[.kw .try_, .ident name, .punct .lparen, .punct .rparen,
        .punct .lbrace, .punct .rbrace] ++ ts ++ parts.flatten], L) := by
  rw [Syn.yield]
  change (c.yield L).bind (fun p => (cs.yield p.2).bind (fun q =>
    some ([[.kw .try_, .ident name, .punct .lparen, .punct .rparen,
      .punct .lbrace, .punct .rbrace] ++ p.1.flatten ++ q.1.flatten], q.2))) = _
  rw [boolean_catch_yield hc L]
  simp only [Option.bind_some]
  rw [boolean_catch_list_yield ht L]
  simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]

inductive BooleanTry : {k : SCtx} → Syn (.stmt k) → List Tok → Nat → Prop where
  | attempt {k : SCtx} {c : Syn (.catchClause k)} {cs : Syn (.list (.catchClause k))}
      {ts : List Tok} {parts : List (List Tok)} {d b : Nat} (name : String) :
      BooleanCatch c ts d → BooleanCatchList cs parts b →
      BooleanTry (.tryStmt (.call (.ident name) (.positional .nil)) .nil (.block .nil) c cs)
        ([.kw .try_, .ident name, .punct .lparen, .punct .rparen,
          .punct .lbrace, .punct .rbrace] ++ ts ++ parts.flatten) (max d b + 10)

theorem boolean_try_fragment_coverage {k : SCtx} {t : Syn (.stmt k)}
    {ts : List Tok} {b : Nat} (h : BooleanTry t ts b) (n : Nat) (s : St)
    (hs : NoFollowingCatch s) : stmt (n + b) k (locatedInput ts s) = .ok (t, s) := by
  cases h with
  | attempt name hc ht =>
    simpa only [tryCallInput, locatedInput_append, Nat.add_assoc] using
      boolean_try_coverage hc ht name n s hs

theorem boolean_try_fragment_yield {k : SCtx} {t : Syn (.stmt k)}
    {ts : List Tok} {b : Nat} (h : BooleanTry t ts b) (L : List Choice) :
    t.yield L = some ([ts], L) := by
  cases h with
  | attempt name hc ht => exact boolean_try_yield hc ht name L

theorem boolean_try_token_unique {k : SCtx} {t u : Syn (.stmt k)}
    {ts us : List Tok} {b e : Nat} (ht : BooleanTry t ts b) (hu : BooleanTry u us e)
    (he : ts = us) : t = u := by
  subst us
  let s : St := ⟨[], [], 0⟩
  have stop : NoFollowingCatch s := by intro bad; cases bad
  have pt := boolean_try_fragment_coverage ht e s stop
  have pu := boolean_try_fragment_coverage hu b s stop
  have fuel : e + b = b + e := by omega
  rw [fuel] at pt
  exact congrArg Prod.fst (Except.ok.inj (pt.symm.trans pu))

theorem boolean_try_derives {k : SCtx} {t : Syn (.stmt k)}
    {ts : List Tok} {b : Nat} (h : BooleanTry t ts b) : t.Derives ts := by
  refine ⟨[], ?_⟩
  unfold Syn.toks
  rw [boolean_try_fragment_yield h []]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

theorem boolean_try_actual_yield_unique {k : SCtx} {t u : Syn (.stmt k)}
    {ts us : List Tok} {b e : Nat} (ht : BooleanTry t ts b) (hu : BooleanTry u us e)
    (L M N P : List Choice) (parts qs : List (List Tok))
    (hyT : t.yield L = some (parts, M)) (hyU : u.yield N = some (qs, P))
    (he : parts.flatten = qs.flatten) : t = u := by
  have tp : [ts] = parts := congrArg Prod.fst
    (Option.some.inj ((boolean_try_fragment_yield ht L).symm.trans hyT))
  have up : [us] = qs := congrArg Prod.fst
    (Option.some.inj ((boolean_try_fragment_yield hu N).symm.trans hyU))
  rw [← tp, ← up] at he
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at he
  exact boolean_try_token_unique ht hu he

#print axioms try_empty_body_prefix
#print axioms try_empty_body_prefix_head
#print axioms boolean_try_coverage
#print axioms boolean_try_yield
#print axioms boolean_try_fragment_coverage
#print axioms boolean_try_fragment_yield
#print axioms boolean_try_token_unique
#print axioms boolean_try_derives
#print axioms boolean_try_actual_yield_unique
end Solidity.Frontend.StatementGrammarH28
