import Solidity.Frontend.StatementGrammarH28.ConditionalFuel

/-! Constructive catch-clause parser coverage over existing syntax.
Bodies use the proved recursive Boolean item-list fragment. Signature headers
use one Boolean parameter, with arbitrary optional clause/parameter names.
This is grammar parser coverage, not Solidity catch-signature semantic validity
or coverage of arbitrary expression/type atoms. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def plainCatchInput (ts : List Tok) (s : St) : St :=
  locatedInput (tk .catch_) (blockInput ts s)

def signatureCatchInput (name paramName : Option String) (ts : List Tok) (s : St) : St :=
  locatedInput (tk .catch_ ++ optToks idt name ++
    parens ([.elem .bool] ++ optToks idt paramName)) (blockInput ts s)

theorem catch_plain_prefix (n : Nat) (k : SCtx) (ts : List Tok) (s : St) :
    catchClause (n + 1) k (plainCatchInput ts s) =
      (block n k (blockInput ts s)).map (fun p => (Syn.catchPlain p.1, p.2)) := by
  rfl

theorem catch_signature_prefix (n : Nat) (k : SCtx)
    (name paramName : Option String) (ts : List Tok) (s : St) :
    catchClause (n + 6) k (signatureCatchInput name paramName ts s) =
      (block (n + 5) k (blockInput ts s)).map
        (fun p => (Syn.catchSig name (.param (.elem .bool) .none paramName) .nil p.1, p.2)) := by
  cases name <;> cases paramName <;> rfl

theorem boolean_list_plain_catch_coverage {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} {b : Nat} (h : BooleanListBound xs parts b)
    (n : Nat) (s : St) :
    catchClause (n + b + 2) k (plainCatchInput parts.flatten s) =
      .ok (.catchPlain (.block xs), s) := by
  change catchClause ((n + b + 1) + 1) k _ = _
  rw [catch_plain_prefix, boolean_list_block_coverage h]
  rfl

theorem boolean_list_signature_catch_coverage {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} {b : Nat} (h : BooleanListBound xs parts b)
    (n : Nat) (name paramName : Option String) (s : St) :
    catchClause (n + b + 6) k (signatureCatchInput name paramName parts.flatten s) =
      .ok (.catchSig name (.param (.elem .bool) .none paramName) .nil (.block xs), s) := by
  rw [catch_signature_prefix]
  have body := boolean_list_block_coverage h (n + 4) s
  have fuel : n + 4 + b + 1 = n + b + 5 := by omega
  rw [fuel] at body
  rw [body]
  rfl

theorem boolean_list_plain_catch_yield {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} (h : BooleanItemList xs parts) (L : List Choice) :
    (Syn.catchPlain (.block xs)).yield L =
      some ([tk .catch_ ++ braces parts.flatten], L) := by
  rw [Syn.yield]
  change ((Syn.block xs).yield L).bind
    (fun p => some ([tk .catch_ ++ p.1.flatten], p.2)) = _
  rw [boolean_item_block_yield h L]
  simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem boolean_list_signature_catch_yield {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} (h : BooleanItemList xs parts)
    (name paramName : Option String) (L : List Choice) :
    (Syn.catchSig name (.param (.elem .bool) .none paramName) .nil (.block xs)).yield L =
      some ([tk .catch_ ++ optToks idt name ++
        parens ([.elem .bool] ++ optToks idt paramName) ++ braces parts.flatten], L) := by
  have hp : (Syn.param (.elem .bool) .none paramName).yield L =
      some ([[.elem .bool] ++ optToks idt paramName], L) := by
    cases paramName <;> rfl
  rw [Syn.yield]
  change ((Syn.param (.elem .bool) .none paramName).yield L).bind (fun p =>
    ((Syn.nil : Syn (.list .param)).yield p.2).bind (fun q =>
      ((Syn.block xs).yield q.2).bind (fun v => some
        ([tk .catch_ ++ optToks idt name ++ parens (commaSep (p.1.flatten :: q.1)) ++
          v.1.flatten], v.2)))) = _
  rw [hp]
  simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]
  have hn : (Syn.nil : Syn (.list .param)).yield L = some ([], L) := rfl
  rw [hn]
  simp only [Option.bind_some]
  rw [boolean_item_block_yield h L]
  simp only [Option.bind_some, commaSep, List.intersperse, List.flatten_cons,
    List.flatten_nil, List.append_nil]

/-- Intrinsic catch fragment: constructors carry syntax-derived body bounds,
not successful parse premises. The stored Nat is a sufficient parser budget. -/
inductive BooleanCatch : {k : SCtx} → Syn (.catchClause k) → List Tok → Nat → Prop where
  | plain {k : SCtx} {xs : Syn (.list (.item k))} {parts : List (List Tok)} {b : Nat} :
      BooleanListBound xs parts b →
      BooleanCatch (.catchPlain (.block xs)) (tk .catch_ ++ braces parts.flatten) (b + 2)
  | signature {k : SCtx} {xs : Syn (.list (.item k))} {parts : List (List Tok)} {b : Nat}
      (name paramName : Option String) : BooleanListBound xs parts b →
      BooleanCatch (.catchSig name (.param (.elem .bool) .none paramName) .nil (.block xs))
        (tk .catch_ ++ optToks idt name ++
          parens ([.elem .bool] ++ optToks idt paramName) ++ braces parts.flatten) (b + 6)

theorem boolean_catch_coverage {k : SCtx} {c : Syn (.catchClause k)} {ts : List Tok} {b : Nat}
    (h : BooleanCatch c ts b) (n : Nat) (s : St) :
    catchClause (n + b) k (locatedInput ts s) = .ok (c, s) := by
  cases h with
  | plain hb =>
    simpa only [plainCatchInput, blockInput, locatedInput_append, Nat.add_assoc] using
      boolean_list_plain_catch_coverage hb n s
  | signature name paramName hb =>
    simpa only [signatureCatchInput, blockInput, locatedInput_append, Nat.add_assoc] using
      boolean_list_signature_catch_coverage hb n name paramName s

theorem boolean_catch_yield {k : SCtx} {c : Syn (.catchClause k)} {ts : List Tok} {b : Nat}
    (h : BooleanCatch c ts b) (L : List Choice) : c.yield L = some ([ts], L) := by
  cases h with
  | plain hb => exact boolean_list_plain_catch_yield (boolean_list_bound_items hb) L
  | signature name paramName hb =>
    exact boolean_list_signature_catch_yield (boolean_list_bound_items hb) name paramName L

theorem boolean_catch_token_unique {k : SCtx} {c d : Syn (.catchClause k)}
    {ts us : List Tok} {b e : Nat} (hc : BooleanCatch c ts b) (hd : BooleanCatch d us e)
    (he : ts = us) : c = d := by
  subst us
  let s : St := ⟨[], [], 0⟩
  have pc := boolean_catch_coverage hc e s
  have pd := boolean_catch_coverage hd b s
  have fuel : e + b = b + e := by omega
  rw [fuel] at pc
  exact congrArg Prod.fst (Except.ok.inj (pc.symm.trans pd))

theorem boolean_catch_clauses_complete {k : SCtx} {xs : Syn (.list (.item k))}
    {parts : List (List Tok)} (h : BooleanItemList xs parts) :
    ∃ b, (∀ n s, catchClause (n + b + 2) k (plainCatchInput parts.flatten s) =
      .ok (.catchPlain (.block xs), s)) ∧
      (∀ n name paramName s,
        catchClause (n + b + 6) k (signatureCatchInput name paramName parts.flatten s) =
          .ok (.catchSig name (.param (.elem .bool) .none paramName) .nil (.block xs), s)) := by
  obtain ⟨b, hb⟩ := boolean_item_list_has_bound h
  exact ⟨b, boolean_list_plain_catch_coverage hb, boolean_list_signature_catch_coverage hb⟩

theorem boolean_catch_derives {k : SCtx} {c : Syn (.catchClause k)} {ts : List Tok} {b : Nat}
    (h : BooleanCatch c ts b) : c.Derives ts := by
  refine ⟨[], ?_⟩
  unfold Syn.toks
  rw [boolean_catch_yield h []]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

theorem boolean_catch_actual_yield_unique {k : SCtx} {c d : Syn (.catchClause k)}
    {ts us : List Tok} {b e : Nat} (hc : BooleanCatch c ts b) (hd : BooleanCatch d us e)
    (L M N P : List Choice) (parts qs : List (List Tok))
    (hyC : c.yield L = some (parts, M)) (hyD : d.yield N = some (qs, P))
    (he : parts.flatten = qs.flatten) : c = d := by
  have cp : [ts] = parts := congrArg Prod.fst
    (Option.some.inj ((boolean_catch_yield hc L).symm.trans hyC))
  have dp : [us] = qs := congrArg Prod.fst
    (Option.some.inj ((boolean_catch_yield hd N).symm.trans hyD))
  rw [← cp, ← dp] at he
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at he
  exact boolean_catch_token_unique hc hd he

#print axioms catch_plain_prefix
#print axioms catch_signature_prefix
#print axioms boolean_list_plain_catch_coverage
#print axioms boolean_list_signature_catch_coverage
#print axioms boolean_list_plain_catch_yield
#print axioms boolean_list_signature_catch_yield
#print axioms boolean_catch_coverage
#print axioms boolean_catch_yield
#print axioms boolean_catch_token_unique
#print axioms boolean_catch_clauses_complete
#print axioms boolean_catch_derives
#print axioms boolean_catch_actual_yield_unique
end Solidity.Frontend.StatementGrammarH28
