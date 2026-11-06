import Solidity.Frontend.TypeGrammarH28.ParserChecks

/-! Independent qualified-name parsing contracts, with arbitrary locations.
The step below is definitionally the frozen idPath loop, not a new parser. -/
namespace Solidity.Frontend.TypeGrammarH28.ParserPath
open Solidity.Source Solidity.Frontend.Checked ParserBasic

def pathStep : P (Option String) := do
  if (← peek) == some (.punct .period) then
    match ← peekN 1 with
    | some (.ident s) => advance; advance; return some s
    | _ => return none
  else return none

def pathTailTokens (parts : List String) : List Tok :=
  parts.flatMap fun s => [.punct .period, .ident s]

theorem path_step_empty (ch : List Choice) (eof : Nat) :
    pathStep ⟨[], ch, eof⟩ = .ok (none, ⟨[], ch, eof⟩) := rfl

theorem path_step_pair (name : String) (a b c d : Nat)
    (rest : List Located) (ch : List Choice) (eof : Nat) :
    pathStep ⟨⟨.punct .period, a, b⟩ :: ⟨.ident name, c, d⟩ :: rest, ch, eof⟩ =
      .ok (some name, ⟨rest, ch, eof⟩) := rfl

theorem many_stop {α : Type} (p : P (Option α)) (fuel : Nat) (s : St)
    (hp : p s = .ok (none, s)) : manyAux p (fuel + 1) s = .ok ([], s) := by
  change (p s >>= _) = _
  rw [hp]
  rfl

theorem many_step {α : Type} (p : P (Option α)) (fuel : Nat) (s s' s'' : St)
    (a : α) (as : List α) (hp : p s = .ok (some a, s'))
    (hr : manyAux p fuel s' = .ok (as, s'')) :
    manyAux p (fuel + 1) s = .ok (a :: as, s'') := by
  change (p s >>= _) = _
  rw [hp]
  change (manyAux p fuel s' >>= _) = _
  rw [hr]
  rfl

theorem path_tail_complete (parts : List String) (n : Nat) (front rest : List Located)
    (ch : List Choice) (eof : Nat)
    (hfront : front.map Located.tok = pathTailTokens parts)
    (hstop : pathStep ⟨rest, ch, eof⟩ = .ok (none, ⟨rest, ch, eof⟩)) :
    manyAux pathStep (n + parts.length + 1) ⟨front ++ rest, ch, eof⟩ =
      .ok (parts, ⟨rest, ch, eof⟩) := by
  induction parts generalizing front with
  | nil =>
    have hf : front = [] := located_nil front hfront
    cases hf
    exact many_stop pathStep n ⟨rest, ch, eof⟩ hstop
  | cons name parts ih =>
    change front.map Located.tok = .punct .period :: .ident name :: pathTailTokens parts at hfront
    obtain ⟨head, tail, he, ht, hr⟩ := located_cons front _ _ hfront
    obtain ⟨next, tail', he', ht', hr'⟩ := located_cons tail _ _ hr
    cases he
    cases he'
    cases head with
    | mk tok a b =>
      cases ht
      cases next with
      | mk tok c d =>
        cases ht'
        exact many_step pathStep (n + parts.length + 1) _ _ _ name parts
          (path_step_pair name a b c d (tail' ++ rest) ch eof) (ih tail' hr')

theorem path_tail_budget (parts : List String) :
    parts.length ≤ (pathTailTokens parts).length := by
  induction parts with
  | nil => exact Nat.le_refl 0
  | cons name parts ih =>
    change parts.length + 1 ≤ (pathTailTokens parts).length + 1 + 1
    exact Nat.le_trans (Nat.succ_le_succ ih) (Nat.le_succ _)

theorem path_tail_complete_ge (parts : List String) (fuel : Nat)
    (hf : parts.length + 1 ≤ fuel) (front rest : List Located)
    (ch : List Choice) (eof : Nat)
    (hfront : front.map Located.tok = pathTailTokens parts)
    (hstop : pathStep ⟨rest, ch, eof⟩ = .ok (none, ⟨rest, ch, eof⟩)) :
    manyAux pathStep fuel ⟨front ++ rest, ch, eof⟩ = .ok (parts, ⟨rest, ch, eof⟩) := by
  have he : fuel - (parts.length + 1) + parts.length + 1 = fuel :=
    (Nat.add_assoc _ _ _).trans (Nat.sub_add_cancel hf)
  rw [← he]
  exact path_tail_complete parts _ front rest ch eof hfront hstop

/-- Qualified-name completeness with an independently recognized terminal
boundary, preserving every actual location and all original layout choices. -/
theorem path_complete (p : IdPath) (front rest : List Located)
    (ch : List Choice) (eof : Nat)
    (hfront : front.map Located.tok = p.toks)
    (hstop : pathStep ⟨rest, ch, eof⟩ = .ok (none, ⟨rest, ch, eof⟩)) :
    idPath ⟨front ++ rest, ch, eof⟩ = .ok (p, ⟨rest, ch, eof⟩) := by
  cases p with
  | mk name parts =>
    obtain ⟨head, tail, he, ht, hr⟩ := located_cons front _ _ hfront
    cases he
    cases head with
    | mk tok a b =>
      cases ht
      have hl : tail.length = (pathTailTokens parts).length := by
        have h := congrArg List.length hr
        simpa only [List.length_map] using h
      have hb : parts.length ≤ (tail ++ rest).length := by
        rw [List.length_append, hl]
        exact Nat.le_trans (path_tail_budget parts) (Nat.le_add_right _ _)
      have hh := path_tail_complete_ge parts ((tail ++ rest).length + 1)
        (Nat.succ_le_succ hb) tail rest ch eof hr hstop
      change (manyAux pathStep ((tail ++ rest).length + 1) ⟨tail ++ rest, ch, eof⟩ >>= _) = _
      rw [hh]
      rfl

theorem path_eof (p : IdPath) (ls : List Located) (ch : List Choice) (eof : Nat)
    (h : ls.map Located.tok = p.toks) :
    idPath ⟨ls, ch, eof⟩ = .ok (p, ⟨[], ch, eof⟩) := by
  have hp := path_complete p ls [] ch eof h (path_step_empty ch eof)
  simpa only [List.append_nil] using hp

theorem user_type_complete (n : Nat) (p : IdPath) (front rest : List Located)
    (ch : List Choice) (eof : Nat)
    (hfront : front.map Located.tok = p.toks)
    (hpath : pathStep ⟨rest, ch, eof⟩ = .ok (none, ⟨rest, ch, eof⟩))
    (hsuffix : eat (.punct .lbrack) ⟨rest, ch, eof⟩ = .ok (false, ⟨rest, ch, eof⟩)) :
    typeName (n + 2) ⟨front ++ rest, ch, eof⟩ = .ok (.userType p, ⟨rest, ch, eof⟩) := by
  have hp := path_complete p front rest ch eof hfront hpath
  obtain ⟨head, tail, he, ht, hr⟩ := located_cons front _ _ hfront
  cases he
  cases head with
  | mk tok a b =>
    cases ht
    change (idPath ⟨⟨.ident p.head, a, b⟩ :: (tail ++ rest), ch, eof⟩ >>= _) = _
    simp only [List.cons_append] at hp
    rw [hp]
    exact suffix_stop n (.userType p) ⟨rest, ch, eof⟩ hsuffix

theorem user_yield_eof (p : IdPath) (n : Nat) (ls : List Located)
    (ch : List Choice) (eof : Nat) (h : ls.map Located.tok = p.toks) :
    typeName (n + 2) ⟨ls, ch, eof⟩ = .ok (.userType p, ⟨[], ch, eof⟩) := by
  have hp := user_type_complete n p ls [] ch eof h (path_step_empty ch eof) rfl
  simpa only [List.append_nil] using hp

theorem user_complete_ge (p : IdPath) (fuel : Nat) (hf : 2 ≤ fuel)
    (ls : List Located) (ch : List Choice) (eof : Nat)
    (h : ls.map Located.tok = p.toks) :
    typeName fuel ⟨ls, ch, eof⟩ = .ok (.userType p, ⟨[], ch, eof⟩) := by
  have he : fuel - 2 + 2 = fuel := Nat.sub_add_cancel hf
  rw [← he]
  exact user_yield_eof p _ ls ch eof h

theorem user_located_complete (p : IdPath) (ls : List Located) (eof : Nat)
    (h : ls.map Located.tok = p.toks) :
    parseCatLocated typeName eof ls = .ok (.userType p, []) := by
  have hf : 2 ≤ 16 * (ls.length + 1) :=
    Nat.le_trans (by decide : 2 ≤ 16) (Nat.le_mul_of_pos_right 16 (Nat.succ_pos ls.length))
  have hraw := user_complete_ge p _ hf ls [] eof h
  apply ParserCheck.checked_category_converse typeName eof ls (.userType p) ⟨[], [], eof⟩ hraw rfl
  · change (Syn.userType p).toks [] = some (ls.map Located.tok)
    rw [userType_toks, h]
  · rfl

theorem user_parseCat_complete (p : IdPath) (src : Bytes) (ps : List Piece)
    (hlex : lex src = .ok ps) (ht : tokensOf ps = p.toks) :
    parseCat typeName src = .ok (.userType p, []) := by
  unfold parseCat
  rw [hlex]
  apply user_located_complete
  rw [List.map_map]
  change (locate .sol 0 ps).map (fun x => x.1.tok) = p.toks
  rw [locate_toks]
  exact ht

theorem parseType_user_complete (p : IdPath) (src : Bytes) (ps : List Piece)
    (hlex : lex src = .ok ps) (ht : tokensOf ps = p.toks) :
    parseType src = .ok (.userType p) := by
  unfold parseType
  rw [user_parseCat_complete p src ps hlex ht]
  rfl

theorem parseType_user_iff (p : IdPath) (src : Bytes) :
    parseType src = .ok (.userType p) ↔ ∃ ps : List Piece, lex src = .ok ps ∧ tokensOf ps = p.toks := by
  constructor
  · intro h
    obtain ⟨ps, hlex, hd, hp⟩ := parseType_derives h
    obtain ⟨layout, hy⟩ := hd
    cases layout with
    | nil =>
      rw [userType_toks] at hy
      exact ⟨ps, hlex, (Option.some.inj hy).symm⟩
    | cons choice rest =>
      rw [userType_no_unused_layout] at hy
      cases hy
  · intro h
    obtain ⟨ps, hlex, ht⟩ := h
    exact parseType_user_complete p src ps hlex ht

theorem user_tokens_injective (p q : IdPath) (h : p.toks = q.toks) : p = q := by
  let ls : List Located := ParserCheck.witnessLocations p.toks
  have hp : ls.map Located.tok = p.toks := ParserCheck.witness_locations_tokens p.toks
  have hq : ls.map Located.tok = q.toks := hp.trans h
  have hl := user_yield_eof p 0 ls [] 0 hp
  have hr := user_yield_eof q 0 ls [] 0 hq
  have he : (Syn.userType p, (⟨[], [], 0⟩ : St)) = (Syn.userType q, (⟨[], [], 0⟩ : St)) :=
    Except.ok.inj (hl.symm.trans hr)
  exact Syn.userType.inj (Prod.mk.inj he).1

theorem user_yield_unique (p q : IdPath) (left right : List Choice) (ts : List Tok)
    (hl : (Syn.userType p).toks left = some ts)
    (hr : (Syn.userType q).toks right = some ts) :
    p = q ∧ LayoutEquivalent (Syn.userType p) left right := by
  cases left with
  | cons choice rest => rw [userType_no_unused_layout] at hl; cases hl
  | nil =>
    cases right with
    | cons choice rest => rw [userType_no_unused_layout] at hr; cases hr
    | nil =>
      have hp : p.toks = ts := Option.some.inj ((userType_toks p).symm.trans hl)
      have hq : q.toks = ts := Option.some.inj ((userType_toks q).symm.trans hr)
      exact ⟨user_tokens_injective p q (hp.trans hq.symm), ⟨ts, hl, hl⟩⟩

/-- A period without a following identifier is left for the surrounding
parser/checker to reject, rather than silently consumed as a path segment. -/
theorem path_step_lone_period (a b : Nat) (ch : List Choice) (eof : Nat) :
    pathStep ⟨[⟨.punct .period, a, b⟩], ch, eof⟩ =
      .ok (none, ⟨[⟨.punct .period, a, b⟩], ch, eof⟩) := rfl

theorem path_step_period_elem (e : Elem) (a b c d : Nat)
    (rest : List Located) (ch : List Choice) (eof : Nat) :
    pathStep ⟨⟨.punct .period, a, b⟩ :: ⟨.elem e, c, d⟩ :: rest, ch, eof⟩ =
      .ok (none, ⟨⟨.punct .period, a, b⟩ :: ⟨.elem e, c, d⟩ :: rest, ch, eof⟩) := rfl

theorem user_trailing_period_refused (name : String) (a b c d eof : Nat) :
    parseCatLocated typeName eof [⟨.ident name, a, b⟩, ⟨.punct .period, c, d⟩] =
      .error ⟨c, "unexpected token"⟩ := by
  have hraw : typeName (16 * (([⟨.ident name, a, b⟩, ⟨.punct .period, c, d⟩] : List Located).length + 1))
      ⟨[⟨.ident name, a, b⟩, ⟨.punct .period, c, d⟩], [], eof⟩ =
      .ok (.userType ⟨name, []⟩, ⟨[⟨.punct .period, c, d⟩], [], eof⟩) :=
    user_type_complete 46 ⟨name, []⟩ [⟨.ident name, a, b⟩] [⟨.punct .period, c, d⟩] [] eof rfl rfl rfl
  unfold parseCatLocated
  rw [hraw]
  rfl

#print axioms path_step_empty
#print axioms path_step_pair
#print axioms many_stop
#print axioms many_step
#print axioms path_tail_complete
#print axioms path_tail_budget
#print axioms path_tail_complete_ge
#print axioms path_complete
#print axioms path_eof
#print axioms user_type_complete
#print axioms user_yield_eof
#print axioms user_complete_ge
#print axioms user_located_complete
#print axioms user_parseCat_complete
#print axioms parseType_user_complete
#print axioms parseType_user_iff
#print axioms user_tokens_injective
#print axioms user_yield_unique
#print axioms path_step_lone_period
#print axioms path_step_period_elem
#print axioms user_trailing_period_refused
end Solidity.Frontend.TypeGrammarH28.ParserPath
