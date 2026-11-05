import Solidity.Frontend.Checked.Check
import Solidity.Frontend.TypeGrammarH28.ParserBasics
import Solidity.Frontend.TypeGrammarH28.Layouts

/-! Checked-parser converse and independently proved elementary completeness.
The generic checker lemma assumes a raw parse; the elementary theorem below
discharges that premise constructively, rather than assuming completeness. -/
namespace Solidity.Frontend.TypeGrammarH28.ParserCheck
open Solidity.Source Solidity.Frontend.Checked ParserBasic

/-- Exact converse of the checked-category guards for a given raw result. -/
theorem checked_category_converse {c : Cat} (p : Nat → P (Syn c)) (eof : Nat)
    (ls : List Located) (t : Syn c) (s : St)
    (hraw : p (16 * (ls.length + 1)) ⟨ls, [], eof⟩ = .ok (t, s))
    (hend : s.ts = []) (hy : t.toks s.ch.reverse = some (ls.map Located.tok))
    (hprec : t.prec = true) : parseCatLocated p eof ls = .ok (t, s.ch.reverse) := by
  unfold parseCatLocated
  rw [hraw]
  change (if !s.ts.isEmpty then _ else if t.toks s.ch.reverse ≠ some (ls.map Located.tok) then _
    else if t.prec = false then _ else (Except.ok (t, s.ch.reverse) : Except Error (Syn c × List Choice))) =
    (Except.ok (t, s.ch.reverse) : Except Error (Syn c × List Choice))
  rw [hend]
  change (if t.toks s.ch.reverse ≠ some (ls.map Located.tok) then _
    else if t.prec = false then _ else (Except.ok (t, s.ch.reverse) : Except Error (Syn c × List Choice))) =
    (Except.ok (t, s.ch.reverse) : Except Error (Syn c × List Choice))
  have hn : ¬ (t.toks s.ch.reverse ≠ some (ls.map Located.tok)) := fun h => h hy
  rw [if_neg hn, hprec]
  rfl

/-- All elementary forms pass the actual checked parser at its frozen fuel,
with arbitrary real source locations and no additional language restriction. -/
theorem elem_located_complete (e : Elem) (ls : List Located) (eof : Nat)
    (h : ls.map Located.tok = e.toks) :
    parseCatLocated typeName eof ls = .ok (.elem e, []) := by
  have hf : 2 ≤ 16 * (ls.length + 1) :=
    Nat.le_trans (by decide : 2 ≤ 16) (Nat.le_mul_of_pos_right 16 (Nat.succ_pos ls.length))
  have hraw : typeName (16 * (ls.length + 1)) ⟨ls, [], eof⟩ =
      .ok (.elem e, ⟨[], [], eof⟩) := elem_complete_ge e _ hf ls [] eof h
  apply checked_category_converse typeName eof ls (.elem e) ⟨[], [], eof⟩ hraw rfl
  · change (Syn.elem e).toks [] = some (ls.map Located.tok)
    rw [elem_toks, h]
  · rfl

theorem elem_parseCat_complete (e : Elem) (src : Bytes) (ps : List Piece)
    (hlex : lex src = .ok ps) (ht : tokensOf ps = e.toks) :
    parseCat typeName src = .ok (.elem e, []) := by
  unfold parseCat
  rw [hlex]
  apply elem_located_complete
  rw [List.map_map]
  change (locate .sol 0 ps).map (fun x => x.1.tok) = e.toks
  rw [locate_toks]
  exact ht

/-- Source-level parseType corollary; lexical success is the independent G08
boundary, not an assumed type-parser success premise. -/
theorem parseType_elem_complete (e : Elem) (src : Bytes) (ps : List Piece)
    (hlex : lex src = .ok ps) (ht : tokensOf ps = e.toks) :
    parseType src = .ok (.elem e) := by
  unfold parseType
  rw [elem_parseCat_complete e src ps hlex ht]
  rfl

/-- The actual checker rejects the artificial raw token counterexample. -/
theorem artificial_payable_refused :
    parseCatLocated typeName 1 [⟨.elem .addressPayable, 0, 1⟩] =
      .error ⟨0, "parser check failed: yield mismatch"⟩ := by
  let ls : List Located := [⟨.elem .addressPayable, 0, 1⟩]
  have hraw : typeName (16 * (ls.length + 1)) ⟨ls, [], 1⟩ =
      .ok (.elem .addressPayable, ⟨[], [], 1⟩) := elem_token_eof .addressPayable 30 0 1 [] 1
  change parseCatLocated typeName 1 ls = _
  unfold parseCatLocated
  rw [hraw]
  rfl

/-- Elementary source parsing is characterized by the existing lexer tokens. -/
theorem parseType_elem_iff (e : Elem) (src : Bytes) :
    parseType src = .ok (.elem e) ↔ ∃ ps : List Piece, lex src = .ok ps ∧ tokensOf ps = e.toks := by
  constructor
  · intro h
    obtain ⟨ps, hlex, hd, hp⟩ := parseType_derives h
    obtain ⟨layout, hy⟩ := hd
    cases layout with
    | nil =>
      rw [elem_toks] at hy
      have he : e.toks = tokensOf ps := Option.some.inj hy
      exact ⟨ps, hlex, he.symm⟩
    | cons choice rest =>
      rw [elem_no_unused_layout] at hy
      cases hy
  · intro h
    obtain ⟨ps, hlex, ht⟩ := h
    exact parseType_elem_complete e src ps hlex ht

/-- A token-only witness for the deterministic-parser uniqueness argument. -/
def witnessLocations (ts : List Tok) : List Located := ts.map fun t => ⟨t, 0, 0⟩

theorem witness_locations_tokens (ts : List Tok) :
    (witnessLocations ts).map Located.tok = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => exact congrArg (List.cons t) ih

/-- Actual elementary yield injectivity, derived from the proved raw
completeness at a common fuel. No type-name uniqueness premise is assumed. -/
theorem elem_tokens_injective (e f : Elem) (h : e.toks = f.toks) : e = f := by
  let ls : List Located := witnessLocations e.toks
  have he : ls.map Located.tok = e.toks := witness_locations_tokens e.toks
  have hf : ls.map Located.tok = f.toks := he.trans h
  have hl : typeName 2 ⟨ls, [], 0⟩ = .ok (.elem e, ⟨[], [], 0⟩) :=
    elem_yield_eof e 0 ls [] 0 he
  have hr : typeName 2 ⟨ls, [], 0⟩ = .ok (.elem f, ⟨[], [], 0⟩) :=
    elem_yield_eof f 0 ls [] 0 hf
  have hp : (Syn.elem e, (⟨[], [], 0⟩ : St)) = (Syn.elem f, (⟨[], [], 0⟩ : St)) :=
    Except.ok.inj (hl.symm.trans hr)
  exact Syn.elem.inj (Prod.mk.inj hp).1

/-- Elementary constructor grammar exactness includes successful exact layout
equivalence; unused layouts cannot create an alternative elementary tree. -/
theorem elem_yield_unique (e f : Elem) (left right : List Choice) (ts : List Tok)
    (hl : (Syn.elem e).toks left = some ts) (hr : (Syn.elem f).toks right = some ts) :
    e = f ∧ LayoutEquivalent (Syn.elem e) left right := by
  cases left with
  | cons choice rest => rw [elem_no_unused_layout] at hl; cases hl
  | nil =>
    cases right with
    | cons choice rest => rw [elem_no_unused_layout] at hr; cases hr
    | nil =>
      have he : e.toks = ts := Option.some.inj ((elem_toks e).symm.trans hl)
      have hf : f.toks = ts := Option.some.inj ((elem_toks f).symm.trans hr)
      exact ⟨elem_tokens_injective e f (he.trans hf.symm), ⟨ts, hl, hl⟩⟩

/-- For an actual raw result, the checker accepts exactly EOF, exact yield and
precedence. This is guard soundness/converse, not assumed raw completeness. -/
theorem checked_category_iff {c : Cat} (p : Nat → P (Syn c)) (eof : Nat)
    (ls : List Located) (t : Syn c) (s : St)
    (hraw : p (16 * (ls.length + 1)) ⟨ls, [], eof⟩ = .ok (t, s)) :
    parseCatLocated p eof ls = .ok (t, s.ch.reverse) ↔
      s.ts = [] ∧ t.toks s.ch.reverse = some (ls.map Located.tok) ∧ t.prec = true := by
  constructor
  · intro h
    unfold parseCatLocated at h
    rw [hraw] at h
    change (if !s.ts.isEmpty then _ else if t.toks s.ch.reverse ≠ some (ls.map Located.tok) then _
      else if t.prec = false then _ else (Except.ok (t, s.ch.reverse) : Except Error (Syn c × List Choice))) =
        (Except.ok (t, s.ch.reverse) : Except Error (Syn c × List Choice)) at h
    split at h
    · cases h
    · next heof =>
      split at h
      · cases h
      · next hyield =>
        split at h
        · cases h
        · next hprec =>
          have hempty : s.ts.isEmpty = true := by
            cases hb : s.ts.isEmpty with
            | false => rw [hb] at heof; exact False.elim (heof rfl)
            | true => rfl
          have hp : t.prec = true := by
            cases hb : t.prec with
            | false => rw [hb] at hprec; exact False.elim (hprec rfl)
            | true => rfl
          exact ⟨List.isEmpty_iff.mp hempty, Decidable.of_not_not hyield, hp⟩
  · intro h
    exact checked_category_converse p eof ls t s hraw h.1 h.2.1 h.2.2

#print axioms checked_category_converse
#print axioms elem_located_complete
#print axioms elem_parseCat_complete
#print axioms parseType_elem_complete
#print axioms artificial_payable_refused
#print axioms parseType_elem_iff
#print axioms witness_locations_tokens
#print axioms elem_tokens_injective
#print axioms elem_yield_unique
#print axioms checked_category_iff

end Solidity.Frontend.TypeGrammarH28.ParserCheck
