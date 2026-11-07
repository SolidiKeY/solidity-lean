import Solidity.Frontend.LiteralGrammarH28.Classification

/-! # Independent fragment sequences and byte concatenation

Each source fragment has its own delimiters and decoder invocation. The grammar
never merges raw escape bodies across a fragment boundary. Universal sequence
proofs concern arbitrary finite fragment lists, not bounded samples. Compiler
source/typing adequacy remains an external test boundary.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive Fragments (literal : Bytes → Bytes → Prop) : List Bytes → List Bytes → Prop where
  | nil : Fragments literal [] []
  | cons {raw out : Bytes} {raws values : List Bytes} : literal raw out →
      Fragments literal raws values → Fragments literal (raw :: raws) (out :: values)

def FragmentValue (literal : Bytes → Bytes → Prop) (raws : List Bytes) (out : Bytes) : Prop :=
  ∃ values, Fragments literal raws values ∧ out = values.flatten

theorem fragments_mapM_iff (literal : Bytes → Bytes → Prop) (decoder : Bytes → Option Bytes)
    (spec : ∀ raw out, decoder raw = some out ↔ literal raw out)
    (raws values : List Bytes) : raws.mapM decoder = some values ↔ Fragments literal raws values := by
  constructor
  · intro h
    induction raws generalizing values with
    | nil => cases h; exact .nil
    | cons raw raws ih =>
      cases hd : decoder raw with
      | none => rw [List.mapM_cons, hd] at h; cases h
      | some out =>
        cases ht : raws.mapM decoder with
        | none => rw [List.mapM_cons, hd, ht] at h; cases h
        | some rest =>
          rw [List.mapM_cons, hd, ht] at h
          cases h
          exact .cons ((spec raw out).mp hd) (ih rest ht)
  · intro h
    induction h with
    | nil => rfl
    | @cons raw out raws values first _ ih =>
      rw [List.mapM_cons, (spec raw out).mpr first, ih]
      rfl

theorem Fragments.append {literal : Bytes → Bytes → Prop}
    {left right lvalues rvalues : List Bytes}
    (hleft : Fragments literal left lvalues) (hright : Fragments literal right rvalues) :
    Fragments literal (left ++ right) (lvalues ++ rvalues) := by
  induction hleft with
  | nil => exact hright
  | cons first _ ih => exact .cons first ih

theorem FragmentValue.append {literal : Bytes → Bytes → Prop}
    {left right : List Bytes} {a b : Bytes}
    (ha : FragmentValue literal left a) (hb : FragmentValue literal right b) :
    FragmentValue literal (left ++ right) (a ++ b) := by
  obtain ⟨av, ag, rfl⟩ := ha
  obtain ⟨bv, bg, rfl⟩ := hb
  exact ⟨av ++ bv, ag.append bg, List.flatten_append.symm⟩

theorem fragments_none_iff (literal : Bytes → Bytes → Prop) (decoder : Bytes → Option Bytes)
    (spec : ∀ raw out, decoder raw = some out ↔ literal raw out) (raws : List Bytes) :
    raws.mapM decoder = none ↔ ∀ values, ¬ Fragments literal raws values := by
  constructor
  · intro hn values h
    have e : raws.mapM decoder = some values := (fragments_mapM_iff literal decoder spec raws values).mpr h
    rw [hn] at e
    cases e
  · intro h
    cases e : raws.mapM decoder with
    | none => rfl
    | some values => exact False.elim (h values ((fragments_mapM_iff literal decoder spec raws values).mp e))

theorem Fragments.classified {literal : Bytes → Bytes → Prop}
    (classifier : Bytes → Option Tok) (tag : Bytes → Tok)
    (sound : ∀ raw out, literal raw out → classifier raw = some (tag out))
    {raws values : List Bytes} (h : Fragments literal raws values) :
    raws.mapM classifier = some (values.map tag) := by
  induction h with
  | nil => rfl
  | @cons raw out raws values first _ ih =>
    rw [List.mapM_cons, sound raw out first, ih]
    rfl

theorem Fragments.plain_classified {raws values : List Bytes} (h : Fragments Plain raws values) :
    raws.mapM solTok = some (values.map Tok.str) :=
  h.classified solTok Tok.str (fun _ _ h => h.solTok)

theorem Fragments.hex_classified {raws values : List Bytes} (h : Fragments HexLiteral raws values) :
    raws.mapM solTok = some (values.map Tok.hexStr) :=
  h.classified solTok Tok.hexStr (fun _ _ h => h.solTok)

theorem Fragments.unicode_classified {raws values : List Bytes} (h : Fragments UnicodeLiteral raws values) :
    raws.mapM solTok = some (values.map Tok.unicodeStr) :=
  h.classified solTok Tok.unicodeStr (fun _ _ h => h.solTok)

theorem encoded_fragments_grammar (q : UInt8) (quote : IsQuote q) (values : List Bytes) :
    Fragments Plain (values.map (fun b => quoteBytes q (encodeBody b))) values := by
  induction values with
  | nil => exact .nil
  | cons bytes rest ih =>
    exact .cons ⟨q, encodeBody bytes, quoteBytes_quoted q quote _, encodeBody_grammar _ _⟩ ih

theorem encoded_fragments_roundtrip (q : UInt8) (quote : IsQuote q) (values : List Bytes) :
    (values.map (fun b => quoteBytes q (encodeBody b))).mapM plainString = some values :=
  (fragments_mapM_iff Plain plainString plainString_iff _ _).mpr (encoded_fragments_grammar q quote values)

theorem encoded_fragments_value (q : UInt8) (quote : IsQuote q) (values : List Bytes) :
    FragmentValue Plain (values.map (fun b => quoteBytes q (encodeBody b))) values.flatten :=
  ⟨values, encoded_fragments_grammar q quote values, rfl⟩

theorem Plain.split {raw out : Bytes} (h : Plain raw out) (suffix : Bytes) :
    split .sol (raw ++ suffix) = .ok (raw, suffix) := by
  obtain ⟨q, body, ⟨quote, rfl⟩, value⟩ := h
  have scanned : untilQuote q (body ++ q :: suffix) = some (body ++ [q], suffix) :=
    (body_scan_value quote (printable_safe q) value suffix).1
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  rcases quote with rfl | rfl
  · change (match untilQuote 34 (body ++ 34 :: suffix) with
      | some (pre, rest) => Except.ok (34 :: pre, rest)
      | none => Except.error "unterminated string literal") = _
    rw [scanned]
  · change (match untilQuote 39 (body ++ 39 :: suffix) with
      | some (pre, rest) => Except.ok (39 :: pre, rest)
      | none => Except.error "unterminated string literal") = _
    rw [scanned]

/-- The next source fragment is consumed exactly, leaving all remaining fragments. -/
theorem Fragments.split_head {raw out : Bytes} {raws values : List Bytes}
    (h : Fragments Plain (raw :: raws) (out :: values)) :
    split .sol (raw ++ raws.flatten) = .ok (raw, raws.flatten) := by
  cases h with
  | cons first _ => exact first.split _

end Solidity.Frontend.LiteralGrammarH28
