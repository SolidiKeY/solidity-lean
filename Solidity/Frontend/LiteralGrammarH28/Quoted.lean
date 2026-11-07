import Solidity.Frontend.LiteralGrammarH28.Body

/-! # Whole quoted bodies and plain literal values

Delimiter grammar is independent of quotedBody: a single or double quote,
an arbitrary byte body and a matching closing quote. Plain literals additionally
carry independent Body evidence for the printable predicate of their delimiter.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def IsQuote (q : UInt8) : Prop := q = 34 ∨ q = 39

def Quoted (raw : Bytes) (q : UInt8) (body : Bytes) : Prop :=
  IsQuote q ∧ raw = q :: (body ++ [q])

theorem quotedBody_complete {raw : Bytes} {q : UInt8} {body : Bytes}
    (h : Quoted raw q body) : quotedBody raw = some (q, body) := by
  obtain ⟨quote, rfl⟩ := h
  rcases quote with rfl | rfl <;>
    simp only [quotedBody, List.getLast?_concat, List.dropLast_concat] <;> rfl

theorem quotedBody_sound (raw : Bytes) (q : UInt8) (body : Bytes)
    (h : quotedBody raw = some (q, body)) : Quoted raw q body := by
  cases raw with
  | nil => cases h
  | cons opener tail =>
    simp only [quotedBody] at h
    split at h
    · rename_i guard
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at guard
      cases h
      obtain ⟨inside, rfl⟩ := List.getLast?_eq_some_iff.mp guard.2
      constructor
      · rcases guard.1 with eq | eq
        · exact Or.inl (UInt8.toNat_inj.mp eq)
        · exact Or.inr (UInt8.toNat_inj.mp eq)
      · rw [List.dropLast_concat]
    · cases h

theorem quotedBody_iff (raw : Bytes) (q : UInt8) (body : Bytes) :
    quotedBody raw = some (q, body) ↔ Quoted raw q body :=
  ⟨quotedBody_sound raw q body, quotedBody_complete⟩

def Plain (raw out : Bytes) : Prop :=
  ∃ q body, Quoted raw q body ∧ Body (printable q) body out

theorem plainString_complete {raw out : Bytes} (h : Plain raw out) :
    plainString raw = some out := by
  obtain ⟨q, body, quoted, decoded⟩ := h
  unfold plainString
  rw [quotedBody_complete quoted]
  exact body_complete decoded

theorem plainString_sound (raw out : Bytes) (h : plainString raw = some out) :
    Plain raw out := by
  unfold plainString at h
  cases e : quotedBody raw with
  | none => rw [e] at h; cases h
  | some pair =>
    rcases pair with ⟨q, body⟩
    rw [e] at h
    exact ⟨q, body, quotedBody_sound raw q body e, body_sound (printable q) body out h⟩

theorem plainString_iff (raw out : Bytes) : plainString raw = some out ↔ Plain raw out :=
  ⟨plainString_sound raw out, plainString_complete⟩

/-- A constructive whole-literal spelling for every byte list and either quote. -/
def quoteBytes (q : UInt8) (body : Bytes) : Bytes := q :: (body ++ [q])

theorem quoteBytes_quoted (q : UInt8) (quote : IsQuote q) (body : Bytes) :
    Quoted (quoteBytes q body) q body := ⟨quote, rfl⟩

theorem encodePlain_roundtrip (q : UInt8) (quote : IsQuote q) (bytes : Bytes) :
    plainString (quoteBytes q (encodeBody bytes)) = some bytes :=
  plainString_complete ⟨q, encodeBody bytes, quoteBytes_quoted q quote _, encodeBody_grammar _ _⟩

theorem quoteBytes_length (q : UInt8) (body : Bytes) :
    (quoteBytes q body).length = body.length + 2 := by
  simp only [quoteBytes, List.length_cons, List.length_append, List.length_nil]

theorem encodePlain_length (q : UInt8) (bytes : Bytes) :
    (quoteBytes q (encodeBody bytes)).length = 4 * bytes.length + 2 := by
  rw [quoteBytes_length, encodeBody_length]

end Solidity.Frontend.LiteralGrammarH28
