import Solidity.Frontend.LiteralGrammarH28.Classification

/-! # Exact literal splitting in each admitted lexer mode

The scanner theorem accepts any escaped bytes. Value relations supply the
stronger decoder facts separately. Pragma mode and assembly-head prefixed
literals retain their original exclusions.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem Scan.split_quoted {q : UInt8} (quote : IsQuote q)
    {raw pre suffix : Bytes} (h : Scan q raw pre suffix) (mode : Mode) (notPragma : mode ≠ .pragma) :
    split mode (q :: raw) = .ok (q :: pre, suffix) := by
  have scanned : untilQuote q raw = some (pre, suffix) := untilQuote_complete quote h
  cases mode <;> try exact False.elim (notPragma rfl)
  all_goals
    rcases quote with rfl | rfl
    · change (match untilQuote 34 raw with
        | some (p, s) => Except.ok (34 :: p, s)
        | none => Except.error "unterminated string literal") = _
      rw [scanned]
    · change (match untilQuote 39 raw with
        | some (p, s) => Except.ok (39 :: p, s)
        | none => Except.error "unterminated string literal") = _
      rw [scanned]

def HexMode (mode : Mode) : Prop := mode = .sol ∨ ∃ depth, mode = .yul depth

theorem Scan.split_hex {q : UInt8} (quote : IsQuote q)
    {raw pre suffix : Bytes} (h : Scan q raw pre suffix) (mode : Mode) (admitted : HexMode mode) :
    split mode (hexPrefix ++ q :: raw) = .ok (hexPrefix ++ q :: pre, suffix) := by
  have scanned : untilQuote q raw = some (pre, suffix) := untilQuote_complete quote h
  rcases admitted with rfl | ⟨depth, rfl⟩
  all_goals
    rcases quote with rfl | rfl
    · change (match untilQuote 34 raw with
        | some (p, s) => Except.ok (hexPrefix ++ 34 :: p, s)
        | none => Except.error "unterminated string literal") = _
      rw [scanned]
    · change (match untilQuote 39 raw with
        | some (p, s) => Except.ok (hexPrefix ++ 39 :: p, s)
        | none => Except.error "unterminated string literal") = _
      rw [scanned]

theorem Scan.split_unicode {q : UInt8} (quote : IsQuote q)
    {raw pre suffix : Bytes} (h : Scan q raw pre suffix) :
    split .sol (unicodePrefix ++ q :: raw) = .ok (unicodePrefix ++ q :: pre, suffix) := by
  have scanned : untilQuote q raw = some (pre, suffix) := untilQuote_complete quote h
  rcases quote with rfl | rfl
  · change (match untilQuote 34 raw with
      | some (p, s) => Except.ok (unicodePrefix ++ 34 :: p, s)
      | none => Except.error "unterminated string literal") = _
    rw [scanned]
  · change (match untilQuote 39 raw with
      | some (p, s) => Except.ok (unicodePrefix ++ 39 :: p, s)
      | none => Except.error "unterminated string literal") = _
    rw [scanned]

theorem split_yul_unicode_word (depth : Nat) (q : UInt8) (quote : IsQuote q) (raw : Bytes) :
    split (.yul depth) (unicodePrefix ++ q :: raw) = .ok (unicodePrefix, q :: raw) := by
  rcases quote with rfl | rfl <;> rfl

theorem Plain.split_mode {raw out : Bytes} (h : Plain raw out)
    (mode : Mode) (notPragma : mode ≠ .pragma) (suffix : Bytes) :
    split mode (raw ++ suffix) = .ok (raw, suffix) := by
  obtain ⟨q, body, ⟨quote, rfl⟩, value⟩ := h
  have scanner : Scan q (body ++ q :: suffix) (body ++ [q]) suffix := value.scan quote (printable_safe q) suffix
  simpa only [List.cons_append, List.append_assoc, List.nil_append] using
    scanner.split_quoted quote mode notPragma

theorem HexLiteral.split {raw out : Bytes} (h : HexLiteral raw out)
    (mode : Mode) (admitted : HexMode mode) (suffix : Bytes) :
    split mode (raw ++ suffix) = .ok (raw, suffix) := by
  obtain ⟨q, body, quote, rfl, value⟩ := h
  have scanner : Scan q (body ++ q :: suffix) (body ++ [q]) suffix := value.scan quote suffix
  simpa only [quoteBytes, List.cons_append, List.append_assoc, List.nil_append] using
    scanner.split_hex quote mode admitted

theorem UnicodeLiteral.split {raw out : Bytes} (h : UnicodeLiteral raw out) (suffix : Bytes) :
    split .sol (raw ++ suffix) = .ok (raw, suffix) := by
  obtain ⟨q, body, quote, rfl, _, _, value⟩ := h
  have scanner : Scan q (body ++ q :: suffix) (body ++ [q]) suffix := value.scan quote (unicode_safe q) suffix
  simpa only [quoteBytes, List.cons_append, List.append_assoc, List.nil_append] using
    scanner.split_unicode quote

end Solidity.Frontend.LiteralGrammarH28
