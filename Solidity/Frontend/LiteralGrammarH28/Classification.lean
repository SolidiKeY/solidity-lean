import Solidity.Frontend.LiteralGrammarH28.Scanner

/-! # Literal classification and exact refusal boundaries

The independent value relations retain the existing raw unicode line/bidi
guards. They add neither a UTF8 validity check nor a scalar-value premise.
Numeric/EIP55 implementations remain unchanged.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def hexPrefix : Bytes := [104, 101, 120]
def unicodePrefix : Bytes := [117, 110, 105, 99, 111, 100, 101]

def HexLiteral (raw out : Bytes) : Prop :=
  ∃ q body, IsQuote q ∧ raw = hexPrefix ++ quoteBytes q body ∧ HexBody body out

def UnicodeLiteral (raw out : Bytes) : Prop :=
  ∃ q body, IsQuote q ∧ raw = unicodePrefix ++ quoteBytes q body ∧
    irregularBreak body = false ∧ bidiBalanced body = true ∧ Body (unicodeChar q) body out

theorem quoted_plain_eq (q : UInt8) (quote : IsQuote q) (body : Bytes) :
    plainString (quoteBytes q body) = strBody (printable q) body := by
  unfold plainString
  rw [quotedBody_complete (quoteBytes_quoted q quote body)]

theorem quote_punct_none (q : UInt8) (quote : IsQuote q) (tail : Bytes) :
    punctExact (q :: tail) = none := by
  rcases quote with rfl | rfl <;>
    rcases tail with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> rfl

theorem solTok_plain_eq (q : UInt8) (quote : IsQuote q) (body : Bytes) :
    solTok (quoteBytes q body) = (strBody (printable q) body).map Tok.str := by
  have e : plainString (quoteBytes q body) = strBody (printable q) body := quoted_plain_eq q quote body
  have word : isWord (quoteBytes q body) = false := by rcases quote with rfl | rfl <;> rfl
  have punct : punctOf solPuncts (quoteBytes q body) = none := by
    simp only [quoteBytes, punctOf, quote_punct_none q quote, Option.filter_none]
  cases decoded : strBody (printable q) body with
  | some out => simp only [solTok, word, Bool.false_eq_true, ite_false, punct, e, decoded, Option.map_some]
  | none =>
    simp only [solTok, word, Bool.false_eq_true, ite_false, punct, e, decoded, Option.map_none]
    rcases quote with rfl | rfl <;> rfl

theorem yulTok_plain_eq (q : UInt8) (quote : IsQuote q) (body : Bytes) :
    yulTok (quoteBytes q body) = (strBody (printable q) body).map Tok.str := by
  have e : plainString (quoteBytes q body) = strBody (printable q) body := quoted_plain_eq q quote body
  have word : isWord (quoteBytes q body) = false := by rcases quote with rfl | rfl <;> rfl
  have notHex : (quoteBytes q body == ascii "hex") = false := by rcases quote with rfl | rfl <;> rfl
  have punct : punctOf yulPuncts (quoteBytes q body) = none := by
    simp only [quoteBytes, punctOf, quote_punct_none q quote, Option.filter_none]
  cases decoded : strBody (printable q) body with
  | some out => simp only [yulTok, notHex, word, Bool.false_eq_true, ite_false, punct, e, decoded, Option.map_some]
  | none =>
    simp only [yulTok, notHex, word, Bool.false_eq_true, ite_false, punct, e, decoded, Option.map_none]
    rcases quote with rfl | rfl <;> rfl

theorem solTok_hex_eq (q : UInt8) (quote : IsQuote q) (body : Bytes) :
    solTok (hexPrefix ++ quoteBytes q body) = (hexBody body).map Tok.hexStr := by
  have e : quotedBody (quoteBytes q body) = some (q, body) :=
    quotedBody_complete (quoteBytes_quoted q quote body)
  rcases quote with rfl | rfl
  · change (match quotedBody (quoteBytes 34 body) with
      | some (_, b) => (hexBody b).map Tok.hexStr | none => none) = _
    rw [e]
  · change (match quotedBody (quoteBytes 39 body) with
      | some (_, b) => (hexBody b).map Tok.hexStr | none => none) = _
    rw [e]

theorem yulTok_hex_eq (q : UInt8) (quote : IsQuote q) (body : Bytes) :
    yulTok (hexPrefix ++ quoteBytes q body) = (hexBody body).map Tok.hexStr := by
  have e : quotedBody (quoteBytes q body) = some (q, body) :=
    quotedBody_complete (quoteBytes_quoted q quote body)
  rcases quote with rfl | rfl
  · change (match quotedBody (quoteBytes 34 body) with
      | some (_, b) => (hexBody b).map Tok.hexStr | none => none) = _
    rw [e]
  · change (match quotedBody (quoteBytes 39 body) with
      | some (_, b) => (hexBody b).map Tok.hexStr | none => none) = _
    rw [e]

theorem solTok_unicode_eq (q : UInt8) (quote : IsQuote q) (body : Bytes) :
    solTok (unicodePrefix ++ quoteBytes q body) =
      if irregularBreak body || !bidiBalanced body then none
      else (strBody (unicodeChar q) body).map Tok.unicodeStr := by
  have e : quotedBody (quoteBytes q body) = some (q, body) :=
    quotedBody_complete (quoteBytes_quoted q quote body)
  rcases quote with rfl | rfl
  · change (match quotedBody (quoteBytes 34 body) with
      | some (q, b) => if irregularBreak b || !bidiBalanced b then none
        else (strBody (unicodeChar q) b).map Tok.unicodeStr
      | none => none) = _
    rw [e]
  · change (match quotedBody (quoteBytes 39 body) with
      | some (q, b) => if irregularBreak b || !bidiBalanced b then none
        else (strBody (unicodeChar q) b).map Tok.unicodeStr
      | none => none) = _
    rw [e]

theorem option_map_same_iff {α β : Type} (f : α → β)
    (injective : ∀ a b, f a = f b → a = b) (value : Option α) (a : α) :
    value.map f = some (f a) ↔ value = some a := by
  constructor
  · intro h
    cases value with
    | none => cases h
    | some b =>
      have e : b = a := injective b a (Option.some.inj h)
      subst b
      rfl
  · intro h
    rw [h]
    rfl

theorem solTok_plain_iff (q : UInt8) (quote : IsQuote q) (body out : Bytes) :
    solTok (quoteBytes q body) = some (.str out) ↔ Body (printable q) body out := by
  rw [solTok_plain_eq q quote body,
    option_map_same_iff Tok.str (by intro a b h; cases h; rfl), body_iff]

theorem solTok_hex_iff (q : UInt8) (quote : IsQuote q) (body out : Bytes) :
    solTok (hexPrefix ++ quoteBytes q body) = some (.hexStr out) ↔ HexBody body out := by
  rw [solTok_hex_eq q quote body,
    option_map_same_iff Tok.hexStr (by intro a b h; cases h; rfl), hexBody_iff]

theorem solTok_unicode_iff (q : UInt8) (quote : IsQuote q) (body out : Bytes) :
    solTok (unicodePrefix ++ quoteBytes q body) = some (.unicodeStr out) ↔
      irregularBreak body = false ∧ bidiBalanced body = true ∧ Body (unicodeChar q) body out := by
  rw [solTok_unicode_eq q quote body]
  constructor
  · intro h
    split at h
    · cases h
    · rename_i good
      have guards : irregularBreak body = false ∧ (!bidiBalanced body) = false :=
        Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr good)
      have balanced : bidiBalanced body = true := by
        cases e : bidiBalanced body with
        | false =>
          have bad : (true : Bool) = false := by simpa only [e, Bool.not_false] using guards.2
          cases bad
        | true => rfl
      have decoded : strBody (unicodeChar q) body = some out :=
        (option_map_same_iff Tok.unicodeStr (by intro a b h; cases h; rfl) _ _).mp h
      exact ⟨guards.1, balanced, body_sound _ _ _ decoded⟩
  · intro ⟨line, bidi, value⟩
    rw [line, bidi]
    change (strBody (unicodeChar q) body).map Tok.unicodeStr = some (.unicodeStr out)
    rw [body_complete value]
    rfl

theorem Plain.solTok {raw out : Bytes} (h : Plain raw out) : solTok raw = some (.str out) := by
  obtain ⟨q, body, ⟨quote, rfl⟩, value⟩ := h
  exact (solTok_plain_iff q quote body out).mpr value

theorem HexLiteral.solTok {raw out : Bytes} (h : HexLiteral raw out) :
    solTok raw = some (.hexStr out) := by
  obtain ⟨q, body, quote, rfl, value⟩ := h
  exact (solTok_hex_iff q quote body out).mpr value

theorem UnicodeLiteral.solTok {raw out : Bytes} (h : UnicodeLiteral raw out) :
    solTok raw = some (.unicodeStr out) := by
  obtain ⟨q, body, quote, rfl, line, bidi, value⟩ := h
  exact (solTok_unicode_iff q quote body out).mpr ⟨line, bidi, value⟩

theorem quote_trivia_none (q : UInt8) (quote : IsQuote q) (tail : Bytes) :
    trivia (q :: tail) = none := by
  rcases quote with rfl | rfl <;> cases tail <;> rfl

theorem classify_sol_plain (q : UInt8) (quote : IsQuote q) (body : Bytes) :
    classify .sol (quoteBytes q body) =
      (strBody (printable q) body).map (fun b => Kind.tok (.str b)) := by
  have noTrivia : trivia (quoteBytes q body) = none := quote_trivia_none q quote _
  simp only [classify, noTrivia, solTok_plain_eq q quote body, Option.map_map, Function.comp_def]

theorem classify_yul_plain (depth : Nat) (q : UInt8) (quote : IsQuote q) (body : Bytes) :
    classify (.yul depth) (quoteBytes q body) =
      (strBody (printable q) body).map (fun b => Kind.tok (.str b)) := by
  have noTrivia : trivia (quoteBytes q body) = none := quote_trivia_none q quote _
  simp only [classify, noTrivia, yulTok_plain_eq q quote body, Option.map_map, Function.comp_def]

theorem classify_sol_hex (q : UInt8) (quote : IsQuote q) (body : Bytes) :
    classify .sol (hexPrefix ++ quoteBytes q body) =
      (hexBody body).map (fun b => Kind.tok (.hexStr b)) := by
  have noTrivia : trivia (hexPrefix ++ quoteBytes q body) = none := rfl
  simp only [classify, noTrivia, solTok_hex_eq q quote body, Option.map_map, Function.comp_def]

theorem classify_yul_hex (depth : Nat) (q : UInt8) (quote : IsQuote q) (body : Bytes) :
    classify (.yul depth) (hexPrefix ++ quoteBytes q body) =
      (hexBody body).map (fun b => Kind.tok (.hexStr b)) := by
  have noTrivia : trivia (hexPrefix ++ quoteBytes q body) = none := rfl
  simp only [classify, noTrivia, yulTok_hex_eq q quote body, Option.map_map, Function.comp_def]

theorem classify_sol_unicode (q : UInt8) (quote : IsQuote q) (body : Bytes) :
    classify .sol (unicodePrefix ++ quoteBytes q body) =
      if irregularBreak body || !bidiBalanced body then none
      else (strBody (unicodeChar q) body).map (fun b => Kind.tok (.unicodeStr b)) := by
  have noTrivia : trivia (unicodePrefix ++ quoteBytes q body) = none := rfl
  simp only [classify, noTrivia, solTok_unicode_eq q quote body]
  split
  · rfl
  · simp only [Option.map_map, Function.comp_def]

theorem classify_yul_unicode_refused (depth : Nat) (q : UInt8) (quote : IsQuote q) (body : Bytes) :
    classify (.yul depth) (unicodePrefix ++ quoteBytes q body) = none := by
  rcases quote with rfl | rfl <;> rfl

theorem classify_asm_double (body : Bytes) :
    classify .asm (quoteBytes 34 body) =
      if (quoteBytes 34 body).length > 2 then
        (strBody (printable 34) body).map (fun b => Kind.tok (.str b)) else none := by
  have noTrivia : trivia (quoteBytes 34 body) = none := quote_trivia_none 34 (Or.inl rfl) _
  have noPunct : punctOf asmPuncts (quoteBytes 34 body) = none := by
    simp only [quoteBytes, punctOf, quote_punct_none 34 (Or.inl rfl), Option.filter_none]
  simp only [classify, noTrivia, noPunct]
  have head : (quoteBytes 34 body).head? = some 34 := rfl
  by_cases large : (quoteBytes 34 body).length > 2 <;>
    simp only [head, BEq.rfl, Bool.true_and, decide_eq_true_eq, large, ite_true, ite_false,
      quoted_plain_eq 34 (Or.inl rfl) body, Option.map_map, Function.comp_def, Option.map_none]

theorem classify_asm_single_refused (body : Bytes) :
    classify .asm (quoteBytes 39 body) = none := by
  have noTrivia : trivia (quoteBytes 39 body) = none := quote_trivia_none 39 (Or.inr rfl) _
  have noPunct : punctOf asmPuncts (quoteBytes 39 body) = none := by
    simp only [quoteBytes, punctOf, quote_punct_none 39 (Or.inr rfl), Option.filter_none]
  simp only [classify, noTrivia, noPunct]
  rfl

end Solidity.Frontend.LiteralGrammarH28

