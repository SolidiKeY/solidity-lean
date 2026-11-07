import Solidity.Frontend.LiteralGrammarH28.WordTable

/-! # Unrestricted literal classification inversion

Raw inputs are unrestricted. Priority branches yielding words, punctuation or
numbers cannot masquerade as a nonnumeric literal token. Numeric values and
EIP55 semantics are not modified or strengthened.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive Flavor where
  | plain | hex | unicode

def Flavor.tag : Flavor → Bytes → Tok
  | .plain => Tok.str
  | .hex => Tok.hexStr
  | .unicode => Tok.unicodeStr

def Flavor.Rel : Flavor → Bytes → Bytes → Prop
  | .plain => Plain
  | .hex => HexLiteral
  | .unicode => UnicodeLiteral

theorem solWordTable_no_literal (flavor : Flavor) (raw out : Bytes) :
    solWordTable raw ≠ .tok (flavor.tag out) := by
  intro e
  have h : wordNonliteral (solWordTable raw) = true := solWordTable_nonliteral raw
  rw [e] at h
  cases flavor <;> cases h

theorem solWord_no_literal (flavor : Flavor) (raw out : Bytes) :
    solWord raw ≠ some (flavor.tag out) := by
  fun_cases solWord raw
  case case1 t table =>
    intro h
    cases h
    exact solWordTable_no_literal flavor raw out table
  all_goals cases flavor <;> intro h <;> cases h

theorem solTok_literal_sound (flavor : Flavor) (raw out : Bytes) :
    solTok raw = some (flavor.tag out) → flavor.Rel raw out := by
  fun_cases solTok raw
  case case1 => intro h; exact False.elim (solWord_no_literal flavor raw out h)
  case case3 =>
    intro h
    cases flavor <;> cases h
    apply plainString_sound
    assumption
  case case4 r q body quoted _ _ _ =>
    intro h
    obtain ⟨v, decoded, eq⟩ := Option.map_eq_some_iff.mp h
    cases flavor <;> cases eq
    obtain ⟨quote, rfl⟩ := quotedBody_sound r q body quoted
    exact ⟨q, body, quote, rfl, hexBody_sound body out decoded⟩
  case case7 r q body quoted good _ _ _ =>
    intro h
    cases flavor with
    | plain => obtain ⟨v, _, eq⟩ := Option.map_eq_some_iff.mp h; cases eq
    | hex => obtain ⟨v, _, eq⟩ := Option.map_eq_some_iff.mp h; cases eq
    | unicode =>
      obtain ⟨quote, rfl⟩ := quotedBody_sound r q body quoted
      have original : solTok (unicodePrefix ++ quoteBytes q body) = some (.unicodeStr out) := by
        rw [solTok_unicode_eq q quote body, if_neg good]
        exact h
      exact ⟨q, body, quote, rfl, (solTok_unicode_iff q quote body out).mp original⟩
  case case9 =>
    intro h
    split at h
    · cases flavor <;> cases h
    · obtain ⟨v, _, eq⟩ := Option.map_eq_some_iff.mp h
      cases flavor <;> cases eq
  case case10 =>
    intro h
    split at h
    · cases flavor <;> cases h
    · obtain ⟨v, _, eq⟩ := Option.map_eq_some_iff.mp h
      cases flavor <;> cases eq
  all_goals cases flavor <;> intro h <;> cases h

theorem solTok_literal_iff (flavor : Flavor) (raw out : Bytes) :
    solTok raw = some (flavor.tag out) ↔ flavor.Rel raw out := by
  constructor
  · exact solTok_literal_sound flavor raw out
  · intro h
    cases flavor with
    | plain => exact Plain.solTok h
    | hex => exact HexLiteral.solTok h
    | unicode => exact UnicodeLiteral.solTok h

theorem yulWordTable_no_literal (flavor : Flavor) (raw out : Bytes) :
    yulWordTable raw ≠ some (flavor.tag out) := by
  fun_cases yulWordTable raw <;> cases flavor <;> intro h <;> cases h

theorem yulWord_no_literal (flavor : Flavor) (raw out : Bytes) :
    yulWord raw ≠ flavor.tag out := by
  fun_cases yulWord raw
  case case1 t table =>
    intro h
    cases h
    exact yulWordTable_no_literal flavor raw out table
  all_goals cases flavor <;> intro h <;> cases h

theorem yulNumber_no_literal (flavor : Flavor) (raw out : Bytes) :
    yulNumber raw ≠ some (flavor.tag out) := by
  fun_cases yulNumber raw <;> cases flavor <;> intro h <;> try cases h
  all_goals obtain ⟨v, _, eq⟩ := Option.map_eq_some_iff.mp h; cases eq

theorem yulTok_literal_sound (flavor : Flavor) (raw out : Bytes) :
    yulTok raw = some (flavor.tag out) → flavor.Rel raw out := by
  fun_cases yulTok raw
  case case2 =>
    intro h
    exact False.elim (yulWord_no_literal flavor raw out (Option.some.inj h))
  case case4 =>
    intro h
    cases flavor <;> cases h
    apply plainString_sound
    assumption
  case case5 r q body quoted _ _ _ _ =>
    intro h
    obtain ⟨v, decoded, eq⟩ := Option.map_eq_some_iff.mp h
    cases flavor <;> cases eq
    obtain ⟨quote, rfl⟩ := quotedBody_sound r q body quoted
    exact ⟨q, body, quote, rfl, hexBody_sound body out decoded⟩
  case case7 => intro h; exact False.elim (yulNumber_no_literal flavor raw out h)
  all_goals cases flavor <;> intro h <;> cases h

theorem Plain.yulTok {raw out : Bytes} (h : Plain raw out) : yulTok raw = some (.str out) := by
  obtain ⟨q, body, ⟨quote, rfl⟩, value⟩ := h
  change Checked.yulTok (quoteBytes q body) = some (.str out)
  rw [yulTok_plain_eq q quote body, body_complete value]
  rfl

theorem HexLiteral.yulTok {raw out : Bytes} (h : HexLiteral raw out) : yulTok raw = some (.hexStr out) := by
  obtain ⟨q, body, quote, rfl, value⟩ := h
  rw [yulTok_hex_eq q quote body, hexBody_complete value]
  rfl

theorem yulTok_plain_iff (raw out : Bytes) : yulTok raw = some (.str out) ↔ Plain raw out :=
  ⟨yulTok_literal_sound .plain raw out, Plain.yulTok⟩

theorem yulTok_hex_iff (raw out : Bytes) : yulTok raw = some (.hexStr out) ↔ HexLiteral raw out :=
  ⟨yulTok_literal_sound .hex raw out, HexLiteral.yulTok⟩

theorem yulTok_unicode_impossible (raw out : Bytes) : yulTok raw ≠ some (.unicodeStr out) := by
  fun_cases yulTok raw
  case case2 => intro h; exact yulWord_no_literal .unicode raw out (Option.some.inj h)
  case case5 => intro h; obtain ⟨v, _, eq⟩ := Option.map_eq_some_iff.mp h; cases eq
  case case7 => exact yulNumber_no_literal .unicode raw out
  all_goals intro h; cases h

theorem Flavor.Rel.noTrivia {flavor : Flavor} {raw out : Bytes} (h : flavor.Rel raw out) :
    trivia raw = none := by
  cases flavor with
  | plain =>
    obtain ⟨q, body, ⟨quote, rfl⟩, _⟩ := h
    exact quote_trivia_none q quote _
  | hex => obtain ⟨q, body, quote, rfl, _⟩ := h; rfl
  | unicode => obtain ⟨q, body, quote, rfl, _⟩ := h; rfl

theorem classify_sol_literal_iff (flavor : Flavor) (raw out : Bytes) :
    classify .sol raw = some (.tok (flavor.tag out)) ↔ flavor.Rel raw out := by
  constructor
  · intro h
    unfold classify at h
    cases t : trivia raw with
    | some tr => rw [t] at h; cases h
    | none =>
      rw [t] at h
      obtain ⟨tok, classified, eq⟩ := Option.map_eq_some_iff.mp h
      cases eq
      exact (solTok_literal_iff flavor raw out).mp classified
  · intro h
    simp only [classify, h.noTrivia, (solTok_literal_iff flavor raw out).mpr h, Option.map_some]

theorem classify_yul_literal_sound (depth : Nat) (flavor : Flavor) (raw out : Bytes)
    (h : classify (.yul depth) raw = some (.tok (flavor.tag out))) : flavor.Rel raw out := by
  unfold classify at h
  cases t : trivia raw with
  | some tr => rw [t] at h; cases h
  | none =>
    rw [t] at h
    obtain ⟨tok, classified, eq⟩ := Option.map_eq_some_iff.mp h
    cases eq
    exact yulTok_literal_sound flavor raw out classified

theorem classify_yul_plain_iff (depth : Nat) (raw out : Bytes) :
    classify (.yul depth) raw = some (.tok (.str out)) ↔ Plain raw out := by
  constructor
  · exact classify_yul_literal_sound depth .plain raw out
  · intro h
    simp only [classify, Flavor.Rel.noTrivia (flavor := .plain) h, h.yulTok, Option.map_some]

theorem classify_yul_hex_iff (depth : Nat) (raw out : Bytes) :
    classify (.yul depth) raw = some (.tok (.hexStr out)) ↔ HexLiteral raw out := by
  constructor
  · exact classify_yul_literal_sound depth .hex raw out
  · intro h
    simp only [classify, Flavor.Rel.noTrivia (flavor := .hex) h, h.yulTok, Option.map_some]

theorem classify_yul_unicode_impossible (depth : Nat) (raw out : Bytes) :
    classify (.yul depth) raw ≠ some (.tok (.unicodeStr out)) := by
  intro h
  unfold classify at h
  cases t : trivia raw with
  | some tr => rw [t] at h; cases h
  | none =>
    rw [t] at h
    obtain ⟨tok, classified, eq⟩ := Option.map_eq_some_iff.mp h
    cases eq
    exact yulTok_unicode_impossible raw out classified

/-- Absence of a flavor is not total classifier refusal: other token kinds remain possible. -/
theorem solTok_no_flavor_iff (flavor : Flavor) (raw : Bytes) :
    (∀ out, solTok raw ≠ some (flavor.tag out)) ↔ ∀ out, ¬ flavor.Rel raw out := by
  constructor
  · intro h out value
    exact h out ((solTok_literal_iff flavor raw out).mpr value)
  · intro h out value
    exact h out ((solTok_literal_iff flavor raw out).mp value)

/-- Assembly strings require a double-quoted, nonempty source spelling, not a nonempty value. -/
def AssemblyLiteral (raw out : Bytes) : Prop :=
  Plain raw out ∧ raw.head? = some 34 ∧ raw.length > 2

theorem classify_asm_plain_iff (raw out : Bytes) :
    classify .asm raw = some (.tok (.str out)) ↔ AssemblyLiteral raw out := by
  constructor
  · intro h
    unfold classify at h
    cases tr : trivia raw with
    | some t => rw [tr] at h; cases h
    | none =>
      rw [tr] at h
      dsimp only at h
      cases pu : punctOf asmPuncts raw with
      | some p => rw [pu] at h; cases h
      | none =>
        rw [pu] at h
        dsimp only at h
        split at h
        · rename_i guard
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at guard
          obtain ⟨tok, hp, eq⟩ := Option.map_eq_some_iff.mp h
          cases eq
          obtain ⟨value, hv, eq⟩ := Option.map_eq_some_iff.mp hp
          cases eq
          exact ⟨plainString_sound raw out hv, guard.1, guard.2⟩
        · cases h
  · intro ⟨value, head, large⟩
    have noTrivia : trivia raw = none := Flavor.Rel.noTrivia (flavor := .plain) value
    have noPunct : punctOf asmPuncts raw = none := by
      obtain ⟨q, body, ⟨quote, eq⟩, _⟩ := value
      rw [eq]
      simp only [punctOf, quote_punct_none q quote, Option.filter_none]
    simp only [classify, noTrivia, noPunct, head, BEq.rfl, Bool.true_and,
      decide_eq_true_eq, if_pos large, plainString_complete value, Option.map_some]

theorem classify_asm_nonplain_impossible (flavor : Flavor) (notPlain : flavor ≠ .plain)
    (raw out : Bytes) : classify .asm raw ≠ some (.tok (flavor.tag out)) := by
  intro h
  unfold classify at h
  cases tr : trivia raw with
  | some t => rw [tr] at h; cases h
  | none =>
    rw [tr] at h
    dsimp only at h
    cases pu : punctOf asmPuncts raw with
    | some p => rw [pu] at h; cases flavor <;> cases h
    | none =>
      rw [pu] at h
      dsimp only at h
      split at h
      · obtain ⟨tok, hp, eq⟩ := Option.map_eq_some_iff.mp h
        cases eq
        obtain ⟨value, _, eq⟩ := Option.map_eq_some_iff.mp hp
        cases flavor <;> cases eq
        exact notPlain rfl
      · cases h

theorem classify_pragma_literal_impossible (flavor : Flavor) (raw out : Bytes) :
    classify .pragma raw ≠ some (.tok (flavor.tag out)) := by
  intro h
  unfold classify at h
  cases tr : trivia raw with
  | some t => rw [tr] at h; cases h
  | none =>
    rw [tr] at h
    dsimp only at h
    split at h
    · cases flavor <;> cases h
    · split at h <;> cases flavor <;> cases h

end Solidity.Frontend.LiteralGrammarH28



