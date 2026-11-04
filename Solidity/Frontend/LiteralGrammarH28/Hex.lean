import Solidity.Frontend.Checked.Lexer

/-!
# Hexadecimal string body grammar

Pairs are adjacent or separated by one underscore. An underscore must have
another pair after it. `HexBody` is independent of the decoder: its premises
are byte classes, a boundary condition and recursive grammar evidence.
No numeric-literal or EIP55 declarations are changed.
-/

namespace Solidity.Frontend.LiteralGrammarH28

open Solidity.Source Solidity.Frontend.Checked

/-- The byte value of one hexadecimal pair. -/
def pairValue (a b : UInt8) : UInt8 := (hexVal a * 16 + hexVal b).toUInt8

/-- Even hex digits, optionally separated by single underscores between pairs.
The adjacent arm excludes an underscore at the beginning of the remaining
body; the separator arm requires a following nonempty body. -/
inductive HexBody : Bytes → Bytes → Prop where
  | nil : HexBody [] []
  | pair {a b : UInt8} {raw out : Bytes} :
      isHexDigit a = true → isHexDigit b = true →
      raw.head? ≠ some 95 → HexBody raw out →
      HexBody (a :: b :: raw) (pairValue a b :: out)
  | sep {a b : UInt8} {raw out : Bytes} :
      isHexDigit a = true → isHexDigit b = true →
      raw ≠ [] → HexBody raw out →
      HexBody (a :: b :: 95 :: raw) (pairValue a b :: out)

/-- Every grammar derivation decodes to exactly its byte value. -/
theorem hexBody_complete {raw out : Bytes} (h : HexBody raw out) :
    hexBody raw = some out := by
  induction h with
  | nil => rfl
  | @pair a b raw out ha hb boundary h ih =>
    cases raw with
    | nil =>
      have e : out = [] := by simpa only [hexBody, Option.some.injEq] using ih.symm
      subst out
      simp only [hexBody, ha, hb, Bool.and_self, ite_true, Option.map_some, pairValue]
    | cons c tail =>
      have hc : c ≠ 95 := by simpa only [List.head?_cons, ne_eq, Option.some.injEq] using boundary
      simp only [List.cons.injEq, hc, false_and, imp_self, implies_true, hexBody, ha, hb, Bool.and_self, ite_true, ih, Option.map_some, pairValue]
  | @sep a b raw out ha hb nonempty h ih =>
    cases raw with
    | nil => exact False.elim (nonempty rfl)
    | cons c tail => simp only [hexBody, ha, hb, List.isEmpty_cons, Bool.not_false, Bool.and_self, ite_true, ih, Option.map_some, pairValue]

/-- No accepted body is hidden by the grammar boundary conditions. -/
theorem hexBody_sound (raw : Bytes) :
    ∀ out, hexBody raw = some out → HexBody raw out := by
  fun_induction hexBody raw <;> intro out h
  case case1 => cases h; exact .nil
  case case2 a b t digits ih =>
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Bool.and_eq_true] at digits
    have nonempty : t ≠ [] := by
      intro ht
      subst t
      simpa only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true] using digits.2
    exact .sep digits.1.1 digits.1.2 nonempty (ih v hv)
  case case4 a b t boundary digits ih =>
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Bool.and_eq_true] at digits
    apply HexBody.pair digits.1 digits.2
    · cases t with
      | nil => intro e; cases e
      | cons c tail =>
        intro e
        have hc : c = 95 := Option.some.inj e
        subst c
        exact boundary tail rfl
    · exact ih v hv
  all_goals cases h

/-- Exact acceptance and exact value, in both directions. -/
theorem hexBody_iff (raw out : Bytes) :
    hexBody raw = some out ↔ HexBody raw out :=
  ⟨hexBody_sound raw out, hexBody_complete⟩

/-- Grammar values are unique. -/
theorem HexBody.deterministic {raw x y : Bytes}
    (hx : HexBody raw x) (hy : HexBody raw y) : x = y :=
  Option.some.inj ((hexBody_complete hx).symm.trans (hexBody_complete hy))

/-- Refusal means absence of every grammar value. -/
theorem hexBody_none_iff (raw : Bytes) :
    hexBody raw = none ↔ ∀ out, ¬ HexBody raw out := by
  constructor
  · intro hn out h
    have e : hexBody raw = some out := hexBody_complete h
    rw [hn] at e
    cases e
  · intro h
    cases e : hexBody raw with
    | none => rfl
    | some out => exact False.elim (h out (hexBody_sound raw out e))

/-- Each output byte consumes two digits and at most one separator. -/
theorem HexBody.length_bounds {raw out : Bytes} (h : HexBody raw out) :
    2 * out.length ≤ raw.length ∧ raw.length ≤ 3 * out.length := by
  induction h with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | pair _ _ _ _ ih => simp only [List.length_cons]; omega
  | sep _ _ _ _ ih => simp only [List.length_cons]; omega

end Solidity.Frontend.LiteralGrammarH28
