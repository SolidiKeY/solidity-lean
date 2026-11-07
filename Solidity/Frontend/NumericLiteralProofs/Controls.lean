import Solidity.Frontend.NumericLiteralProofs.Backfill
import Solidity.Frontend.NumericLiteralProofs.Underscores

/-! # Inhabited constructor witnesses and kernel-evaluated scanner-arm controls -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem control_tail_nil : Tail [] [] [] := .nil
theorem control_tail_digit : Tail [49] [49] [] := .digit (by decide) .nil
theorem control_tail_separated : Tail [95, 49] [49] [] :=
  .separated (by decide) (by decide) (by decide) .nil
theorem control_tail_other : Tail [65] [] [65] := .other (by decide) (by decide)
theorem control_tail_final : Tail [95] [] [95] := .finalUnderscore (by decide) (by decide)
theorem control_tail_bad : Tail [95, 95] [] [95, 95] :=
  .badUnderscore (by decide) (by decide) (by decide)
theorem control_digits : Digits [49] [49] [] := .first (by decide) .nil
theorem control_nodigits_nil : NoDigits [] := .nil
theorem control_nodigits_other : NoDigits [65] := .other (by decide)
theorem control_integer_absent : IntegerPart [] [] [] := .absent .nil
theorem control_integer_present : IntegerPart [49] [49] [] := .present control_digits
theorem control_fraction_nil : FractionPart [] [] [] := .nil
theorem control_fraction_absent : FractionPart [101] [] [101] := .absent (by decide)
theorem control_fraction_present : FractionPart [46, 49] [49] [] := .present control_digits
theorem control_exponent_absent : Exponent [] 0 := .absent
theorem control_exponent_unsigned : Exponent [101, 49] 1 :=
  .unsigned (Or.inl rfl) control_digits
theorem control_exponent_negative : Exponent [69, 45, 49] (-1) :=
  .negative (Or.inr rfl) control_digits
theorem control_decimal : Decimal [49] (.dec 1 0 0) :=
  .mk control_integer_present .nil (Or.inl (by decide)) (by decide) .absent
theorem control_hex_single : HexDigits [49] [49] := .single (by decide)
theorem control_hex_adjacent : HexDigits [49, 50] [49, 50] :=
  .adjacent (by decide) (.single (by decide))
theorem control_hex_separated : HexDigits [49, 95, 50] [49, 50] :=
  .separated (by decide) (.single (by decide))
theorem control_hexadecimal : Hexadecimal [48, 120, 49] (.hex [⟨1, by decide⟩] false) :=
  .mk control_hex_single

/-- Generated course-of-values constructors are inventoried and inhabited too. -/
theorem control_tail_below_nil :
    Tail.below (motive := fun _ _ _ _ => True) control_tail_nil := .nil

theorem control_tail_below_digit :
    Tail.below (motive := fun _ _ _ _ => True) control_tail_digit :=
  .digit (by decide) control_tail_nil control_tail_below_nil True.intro

theorem control_tail_below_separated :
    Tail.below (motive := fun _ _ _ _ => True) control_tail_separated :=
  .separated (by decide) (by decide) (by decide) control_tail_nil control_tail_below_nil True.intro

theorem control_tail_below_other :
    Tail.below (motive := fun _ _ _ _ => True) control_tail_other :=
  .other (by decide) (by decide)

theorem control_tail_below_final :
    Tail.below (motive := fun _ _ _ _ => True) control_tail_final :=
  .finalUnderscore (by decide) (by decide)

theorem control_tail_below_bad :
    Tail.below (motive := fun _ _ _ _ => True) control_tail_bad :=
  .badUnderscore (by decide) (by decide) (by decide)

theorem control_hex_below_single :
    HexDigits.below (motive := fun _ _ _ => True) control_hex_single := .single (by decide)

theorem control_hex_below_adjacent :
    HexDigits.below (motive := fun _ _ _ => True) control_hex_adjacent :=
  .adjacent (b := 49) (raw := [50]) (ds := [50]) (by decide)
    (.single (by decide)) (.single (by decide)) True.intro

theorem control_hex_below_separated :
    HexDigits.below (motive := fun _ _ _ => True) control_hex_separated :=
  .separated (b := 49) (raw := [50]) (ds := [50]) (by decide)
    (.single (by decide)) (.single (by decide)) True.intro

/-- One named row per scanner arm or boundary, including negative inputs.
The acceptance checker pins these IDs separately from constructor witnesses. -/
def scannerControls : List (String × Bool) := [
  ("tail.nil", decide (digitsTail [] = ([], []))),
  ("tail.digit", decide (digitsTail [49] = ([49], []))),
  ("tail.separated", decide (digitsTail [95,49] = ([49], []))),
  ("tail.other", decide (digitsTail [65,49] = ([], [65,49]))),
  ("tail.final", decide (digitsTail [95] = ([], [95]))),
  ("tail.bad", decide (digitsTail [95,95,49] = ([], [95,95,49]))),
  ("digits.empty", decide (digits1 [] = none)),
  ("digits.nondigit", decide (digits1 [95,49] = none)),
  ("decimal.empty", decide (decNumber [] = none)),
  ("decimal.integer", decide (decNumber (ascii "12") = some (.dec 12 0 0))),
  ("decimal.leading-dot", decide (decNumber (ascii ".12") = some (.dec 12 2 0))),
  ("decimal.fraction", decide (decNumber (ascii "12.34") = some (.dec 1234 2 0))),
  ("decimal.missing-fraction", decide (decNumber (ascii "12.") = none)),
  ("decimal.octal", decide (decNumber (ascii "01") = none)),
  ("decimal.underscore-octal", decide (decNumber (ascii "0_1") = none)),
  ("decimal.unsigned-exponent", decide (decNumber (ascii "1e02") = some (.dec 1 0 2))),
  ("decimal.negative-exponent", decide (decNumber (ascii "1E-02") = some (.dec 1 0 (-2)))),
  ("decimal.plus-exponent", decide (decNumber (ascii "1e+2") = none)),
  ("decimal.empty-exponent", decide (decNumber (ascii "1e") = none)),
  ("decimal.empty-negative-exponent", decide (decNumber (ascii "1e-") = none)),
  ("decimal.exponent-leftover", decide (decNumber (ascii "1e2x") = none)),
  ("decimal.other-leftover", decide (decNumber (ascii "1x") = none)),
  ("decimal.all-underscores", decide (decNumber (ascii "1_2.3_4E-5_6") = some (.dec 1234 2 (-56)))),
  ("decimal.fraction-bad-underscore", decide (decNumber (ascii "1._2") = none)),
  ("decimal.exponent-bad-underscore", decide (decNumber (ascii "1e_2") = none)),
  ("decimal.trailing-underscore", decide (decNumber (ascii "1.2e3_") = none)),
  ("hex.empty", decide (hexDigits [] = none)),
  ("hex.single", decide (hexDigits [65] = some [65])),
  ("hex.adjacent", decide (hexDigits [65,98] = some [65,98])),
  ("hex.separated", decide (hexDigits [65,95,98] = some [65,98])),
  ("hex.leading-underscore", decide (hexDigits [95,65] = none)),
  ("hex.trailing-underscore", decide (hexDigits [65,95] = none)),
  ("hex.doubled-underscore", decide (hexDigits [65,95,95,98] = none)),
  ("hex.invalid", decide (hexDigits [71] = none)),
  ("hex.invalid-separated-head", decide (hexDigits [71,95,65] = none)),
  ("hex.invalid-cons-head", decide (hexDigits [71,65] = none)),
  ("hex.invalid-tail", decide (hexDigits [65,71] = none)),
  ("hex.empty-prefix", decide (hexNumber (ascii "0x") = none)),
  ("hex.upper-prefix", decide (hexNumber (ascii "0X1") = none)),
  ("hex.value", decide (hexNumber (ascii "0xA_b") = some (.hex [⟨10,by decide⟩,⟨11,by decide⟩] false))),
  ("source.glued-unit", !(lex (ascii "1wei")).toOption.isSome),
  ("source.separated-unit", (lex (ascii "1 wei")).toOption.isSome),
  ("source.comment-unit", (lex (ascii "1/*x*/wei")).toOption.isSome),
  ("source.glued-elementary", !(lex (ascii "1uint8")).toOption.isSome),
  ("source.separate-period", (lex (ascii "1.")).toOption.isSome),
  ("source.leading-underscore-word", (lex (ascii "_1")).toOption.isSome),
  ("source.empty-hex", !(lex (ascii "0x")).toOption.isSome),
  ("source.missing-exponent", !(lex (ascii "1e")).toOption.isSome),
  ("yul.decimal", decide (yulNumber (ascii "12") = some (.yulDec 12))),
  ("yul.hex", decide (yulNumber (ascii "0xAb") = some (.yulHex 171))),
  ("yul.no-underscores", decide (yulNumber (ascii "1_2") = none)),
  ("yul.no-fraction", decide (yulNumber (ascii ".1") = none)),
  ("yul.no-exponent", decide (yulNumber (ascii "1e2") = none)),
  ("yul.hex-no-underscores", decide (yulNumber (ascii "0xA_b") = none)),
  ("yul.leading-zero", decide (yulNumber (ascii "01") = none)),
  ("yul.empty-hex", decide (yulNumber (ascii "0x") = none)),
  ("span.empty", decide (numberSpan false [] = ([],[]))),
  ("span.hex", decide (numberSpan false (ascii "0xA_bG") = (ascii "0xA_b",ascii "G"))),
  ("span.fraction-exponent", decide (numberSpan false (ascii "1.2e-3tail") = (ascii "1.2e-3",ascii "tail"))),
  ("span.period-leftover", decide (numberSpan false (ascii "1.") = (ascii "1",ascii "."))),
  ("span.plus-leftover", decide (numberSpan false (ascii "1e+2") = (ascii "1",ascii "e+2"))),
  ("span.bad-negative-exponent", decide (numberSpan false (ascii "1e-x") = (ascii "1",ascii "e-x"))),
  ("span.bad-exponent-marker", decide (numberSpan false (ascii "1a-2") = (ascii "1",ascii "a-2"))),
  ("span.bad-unsigned-marker", decide (numberSpan false (ascii "1a2") = (ascii "1",ascii "a2"))),
  ("span.yul-integer", decide (numberSpan true (ascii "1_2") = (ascii "1",ascii "_2"))),
  ("span.yul-hex", decide (numberSpan true (ascii "0xA_b") = (ascii "0xA",ascii "_b"))),
  ("span.malformed-underscores", decide (numberSpan false (ascii "12__3") = (ascii "12__3",[]))),
  ("range.exact", decide (((tokens (ascii "1 wei")).toOption.map (·.map fun x => (x.start,x.stop))) = some [(0,1),(2,5)]))
]

theorem scanner_controls_pass : scannerControls.all (·.2) = true := by decide +kernel

theorem checksum_controls :
    eip55 (ascii "5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed") = true ∧
    eip55 (ascii "5aaeb6053F3E94C9b9A09f33669435E7Ef1BeAed") = false := by decide +kernel

theorem checksum_length_controls :
    eip55 (ascii "000000000000000000000000000000000000000") = false ∧
    eip55 (ascii "0000000000000000000000000000000000000000") = true ∧
    eip55 (ascii "00000000000000000000000000000000000000000") = false := by decide +kernel

end Solidity.Frontend.NumericLiteralProofs
