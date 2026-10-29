import Solidity.Language.FixedPoint.Literals

/-!
# Fixed-point conformance with the pinned upstream tests

Kernel-checked verdicts of the decided rules on the fixed-point uses in
the pinned upstream syntax tests (`tests/upstream/solidity-0.8.38.tar.gz`,
under `test/libsolidity/syntaxTests/`).  Each `example` names its test
file; `docs/feature-work/fixed-point-semantics.md`, §6.5, classifies every
use (including those decided by the parser, the scanner or the exclusions,
which no function here computes) and records each deviation from solc's
type checker as intended, with the decision it follows.

solc's verdict is the test's expectation: a test whose only error is
`UnimplementedFeatureError 1834` passes solc's type checker.
-/

namespace Solidity.Language.FixedPoint.Conformance

open Fx

/-- A type's signedness, width and digits. -/
def sig (o : Option FxTy) : Option (Bool × Nat × Nat) := o.map fun t => (t.signed, t.bits, t.digits)

/-- The type `fixedMxN` / `ufixedMxN` (in the scanner's bounds). -/
def ty (signed : Bool) (m n : Nat) (h : (FxTy.mk? signed m n).isSome = true) : FxTy :=
  (FxTy.mk? signed m n).get h

/-- `ofRat?` succeeds: the constant converts implicitly. -/
def implicitOK (t : FxTy) (q : Rat) : Bool := (ofRat? t q).isSome

/-- `explicitRat?` succeeds: the explicit conversion of the constant
compiles. -/
def explicitOK (t : FxTy) (q : Rat) : Bool := (explicitRat? t q).isSome

/-! ### Accepted by solc's type checker and by the decided rules -/

/-- `constants/mod_div_rational.sol`: `0.1 % ∓0.4271087646484375 = 0.1` and
`0 / ±0.123 = 0`, all exact at `fixed`. -/
example : (CExpr.eval (.mod (.lit 0.1) (.lit (-0.4271087646484375)))).map (implicitOK .fixed) =
      some true ∧
    (CExpr.eval (.mod (.lit 0.1) (.lit 0.4271087646484375))) = some 0.1 ∧
    (CExpr.eval (.div (.lit 0) (.lit 0.123))) = some 0 ∧
    (CExpr.eval (.div (.lit 0) (.lit (-0.123)))) = some 0 := by
  decide +kernel

/-- `denominations/fixed_point_division.sol`: `ufixed(4 ether / 3 hours)`
compiles, and solc's suggested type for `10^16 / 27` is its mobile type
`ufixed256x62`. -/
example : explicitOK .ufixed (mkRat (4 * 10 ^ 18) (3 * 3600)) = true ∧
    sig (mobileFx? (mkRat (10 ^ 16) 27)) = some (false, 256, 62) := by
  decide +kernel

/-- `inlineArrays/inline_array_fixed_types.sol` and
`inline_array_rationals.sol`. -/
example : explicitOK .fixed 3.5 = true ∧ explicitOK .fixed (-4.25) = true ∧
    explicitOK .fixed 967.125 = true ∧
    explicitOK (ty false 128 3 (by decide)) 3.5 = true ∧
    implicitOK (ty false 128 3 (by decide)) 4.125 = true ∧
    implicitOK (ty false 128 3 (by decide)) 2.5 = true ∧
    implicitOK (ty false 128 3 (by decide)) 4.0 = true := by
  decide +kernel

/-- `nameAndTypeResolution/303_fixed_type_int_conversion.sol` (and `343`,
`smtCheckerTests/operators/fixed_point_add.sol`, `file_level/free_function_4.sol`):
`int64 → fixed` and `uint64 → ufixed` are implicit. -/
example : FxTy.fixed.intImplicit (-2 ^ 63) (2 ^ 63 - 1) = true ∧
    FxTy.ufixed.intImplicit 0 (2 ^ 64 - 1) = true := by
  decide +kernel

/-- `304`, `305`, `307`, `314`, `324`, `lexer_numbers_with_underscores_fixed.sol`,
`smtCheckerTests/operators/fixed_point_compound_add.sol` (`b[0] += 1`). -/
example : implicitOK .fixed 3 = true ∧ implicitOK .ufixed 4 = true ∧
    implicitOK .fixed 4.5 = true ∧ implicitOK .ufixed 2.5 = true ∧
    implicitOK (ty false 16 2 (by decide)) 3.25 = true ∧
    implicitOK (ty true 16 2 (by decide)) (-3.25) = true ∧
    implicitOK (ty true 16 2 (by decide)) 0 = true ∧
    implicitOK (ty false 32 1 (by decide)) 0 = true ∧
    implicitOK .ufixed 3.125 = true ∧
    implicitOK .fixed 3.1415 = true ∧ implicitOK .fixed 31.415 = true ∧
    implicitOK .fixed 1 = true := by
  decide +kernel

/-- `312_leading_zero_rationals_convert.sol`. -/
example : implicitOK (ty false 16 2 (by decide)) 0.5 = true ∧
    implicitOK (ty false 256 52 (by decide)) 0.0000000000000006661338147750939242541790008544921875 =
      true ∧
    implicitOK (ty true 16 2 (by decide)) (-0.5) = true ∧
    implicitOK (ty true 256 52 (by decide))
      (-0.0000000000000006661338147750939242541790008544921875) = true := by
  decide +kernel

/-- `323_mapping_with_fixed_literal.sol`: the key `0.5` at `ufixed8x1`. -/
example : implicitOK (ty false 8 1 (by decide)) 0.5 = true := by
  decide +kernel

/-- `328_rational_to_fixed_literal_expression.sol`, the accepted lines:
`3.5 * 3`, `4 - 2.5`, `11 / 4` at `ufixed64x8`, `599 + 0.21875` at
`ufixed240x5`, `2 ** -2` at `fixed`. -/
example :
    (CExpr.eval (.mul (.lit 3.5) (.lit 3))).map (implicitOK (ty false 64 8 (by decide))) =
      some true ∧
    (CExpr.eval (.sub (.lit 4) (.lit 2.5))).map (implicitOK (ty false 64 8 (by decide))) =
      some true ∧
    (CExpr.eval (.div (.lit 11) (.lit 4))).map (implicitOK (ty false 64 8 (by decide))) =
      some true ∧
    (CExpr.eval (.add (.lit 599) (.lit 0.21875))).map (implicitOK (ty false 240 5 (by decide))) =
      some true ∧
    (CExpr.eval (.pow (.lit 2) (.lit (-2)))).map (implicitOK .fixed) = some true := by
  decide +kernel

/-- `parsing/declaring_fixed_and_ufixed_variables.sol`: `fixed40x40`,
`ufixed8x8`, `fixed32x32` are types. -/
example : (FxTy.mk? true 40 40).isSome ∧ (FxTy.mk? false 8 8).isSome ∧
    (FxTy.mk? true 32 32).isSome := by
  decide

/-- `types/rational_number_literal_to_fixed_implicit.sol`. -/
example : implicitOK (ty false 8 2 (by decide)) 0.10 = true ∧
    implicitOK (ty false 8 2 (by decide)) 0.00 = true ∧
    implicitOK (ty false 8 2 (by decide)) 2.55 = true ∧
    implicitOK (ty true 8 1 (by decide)) 0.1 = true ∧
    implicitOK (ty true 8 1 (by decide)) 12.7 = true ∧
    implicitOK (ty true 8 1 (by decide)) (-12.8) = true := by
  decide +kernel

/-! ### Rejected by both -/

/-- `313_fixed_type_size_capabilities.sol`: `b` (78 digits at `ufixed256x77`)
and `e` (77 digits at `fixed256x76`) are refused, the other four accepted,
exactly solc's two errors. -/
example :
    implicitOK (ty false 256 1 (by decide))
      123456781234567979695948382928485849359686494864095409282048094275023098123.5 = true ∧
    implicitOK (ty false 256 77 (by decide))
      0.920890746623327805482905058466021565416131529487595827354393978494366605267637 = false ∧
    implicitOK (ty false 224 78 (by decide))
      0.000000000001519884736399797998492268541131529487595827354393978494366605267646 = true ∧
    implicitOK (ty true 256 1 (by decide))
      (-123456781234567979695948382928485849359686494864095409282048094275023098123.5) = true ∧
    implicitOK (ty true 256 76 (by decide))
      (-0.93322335481643744342575580035176794825198893968114429702091846411734101080123) = false ∧
    implicitOK (ty true 256 79 (by decide))
      (-0.0001178860664374434257558003517679482519889396811442970209184641173410108012309) =
      true := by
  decide +kernel

/-- `315_fixed_type_invalid_implicit_conversion_size.sol`: `ufixed128x18 →
ufixed248x8` drops digits. -/
example : FxTy.ufixed.implicitOK (ty false 248 8 (by decide)) = false := by
  decide +kernel

/-- `316_…_lost_data.sol`, `344_one_divided_by_three_integer_conversion.sol`:
`1/3` is not exact at `ufixed256x1`; solc suggests its mobile type
`ufixed256x77`. -/
example : implicitOK (ty false 256 1 (by decide)) (mkRat 1 3) = false ∧
    sig (mobileFx? (mkRat 1 3)) = some (false, 256, 77) := by
  decide +kernel

/-- Suggested mobile types in solc's messages: `321_rational_to_bytes_…`
(`16/5`: `ufixed8x1`), `327_rational_index_access.sol` (`1/2`: `ufixed8x1`),
`parsing/declaring_fixed_literal_variables.sol` (`3.14`: `ufixed16x2`,
refused at `fixed40x40`). -/
example : sig (mobileFx? (mkRat 16 5)) = some (false, 8, 1) ∧
    sig (mobileFx? (mkRat 1 2)) = some (false, 8, 1) ∧
    sig (mobileFx? 3.14) = some (false, 16, 2) ∧
    implicitOK (ty true 40 40 (by decide)) 3.14 = false := by
  decide +kernel

/-- `329`, `330`: a fractional exponent is refused. -/
example : CExpr.eval (.pow (.lit 2) (.lit (-2.2))) = none ∧
    CExpr.eval (.pow (.lit 3) (.lit 2.5)) = none := by
  decide +kernel

/-- `operators/signed_rational_modulus.sol`: `a = 0.42578125 % -0.4271…`
is `0.42578125`, exact at `fixed`; `.5 % a` is refused ("Fractional
literals not supported."). -/
example : (CExpr.eval (.mod (.lit 0.42578125) (.lit (-0.4271087646484375)))) = some 0.42578125 ∧
    litCommonRev? 0.5 .fixed = none := by
  decide +kernel

/-- `types/too_small_negative_numbers.sol`: `-1e-100` is not implicitly
convertible to `fixed8x80` but can be converted explicitly (to `0`). -/
example : implicitOK (ty true 8 80 (by decide)) (mkRat (-1) (10 ^ 100)) = false ∧
    (explicitRat? (ty true 8 80 (by decide)) (mkRat (-1) (10 ^ 100))).map Subtype.val = some 0 := by
  decide +kernel

/-- `types/rational_number_div_limit.sol`: `1/(2<<4094)/(2<<4094)` exceeds
4096 bits; the first quotient's mobile type is `ufixed8x80` (its value
truncates to `0`), as solc's message suggests. -/
example : CExpr.eval (.div (.lit (mkRat 1 (2 ^ 4095))) (.lit (2 ^ 4095))) = none ∧
    sig (mobileFx? (mkRat 1 (2 ^ 4095))) = some (false, 8, 80) := by
  decide +kernel

/-- `298`, `300`, `302`, `types/weird_sized_types.sol`: these (M, N) are not
in the scanner's bounds, so the names are identifiers. -/
example : (FxTy.mk? true 0 7).isNone ∧ (FxTy.mk? true 7 8).isNone ∧ (FxTy.mk? true 0 0).isNone ∧
    (FxTy.mk? true 8 888888888888888888888888888888888888888888888888888).isNone ∧
    (FxTy.mk? false 1 1).isNone ∧ (FxTy.mk? true 99000 1).isNone := by
  decide

/-! ### Accepted by solc's type checker, rejected here (intended) -/

/-- `317_fixed_type_valid_explicit_conversions.sol`: `ufixed256x80(1/3)` and
`ufixed248x80(1/3)` are out of range at 80 digits, compile errors by Q2;
`ufixed8x1(1/3)` is `0.3`. -/
example : explicitOK (ty false 256 80 (by decide)) (mkRat 1 3) = false ∧
    explicitOK (ty false 248 80 (by decide)) (mkRat 1 3) = false ∧
    (explicitRat? (ty false 8 1 (by decide)) (mkRat 1 3)).map Subtype.val = some 3 := by
  decide +kernel

/-- `328_rational_to_fixed_literal_expression.sol`, lines `e` and `f`:
`ufixed256x80(35.245 % 12.9)` (`9.445`) and `ufixed256x80(1.2 % 2)` (`1.2`)
are out of range at 80 digits, compile errors by Q2. -/
example : CExpr.eval (.mod (.lit 35.245) (.lit 12.9)) = some 9.445 ∧
    (CExpr.eval (.mod (.lit 35.245) (.lit 12.9))).map
      (explicitOK (ty false 256 80 (by decide))) = some false ∧
    (CExpr.eval (.mod (.lit 1.2) (.lit 2))).map
      (explicitOK (ty false 256 80 (by decide))) = some false := by
  decide +kernel

end Solidity.Language.FixedPoint.Conformance
