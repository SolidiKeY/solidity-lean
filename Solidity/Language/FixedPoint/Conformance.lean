import Solidity.Language.FixedPoint.Literals

namespace Solidity.Language.FixedPoint.Conformance

open Fx

def sig (o : Option FxTy) : Option (Bool × Nat × Nat) := o.map fun t => (t.signed, t.bits, t.digits)

def ty (signed : Bool) (m n : Nat) (h : (FxTy.mk? signed m n).isSome = true) : FxTy :=
  (FxTy.mk? signed m n).get h

def implicitOK (t : FxTy) (q : Rat) : Bool := (ofRat? t q).isSome

def explicitOK (t : FxTy) (q : Rat) : Bool := (explicitRat? t q).isSome

example : (CExpr.eval (.mod (.lit 0.1) (.lit (-0.4271087646484375)))).map (implicitOK .fixed) =
      some true ∧
    (CExpr.eval (.mod (.lit 0.1) (.lit 0.4271087646484375))) = some 0.1 ∧
    (CExpr.eval (.div (.lit 0) (.lit 0.123))) = some 0 ∧
    (CExpr.eval (.div (.lit 0) (.lit (-0.123)))) = some 0 := by
  decide +kernel

example : explicitOK .ufixed (mkRat (4 * 10 ^ 18) (3 * 3600)) = true ∧
    sig (mobileFx? (mkRat (10 ^ 16) 27)) = some (false, 256, 62) := by
  decide +kernel

example : explicitOK .fixed 3.5 = true ∧ explicitOK .fixed (-4.25) = true ∧
    explicitOK .fixed 967.125 = true ∧
    explicitOK (ty false 128 3 (by decide)) 3.5 = true ∧
    implicitOK (ty false 128 3 (by decide)) 4.125 = true ∧
    implicitOK (ty false 128 3 (by decide)) 2.5 = true ∧
    implicitOK (ty false 128 3 (by decide)) 4.0 = true := by
  decide +kernel

example : (litCommon? (ty false 128 3 (by decide)) 4.125).map (·.digits) = some 3 ∧
    (litCommon? (ty false 128 3 (by decide)) 2.5).map (·.digits) = some 3 ∧
    (litCommon? (ty false 128 3 (by decide)) 4.0).map (·.digits) = some 3 ∧
    (litCommon? .fixed 1).map (·.bits) = some 128 := by
  decide +kernel

example : FxTy.fixed.intImplicit (-2 ^ 63) (2 ^ 63 - 1) = true ∧
    FxTy.ufixed.intImplicit 0 (2 ^ 64 - 1) = true := by
  decide +kernel

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

example : implicitOK (ty false 16 2 (by decide)) 0.5 = true ∧
    implicitOK (ty false 256 52 (by decide)) 0.0000000000000006661338147750939242541790008544921875 =
      true ∧
    implicitOK (ty true 16 2 (by decide)) (-0.5) = true ∧
    implicitOK (ty true 256 52 (by decide))
      (-0.0000000000000006661338147750939242541790008544921875) = true := by
  decide +kernel

example : implicitOK (ty false 8 1 (by decide)) 0.5 = true := by
  decide +kernel

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

example : (FxTy.mk? true 40 40).isSome ∧ (FxTy.mk? false 8 8).isSome ∧
    (FxTy.mk? true 32 32).isSome := by
  decide

example : implicitOK (ty false 8 2 (by decide)) 0.10 = true ∧
    implicitOK (ty false 8 2 (by decide)) 0.00 = true ∧
    implicitOK (ty false 8 2 (by decide)) 2.55 = true ∧
    implicitOK (ty true 8 1 (by decide)) 0.1 = true ∧
    implicitOK (ty true 8 1 (by decide)) 12.7 = true ∧
    implicitOK (ty true 8 1 (by decide)) (-12.8) = true := by
  decide +kernel

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

example : implicitOK .ufixed (mkRat 11 4) = true ∧
    FxTy.ufixed.implicitOK (ty false 248 8 (by decide)) = false := by
  decide +kernel

example : implicitOK (ty false 256 1 (by decide)) (mkRat 1 3) = false ∧
    sig (mobileFx? (mkRat 1 3)) = some (false, 256, 77) := by
  decide +kernel

example : sig (mobileFx? (mkRat 16 5)) = some (false, 8, 1) ∧
    sig (mobileFx? (mkRat 1 2)) = some (false, 8, 1) ∧
    sig (mobileFx? 3.14) = some (false, 16, 2) ∧
    implicitOK (ty true 40 40 (by decide)) 3.14 = false := by
  decide +kernel

example : CExpr.eval (.pow (.lit 2) (.lit (-2.2))) = none ∧
    CExpr.eval (.pow (.lit 3) (.lit 2.5)) = none ∧
    CExpr.eval (.pow (.lit 2) (.div (.lit 1) (.lit 2))) = none ∧
    CExpr.eval (.pow (.lit 42) (.div (.lit (-1)) (.lit 4))) = none := by
  decide +kernel

example : (CExpr.eval (.mod (.lit 0.42578125) (.lit (-0.4271087646484375)))) = some 0.42578125 ∧
    litCommonRev? 0.5 .fixed = none := by
  decide +kernel

example : implicitOK (ty true 8 80 (by decide)) (mkRat (-1) (10 ^ 100)) = false ∧
    (explicitRat? (ty true 8 80 (by decide)) (mkRat (-1) (10 ^ 100))).map Subtype.val = some 0 := by
  decide +kernel

example : CExpr.eval (.div (.lit (mkRat 1 (2 ^ 4095))) (.lit (2 ^ 4095))) = none ∧
    sig (mobileFx? (mkRat 1 (2 ^ 4095))) = some (false, 8, 80) := by
  decide +kernel

example : (FxTy.mk? true 99999999999999999999999999999999999999 7).isNone ∧
    (FxTy.mk? true 0 7).isNone ∧ (FxTy.mk? true 7 8).isNone ∧ (FxTy.mk? true 0 0).isNone ∧
    (FxTy.mk? true 8 888888888888888888888888888888888888888888888888888).isNone ∧
    (FxTy.mk? false 1 1).isNone ∧ (FxTy.mk? true 99000 1).isNone := by
  decide

example : explicitOK (ty false 256 80 (by decide)) (mkRat 1 3) = false ∧
    explicitOK (ty false 248 80 (by decide)) (mkRat 1 3) = false ∧
    (explicitRat? (ty false 8 1 (by decide)) (mkRat 1 3)).map Subtype.val = some 3 := by
  decide +kernel

example : CExpr.eval (.mod (.lit 35.245) (.lit 12.9)) = some 9.445 ∧
    (CExpr.eval (.mod (.lit 35.245) (.lit 12.9))).map
      (explicitOK (ty false 256 80 (by decide))) = some false ∧
    (CExpr.eval (.mod (.lit 1.2) (.lit 2))).map
      (explicitOK (ty false 256 80 (by decide))) = some false := by
  decide +kernel

end Solidity.Language.FixedPoint.Conformance
