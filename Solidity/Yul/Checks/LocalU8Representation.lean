import Solidity.Yul.LocalU8Representation
import Solidity.Yul.Checks.LocalBoolRepresentation

namespace Solidity.Yul.Checks.LocalU8Representation
export Solidity.Yul.Checks.LocalBoolRepresentation (env cleanTrue cleanFalse)
abbrev Ty := LocalU8Expr.Ty
abbrev Ctx : Solidity.Source.RCtx := [Ty,Ty,.bool]
def x : Solidity.Source.Idx Ctx Ty := .here
def arg : Solidity.Source.Idx Ctx Ty := .there .here
def flag : Solidity.Source.Idx Ctx .bool := .there (.there .here)
def raw8 (n : Nat) : LocalValue env Ty :=
  .scalar (LocalOperations.u8Shape env) (word n)
def rawBool : LocalValue env .bool :=
  .scalar (LocalOperations.boolShape env) (word 1)
def initial (a b : Nat) (value : LocalValue env .bool) (world : Solidity.Source.St env) :
    LocalState env Ctx := ((raw8 a,(raw8 b,(value,()))),world)
def readX : LocalU8Expr.Supported env Ctx (.local x) := .local x
def readArg : LocalU8Expr.Supported env Ctx (.local arg) := .local arg
def assignExpr : Solidity.Source.RExpr env Ctx Ty := .assign (.local x) (.local arg)
def assign : LocalU8Expr.Supported env Ctx assignExpr := .assign x readArg
def orderExpr : Solidity.Source.RExpr env Ctx Ty := .binary .add assignExpr (.local x)
def order : LocalU8Expr.Supported env Ctx orderExpr := .add assign readX
def deepExpr : Solidity.Source.RExpr env Ctx Ty := .assign (.local x) assignExpr
def deep : LocalU8Expr.Supported env Ctx deepExpr := .assign x assign
def timeoutExpr : Solidity.Source.RExpr env Ctx Ty := .binary .add assignExpr deepExpr
def timeout : LocalU8Expr.Supported env Ctx timeoutExpr := .add assign deep
def sumExpr : Solidity.Source.RExpr env Ctx Ty := .binary .add (.local x) (.local arg)
def sum : LocalU8Expr.Supported env Ctx sumExpr := .add readX readArg
def yes : LocalBoolControl.Supported env Ctx (.local flag) := .base (.local flag)
def no : LocalBoolControl.Supported env Ctx (.unary .not (.local flag)) := .not yes
def word8 (value : LocalValue env Ty) : Word :=
  LocalOperations.scalarWord value (LocalOperations.u8Shape env)
def conditional (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
    (state : LocalState env Ctx) :=
  LocalCompareControl.eval .eq assign readX yes no pipeline fuel state
def witness : Nonempty (LocalU8Expr.Supported env Ctx orderExpr) := ⟨order⟩
def concrete (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
    (one two : LocalState env Ctx) (related : LocalBoolRepresentation.State one two) :=
  Solidity.Yul.LocalU8Representation.conditional env Ctx assignExpr (.local x) .eq
    assign readX (.local flag) (.unary .not (.local flag)) yes no pipeline fuel one two related

theorem inputRelated : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalBoolRepresentation.State (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.cleanTrue world) (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by

  intro world; exact ⟨.cons (.same _) (.cons (.same _) (.cons (.boolean (one := Solidity.Yul.Checks.LocalU8Representation.cleanTrue) (two := Solidity.Yul.Checks.LocalU8Representation.rawBool) rfl) (.same (ctx := []) ()))),rfl⟩

theorem legacyOrder : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), (Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.order .legacy 5 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1.map Solidity.Yul.Checks.LocalU8Representation.word8 = .ok (Solidity.Yul.word 3) := by

  intro world
  simp only [Solidity.Yul.Checks.LocalU8Representation.order,Solidity.Yul.LocalU8Expr.add_legacy,
    Solidity.Yul.Checks.LocalU8Representation.assign,Solidity.Yul.Checks.LocalU8Representation.readX,Solidity.Yul.Checks.LocalU8Representation.readArg,Solidity.Yul.LocalU8Expr.assign_step,Solidity.Yul.LocalU8Expr.local_read,
    Solidity.Yul.Checks.LocalU8Representation.initial,Solidity.Yul.Checks.LocalU8Representation.x,Solidity.Yul.Checks.LocalU8Representation.arg,Solidity.Yul.LocalValues.get,Solidity.Yul.LocalValues.set]
  change (Solidity.Yul.LocalOperations.u8Binary true .add (Solidity.Yul.Checks.LocalU8Representation.raw8 2) (Solidity.Yul.Checks.LocalU8Representation.raw8 257)).map Solidity.Yul.Checks.LocalU8Representation.word8 = .ok (Solidity.Yul.word 3)
  unfold Solidity.Yul.LocalOperations.u8Binary Solidity.Yul.LocalOperations.u8Input Solidity.Yul.Checks.LocalU8Representation.raw8
  simp only [Solidity.Yul.LocalOperations.scalarWord_raw]
  have residue0 : (Solidity.Yul.word 2).val % 256 = 2 := by decide
  have residue1 : (Solidity.Yul.word 257).val % 256 = 1 := by decide
  simp only [residue0,residue1]
  rfl

theorem viaOrder : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), (Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.order .viaIR 5 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1.map Solidity.Yul.Checks.LocalU8Representation.word8 = .ok (Solidity.Yul.word 4) := by

  intro world
  simp only [Solidity.Yul.Checks.LocalU8Representation.order,Solidity.Yul.LocalU8Expr.add_viaIR,
    Solidity.Yul.Checks.LocalU8Representation.assign,Solidity.Yul.Checks.LocalU8Representation.readX,Solidity.Yul.Checks.LocalU8Representation.readArg,Solidity.Yul.LocalU8Expr.assign_step,Solidity.Yul.LocalU8Expr.local_read,
    Solidity.Yul.Checks.LocalU8Representation.initial,Solidity.Yul.Checks.LocalU8Representation.x,Solidity.Yul.Checks.LocalU8Representation.arg,Solidity.Yul.LocalValues.get,Solidity.Yul.LocalValues.set]
  change (Solidity.Yul.LocalOperations.u8Binary true .add (Solidity.Yul.Checks.LocalU8Representation.raw8 2) (Solidity.Yul.Checks.LocalU8Representation.raw8 2)).map Solidity.Yul.Checks.LocalU8Representation.word8 = .ok (Solidity.Yul.word 4)
  unfold Solidity.Yul.LocalOperations.u8Binary Solidity.Yul.LocalOperations.u8Input Solidity.Yul.Checks.LocalU8Representation.raw8
  simp only [Solidity.Yul.LocalOperations.scalarWord_raw]
  have residue0 : (Solidity.Yul.word 2).val % 256 = 2 := by decide
  simp only [residue0]
  rfl

theorem legacyPartialTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.timeout .legacy 4 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.error .timeout,Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by

  intro world; rfl

theorem viaPartialTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.timeout .viaIR 4 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.error .timeout,Solidity.Yul.Checks.LocalU8Representation.initial 2 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by

  intro world; rfl

theorem overflow : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), (Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.sum pipeline 3 (Solidity.Yul.Checks.LocalU8Representation.initial 511 1 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1 = .error (.revert (Solidity.Source.panicData .arithmetic)) := by

  have arithmetic : Solidity.Yul.LocalOperations.u8Binary true .add (Solidity.Yul.Checks.LocalU8Representation.raw8 511) (Solidity.Yul.Checks.LocalU8Representation.raw8 1) =
      .error (.revert (Solidity.Source.panicData .arithmetic)) := by
    unfold Solidity.Yul.LocalOperations.u8Binary Solidity.Yul.LocalOperations.u8Input Solidity.Yul.Checks.LocalU8Representation.raw8
    simp only [Solidity.Yul.LocalOperations.scalarWord_raw]
    have large : (Solidity.Yul.word 511).val % 256 = 255 := by decide
    have small : (Solidity.Yul.word 1).val % 256 = 1 := by decide
    simp only [large,small]
    rfl
  intro pipeline world
  cases pipeline with
  | legacy =>
    simp only [Solidity.Yul.Checks.LocalU8Representation.sum,Solidity.Yul.Checks.LocalU8Representation.readX,Solidity.Yul.Checks.LocalU8Representation.readArg,Solidity.Yul.LocalU8Expr.add_legacy,
      Solidity.Yul.LocalU8Expr.local_read,Solidity.Yul.Checks.LocalU8Representation.initial,Solidity.Yul.Checks.LocalU8Representation.x,Solidity.Yul.Checks.LocalU8Representation.arg,Solidity.Yul.LocalValues.get]
    change Solidity.Yul.LocalOperations.u8Binary true .add (Solidity.Yul.Checks.LocalU8Representation.raw8 511) (Solidity.Yul.Checks.LocalU8Representation.raw8 1) = _
    exact arithmetic
  | viaIR =>
    simp only [Solidity.Yul.Checks.LocalU8Representation.sum,Solidity.Yul.Checks.LocalU8Representation.readX,Solidity.Yul.Checks.LocalU8Representation.readArg,Solidity.Yul.LocalU8Expr.add_viaIR,
      Solidity.Yul.LocalU8Expr.local_read,Solidity.Yul.Checks.LocalU8Representation.initial,Solidity.Yul.Checks.LocalU8Representation.x,Solidity.Yul.Checks.LocalU8Representation.arg,Solidity.Yul.LocalValues.get]
    change Solidity.Yul.LocalOperations.u8Binary true .add (Solidity.Yul.Checks.LocalU8Representation.raw8 511) (Solidity.Yul.Checks.LocalU8Representation.raw8 1) = _
    exact arithmetic

theorem legacySelection : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), (Solidity.Yul.Checks.LocalU8Representation.conditional .legacy 8 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1 = .ok Solidity.Yul.Checks.LocalU8Representation.cleanFalse := by

  intro world
  simp only [Solidity.Yul.Checks.LocalU8Representation.conditional,Solidity.Yul.LocalCompareControl.step,Solidity.Yul.Checks.LocalU8Representation.assign,Solidity.Yul.Checks.LocalU8Representation.readX,Solidity.Yul.Checks.LocalU8Representation.readArg,
    Solidity.Yul.LocalU8Compare.compare_legacy,Solidity.Yul.LocalU8Expr.assign_step,
    Solidity.Yul.LocalU8Expr.local_read,Solidity.Yul.Checks.LocalU8Representation.initial,Solidity.Yul.Checks.LocalU8Representation.x,Solidity.Yul.Checks.LocalU8Representation.arg,
    Solidity.Yul.LocalValues.get,Solidity.Yul.LocalValues.set]
  rfl

theorem viaSelection : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), (Solidity.Yul.Checks.LocalU8Representation.conditional .viaIR 8 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1 = .ok Solidity.Yul.Checks.LocalU8Representation.rawBool := by

  intro world; rfl

theorem projectionDiffers : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), (Solidity.Yul.Checks.LocalU8Representation.conditional .viaIR 8 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.cleanTrue world)).1.map Solidity.Yul.LocalValue.clean? = .ok (some (.bool true)) ∧ (Solidity.Yul.Checks.LocalU8Representation.conditional .viaIR 8 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1.map Solidity.Yul.LocalValue.clean? = .ok none := by

  intro world; exact ⟨rfl,rfl⟩

theorem unsupportedSub : ¬ Nonempty (Solidity.Yul.LocalU8Expr.Supported Solidity.Yul.Checks.LocalU8Representation.env Solidity.Yul.Checks.LocalU8Representation.Ctx (.binary .sub (.local Solidity.Yul.Checks.LocalU8Representation.x) (.local Solidity.Yul.Checks.LocalU8Representation.arg))) := by

  rintro ⟨proof⟩; cases proof

theorem flagRetained : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), (Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.order pipeline 5 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).2.1.get Solidity.Yul.Checks.LocalU8Representation.flag = Solidity.Yul.Checks.LocalU8Representation.rawBool := by

  intro pipeline world; cases pipeline <;> rfl

#print axioms Solidity.Yul.LocalU8Representation.value_eq
#print axioms Solidity.Yul.LocalU8Representation.expression
#print axioms Solidity.Yul.LocalU8Representation.comparison
#print axioms Solidity.Yul.LocalU8Representation.conditional
#print axioms inputRelated
#print axioms legacyOrder
#print axioms viaOrder
#print axioms legacyPartialTimeout
#print axioms viaPartialTimeout
#print axioms overflow
#print axioms legacySelection
#print axioms viaSelection
#print axioms projectionDiffers
#print axioms unsupportedSub
#print axioms flagRetained

end Solidity.Yul.Checks.LocalU8Representation
