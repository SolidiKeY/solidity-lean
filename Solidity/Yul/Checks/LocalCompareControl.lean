import Solidity.Yul.LocalCompareControl
import Solidity.Yul.Checks.LocalBoolExpr

namespace Solidity.Yul.Checks.LocalCompareControl
abbrev U8 := LocalU8Expr.Ty
def env : Solidity.Source.Env := ⟨[]⟩
def ctx : Solidity.Source.Ctx :=
  {env:=env,scope:=none,locals:=[("x",U8),("arg",U8),("flag",.bool),("target",.bool),("other",.bool)]}
def x : Solidity.Source.Idx ctx.tys U8 := .here
def arg : Solidity.Source.Idx ctx.tys U8 := .there .here
def flag : Solidity.Source.Idx ctx.tys .bool := .there (.there .here)
def target : Solidity.Source.Idx ctx.tys .bool := .there (.there (.there .here))
def other : Solidity.Source.Idx ctx.tys .bool := .there (.there (.there (.there .here)))
def initial (a b : Nat) : LocalState env ctx.tys :=
  ((.scalar (LocalOperations.u8Shape env) (word a),
    (.scalar (LocalOperations.u8Shape env) (word b),
      (.scalar (LocalOperations.boolShape env) (word 2),
        (.scalar (LocalOperations.boolShape env) (word 8),
          (.scalar (LocalOperations.boolShape env) (word 4),()))))),Solidity.Source.St.init env)
def readU8 (i : Solidity.Source.Idx ctx.tys U8) : LocalU8Expr.Supported env ctx.tys (.local i) := .local i
def readBool (i : Solidity.Source.Idx ctx.tys .bool) : LocalBoolControl.Supported env ctx.tys (.local i) := .base (.local i)

structure Case where
  name : String
  op : Solidity.Source.BinOp
  left : Solidity.Source.RExpr env ctx.tys U8
  right : Solidity.Source.RExpr env ctx.tys U8
  yes : Solidity.Source.RExpr env ctx.tys .bool
  no : Solidity.Source.RExpr env ctx.tys .bool
  one : LocalU8Expr.Supported env ctx.tys left
  two : LocalU8Expr.Supported env ctx.tys right
  yesProof : LocalBoolControl.Supported env ctx.tys yes
  noProof : LocalBoolControl.Supported env ctx.tys no
  state : LocalState env ctx.tys

def eqCopy : Case := ⟨"eqCopy",.eq,_,_,_,_,readU8 x,readU8 arg,
  .assign target (readBool flag),.assign target (readBool other),initial 257 1⟩
def neqCopy : Case := {eqCopy with name:="neqCopy",op:=.ne}
def capturedOrder : Case := ⟨"capturedOrder",.eq,_,_,_,_,.assign x (readU8 arg),readU8 x,
  .base (.literal true),.base (.literal false),initial 257 2⟩
def skipDeep : Case := ⟨"skipDeep",.eq,_,_,_,_,readU8 x,readU8 arg,
  readBool flag,.not (.not (.not (readBool other))),initial 257 1⟩
def overflow : Case := ⟨"overflow",.eq,_,_,_,_,.add (readU8 x) (readU8 arg),readU8 arg,
  .assign target (readBool flag),.assign target (readBool other),initial 511 1⟩
def selectedNot : Case := ⟨"selectedNot",.eq,_,_,_,_,readU8 x,readU8 arg,
  .not (readBool flag),readBool other,initial 257 1⟩
def fixtures : List Case := [eqCopy,neqCopy,capturedOrder,skipDeep,overflow,selectedNot]
def run (c : Case) (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) :=
  Solidity.Yul.LocalCompareControl.eval c.op c.one c.two c.yesProof c.noProof pipeline fuel c.state
def boolWord (v : LocalValue env .bool) : Nat :=
  (LocalOperations.scalarWord v (LocalOperations.boolShape env)).val
def u8Word (v : LocalValue env U8) : Nat :=
  (LocalOperations.scalarWord v (LocalOperations.u8Shape env)).val
def snapshot (s : LocalState env ctx.tys) : List Nat :=
  [u8Word (s.1.get x),u8Word (s.1.get arg),boolWord (s.1.get flag),boolWord (s.1.get target),boolWord (s.1.get other)]
def observe (c : Case) (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) : Option (List Nat) := do
  let result := run c pipeline fuel
  let value ← LocalBoolExpr.wordResult result.1
  pure [value,u8Word (result.2.1.get x),boolWord (result.2.1.get target)]

example : fixtures.map (fun c => observe c .legacy 8) =
    [some [2,257,2],some [4,257,4],some [0,2,8],some [2,257,8],none,some [0,257,8]] := by decide
example : fixtures.map (fun c => observe c .viaIR 8) =
    [some [2,257,2],some [4,257,4],some [1,2,8],some [2,257,8],none,some [0,257,8]] := by decide
example : observe skipDeep .legacy 3 = none := by decide
example : observe skipDeep .legacy 4 = some [2,257,8] := by decide
example : observe {skipDeep with op:=.ne} .legacy 4 = none := by decide
example : LocalBoolExpr.haltResult (run overflow .legacy 6).1 =
    some (.revert (Solidity.Source.panicData .arithmetic)) := by decide
example : snapshot (run overflow .viaIR 6).2 = [511,1,2,8,4] := by decide
example : LocalBoolExpr.haltResult (run {eqCopy with op:=.add} .legacy 4).1 =
    some (.stuck "not a comparison") := by decide
example : snapshot (run {eqCopy with op:=.add} .legacy 4).2 = [257,1,2,8,4] := by decide

def partialCase : Case := ⟨"partialCase",.eq,_,_,_,_,readU8 x,readU8 arg,
  .and (.assign target (.base (.literal true))) (.not (.not (.not (readBool flag)))),
  readBool other,initial 257 1⟩
example : LocalBoolExpr.haltResult (run partialCase .legacy 5).1 = some .timeout := by decide
example : boolWord ((run partialCase .legacy 5).2.1.get target) = 1 := by decide
example : observe partialCase .legacy 6 = some [0,257,1] := by decide
example (c : Case) (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) :
    (run c pipeline fuel).2.2 = c.state.2 :=
  Solidity.Yul.LocalCompareControl.world _ _ _ _ _ pipeline fuel _
def witness : Nonempty Case := ⟨partialCase⟩

def cleanLocals (s : LocalState env ctx.tys) : Solidity.Source.Locals env.layout ctx.tys :=
  .cons (LocalOperations.u8Input (s.1.get x))
    (.cons (LocalOperations.u8Input (s.1.get arg))
      (.cons (.bool (LocalBoolControl.truth (s.1.get flag)))
        (.cons (.bool (LocalBoolControl.truth (s.1.get target)))
          (.cons (.bool (LocalBoolControl.truth (s.1.get other))) .nil))))

#eval do
  for c in fixtures ++ [partialCase] do
    for pipeline in [Solidity.Roadmap.Pipeline.legacy,.viaIR] do
      for fuel in [0,1,2,3,4,5,6,8] do
        let clean := (cleanLocals c.state,c.state.2)
        let actual := Solidity.Yul.LocalCompareControl.eval c.op c.one c.two c.yesProof c.noProof
          pipeline fuel (LocalState.ofClean clean)
        let reference := LocalBoolExpr.cleanOutcome ((Solidity.Source.evalE
          (Solidity.Source.SemanticsExamples.G0 pipeline) Solidity.Source.SemanticsExamples.F0 fuel
            (.cond (.compare c.op c.left c.right) c.yes c.no)).run clean)
        unless LocalBoolExpr.wordResult actual.1 == LocalBoolExpr.wordResult reference.1 &&
            LocalBoolExpr.haltResult actual.1 == LocalBoolExpr.haltResult reference.1 &&
            snapshot actual.2 == snapshot reference.2 do
          throw (IO.userError "comparison/control actual Source mismatch")
  IO.println "LOCAL_COMPARE_CONTROL_PASS:112 actual clean Source comparisons; dirty branch/skip/prefix controls"

#check @Solidity.Yul.LocalCompareControl.source_agrees
#print axioms Solidity.Yul.LocalCompareControl.source_agrees
end Solidity.Yul.Checks.LocalCompareControl
