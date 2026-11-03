import Solidity.Yul.LocalU8Agreement
import Solidity.Yul.Checks.LocalBoolExpr

namespace Solidity.Yul.Checks.LocalU8Expr
open Solidity.Yul.LocalU8Expr
abbrev U8 := _root_.Solidity.Yul.LocalU8Expr.Ty
def env : Solidity.Source.Env := ⟨[]⟩
def ctx : Solidity.Source.Ctx :=
  {env:=env,scope:=none,locals:=[("x",U8),("arg",U8),("zero",U8),("top",U8),("target",U8)]}
def x : Solidity.Source.Idx ctx.tys U8 := .here
def arg : Solidity.Source.Idx ctx.tys U8 := .there .here
def zeroIndex : Solidity.Source.Idx ctx.tys U8 := .there (.there .here)
def top : Solidity.Source.Idx ctx.tys U8 := .there (.there (.there .here))
def target : Solidity.Source.Idx ctx.tys U8 := .there (.there (.there (.there .here)))
def initial (a b high : Nat) : LocalState env ctx.tys :=
  ((.scalar (LocalOperations.u8Shape env) (word a),
    (.scalar (LocalOperations.u8Shape env) (word b),
      (.scalar (LocalOperations.u8Shape env) (word 0),
        (.scalar (LocalOperations.u8Shape env) (word high),
          (.scalar (LocalOperations.u8Shape env) (word 0),()))))),Solidity.Source.St.init env)
def read (index : Solidity.Source.Idx ctx.tys U8) : Supported env ctx.tys (.local index) := .local index

structure Case where
  name : String
  state : LocalState env ctx.tys
  expr : Solidity.Source.RExpr env ctx.tys U8
  proof : Supported env ctx.tys expr
  includeX : Bool := false

def copyRaw : Case := ⟨"copyRaw",initial 257 2 511,_,read x,false⟩
def addZero : Case := ⟨"addZero",initial 257 2 511,_,.add (read x) (read zeroIndex),false⟩
def assignRaw : Case := ⟨"assignRaw",initial 257 2 511,_,.assign target (read x),true⟩
def order : Case := ⟨"order",initial 257 2 511,_,.add (.assign x (read arg)) (read x),true⟩
def checkedOverflow : Case := ⟨"checkedOverflow",initial 511 1 511,_,.add (read x) (read arg),false⟩
def overflowAfterEffect : Case :=
  ⟨"overflowAfterEffect",initial 511 1 511,_,.add (.assign x (read arg)) (read top),false⟩
def fixtures : List Case := [copyRaw,addZero,assignRaw,order,checkedOverflow,overflowAfterEffect]
def wordValue (value : LocalValue env U8) : Nat :=
  (LocalOperations.scalarWord value (LocalOperations.u8Shape env)).val
def wordResult (result : Solidity.Source.R (LocalValue env U8)) : Option Nat :=
  match result with | .ok value => some (wordValue value) | .error _ => none
def haltResult (result : Solidity.Source.R (LocalValue env U8)) : Option Solidity.Source.Halt :=
  match result with | .ok _ => none | .error halt => some halt
def observe (c : Case) (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) : Option (List Nat) :=
  let (result,next) := eval c.proof pipeline fuel c.state
  match result with
  | .error _ => none
  | .ok value => some ([wordValue value] ++ if c.includeX then [wordValue (next.1.get x)] else [])

example : fixtures.map (fun c => observe c .legacy 8) =
    [some [257],some [1],some [257,257],some [3,2],none,none] := by decide
example : fixtures.map (fun c => observe c .viaIR 8) =
    [some [257],some [1],some [257,257],some [4,2],none,none] := by decide
example : observe addZero .legacy 2 = none := by decide
example : observe addZero .legacy 3 = some [1] := by decide
example : haltResult (eval checkedOverflow.proof .legacy 3 checkedOverflow.state).1 =
    some (.revert (Solidity.Source.panicData .arithmetic)) := by decide
example : haltResult (eval overflowAfterEffect.proof .viaIR 4 overflowAfterEffect.state).1 =
    some (.revert (Solidity.Source.panicData .arithmetic)) := by decide
example : wordValue ((eval overflowAfterEffect.proof .legacy 4 overflowAfterEffect.state).2.1.get x) = 1 := by decide
example : wordValue ((eval overflowAfterEffect.proof .viaIR 4 overflowAfterEffect.state).2.1.get x) = 1 := by decide

/-- The first operand's write survives a later operand timeout; first follows
the actual pipeline order. -/
def deep : Supported env ctx.tys (.assign (.local x) (.assign (.local x) (.local arg))) :=
  .assign x (.assign x (read arg))
def rightDeep : Case := ⟨"rightDeep",initial 257 2 511,_,.add (.assign x (read arg)) deep,false⟩
def leftDeep : Case := ⟨"leftDeep",initial 257 2 511,_,.add deep (.assign x (read arg)),false⟩
example : haltResult (eval rightDeep.proof .legacy 4 rightDeep.state).1 = some .timeout := by decide
example : haltResult (eval rightDeep.proof .viaIR 4 rightDeep.state).1 = some .timeout := by decide
example : wordValue ((eval rightDeep.proof .legacy 4 rightDeep.state).2.1.get x) = 257 := by decide
example : wordValue ((eval rightDeep.proof .viaIR 4 rightDeep.state).2.1.get x) = 2 := by decide
example : wordValue ((eval leftDeep.proof .legacy 4 leftDeep.state).2.1.get x) = 2 := by decide
example : wordValue ((eval leftDeep.proof .viaIR 4 leftDeep.state).2.1.get x) = 257 := by decide
example (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) :
    (eval order.proof pipeline fuel order.state).2.2 = order.state.2 := world order.proof pipeline fuel order.state
example : ¬ Nonempty (Supported env ctx.tys (.binary .sub (.local x) (.local arg))) := by
  rintro ⟨proof⟩
  cases proof

def cleanLocals (state : LocalState env ctx.tys) : Solidity.Source.Locals env.layout ctx.tys :=
  .cons (LocalOperations.u8Input (state.1.get x))
    (.cons (LocalOperations.u8Input (state.1.get arg))
      (.cons (LocalOperations.u8Input (state.1.get zeroIndex))
        (.cons (LocalOperations.u8Input (state.1.get top))
          (.cons (LocalOperations.u8Input (state.1.get target)) .nil))))
def snapshot (state : LocalState env ctx.tys) : List Nat :=
  [wordValue (state.1.get x),wordValue (state.1.get arg),wordValue (state.1.get zeroIndex),
    wordValue (state.1.get top),wordValue (state.1.get target)]
example (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) :
    eval order.proof pipeline fuel (LocalState.ofClean (cleanLocals order.state,order.state.2)) =
      cleanOutcome ((Solidity.Source.evalE (Solidity.Source.SemanticsExamples.G0 pipeline)
        Solidity.Source.SemanticsExamples.F0 fuel order.expr).run (cleanLocals order.state,order.state.2)) :=
  source_agrees order.proof (Solidity.Source.SemanticsExamples.G0 pipeline)
    Solidity.Source.SemanticsExamples.F0 rfl fuel (cleanLocals order.state,order.state.2)
def certWitness : Nonempty (Supported env ctx.tys order.expr) := ⟨order.proof⟩
def stateWitness : Nonempty (LocalState env ctx.tys) := ⟨order.state⟩

#eval do
  for c in fixtures ++ [leftDeep,rightDeep] do
    for pipeline in [Solidity.Roadmap.Pipeline.legacy,.viaIR] do
      for fuel in [0,1,2,3,4,8] do
        let clean := (cleanLocals c.state,c.state.2)
        let actual := eval c.proof pipeline fuel (LocalState.ofClean clean)
        let reference := cleanOutcome ((Solidity.Source.evalE
          (Solidity.Source.SemanticsExamples.G0 pipeline) Solidity.Source.SemanticsExamples.F0
            fuel c.expr).run clean)
        unless wordResult actual.1 == wordResult reference.1 &&
            haltResult actual.1 == haltResult reference.1 && snapshot actual.2 == snapshot reference.2 do
          throw (IO.userError "actual checked Source u8 comparison failed")
  unless observe order .legacy 8 == some [3,2] && observe order .viaIR 8 == some [4,2] do
    throw (IO.userError "checked u8 captured-operand pipeline order changed")
  unless snapshot (eval rightDeep.proof .legacy 4 rightDeep.state).2 == [257,2,0,511,0] &&
      snapshot (eval rightDeep.proof .viaIR 4 rightDeep.state).2 == [2,2,0,511,0] do
    throw (IO.userError "checked u8 pipeline timeout prefix changed")
  IO.println "LOCAL_U8_COMPILED_PASS:96 actual checked clean Source comparisons; raw copies/order/overflow/prefix effects"

#check @Solidity.Yul.LocalU8Expr.source_agrees
#print axioms Solidity.Yul.LocalU8Expr.source_agrees
#print axioms Solidity.Yul.LocalU8Expr.evidence_independent
end Solidity.Yul.Checks.LocalU8Expr
