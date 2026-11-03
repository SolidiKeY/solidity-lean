import Solidity.Yul.LocalU8Compare
import Solidity.Yul.Checks.LocalU8Expr

namespace Solidity.Yul.Checks.LocalU8Compare
open Solidity.Yul.LocalU8Expr
open Solidity.Yul.LocalU8Compare
open Solidity.Yul.Checks.LocalU8Expr (U8 env ctx x arg zeroIndex target initial read deep wordValue snapshot cleanLocals)

structure Case where
  name : String
  op : Solidity.Source.BinOp
  left : Solidity.Source.RExpr env ctx.tys U8
  right : Solidity.Source.RExpr env ctx.tys U8
  one : Supported env ctx.tys left
  two : Supported env ctx.tys right
  state : LocalState env ctx.tys

def eqDirty : Case := ⟨"eqDirty",.eq,_,_,read x,read arg,initial 257 1 511⟩
def neqDirty : Case := ⟨"neqDirty",.ne,_,_,read x,read arg,initial 257 1 511⟩
def greaterDirty : Case := ⟨"greaterDirty",.gt,_,_,read x,read arg,initial 511 1 511⟩
def capturedOrder : Case := ⟨"capturedOrder",.eq,_,_,.assign x (read arg),read x,initial 257 2 511⟩
def nestedAdd : Case := ⟨"nestedAdd",.eq,_,_,.add (read x) (read zeroIndex),read arg,initial 257 1 511⟩
def overflowEffect : Case := ⟨"overflowEffect",.eq,_,_,.add (read x) (read arg),
  .assign target (read arg),initial 511 1 511⟩
def fixtures : List Case := [eqDirty,neqDirty,greaterDirty,capturedOrder,nestedAdd,overflowEffect]
def run (c : Case) (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) :=
  compare c.op c.one c.two pipeline fuel c.state
def wordResult (result : Solidity.Source.R (LocalValue env .bool)) : Option Nat :=
  match result with
  | .ok value => some (LocalOperations.scalarWord value (LocalOperations.boolShape env)).val
  | .error _ => none
def haltResult (result : Solidity.Source.R (LocalValue env .bool)) : Option Solidity.Source.Halt :=
  match result with | .ok _ => none | .error halt => some halt
def observe (c : Case) (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) : Option (List Nat) := do
  let result := run c pipeline fuel
  let b ← wordResult result.1
  pure [b,wordValue (result.2.1.get x),wordValue (result.2.1.get target)]

example : fixtures.map (fun c => observe c .legacy 8) =
    [some [1,257,0],some [0,257,0],some [1,511,0],some [0,2,0],some [1,257,0],none] := by decide
example : fixtures.map (fun c => observe c .viaIR 8) =
    [some [1,257,0],some [0,257,0],some [1,511,0],some [1,2,0],some [1,257,0],none] := by decide
example : observe capturedOrder .legacy 3 = none := by decide
example : observe capturedOrder .legacy 4 = some [0,2,0] := by decide
example : observe capturedOrder .viaIR 4 = some [1,2,0] := by decide
example : haltResult (run overflowEffect .legacy 5).1 =
    some (.revert (Solidity.Source.panicData .arithmetic)) := by decide
example : wordValue ((run overflowEffect .legacy 5).2.1.get target) = 1 := by decide
example : wordValue ((run overflowEffect .viaIR 5).2.1.get target) = 0 := by decide
example : haltResult (compare .add (read x) (read arg) .legacy 3 (initial 257 1 511)).1 =
    some (.stuck "not a comparison") := by decide
example : snapshot (compare .eq (.assign x (read arg)) deep .legacy 4 (initial 257 2 511)).2 =
    [257,2,0,511,0] := by decide
example : snapshot (compare .eq (.assign x (read arg)) deep .viaIR 4 (initial 257 2 511)).2 =
    [2,2,0,511,0] := by decide
example (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) :
    (run overflowEffect pipeline fuel).2.2 = overflowEffect.state.2 :=
  Solidity.Yul.LocalU8Compare.world _ _ _ pipeline fuel _
example (c : Case) (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) :
    compare c.op c.one c.two pipeline fuel
      (LocalState.ofClean (cleanLocals c.state,c.state.2)) =
    LocalBoolExpr.cleanOutcome ((Solidity.Source.evalE
      (Solidity.Source.SemanticsExamples.G0 pipeline) Solidity.Source.SemanticsExamples.F0 fuel
      (.compare c.op c.left c.right)).run (cleanLocals c.state,c.state.2)) :=
  Solidity.Yul.LocalU8Compare.source_agrees c.op c.one c.two
    (Solidity.Source.SemanticsExamples.G0 pipeline) Solidity.Source.SemanticsExamples.F0 rfl fuel _
def witness : Nonempty Case := ⟨capturedOrder⟩

#eval do
  for c in fixtures do
    for pipeline in [Solidity.Roadmap.Pipeline.legacy,.viaIR] do
      for fuel in [0,1,2,3,4,8] do
        let clean := (cleanLocals c.state,c.state.2)
        let actual := compare c.op c.one c.two pipeline fuel (LocalState.ofClean clean)
        let reference := LocalBoolExpr.cleanOutcome ((Solidity.Source.evalE
          (Solidity.Source.SemanticsExamples.G0 pipeline) Solidity.Source.SemanticsExamples.F0
            fuel (.compare c.op c.left c.right)).run clean)
        unless wordResult actual.1 == wordResult reference.1 &&
            haltResult actual.1 == haltResult reference.1 && snapshot actual.2 == snapshot reference.2 do
          throw (IO.userError "actual checked Source comparison mismatch")
  IO.println "LOCAL_U8_COMPARE_PASS:72 actual clean Source comparisons; raw projection/order/overflow/prefix controls"

#check @Solidity.Yul.LocalU8Compare.source_agrees
#print axioms Solidity.Yul.LocalU8Compare.source_agrees
end Solidity.Yul.Checks.LocalU8Compare
