import Solidity.Yul.LocalExprStatement
import Solidity.Yul.Checks.LocalCompareControl

namespace Solidity.Yul.Checks.LocalExprStatement
open Solidity.Yul.Checks.LocalCompareControl
open Solidity.Yul.LocalExprStatement

def capturedStatement : Case := ⟨"capturedOrder",.eq,_,_,_,_,.assign x (readU8 arg),readU8 x,
  .assign target (.base (.literal true)),.assign target (.base (.literal false)),initial 257 2⟩
def fixtures : List Case := [eqCopy,neqCopy,capturedStatement,skipDeep,overflow,selectedNot]
def run (c : Case) (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) :=
  discard (Solidity.Yul.LocalCompareControl.eval c.op c.one c.two c.yesProof c.noProof pipeline)
    fuel c.state
def observe (c : Case) (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) : Option (List Nat) :=
  let (result,next) := run c pipeline fuel
  match result with
  | .error _ => none
  | .ok _ => some [u8Word (next.1.get x),boolWord (next.1.get target),boolWord (next.1.get flag)]
def haltResult (result : Solidity.Source.R Unit) : Option Solidity.Source.Halt :=
  match result with | .error halt => some halt | .ok _ => none

example : fixtures.map (fun c => observe c .legacy 9) =
    [some [257,2,2],some [257,4,2],some [2,0,2],some [257,8,2],none,some [257,8,2]] := by decide
example : fixtures.map (fun c => observe c .viaIR 9) =
    [some [257,2,2],some [257,4,2],some [2,1,2],some [257,8,2],none,some [257,8,2]] := by decide
example : observe skipDeep .legacy 4 = none := by decide
example : observe skipDeep .legacy 5 = some [257,8,2] := by decide
example : observe {skipDeep with op:=.ne} .legacy 5 = none := by decide
example : haltResult (run overflow .legacy 7).1 =
    some (.revert (Solidity.Source.panicData .arithmetic)) := by decide
example : haltResult (run {eqCopy with op:=.add} .legacy 5).1 =
    some (.stuck "not a comparison") := by decide
example : snapshot (run partialCase .legacy 6).2 = [257,1,2,1,4] := by decide
example : haltResult (run partialCase .legacy 6).1 = some .timeout := by decide
example : observe partialCase .legacy 7 = some [257,1,2] := by decide
/-- A normal raw LOCAL statement is not silently cleaned into old Source. -/
example : project (run eqCopy .legacy 9) = none := by rfl
/-- Halt projection exposes exactly the old Source halt/world, while the
separate preceding kernel control retains the partial target write. -/
example : project (run partialCase .legacy 6) =
    some (.error .timeout,(Solidity.Source.L0 env,partialCase.state.2)) := by rfl

def witness : Nonempty Case := ⟨capturedStatement⟩
example (c : Case) (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) :
    project (discard (Solidity.Yul.LocalCompareControl.eval c.op c.one c.two c.yesProof c.noProof pipeline)
      fuel (LocalState.ofClean (cleanLocals c.state,c.state.2))) =
      some ((Solidity.Source.execS (Solidity.Source.SemanticsExamples.G0 pipeline)
        Solidity.Source.SemanticsExamples.F0 fuel 0 none
        (Solidity.Source.RStmt.expr (R := []) (M := false) (k := ⟨false,false⟩)
          (.cond (.compare c.op c.left c.right) c.yes c.no)) (cleanLocals c.state)).run
            (Solidity.Source.L0 env,c.state.2)) :=
  compare_source_agrees c.op c.one c.two c.yesProof c.noProof
    (Solidity.Source.SemanticsExamples.G0 pipeline) Solidity.Source.SemanticsExamples.F0
    rfl fuel 0 none [] false ⟨false,false⟩ (cleanLocals c.state) c.state.2

#eval do
  for c in fixtures ++ [partialCase] do
    for pipeline in [Solidity.Roadmap.Pipeline.legacy,.viaIR] do
      for fuel in [0,1,2,3,4,5,6,7,9] do
        let extended := discard
          (Solidity.Yul.LocalCompareControl.eval c.op c.one c.two c.yesProof c.noProof pipeline)
          fuel (LocalState.ofClean (cleanLocals c.state,c.state.2))
        let actual := (Solidity.Source.execS (Solidity.Source.SemanticsExamples.G0 pipeline)
          Solidity.Source.SemanticsExamples.F0 fuel 0 none
          (Solidity.Source.RStmt.expr (R := []) (M := false) (k := ⟨false,false⟩)
            (.cond (.compare c.op c.left c.right) c.yes c.no)) (cleanLocals c.state)).run
              (Solidity.Source.L0 env,c.state.2)
        let some projected := project extended | throw (IO.userError "clean statement projection refused")
        match projected.1,actual.1 with
        | .error left,.error right =>
            unless left == right do throw (IO.userError "Source statement halt mismatch")
        | .ok (.normal left),.ok (.normal right) =>
            unless snapshot (LocalState.ofClean (left,c.state.2)) ==
                snapshot (LocalState.ofClean (right,c.state.2)) do
              throw (IO.userError "Source statement normal locals mismatch")
        | _,_ => throw (IO.userError "Source statement control mismatch")
  IO.println "LOCAL_EXPR_STATEMENT_PASS:126 actual clean Source.execS comparisons; raw/no-clean/partial-halt controls"

#check @Solidity.Yul.LocalExprStatement.bool_source_agrees
#check @Solidity.Yul.LocalExprStatement.compare_source_agrees
#print axioms Solidity.Yul.LocalExprStatement.compare_source_agrees
end Solidity.Yul.Checks.LocalExprStatement
