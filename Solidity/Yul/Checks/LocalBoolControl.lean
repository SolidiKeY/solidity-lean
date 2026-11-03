import Solidity.Yul.LocalBoolControlAgreement
import Solidity.Yul.LocalBoolControlEvidence
import Solidity.Yul.Checks.LocalBoolExpr

namespace Solidity.Yul.Checks.LocalBoolControl
open Solidity.Yul.LocalBoolControl
def env : Solidity.Source.Env := ⟨[]⟩
def ctx : Solidity.Source.Ctx :=
  {env:=env,scope:=none,locals:=[("x",.bool),("y",.bool),("w",.bool)]}
def x : Solidity.Source.Idx ctx.tys .bool := .here
def y : Solidity.Source.Idx ctx.tys .bool := .there .here
def w : Solidity.Source.Idx ctx.tys .bool := .there (.there .here)
def read (index : Solidity.Source.Idx ctx.tys .bool) :
    Supported env ctx.tys (.local index) := .base (.local index)
def literal (value : Bool) : Supported env ctx.tys (.bool value) := .base (.literal value)
def initial (a b c : Nat) : LocalState env ctx.tys :=
  ((.scalar (LocalOperations.boolShape env) (word a),
    (.scalar (LocalOperations.boolShape env) (word b),
      (.scalar (LocalOperations.boolShape env) (word c),()))),Solidity.Source.St.init env)

structure Case where
  name : String
  state : LocalState env ctx.tys
  expr : Solidity.Source.RExpr env ctx.tys .bool
  proof : Supported env ctx.tys expr
  includeY : Bool := false

def andRaw : Case := ⟨"andRaw",initial 2 4 8,_,.and (read x) (read y),false⟩
def andFalse : Case := ⟨"andFalse",initial 0 4 8,_,.and (read x) (read y),false⟩
def orRaw : Case := ⟨"orRaw",initial 2 4 8,_,.or (read x) (read y),false⟩
def orFalse : Case := ⟨"orFalse",initial 0 4 8,_,.or (read x) (read y),false⟩
def andAssign : Case :=
  ⟨"andAssign",initial 2 4 8,_,.and (read x) (.assign y (literal false)),true⟩
def orAssign : Case :=
  ⟨"orAssign",initial 2 4 8,_,.or (read x) (.assign y (literal false)),true⟩
def conditionalRaw : Case :=
  ⟨"conditionalRaw",initial 2 4 8,_,.cond (read x) (read y) (read w),false⟩
def conditionalAssign : Case :=
  ⟨"conditionalAssign",initial 0 4 8,_,
    .cond (read x) (.assign y (literal false)) (.assign y (literal true)),true⟩
def fixtures : List Case :=
  [andRaw,andFalse,orRaw,orFalse,andAssign,orAssign,conditionalRaw,conditionalAssign]

def wordValue (value : LocalValue env .bool) : Nat :=
  (LocalOperations.scalarWord value (LocalOperations.boolShape env)).val
def observe (c : Case) (fuel : Nat) : Option (List Nat) :=
  let (result,next) := eval c.proof fuel c.state
  match result with
  | .error _ => none
  | .ok value => some ([wordValue value] ++ if c.includeY then [wordValue (next.1.get y)] else [])

example : fixtures.map (fun c => observe c 8) =
    ([some [4],some [0],some [2],some [4],some [0,0],some [2,4],some [4],some [1,1]]) := by decide
example : observe orAssign 2 = some [2,4] := by decide
example : observe andAssign 2 = none := by decide
example : observe andAssign 3 = some [0,0] := by decide
example : observe {orAssign with state:=initial (2^256-1) 4 8} 2 = some [2^256-1,4] := by decide
example : observe {conditionalAssign with state:=initial 2 4 8} 3 = some [0,0] := by decide
example : observe conditionalAssign 3 = some [1,1] := by decide

/-- Left assignment completes before selected RHS exhausts its horizon. -/
def prefixExpr : Solidity.Source.RExpr env ctx.tys .bool :=
  .binary .and (.assign (.local x) (.bool true)) (.unary .not (.unary .not (.bool false)))
def prefixProof : Supported env ctx.tys prefixExpr :=
  .and (.assign x (literal true)) (.not (.not (literal false)))
def prefixState := initial 0 0 0
example : LocalBoolExpr.haltResult (eval prefixProof 3 prefixState).1 = some .timeout := by decide
example : wordValue ((eval prefixProof 3 prefixState).2.1.get x) = 1 := by decide
example : wordValue (prefixState.1.get x) = 0 := by decide
example : LocalBoolExpr.wordResult (eval prefixProof 4 prefixState).1 = some 0 := by decide
example (fuel : Nat) : (eval prefixProof fuel prefixState).2.2 = prefixState.2 :=
  world prefixProof fuel prefixState

def baseNot : Supported env ctx.tys (.unary .not (.local x)) := .base (.not (.local x))
def controlNot : Supported env ctx.tys (.unary .not (.local x)) := .not (read x)
example : baseNot ≠ controlNot := by intro impossible; cases impossible
example (fuel : Nat) (state : LocalState env ctx.tys) :
    eval baseNot fuel state = eval controlNot fuel state :=
  evidence_independent baseNot controlNot fuel state
example : ¬ Nonempty (Supported env ctx.tys (.compare .eq (.bool true) (.bool false))) := by
  rintro ⟨proof⟩
  cases proof with
  | base impossible => cases impossible

def cleanLocals (state : LocalState env ctx.tys) : Solidity.Source.Locals env.layout ctx.tys :=
  .cons (.bool (Solidity.Yul.LocalBoolControl.truth (state.1.get x))) (.cons (.bool (Solidity.Yul.LocalBoolControl.truth (state.1.get y)))
    (.cons (.bool (Solidity.Yul.LocalBoolControl.truth (state.1.get w))) .nil))
def snapshot (state : LocalState env ctx.tys) : List Nat :=
  [wordValue (state.1.get x),wordValue (state.1.get y),wordValue (state.1.get w)]
example (fuel : Nat) (pipeline : Solidity.Roadmap.Pipeline) :
    eval prefixProof fuel (LocalState.ofClean (cleanLocals prefixState,prefixState.2)) =
      Solidity.Yul.LocalBoolExpr.cleanOutcome ((Solidity.Source.evalE
        (Solidity.Source.SemanticsExamples.G0 pipeline) Solidity.Source.SemanticsExamples.F0 fuel prefixExpr).run
          (cleanLocals prefixState,prefixState.2)) := source_agrees prefixProof _ _ fuel _

def certWitness : Nonempty (Supported env ctx.tys prefixExpr) := ⟨prefixProof⟩
def caseWitness : Nonempty Case := ⟨orAssign⟩

#eval do
  for c in fixtures do
    for pipeline in [Solidity.Roadmap.Pipeline.legacy,.viaIR] do
      for fuel in [0,1,2,3,4,8] do
        let clean := (cleanLocals c.state,c.state.2)
        let actual := eval c.proof fuel (LocalState.ofClean clean)
        let reference := Solidity.Yul.LocalBoolExpr.cleanOutcome
          ((Solidity.Source.evalE (Solidity.Source.SemanticsExamples.G0 pipeline)
            Solidity.Source.SemanticsExamples.F0 fuel c.expr).run clean)
        unless LocalBoolExpr.wordResult actual.1 == LocalBoolExpr.wordResult reference.1 &&
            LocalBoolExpr.haltResult actual.1 == LocalBoolExpr.haltResult reference.1 &&
            snapshot actual.2 == snapshot reference.2 do
          throw (IO.userError "actual clean Source control comparison changed")
  let timedOut := eval prefixProof 3 prefixState
  unless LocalBoolExpr.haltResult timedOut.1 == some Solidity.Source.Halt.timeout && snapshot timedOut.2 == [1,0,0] do
    throw (IO.userError "selected RHS timeout lost completed left assignment")
  let expected := [[4],[0],[2],[4],[0,0],[2,4],[4],[1,1]]
  unless fixtures.map (fun c => observe c 8) == expected.map some do
    throw (IO.userError "compiled dirty Source control fixture changed")
  IO.println "LOCAL_BOOL_CONTROL_COMPILED_PASS:96 actual clean Source comparisons; dirty raw selection/skipped effects/partial timeout controls"

#check @Solidity.Yul.LocalBoolControl.source_agrees
#check @Solidity.Yul.LocalBoolControl.evidence_independent
#print axioms Solidity.Yul.LocalBoolControl.source_agrees
#print axioms Solidity.Yul.LocalBoolControl.evidence_independent
end Solidity.Yul.Checks.LocalBoolControl
