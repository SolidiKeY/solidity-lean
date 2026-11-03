import Solidity.Yul.LocalBoolAgreement
import Solidity.Yul.Checks.LocalBlock
import Solidity.Source.SemanticsExamples

namespace Solidity.Yul.Checks.LocalBoolExpr
open Solidity.Yul.LocalBoolExpr

abbrev ctx := LocalBlock.ctx
abbrev env := LocalBlock.env
def expr : Solidity.Source.RExpr env ctx.tys .bool :=
  .assign (.local .here) (.unary .not (.local .here))
def supported : Supported env ctx.tys expr := .assign .here (.not (.local .here))
def dirty : LocalState env ctx.tys :=
  (LocalBlock.initial.1.writeScalar .here (LocalOperations.boolShape env) (word 2),LocalBlock.initial.2)
def cleanInitial : Solidity.Source.Locals env.layout ctx.tys × Solidity.Source.St env :=
  (LocalBlock.locals,LocalBlock.initial.2)

def wordResult (result : Solidity.Source.R (LocalValue env .bool)) : Option Nat :=
  match result with
  | .ok value => some (LocalOperations.scalarWord value (LocalOperations.boolShape env)).val
  | .error _ => none
def haltResult (result : Solidity.Source.R (LocalValue env .bool)) : Option Solidity.Source.Halt :=
  match result with
  | .ok _ => none
  | .error halt => some halt

example : wordResult (eval supported 3 dirty).1 = some 0 := by decide
example : haltResult (eval supported 0 dirty).1 = some .timeout := by decide
example : haltResult (eval supported 1 dirty).1 = some .timeout := by decide
example : haltResult (eval supported 2 dirty).1 = some .timeout := by decide
example : haltResult (eval supported 3 dirty).1 = none := by decide
example : LocalBlock.snapshot (eval supported 3 dirty).2 =
    [0,4660,2309737967,1,22136,16909060,171*2^248] := by decide
example : LocalBlock.snapshot (eval supported 2 dirty).2 =
    [2,4660,2309737967,1,22136,16909060,171*2^248] := by decide
example (fuel : Nat) : (eval supported fuel dirty).2.2 = dirty.2 := world supported fuel dirty
example (fuel : Nat) (pipeline : Solidity.Roadmap.Pipeline) :
    eval supported fuel (LocalState.ofClean cleanInitial) =
      cleanOutcome ((Solidity.Source.evalE (Solidity.Source.SemanticsExamples.G0 pipeline)
        Solidity.Source.SemanticsExamples.F0 fuel expr).run cleanInitial) :=
  source_agrees supported _ _ fuel cleanInitial

example : ¬ Nonempty (Supported env ctx.tys (.unary .bitNot (.bool true))) := by
  rintro ⟨proof⟩
  cases proof
example : ¬ Nonempty (Supported env ctx.tys (.binary .and (.bool true) (.bool false))) := by
  rintro ⟨proof⟩
  cases proof
example : ¬ Nonempty (Solidity.Source.Idx [] .bool) := by
  rintro ⟨index⟩
  cases index

def copyCtx : Solidity.Source.Ctx := {env:=env,scope:=none,locals:=[("a",.bool),("b",.bool)]}
def rawPair : LocalState env copyCtx.tys :=
  ((.scalar (LocalOperations.boolShape env) (word 2),
    (.scalar (LocalOperations.boolShape env) (word 4),())),Solidity.Source.St.init env)
def copyExpr : Solidity.Source.RExpr env copyCtx.tys .bool :=
  .assign (.local .here) (.local (.there .here))
def copyProof : Supported env copyCtx.tys copyExpr := .assign .here (.local (.there .here))
example : wordResult (eval copyProof 2 rawPair).1 = some 4 := by decide
example : ((eval copyProof 2 rawPair).2.1.get .here).scalar? = some (word 4) := by decide
example : ((eval copyProof 2 rawPair).2.1.get (.there .here)).scalar? = some (word 4) := by decide
example : ((eval copyProof 2 rawPair).2.1.get .here).clean? = none := rfl

def readBack : Stmt [] (localExternalTypes ctx) ⟨false,false⟩ 0 :=
  LocalBlock.assign LocalBlock.small (.builtin (.pure .add)
    (Fin.cases (.external LocalBlock.small.readRef)
      (Fin.cases (.external LocalBlock.flag.readRef) Fin.elim0)))
def readBackPolicy : Policy.StmtP .A readBack := (Policy.stmt_iff .A readBack).mp rfl

def certWitness : Nonempty (Supported env ctx.tys expr) := ⟨supported⟩
def stateWitness : Nonempty (LocalState env ctx.tys) := ⟨dirty⟩
def globWitness : Nonempty (Solidity.Source.Glob env) := ⟨Solidity.Source.SemanticsExamples.G0 .legacy⟩

#eval do
  for pipeline in [Solidity.Roadmap.Pipeline.legacy,.viaIR] do
    for fuel in [0,1,2,3,4,8] do
      let actual := eval supported fuel (LocalState.ofClean cleanInitial)
      let reference := cleanOutcome ((Solidity.Source.evalE
        (Solidity.Source.SemanticsExamples.G0 pipeline) Solidity.Source.SemanticsExamples.F0
          fuel expr).run cleanInitial)
      unless wordResult actual.1 == wordResult reference.1 &&
          haltResult actual.1 == haltResult reference.1 &&
          LocalBlock.snapshot actual.2 == LocalBlock.snapshot reference.2 do
        throw (IO.userError "actual Source boolean clean-run comparison failed")
  let some before := runLocalBlock ctx LocalBlock.code LocalBlock.policy 32 LocalBlock.initial |
    throw (IO.userError "first actual Yul block exhausted original horizon32")
  let (result,middle) := eval supported 3 before.state
  unless wordResult result == some 0 &&
      LocalBlock.snapshot middle == [0,2^256-1,2309737967,257,22136,2^256-1,171*2^248] do
    throw (IO.userError "Yul to actual Source expression preserved dirty-neighbor regression failed")
  let some after := runLocalBlock ctx readBack readBackPolicy 8 middle |
    throw (IO.userError "second actual Yul block exhausted horizon8")
  unless LocalBlock.snapshot after.state == LocalBlock.snapshot middle && after.flow.isNormal do
    throw (IO.userError "actual Source expression to Yul raw-read regression failed")
  IO.println "LOCAL_BOOL_EXPR_COMPILED_PASS:12 actual Source horizon/profile comparisons; Yul/Source/Yul dirty-neighbor combination"

#check @Solidity.Yul.LocalBoolExpr.source_agrees
#print axioms Solidity.Yul.LocalBoolExpr.source_agrees
#print axioms Solidity.Yul.LocalBoolExpr.world
end Solidity.Yul.Checks.LocalBoolExpr
