import SolidityBridge.Yul.LiteralSelection
import Solidity.Yul.Compilation.NormalControl
/-! Source/model branch composition using real condition/arm instruction
certificates. No target run premise or new branch/source semantics is supplied.
Relative model skips are not native byte offsets, gas or general Source/G24. -/
namespace SolidityBridge.Yul.BranchModel
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation MachineAdapter

def branch {fuel n c} {test : Solidity.Yul.Expr [] [] n 1} {body : Solidity.Yul.Stmt [] [] c n}
    (condition : ProducerExpressions.Compiled fuel test) (arm : ProducerStatements.Compiled fuel body) :
    NormalControl.Derivation (fuel+1) (.if_ test body) := .branch condition (.scalar arm)

theorem source_model :
∀ {fuel n : Nat} {c : Solidity.Yul.Control} {test : Solidity.Yul.Expr [] [] n 1}
    {body : Solidity.Yul.Stmt [] [] c n}
    (condition : Solidity.Yul.Compilation.ProducerExpressions.Compiled fuel test)
    (arm : Solidity.Yul.Compilation.ProducerStatements.Compiled fuel body)
    (cc yes : List Solidity.Evm.Instr)
    (ccCert : SolidityBridge.Yul.SelectionSequence.Certificates cc)
    (yesCert : SolidityBridge.Yul.SelectionSequence.Certificates yes),
    condition.lowered.code 0 = some (SolidityBridge.Yul.SelectionSequence.emit cc ccCert) →
    arm.lowered.code 0 = some (SolidityBridge.Yul.SelectionSequence.emit yes yesCert) →
    ∀ (locals : Vector Solidity.Backend.Scalar.Word n) (tail : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack (locals.toList ++ tail) →
    Solidity.Yul.Closed.evalStmt (fuel+1) .nil True.intro (.if_ test body)
      (SolidityBridge.Yul.BranchModel.branch condition arm).profile
      (Solidity.Yul.Compilation.ProducerExpressions.sourceLocals locals) =
      some ⟨Solidity.Yul.Compilation.ProducerExpressions.sourceLocals
        ((SolidityBridge.Yul.BranchModel.branch condition arm).update locals),.normal⟩ ∧
    Solidity.Evm.run (Solidity.Yul.Compilation.MachineControl.branchCode cc yes []) m =
      .ok {m with stack := Solidity.Backend.Selection.irStack (((SolidityBridge.Yul.BranchModel.branch condition arm).update locals).toList ++ tail)} 0 := by
  intro fuel n c test body condition arm cc yes ccCert yesCert hc hy locals tail m represented
  have scalar := condition.lowered.correct 0 (SelectionSequence.emit cc ccCert) hc locals #v[] tail
  change Scalar.run (SelectionSequence.emit cc ccCert) (locals.toList ++ tail) =
    some (condition.value locals :: (locals.toList ++ tail)) at scalar
  have conditionRun := SelectionSequence.execute cc ccCert (locals.toList ++ tail) m represented
  rw [scalar] at conditionRun
  change Evm.run cc m = .ok {m with stack := irStack (condition.value locals :: (locals.toList ++ tail))} 0 at conditionRun
  have mapped : irStack (condition.value locals :: (locals.toList ++ tail)) =
      coreWord (condition.value locals) :: m.stack := by
    calc
      irStack (condition.value locals :: (locals.toList ++ tail)) =
          (condition.value locals :: (locals.toList ++ tail)).map coreWord := ArithmeticSelection.irStack_words _
      _ = coreWord (condition.value locals) :: m.stack :=
        congrArg (List.cons (coreWord (condition.value locals)))
          ((ArithmeticSelection.irStack_words _).symm.trans represented.symm)
  rw [mapped] at conditionRun
  have armRun := (WriteSelection.statement_model arm yes yesCert hy locals tail m represented).2
  have law := MachineControl.branchCode_run
    ⟨(condition.value locals).toNat,(condition.value locals).isLt⟩ cc yes [] m
    {m with stack := irStack ((arm.update locals).toList ++ tail)} m
    conditionRun armRun (by rfl)
  refine ⟨(branch condition arm).source locals,?_⟩
  change Evm.run (MachineControl.branchCode cc yes []) m =
    .ok {m with stack := irStack ((if condition.value locals = 0 then locals else arm.update locals).toList ++ tail)} 0
  have truth : (condition.value locals).toNat=0 ↔ condition.value locals=0 :=
    ⟨fun h => BitVec.eq_of_toNat_eq h,fun h => congrArg BitVec.toNat h⟩
  by_cases zero : condition.value locals=0
  · simpa only [truth,zero,ite_true,←represented] using law
  · simpa only [truth,zero,ite_false] using law

def test : Solidity.Yul.Expr [] [] 2 1 := .local 0
def body : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .assign (fun _ : Fin 1 => .local 1)
    (.builtin (.pure .add) (Fin.cases (.local 1) (fun _ => .literal (Solidity.Yul.word 1))))
def condition := (PureExpressions.compile 3 test).get (by rfl)
def arm := (PureStatements.compile 3 body).get (by rfl)
def compiled := (NormalControl.compile 4 (Solidity.Yul.Stmt.if_ test body)).get (by rfl)
def conditionIR : List Evm.Instr := [.dup 1]
def armIR : List Evm.Instr := [.push (coreWord 1),.dup 3,.add,.swap 2,.pop]
def conditionCertificates : SelectionSequence.Certificates conditionIR :=
  fun i member => (LiteralSelection.select i).get (by
    simp only [conditionIR,List.mem_singleton] at member
    subst i
    rfl)
def armCertificates : SelectionSequence.Certificates armIR :=
  fun i member => (LiteralSelection.select i).get (by
    simp only [armIR,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same | same | same | same <;> subst i <;> rfl)
def code := MachineControl.branchCode conditionIR armIR []

/-- Concrete original compiler instance; no child-code or run premise remains. -/
abbrev example_model := source_model condition arm conditionIR armIR conditionCertificates armCertificates (by rfl) (by rfl)
end SolidityBridge.Yul.BranchModel
