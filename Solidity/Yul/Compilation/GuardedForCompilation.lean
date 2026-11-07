import Solidity.Yul.Compilation.GuardedForCompletion
/-! Concrete original-AST if/for visitor using actual existing expression and
loop visitors. The evidence is not source syntax and stores no assumed run law.
Component fuel is distinct from the existential whole-source horizon. -/
namespace Solidity.Yul.Compilation.GuardedForCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

inductive Compiled {c : Control} {n : Nat} (fuel depth : Nat) : Stmt [] [] c n → Type where
 | branch {test : Expr [] [] n 1} {body : Stmt [] [] c n}
     (condition : ProducerExpressions.Compiled fuel test)
     (loop : ForCompilation.Artifact fuel body depth) : Compiled fuel depth (.if_ test body)

def Compiled.profile {c n fuel depth} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel depth stmt) : StmtWordP stmt :=
 Compiled.casesOn (motive := fun stmt _ => StmtWordP stmt) compiled
   (fun condition loop => ⟨condition.profile,loop.compiled.profile⟩)

def Compiled.code {c n fuel depth} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel depth stmt) : Option (List Evm.Instr) :=
 Compiled.casesOn (motive := fun _ _ => Option (List Evm.Instr)) compiled
   (fun condition loop => GuardedFor.lower condition loop)

/-- This visitor recognizes the original if constructor and delegates its
actual body to ForCompilation.lower, not a manually assumed body producer.
All other top-level forms refuse locally, without changing admission. -/
def compile {c : Control} {n : Nat} (fuel depth : Nat) (stmt : Stmt [] [] c n) :
 Option (Compiled fuel depth stmt) := by
 apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
   match F,X with
   | [],[] => Option (Compiled fuel depth stmt)
   | _,_ => Unit) stmt
 case if_ =>
   intro F X c n test body
   cases F <;> cases X
   · exact do
       let condition ← PureExpressions.compile fuel test
       let loop ← ForCompilation.lower fuel body depth
       pure (.branch condition loop)
   all_goals exact ()
 all_goals intro F X; cases F <;> cases X <;> intros <;> first | exact none | exact ()

/-- Exact selected output and real compiler evidence, without any assumed
execution theorem. Generic certified records do not assert visitor origin;
actual lower constructs them through the source visitor above. -/
structure Artifact {c : Control} {n : Nat} (fuel depth : Nat) (stmt : Stmt [] [] c n) where
 compiled : Compiled fuel depth stmt
 code : List Evm.Instr
 lowered : compiled.code = some code

def lower {c : Control} {n : Nat} (fuel depth : Nat) (stmt : Stmt [] [] c n) :
 Option (Artifact fuel depth stmt) := do
 let compiled ← compile fuel depth stmt
 match lowered : compiled.code with
 | none => none
 | some code => some ⟨compiled,code,lowered⟩

/-- Existing concrete compiler proofs close normal-success equivalence for
this artifact; no new assumed producer or stored simulation law is used. -/
theorem Artifact.completion_iff {c : Control} {n fuel depth : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel depth stmt) (locals out : Vector Scalar.Word n)
 (newer : Vector Scalar.Word depth) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
   .ok {m with stack := (newer.toList++out.toList).map coreWord++caller} 0 := by
 rcases artifact with ⟨compiled,code,lowered⟩
 cases compiled with
 | branch condition loop =>
   exact GuardedForCompletion.completion_iff condition loop code lowered locals out newer m caller

/-- Unknown successful output/pending state determines a real original source
horizon and exact normal final words and unchanged caller/machine frame. -/
theorem Artifact.reflected {c : Control} {n fuel depth : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel depth stmt) (locals : Vector Scalar.Word n)
 (newer : Vector Scalar.Word depth) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := (newer.toList++locals.toList).map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧
 final = {m with stack := (newer.toList++out.toList).map coreWord++caller} := by
 rcases artifact with ⟨compiled,code,lowered⟩
 cases compiled with
 | branch condition loop =>
   exact GuardedForCompletion.model_to_source condition loop code lowered locals newer m final caller skip ran

/-- info: 'Solidity.Yul.Compilation.GuardedForCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.GuardedForCompilation.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower
/-- info: 'Solidity.Yul.Compilation.GuardedForCompilation.Artifact.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.completion_iff
/-- info: 'Solidity.Yul.Compilation.GuardedForCompilation.Artifact.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.reflected
end Solidity.Yul.Compilation.GuardedForCompilation
