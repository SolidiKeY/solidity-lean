import Solidity.Yul.Compilation.InitializedLoopCompletion
import Solidity.Yul.Compilation.ScopedStatements
/-! Concrete visitor and selected artifact for an ACTUAL original intrinsic for.
Compiler evidence is indexed by the existing statement, not a replacement AST.
The fuel parameter bounds component certificates, not whole loop execution.
Only normal initializer/body/post components supported by existing visitors
are accepted here; admission, early control, Source/G24/native remain open. -/
namespace Solidity.Yul.Compilation.ForCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

/-- Compiler evidence for the original source constructor. No alternative
source syntax, evaluator, state or control convention is introduced. -/
inductive Compiled {c : Control} {n : Nat} (fuel : Nat) : Stmt [] [] c n → Type where
 | loop {pre : Stmt [] [] ⟨c.function,false⟩ n} {test : Expr [] [] n 1}
     {post : Stmt [] [] ⟨c.function,false⟩ n} {body : Stmt [] [] ⟨c.function,true⟩ n}
     (initializer : ProducerStatements.Compiled fuel pre)
     (condition : ProducerExpressions.Compiled fuel test)
     (step : ProducerStatements.Compiled fuel post)
     (work : ProducerStatements.Compiled fuel body) : Compiled fuel (.for_ pre test post body)

def Compiled.profile {c n fuel} {stmt : Stmt [] [] c n} (compiled : Compiled fuel stmt) : StmtWordP stmt := by
 exact Compiled.casesOn (motive := fun stmt _ => StmtWordP stmt) compiled
   (fun initializer condition step work =>
     ⟨initializer.profile,condition.profile,step.profile,work.profile⟩)

def Compiled.emit {c n fuel} {stmt : Stmt [] [] c n} (compiled : Compiled fuel stmt)
 (depth : Nat) : Option Backend.Block := by
 exact Compiled.casesOn (motive := fun _ _ => Option Backend.Block) compiled
   (fun initializer condition step work => SourceLoopInitializer.emit initializer condition step work depth)

/-- Actual constructor inspection calls the published original-AST component
visitors. Unsupported forms refuse locally; this does not change admission. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Compiled fuel stmt) := by
 apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
   match F,X with
   | [],[] => Option (Compiled fuel stmt)
   | _,_ => Unit) stmt
 case for_ =>
   intro F X c n pre test post body
   cases F <;> cases X
   · exact do
       let initializer ← ScopedStatements.compile fuel pre
       let condition ← PureExpressions.compile fuel test
       let step ← ScopedStatements.compile fuel post
       let work ← ScopedStatements.compile fuel body
       pure (.loop initializer condition step work)
   all_goals exact ()
 all_goals intro F X; cases F <;> cases X <;> intros <;> first | exact none | exact ()

/-- Selected artifact retains exact actual component, emission and selection
witnesses. The record contains no assumed execution/simulation law. -/
structure Artifact {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) (depth : Nat) where
 compiled : Compiled fuel stmt
 block : Backend.Block
 code : List Evm.Instr
 emitted : compiled.emit depth = some block
 selected : WordControl.blockCode block = some code

/-- Construct exact selected artifacts using real decisions; missing operand
accessibility/selection is refusal, never fabricated evidence. -/
def lower {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) (depth : Nat) :
 Option (Artifact fuel stmt depth) := do
 let compiled ← compile fuel stmt
 match emitted : compiled.emit depth with
 | none => none
 | some block =>
   match selected : WordControl.blockCode block with
   | none => none
   | some code => some ⟨compiled,block,code,emitted,selected⟩

/-- Exact normal-success transport for the returned artifact. Selection and
emission equations are produced by lower, rather than supplied as assumed
simulation premises. Actual normal component compiler laws remain stored. -/
theorem Artifact.completion_iff {c : Control} {n componentFuel depth : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact componentFuel stmt depth)
 (locals out : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ fuel, evalStmt fuel .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
   .ok {m with stack := (newer.toList++out.toList).map coreWord++caller} 0 := by
 rcases artifact with ⟨compiled,block,code,emitted,selected⟩
 cases compiled with
 | loop initializer condition step work =>
   exact InitializedLoopCompletion.completion_iff initializer condition step work depth block code
     emitted selected locals out newer m caller

/-- Any successful run of the returned selected artifact recovers an actual
original-source horizon, exact final words, pending zero and full frame. -/
theorem Artifact.reflected {c : Control} {n componentFuel depth : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact componentFuel stmt depth)
 (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := (newer.toList++locals.toList).map coreWord++caller} = .ok final skip) :
 ∃ (fuel : Nat) (out : Vector Scalar.Word n),
 evalStmt fuel .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧
 final = {m with stack := (newer.toList++out.toList).map coreWord++caller} := by
 rcases artifact with ⟨compiled,block,code,emitted,selected⟩
 cases compiled with
 | loop initializer condition step work =>
   exact InitializedLoopCompletion.model_to_source initializer condition step work depth block code
     emitted selected locals newer m final caller skip ran

/-- info: 'Solidity.Yul.Compilation.ForCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.ForCompilation.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower
/-- info: 'Solidity.Yul.Compilation.ForCompilation.Artifact.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.completion_iff
/-- info: 'Solidity.Yul.Compilation.ForCompilation.Artifact.reflected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Artifact.reflected
end Solidity.Yul.Compilation.ForCompilation
