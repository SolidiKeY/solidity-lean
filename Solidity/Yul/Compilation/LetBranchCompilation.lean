import Solidity.Yul.Compilation.LetSequenceCompilation
import Solidity.Yul.Compilation.FramedBranch
/-! Actual original if visitor around existing compiled let sequences. Raw
word conditions and existing branch tails are reused, not a new control AST,
source state, admission rule or native-PC convention. -/
namespace Solidity.Yul.Compilation.LetBranchCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

inductive Compiled {c : Control} {n : Nat} (fuel : Nat) : Stmt [] [] c n → Type where
 | branch {test : Expr [] [] n 1} {body : Stmt [] [] c n}
     (condition : ProducerExpressions.Compiled fuel test)
     (arm : LetSequenceCompilation.Artifact fuel body) : Compiled fuel (.if_ test body)

def Compiled.profile {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) : StmtWordP stmt :=
 Compiled.casesOn (motive := fun stmt _ => StmtWordP stmt) compiled
   (fun condition arm => ⟨condition.profile,arm.compiled.profile⟩)

def Compiled.code {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) : Option (List Evm.Instr) :=
 Compiled.casesOn (motive := fun _ _ => Option (List Evm.Instr)) compiled
   (fun condition arm => do
     let p ← condition.lowered.code 0
     let q ← WordMachine.selectCode p
     pure (MachineControl.branchCode q arm.code []))

/-- Visit the original if, compile its actual condition and actual arm.
Current arm domain is the existing let-sequence compiler, without admission
or ordinary-statement fallback changes. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Compiled fuel stmt) := by
 apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
   match F,X with
   | [],[] => Option (Compiled fuel stmt)
   | _,_ => Unit) stmt
 case if_ =>
   intro F X c n test body
   cases F <;> cases X
   · exact do
       let condition ← PureExpressions.compile fuel test
       let arm ← LetSequenceCompilation.lower fuel body
       pure (.branch condition arm)
   all_goals exact ()
 all_goals intro F X; cases F <;> cases X <;> intros <;> first | exact none | exact ()

structure Artifact {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) where
 compiled : Compiled fuel stmt
 code : List Evm.Instr
 lowered : compiled.code = some code

def lower {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Artifact fuel stmt) := do
 let compiled ← compile fuel stmt
 match lowered : compiled.code with
 | none => none
 | some code => some ⟨compiled,code,lowered⟩

/-- Actual completed source evaluation determines the full condition word
and only the taken arm's run. No favourable untaken execution is required. -/
theorem Artifact.source_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 rcases artifact with ⟨compiled,code,lowered⟩
 cases compiled with
 | branch condition arm =>
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp lowered
   obtain ⟨q,sq,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   have testedTarget : Evm.run q {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} 0 := by
     simpa only [Vector.toList_empty,List.nil_append] using
       WordExecution.loweredExpr_machine condition.lowered 0 p q hp sq locals #v[] m caller
   cases horizon with
   | zero => cases ran
   | succ horizon =>
     change Option.bind (evalExpr horizon .nil True.intro _ condition.profile (sourceLocals locals)) _ = some result at ran
     obtain ⟨values,tested,remaining⟩ := Option.bind_eq_some_iff.mp ran
     have same := evalExpr_completed_unique .nil True.intro _ condition.profile (sourceLocals locals)
       tested (condition.source locals)
     subst values
     change (if (condition.value locals).toNat = 0 then
       some (⟨sourceLocals locals,.normal⟩ : Outcome _ _)
       else evalStmt horizon .nil True.intro _ arm.compiled.profile (sourceLocals locals)) = some result at remaining
     by_cases zero : condition.value locals = 0
     · have zn : (condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
       rw [if_pos zn] at remaining
       refine ⟨locals,(Option.some.inj remaining).symm,?_⟩
       change Evm.run (MachineControl.branchCode q arm.code [])
         {m with stack := locals.toList.map coreWord++caller} = _
       rw [MachineControl.branchCode,Evm.run_append_ok testedTarget,zero]
       change Evm.exec arm.code arm.code.length {m with stack := locals.toList.map coreWord++caller} = _
       exact Evm.exec_length arm.code _
     · have nz : (condition.value locals).toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
       rw [if_neg nz] at remaining
       obtain ⟨out,same,armRun⟩ := arm.source_to_model horizon locals result remaining m caller
       refine ⟨out,same,?_⟩
       change Evm.run (MachineControl.branchCode q arm.code [])
         {m with stack := locals.toList.map coreWord++caller} = _
       rw [MachineControl.branchCode,Evm.run_append_ok testedTarget]
       rw [FramedBranch.nonzero_tail (condition.value locals) arm.code []
         {m with stack := locals.toList.map coreWord++caller} zero]
       exact armRun

theorem Artifact.normal_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals out : Vector Scalar.Word n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 obtain ⟨actual,same,target⟩ := artifact.source_to_model horizon locals ⟨sourceLocals out,.normal⟩ ran m caller
 have equal : out = actual := SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 cases equal
 exact target

/-- info: 'Solidity.Yul.Compilation.LetBranchCompilation.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
/-- info: 'Solidity.Yul.Compilation.LetBranchCompilation.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
/-- info: 'Solidity.Yul.Compilation.LetBranchCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.LetBranchCompilation.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower
end Solidity.Yul.Compilation.LetBranchCompilation
