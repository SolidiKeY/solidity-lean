import Solidity.Yul.Compilation.LetScopeCompilation
import Solidity.Yul.Compilation.FramedBranch
/-! Recursive original seq/if traversal around actual let-scope compiler
artifacts. Existing intrinsic syntax, source profiles and target branch tails
are reused; this is neither another source AST nor an admission change. -/
namespace Solidity.Yul.Compilation.LetControlCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

inductive Compiled {c : Control} {n : Nat} : Nat → Stmt [] [] c n → Type where
 | scope {fuel : Nat} {stmt : Stmt [] [] c n}
     (artifact : LetScopeCompilation.Artifact fuel stmt) : Compiled fuel stmt
 | seq {fuel : Nat} {a b : Stmt [] [] c n}
     (left : Compiled fuel a) (right : Compiled fuel b) : Compiled (fuel+1) (.seq a b)
 | branch {fuel : Nat} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
     (condition : ProducerExpressions.Compiled fuel test) (arm : Compiled fuel body) :
     Compiled (fuel+1) (.if_ test body)

def Compiled.profile {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) : StmtWordP stmt := by
 apply Compiled.casesOn (motive := fun _ stmt _ => StmtWordP stmt) compiled
 case scope => intro fuel stmt artifact; exact artifact.compiled.profile
 case seq => intro fuel a b left right; exact ⟨left.profile,right.profile⟩
 case branch => intro fuel test body condition arm; exact ⟨condition.profile,arm.profile⟩
termination_by structural compiled

def Compiled.code {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) : Option (List Evm.Instr) := by
 apply Compiled.casesOn (motive := fun _ _ _ => Option (List Evm.Instr)) compiled
 case scope => intro fuel stmt artifact; exact some artifact.code
 case seq =>
   intro fuel a b left right
   exact do
     let a ← left.code
     let b ← right.code
     pure (a++b)
 case branch =>
   intro fuel test body condition arm
   exact do
     let p ← condition.lowered.code 0
     let q ← WordMachine.selectCode p
     let body ← arm.code
     pure (MachineControl.branchCode q body [])
termination_by structural compiled

/-- Actual original syntax visitor. Only seq/if recurse; leaves delegate to
the existing let compiler and retain all its real initializer/body refusals. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Compiled fuel stmt) :=
 match fuel with
 | 0 => none
 | fuel+1 => by
   apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
     match F,X with
     | [],[] => Option (Compiled (fuel+1) stmt)
     | _,_ => Unit) stmt
   case seq =>
     intro F X c n a b
     cases F <;> cases X
     · exact do
         let left ← compile fuel a
         let right ← compile fuel b
         pure (.seq left right)
     all_goals exact ()
   case if_ =>
     intro F X c n test body
     cases F <;> cases X
     · exact do
         let condition ← PureExpressions.compile fuel test
         let arm ← compile fuel body
         pure (.branch condition arm)
     all_goals exact ()
   all_goals intro F X; cases F <;> cases X <;> intros <;>
     first | exact (LetScopeCompilation.lower (fuel+1) _).map Compiled.scope | exact ()
termination_by structural fuel

structure Artifact {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) where
 compiled : Compiled fuel stmt
 code : List Evm.Instr
 lowered : compiled.code = some code

def lower {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Artifact fuel stmt) := do
 let compiled ← compile fuel stmt
 match lowered : compiled.code with
 | none => none
 | some code => some ⟨compiled,code,lowered⟩

/-- Actual source completion supplies each intermediate local vector and
normal flow before selected instruction concatenation is executed. No desired
child run or intermediate state is a caller premise. -/
theorem source_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) (code : List Evm.Instr) (lowered : compiled.code = some code)
 (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 induction compiled generalizing code horizon locals result with
 | scope artifact =>
   change some artifact.code = some code at lowered
   cases Option.some.inj lowered
   exact artifact.source_to_model horizon locals result ran m caller
 | seq left right ihLeft ihRight =>
   change (left.code).bind (fun a => (right.code).bind (fun b => some (a++b))) = some code at lowered
   obtain ⟨a,ha,rest⟩ := Option.bind_eq_some_iff.mp lowered
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   cases horizon with
   | zero => cases ran
   | succ horizon =>
     change Option.bind (evalStmt horizon .nil True.intro _ left.profile (sourceLocals locals)) _ = some result at ran
     obtain ⟨middle,first,remaining⟩ := Option.bind_eq_some_iff.mp ran
     obtain ⟨mid,same,firstRun⟩ := ihLeft a ha horizon locals middle first
     subst middle
     change evalStmt horizon .nil True.intro _ right.profile (sourceLocals mid) = some result at remaining
     obtain ⟨out,same,lastRun⟩ := ihRight b hb horizon mid result remaining
     refine ⟨out,same,?_⟩
     rw [Evm.run_append_ok firstRun]
     exact lastRun

 | branch condition arm ih =>
   change (condition.lowered.code 0).bind (fun p => (WordMachine.selectCode p).bind (fun q =>
     (arm.code).bind (fun body => some (MachineControl.branchCode q body [])))) = some code at lowered
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp lowered
   obtain ⟨q,sq,rest⟩ := Option.bind_eq_some_iff.mp rest
   obtain ⟨body,hb,same⟩ := Option.bind_eq_some_iff.mp rest
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
       else evalStmt horizon .nil True.intro _ arm.profile (sourceLocals locals)) = some result at remaining
     by_cases zero : condition.value locals = 0
     · have zn : (condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
       rw [if_pos zn] at remaining
       refine ⟨locals,(Option.some.inj remaining).symm,?_⟩
       rw [MachineControl.branchCode,Evm.run_append_ok testedTarget,zero]
       change Evm.exec body body.length {m with stack := locals.toList.map coreWord++caller} = _
       exact Evm.exec_length body _
     · have nz : (condition.value locals).toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
       rw [if_neg nz] at remaining
       obtain ⟨out,same,armRun⟩ := ih body hb horizon locals result remaining
       refine ⟨out,same,?_⟩
       rw [MachineControl.branchCode,Evm.run_append_ok testedTarget]
       rw [FramedBranch.nonzero_tail (condition.value locals) body []
         {m with stack := locals.toList.map coreWord++caller} zero]
       exact armRun

/-- Concrete artifact transport with no stored execution or simulation law. -/
theorem Artifact.source_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 :=
 LetControlCompilation.source_to_model artifact.compiled artifact.code artifact.lowered horizon locals result ran m caller

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

/-- info: 'Solidity.Yul.Compilation.LetControlCompilation.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_to_model
/-- info: 'Solidity.Yul.Compilation.LetControlCompilation.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
/-- info: 'Solidity.Yul.Compilation.LetControlCompilation.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
/-- info: 'Solidity.Yul.Compilation.LetControlCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.LetControlCompilation.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower
end Solidity.Yul.Compilation.LetControlCompilation
