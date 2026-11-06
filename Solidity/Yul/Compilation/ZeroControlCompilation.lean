import Solidity.Yul.Compilation.LetControlCompilation
import Solidity.Yul.Compilation.ZeroLoopScope
/-! Original zero binder around actual recursive let/control compilation.
Reuses existing top-first prefix initialization and retirement; no alternative
source state, allocation layout, calling convention or admission rule. -/
namespace Solidity.Yul.Compilation.ZeroControlCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

inductive Compiled {c : Control} {n : Nat} (fuel : Nat) : Stmt [] [] c n → Type where
 | scope {fresh : Nat} {body : Stmt [] [] c (fresh+n)}
     (artifact : LetControlCompilation.Artifact fuel body) : Compiled fuel (.zero fresh body)

def Compiled.profile {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) : StmtWordP stmt :=
 Compiled.casesOn (motive := fun stmt _ => StmtWordP stmt) compiled
   (fun artifact => artifact.compiled.profile)

def Compiled.code {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) : Option (List Evm.Instr) :=
 Compiled.casesOn (motive := fun _ _ => Option (List Evm.Instr)) compiled
   (fun {fresh} {_body} artifact => do
     let begin ← WordMachine.selectCode (ZeroLoopScope.entry fresh)
     let finish ← WordMachine.selectCode (popPrefix fresh)
     pure (begin ++ artifact.code ++ finish))

/-- Actual original zero visitor delegates its exact extended-context body
to the existing recursive seq/if/let compiler, retaining its real refusals. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Compiled fuel stmt) := by
 apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
   match F,X with
   | [],[] => Option (Compiled fuel stmt)
   | _,_ => Unit) stmt
 case zero =>
   intro F X c n fresh body
   cases F <;> cases X
   · exact (LetControlCompilation.lower fuel body).map (fun artifact => Compiled.scope (fresh := fresh) artifact)
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

/-- Actual body completion closes the original zero binder at one more
source horizon, dropping exactly its fresh prefix. -/
theorem source_scope {c : Control} {n fresh fuel : Nat} {body : Stmt [] [] c (fresh+n)}
 (artifact : LetControlCompilation.Artifact fuel body) (horizon : Nat)
 (locals : Vector Scalar.Word n) (out : Vector Scalar.Word (fresh+n))
 (ran : evalStmt horizon .nil True.intro body artifact.compiled.profile
   (sourceLocals (Vector.replicate fresh (0 : Scalar.Word) ++ locals)) = some ⟨sourceLocals out,.normal⟩) :
 evalStmt (horizon+1) .nil True.intro (.zero fresh body) artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals (outerLocals out),.normal⟩ := by
 change Option.bind (evalStmt horizon .nil True.intro body artifact.compiled.profile
   (extendValues (fun _ : Fin fresh => word 0) (sourceLocals locals))) _ = _
 rw [←ZeroLoopScope.initial_values,ran]
 change some (⟨dropValues fresh (sourceLocals out),.normal⟩ : Outcome c n) = _
 rw [←ScopedStatements.locals_outer]

/-- A real completed zero scope derives initialized body execution and
exact retirement. Neither desired body contents nor a run is assumed. -/
theorem Artifact.source_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 rcases artifact with ⟨compiled,code,lowered⟩
 cases compiled with
 | @scope fresh bodyStmt body =>
   obtain ⟨begin,beginSelected,rest⟩ := Option.bind_eq_some_iff.mp lowered
   obtain ⟨finish,finishSelected,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   cases horizon with
   | zero => cases ran
   | succ horizon =>
     change Option.bind (evalStmt horizon .nil True.intro bodyStmt body.compiled.profile
       (extendValues (fun _ : Fin fresh => word 0) (sourceLocals locals))) _ = some result at ran
     rw [←ZeroLoopScope.initial_values] at ran
     obtain ⟨middle,bodySource,remaining⟩ := Option.bind_eq_some_iff.mp ran
     obtain ⟨out,same,bodyRun⟩ := body.source_to_model horizon
       (Vector.replicate fresh (0 : Scalar.Word) ++ locals) middle bodySource m caller
     subst middle
     have projected : result = ⟨sourceLocals (outerLocals out),.normal⟩ := by
       have same := (Option.some.inj remaining).symm
       rw [←ScopedStatements.locals_outer] at same
       exact same
     have entering := WordExecution.run (ZeroLoopScope.entry fresh) begin beginSelected locals.toList
       ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList) (pushPrefix_run _ _) m caller
     have bodyRun' : Evm.run body.code
       {m with stack := ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList).map coreWord++caller} =
       .ok {m with stack := out.toList.map coreWord++caller} 0 := by
       simpa only [Vector.toList_append] using bodyRun
     have exitScalar : Scalar.run (popPrefix fresh) out.toList = some (outerLocals out).toList := by
       simpa only [List.append_nil] using popFresh_run out []
     have exiting := WordExecution.run (popPrefix fresh) finish finishSelected out.toList
       (outerLocals out).toList exitScalar m caller
     refine ⟨outerLocals out,projected,?_⟩
     change Evm.run (begin ++ body.code ++ finish) {m with stack := locals.toList.map coreWord++caller} =
       .ok {m with stack := (outerLocals out).toList.map coreWord++caller} 0
     rw [List.append_assoc,Evm.run_append_ok entering,Evm.run_append_ok bodyRun']
     exact exiting

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

/-- info: 'Solidity.Yul.Compilation.ZeroControlCompilation.source_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_scope
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompilation.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompilation.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompilation.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower
end Solidity.Yul.Compilation.ZeroControlCompilation
