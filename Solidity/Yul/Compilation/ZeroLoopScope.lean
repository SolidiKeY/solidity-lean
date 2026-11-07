import Solidity.Yul.Compilation.LoopControlCompilation
import Solidity.Yul.Compilation.ScopedStatements
/-! Source zero binders around actual structured-loop body artifacts. The
existing top-first prefix operations and original source context are reused.
Body depth is explicitly zero: no invented V12 frame convention or memory view.
Source/G24/native/capacity adequacy remains a separate obligation. -/
namespace Solidity.Yul.Compilation.ZeroLoopScope
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

def entry (fresh : Nat) : Backend.Program :=
 pushPrefix (Vector.replicate fresh (0 : Scalar.Word)).toList

def lower (fresh : Nat) {c : Control} {n fuel : Nat} {body : Stmt [] [] c (fresh+n)}
 (artifact : LoopControlCompilation.Artifact fuel body 0) : Option (List Evm.Instr) := do
 let begin ← WordMachine.selectCode (entry fresh)
 let finish ← WordMachine.selectCode (popPrefix fresh)
 pure (begin ++ artifact.code ++ finish)

/-- Reuse the original producer context extension; no alternate layout. -/
theorem initial_values {n fresh : Nat} (locals : Vector Scalar.Word n) :
 sourceLocals (Vector.replicate fresh (0 : Scalar.Word) ++ locals) =
 extendValues (fun _ : Fin fresh => word 0) (sourceLocals locals) := by
 have zeros : sourceLocals (Vector.replicate fresh (0 : Scalar.Word)) = (fun _ : Fin fresh => word 0) := by
   funext i
   simp only [sourceLocals,Vector.getElem_replicate]
   rfl
 rw [ScopedStatements.locals_append,zeros]

/-- Actual body completion closes the original zero binder at one more
source horizon, dropping exactly its fresh prefix. -/
theorem source_scope {c : Control} {n fresh fuel : Nat} {body : Stmt [] [] c (fresh+n)}
 (artifact : LoopControlCompilation.Artifact fuel body 0) (horizon : Nat)
 (locals : Vector Scalar.Word n) (out : Vector Scalar.Word (fresh+n))
 (ran : evalStmt horizon .nil True.intro body artifact.compiled.profile
   (sourceLocals (Vector.replicate fresh (0 : Scalar.Word) ++ locals)) = some ⟨sourceLocals out,.normal⟩) :
 evalStmt (horizon+1) .nil True.intro (.zero fresh body) artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals (outerLocals out),.normal⟩ := by
 change Option.bind (evalStmt horizon .nil True.intro body artifact.compiled.profile
   (extendValues (fun _ : Fin fresh => word 0) (sourceLocals locals))) _ = _
 rw [←initial_values,ran]
 change some (⟨dropValues fresh (sourceLocals out),.normal⟩ : Outcome c n) = _
 rw [←ScopedStatements.locals_outer]

/-- Entry capacity is a SEPARATE actual trace obligation. Scalar or model
execution success alone supplies no such 1024-word bound. -/
theorem entry_capacity {n fresh : Nat} (locals : Vector Scalar.Word n) (tail : Stack)
 (bounded : Scalar.stackBound (entry fresh) ((n+tail.length : Nat) : Int) = true) :
 fresh+n+tail.length ≤ 1024 := by
 have executed := pushPrefix_run (Vector.replicate fresh (0 : Scalar.Word)).toList (locals.toList++tail)
 have height := run_capacity executed (by simpa only [List.length_append,Vector.length_toList] using bounded)
 simpa only [List.length_append,Vector.length_toList,Nat.add_assoc] using height

/-- A completed original zero scope derives an actual selected whole run.
Fresh-local body updates and caller contents come from real compiler laws,
not desired exchange/body results; the actual body depth remains zero. -/
theorem source_to_model {c : Control} {n fresh fuel : Nat} {body : Stmt [] [] c (fresh+n)}
 (artifact : LoopControlCompilation.Artifact fuel body 0) (code : List Evm.Instr)
 (lowered : lower fresh artifact = some code) (horizon : Nat)
 (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro (.zero fresh body) artifact.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 obtain ⟨begin,beginSelected,rest⟩ := Option.bind_eq_some_iff.mp lowered
 obtain ⟨finish,finishSelected,same⟩ := Option.bind_eq_some_iff.mp rest
 cases Option.some.inj same
 cases horizon with
 | zero => cases ran
 | succ horizon =>
   change Option.bind (evalStmt horizon .nil True.intro body artifact.compiled.profile
     (extendValues (fun _ : Fin fresh => word 0) (sourceLocals locals))) _ = some result at ran
   rw [←initial_values] at ran
   obtain ⟨middle,bodySource,remaining⟩ := Option.bind_eq_some_iff.mp ran
   obtain ⟨out,same,bodyRun⟩ := artifact.source_to_model horizon
     (Vector.replicate fresh (0 : Scalar.Word) ++ locals) middle bodySource #v[] m caller
   subst middle
   have projected : result = ⟨sourceLocals (outerLocals out),.normal⟩ := by
     have same := (Option.some.inj remaining).symm
     rw [←ScopedStatements.locals_outer] at same
     exact same
   have entering := WordExecution.run (entry fresh) begin beginSelected locals.toList
     ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList)
     (pushPrefix_run _ _) m caller
   have bodyRun' : Evm.run artifact.code
     {m with stack := ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList).map coreWord++caller} =
     .ok {m with stack := out.toList.map coreWord++caller} 0 := by
     simpa only [Vector.toList_empty,List.nil_append,Vector.toList_append] using bodyRun
   have exitScalar : Scalar.run (popPrefix fresh) out.toList = some (outerLocals out).toList := by
     simpa only [List.append_nil] using popFresh_run out []
   have exiting := WordExecution.run (popPrefix fresh) finish finishSelected out.toList
     (outerLocals out).toList exitScalar m caller
   refine ⟨outerLocals out,projected,?_⟩
   rw [List.append_assoc,Evm.run_append_ok entering,Evm.run_append_ok bodyRun']
   exact exiting

/-- info: 'Solidity.Yul.Compilation.ZeroLoopScope.entry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms entry
/-- info: 'Solidity.Yul.Compilation.ZeroLoopScope.lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lower
/-- info: 'Solidity.Yul.Compilation.ZeroLoopScope.initial_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms initial_values
/-- info: 'Solidity.Yul.Compilation.ZeroLoopScope.source_scope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_scope
/-- info: 'Solidity.Yul.Compilation.ZeroLoopScope.entry_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_capacity
/-- info: 'Solidity.Yul.Compilation.ZeroLoopScope.source_to_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_to_model
end Solidity.Yul.Compilation.ZeroLoopScope
