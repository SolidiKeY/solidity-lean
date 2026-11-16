import Solidity.Yul.Compilation.ZeroScopeCompilation
import Solidity.Yul.Compilation.CompletionControls
/-! Actual single-word let binder with an existing structured body artifact.
Original syntax/profiles/contexts and actual scalar/model execution are reused.
This is not a new source representation, calling convention or admission rule. -/
namespace Solidity.Yul.Compilation.LetScopeCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

inductive Compiled {c : Control} {n : Nat} (fuel : Nat) : Stmt [] [] c n → Type where
 | scope {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}
     (initializer : ProducerExpressions.Compiled fuel rhs)
     (artifact : LoopControlCompilation.Artifact fuel body 0) : Compiled fuel (.let_ 1 rhs body)

def Compiled.profile {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) : StmtWordP stmt :=
 Compiled.casesOn (motive := fun stmt _ => StmtWordP stmt) compiled
   (fun initializer artifact => ⟨initializer.profile,artifact.compiled.profile⟩)

def Compiled.code {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) : Option (List Evm.Instr) :=
 Compiled.casesOn (motive := fun _ _ => Option (List Evm.Instr)) compiled
   (fun initializer artifact => do
     let entry ← initializer.lowered.code 0
     let begin ← WordMachine.selectCode entry
     let finish ← WordMachine.selectCode (popPrefix 1)
     pure (begin ++ artifact.code ++ finish))

/-- Actual original let visitor; only single-result initializers are currently
supported. Arity is inspected before constructing exact indexed evidence. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Compiled fuel stmt) := by
 apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
   match F,X with
   | [],[] => Option (Compiled fuel stmt)
   | _,_ => Unit) stmt
 case let_ =>
   intro F X c n arity rhs body
   cases F <;> cases X
   · cases arity with
     | zero => exact none
     | succ rest =>
       cases rest with
       | zero => exact do
         let initializer ← PureExpressions.compile fuel rhs
         let artifact ← LoopControlCompilation.lower fuel body 0
         pure (.scope initializer artifact)
       | succ _ => exact none
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

/-- A real single-result expression value extends the original source frame
in exactly the same top-first order as the target result push. -/
theorem initial_values {n : Nat} (value : Scalar.Word) (locals : Vector Scalar.Word n) :
 extendValues (fun _ : Fin 1 => value.toFin) (sourceLocals locals) = sourceLocals (#v[value] ++ locals) := by
 have one : (fun _ : Fin 1 => value.toFin) = sourceLocals #v[value] := by
   funext i
   have equal : i = 0 := by omega
   subst i
   rfl
 rw [one,ScopedStatements.locals_append]

/-- Every completed source run of the actual selected let artifact derives
normal output and exact model execution. Actual source evaluation determines
the initializer and intermediate body values; no desired body run is assumed. -/
theorem Artifact.source_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 rcases artifact with ⟨compiled,code,lowered⟩
 cases compiled with
 | scope initializer body =>
   obtain ⟨entry,emitted,rest⟩ := Option.bind_eq_some_iff.mp lowered
   obtain ⟨begin,beginSelected,rest⟩ := Option.bind_eq_some_iff.mp rest
   obtain ⟨finish,finishSelected,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   cases horizon with
   | zero => cases ran
   | succ horizon =>
     change (do
       let values ← evalExpr horizon .nil True.intro _ initializer.profile (sourceLocals locals)
       let middle ← evalStmt horizon .nil True.intro _ body.compiled.profile (extendValues values (sourceLocals locals))
       pure (⟨dropValues 1 middle.vars,middle.flow⟩ : Outcome c n)) = some result at ran
     obtain ⟨values,exprSource,rest⟩ := Option.bind_eq_some_iff.mp ran
     have same := evalExpr_completed_unique .nil True.intro _ initializer.profile (sourceLocals locals)
       exprSource (initializer.source locals)
     subst values
     rw [initial_values] at rest
     obtain ⟨middle,bodySource,remaining⟩ := Option.bind_eq_some_iff.mp rest
     obtain ⟨out,same,bodyRun⟩ := body.source_to_model horizon (#v[initializer.value locals] ++ locals)
       middle bodySource #v[] m caller
     subst middle
     have projected : result = ⟨sourceLocals (outerLocals out),.normal⟩ := by
       have same := (Option.some.inj remaining).symm
       rw [←ScopedStatements.locals_outer] at same
       exact same
     have initScalar : Scalar.run entry locals.toList = some (initializer.value locals :: locals.toList) := by
       simpa only [Vector.toList_empty,List.nil_append,List.append_nil] using
         initializer.lowered.correct 0 entry emitted locals #v[] []
     have entering := WordExecution.run entry begin beginSelected locals.toList
       (initializer.value locals :: locals.toList) initScalar m caller
     have bodyRun' : Evm.run body.code
       {m with stack := (initializer.value locals :: locals.toList).map coreWord++caller} =
       .ok {m with stack := out.toList.map coreWord++caller} 0 := by
       simpa only [Vector.toList_empty,List.nil_append,Vector.toList_append,Vector.toList_singleton,List.singleton_append] using bodyRun
     have exitScalar : Scalar.run (popPrefix 1) out.toList = some (outerLocals out).toList := by
       simpa only [List.append_nil] using popFresh_run out []
     have exiting := WordExecution.run (popPrefix 1) finish finishSelected out.toList
       (outerLocals out).toList exitScalar m caller
     refine ⟨outerLocals out,projected,?_⟩
     change Evm.run (begin ++ body.code ++ finish) {m with stack := locals.toList.map coreWord++caller} =
       .ok {m with stack := (outerLocals out).toList.map coreWord++caller} 0
     rw [List.append_assoc,Evm.run_append_ok entering,Evm.run_append_ok bodyRun']
     exact exiting

/-- Build the original let completion from the actual expression producer and
body completion. Their horizons are reconciled by the existing stability laws. -/
theorem scope_source {c : Control} {n fuel : Nat} {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}
 (initializer : ProducerExpressions.Compiled fuel rhs)
 (artifact : LoopControlCompilation.Artifact fuel body 0) (horizon : Nat)
 (locals : Vector Scalar.Word n) (out : Vector Scalar.Word (1+n))
 (ran : evalStmt horizon .nil True.intro body artifact.compiled.profile
   (sourceLocals (#v[initializer.value locals] ++ locals)) = some ⟨sourceLocals out,.normal⟩) :
 evalStmt (max fuel horizon+1) .nil True.intro (.let_ 1 rhs body)
   (⟨initializer.profile,artifact.compiled.profile⟩ : StmtWordP (.let_ 1 rhs body)) (sourceLocals locals) =
 some ⟨sourceLocals (outerLocals out),.normal⟩ := by
 have expr : evalExpr (max fuel horizon) .nil True.intro rhs initializer.profile (sourceLocals locals) =
   some (fun _ => (initializer.value locals).toFin) := CompletionControls.completed_horizon
   (fun budget => evalExpr budget .nil True.intro rhs initializer.profile (sourceLocals locals))
   (fun budget extra => evalExpr_refines_add budget extra .nil True.intro rhs initializer.profile (sourceLocals locals))
   (Nat.le_max_left fuel horizon) (initializer.source locals)
 have bodyRun : evalStmt (max fuel horizon) .nil True.intro body artifact.compiled.profile
   (sourceLocals (#v[initializer.value locals] ++ locals)) = some ⟨sourceLocals out,.normal⟩ :=
   CompletionControls.completed_horizon
     (fun budget => evalStmt budget .nil True.intro body artifact.compiled.profile
       (sourceLocals (#v[initializer.value locals] ++ locals)))
     (fun budget extra => evalStmt_refines_add budget extra .nil True.intro body artifact.compiled.profile
       (sourceLocals (#v[initializer.value locals] ++ locals)))
     (Nat.le_max_right fuel horizon) ran
 change (do
   let values ← evalExpr (max fuel horizon) .nil True.intro rhs initializer.profile (sourceLocals locals)
   let middle ← evalStmt (max fuel horizon) .nil True.intro body artifact.compiled.profile
     (extendValues values (sourceLocals locals))
   pure (⟨dropValues 1 middle.vars,middle.flow⟩ : Outcome c n)) = _
 rw [expr]
 change (do
   let middle ← evalStmt (max fuel horizon) .nil True.intro body artifact.compiled.profile
     (extendValues (fun _ : Fin 1 => (initializer.value locals).toFin) (sourceLocals locals))
   pure (⟨dropValues 1 middle.vars,middle.flow⟩ : Outcome c n)) = _
 rw [initial_values,bodyRun]
 change some (⟨dropValues 1 (sourceLocals out),.normal⟩ : Outcome c n) = _
 rw [←ScopedStatements.locals_outer]

/-- Exact selected run from a specified normal source completion; the output
vector is recovered using original source-local injectivity. -/
theorem Artifact.normal_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals out : Vector Scalar.Word n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 exact CompletionControls.normal_output out _
   (artifact.source_to_model horizon locals ⟨sourceLocals out,.normal⟩ ran m caller)

/-- info: 'Solidity.Yul.Compilation.LetScopeCompilation.scope_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scope_source
/-- info: 'Solidity.Yul.Compilation.LetScopeCompilation.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
/-- info: 'Solidity.Yul.Compilation.LetScopeCompilation.initial_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms initial_values
/-- info: 'Solidity.Yul.Compilation.LetScopeCompilation.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
/-- info: 'Solidity.Yul.Compilation.LetScopeCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.LetScopeCompilation.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower
end Solidity.Yul.Compilation.LetScopeCompilation
