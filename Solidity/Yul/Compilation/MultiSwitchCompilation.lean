import Solidity.Yul.Compilation.CaseCompilation
/-! Original switch lowering for finite Cases using actual scoped arm/default
artifacts. The selector is computed once; case fuel and default runtime horizon
remain distinct. This supplies no new source/checker admission or G24 closure. -/
namespace Solidity.Yul.Compilation.MultiSwitchCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

inductive Compiled {c : Control} {n : Nat} (fuel : Nat) : Stmt [] [] c n → Type where
 | many {test : Expr [] [] n 1} {arms : Cases [] [] c n} {fallback : Stmt [] [] c n}
     (condition : ProducerExpressions.Compiled fuel test)
     (cases : CaseCompilation.Compiled fuel arms)
     (default : ScopedControlCompilation.Artifact fuel fallback) : Compiled fuel (.switch test arms fallback)

def Compiled.profile {c n fuel} {stmt : Stmt [] [] c n} (compiled : Compiled fuel stmt) : StmtWordP stmt :=
 Compiled.casesOn (motive := fun stmt _ => StmtWordP stmt) compiled
   (fun condition cases default => ⟨condition.profile,cases.profile,default.compiled.profile⟩)

def Compiled.emit {c n fuel} {stmt : Stmt [] [] c n} (compiled : Compiled fuel stmt) : Option Backend.Block :=
 Compiled.casesOn (motive := fun _ _ => Option Backend.Block) compiled
   (fun condition cases default => do
     let p ← condition.lowered.code 0
     let next ← cases.emit default.block
     pure (.seq (.code p) next))

def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Compiled fuel stmt) := by
 apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
   match F,X with
   | [],[] => Option (Compiled fuel stmt)
   | _,_ => Unit) stmt
 case switch =>
   intro F X c n test arms fallback
   cases F <;> cases X
   · exact do
       let condition ← PureExpressions.compile fuel test
       let cases ← CaseCompilation.compile fuel arms
       let default ← ScopedControlCompilation.lower fuel fallback
       pure (.many condition cases default)
   all_goals exact ()
 all_goals intro F X; cases F <;> cases X <;> intros <;> first | exact none | exact ()

structure Artifact {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) where
 compiled : Compiled fuel stmt
 block : Backend.Block
 code : List Evm.Instr
 emitted : compiled.emit = some block
 selected : WordControl.blockCode block = some code

def lower {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Artifact fuel stmt) := do
 let compiled ← compile fuel stmt
 match emitted : compiled.emit with
 | none => none
 | some block =>
   match selected : WordControl.blockCode block with
   | none => none
   | some code => some ⟨compiled,block,code,emitted,selected⟩

/-- Compose the real original selector/case/default source computations. -/
theorem source_chosen {c : Control} {n fc : Nat} {test : Expr [] [] n 1}
 {arms : Cases [] [] c n} {fallback : Stmt [] [] c n}
 (condition : ProducerExpressions.Compiled fc test) (hc : CasesWordP arms) (hf : StmtWordP fallback)
 (horizon : Nat) (locals : Vector Scalar.Word n) (chosen : Option (Outcome c n)) (result : Outcome c n)
 (bound : fc ≤ horizon)
 (selected : evalCases horizon .nil True.intro arms hc (condition.value locals).toFin (sourceLocals locals) = some chosen)
 (continued : (match chosen with
   | some result => some result
   | none => evalStmt horizon .nil True.intro fallback hf (sourceLocals locals)) = some result) :
 evalStmt (horizon+1) .nil True.intro (.switch test arms fallback) ⟨condition.profile,hc,hf⟩ (sourceLocals locals) = some result := by
 have tested := evalExpr_stable bound .nil True.intro test condition.profile (sourceLocals locals) (condition.source locals)
 change Option.bind (evalExpr horizon .nil True.intro test condition.profile (sourceLocals locals)) _ = _
 rw [tested]
 change Option.bind (evalCases horizon .nil True.intro arms hc (condition.value locals).toFin (sourceLocals locals)) _ = _
 rw [selected]
 cases chosen <;> exact continued

theorem Artifact.source_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 rcases artifact with ⟨compiled,block,code,emitted,selected⟩
 cases compiled with
 | many condition cases default =>
   change (condition.lowered.code 0).bind (fun p => (cases.emit default.block).bind
     (fun next => some (Backend.Block.seq (.code p) next))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨next,hn,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   change (WordMachine.selectCode p).bind (fun ps => (WordControl.blockCode next).map (fun ns => ps++ns)) = some code at selected
   obtain ⟨ps,sp,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨ns,sn,same⟩ := Option.map_eq_some_iff.mp rest
   subst code
   have selectorTarget : Evm.run ps {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} 0 := by
     simpa only [Vector.toList_empty,List.nil_append] using
       WordExecution.loweredExpr_machine condition.lowered 0 p ps hp sp locals #v[] m caller
   cases horizon with
   | zero => cases ran
   | succ horizon =>
     change Option.bind (evalExpr horizon .nil True.intro _ condition.profile (sourceLocals locals)) _ = some result at ran
     obtain ⟨values,tested,remaining⟩ := Option.bind_eq_some_iff.mp ran
     have same := evalExpr_completed_unique .nil True.intro _ condition.profile (sourceLocals locals)
       tested (condition.source locals)
     subst values
     obtain ⟨out,same,target⟩ := CaseCompilation.source_to_model cases default next ns hn sn
       (condition.value locals) horizon horizon locals result remaining m caller
     refine ⟨out,same,?_⟩
     rw [Evm.run_append_ok selectorTarget]
     exact target

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




/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.source_chosen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_chosen
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
end Solidity.Yul.Compilation.MultiSwitchCompilation
