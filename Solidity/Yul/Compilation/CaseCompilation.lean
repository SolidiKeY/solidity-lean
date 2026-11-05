import Solidity.Yul.Compilation.SwitchCompilation
/-! Finite original Cases compilation retaining one full-word selector between
misses and retiring it exactly once before the selected scoped arm/default.
Evidence is indexed by original Cases, not another source AST. Static label
admission remains the existing checker obligation, not an execution theorem. -/
namespace Solidity.Yul.Compilation.CaseCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

inductive Compiled {c : Control} {n : Nat} : Nat → Cases [] [] c n → Type where
 | nil (fuel : Nat) : Compiled fuel .nil
 | cons {fuel : Nat} {label : Solidity.Yul.Word} {body : Stmt [] [] c n} {rest : Cases [] [] c n}
     (arm : ScopedControlCompilation.Artifact fuel body) (tail : Compiled fuel rest) :
     Compiled (fuel+1) (.cons label body rest)

def Compiled.profile {c n fuel} {arms : Cases [] [] c n} (compiled : Compiled fuel arms) : CasesWordP arms := by
 apply Compiled.casesOn (motive := fun fuel arms _ => CasesWordP arms) compiled
 case nil => intro fuel; exact True.intro
 case cons => intro fuel label body rest arm tail; exact ⟨arm.compiled.profile,tail.profile⟩
termination_by structural compiled

def Compiled.emit {c n fuel} {arms : Cases [] [] c n} (compiled : Compiled fuel arms)
 (fallback : Backend.Block) : Option Backend.Block := by
 apply Compiled.casesOn (motive := fun _ _ _ => Option Backend.Block) compiled
 case nil => intro fuel; exact some (.seq (.code (popPrefix 1)) fallback)
 case cons =>
   intro fuel label body rest arm tail
   exact do
     let p ← (SwitchCompilation.comparison label).code 0
     let next ← tail.emit fallback
     pure (.ite p (.seq (.code (popPrefix 1)) arm.block) next)
termination_by structural compiled

def compile {c : Control} {n : Nat} (fuel : Nat) (arms : Cases [] [] c n) : Option (Compiled fuel arms) :=
 match fuel with
 | 0 => by
   apply Cases.casesOn (motive_2 := fun F X c n arms =>
     match F,X with
     | [],[] => Option (Compiled 0 arms)
     | _,_ => Unit) arms
   case nil => intro F X c n; cases F <;> cases X; exact some (.nil 0); all_goals exact ()
   case cons => intro F X c n label body rest; cases F <;> cases X; exact none; all_goals exact ()
 | fuel+1 => by
   apply Cases.casesOn (motive_2 := fun F X c n arms =>
     match F,X with
     | [],[] => Option (Compiled (fuel+1) arms)
     | _,_ => Unit) arms
   case nil => intro F X c n; cases F <;> cases X; exact some (.nil (fuel+1)); all_goals exact ()
   case cons =>
     intro F X c n label body rest
     cases F <;> cases X
     · exact do
         let arm ← ScopedControlCompilation.lower fuel body
         let tail ← compile fuel rest
         pure (.cons arm tail)
     all_goals exact ()
termination_by structural fuel

/-- Original matching case evaluation; the tail does not execute. -/
theorem source_hit {c : Control} {n : Nat} {body : Stmt [] [] c n} {rest : Cases [] [] c n}
 (label selector : Solidity.Yul.Word) (hb : StmtWordP body) (hr : CasesWordP rest)
 (horizon : Nat) (locals out : Vector Scalar.Word n) (equal : selector = label)
 (ran : evalStmt horizon .nil True.intro body hb (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩) :
 evalCases (horizon+1) .nil True.intro (.cons label body rest) ⟨hb,hr⟩ selector (sourceLocals locals) =
 some (some ⟨sourceLocals out,.normal⟩) := by
 change (if selector = label then (evalStmt horizon .nil True.intro body hb (sourceLocals locals)).map some
   else evalCases horizon .nil True.intro rest hr selector (sourceLocals locals)) = _
 rw [if_pos equal,ran]
 rfl

/-- A missed original case advances exactly one case horizon. -/
theorem source_miss {c : Control} {n : Nat} {body : Stmt [] [] c n} {rest : Cases [] [] c n}
 (label selector : Solidity.Yul.Word) (hb : StmtWordP body) (hr : CasesWordP rest)
 (horizon : Nat) (locals : Vector Scalar.Word n) (chosen : Option (Outcome c n))
 (different : selector ≠ label)
 (ran : evalCases horizon .nil True.intro rest hr selector (sourceLocals locals) = some chosen) :
 evalCases (horizon+1) .nil True.intro (.cons label body rest) ⟨hb,hr⟩ selector (sourceLocals locals) = some chosen := by
 change (if selector = label then (evalStmt horizon .nil True.intro body hb (sourceLocals locals)).map some
   else evalCases horizon .nil True.intro rest hr selector (sourceLocals locals)) = _
 rw [if_neg different]
 exact ran

theorem source_to_model {c : Control} {n fuel ff : Nat} {arms : Cases [] [] c n} {fallbackStmt : Stmt [] [] c n}
 (compiled : Compiled fuel arms) (fallback : ScopedControlCompilation.Artifact ff fallbackStmt)
 (block : Backend.Block) (code : List Evm.Instr)
 (emitted : compiled.emit fallback.block = some block) (selected : WordControl.blockCode block = some code)
 (selector : Scalar.Word) (horizon fallbackHorizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : (do
   let chosen ← evalCases horizon .nil True.intro arms compiled.profile selector.toFin (sourceLocals locals)
   match chosen with
   | some result => pure result
   | none => evalStmt fallbackHorizon .nil True.intro fallbackStmt fallback.compiled.profile (sourceLocals locals)) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run code {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 induction compiled generalizing block code horizon result with
 | nil fuel =>
   change some (Backend.Block.seq (.code (popPrefix 1)) fallback.block) = some block at emitted
   cases Option.some.inj emitted
   change (WordMachine.selectCode (popPrefix 1)).bind (fun p => (WordControl.blockCode fallback.block).map (fun q => p++q)) = some code at selected
   rw [fallback.selected] at selected
   change some (.pop::fallback.code) = some code at selected
   cases Option.some.inj selected
   cases horizon with
   | zero => cases ran
   | succ horizon =>
     change evalStmt fallbackHorizon .nil True.intro fallbackStmt fallback.compiled.profile (sourceLocals locals) = some result at ran
     obtain ⟨out,same,target⟩ := fallback.source_to_model fallbackHorizon locals result ran m caller
     refine ⟨out,same,?_⟩
     have popped : Evm.run [.pop] {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} =
       .ok {m with stack := locals.toList.map coreWord++caller} 0 := by rfl
     change Evm.run ([.pop]++fallback.code) _ = _
     rw [Evm.run_append_ok popped]
     exact target
 | @cons fuel label body rest arm tail ih =>
   change ((SwitchCompilation.comparison label).code 0).bind (fun p => (tail.emit fallback.block).bind
     (fun next => some (Backend.Block.ite p (.seq (.code (popPrefix 1)) arm.block) next))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨next,ht,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   have armSelected : WordControl.blockCode (.seq (.code (popPrefix 1)) arm.block) = some (.pop::arm.code) := by
     change (WordMachine.selectCode (popPrefix 1)).bind (fun p => (WordControl.blockCode arm.block).map (fun q => p++q)) = _
     rw [arm.selected]
     rfl
   change (WordMachine.selectCode p).bind (fun ps =>
     (WordControl.blockCode (.seq (.code (popPrefix 1)) arm.block)).bind (fun yes =>
       (WordControl.blockCode next).map (fun no => MachineControl.branchCode ps yes no))) = some code at selected
   rw [armSelected] at selected
   simp only [Option.bind_some] at selected
   obtain ⟨ps,sp,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨ns,sn,same⟩ := Option.map_eq_some_iff.mp rest
   subst code
   have compared : Evm.run ps {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} =
     .ok {m with stack := (coreWord (WordExpressions.selectEq.value selector (BitVec.ofFin label))::
       coreWord selector::(locals.toList.map coreWord++caller))} 0 := by
     simpa only [Vector.toList_empty,Vector.toList_singleton,List.nil_append,List.map_cons,List.map_nil,List.singleton_append] using
       WordExecution.loweredExpr_machine (SwitchCompilation.comparison label) 0 p ps hp sp #v[selector] #v[] m
         (locals.toList.map coreWord++caller)
   cases horizon with
   | zero => cases ran
   | succ horizon =>
     change Option.bind (if selector.toFin = label then
       (evalStmt horizon .nil True.intro body arm.compiled.profile (sourceLocals locals)).map some
       else evalCases horizon .nil True.intro _ tail.profile selector.toFin (sourceLocals locals))
       (fun chosen => match chosen with
         | some result => some result
         | none => evalStmt fallbackHorizon .nil True.intro fallbackStmt fallback.compiled.profile (sourceLocals locals)) = some result at ran
     by_cases equal : selector.toFin = label
     · rw [if_pos equal] at ran
       obtain ⟨choice,selectedSource,remaining⟩ := Option.bind_eq_some_iff.mp ran
       obtain ⟨actual,armSource,same⟩ := Option.map_eq_some_iff.mp selectedSource
       subst choice
       change some actual = some result at remaining
       cases Option.some.inj remaining
       obtain ⟨out,same,target⟩ := arm.source_to_model horizon locals result armSource m caller
       refine ⟨out,same,?_⟩
       rw [MachineControl.branchCode,Evm.run_append_ok compared,SwitchCompilation.comparison_value,if_pos equal]
       rw [FramedBranch.nonzero_tail 1 (.pop::arm.code) ns
         {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} (by decide)]
       have popped : Evm.run [.pop] {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} =
         .ok {m with stack := locals.toList.map coreWord++caller} 0 := by rfl
       change Evm.run ([.pop]++arm.code) _ = _
       rw [Evm.run_append_ok popped]
       exact target
     · rw [if_neg equal] at ran
       obtain ⟨out,same,target⟩ := ih next ns ht sn horizon result ran
       refine ⟨out,same,?_⟩
       rw [MachineControl.branchCode,Evm.run_append_ok compared,SwitchCompilation.comparison_value,if_neg equal]
       change Evm.run (ns++(.jump ((.pop::arm.code).length)::(.pop::arm.code)))
         {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} =
         .ok {m with stack := out.toList.map coreWord++caller} 0
       rw [Evm.run_append_ok target]
       exact Evm.exec_length (.pop::arm.code) _


/-- info: 'Solidity.Yul.Compilation.CaseCompilation.source_hit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_hit
/-- info: 'Solidity.Yul.Compilation.CaseCompilation.source_miss' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_miss
/-- info: 'Solidity.Yul.Compilation.CaseCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.CaseCompilation.source_to_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_to_model
end Solidity.Yul.Compilation.CaseCompilation
