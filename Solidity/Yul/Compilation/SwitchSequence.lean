import Solidity.Yul.Compilation.MultiSwitchCompilation
/-! Composition of two actual finite-switch compilations at an original seq
node. The second selector observes the updated first frame. Source runtime
horizons and compiler search fuel remain separate. No Source/G24, admission,
native capacity or failure/divergence correspondence is claimed. -/
namespace Solidity.Yul.Compilation.SwitchSequence
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

structure Artifact {c : Control} {n : Nat} (f g : Nat) (a b : Stmt [] [] c n) where
 left : MultiSwitchCompilation.Artifact f a
 right : MultiSwitchCompilation.Artifact g b

def Artifact.profile {c n f g} {a b : Stmt [] [] c n} (artifact : Artifact f g a b) :
 StmtWordP (.seq a b) := ⟨artifact.left.compiled.profile,artifact.right.compiled.profile⟩

def Artifact.block {c n f g} {a b : Stmt [] [] c n} (artifact : Artifact f g a b) : Backend.Block :=
 .seq artifact.left.block artifact.right.block

def Artifact.code {c n f g} {a b : Stmt [] [] c n} (artifact : Artifact f g a b) : List Evm.Instr :=
 artifact.left.code ++ artifact.right.code

/-- Both operands are lowered by the existing compiler, without a run premise. -/
def lower {c n} (f g : Nat) (a b : Stmt [] [] c n) : Option (Artifact f g a b) := do
 let left ← MultiSwitchCompilation.lower f a
 let right ← MultiSwitchCompilation.lower g b
 pure ⟨left,right⟩

theorem Artifact.selected {c n f g} {a b : Stmt [] [] c n} (artifact : Artifact f g a b) :
 WordControl.blockCode artifact.block = some artifact.code := by
 simp only [Artifact.block,Artifact.code,WordControl.blockCode,artifact.left.selected,
   artifact.right.selected,Option.bind_some,Option.map_some]

/-- Actual source sequencing derives the intermediate raw frame, then feeds it
into the second compiler run. No desired intermediate contents are assumed. -/
theorem Artifact.source_to_model {c n f g} {a b : Stmt [] [] c n}
 (artifact : Artifact f g a b) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro (.seq a b) artifact.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 cases horizon with
 | zero => cases ran
 | succ horizon =>
   change Option.bind (evalStmt horizon .nil True.intro a artifact.left.compiled.profile (sourceLocals locals)) _ = some result at ran
   obtain ⟨middle,first,remaining⟩ := Option.bind_eq_some_iff.mp ran
   obtain ⟨mid,same,firstRun⟩ := artifact.left.source_to_model horizon locals middle first m caller
   subst middle
   change evalStmt horizon .nil True.intro b artifact.right.compiled.profile (sourceLocals mid) = some result at remaining
   obtain ⟨out,same,lastRun⟩ := artifact.right.source_to_model horizon mid result remaining
     {m with stack := mid.toList.map coreWord++caller} caller
   refine ⟨out,same,?_⟩
   rw [Artifact.code,Evm.run_append_ok firstRun]
   exact lastRun

/-- Independent successful component horizons suffice; their maximum is used
only for source sequencing, never as a compiler or native gas budget. -/
theorem Artifact.join_source {c n f g} {a b : Stmt [] [] c n}
 (artifact : Artifact f g a b) (ha hb : Nat) (locals mid out : Vector Scalar.Word n)
 (first : evalStmt ha .nil True.intro a artifact.left.compiled.profile (sourceLocals locals) = some ⟨sourceLocals mid,.normal⟩)
 (last : evalStmt hb .nil True.intro b artifact.right.compiled.profile (sourceLocals mid) = some ⟨sourceLocals out,.normal⟩) :
 evalStmt (max ha hb+1) .nil True.intro (.seq a b) artifact.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ := by
 have first' := evalStmt_stable (Nat.le_max_left ha hb) .nil True.intro a artifact.left.compiled.profile (sourceLocals locals) first
 have last' := evalStmt_stable (Nat.le_max_right ha hb) .nil True.intro b artifact.right.compiled.profile (sourceLocals mid) last
 change Option.bind (evalStmt (max ha hb) .nil True.intro a artifact.left.compiled.profile (sourceLocals locals)) _ = _
 rw [first']
 exact last'

theorem Artifact.normal_to_model {c n f g} {a b : Stmt [] [] c n}
 (artifact : Artifact f g a b) (horizon : Nat) (locals out : Vector Scalar.Word n)
 (ran : evalStmt horizon .nil True.intro (.seq a b) artifact.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 obtain ⟨actual,same,target⟩ := artifact.source_to_model horizon locals ⟨sourceLocals out,.normal⟩ ran m caller
 have equal : out = actual := SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 cases equal
 exact target

/-- info: 'Solidity.Yul.Compilation.SwitchSequence.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
/-- info: 'Solidity.Yul.Compilation.SwitchSequence.Artifact.join_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.join_source
/-- info: 'Solidity.Yul.Compilation.SwitchSequence.Artifact.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Artifact.selected
/-- info: 'Solidity.Yul.Compilation.SwitchSequence.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
end Solidity.Yul.Compilation.SwitchSequence
