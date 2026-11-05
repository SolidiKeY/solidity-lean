import Solidity.Yul.Compilation.WordExecution
import Solidity.Yul.Compilation.WordControl
import Solidity.Backend.Selection.Interface
/-! Forward execution for the existing StructuredExec relation and unchanged
WordControl selector. All reached scalar runs and loop witnesses are derived.
No replacement syntax/state, scalar failure reflection, native bytes/resource
or Source/G24 adequacy is introduced. Arbitrary symbolic caller tails remain. -/
namespace Solidity.Yul.Compilation.WordBlockExecution
open Backend Scalar MachineAdapter
open Backend.Selection

private theorem seq_parts (a b : Backend.Block) (code : List Evm.Instr)
 (selected : WordControl.blockCode (.seq a b) = some code) :
 ∃ qa qb, WordControl.blockCode a = some qa ∧ WordControl.blockCode b = some qb ∧ code = qa++qb := by
 obtain ⟨qa,ha,rest⟩ := Option.bind_eq_some_iff.mp selected
 obtain ⟨qb,hb,same⟩ := Option.map_eq_some_iff.mp rest
 exact ⟨qa,qb,ha,hb,same.symm⟩

private theorem branch_parts (cc : Backend.Program) (a b : Backend.Block) (code : List Evm.Instr)
 (selected : WordControl.blockCode (.ite cc a b) = some code) :
 ∃ qc qa qb, WordMachine.selectCode cc = some qc ∧ WordControl.blockCode a = some qa ∧
 WordControl.blockCode b = some qb ∧ code = MachineControl.branchCode qc qa qb := by
 obtain ⟨qc,hc,rest⟩ := Option.bind_eq_some_iff.mp selected
 obtain ⟨qa,ha,rest⟩ := Option.bind_eq_some_iff.mp rest
 obtain ⟨qb,hb,same⟩ := Option.map_eq_some_iff.mp rest
 exact ⟨qc,qa,qb,hc,ha,hb,same.symm⟩

private theorem loop_parts (cc : Backend.Program) (b : Backend.Block) (code : List Evm.Instr)
 (selected : WordControl.blockCode (.loop cc b) = some code) :
 ∃ qc qb, WordMachine.selectCode cc = some qc ∧ WordControl.blockCode b = some qb ∧
 code = [.loop qc qb] := by
 obtain ⟨qc,hc,rest⟩ := Option.bind_eq_some_iff.mp selected
 obtain ⟨qb,hb,same⟩ := Option.map_eq_some_iff.mp rest
 exact ⟨qc,qb,hc,hb,same.symm⟩

private theorem loop_singleton (qc qb : List Evm.Instr) (m : Evm.Machine) :
 Evm.run [.loop qc qb] m = Evm.loopRun (Evm.run qc) (Evm.run qb) m := by
 change (Evm.loopRun (Evm.run qc) (Evm.run qb) m).bind (fun next pending => Evm.exec [] pending next) = _
 cases Evm.loopRun (Evm.run qc) (Evm.run qb) m <;> rfl

/-- A successful existing loop denotation has an actual finite iteration
witness. Noncompletion/fault is not silently turned into a finite run. -/
private theorem loop_success_finite {rc rb : Evm.Machine → Evm.Out} {m out : Evm.Machine}
 (ran : Evm.loopRun rc rb m = .ok out 0) :
 ∃ count, Evm.loopIterN rc rb count m = .inr (.ok out 0) := by
 by_cases ends : ∃ result count, Evm.loopIterN rc rb count m = .inr result
 · obtain ⟨result,count,actual⟩ := ends
   have same : result = .ok out 0 := (Evm.loopRun_of_iterN actual).symm.trans ran
   exact ⟨count,actual.trans (congrArg Sum.inr same)⟩
 · simp only [Evm.loopRun,ends,↓reduceDIte] at ran
   cases ran

private theorem branch_true (word : Scalar.Word) (yes no : List Evm.Instr)
 (m out : Evm.Machine) (nonzero : word ≠ 0) (body : Evm.run yes m = .ok out 0) :
 Evm.run (MachineControl.branchTail yes no) {m with stack := coreWord word::m.stack} = .ok out 0 := by
 have nz : word.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
 simp only [MachineControl.branchTail,Evm.run,Evm.exec_cons_zero,Evm.Instr.step,
   coreWord,nz,ite_false,Evm.Out.ok_bind]
 rw [Evm.exec_skip_append]
 exact body

private theorem branch_false (yes no : List Evm.Instr) (m out : Evm.Machine)
 (body : Evm.run no m = .ok out 0) :
 Evm.run (MachineControl.branchTail yes no) {m with stack := coreWord 0::m.stack} = .ok out 0 := by
 change Evm.run (no++(.jump yes.length::yes)) m = _
 rw [Evm.run_append_ok body]
 exact Evm.exec_length yes out

/-- Actual selected block execution. The original finite StructuredExec proof
supplies reached conditions/bodies; untaken arms need no execution premise. -/
theorem execute {block : Backend.Block} {input output : Stack}
 (executed : StructuredExec block input output)
 (code : List Evm.Instr) (selected : WordControl.blockCode block = some code)
 (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run code {m with stack := input.map coreWord++caller} =
 .ok {m with stack := output.map coreWord++caller} 0 := by
 induction executed generalizing code m with
 | @code p s t ran => exact WordExecution.run p code selected s t ran m caller
 | @seq a b s u t left right ihLeft ihRight =>
   obtain ⟨qa,qb,sa,sb,rfl⟩ := seq_parts a b code selected
   rw [Evm.run_append_ok (ihLeft qa sa m)]
   exact ihRight qb sb m
 | @iteTrue cc a b s u t w condition nonzero body ih =>
   obtain ⟨qc,qa,qb,sc,sa,sb,rfl⟩ := branch_parts cc a b code selected
   have conditionRun := WordExecution.run cc qc sc s (w::u) condition m caller
   rw [MachineControl.branchCode,Evm.run_append_ok conditionRun]
   exact branch_true w qa qb {m with stack := u.map coreWord++caller}
     {m with stack := t.map coreWord++caller} nonzero (ih qa sa m)
 | @iteFalse cc a b s u t condition body ih =>
   obtain ⟨qc,qa,qb,sc,sa,sb,rfl⟩ := branch_parts cc a b code selected
   have conditionRun := WordExecution.run cc qc sc s (0::u) condition m caller
   rw [MachineControl.branchCode,Evm.run_append_ok conditionRun]
   exact branch_false qa qb {m with stack := u.map coreWord++caller}
     {m with stack := t.map coreWord++caller} (ih qb sb m)
 | @loopDone cc b s t condition =>
   obtain ⟨qc,qb,sc,sb,rfl⟩ := loop_parts cc b code selected
   have conditionRun := WordExecution.run cc qc sc s (0::t) condition m caller
   have done : Evm.loopIterN (Evm.run qc) (Evm.run qb) 1
     {m with stack := s.map coreWord++caller} =
     .inr (.ok {m with stack := t.map coreWord++caller} 0) := by
     rw [Evm.loopIterN,Evm.loopTurn,conditionRun]
     rfl
   rw [loop_singleton]
   exact Evm.loopRun_of_iterN done
 | @loopMore cc b s u v t w condition nonzero body rest ihBody ihRest =>
   obtain ⟨qc,qb,sc,sb,rfl⟩ := loop_parts cc b code selected
   have conditionRun := WordExecution.run cc qc sc s (w::u) condition m caller
   have bodyRun := ihBody qb sb m
   have restRun := ihRest [.loop qc qb] selected m
   rw [loop_singleton] at restRun
   obtain ⟨count,ended⟩ := loop_success_finite restRun
   have nz : w.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
   have advanced : Evm.loopTurn (Evm.run qc) (Evm.run qb)
     {m with stack := s.map coreWord++caller} = .inl {m with stack := v.map coreWord++caller} := by
     rw [Evm.loopTurn,conditionRun]
     change ((if w.toNat = 0 then
       .inr (.ok {m with stack := u.map coreWord++caller} 0)
       else match Evm.run qb {m with stack := u.map coreWord++caller} with
         | .ok next 0 => .inl next
         | .ok _ (_+1) => .inr .fault
         | result => .inr result) : Evm.Machine ⊕ Evm.Out) = _
     rw [if_neg nz,bodyRun]
   have done : Evm.loopIterN (Evm.run qc) (Evm.run qb) (count+1)
     {m with stack := s.map coreWord++caller} =
     .inr (.ok {m with stack := t.map coreWord++caller} 0) := by
     simpa only [Evm.loopIterN,advanced] using ended
   rw [loop_singleton]
   exact Evm.loopRun_of_iterN done

/-- info: 'Solidity.Yul.Compilation.WordBlockExecution.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms execute
end Solidity.Yul.Compilation.WordBlockExecution
