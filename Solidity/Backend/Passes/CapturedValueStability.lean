import Solidity.Backend.Passes.ValueCertificate
import Solidity.Backend.Passes.MappedSequence
import Solidity.Backend.Passes.TailLoop

/-! Actual primitive capture followed by an old-local update. Both operand
words are chosen before all caller tails. The captured cell is physically
disjoint from every old local; no value-representation injectivity premise. -/
namespace Solidity.Backend.Passes.CapturedValueStability
open Evm Evm.Memory Evm.Compiler
variable {C : Contract} {Γ : Ctx} {p q : PrimTy}

/-- One actual successful value execution fixes its word for every tail. -/
theorem value_shared {b L frame : Nat} {F : Frag Γ}
    (e : Val C Γ p) (code : CompiledVal b F e)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (v : p.Denote) (evaluated : e.evalT state = .ok v) :
    ∃ word, ReprV p v word ∧ ∀ tail,
      run code.code {machine with stack := tail} =
        .ok ({machine with stack := tail}.push word) 0 := by
  obtain ⟨word,repr,emptyRun⟩ := value_success_tail code represented evaluated []
  refine ⟨word,repr,?_⟩
  intro tail
  have stable := run_tail code.code {machine with stack := []} tail
    (by rw [emptyRun]; intro impossible; cases impossible)
  simpa only [emptyRun,appendOut,appendTail,Machine.push,List.nil_append,
    List.cons_append] using stable

def program (x : Var) (e : Val C Γ p) (dst : Idx Γ (.val q))
    (update : Val C (.val p :: Γ) q) : Prog C Γ (.val p :: Γ) :=
  .cons (.declLocal p x (some e)) (.cons (.assignLocal (.there dst) update) .nil)

def compiled {b : Nat} {F : Frag Γ} (x : Var) (e : Val C Γ p)
    (first : CompiledVal b F e) (dst : Idx Γ (.val q))
    (update : Val C (.val p :: Γ) q)
    (second : CompiledVal b (F.push (.val p) .ok) update) :
    Compilation b F (program x e dst update) :=
  .memory ⟨F.push (.val p) .ok,
    (first.code ++ [.mstore (cell (b+Γ.length))]) ++
      ((second.code ++ [.mstore (cellOf b (.there (u := .val p) dst))]) ++ []),
    .cons (.declare F x e _ first.cert)
      (.cons (.assign _ (.there dst) update _ second.cert) (.nil _))⟩

theorem source (x : Var) (e : Val C Γ p) (dst : Idx Γ (.val q))
    (update : Val C (.val p :: Γ) q) (state : State C Γ)
    (v : p.Denote) (u : q.Denote) (first : e.evalT state = .ok v)
    (second : update.evalT (state.push (t := .val p) v) = .ok u) :
    (program x e dst update).run state =
      .ok ⟨(state.push (t := .val p) v).setLocal (.there dst) u,List.prefix_refl _⟩ := by
  have declaration : (Stmt.declLocal p x (some e)).run state =
      .ok ⟨state.push (t := .val p) v,List.prefix_refl _⟩ := by
    change TRun.declLocal p (some e) state = _
    simp only [TRun.declLocal,first,bind,Except.bind,pure,Except.pure]
  have assignment : (Stmt.assignLocal (.there dst) update).run
      (state.push (t := .val p) v) =
      .ok ⟨(state.push (t := .val p) v).setLocal (.there dst) u,List.prefix_refl _⟩ := by
    change TRun.assignLocal (.there dst) update _ = _
    simp only [TRun.assignLocal,second,bind,Except.bind]
    rfl
  rw [program,Prog.run_cons_ok declaration,Prog.run_cons_ok assignment]
  rfl

theorem input {b L frame : Nat} {F : Frag Γ}
    (x : Var) (e : Val C Γ p) (first : CompiledVal b F e) (dst : Idx Γ (.val q))
    (update : Val C (.val p :: Γ) q) (second : CompiledVal b (F.push (.val p) .ok) update)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) :
    (compiled x e first dst update second).Input L frame base state machine := by
  refine ⟨represented,?_,Or.inl rfl⟩
  change b+max (max Γ.length (max (Γ.length+1) 0))
    (max (max (Γ.length+1) (max (Γ.length+1) 0)) (Γ.length+1)) ≤ frame
  omega

/-- Actual capture and update prefixes, full accepted mapped output and
physical readback of the ORIGINAL captured word after the old local changes. -/
theorem execution {b L frame : Nat} {F : Frag Γ}
    (x : Var) (e : Val C Γ p) (first : CompiledVal b F e) (dst : Idx Γ (.val q))
    (update : Val C (.val p :: Γ) q) (second : CompiledVal b (F.push (.val p) .ok) update)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame)
    (v : p.Denote) (u : q.Denote) (hv : e.evalT state = .ok v)
    (hu : update.evalT (state.push (t := .val p) v) = .ok u) :
    ∃ captured updated, ReprV p v captured ∧ ReprV q u updated ∧ ∀ tail,
      let cm := writeMachine {machine with stack := tail} (cell (b+Γ.length)) captured
      let em := writeMachine cm (cellOf b (.there (u := .val p) dst)) updated
      (compiled x e first dst update second).Input L frame base state {machine with stack := tail} ∧
      run (first.code ++ [.mstore (cell (b+Γ.length))]) {machine with stack := tail} = .ok cm 0 ∧
      run (second.code ++ [.mstore (cellOf b (.there (u := .val p) dst))]) cm = .ok em 0 ∧
      MappedOutput (compiled x e first dst update second) L frame base state
        {machine with stack := tail}
        ((state.push (t := .val p) v).setLocal (.there dst) u) em base ∧
      run (compiled x e first dst update second).code {machine with stack := tail} = .ok em 0 ∧
      run [.mload (cell (b+Γ.length))] em = .ok (em.push captured) 0 := by
  obtain ⟨captured,repr1,firstRuns⟩ := value_shared e first represented v hv
  have capRepr := (represented.stack []).consVal (p := p) v captured repr1 capacity
  obtain ⟨updated,repr2,secondRuns⟩ := value_shared update second capRepr u hu
  refine ⟨captured,updated,repr1,repr2,?_⟩
  intro tail
  let cm := writeMachine {machine with stack := tail} (cell (b+Γ.length)) captured
  let em := writeMachine cm (cellOf b (.there (u := .val p) dst)) updated
  have captureRun : run (first.code ++ [.mstore (cell (b+Γ.length))])
      {machine with stack := tail} = .ok cm 0 := by
    rw [run_append_ok (firstRuns tail)]
    rfl
  have updateValue : run second.code cm = .ok (cm.push updated) 0 := by
    simpa only [cm,writeMachine] using secondRuns tail
  have updateRun : run (second.code ++ [.mstore (cellOf b (.there (u := .val p) dst))]) cm = .ok em 0 := by
    rw [run_append_ok updateValue]
    rfl
  have reached := ((represented.stack tail).consVal (p := p) v captured repr1 capacity).setVal (p := q)
    (.there (u := .val p) dst) u updated repr2
  refine ⟨input x e first dst update second (represented.stack tail) capacity,
    captureRun,updateRun,⟨reached,BaseExtends.refl base,?_⟩,?_,?_⟩
  · intro cursor hb allocator space
    have initial := allocator.localWrite (b+Γ.length) (by omega) (by omega) captured
    exact initial.localWrite _ (Nat.lt_of_lt_of_le hb (le_lvl b (.there dst)))
      (by simpa only [cellOf,lvl_there] using Nat.lt_of_lt_of_le (lvl_lt b dst) represented.locals) updated
  · change run ((_ ++ _) ++ ((_ ++ _) ++ [])) _ = _
    rw [run_append_ok captureRun,run_append_ok updateRun]
    rfl
  · have separate : cellOf b (.there (u := .val p) dst) ≠ cell (b+Γ.length) := by
      simpa only [cellOf,lvl_there,cell] using Nat.ne_of_lt (lvl_lt b dst)
    change run [.mload (cell (b+Γ.length))] em = _
    have read : em.mem (cell (b+Γ.length)) = captured := by
      exact (upd_other _ _ separate.symm).trans (upd_same _ _ _)
    change Evm.Out.ok (em.push (em.mem (cell (b+Γ.length)))) 0 = _
    rw [read]

end Solidity.Backend.Passes.CapturedValueStability
/-- info: 'Solidity.Backend.Passes.CapturedValueStability.value_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.CapturedValueStability.value_shared
/-- info: 'Solidity.Backend.Passes.CapturedValueStability.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.CapturedValueStability.source
/-- info: 'Solidity.Backend.Passes.CapturedValueStability.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.CapturedValueStability.input
/-- info: 'Solidity.Backend.Passes.CapturedValueStability.execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.CapturedValueStability.execution

namespace Solidity.Backend.Passes.CapturedValueStability
open Evm Evm.Memory Evm.Compiler
variable {C : Contract} {Γ : Ctx} {p q : PrimTy}

def captureStage {b : Nat} {F : Frag Γ} (x : Var) (e : Val C Γ p)
    (first : CompiledVal b F e) :
    Compilation b F (.cons (.declLocal p x (some e)) .nil) :=
  .memory ⟨F.push (.val p) .ok,(first.code ++ [.mstore (cell (b+Γ.length))]) ++ [],
    .cons (.declare F x e _ first.cert) (.nil _)⟩

theorem captured_source (state : State C Γ) (v : p.Denote)
    (dst : Idx Γ (.val q)) (u : q.Denote) :
    (Val.simple (.local .here) : Val C (.val p :: Γ) p).evalT
      ((state.push (t := .val p) v).setLocal (.there dst) u) = .ok v := rfl

/-- A real successful capture, with full mapped prefix output, precedes an
actual update-expression revert. No post-revert machine/map is supplied. -/
theorem edit_failure {b L frame : Nat} {F : Frag Γ}
    (x : Var) (e : Val C Γ p) (first : CompiledVal b F e) (dst : Idx Γ (.val q))
    (update : Val C (.val p :: Γ) q) (second : CompiledVal b (F.push (.val p) .ok) update)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame)
    (v : p.Denote) (hv : e.evalT state = .ok v)
    (hu : update.evalT (state.push (t := .val p) v) = .error .revert) :
    (program x e dst update).run state = .error .revert ∧
    ∃ captured, ReprV p v captured ∧ ∀ tail,
      let cm := writeMachine {machine with stack := tail} (cell (b+Γ.length)) captured
      (compiled x e first dst update second).Input L frame base state {machine with stack := tail} ∧
      run (captureStage x e first).code {machine with stack := tail} = .ok cm 0 ∧
      MappedOutput (captureStage x e first) L frame base state {machine with stack := tail}
        (state.push (t := .val p) v) cm base ∧
      run second.code cm = .revert ∧
      run (compiled x e first dst update second).code {machine with stack := tail} = .revert := by
  have declaration : (Stmt.declLocal p x (some e)).run state =
      .ok ⟨state.push (t := .val p) v,List.prefix_refl _⟩ := by
    change TRun.declLocal p (some e) state = _
    simp only [TRun.declLocal,hv,bind,Except.bind,pure,Except.pure]
  have assignment : (Stmt.assignLocal (.there dst) update).run (state.push (t := .val p) v) =
      .error .revert := by
    change TRun.assignLocal (.there dst) update _ = _
    simp only [TRun.assignLocal,hu,bind,Except.bind]
  refine ⟨?_,?_⟩
  · rw [program,Prog.run_cons_ok declaration,Prog.run_cons_error assignment]
    rfl
  · obtain ⟨captured,repr,runs⟩ := value_shared e first represented v hv
    refine ⟨captured,repr,?_⟩
    intro tail
    have captureRun : run (first.code ++ [.mstore (cell (b+Γ.length))])
        {machine with stack := tail} =
        .ok (writeMachine {machine with stack := tail} (cell (b+Γ.length)) captured) 0 := by
      rw [run_append_ok (runs tail)]
      rfl
    have reached := (represented.stack tail).consVal (p := p) v captured repr capacity
    have failed := (value_revert_iff second reached tail).mpr hu
    refine ⟨input x e first dst update second (represented.stack tail) capacity,?_,
      ⟨reached,BaseExtends.refl base,?_⟩,failed,?_⟩
    · change run ((_ ++ _) ++ []) _ = _
      rw [List.append_nil]
      exact captureRun
    · intro cursor hb allocator space
      exact allocator.localWrite (b+Γ.length) (by omega) (by omega) captured
    · change run ((_ ++ _) ++ ((_ ++ _) ++ [])) _ = _
      rw [run_append_ok captureRun]
      exact run_append_revert (run_append_revert failed)

end Solidity.Backend.Passes.CapturedValueStability
/-- info: 'Solidity.Backend.Passes.CapturedValueStability.captured_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.CapturedValueStability.captured_source
/-- info: 'Solidity.Backend.Passes.CapturedValueStability.edit_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.CapturedValueStability.edit_failure

namespace Solidity.Backend.Passes.CapturedValueStability
open Evm Evm.Memory Evm.Compiler
variable {C : Contract} {Γ : Ctx} {p q : PrimTy}

theorem immediate_failure {b L frame : Nat} {F : Frag Γ}
    (x : Var) (e : Val C Γ p) (first : CompiledVal b F e) (dst : Idx Γ (.val q))
    (update : Val C (.val p :: Γ) q) (second : CompiledVal b (F.push (.val p) .ok) update)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) (failed : e.evalT state = .error .revert) :
    (program x e dst update).run state = .error .revert ∧ ∀ tail,
      (compiled x e first dst update second).Input L frame base state {machine with stack := tail} ∧
      run first.code {machine with stack := tail} = .revert ∧
      run (compiled x e first dst update second).code {machine with stack := tail} = .revert := by
  have declaration : (Stmt.declLocal p x (some e)).run state = .error .revert := by
    change TRun.declLocal p (some e) state = _
    simp only [TRun.declLocal,failed,bind,Except.bind]
  refine ⟨Prog.run_cons_error declaration,?_⟩
  intro tail
  have target := (value_revert_iff first represented tail).mpr failed
  refine ⟨input x e first dst update second (represented.stack tail) capacity,target,?_⟩
  exact run_append_revert (run_append_revert target)

theorem failure_iff_source {b L frame : Nat} {F : Frag Γ}
    (x : Var) (e : Val C Γ p) (first : CompiledVal b F e) (dst : Idx Γ (.val q))
    (update : Val C (.val p :: Γ) q) (second : CompiledVal b (F.push (.val p) .ok) update)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) (tail : List Word) :
    run (compiled x e first dst update second).code {machine with stack := tail} = .revert ↔
      (program x e dst update).run state = .error .revert := by
  have exactFailure := compilation_revert_iff (compiled x e first dst update second)
    (input x e first dst update second (represented.stack tail) capacity) rfl
  simpa only [show (program x e dst update).asserts = false from rfl,
    Bool.false_eq_true,false_and,or_false] using exactFailure

end Solidity.Backend.Passes.CapturedValueStability
/-- info: 'Solidity.Backend.Passes.CapturedValueStability.immediate_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.CapturedValueStability.immediate_failure
/-- info: 'Solidity.Backend.Passes.CapturedValueStability.failure_iff_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.CapturedValueStability.failure_iff_source
