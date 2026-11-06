import Solidity.Backend.Passes.SignedWidthGuard
import Solidity.Backend.Passes.MappedSequence
import Solidity.Backend.Passes.TailLoop

/-! Materialize the existing intrinsic signed operand in a fresh local BEFORE
the signed guard. The guard rereads that local, not the original expression.
This is a pass application, not effectful Source/frontend lowering. -/
namespace Solidity.Backend.Passes.SignedWidthCapture
open Backend.Scalar
variable {C : Contract} {Γ : Ctx}

def localOperand : Val C (.val .int :: Γ) .int := .simple (.local .here)

def localCode (b : Nat) (F : Evm.Frag Γ) :
    Evm.Memory.CompiledVal b (F.push (.val .int) .ok) (localOperand : Val C _ .int) :=
  ⟨_,.core _ rfl⟩

def program (w : Fin 32) (x : Var) (operand : Val C Γ .int) :
    Prog C Γ (.val .int :: Γ) :=
  .cons (.declLocal .int x (some operand))
    (.cons (.require (SignedWidthGuard.condition w localOperand)) .nil)

def compiled {b : Nat} {F : Evm.Frag Γ} (w : Fin 32) (x : Var)
    (operand : Val C Γ .int) (given : Evm.Memory.CompiledVal b F operand) :
    Evm.Compiler.Compilation b F (program w x operand) :=
  let condition := SignedWidthGuard.compiled w localOperand (localCode b F)
  .memory ⟨F.push (.val .int) .ok,
    (given.code ++ [.mstore (Evm.cell (b+Γ.length))]) ++
      ((condition.code ++ Evm.assertTop) ++ []),
    .cons (.declare F x operand given.code given.cert)
      (.cons (.require _ _ _ condition.cert) (.nil _))⟩

theorem input {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (x : Var) (operand : Val C Γ .int)
    (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (represented : Evm.Memory.StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) :
    (compiled w x operand given).Input L frame base state machine := by
  refine ⟨represented,?_,Or.inl rfl⟩
  change b + max (max Γ.length (max (Γ.length+1) 0))
    (max (max (Γ.length+1) (max (Γ.length+1) 0)) (Γ.length+1)) ≤ frame
  omega

theorem source (w : Fin 32) (x : Var) (operand : Val C Γ .int)
    (state : State C Γ) (value : PrimTy.int.Denote)
    (evaluated : operand.evalT state = .ok value) :
    (program w x operand).run state =
      if signedFits w value then
        .ok ⟨state.push (t := .val .int) value,List.prefix_refl _⟩ else .error .revert := by
  have captured : (Stmt.declLocal .int x (some operand)).run state =
      .ok ⟨state.push (t := .val .int) value,List.prefix_refl _⟩ := by
    change TRun.declLocal .int (some operand) state = _
    simp only [TRun.declLocal,evaluated,bind,Except.bind,pure,Except.pure]
  rw [program,Prog.run_cons_ok captured,
    SignedWidthGuard.require_source w localOperand _ value rfl]
  cases signedFits w value <;> rfl

/-- Original whole Input and the suffix Input are derived, not assumed
preservation facts. The reached map is the SAME actual address map. -/
theorem execution {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (x : Var) (operand : Val C Γ .int)
    (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (represented : Evm.Memory.StateRepr L b frame F state base machine)
    (value : PrimTy.int.Denote) (evaluated : operand.evalT state = .ok value)
    (capacity : b+(Γ.length+1) ≤ frame) (tail : List Evm.Word) :
    ∃ word, Evm.ReprV .int value word ∧
      (compiled w x operand given).Input L frame base state {machine with stack := tail} ∧
      Evm.run (given.code ++ [.mstore (Evm.cell (b+Γ.length))])
        {machine with stack := tail} =
        .ok (Evm.Memory.writeMachine {machine with stack := tail}
          (Evm.cell (b+Γ.length)) word) 0 ∧
      Evm.Memory.StateRepr L b frame (F.push (.val .int) .ok)
        (state.push (t := .val .int) value) base
        (Evm.Memory.writeMachine {machine with stack := tail}
          (Evm.cell (b+Γ.length)) word) ∧
      (SignedWidthGuard.requireStage w localOperand (localCode b F)).Input L frame base
        (state.push (t := .val .int) value)
        (Evm.Memory.writeMachine {machine with stack := tail}
          (Evm.cell (b+Γ.length)) word) ∧
      Evm.run (compiled w x operand given).code {machine with stack := tail} =
        (if signedFits w value then
          .ok (Evm.Memory.writeMachine {machine with stack := tail}
            (Evm.cell (b+Γ.length)) word) 0 else .revert) ∧
      (signedFits w value = true →
        MappedOutput (compiled w x operand given) L frame base state {machine with stack := tail}
          (state.push (t := .val .int) value)
          (Evm.Memory.writeMachine {machine with stack := tail}
            (Evm.cell (b+Γ.length)) word) base) := by
  rcases given.cert.correct (represented.stack tail) with
    ⟨actual,word,evaluation,repr,target⟩ | ⟨failed,_⟩
  · have equal : actual = value := Except.ok.inj (evaluation.symm.trans evaluated)
    cases equal
    have capture :
        Evm.run (given.code ++ [.mstore (Evm.cell (b+Γ.length))])
          {machine with stack := tail} =
        .ok (Evm.Memory.writeMachine {machine with stack := tail}
          (Evm.cell (b+Γ.length)) word) 0 := by
      rw [Evm.run_append_ok target]
      rfl
    have reached := (represented.stack tail).consVal value word repr capacity
    have guard := SignedWidthGuard.require_target w localOperand (localCode b F)
      reached value rfl tail
    refine ⟨word,repr,input w x operand given (represented.stack tail) capacity,
      capture,reached,SignedWidthGuard.require_input w localOperand (localCode b F)
        reached capacity,?_,?_⟩
    · change Evm.run ((given.code ++ [.mstore (Evm.cell (b+Γ.length))]) ++
        (SignedWidthGuard.requireStage w localOperand (localCode b F)).code) _ = _
      rw [Evm.run_append_ok capture]
      exact guard
    · intro accepted
      refine ⟨reached,Evm.Memory.BaseExtends.refl base,?_⟩
      intro cursor hb allocator space
      exact allocator.localWrite (b+Γ.length) (by omega) (by omega) word
  · rw [evaluated] at failed
    cases failed

end Solidity.Backend.Passes.SignedWidthCapture
/-- info: 'Solidity.Backend.Passes.SignedWidthCapture.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthCapture.input
/-- info: 'Solidity.Backend.Passes.SignedWidthCapture.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthCapture.source
/-- info: 'Solidity.Backend.Passes.SignedWidthCapture.execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthCapture.execution

namespace Solidity.Backend.Passes.SignedWidthCapture
open Backend.Scalar
variable {C : Contract} {Γ : Ctx}

/-- The captured word is selected ONCE before all saved tails. Equality comes
from the same actual successful capture run, never merely from Rep. The raw
tail law is used only on that successful prefix, not on a faulting program. -/
theorem execution_shared {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (x : Var) (operand : Val C Γ .int)
    (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (represented : Evm.Memory.StateRepr L b frame F state base machine)
    (value : PrimTy.int.Denote) (evaluated : operand.evalT state = .ok value)
    (capacity : b+(Γ.length+1) ≤ frame) :
    ∃ word, Evm.ReprV .int value word ∧ ∀ tail,
      (compiled w x operand given).Input L frame base state {machine with stack := tail} ∧
      Evm.run (given.code ++ [.mstore (Evm.cell (b+Γ.length))])
        {machine with stack := tail} =
        .ok (Evm.Memory.writeMachine {machine with stack := tail}
          (Evm.cell (b+Γ.length)) word) 0 ∧
      Evm.Memory.StateRepr L b frame (F.push (.val .int) .ok)
        (state.push (t := .val .int) value) base
        (Evm.Memory.writeMachine {machine with stack := tail}
          (Evm.cell (b+Γ.length)) word) ∧
      (SignedWidthGuard.requireStage w localOperand (localCode b F)).Input L frame base
        (state.push (t := .val .int) value)
        (Evm.Memory.writeMachine {machine with stack := tail}
          (Evm.cell (b+Γ.length)) word) ∧
      Evm.run (compiled w x operand given).code {machine with stack := tail} =
        (if signedFits w value then
          .ok (Evm.Memory.writeMachine {machine with stack := tail}
            (Evm.cell (b+Γ.length)) word) 0 else .revert) ∧
      (signedFits w value = true →
        MappedOutput (compiled w x operand given) L frame base state {machine with stack := tail}
          (state.push (t := .val .int) value)
          (Evm.Memory.writeMachine {machine with stack := tail}
            (Evm.cell (b+Γ.length)) word) base) := by
  obtain ⟨word,repr,_,emptyRun,_,_,_,_⟩ :=
    execution w x operand given represented value evaluated capacity []
  refine ⟨word,repr,?_⟩
  intro tail
  have stable := run_tail (given.code ++ [.mstore (Evm.cell (b+Γ.length))])
    {machine with stack := []} tail (by rw [emptyRun]; intro impossible; cases impossible)
  have common :
      Evm.run (given.code ++ [.mstore (Evm.cell (b+Γ.length))])
        {machine with stack := tail} =
        .ok (Evm.Memory.writeMachine {machine with stack := tail}
          (Evm.cell (b+Γ.length)) word) 0 := by
    simpa only [emptyRun,appendTail,appendOut,Evm.Memory.writeMachine,List.nil_append] using stable
  obtain ⟨actual,actualRep,wholeInput,captured,reached,guardInput,wholeRun,output⟩ :=
    execution w x operand given represented value evaluated capacity tail
  have machines := (Evm.Out.ok.inj (captured.symm.trans common)).1
  have words : actual = word := by
    have equal := congrArg (fun m : Evm.Machine => m.mem (Evm.cell (b+Γ.length))) machines
    simpa only [Evm.Memory.writeMachine,Evm.upd_same] using equal
  cases words
  exact ⟨wholeInput,captured,reached,guardInput,wholeRun,output⟩

end Solidity.Backend.Passes.SignedWidthCapture
/-- info: 'Solidity.Backend.Passes.SignedWidthCapture.execution_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthCapture.execution_shared

namespace Solidity.Backend.Passes.SignedWidthCapture
open Backend.Scalar
variable {C : Contract} {Γ : Ctx}

theorem operand_failure {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (x : Var) (operand : Val C Γ .int)
    (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (represented : Evm.Memory.StateRepr L b frame F state base machine)
    (failed : operand.evalT state = .error .revert) (tail : List Evm.Word) :
    (program w x operand).run state = .error .revert ∧
    Evm.run (compiled w x operand given).code {machine with stack := tail} = .revert := by
  constructor
  · change TRun.seq (TRun.declLocal .int (some operand)) _ state = _
    simp only [TRun.seq,TRun.declLocal,failed,bind,Except.bind]
  · have target := (value_revert_iff given represented tail).mpr failed
    change Evm.run ((given.code ++ [.mstore (Evm.cell (b+Γ.length))]) ++
      (SignedWidthGuard.requireStage w localOperand (localCode b F)).code) _ = _
    exact Evm.run_append_revert (Evm.run_append_revert target)

theorem failure_cases {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (x : Var) (operand : Val C Γ .int)
    (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (represented : Evm.Memory.StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) (tail : List Evm.Word) :
    Evm.run (compiled w x operand given).code {machine with stack := tail} = .revert ↔
      operand.evalT state = .error .revert ∨
      ∃ value, operand.evalT state = .ok value ∧ signedFits w value = false := by
  constructor
  · intro failed
    rcases given.cert.correct (represented.stack tail) with
      ⟨value,word,evaluated,repr,target⟩ | ⟨failedOperand,_⟩
    · obtain ⟨actual,_,_,_,_,_,whole,_⟩ :=
        execution w x operand given represented value evaluated capacity tail
      refine .inr ⟨value,evaluated,?_⟩
      cases fits : signedFits w value with
      | false => rfl
      | true => rw [fits] at whole; rw [whole] at failed; cases failed
    · exact .inl failedOperand
  · rintro (failed | ⟨value,evaluated,outside⟩)
    · exact (operand_failure w x operand given represented failed tail).2
    · obtain ⟨actual,_,_,_,_,_,whole,_⟩ :=
        execution w x operand given represented value evaluated capacity tail
      simpa only [outside,Bool.false_eq_true,ite_false] using whole

theorem failure_iff_source {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (x : Var) (operand : Val C Γ .int)
    (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (represented : Evm.Memory.StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) (tail : List Evm.Word) :
    Evm.run (compiled w x operand given).code {machine with stack := tail} = .revert ↔
      (program w x operand).run state = .error .revert := by
  rcases given.cert.correct (represented.stack tail) with
    ⟨value,word,evaluated,repr,target⟩ | ⟨failedOperand,_⟩
  · obtain ⟨actual,_,_,_,_,_,whole,_⟩ :=
      execution w x operand given represented value evaluated capacity tail
    rw [whole,source w x operand state value evaluated]
    cases signedFits w value <;> simp only [Bool.false_eq_true,ite_false,ite_true,
      reduceCtorEq]
  · obtain ⟨source,target⟩ := operand_failure w x operand given represented failedOperand tail
    rw [source,target]
    constructor <;> intro ignored <;> rfl

theorem short_frame {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (x : Var) (operand : Val C Γ .int)
    (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (short : frame < b+(Γ.length+1)) :
    ¬ (compiled w x operand given).Input L frame base state machine := by
  intro accepted
  have capacity := accepted.2.1
  change b + max (max Γ.length (max (Γ.length+1) 0))
    (max (max (Γ.length+1) (max (Γ.length+1) 0)) (Γ.length+1)) ≤ frame at capacity
  omega

end Solidity.Backend.Passes.SignedWidthCapture
/-- info: 'Solidity.Backend.Passes.SignedWidthCapture.operand_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthCapture.operand_failure
/-- info: 'Solidity.Backend.Passes.SignedWidthCapture.failure_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthCapture.failure_cases
/-- info: 'Solidity.Backend.Passes.SignedWidthCapture.failure_iff_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthCapture.failure_iff_source
/-- info: 'Solidity.Backend.Passes.SignedWidthCapture.short_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthCapture.short_frame
