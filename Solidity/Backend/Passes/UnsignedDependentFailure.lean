import Solidity.Backend.Passes.UnsignedDependentCapture

/-! Immediate versus actually reached zero-divisor failure. No post-failure
machine/map is invented, and no raw faulting-code tail transport is used. -/
namespace Solidity.Backend.Passes.UnsignedDependentFailure
open Evm Evm.Memory Evm.Compiler Backend.PrimitivePackets.UnsignedDiv
open UnsignedDependentCapture
variable {C : Contract} {Γ : Ctx}

/-- The first failure requires neither a suffix Input nor a suffix success. -/
theorem immediate {b L frame : Nat} {F : Frag (modelContext Γ)} (qname rname : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (zero : state.env.2.1.val = 0) (tail : List Word) :
    (program qname rname).run state = .error .revert ∧
    run (code (C := C) b F qname rname).code {machine with stack := tail} = .revert := by
  have target := (selected_div_zero (represented.stack tail) zero).2
  have evaluated : (modelDiv C Γ).evalT state = .error .revert :=
    (value_revert_iff (selectedDiv b F) represented tail).mp target
  have statement : (Stmt.declLocal .uint qname (some (modelDiv C Γ))).run state = .error .revert := by
    change TRun.declLocal .uint (some (modelDiv C Γ)) state = _
    simp only [TRun.declLocal,evaluated,bind,Except.bind]
  have failed : (first (C := C) qname).run state = .error .revert := by
    rw [first,Prog.run_cons_error statement]
  refine ⟨?_,?_⟩
  · rw [program,DeferredSource.join_run]
    simp only [TRun.seq,failed]
  · rw [code_join,first_emitted]
    exact run_append_revert (run_append_revert target)

/-- Nonzero initial divisor and zero initial numerator make the SECOND
operation fail, after the real quotient capture and physical Input transport.
All prefix values/maps/machines are fixed before arbitrary caller tails. -/
theorem reached {b L frame : Nat} {F : Frag (modelContext Γ)} (qname rname : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+((modelContext Γ).length+2) ≤ frame)
    (divisor : state.env.2.1.val ≠ 0) (zero : state.env.1.val = 0) :
    (program qname rname).run state = .error .revert ∧
    ∃ q : Uint, q.val = state.env.1.val.tdiv state.env.2.1.val ∧
      (first qname).run state = .ok ⟨state.push (t := .val .uint) q,List.prefix_refl _⟩ ∧
      (second rname).run (state.push (t := .val .uint) q) = .error .revert ∧
      ∃ (mid : Machine) (midBase : Nat → Fin W), mid.stack = [] ∧ ∀ tail,
        run (firstCode (C := C) b F qname).code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
        MappedOutput (.memory (firstCode (C := C) b F qname)) L frame base state {machine with stack := tail}
          (state.push (t := .val .uint) q) {mid with stack := tail} midBase ∧
        (Compilation.memory (secondCode (C := C) b F qname rname)).Input L frame midBase
          (state.push (t := .val .uint) q) {mid with stack := tail} ∧
        run (secondCode (C := C) b F qname rname).code {mid with stack := tail} = .revert ∧
        run (code (C := C) b F qname rname).code {machine with stack := tail} = .revert := by
  obtain ⟨q,qval,firstSource,mid,midBase,empty,allRuns⟩ :=
    reached_prefix qname rname represented capacity divisor
  have target0 := (selected_mod_zero ((allRuns []).2.2.1.stack []) zero).2
  have evaluated : (modelMod C (.val .uint :: Γ)).evalT (state.push (t := .val .uint) q) = .error .revert :=
    (value_revert_iff (selectedMod b (firstCode (C := C) b F qname).frag) (allRuns []).2.2.1 []).mp target0
  have statement : (Stmt.declLocal .uint rname (some (modelMod C (.val .uint :: Γ)))).run
      (state.push (t := .val .uint) q) = .error .revert := by
    change TRun.declLocal .uint (some (modelMod C (.val .uint :: Γ))) _ = _
    simp only [TRun.declLocal,evaluated,bind,Except.bind]
  have secondSource : (second (C := C) (Γ := Γ) rname).run (state.push (t := .val .uint) q) = .error .revert := by
    rw [second,Prog.run_cons_error statement]
  refine ⟨?_,q,qval,firstSource,secondSource,mid,midBase,empty,?_⟩
  · rw [program,DeferredSource.join_run]
    simp only [TRun.seq,firstSource,secondSource,Except.map]
  · intro tail
    have target := (selected_mod_zero (allRuns tail).2.2.1 zero).2
    have suffix : run (secondCode (C := C) b F qname rname).code {mid with stack := tail} = .revert := by
      rw [second_emitted]
      exact run_append_revert target
    refine ⟨(allRuns tail).1,(allRuns tail).2.1,(allRuns tail).2.2,suffix,?_⟩
    rw [code_join,run_append_ok (allRuns tail).1]
    exact suffix

/-- Source panic payload at the actual captured operand locals, alongside
physical prefix/Input/failure witnesses. This is not Source declaration or
ABI lowering, and the coarse target revert does not carry those bytes. -/
theorem reached_source {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (sourceTail : Source.Locals E.layout Δ) (sourceState : Source.St E)
    {b L frame : Nat} {F : Frag (modelContext Γ)} (qname rname : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+((modelContext Γ).length+2) ≤ frame)
    (divisor : state.env.2.1.val ≠ 0) (zero : state.env.1.val = 0) :
    ∃ (q : Uint) (mid : Machine) (midBase : Nat → Fin W),
      q.val = state.env.1.val.tdiv state.env.2.1.val ∧
      (first qname).run state = .ok ⟨state.push (t := .val .uint) q,List.prefix_refl _⟩ ∧
      mid.stack = [] ∧ ∀ tail,
      run (firstCode (C := C) b F qname).code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput (.memory (firstCode (C := C) b F qname)) L frame base state {machine with stack := tail}
        (state.push (t := .val .uint) q) {mid with stack := tail} midBase ∧
      (Compilation.memory (secondCode (C := C) b F qname rname)).Input L frame midBase
        (state.push (t := .val .uint) q) {mid with stack := tail} ∧
      (Source.evalE G fr (fuel+3) (sourceMod E (.int Source.IntTy.u256 :: Δ))).run
        (sourceLocals q state.env.1 (.cons (sourceUInt E.layout state.env.2.1) sourceTail),sourceState) =
        (.error (.revert (Source.panicData .divZero)),
          (sourceLocals q state.env.1 (.cons (sourceUInt E.layout state.env.2.1) sourceTail),sourceState)) ∧
      run (secondCode (C := C) b F qname rname).code {mid with stack := tail} = .revert ∧
      run (code (C := C) b F qname rname).code {machine with stack := tail} = .revert := by
  obtain ⟨_,q,qval,firstSource,_,mid,midBase,empty,allRuns⟩ := reached qname rname represented capacity divisor zero
  refine ⟨q,mid,midBase,qval,firstSource,empty,?_⟩
  intro tail
  have packet := remainder_zero_packet (allRuns tail).2.2.1.1 G fr fuel
    (.cons (sourceUInt E.layout state.env.2.1) sourceTail) sourceState zero
  exact ⟨(allRuns tail).1,(allRuns tail).2.1,(allRuns tail).2.2.1,
    packet.1,(allRuns tail).2.2.2.1,(allRuns tail).2.2.2.2⟩

/-- Exact internal coarse failure boundary. An intermediate zero quotient
alone is NOT a failure: the reached denominator is the original numerator. -/
theorem revert_iff {b L frame : Nat} {F : Frag (modelContext Γ)} (qname rname : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+((modelContext Γ).length+2) ≤ frame) (tail : List Word) :
    run (code (C := C) b F qname rname).code {machine with stack := tail} = .revert ↔
      state.env.2.1.val = 0 ∨ state.env.1.val = 0 := by
  constructor
  · intro target
    by_cases divisor : state.env.2.1.val = 0
    · exact .inl divisor
    by_cases numerator : state.env.1.val = 0
    · exact .inr numerator
    obtain ⟨q,r,_,_,_,mid,final,mb,ob,_,_,allRuns⟩ := success qname rname represented capacity divisor numerator
    rw [(allRuns tail).2.2.2.2.2.1] at target
    cases target
  · rintro (divisor | numerator)
    · exact (immediate qname rname represented divisor tail).2
    · by_cases divisor : state.env.2.1.val = 0
      · exact (immediate qname rname represented divisor tail).2
      obtain ⟨_,q,_,_,_,mid,mb,_,allRuns⟩ := reached qname rname represented capacity divisor numerator
      exact (allRuns tail).2.2.2.2

/-- info: 'Solidity.Backend.Passes.UnsignedDependentFailure.reached_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reached_source
/-- info: 'Solidity.Backend.Passes.UnsignedDependentFailure.immediate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms immediate
/-- info: 'Solidity.Backend.Passes.UnsignedDependentFailure.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reached
/-- info: 'Solidity.Backend.Passes.UnsignedDependentFailure.revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms revert_iff
end Solidity.Backend.Passes.UnsignedDependentFailure
