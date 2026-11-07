import Solidity.Backend.Passes.DeferredCondition

/-! Exact internal failure alternatives for existing deferred Boolean operands.
Successful prefixes retain their actual private context and full selected map.
No failed execution has a fabricated post-state or public ABI observation. -/
namespace Solidity.Backend.Passes.DeferredConditionFailure
open Evm Evm.Memory Evm.Compiler
variable {C : Contract} {Γ : Ctx}
/-- Exact native failure stage; no state is returned by a failing stage. -/
theorem source_iff (operand : DeferredSource.Operand C Γ (.prim .bool))
    (state : State C Γ) (halt : THalt) :
    operand.run state = .error halt ↔
      operand.code.run state = .error halt ∨
      ∃ reached : Out C state.H operand.tailCtx,
        operand.code.run state = .ok reached ∧
        (DeferredCondition.expression operand).evalT reached.st = .error halt := by
  unfold DeferredSource.Operand.run
  rw [DeferredCondition.expression_source operand]
  simp only [Src.valueT]
  cases operand.code.run state with
  | error err =>
    simp only [bind,Except.bind,Except.error.injEq,reduceCtorEq,false_and,
      exists_false,or_false]
  | ok reached =>
    simp only [bind,Except.bind,reduceCtorEq,false_or,Except.ok.injEq,
      exists_eq_left']
    cases (DeferredCondition.expression operand).evalT reached.st with
    | error err => simp only [Except.error.injEq]
    | ok value => simp only [pure,Except.pure,reduceCtorEq]

/-- Exact reached physical alternatives for internal coarse revert. Immediate
failure needs no successful suffix; a reached read uses the actual output map. -/
theorem revert_witness_iff {b L frame : Nat} {F : Frag Γ}
    (operand : DeferredSource.Operand C Γ (.prim .bool))
    (code : CompiledProg b F operand.code)
    (reader : CompiledVal b code.frag (DeferredCondition.expression operand))
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (input : (Compilation.memory code).Input L frame base state machine)
    (free : Evm.Prog.pays operand.code = false) :
    run (code.code ++ reader.code) machine = .revert ↔
      ((operand.code.run state = .error .revert ∨
          (operand.code.asserts = true ∧ operand.code.run state = .error .panic)) ∧
        run code.code machine = .revert) ∨
      ∃ (reached : Out C state.H operand.tailCtx) (mid : Machine) (selected : Nat → Fin W),
        operand.code.run state = .ok reached ∧ run code.code machine = .ok mid 0 ∧
        MappedOutput (.memory code) L frame base state machine reached.st mid selected ∧
        StateRepr L b frame code.frag reached.st selected mid ∧
        (DeferredCondition.expression operand).evalT reached.st = .error .revert ∧
        run reader.code mid = .revert := by
  constructor
  · intro terminal
    rcases compilation_exact (.memory code) input free with
      ⟨reached,mid,source,emitted,_,rep⟩ | ⟨source,emitted⟩ | ⟨_,emitted⟩
    · obtain ⟨selected,mapped⟩ := (mapped_output_iff (.memory code) _ _ _ _ _ _ _).mp rep
      rw [code.cert.pushes_zero,Nat.add_zero] at mapped
      have emittedCode : run code.code machine = .ok mid 0 := emitted
      rw [run_append_ok emittedCode] at terminal
      exact .inr ⟨reached,mid,selected,source,emittedCode,mapped,mapped.1,
        (value_revert_iff reader mapped.1 mid.stack).mp terminal,terminal⟩
    · exact .inl ⟨source,emitted⟩
    · have emittedCode : run code.code machine = .fault := emitted
      have bad := run_append_fault (c₂ := reader.code) emittedCode
      rw [terminal] at bad
      cases bad
  · rintro (⟨_,emitted⟩ | ⟨reached,mid,selected,_,emitted,_,_,_,failed⟩)
    · exact run_append_revert emitted
    · rw [run_append_ok emitted]
      exact failed

/-- A successful real prefix fixes its map before ALL tails, including when
its final read reverts. run_tail is never applied to failing code. -/
theorem reached_shared {b L frame : Nat} {F : Frag Γ}
    (operand : DeferredSource.Operand C Γ (.prim .bool))
    (code : CompiledProg b F operand.code)
    (reader : CompiledVal b code.frag (DeferredCondition.expression operand))
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (input : (Compilation.memory code).Input L frame base state machine)
    (free : Evm.Prog.pays operand.code = false)
    (reached : Out C state.H operand.tailCtx)
    (source : operand.code.run state = .ok reached)
    (failed : (DeferredCondition.expression operand).evalT reached.st = .error .revert) :
    operand.run state = .error .revert ∧
    ∃ (canonical : Machine) (selected : Nat → Fin W), canonical.stack = [] ∧ ∀ tail,
      (Compilation.memory code).Input L frame base state {machine with stack := tail} ∧
      run code.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput (.memory code) L frame base state {machine with stack := tail}
        reached.st {canonical with stack := tail} selected ∧
      StateRepr L b frame code.frag reached.st selected {canonical with stack := tail} ∧
      run reader.code {canonical with stack := tail} = .revert ∧
      run (code.code ++ reader.code) {machine with stack := tail} = .revert := by
  refine ⟨(source_iff operand state .revert).mpr (.inr ⟨reached,source,failed⟩),?_⟩
  obtain ⟨canonical,selected,_,empty,runs⟩ :=
    compilation_success_shared_mapped (.memory code) input free source
  refine ⟨canonical,selected,empty,?_⟩
  intro tail
  have mapped := (runs tail).2
  rw [code.cert.pushes_zero,Nat.add_zero] at mapped
  have bad : run reader.code {canonical with stack := tail} = .revert :=
    (value_revert_iff reader mapped.1 tail).mpr failed
  have emitted : run code.code {machine with stack := tail} =
      .ok {canonical with stack := tail} 0 := (runs tail).1
  refine ⟨compilation_input_stack (.memory code) input tail,emitted,mapped,mapped.1,bad,?_⟩
  rw [run_append_ok emitted]
  exact bad

/-- Two-sided native terminal adequacy for this accepted prefix/value pair.
Panic retains the prefix asserts guard; no ABI-byte interpretation follows. -/
theorem revert_iff {b L frame : Nat} {F : Frag Γ}
    (operand : DeferredSource.Operand C Γ (.prim .bool))
    (code : CompiledProg b F operand.code)
    (reader : CompiledVal b code.frag (DeferredCondition.expression operand))
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (input : (Compilation.memory code).Input L frame base state machine)
    (free : Evm.Prog.pays operand.code = false) :
    run (code.code ++ reader.code) machine = .revert ↔
      operand.run state = .error .revert ∨
      (operand.code.asserts = true ∧ operand.run state = .error .panic) := by
  constructor
  · intro ht
    rcases (revert_witness_iff operand code reader input free).mp ht with
      ⟨hs | ⟨guard,hs⟩,_⟩ | ⟨reached,mid,selected,hs,_,_,_,failed,_⟩
    · exact .inl ((source_iff operand state .revert).mpr (.inl hs))
    · exact .inr ⟨guard,(source_iff operand state .panic).mpr (.inl hs)⟩
    · exact .inl ((source_iff operand state .revert).mpr (.inr ⟨reached,hs,failed⟩))
  · rintro (native | ⟨guard,native⟩)
    · rcases (source_iff operand state .revert).mp native with hs | ⟨reached,hs,failed⟩
      · have emitted : run code.code machine = .revert :=
          (compilation_revert_iff (.memory code) input free).mpr (.inl hs)
        exact run_append_revert emitted
      · obtain ⟨mid,emitted,_,rep⟩ := compilation_success (.memory code) input free hs
        obtain ⟨selected,full⟩ := (mapped_output_iff (.memory code) _ _ _ _ _ _ _).mp rep
        rw [code.cert.pushes_zero,Nat.add_zero] at full
        have codeRun : run code.code machine = .ok mid 0 := emitted
        rw [run_append_ok codeRun]
        exact (value_revert_iff reader full.1 mid.stack).mpr failed
    · rcases (source_iff operand state .panic).mp native with hs | ⟨reached,hs,failed⟩
      · have emitted : run code.code machine = .revert :=
          (compilation_revert_iff (.memory code) input free).mpr (.inr ⟨guard,hs⟩)
        exact run_append_revert emitted
      · obtain ⟨mid,_,_,rep⟩ := compilation_success (.memory code) input free hs
        obtain ⟨selected,full⟩ := (mapped_output_iff (.memory code) _ _ _ _ _ _ _).mp rep
        rw [code.cert.pushes_zero,Nat.add_zero] at full
        rcases reader.cert.correct full.1 with ⟨_,_,evaluated,_,_⟩ | ⟨evaluated,_⟩
        · rw [failed] at evaluated
          cases evaluated
        · rw [failed] at evaluated
          cases evaluated

end Solidity.Backend.Passes.DeferredConditionFailure

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.source_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.source_iff

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.revert_witness_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.revert_witness_iff

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.reached_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.reached_shared

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.revert_iff
