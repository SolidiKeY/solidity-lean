import Solidity.Backend.Passes.UnsignedDependentFailure
import Solidity.Backend.Passes.MemoryScopeBoundary

/-! Scope exit after dependent quotient/remainder capture, followed by real
slot reuse. The public memory compiler selects both stages and their join.
Private words remain in memory but leave the intrinsic local context. -/
namespace Solidity.Backend.Passes.UnsignedDependentScope
open Evm Evm.Memory Evm.Compiler Backend.PrimitivePackets.UnsignedDiv
variable {C : Contract} {Γ : Ctx}

def blockProgram (qn rn : Var) : Prog C (modelContext Γ) (modelContext Γ) :=
  MemoryScopeBoundary.program (UnsignedDependentCapture.program qn rn)
def outer (b : Nat) (F : Frag (modelContext Γ)) (qn rn : Var) : CompiledProg b F (blockProgram (C := C) qn rn) :=
  MemoryScopeBoundary.compiled (UnsignedDependentCapture.code (C := C) b F qn rn)
def fortyTwo : Uint := ⟨42,by decide⟩

def reuse (name : Var) : Prog C (modelContext Γ) (.val .uint :: modelContext Γ) :=
  .cons (.declLocal .uint name (some (.simple (.lit 42 (by decide))))) .nil
def receiver (b : Nat) (F : Frag (modelContext Γ)) (qn rn name : Var) :
    CompiledProg b (outer (C := C) b F qn rn).frag (reuse (C := C) name) :=
  (Memory.compileProg b (outer (C := C) b F qn rn).frag (reuse name)).get (by rfl)
def joined (qn rn name : Var) := (blockProgram (C := C) (Γ := Γ) qn rn).join (reuse name)
def whole (b : Nat) (F : Frag (modelContext Γ)) (qn rn name : Var) :
    CompiledProg b F (joined (C := C) qn rn name) :=
  ⟨(receiver (C := C) b F qn rn name).frag,
    (UnsignedDependentCapture.code (C := C) b F qn rn).code ++ (receiver (C := C) b F qn rn name).code,
    .cons (.block (UnsignedDependentCapture.program qn rn) _ (UnsignedDependentCapture.code (C := C) b F qn rn).cert)
      (receiver (C := C) b F qn rn name).cert⟩

theorem block_stmt_selection (b : Nat) (F : Frag (modelContext Γ)) (qn rn : Var) :
    Memory.compileStmt (C := C) b F (.block (UnsignedDependentCapture.program qn rn)) =
      some (⟨(UnsignedDependentCapture.code (C := C) b F qn rn).frag.restrict (modelContext Γ),
        (UnsignedDependentCapture.code (C := C) b F qn rn).code,
        .block _ _ (UnsignedDependentCapture.code (C := C) b F qn rn).cert⟩ : CompiledStmt b F (.block (UnsignedDependentCapture.program qn rn))) := by
  change (do
    let result ← Memory.compileProg b F (UnsignedDependentCapture.program qn rn)
    pure (⟨result.frag.restrict (modelContext Γ),result.code,.block _ _ result.cert⟩ : CompiledStmt b F (.block (UnsignedDependentCapture.program qn rn)))) = _
  rw [UnsignedDependentCapture.public_selection]
  rfl

theorem block_selection (b : Nat) (F : Frag (modelContext Γ)) (qn rn : Var) :
    Memory.compileProg (C := C) b F (blockProgram qn rn) = some (outer (C := C) b F qn rn) := by
  simp only [blockProgram,MemoryScopeBoundary.program,Memory.compileProg,block_stmt_selection,bind,Option.bind,pure]
  rfl

theorem receiver_selection (b : Nat) (F : Frag (modelContext Γ)) (qn rn name : Var) :
    Memory.compileProg (C := C) b (outer (C := C) b F qn rn).frag (reuse name) = some (receiver (C := C) b F qn rn name) := by rfl

theorem whole_selection (b : Nat) (F : Frag (modelContext Γ)) (qn rn name : Var) :
    Memory.compileProg (C := C) b F (joined qn rn name) = some (whole (C := C) b F qn rn name) := by
  simp only [joined,blockProgram,MemoryScopeBoundary.program,Prog.join]
  rw [Memory.compileProg,block_stmt_selection]
  change (do
    let rest ← Memory.compileProg b (outer (C := C) b F qn rn).frag (reuse name)
    pure (⟨rest.frag,(UnsignedDependentCapture.code (C := C) b F qn rn).code ++ rest.code,
      .cons (.block _ _ (UnsignedDependentCapture.code (C := C) b F qn rn).cert) rest.cert⟩ :
      CompiledProg b F (.cons (.block (UnsignedDependentCapture.program qn rn)) (reuse name)))) = _
  rw [receiver_selection]
  rfl

theorem outer_boundary (b : Nat) (F : Frag (modelContext Γ)) (qn rn : Var) :
    outer (C := C) b F qn rn = MemoryScopeBoundary.compiled (UnsignedDependentCapture.code (C := C) b F qn rn) := by rfl

theorem emitted (b : Nat) (F : Frag (modelContext Γ)) (qn rn name : Var) :
    (outer (C := C) b F qn rn).code = (UnsignedDependentCapture.code (C := C) b F qn rn).code ∧
    (receiver (C := C) b F qn rn name).code = [.push w[42], .mstore (cell (b+(modelContext Γ).length))] ∧
    (whole (C := C) b F qn rn name).code = (outer (C := C) b F qn rn).code ++ (receiver (C := C) b F qn rn name).code := by
  refine ⟨?_,rfl,?_⟩
  · exact MemoryScopeBoundary.code _
  · simp only [whole,outer,MemoryScopeBoundary.code]

theorem dropped (state : State C (modelContext Γ)) (q r : Uint) (qn rn : Var) :
    ((state.push (t := .val .uint) q).push (t := .val .uint) r).drop
      (UnsignedDependentCapture.program (C := C) qn rn).ext = state := by rfl

theorem input {b L frame : Nat} {F : Frag (modelContext Γ)} (qn rn : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+((modelContext Γ).length+2) ≤ frame) :
    (Compilation.memory (outer (C := C) b F qn rn)).Input L frame base state machine :=
  MemoryScopeBoundary.input _ (UnsignedDependentCapture.whole_input qn rn represented capacity)

theorem whole_input {b L frame : Nat} {F : Frag (modelContext Γ)} (qn rn name : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+((modelContext Γ).length+2) ≤ frame) :
    (Compilation.memory (whole (C := C) b F qn rn name)).Input L frame base state machine := by
  have bodyPeak := (UnsignedDependentCapture.whole_input qn rn represented capacity).2.1
  change b+frameNeedProg (UnsignedDependentCapture.program (C := C) qn rn) ≤ frame at bodyPeak
  refine ⟨represented,?_,Or.inl rfl⟩
  change b+max (max (modelContext Γ).length (max (modelContext Γ).length
    (frameNeedProg (UnsignedDependentCapture.program (C := C) qn rn))))
    (max (max (modelContext Γ).length (max ((modelContext Γ).length+1) 0)) ((modelContext Γ).length+1)) ≤ frame
  omega

/-- The real dependent operations succeed before dropping their two locals.
The selected map and canonical machine are chosen before arbitrary saved tails;
full outputs and the receiver's Input hold for each reached tail. -/
theorem scope_success {b L frame : Nat} {F : Frag (modelContext Γ)} (qn rn name : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+((modelContext Γ).length+2) ≤ frame)
    (divisor : state.env.2.1.val ≠ 0) (numerator : state.env.1.val ≠ 0) :
    ∃ (q r : Uint), q.val = state.env.1.val.tdiv state.env.2.1.val ∧ r.val = q.val.tmod state.env.1.val ∧
      (blockProgram qn rn).run state = .ok ⟨state,List.prefix_refl _⟩ ∧
      ∃ (mid : Machine) (selected : Nat → Fin W), mid.stack = [] ∧ ∀ tail,
        run (outer (C := C) b F qn rn).code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
        MappedOutput (.memory (outer (C := C) b F qn rn)) L frame base state {machine with stack := tail}
          state {mid with stack := tail} selected ∧
        (Compilation.memory (receiver (C := C) b F qn rn name)).Input L frame selected state {mid with stack := tail} := by
  obtain ⟨q,r,qval,rval,source,_,mid,_,selected,_,empty,runs⟩ :=
    UnsignedDependentCapture.success qn rn represented capacity divisor numerator
  have native := MemoryScopeBoundary.source_success source
  change (blockProgram qn rn).run state = .ok ⟨state,List.prefix_refl _⟩ at native
  refine ⟨q,r,qval,rval,native,mid,selected,empty,?_⟩
  intro tail
  have body := (runs tail).2.2.2.2.2.2
  have out : MappedOutput (.memory (outer (C := C) b F qn rn)) L frame base state
      {machine with stack := tail} state {mid with stack := tail} selected :=
    MemoryScopeBoundary.output (UnsignedDependentCapture.code (C := C) b F qn rn) body
  refine ⟨?_,out,out.1,?_,Or.inl rfl⟩
  · rw [(emitted (C := C) b F qn rn name).1]
    exact (runs tail).2.2.2.2.2.1
  · change b+max (max (modelContext Γ).length (max ((modelContext Γ).length+1) 0)) ((modelContext Γ).length+1) ≤ frame
    omega

/-- Actual scope-to-receiver composition, including whole-program output.
The private quotient slot is reused by the newly declared 42; the dropped
remainder word is not claimed to be erased. -/
theorem reused {b L frame : Nat} {F : Frag (modelContext Γ)} (qn rn name : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+((modelContext Γ).length+2) ≤ frame)
    (divisor : state.env.2.1.val ≠ 0) (numerator : state.env.1.val ≠ 0) :
    (joined qn rn name).run state = .ok ⟨state.push (t := .val .uint) fortyTwo,List.prefix_refl _⟩ ∧
    ∃ (mid final : Machine) (selected next : Nat → Fin W), mid.stack = [] ∧ final.stack = [] ∧ ∀ tail,
      run (outer (C := C) b F qn rn).code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput (.memory (outer (C := C) b F qn rn)) L frame base state {machine with stack := tail}
        state {mid with stack := tail} selected ∧
      (Compilation.memory (receiver (C := C) b F qn rn name)).Input L frame selected state {mid with stack := tail} ∧
      run (receiver (C := C) b F qn rn name).code {mid with stack := tail} = .ok {final with stack := tail} 0 ∧
      MappedOutput (.memory (receiver (C := C) b F qn rn name)) L frame selected state {mid with stack := tail}
        (state.push (t := .val .uint) fortyTwo) {final with stack := tail} next ∧
      run (whole (C := C) b F qn rn name).code {machine with stack := tail} = .ok {final with stack := tail} 0 ∧
      MappedOutput (.memory (whole (C := C) b F qn rn name)) L frame base state {machine with stack := tail}
        (state.push (t := .val .uint) fortyTwo) {final with stack := tail} next := by
  obtain ⟨q,r,_,_,source,mid,selected,empty,runs⟩ := scope_success qn rn name represented capacity divisor numerator
  have suffix : (reuse (C := C) (Γ := Γ) name).run state =
      .ok ⟨state.push (t := .val .uint) fortyTwo,List.prefix_refl _⟩ := by rfl
  obtain ⟨final,next,_,finalEmpty,last⟩ := compilation_success_shared_mapped
    (.memory (receiver (C := C) b F qn rn name)) (runs []).2.2 rfl suffix
  refine ⟨?_,mid,final,selected,next,empty,finalEmpty,?_⟩
  · rw [joined,DeferredSource.join_run]
    simp only [TRun.seq,source,suffix,Except.map]
  · intro tail
    have out := (last tail).2
    rw [(receiver (C := C) b F qn rn name).cert.pushes_zero,Nat.add_zero] at out
    have wholeRun : run (whole (C := C) b F qn rn name).code {machine with stack := tail} = .ok {final with stack := tail} 0 := by
      rw [(emitted (C := C) b F qn rn name).2.2,run_append_ok (runs tail).1]
      exact (last tail).1
    refine ⟨(runs tail).1,(runs tail).2.1,(runs tail).2.2,(last tail).1,out,wholeRun,out.1,?_,?_⟩
    · intro R ref
      exact (out.2.1 ref).trans ((runs tail).2.1.2.1 ref)
    · exact GrowsAllocator.comp (runs tail).2.1.2.2 out.2.2

/-- A failed body never reaches the reused-slot declaration. Failure is the
existing internal terminal revert, not a claim about ABI payload bytes. -/
theorem failure {b L frame : Nat} {F : Frag (modelContext Γ)} (qn rn name : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+((modelContext Γ).length+2) ≤ frame) (tail : List Word) :
    run (whole (C := C) b F qn rn name).code {machine with stack := tail} = .revert ↔
      state.env.2.1.val = 0 ∨ state.env.1.val = 0 := by
  constructor
  · intro h
    by_cases divisor : state.env.2.1.val = 0
    · exact .inl divisor
    by_cases numerator : state.env.1.val = 0
    · exact .inr numerator
    obtain ⟨_,mid,final,selected,next,_,_,runs⟩ := reused qn rn name represented capacity divisor numerator
    rw [(runs tail).2.2.2.2.2.1] at h
    cases h
  · intro h
    have bad := (UnsignedDependentFailure.revert_iff qn rn represented capacity tail).mpr h
    rw [(emitted (C := C) b F qn rn name).2.2]
    apply run_append_revert
    rw [(emitted (C := C) b F qn rn name).1]
    exact bad

/-- Native scope failure and joined failure preserve the actual first/second
zero-divisor distinction. In either case the reuse suffix is unreachable. -/
theorem source_failure {b L frame : Nat} {F : Frag (modelContext Γ)} (qn rn name : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+((modelContext Γ).length+2) ≤ frame)
    (bad : state.env.2.1.val = 0 ∨ state.env.1.val = 0) :
    (blockProgram qn rn).run state = .error .revert ∧
    (joined qn rn name).run state = .error .revert := by
  have body : (UnsignedDependentCapture.program qn rn).run state = .error .revert := by
    by_cases divisor : state.env.2.1.val = 0
    · exact (UnsignedDependentFailure.immediate qn rn represented divisor []).1
    · have numerator := bad.resolve_left divisor
      exact (UnsignedDependentFailure.reached qn rn represented capacity divisor numerator).1
  have blockError : (blockProgram qn rn).run state = .error .revert :=
    (MemoryScopeBoundary.source_error .revert).mpr body
  refine ⟨blockError,?_⟩
  rw [joined,DeferredSource.join_run]
  simp only [TRun.seq,blockError]

/-- info: 'Solidity.Backend.Passes.UnsignedDependentScope.block_stmt_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms block_stmt_selection
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScope.block_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms block_selection
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScope.receiver_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms receiver_selection
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScope.whole_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms whole_selection
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScope.outer_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outer_boundary
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScope.emitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms emitted
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScope.dropped' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms dropped
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScope.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms input
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScope.whole_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms whole_input
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScope.scope_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scope_success
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScope.reused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reused
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScope.failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms failure
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScope.source_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_failure
end Solidity.Backend.Passes.UnsignedDependentScope
