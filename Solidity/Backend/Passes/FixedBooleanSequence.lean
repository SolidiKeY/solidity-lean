import Solidity.Backend.Passes.ReferenceControls
import Solidity.Backend.Passes.MemoryCallControls
import Solidity.Backend.Passes.SharedPair

/-! One fixed runtime-Boolean conditional followed by selected-reference
capture/observation. Input provisioning is separate from the fixed receiver;
this is not ABI decoding or frontend correspondence. -/
namespace Solidity.Backend.Passes.FixedBooleanSequence
open Evm Evm.Memory Evm.Compiler
open Controls.Fixture
open ReferenceControls (Γb state branchThenRead initializeBool wrongOrder)
private abbrev A : RefTy := .array (.prim .uint)
abbrev Captured : Ctx := .val .uint :: Γb
abbrev Final : Ctx := .val .uint :: Captured
def initial : State C [] := State.init C
def initialBase : Nat → Fin W := fun _ => wmod 0
def initialMachine : Machine := MemoryCallControls.machine

def population : Memory.CompiledProg 1 (Frag.init []) ReachabilityControls.populatedBuilder :=
  (Memory.compileProg 1 _ ReachabilityControls.populatedBuilder).get (by decide +kernel)
def F : Frag Γ := Frag.init Γ
def BF : Frag Γb := F.push (.val .bool) .ok
theorem population_fragment : population.frag = F := by decide +kernel

def sourcePopulation : Solidity.Out C initial.H Γ := ⟨σ,⟨σ.H,rfl⟩⟩
theorem population_source : ReachabilityControls.populatedBuilder.run initial = .ok sourcePopulation :=
  ReachabilityControls.fresh_state_reaches_fixture

private def okMachine : Evm.Out → Option Machine
  | .ok m 0 => some m | _ => none
noncomputable def populatedTarget : Machine :=
  (okMachine (run population.code initialMachine)).get (by decide +kernel)
theorem population_target : run population.code initialMachine = .ok populatedTarget 0 := by
  have h : some populatedTarget = okMachine (run population.code initialMachine) := Option.some_get _
  generalize run population.code initialMachine = out at h ⊢
  cases out with
  | ok m skip =>
    cases skip with
    | zero => exact congrArg (fun m => Evm.Out.ok m 0) (Option.some.inj h).symm
    | succ n => cases h
  | revert => cases h
  | fault => cases h

theorem population_input : (Compilation.memory population).Input 1 128 initialBase initial initialMachine :=
  ⟨MemoryCallControls.initial_repr.1,by decide +kernel,
    .inr ⟨by decide,wmod 256,MemoryCallControls.initial_repr.2,by decide +kernel⟩⟩

theorem reached_population :
    ∃ mb, MappedOutput (.memory population) 1 128 initialBase initial initialMachine σ populatedTarget mb := by
  obtain ⟨m,ht,_,hr⟩ := compilation_success (.memory population) population_input
    (by decide +kernel) population_source
  have same : m = populatedTarget := (Evm.Out.ok.inj (ht.symm.trans population_target)).1
  subst m
  simpa only [show Evm.Prog.pushes ReachabilityControls.populatedBuilder = 0 from by decide +kernel,
    Nat.add_zero] using (mapped_output_iff (.memory population) _ _ _ _ _ _ _).mp hr

/-- Only input memory cell5 varies. Neither receiver nor consuming code takes b. -/
noncomputable def runtimeInput (b : Bool) : Machine :=
  writeMachine populatedTarget 5 (.val (bword b))
def initializer (b : Bool) : Memory.CompiledProg 1 F (initializeBool b) :=
  (Memory.compileProg 1 F (initializeBool b)).get (by rfl)
theorem initializer_fragment (b : Bool) : (initializer b).frag = BF := rfl

def receiver : Memory.CompiledProg 1 BF branchThenRead :=
  (Memory.compileProg 1 BF branchThenRead).get (by decide +kernel)

private abbrev selected : Idx Captured (.mem A) := .there (.there (.there .here))
def capturePrefix : Prog C Γb Captured :=
  .cons (.declLocal .uint (.user "captured") none)
  (.cons (.assignIncDec .here .postInc rfl
    (.mindex .dyn (.var selected rfl) (.lit 0 rfl)) rfl) .nil)
def observe : Prog C Captured Final :=
  .cons (.declLocal .uint (.user "observed")
    (some (.readMem (.index .dyn (.var selected rfl) (.simple (.lit 0 rfl)))))) .nil
def suffix : Prog C Γb Final := capturePrefix.join observe
def consumer : Memory.CompiledProg 1 receiver.frag suffix :=
  (Memory.compileProg 1 _ suffix).get (by decide +kernel)
def fixedProgram : Prog C Γb Final := branchThenRead.join suffix
def fixedCode : List Instr := receiver.code ++ consumer.code

private theorem middle_some (b : Bool) : (branchThenRead.run (state b)).toOption.isSome = true := by
  cases b <;> decide +kernel
noncomputable def middle (b : Bool) : Solidity.Out C (state b).H Γb :=
  (branchThenRead.run (state b)).toOption.get (middle_some b)
private theorem final_some (b : Bool) : (suffix.run (middle b).st).toOption.isSome = true := by
  cases b <;> decide +kernel
noncomputable def final (b : Bool) : Solidity.Out C (middle b).st.H Final :=
  (suffix.run (middle b).st).toOption.get (final_some b)

private theorem source_get {Γ Δ : Ctx} {τ : State C Γ} {P : Prog C Γ Δ}
    {o : Solidity.Out C τ.H Δ} (hx : some o = (P.run τ).toOption) : P.run τ = .ok o := by
  cases hs : P.run τ with
  | ok value => rw [hs] at hx; exact congrArg Except.ok (Option.some.inj hx).symm
  | error e => rw [hs] at hx; cases hx

theorem middle_source (b : Bool) : branchThenRead.run (state b) = .ok (middle b) :=
  source_get (Option.some_get (middle_some b))
theorem final_source (b : Bool) : suffix.run (middle b).st = .ok (final b) :=
  source_get (Option.some_get (final_some b))
theorem initialized_source (b : Bool) :
    (initializeBool b).run σ = .ok ⟨state b,List.prefix_refl _⟩ := by cases b <;> with_unfolding_all rfl

theorem runtime_input {mb : Nat → Fin W}
    (hp : MappedOutput (.memory population) 1 128 initialBase initial initialMachine σ populatedTarget mb)
    (b : Bool) :
    (Compilation.memory receiver).Input 1 128 mb (state b) (runtimeInput b) := by
  have repr : StateRepr 1 1 128 F σ mb populatedTarget := by
    simpa only [population_fragment] using hp.1
  exact ⟨repr.consVal (p := .bool) b (.val (bword b)) rfl (by decide +kernel),
    by decide +kernel,.inl (allocationCostProg_zero branchThenRead (by decide +kernel) (state b))⟩

theorem initializer_input {mb : Nat → Fin W}
    (hp : MappedOutput (.memory population) 1 128 initialBase initial initialMachine σ populatedTarget mb)
    (b : Bool) :
    (Compilation.memory (initializer b)).Input 1 128 mb σ populatedTarget := by
  have repr : StateRepr 1 1 128 F σ mb populatedTarget := by
    simpa only [population_fragment] using hp.1
  exact ⟨repr,by cases b <;> decide +kernel,.inl (by rfl)⟩

theorem joined_source (b : Bool) :
    fixedProgram.run (state b) = .ok ⟨(final b).st,(middle b).ext.trans (final b).ext⟩ := by
  rw [fixedProgram,DeferredSource.join_run]
  simp only [TRun.seq,middle_source,final_source,Except.map]

def addresses : List Nat := [0,127,1,2,3,4,5,6,7,256,257,258,259,260]
private def words (out : Evm.Out) : Option (List Nat) :=
  match out with
  | .ok m _ => (m.stack ++ addresses.map m.mem).mapM fun w =>
      match w with | .val v => some v.val | .slot _ => none
  | _ => none

theorem both_complete_target_vectors :
    words (run fixedCode {(runtimeInput true) with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,259,4,1,4,5,2,7,9,1,5] ∧
    words (run fixedCode {(runtimeInput false) with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,256,7,0,7,8,2,8,9,1,4] := by
  exact ⟨by decide +kernel,by decide +kernel⟩


theorem populated_stack : populatedTarget.stack = [] := by
  obtain ⟨m,ht,hstack,_⟩ := compilation_success (.memory population) population_input
    (by decide +kernel) population_source
  have same : m = populatedTarget := (Evm.Out.ok.inj (ht.symm.trans population_target)).1
  subst m
  exact hstack

/-- Generic machine parameter prevents unfolding the allocated target while
checking the actual initializer. Only the provisioning code depends on b. -/
theorem initialize_target (b : Bool) (m : Machine) :
    run (initializer b).code m = .ok (writeMachine m 5 (.val (bword b))) 0 := by
  cases b <;> rfl

/-- The Boolean is read from the caller's local by the SAME code in both
cases. Physical suffix Input consumes the receiver's actual selected map. -/
theorem shared {mb : Nat → Fin W}
    (hp : MappedOutput (.memory population) 1 128 initialBase initial initialMachine σ populatedTarget mb)
    (b : Bool) :
    ∃ (nb ob : Nat → Fin W) (mid out : Machine),
      fixedProgram.run (state b) = .ok ⟨(final b).st,(middle b).ext.trans (final b).ext⟩ ∧
      mid.stack = [] ∧ out.stack = [] ∧ ∀ tail,
        (Compilation.memory receiver).Input 1 128 mb (state b) {(runtimeInput b) with stack := tail} ∧
        run receiver.code {(runtimeInput b) with stack := tail} = .ok {mid with stack := tail} 0 ∧
        (Compilation.memory consumer).Input 1 128 nb (middle b).st {mid with stack := tail} ∧
        run consumer.code {mid with stack := tail} = .ok {out with stack := tail} 0 ∧
        run fixedCode {(runtimeInput b) with stack := tail} = .ok {out with stack := tail} 0 ∧
        MappedOutput (.memory receiver) 1 128 mb (state b) {(runtimeInput b) with stack := tail}
          (middle b).st {mid with stack := tail} nb ∧
        MappedOutput (.memory consumer) 1 128 nb (middle b).st {mid with stack := tail}
          (final b).st {out with stack := tail} ob := by
  have link : MappedBoundaryLink (.memory receiver) (.memory consumer) 1 128 mb (state b) (runtimeInput b) :=
    memory_nonallocating_mapped_link receiver consumer (by decide +kernel) (by decide +kernel)
  have empty : (runtimeInput b).stack = [] := by
    simpa only [runtimeInput,writeMachine] using populated_stack
  simpa only [show Evm.Prog.pushes branchThenRead = 0 from by decide +kernel,
    show Evm.Prog.pushes suffix = 0 from by decide +kernel,Nat.add_zero,fixedProgram,fixedCode] using
    compilation_pair_shared (C := C) (b := 1) (L := 1) (frame := 128)
      (Γ := Γb) (Δ := Γb) (Ξ := Final) (F := BF) (P := branchThenRead) (Q := suffix)
      (base := mb) (σ := state b) (m := runtimeInput b)
      (.memory receiver) (.memory consumer) (runtime_input hp b)
      empty link (by decide +kernel) (by decide +kernel) (middle_source b) (final_source b)

/-- Actual emitted allocation and input provisioning reach the SAME fixed
receiver/suffix. Only provisioning, not fixedCode, is specialized to b. -/
theorem fresh_target (b : Bool) : ∃ out : Machine, ∀ tail,
    run (population.code ++ ((initializer b).code ++ fixedCode))
      {initialMachine with stack := tail} = .ok {out with stack := tail} 0 := by
  obtain ⟨base,hp⟩ := reached_population
  obtain ⟨mb,nb,mid,out,_,_,_,hall⟩ := shared hp b
  refine ⟨out,?_⟩
  intro tail
  have first : run population.code {initialMachine with stack := tail} =
      .ok {populatedTarget with stack := tail} 0 := by
    have h := run_tail population.code initialMachine tail (by rw [population_target]; intro h; cases h)
    simpa only [population_target,appendOut,appendTail,show initialMachine.stack = [] from rfl,
      populated_stack,List.nil_append] using h
  have init : run (initializer b).code {populatedTarget with stack := tail} =
      .ok {(runtimeInput b) with stack := tail} 0 := by
    simpa only [runtimeInput,writeMachine] using initialize_target b {populatedTarget with stack := tail}
  rw [run_append_ok first,run_append_ok init]
  exact (hall tail).2.2.2.2.1

theorem fresh_source (b : Bool) :
    (ReachabilityControls.populatedBuilder.join ((initializeBool b).join fixedProgram)).run initial =
      .ok ⟨(final b).st,sourcePopulation.ext.trans
        ((List.prefix_refl _).trans ((middle b).ext.trans (final b).ext))⟩ := by
  exact (triple_source_success initial population_source (initialized_source b) (joined_source b)).2

/-- A real allocated state witnesses the premise for BOTH runtime values.
The same prefix map is selected before choosing the Boolean input. -/
theorem inhabited_inputs :
    ∃ mb, MappedOutput (.memory population) 1 128 initialBase initial initialMachine σ populatedTarget mb ∧
      ∀ b, (Compilation.memory receiver).Input 1 128 mb (state b) (runtimeInput b) := by
  obtain ⟨mb,hp⟩ := reached_population
  exact ⟨mb,hp,runtime_input hp⟩

theorem receiver_recognized :
    (Compiler.compile 1 BF branchThenRead).map (·.isMemory) = some true := by decide +kernel
theorem fixed_program_recognized :
    (Compiler.compile 1 BF fixedProgram).map (·.isMemory) = some true := by decide +kernel

end Solidity.Backend.Passes.FixedBooleanSequence
