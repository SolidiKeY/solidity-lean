import Solidity.Backend.Passes.MappedTail

/-! A returned memory reference is read through the ACTUAL selected output map,
including when the compiled program allocates it. No stale-map identity is
assumed for new objects. Programs, states and references remain intrinsic. -/
namespace Solidity.Backend.Passes.ReturnedMemoryCapture
open Evm Evm.Memory Evm.Compiler

variable {C : Contract} {b L frame : Nat} {Γ Δ : Ctx} {R : RefTy}
  {F : Frag Γ} {P : Prog C Γ (.mem R :: Δ)}

theorem readback (compiled : CompiledProg b F P)
    (accepted : Memory.compileProg b F P = some compiled)
    {base : Nat → Fin W} {state : State C Γ} {machine : Machine}
    {out : Solidity.Out C state.H (.mem R :: Δ)}
    (input : (Compilation.memory compiled).Input L frame base state machine)
    (free : Evm.Prog.pays P = false) (success : P.run state = .ok out)
    (reference : HRef out.st.H R) (bound : TEnv.get .here out.st.env = some reference) :
    Memory.compileProg b F P = some compiled ∧
    ∃ (canonical : Machine) (selected : Nat → Fin W), canonical.stack = [] ∧ ∀ tail,
      (Compilation.memory compiled).Input L frame base state {machine with stack := tail} ∧
      run compiled.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput (.memory compiled) L frame base state {machine with stack := tail}
        out.st {canonical with stack := tail} selected ∧
      canonical.mem (cell (b+Δ.length)) = .val (selected reference.id) ∧
      run (compiled.code ++ [.mload (cell (b+Δ.length))]) {machine with stack := tail} =
        .ok ({canonical with stack := tail}.push (.val (selected reference.id))) 0 := by
  obtain ⟨canonical,selected,_,empty,runs⟩ :=
    compilation_success_shared_mapped (.memory compiled) input free success
  refine ⟨accepted,canonical,selected,empty,?_⟩
  intro tail
  obtain ⟨target,mapped⟩ := runs tail
  rw [compiled.cert.pushes_zero,Nat.add_zero] at mapped
  obtain ⟨actual,localRead,word⟩ := mapped.1.pointers (.here : Idx (.mem R :: Δ) (.mem R))
  rw [bound] at localRead
  have same : actual = reference := Option.some.inj localRead.symm
  subst actual
  have physical : canonical.mem (cell (b+Δ.length)) = .val (selected reference.id) := by
    simpa only [cellOf,lvl_here] using word
  have load : run [.mload (cell (b+Δ.length))] {canonical with stack := tail} =
      .ok ({canonical with stack := tail}.push (.val (selected reference.id))) 0 := by
    change Evm.Out.ok ({canonical with stack := tail}.push (canonical.mem (cell (b+Δ.length)))) 0 = _
    rw [physical]
  exact ⟨compilation_input_stack (.memory compiled) input tail,target,mapped,physical,
    (run_append_ok (c₂ := [.mload (cell (b+Δ.length))]) target).trans load⟩

/-- The current internal terminal compiler certificate does not emit an
intrinsic revertWith result. This is not a byte-erasure or ABI theorem. -/
theorem excludes_revert_with (compiled : CompiledProg b F P)
    {base : Nat → Fin W} {state : State C Γ} {machine : Machine}
    (input : (Compilation.memory compiled).Input L frame base state machine)
    (free : Evm.Prog.pays P = false) (data : List UInt8) :
    P.run state ≠ .error (.revertWith data) := by
  intro failed
  rcases compilation_exact (.memory compiled) input free with
    ⟨out,final,source,rest⟩ | ⟨source,rest⟩ | ⟨source,rest⟩
  · rw [failed] at source
    cases source
  · rcases source with source | ⟨_,source⟩
    · rw [failed] at source
      cases source
    · rw [failed] at source
      cases source
  · rw [failed] at source
    cases source

/-- info: 'Solidity.Backend.Passes.ReturnedMemoryCapture.readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readback
/-- info: 'Solidity.Backend.Passes.ReturnedMemoryCapture.excludes_revert_with' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms excludes_revert_with
end Solidity.Backend.Passes.ReturnedMemoryCapture
