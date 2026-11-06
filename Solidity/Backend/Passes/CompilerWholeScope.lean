import Solidity.Backend.Passes.CompilerCallScopeControls

/-! Concrete whole-program public recognition for the existing allocating
scoped-call fixture. This is intrinsic-program adequacy, not SourceSpec/world
or byte-level compiler completeness. -/
namespace Solidity.Backend.Passes.CompilerWholeScope
open Evm Evm.Memory Evm.Compiler MemoryCallControls
open MemoryCallScopeBoundary.Controls (scopeProgram suffix)

def program : Prog C [] Before := (allocate.join scopeProgram).join suffix
def rightProgram : Prog C [] Before := allocate.join (scopeProgram.join suffix)

theorem accepted_some : (Compiler.compile 1 (Frag.init []) program).isSome = true := by
  decide +kernel
@[irreducible] def actual : Compilation 1 (Frag.init []) program :=
  (Compiler.compile 1 (Frag.init []) program).get accepted_some

theorem accepted : Compiler.compile 1 (Frag.init []) program = some actual := by
  unfold actual
  exact (Option.some_get _).symm

theorem branch : actual.isMemoryCalls = true := by with_unfolding_all decide +kernel
theorem room : 1 + actual.requiredFrame ≤ 128 := by with_unfolding_all decide +kernel
theorem allocation_cost : actual.allocationCost initial = 8 := by with_unfolding_all decide +kernel
theorem free : Evm.Prog.pushes program = 0 := by decide +kernel

noncomputable def result : Solidity.Out C initial.H Before :=
  ⟨MemoryCallScopeBoundary.Controls.final.st,
    (first.ext.trans second.ext).trans MemoryCallScopeBoundary.Controls.final.ext⟩

theorem source_run : program.run initial = .ok result :=
  MemoryCallScopeBoundary.Controls.joined_source.1

theorem initial_input : actual.Input 1 128 base initial machine := by
  apply (actual.memoryCalls_input branch 1 128 base initial machine).mpr
  refine ⟨initial_repr.1,room,?_⟩
  rw [allocation_cost]
  exact .inr ⟨by decide,wmod 256,initial_repr.2,by decide +kernel⟩

theorem shared : ∃ (canonical : Machine) (selected : Nat → Fin W), canonical.stack = [] ∧ ∀ tail,
    run actual.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
    MappedOutput actual 1 128 base initial {machine with stack := tail}
      result.st {canonical with stack := tail} selected := by
  obtain ⟨canonical,selected,_,empty,runs⟩ := compilation_success_shared_mapped actual initial_input
    (by decide +kernel) source_run
  refine ⟨canonical,selected,empty,?_⟩
  intro tail
  simpa only [free,Nat.add_zero] using runs tail

theorem resources : ∃ (canonical : Machine) (selected : Nat → Fin W), canonical.stack = [] ∧ ∀ tail,
    run actual.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
    MappedOutput actual 1 128 base initial {machine with stack := tail}
      result.st {canonical with stack := tail} selected ∧
    StructAllocatorRepr result.st.heap selected 128 (wmod 264) {canonical with stack := tail} := by
  obtain ⟨canonical,selected,empty,runs⟩ := shared
  refine ⟨canonical,selected,empty,?_⟩
  intro tail
  have observed := (CompilerCallScopeRecognition.memory_calls_mapped_iff actual branch
    base selected initial {machine with stack := tail} result.st {canonical with stack := tail}).mp (runs tail).2
  have growth := observed.2.2
  rw [allocation_cost] at growth
  have allocated := growth (wmod 256) (by decide) (initial_repr.2.mem_eq rfl) (by decide +kernel)
  exact ⟨(runs tail).1,(runs tail).2,allocated⟩

theorem heap_objects : result.st.H.length = 4 := by with_unfolding_all decide +kernel

theorem compiler_join_codes_assoc {C : Contract} {b : Nat} {Γ Δ Ξ Ω : Ctx} (F : Frag Γ)
    (P : Prog C Γ Δ) (Q : Prog C Δ Ξ) (R : Prog C Ξ Ω) :
    (Compiler.compile b F ((P.join Q).join R)).map (·.code) =
      (Compiler.compile b F (P.join (Q.join R))).map (·.code) :=
  @congrArg (Prog C Γ Ω) (Option (List Instr)) ((P.join Q).join R) (P.join (Q.join R))
    (fun S : Prog C Γ Ω => (Compiler.compile b F S).map (·.code))
    (typed_sequencing_assoc P Q R)

theorem selected_code_associative :
    (Compiler.compile 1 (Frag.init []) program).map (·.code) =
      (Compiler.compile 1 (Frag.init []) rightProgram).map (·.code) :=
  compiler_join_codes_assoc (Frag.init []) allocate scopeProgram suffix

theorem right_selected_code : (Compiler.compile 1 (Frag.init []) rightProgram).map (·.code) = some actual.code := by
  rw [← selected_code_associative,accepted]
  rfl

theorem source_frame_strict : frameNeedProg program < actual.requiredFrame := by
  with_unfolding_all decide +kernel

theorem source_frame_refused {selected : Nat → Fin W} {state : State C []} {m : Machine} :
    ¬ actual.Input 1 (1+frameNeedProg program) selected state m := by
  intro h
  have bound := ((actual.memoryCalls_input branch 1 (1+frameNeedProg program) selected state m).mp h).2.1
  have strict := source_frame_strict
  omega

end Solidity.Backend.Passes.CompilerWholeScope
