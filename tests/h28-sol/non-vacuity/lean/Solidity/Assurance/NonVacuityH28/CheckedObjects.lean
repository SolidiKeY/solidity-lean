import Solidity.Assurance.NonVacuityH28.MemoryInputs

/-! Nonempty object heaps for additional existing checked compiler contracts. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics

/-- Transport helper only. Clients below construct Input, pay and source-run
premises; no implication from an assumed contradiction is used as a witness. -/
theorem checked_success_after_source {C : Contract} {Γ Δ : Ctx} {P : Prog C Γ Δ}
    {F : Evm.Frag Γ} {b L frame : Nat} (result : Evm.Compiler.Compilation b F P)
    {base : Nat → Fin Evm.W} {σ : State C Γ} {mc : Evm.Machine} {o : Out C σ.H Δ}
    (input : result.Input L frame base σ mc) (hpay : Evm.Prog.pays P = false)
    (hs : Prog.run σ P = .ok o) :
    ∃ mc', Evm.run result.code mc = .ok mc' 0 ∧ mc'.stack = mc.stack ∧
      result.Rep (L + Evm.Prog.pushes P) frame base σ mc o.st mc' := by
  rcases Main.compiler_checked result input with
    ⟨o', mc', ho, ht, hstack, hr⟩ | ⟨he, _⟩ | ⟨hp, _⟩ | ⟨hd, _⟩
  · have heq : (Except.ok o' : TRes (Out C σ.H Δ)) = .ok o := ho.symm.trans hs
    cases heq
    exact ⟨mc', ht, hstack, hr⟩
  · rcases he with he | ⟨_, he⟩
    · have hbad : (Except.ok o : TRes (Out C σ.H Δ)) = .error .revert := hs.symm.trans he
      cases hbad
    · have hbad : (Except.ok o : TRes (Out C σ.H Δ)) = .error .panic := hs.symm.trans he
      cases hbad
  · have hbad : false = true := hpay.symm.trans hp
    cases hbad
  · have hbad : (Except.ok o : TRes (Out C σ.H Δ)) = .error .diverge := hs.symm.trans hd
    cases hbad

variable (C : Contract)

def constructionResult : Evm.Memory.Construction.CompiledProg 1 (Evm.Frag.init []) (primitiveAllocation C) :=
  (Evm.Memory.Construction.compileProg 1 (Evm.Frag.init []) (primitiveAllocation C)).get (by rfl)

def constructionCompiled : Evm.Compiler.Compilation 1 (Evm.Frag.init []) (primitiveAllocation C) :=
  .construction (constructionResult C)

theorem construction_input :
    (constructionCompiled C).Input 1 128 memoryBases (memorySource C) memoryMachine := by
  refine ⟨fresh_object_state C, ?_, ?_⟩
  · change 2 ≤ 128
    decide +kernel
  · refine .inr ⟨by decide, Evm.wmod 256, fresh_object_allocator C, ?_⟩
    change 256 + 2 < Evm.W
    decide +kernel

theorem construction_joint :
    ∃ mc' base', Evm.run (constructionCompiled C).code memoryMachine = .ok mc' 0 ∧
      mc'.stack = memoryMachine.stack ∧
      Evm.Memory.Objects.StateRepr 1 1 128 (constructionResult C).frag
        (primitiveOutcome C).st base' mc' := by
  obtain ⟨mc', ht, hstack, hr⟩ := checked_success_after_source (constructionCompiled C)
    (construction_input C) rfl (primitive_source_eq C)
  obtain ⟨base', hstate, _, _⟩ := hr
  exact ⟨mc', base', ht, hstack, hstate⟩

/-- The represented pointer is an actual typed reference, not a free word. -/
theorem construction_live_pointer :
    ∃ mc' : Evm.Machine, ∃ base' : Nat → Fin Evm.W,
      ∃ r : HRef (primitiveOutcome C).st.H (.array (.prim .uint)),
      Evm.run (constructionCompiled C).code memoryMachine = .ok mc' 0 ∧
      mc'.stack = memoryMachine.stack ∧
      TEnv.get .here (primitiveOutcome C).st.env = some r ∧
      mc'.mem (Evm.cellOf 1 (.here : Idx [.mem (.array (.prim .uint))] (.mem (.array (.prim .uint))))) = .val (base' r.id) ∧
      128 ≤ (base' r.id).val := by
  obtain ⟨mc', base', ht, hstack, hstate⟩ := construction_joint C
  obtain ⟨r, hr, hp⟩ := hstate.pointers (.here : Idx [.mem (.array (.prim .uint))] (.mem (.array (.prim .uint))))
  exact ⟨mc', base', r, ht, hstack, hr, hp, hstate.heap.owner.above r⟩

end Solidity.Assurance.NonVacuityH28
