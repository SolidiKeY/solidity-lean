import Solidity.Source.Progress.ForwardingChain
import Solidity.Source.Progress.ForwardingControls

/-! The actual allocating/relay unit consumes a finite chain certificate.
Both base and added functions use the whole-unit theorem. Duplicate/value-list
overlap guards and omitted-function coverage remain explicit negative controls. -/
namespace Solidity.Source.Progress.ForwardingChainControls
open EM Solidity.Lowering.P9 ForwardingControls

theorem fresh_guard : forwardFresh [] [leafDecl] relayDecl = true := by decide +kernel
theorem duplicate_guard : forwardFresh [] [relayDecl,leafDecl] relayDecl = false := by decide +kernel
theorem value_overlap_guard : forwardFresh [relayDecl] [leafDecl] relayDecl = false := by decide +kernel

theorem chain (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ForwardingChain resolution (glob p fixed) "Memory" [] [relayDecl,leafDecl] :=
  .extend (.ready (leaf_catalogue p fixed)) relayDecl [U] Aty (by decide +kernel) fresh_guard
    relay_signature relayExpr same (.inr rfl) (.memory (.array _)) relay_ready
    (by rw [relay_dispatch]; exact relay_body.trans (congrArg some relay_flat))

theorem coverage : readyCoverage resolution [] [relayDecl,leafDecl] = true := by decide +kernel
theorem relay_omitted : readyCoverage resolution [] [leafDecl] = false := by decide +kernel
theorem leaf_omitted : readyCoverage resolution [] [relayDecl] = false := by decide +kernel

theorem registered (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ∀ called ∈ [relayDecl,leafDecl], called ∈ E.decls :=
  (chain p fixed).declared (value_check p fixed)

theorem whole (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyProgramCalls resolution (glob p fixed) "Memory" :=
  forwarding_chain_program_calls resolution actual_elaboration (glob p fixed) rfl "Memory" [] [relayDecl,leafDecl]
    (value_check p fixed) (chain p fixed) coverage

theorem relay_inhabited (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (callInternal (glob p fixed) frame 20 relayDecl arguments [Aty]) ∧
    MemOK E seed.ty ((.nil : Locals E.layout []),after) ∧
    RValOK E after.heap.ty (.val (.memRef rfl 3) : RVal E.layout Aty) := by
  have joint := whole p fixed frame rfl relayDecl relay_signature (by decide +kernel) arguments seed.ty 20
  have actual := joint.2 (.nil,initial) ⟨initial_mem,trivial,trivial⟩
  rw [success_run] at actual
  exact ⟨joint.1,actual⟩

def leafAfter : St E := {initial with heap := ((seed.alloc ⟨Aty,empty⟩).1.alloc ⟨Aty,fresh⟩).1}

theorem leaf_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 20 leafDecl arguments [Aty]).run (.nil,initial) =
      (.ok (.val (.memRef rfl 2)),(.nil,leafAfter)) := by
  rw [←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem leaf_inhabited (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (callInternal (glob p fixed) frame 20 leafDecl arguments [Aty]) ∧
    MemOK E seed.ty ((.nil : Locals E.layout []),leafAfter) ∧
    RValOK E leafAfter.heap.ty (.val (.memRef rfl 2) : RVal E.layout Aty) := by
  have joint := whole p fixed frame rfl leafDecl leaf_signature (by decide +kernel) arguments seed.ty 20
  have actual := joint.2 (.nil,initial) ⟨initial_mem,trivial,trivial⟩
  rw [leaf_run] at actual
  exact ⟨joint.1,actual⟩

theorem complete_composition (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (n : Nat) :
    CompositionAt (fun d => d ∈ ([] : List Decl)) (glob p fixed) "Memory" (WholeProgram.functions resolution) n :=
  forwarding_chain_composition resolution actual_elaboration (glob p fixed) rfl "Memory" [] [relayDecl,leafDecl]
    (value_check p fixed) (chain p fixed) coverage n

theorem expression_admitted :
    ComposedExpr (fun d => d ∈ ([] : List Decl)) (fun d => d ∈ WholeProgram.functions resolution) expression :=
  .call relay_signature (by decide +kernel) (.cons _ (.inl rfl) (.base (.local _)) .nil)

theorem caller_success (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 20 expression) ∧
    MemOK E seed.ty (caller,after) ∧ RValOK E after.heap.ty (.val (.memRef rfl 3) : RVal E.layout Aty) := by
  have joint := (complete_composition p fixed 20).expr frame rfl expression expression_admitted seed.ty
  have actual := joint.2 (caller,initial) caller_mem
  rw [expression_run] at actual
  exact ⟨joint.1,actual⟩

theorem caller_panic (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    MemOK E seed.ty (hugeCaller,stopped) := by
  have joint := (complete_composition p fixed 20).expr frame rfl expression expression_admitted seed.ty
  have actual := joint.2 (hugeCaller,initial) huge_caller_mem
  rw [caller_panic_run] at actual
  exact actual

#print axioms chain
#print axioms registered
#print axioms whole
#print axioms relay_inhabited
#print axioms leaf_inhabited
#print axioms complete_composition
#print axioms caller_success
#print axioms caller_panic
#print axioms duplicate_guard
#print axioms value_overlap_guard
#print axioms relay_omitted
#print axioms leaf_omitted
end Solidity.Source.Progress.ForwardingChainControls
