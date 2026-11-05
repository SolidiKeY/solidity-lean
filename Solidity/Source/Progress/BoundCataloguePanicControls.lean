import Solidity.Source.Progress.BoundCatalogue
import Solidity.Source.Progress.BoundParentPanicControls

/-! Inhabited catalogue consumers over an actual elaborated program. No
parameter/return/local frame equations are supplied to the public adapter;
elaboration derives them. Coverage omission and false body metadata refuse. -/
namespace Solidity.Source.Progress.BoundCataloguePanicControls
open EM Solidity.Lowering.P9 BoundParentPanicControls

theorem catalogue (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    BoundMemoryCatalogue (fun d=>d ∈ ([] : List Decl)) (globals p fixed) "C" [d] := by
  intro called member
  rcases List.mem_singleton.mp member with rfl
  refine ⟨by decide +kernel,ps,[Aty],ps,body,signature,?_,?_,rfl,?_,admitted⟩
  · rw [BoundParentPanicControls.dispatch];exact signature
  · rw [BoundParentPanicControls.dispatch];exact source_body
  · intro τ member
    rcases List.mem_singleton.mp member with rfl
    exact shape

theorem coverage : readyCoverage resolution [] [d] = true := by decide +kernel
theorem omitted_refused : readyCoverage resolution [] [] = false := by decide +kernel
theorem whole (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyProgramCalls resolution (globals p fixed) "C" :=
  bound_memory_program_calls resolution actual_elaboration (globals p fixed) rfl "C" [] [d]
    (checked p fixed) (catalogue p fixed) coverage

theorem inhabited (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (callInternal (globals p fixed) frame 20 d parameters [Aty]) ∧
    MemOK E seed.ty (L0 E,reached) := by
  have joint := whole p fixed frame rfl d signature declared parameters seed.ty 20
  have actual := joint.2 (L0 E,initial) ⟨entry_mem,parameters_ok⟩
  rw [call_run] at actual
  exact ⟨joint.1,actual⟩

theorem checked_expression (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (globals p fixed) frame 22 (.call d signature args)) ∧
    Hoare (MemOK E seed.ty) (evalE (globals p fixed) frame 22 (.call d signature args))
      (fun v y=>MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y=>MemOK E seed.ty y) :=
  bound_memory_expr_from_elaborate resolution actual_elaboration (globals p fixed) rfl "C" [] [d]
    (checked p fixed) (catalogue p fixed) frame rfl d signature (List.mem_cons_self) args
    (.cons rfl (.inl rfl) (.local _) (.cons rfl (.inr rfl) (.local _) .nil)) seed.ty 21

theorem caller_inhabited (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (globals p fixed) frame 22 (.call d signature args)) ∧
    MemOK E seed.ty (caller,reached) := by
  have actual := (checked_expression p fixed).2 (caller,initial) caller_mem
  rw [caller_run] at actual
  exact ⟨(checked_expression p fixed).1,actual⟩

def wrongBody : RBody E := {body with ps:=[]}
theorem false_metadata_refused :
    (Source.progOf E).body d ≠ some wrongBody := by
  rw [source_body]
  intro same
  have bad := congrArg RBody.ps (Option.some.inj same)
  change ps = [] at bad
  cases bad

theorem old_catalogue_refused (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ¬ReadyMemoryCatalogue (fun d=>d ∈ ([] : List Decl)) (globals p fixed) "C" [d] := by
  intro old
  obtain ⟨member,inputs,outputs,targetInputs,b,sourceSig,targetSig,actual,mods,defaults,ready⟩ :=
    old d List.mem_cons_self
  have out : outputs = [Aty] := congrArg Prod.snd (Option.some.inj (sourceSig.symm.trans signature))
  subst outputs
  exact old_default_refused (defaults Aty List.mem_cons_self)

#print axioms catalogue
#print axioms coverage
#print axioms omitted_refused
#print axioms whole
#print axioms inhabited
#print axioms checked_expression
#print axioms caller_inhabited
#print axioms false_metadata_refused
#print axioms old_catalogue_refused
end Solidity.Source.Progress.BoundCataloguePanicControls
