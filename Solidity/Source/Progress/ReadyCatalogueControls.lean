import Solidity.Source.Progress.ReadyCatalogue
import Solidity.Source.Progress.ReadyBodyControls
import Solidity.Source.Progress.ReadyProgramControls

/-! Consumers of ready catalogues with elaboration-derived frame metadata.
Actual nested allocation, reference-parameter identity and mixed value/memory
units consume the public theorem at inhabited inputs. Supplied call-expression
nodes remain intrinsic controls over these elaborated programs. -/
namespace Solidity.Source.Progress.ReadyCatalogueControls
open EM ReadyBodyControls

theorem catalogue (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyMemoryCatalogue (fun d => d ∈ ([] : List Decl)) (glob p fixed) "Memory" [d] := by
  intro called member
  rcases List.mem_singleton.mp member with rfl
  refine ⟨by decide +kernel,[U],[Aty],[U],flatBody,signature,?_,?_,rfl,?_,fragment⟩
  · rw [ReadyBodyControls.dispatch]; exact signature
  · rw [ReadyBodyControls.dispatch]; exact source_body
  · intro τ member
    rcases List.mem_singleton.mp member with rfl
    exact .memory (.array _)

theorem coverage : readyCoverage resolution [] [d] = true := by decide +kernel
theorem omitted_refused : readyCoverage resolution [] [] = false := by decide +kernel

theorem whole (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyProgramCalls resolution (glob p fixed) "Memory" :=
  ready_memory_program_calls resolution actual_elaboration (glob p fixed) rfl "Memory" [] [d]
    (value_check p fixed) (catalogue p fixed) coverage

theorem inhabited (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (callInternal (glob p fixed) frame 30 d arguments [Aty]) ∧
    MemOK E seed.ty ((.nil : Locals E.layout []),after) ∧
    RValOK E after.heap.ty (.val (.memRef rfl 4) : RVal E.layout Aty) := by
  have checked := whole p fixed frame rfl d signature (by decide +kernel) arguments seed.ty 30
  have actual := checked.2 (.nil,initial) ⟨entry_mem,trivial,trivial⟩
  rw [run] at actual
  exact ⟨checked.1,actual⟩

theorem halted (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (callInternal (glob p fixed) frame 30 d huge [Aty]) ∧
    NS (callInternal (glob p fixed) frame 8 d arguments [Aty]) ∧
    MemOK E seed.ty ((.nil : Locals E.layout []),stopped) := by
  have panic := whole p fixed frame rfl d signature (by decide +kernel) huge seed.ty 30
  have timeout := whole p fixed frame rfl d signature (by decide +kernel) arguments seed.ty 8
  have hp := panic.2 (.nil,initial) ⟨entry_mem,trivial,trivial⟩
  have ht := timeout.2 (.nil,initial) ⟨entry_mem,trivial,trivial⟩
  rw [panic_run] at hp
  rw [timeout_run] at ht
  exact ⟨panic.1,timeout.1,⟨ht.1,hp.2.1,hp.2.2⟩⟩

theorem expression_context (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 31 expression) :=
  ((whole p fixed).expr_context frame rfl 31).val expression
    (by decide) (by change True ∧ True; decide)

theorem expression_joint (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 31 expression) ∧
    Hoare (MemOK E seed.ty) (evalE (glob p fixed) frame 31 expression)
      (fun v y => MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E seed.ty y) :=
  ready_memory_expr_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] [d]
    (value_check p fixed) (catalogue p fixed) frame rfl d signature (by decide +kernel) args
    (.cons _ (.inl rfl) (.local _) .nil) seed.ty 30

theorem restored (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 31 expression) ∧
    MemOK E seed.ty (caller,after) ∧
    RValOK E after.heap.ty (.val (.memRef rfl 4) : RVal E.layout Aty) := by
  have checked := expression_joint p fixed
  have actual := checked.2 (caller,initial) caller_mem
  rw [expression_run] at actual
  exact ⟨checked.1,actual⟩

def inventedBody : RBody E where
  ps := [U]; rs := [Aty]; inModifier := false
  locals := []; out := []; items := .nil

theorem invented_frame_refused (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (glob p fixed).prog.body ((glob p fixed).dispatchFn "Memory" d) ≠ some inventedBody := by
  rw [ReadyBodyControls.dispatch]
  have selected : (glob p fixed).prog.body d = some flatBody := source_body
  rw [selected]
  intro same
  have locals := congrArg RBody.locals (Option.some.inj same)
  cases locals

#print axioms whole
#print axioms inhabited
#print axioms halted
#print axioms expression_context
#print axioms expression_joint
#print axioms restored
#print axioms invented_frame_refused
end Solidity.Source.Progress.ReadyCatalogueControls

namespace Solidity.Source.Progress.ReadyCatalogueIdentityControls
open EM Preservation.MemoryProgramControls

theorem catalogue (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyMemoryCatalogue (fun d => d ∈ ([] : List Decl)) (glob p fixed) "Memory" [d] := by
  intro called member
  rcases List.mem_singleton.mp member with rfl
  refine ⟨by decide +kernel,[Aty],[Aty],[Aty],flatBody,signature,?_,?_,rfl,?_,?_⟩
  · rw [Preservation.MemoryProgramControls.dispatch]; exact signature
  · rw [Preservation.MemoryProgramControls.dispatch]; exact source_body
  · intro τ member
    rcases List.mem_singleton.mp member with rfl
    exact .memory (.array _)
  · exact .stmt (.returnValue rfl _ (.inr rfl) (.local _)) .nil

theorem whole (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyProgramCalls resolution (glob p fixed) "Memory" :=
  ready_memory_program_calls resolution actual_elaboration (glob p fixed) rfl "Memory" [] [d]
    (value_check p fixed) (catalogue p fixed) (by decide +kernel)

theorem inhabited (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (callInternal (glob p fixed) frame 20 d arguments [Aty]) ∧
    MemOK E seed.ty ((.nil : Locals E.layout []),after) ∧
    RValOK E after.heap.ty (.val (.memRef rfl 0) : RVal E.layout Aty) := by
  have checked := whole p fixed frame rfl d signature (by decide +kernel) arguments seed.ty 20
  have actual := checked.2 (.nil,initial) ⟨entry_mem,arguments_valid⟩
  rw [run] at actual
  exact ⟨checked.1,actual⟩

def caller : Locals E.layout [Aty] := .cons (.memRef rfl 0) .nil
def args : RConvArgs E [Aty] [Aty] := .cons (.local .here) (by decide +kernel) .nil
def expression : RExpr E [Aty] Aty := .call d signature args

theorem caller_mem : MemOK E seed.ty (caller,initial) :=
  Preservation.relocalize entry_mem caller ⟨⟨Aty,rfl,rfl⟩,trivial⟩

theorem expression_joint (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 21 expression) ∧
    Hoare (MemOK E seed.ty) (evalE (glob p fixed) frame 21 expression)
      (fun v y => MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E seed.ty y) :=
  ready_memory_expr_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] [d]
    (value_check p fixed) (catalogue p fixed) frame rfl d signature (by decide +kernel) args
    (.cons _ (.inr rfl) (.local _) .nil) seed.ty 20

theorem argument_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalConvArgs (glob p fixed) frame 20 args).run (caller,initial) =
      (.ok arguments,(caller,initial)) := by
  cases p <;> rfl

theorem expression_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 21 expression).run (caller,initial) =
      (.ok (.val (.memRef rfl 0)),(caller,after)) := by
  have restored :
      (sub .nil (callInternal (glob p fixed) frame 20 d arguments [Aty]) : EM E [Aty] _).run (caller,initial) =
        (.ok (.val (.memRef rfl 0),.nil),(caller,after)) := by
    unfold EM.sub
    dsimp only [ExceptT.run,ExceptT.mk]
    have actual := Preservation.MemoryProgramControls.run p fixed
    dsimp only [ExceptT.run] at actual
    rw [actual]
  unfold expression
  rw [evalE,Hoare.run_bind,argument_run]
  change (do
    let r ← (sub .nil (callInternal (glob p fixed) frame 20 d arguments [Aty]) : EM E [Aty] _)
    pure r.1).run (caller,initial) = _
  rw [Hoare.run_bind,restored]
  rfl

theorem alias_restored (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 21 expression) ∧
    MemOK E seed.ty (caller,after) ∧
    RValOK E after.heap.ty (.val (.memRef rfl 0) : RVal E.layout Aty) := by
  have checked := expression_joint p fixed
  have actual := checked.2 (caller,initial) caller_mem
  rw [expression_run] at actual
  exact ⟨checked.1,actual⟩

#print axioms expression_joint
#print axioms expression_run
#print axioms alias_restored

#print axioms whole
#print axioms inhabited
end Solidity.Source.Progress.ReadyCatalogueIdentityControls

namespace Solidity.Source.Progress.ReadyCatalogueMixedControls
open EM ReadyProgramControls

theorem catalogue (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyMemoryCatalogue (fun d => d ∈ [countDecl]) (glob p fixed) "Memory" [freshDecl] := by
  intro called member
  rcases List.mem_singleton.mp member with rfl
  refine ⟨by decide +kernel,[],[Aty],[],flatFresh,fresh_signature,?_,?_,rfl,?_,?_⟩
  · rw [fresh_dispatch]; exact fresh_signature
  · rw [fresh_dispatch]; exact fresh_body.trans (congrArg some fresh_flat)
  · intro τ member
    rcases List.mem_singleton.mp member with rfl
    exact .memory (.array _)
  · exact .stmt (.returnValue rfl _ (.inr rfl) expression_ready) .nil

theorem whole (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyProgramCalls resolution (glob p fixed) "Memory" :=
  ready_memory_program_calls resolution actual_elaboration (glob p fixed) rfl "Memory" [countDecl] [freshDecl]
    (value_check p fixed) (catalogue p fixed) coverage

theorem both_branches (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (NS (callInternal (glob p fixed) frame 20 countDecl (.nil : Vals E.layout []) [U]) ∧
      MemOK E seed.ty ((.nil : Locals E.layout []),initial)) ∧
    (NS (callInternal (glob p fixed) frame 20 freshDecl (.nil : Vals E.layout []) [Aty]) ∧
      MemOK E seed.ty ((.nil : Locals E.layout []),after) ∧
      RValOK E after.heap.ty (.val (.memRef rfl 2) : RVal E.layout Aty)) := by
  have scalar := whole p fixed frame rfl countDecl count_signature (by decide +kernel) .nil seed.ty 20
  have memory := whole p fixed frame rfl freshDecl fresh_signature (by decide +kernel) .nil seed.ty 20
  have hs := scalar.2 (.nil,initial) ⟨initial_mem,trivial⟩
  have hm := memory.2 (.nil,initial) ⟨initial_mem,trivial⟩
  rw [scalar_run] at hs
  rw [memory_run] at hm
  exact ⟨⟨scalar.1,hs.1⟩,memory.1,hm⟩

theorem memory_omitted : readyCoverage resolution [countDecl] [] = false := by decide +kernel
theorem value_omitted : readyCoverage resolution [] [freshDecl] = false := by decide +kernel

#print axioms whole
#print axioms both_branches
#print axioms memory_omitted
#print axioms value_omitted
end Solidity.Source.Progress.ReadyCatalogueMixedControls
