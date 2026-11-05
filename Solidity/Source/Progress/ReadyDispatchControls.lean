import Solidity.Source.Progress.ReadyCatalogue
import Solidity.Lowering.P9.OverrideControls

/-! Nonidentity dispatch consumes the elaboration-derived ready catalogue.
These primitive-return bodies are deliberately placed in the ready catalogue
to exercise its selected-target metadata derivation, rather than the old value
branch. The call-expression node is intrinsic over a legacy-elaborated unit. -/
namespace Solidity.Source.Progress.ReadyDispatchControls
open EM Solidity.Lowering.P9.OverrideControls

theorem empty_value_check (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    Solidity.Lowering.P9.WholeProgram.check resolution (glob p fixed) "Derived" [] = true := rfl

theorem target_ready :
    ReadyItems (fun d => d ∈ ([] : List Decl)) derivedBody.rs derivedBody.inModifier derivedBody.items :=
  .stmt (.value (by decide +kernel) (by change True; trivial)) .nil

theorem admitted (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyMemoryCatalogue (fun d => d ∈ ([] : List Decl)) (glob p fixed) "Derived" [baseDecl,derivedDecl] := by
  intro called member
  rcases List.mem_cons.mp member with rfl | last
  · refine ⟨by decide +kernel,[],[.bool],[],derivedBody,base_sig,?_,?_,rfl,?_,target_ready⟩
    · rw [selected_override]; exact derived_sig
    · rw [selected_override]; exact derived_body
    · intro τ member
      rcases List.mem_singleton.mp member with rfl
      exact .value (by decide +kernel)
  · rcases List.mem_singleton.mp last with rfl
    refine ⟨by decide +kernel,[],[.bool],[],derivedBody,derived_sig,?_,?_,rfl,?_,target_ready⟩
    · rw [derived_dispatch]; exact derived_sig
    · rw [derived_dispatch]; exact derived_body
    · intro τ member
      rcases List.mem_singleton.mp member with rfl
      exact .value (by decide +kernel)

theorem coverage : readyCoverage resolution [] [baseDecl,derivedDecl] = true := by decide +kernel

theorem whole (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyProgramCalls resolution (glob p fixed) "Derived" :=
  ready_memory_program_calls resolution actual_elaboration (glob p fixed) rfl "Derived" [] [baseDecl,derivedDecl]
    (empty_value_check p fixed) (admitted p fixed) coverage

def initial : St resolution.env where
  ex := ⟨⟨fun _ => Account.empty _⟩,Transient.empty,[]⟩
  heap := Heap.empty
  events := []
  logs := [(⟨17,by decide⟩,[9])]
  fnLocals := ⟨[.bool],.cons (.bool true) .nil⟩
def caller : Locals resolution.env.layout [.bool] := .cons (.bool false) .nil

theorem initial_mem : MemOK resolution.env initial.heap.ty (caller,initial) :=
  ⟨⟨⟨HeapOK.empty,HeapTy.Le.refl _⟩,trivial,trivial⟩,HeapShaped.empty,HeapInner.empty⟩

theorem expression_joint (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 12 call) ∧
    Hoare (MemOK resolution.env initial.heap.ty) (evalE (glob p fixed) frame 12 call)
      (fun v y => MemOK resolution.env initial.heap.ty y ∧ RValOK resolution.env y.2.heap.ty v)
      (fun _ y => MemOK resolution.env initial.heap.ty y) :=
  ready_memory_expr_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Derived" []
    [baseDecl,derivedDecl] (empty_value_check p fixed) (admitted p fixed) frame rfl baseDecl base_sig
    (by decide +kernel) .nil .nil initial.heap.ty 11

theorem inhabited (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (glob p fixed).dispatchFn "Derived" baseDecl ≠ baseDecl ∧
    NS (evalE (glob p fixed) frame 12 call) ∧
    MemOK resolution.env initial.heap.ty (caller,initial) ∧
    RValOK resolution.env initial.heap.ty (.val (.bool true) : RVal resolution.env.layout .bool) := by
  have checked := expression_joint p fixed
  have actual := checked.2 (caller,initial) initial_mem
  have run : (evalE (glob p fixed) frame 12 call).run (caller,initial) =
      (.ok (.val (.bool true)),(caller,initial)) := calls_override p fixed initial
  rw [run] at actual
  exact ⟨dispatch_differs p fixed,checked.1,actual⟩

#print axioms whole
#print axioms expression_joint
#print axioms inhabited
end Solidity.Source.Progress.ReadyDispatchControls
