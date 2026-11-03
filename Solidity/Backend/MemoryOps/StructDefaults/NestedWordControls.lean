import Solidity.Backend.MemoryOps.StructDefaults.WordControls
import Solidity.Backend.MemoryOps.StructDefaults.NestedWord

namespace Solidity.Backend.MemoryOps.StructDefaults.NestedWordControls
open Semantics Evm Evm.Memory WordControls

def nestedName : Name := "Q{pair:P{tag:uint;child:bool[]};flag:bool}"
def layout : NestedLayout Controls.E Controls.name Controls.outerName
    pairName nestedName "tag" "child" "pair" "flag" :=
  ⟨WordControls.layout, Controls.actual_outer_layout, by decide +kernel, by decide⟩
def fields : DefaultFieldsPlan (structDef nestedName) :=
  DefaultFieldsPlan.consReference "pair" plan
    (DefaultFieldsPlan.consPrimitive "flag" .bool DefaultFieldsPlan.nil)
def nestedPlan : DefaultPlan (.struct nestedName) := DefaultPlan.struct nestedName fields

def completed : Source.EMState Controls.E [] :=
  ((Source.zeroVal (E := Controls.E) (Γ := []) 9 (.struct .memory Controls.outerName)).run Controls.state).2

theorem bridge_inhabited :
    let g := initial.heap.allocDefault (.struct nestedName) (by decide +kernel)
    ∃ (base' : Nat → Fin W) (mem : Nat → Evm.Word),
      run nestedPlan.code machine = .ok (({machine with mem := mem} : Machine).push
        (.val (wmod (128+nestedPlan.root)))) 0 ∧
      NestedAt completed 3 2 1 g.heap g.val layout ∧
      StateRepr 1 1 64 (Frag.init []) (initial.adopt g).1 base' {machine with mem := mem} ∧
      StructAllocatorRepr g.heap base' 64 ⟨128+nestedPlan.cost, by decide +kernel⟩
        {machine with mem := mem} := by
  obtain ⟨base', mem, represented, allocator, _, _, evaluated, _, relation, _, _⟩ :=
    source_nested_word Controls.state 0 initial layout nestedPlan bases (wmod 128) machine
      (by decide +kernel) initial_repr.1 initial_repr.2 (by decide) (by decide +kernel)
  exact ⟨base', mem, evaluated, relation, represented, allocator⟩

def observe : Evm.Out → Option (List Nat)
  | .ok m _ => (m.stack ++ [m.mem 0, m.mem 63] ++ (List.range 5).map (fun i => m.mem (128+i))).mapM
      (fun w => match w with | .val v => some v.val | .slot _ => none)
  | _ => none

theorem target_observation : observe (run nestedPlan.code machine) =
    some [131,77,133,99,0,0,128,129,0] := by decide +kernel

theorem exact_cost : nestedPlan.cost = 5 := rfl

/-- Refusal of the real target capacity premise, without a runtime halt claim. -/
def boundary : Fin W := wmod (W-5)
theorem capacity_refusal : ¬ (boundary.val + nestedPlan.cost < W) := by decide +kernel

theorem wrong_inner_pointer_refused : observe (run nestedPlan.code machine) ≠
    some [131,77,133,99,0,0,128,130,0] := by decide +kernel

#print axioms bridge_inhabited
#print axioms target_observation
#print axioms capacity_refusal
#print axioms wrong_inner_pointer_refused
end Solidity.Backend.MemoryOps.StructDefaults.NestedWordControls
