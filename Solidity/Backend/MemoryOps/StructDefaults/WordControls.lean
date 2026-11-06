import Solidity.Backend.MemoryOps.StructDefaults.Controls
import Solidity.Backend.MemoryOps.StructDefaults.Word
import Solidity.Evm.Correct

namespace Solidity.Backend.MemoryOps.StructDefaults.WordControls
open Semantics Evm Evm.Memory

def pairName : Name := "P{tag:uint;child:bool[]}"
def C : Contract := {vars := []}
def layout : SourceBoolStructLayout Controls.E Controls.name pairName "tag" "child" :=
  ⟨rfl, by decide +kernel, by decide⟩
def fields : DefaultFieldsPlan (structDef pairName) :=
  DefaultFieldsPlan.consPrimitive "tag" .uint
    (DefaultFieldsPlan.consReference "child" (DefaultPlan.array .bool) DefaultFieldsPlan.nil)
def plan : DefaultPlan (.struct pairName) := DefaultPlan.struct pairName fields

def bases : Nat → Fin W := fun _ => wmod 0
def initial : State C [] := State.init C
def machine : Machine :=
  {Machine.init with stack := [w[77]], mem := fun a =>
    if a = 0 then w[128] else if a = 63 then w[99] else w[0]}

private theorem noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?

/-- Intrinsic and word input premises share an actual empty heap and free tail. -/
theorem initial_repr : StateRepr 1 1 64 (Frag.init []) initial bases machine ∧
    StructAllocatorRepr initial.heap bases 64 (wmod 128) machine := by
  have hh : HeapRepr initial.heap bases 64 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hs : StructHeapRepr initial.heap bases 64 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hx : StructArraySeparated initial.heap bases := fun _ r => (noRef r).elim
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
  refine ⟨⟨?_, hh, ?_, by decide, hs, hx, ?_⟩, ⟨⟨hh, ?_, fun r => (noRef r).elim⟩, hs, hx,
    fun r => (noRef r).elim⟩⟩
  · refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
    · intro p i; nomatch i
    · intro R i hi; nomatch i
    · intro R i hi; nomatch i
  · intro R i; nomatch i
  · intro s f R r hf
    exact (noRef r).elim
  · refine ⟨by decide, by decide, rfl, ?_⟩
    intro a ha
    change 128 ≤ a at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · rfl


theorem bridge_inhabited :
    let g := initial.heap.allocDefault (.struct pairName) (by decide +kernel)
    ∃ (base' : Nat → Fin W) (mem : Nat → Evm.Word),
      run plan.code machine = .ok (({machine with mem := mem} : Machine).push
        (.val (wmod (128+plan.root)))) 0 ∧
      PairAt Controls.completed 2 1 g.heap g.val layout ∧
      StateRepr 1 1 64 (Frag.init []) (initial.adopt g).1 base' {machine with mem := mem} ∧
      StructAllocatorRepr g.heap base' 64 ⟨128+plan.cost, by decide +kernel⟩
        {machine with mem := mem} := by
  obtain ⟨base', mem, represented, allocator, _, _, evaluated, _, relation, _, _⟩ :=
    source_pair_word Controls.state 0 initial layout plan bases (wmod 128) machine
      (by decide +kernel) initial_repr.1 initial_repr.2 (by decide) (by decide +kernel)
  exact ⟨base', mem, evaluated, relation, represented, allocator⟩

def observe : Evm.Out → Option (List Nat)
  | .ok m _ => (m.stack ++ [m.mem 0, m.mem 63, m.mem 128, m.mem 129, m.mem 130]).mapM
      (fun w => match w with | .val v => some v.val | .slot _ => none)
  | _ => none

theorem target_observation : observe (run plan.code machine) =
    some [129,77,131,99,0,0,128] := by decide +kernel

theorem exact_cost : plan.cost = 3 := rfl

/-- This refutes the actual bridge capacity premise, not a runtime revert. -/
def boundary : Fin W := wmod (W-3)
theorem capacity_refusal : ¬ (boundary.val + plan.cost < W) := by decide +kernel

theorem wrong_child_pointer_refused : observe (run plan.code machine) ≠
    some [129,77,131,99,0,0,129] := by decide +kernel

#print axioms bridge_inhabited
#print axioms target_observation
#print axioms capacity_refusal
#print axioms wrong_child_pointer_refused
end Solidity.Backend.MemoryOps.StructDefaults.WordControls
