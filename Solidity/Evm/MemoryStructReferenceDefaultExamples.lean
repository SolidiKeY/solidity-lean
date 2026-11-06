import Solidity.Evm.Compiler
import Solidity.Syntax.Splice

/-! Inhabited finite reference-member default construction through the public compiler. -/
namespace Solidity.Evm.Memory.StructReferenceDefaultExamples
open Semantics
def C : Contract := contract!{
  struct Leaf { uint n; bool flag; }
  struct Holder { Leaf leaf; uint[] items; bool marker; }
  struct Wrapper { Holder holder; uint own; }
}
local instance : InContract := ⟨C⟩
def bases : Nat → Fin W := fun _ => wmod 0
def initial : State C [] := State.init C
def machine : Machine :=
  {Machine.init with stack := [w[77]], mem := fun a =>
    if a = 0 then w[128] else if a = 63 then w[99] else w[0]}

private theorem noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?

/-- Source and machine input premises share an actual empty heap and free tail. -/
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

private def program := (sol{
  Wrapper memory first;
  Wrapper memory same = first;
  require(first.holder.leaf.n == 0 && !first.holder.leaf.flag && first.holder.items.length == 0);
  require(!first.holder.marker && first.own == 0);
  first.holder.leaf.n = 7;
  Leaf memory saved = first.holder.leaf;
  Holder memory fresh;
  fresh.leaf.n = 9;
  first.holder = fresh;
  require(same.holder.leaf.n == 9 && saved.n == 7);
  Wrapper memory second;
  second.holder.leaf.flag = true;
  require(first.holder.leaf.n == 9 && !first.holder.leaf.flag);
  first = second;
  require(same.holder.leaf.n == 9 && first.holder.leaf.flag && saved.n == 7);
} : Prog C [] _)
private def compiled : Compiler.Compilation 1 (Frag.init []) program :=
  (Compiler.compile 1 (Frag.init []) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem program_cost : allocationCostProg program initial = 22 := by decide +kernel

theorem compiled_input : compiled.Input 1 64 bases initial machine := by
  apply (compiled.memory_input (by decide +kernel) 1 64 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 128, initial_repr.2, by decide +kernel⟩⟩

theorem compiled_agrees : compiled.Agrees 1 64 bases initial machine := compiled.correct compiled_input

def observeTarget : Out → Option (List Nat)
  | .ok m _ => do
    let words := m.stack ++ [m.mem 0, m.mem 63] ++ (List.range 23).map (fun i => m.mem (128 + i))
    words.mapM fun w => match w with | .val v => some v.val | .slot _ => none
  | _ => none

theorem target_observation : observeTarget (run compiled.code machine) =
    some [77,150,99,7,0,0,128,130,0,139,0,9,0,0,136,138,0,0,1,0,142,144,0,145,0,0] := by
  decide +kernel

private def refAt? (H : HTy) (i : Nat) (R : RefTy) : Option (HRef H R) :=
  if h : H[i]? = some R then some ⟨i, h⟩ else none
private def leafName : Name := (C.structName? "Leaf").getD ""
def observeSource {Δ : Ctx} : TRes (Solidity.Out C [] Δ) → Option (List Int)
  | .ok o => do
    let leaves ← [0,4,7].mapM fun i => do
      let r ← refAt? o.st.H i (.struct leafName)
      let flag : Bool := o.st.heap.field (T := .prim .bool) r (f := "flag") rfl
      pure [(o.st.heap.field r (f := "n") rfl).1, if flag then 1 else 0]
    let lens ← [1,5,8].mapM fun i => do
      let r ← refAt? o.st.H i (.array (.prim .uint))
      pure (Int.ofNat (o.st.heap.len r .dyn))
    some (Int.ofNat o.st.H.length :: (leaves.flatten ++ lens))
  | .error _ => none

theorem source_observation : observeSource (program.run initial) = some [11,7,0,9,0,0,1,0,0,0] := by
  decide +kernel

example : (Compiler.compile 0 (Frag.init []) program).isSome = false := by decide +kernel
example : (defaultPlan? (.array (.ref (.array (.prim .uint))))).isSome = false := by decide +kernel
example : (defaultPlan? (.fixed (.prim .uint) 2)).isSome = false := by decide +kernel
example : (defaultPlan? (.mapping .uint (.prim .uint))).isSome = false := by decide +kernel
example : finiteDefaultCellsComputed (.ref (.struct "Empty{x:uint;x:uint}")) = some 1 := by decide +kernel

private def tooFull : Machine := writeMachine machine 0 (.val (wmod (W - 10)))
theorem capacity_invalid : ¬ compiled.Input 1 64 bases initial tooFull := by
  intro h
  have hi := ((compiled.memory_input (by decide +kernel) 1 64 bases initial tooFull).mp h).2.2
  rcases hi with hz | ⟨_, c, ha, hs⟩
  · rw [program_cost] at hz; cases hz
  · have he : c = wmod (W - 10) := Word.val.inj ha.arrays.free.cell.symm
    subst c
    rw [program_cost] at hs
    exact (by decide +kernel : ¬ (wmod (W - 10)).val + 22 < W) hs

private def failure := (sol{
  Wrapper memory w;
  require(w.holder.items[0] == 0);
} : Prog C [] _)
private def failureCompilation : Compiler.Compilation 1 (Frag.init []) failure :=
  (Compiler.compile 1 (Frag.init []) failure).get (by decide +kernel)
attribute [irreducible] failureCompilation

theorem failure_input : failureCompilation.Input 1 64 bases initial machine := by
  apply (failureCompilation.memory_input (by decide +kernel) 1 64 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 128, initial_repr.2, by decide +kernel⟩⟩
theorem failure_agrees : failureCompilation.Agrees 1 64 bases initial machine :=
  failureCompilation.correct failure_input
example : allocationCostProg failure initial = 8 := by decide +kernel
def sourceReverted {Δ : Ctx} : TRes (Solidity.Out C [] Δ) → Bool
  | .error .revert => true
  | _ => false
def targetReverted : Out → Bool
  | .revert => true
  | _ => false
theorem sourceReverted_eq {Δ : Ctx} (out : TRes (Solidity.Out C [] Δ))
    (h : sourceReverted out = true) : out = .error .revert := by
  cases out with
  | ok o => cases h
  | error e => cases e <;> first | rfl | cases h
theorem targetReverted_eq (out : Out) (h : targetReverted out = true) : out = .revert := by
  cases out <;> first | rfl | cases h
example : failure.run initial = .error .revert := sourceReverted_eq _ (by decide +kernel)
example : run failureCompilation.code machine = .revert := targetReverted_eq _ (by decide +kernel)

private def irContract : Contract := {C with evalOrder := .viaIR}
private def irProgram := (sol[irContract]{
  Wrapper memory first;
  Wrapper memory same = first;
  require(first.holder.leaf.n == 0 && !first.holder.leaf.flag && first.holder.items.length == 0);
  require(!first.holder.marker && first.own == 0);
  first.holder.leaf.n = 7;
  Leaf memory saved = first.holder.leaf;
  Holder memory fresh;
  fresh.leaf.n = 9;
  first.holder = fresh;
  require(same.holder.leaf.n == 9 && saved.n == 7);
  Wrapper memory second;
  second.holder.leaf.flag = true;
  require(first.holder.leaf.n == 9 && !first.holder.leaf.flag);
  first = second;
  require(same.holder.leaf.n == 9 && first.holder.leaf.flag && saved.n == 7);
} : Prog irContract [] _)
example : (Compiler.compile 1 (Frag.init []) irProgram).isSome = true := by decide +kernel
example : allocationCostProg irProgram (State.init irContract) = 22 := by decide +kernel

#print axioms compiled_agrees
#print axioms allocateReferenceStruct_correct
#print axioms DefaultPlan.struct
end Solidity.Evm.Memory.StructReferenceDefaultExamples
