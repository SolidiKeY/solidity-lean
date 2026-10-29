import Solidity.Evm.MemoryStructReferenceDefaultExamples
/-! The same nested default/alias behavior has inhabited via-IR source and target observations. -/
namespace Solidity.Evm.Memory.StructReferenceDefaultModes
open Semantics
def C : Contract := {StructReferenceDefaultExamples.C with evalOrder := .viaIR}
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


#print axioms compiled_agrees
end Solidity.Evm.Memory.StructReferenceDefaultModes
