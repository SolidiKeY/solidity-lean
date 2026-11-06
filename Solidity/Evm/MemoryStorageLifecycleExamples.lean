import Solidity.Evm.Compiler
import Solidity.Syntax.Splice

/-! Inhabited public allocation-copy-mutation controls using the published
object allocator and access code, with exact live/shadow and target tail reads. -/
namespace Solidity.Evm.Memory.StorageLifecycleExamples
open Semantics
private def C : Contract := contract!{
  struct Record { uint n; }
  uint[2] fixedValues;
  uint[3] padded;
  uint[] values;
  Record stored;
  uint[][] rows;
}
local instance : InContract := ⟨C⟩
private def recordName : Name := (C.structName? "Record").getD ""
private def Δ : Ctx := [.mem (.struct recordName), .mem (.array (.prim .uint)), .mem (.fixed (.prim .uint) 2)]
private def program : Prog C [] Δ := sol{
  uint[2] memory xs;
  fixedValues = xs;
  require(fixedValues[0] == 0 && fixedValues[1] == 0);
  xs[0] = 31; xs[1] = 47;
  fixedValues = xs;
  padded = xs;
  uint[] memory old = new uint[](3);
  old[0] = 8; old[1] = 9; old[2] = 88;
  values = old;
  values = xs;
  xs[0] = 99;
  Record memory r; r.n = 77;
  stored = r; r.n = 88;
  require(fixedValues[0] == 31 && fixedValues[1] == 47);
  require(values.length == 2 && values[0] == 31 && values[1] == 47);
  require(stored.n == 77);
}
private def state : State C [] := State.init C
private def bases : Nat → Fin W := fun _ => wmod 0
private def machine : Machine := {Machine.init with stack := [w[77]], mem := fun a =>
  if a = 0 then w[128] else if a = 63 then w[99] else w[0]}
private theorem noRefs {R : RefTy} (r : HRef [] R) : False := by
  simpa only [List.getElem?_nil, reduceCtorEq] using r.get?
private theorem heap_repr : Objects.HeapRepr state.heap bases 64 machine :=
  ⟨⟨fun r => (noRefs r).elim, fun r => (noRefs r).elim, fun r _ _ => (noRefs r).elim⟩,
    (fun _ r => (noRefs r).elim), (fun r => (noRefs r).elim), (fun r _ => (noRefs r).elim)⟩
private theorem initial_at (L : Nat) (hp : 1 ≤ L) (hL : L ≤ Lmax) :
    Objects.StateRepr L 1 64 (Frag.init []) state bases machine := by
  have hc := (Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl).mono hp hL
  refine ⟨⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩,
    heap_repr, ?_, by decide⟩
  all_goals intro p i; nomatch i

theorem initial_repr : Objects.StateRepr 4 1 64 (Frag.init []) state bases machine :=
  initial_at 4 (by decide) (by decide)
theorem initial_allocator : Objects.AllocatorRepr state.heap bases 64 (wmod 128) machine := by
  refine ⟨heap_repr, ⟨by decide, by decide, rfl, ?_⟩, fun r => (noRefs r).elim⟩
  intro addr ha
  change 128 ≤ addr at ha
  simp only [machine, if_neg (show addr ≠ 0 by omega), if_neg (show addr ≠ 63 by omega)]

private def compiled : Compiler.Compilation 1 (Frag.init []) program :=
  (Compiler.compile 1 (Frag.init []) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem selected_route : compiled.isCopyConstruction = true := by decide +kernel
theorem source_cost : Construction.allocationCostProg program state = 7 := by decide +kernel
theorem copy_demand : copyBoundProg program state = 4 := by decide +kernel
theorem compiled_input : compiled.Input 4 64 bases state machine := by
  apply (compiled.copyConstruction_input selected_route 4 64 bases state machine).mpr
  refine ⟨initial_repr, by decide +kernel, .inr ⟨by decide, wmod 128, initial_allocator, ?_⟩, ?_⟩
  · rw [source_cost]
    decide +kernel
  · rw [copy_demand]
    exact Nat.le_refl _
theorem compiled_agrees : compiled.Agrees 4 64 bases state machine := compiled.correct compiled_input

theorem bound_refusal : ¬ compiled.Input 3 64 bases state machine := by
  intro h
  have hb := ((compiled.copyConstruction_input selected_route 3 64 bases state machine).mp h).2.2.2
  rw [copy_demand] at hb
  omega

private def sourceObservation : Option (List Nat) := do
  let o ← (program.run state).toOption
  let fixed := (o.st.storage.get (f := "fixedValues") (T := .ref (.fixed (.prim .uint) 2)) (by decide +kernel)).view
  let pad := (o.st.storage.get (f := "padded") (T := .ref (.fixed (.prim .uint) 3)) (by decide +kernel)).view
  let dyn := (o.st.storage.get (f := "values") (T := .ref (.array (.prim .uint))) (by decide +kernel)).view
  let record : SFields (structDef recordName) := (o.st.storage.get (f := "stored") (T := .ref (.struct recordName)) (by decide +kernel)).view
  let rx ← TEnv.get (.there (.there .here) : Idx Δ (.mem (.fixed (.prim .uint) 2))) o.st.env
  let rr ← TEnv.get (.here : Idx Δ (.mem (.struct recordName))) o.st.env
  let x ← (o.st.heap.get rx).val[0]?
  let v := o.st.heap.field rr (f := "n") (T := .prim .uint) (by decide +kernel)
  pure ((fixed.toList ++ pad.toList).map (fun v => v.view.1.toNat) ++ [dyn.n] ++
    dyn.elems.toList.map (fun v => v.view.1.toNat) ++ dyn.shadow.toList.map (fun v => v.view.1.toNat) ++
    [(record.get (f := "n") (T := .prim .uint) (by decide +kernel)).view.1.toNat, x.val.toNat, v.val.toNat])

theorem source_observation : sourceObservation = some [31,47,31,47,0,2,31,47,0,77,99,88] := by decide +kernel
private def targetObservation : Option (List Nat) := do
  let .ok m _ := run compiled.code machine | none
  let f := rootSlot C "fixedValues"
  let p := rootSlot C "padded"
  let a := rootSlot C "values"
  pure ([m.store f,m.store (f.add 1),m.store p,m.store (p.add 1),m.store (p.add 2),
    m.store a,m.store (.data a 0),m.store (.data a 1),m.store (.data a 2),m.store (rootSlot C "stored"),
    (payloadWord (m.mem 128)).val,(payloadWord (m.mem 134)).val,(payloadWord (m.mem 0)).val,
    (payloadWord (m.mem 63)).val] ++ m.stack.map (fun v => (payloadWord v).val))
/-- info: some [31, 47, 31, 47, 0, 2, 31, 47, 0, 77, 99, 88, 135, 99, 77] -/
#guard_msgs in #eval targetObservation

private def BadΔ : Ctx := [.mem (.fixed (.prim .uint) 2)]
private def bad : Prog C [] BadΔ := sol{ uint[2] memory xs; rows[0] = xs; }
private def failed : Compiler.Compilation 1 (Frag.init []) bad :=
  (Compiler.compile 1 (Frag.init []) bad).get (by decide +kernel)
attribute [irreducible] failed

theorem failed_demand : copyBoundProg bad state = 0 := by decide +kernel
theorem failed_input : failed.Input 1 64 bases state machine := by
  apply (failed.copyConstruction_input (by decide +kernel) 1 64 bases state machine).mpr
  refine ⟨initial_at 1 (by decide) (by decide), by decide +kernel,
    .inr ⟨by decide, wmod 128, initial_allocator, by decide +kernel⟩, ?_⟩
  rw [failed_demand]
  exact Nat.zero_le _
theorem failed_agrees : failed.Agrees 1 64 bases state machine := failed.correct failed_input
theorem failed_source : bad.run state = .error .revert := by rfl
/-- info: true -/
#guard_msgs in #eval match run failed.code machine with | .revert => true | _ => false

end Solidity.Evm.Memory.StorageLifecycleExamples
