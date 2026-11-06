import Solidity.Evm.MemoryStructReferenceDefaultModes
/-! Reference-member literals and allocating rebinding retain replaced default children and old aliases. -/
namespace Solidity.Evm.Memory.StructReferenceDefaultLiterals
open Semantics

local instance : InContract := ⟨StructReferenceDefaultExamples.C⟩
private def legacy := (sol{
  Holder memory first = Holder(Leaf(3, true), new uint[](0), true);
  Holder memory old = first;
  Leaf memory leafAlias = first.leaf;
  first = Holder(Leaf(5, false), new uint[](1), false);
  first.items[0] = 19;
  require(old.leaf.n == 3 && old.marker && old.items.length == 0 && leafAlias.n == 3);
  require(first.leaf.n == 5 && !first.marker && first.items[0] == 19);
} : Prog StructReferenceDefaultExamples.C [] _)
private def viaIR := (sol[StructReferenceDefaultModes.C]{
  Holder memory first = Holder(Leaf(3, true), new uint[](0), true);
  Holder memory old = first;
  Leaf memory leafAlias = first.leaf;
  first = Holder(Leaf(5, false), new uint[](1), false);
  first.items[0] = 19;
  require(old.leaf.n == 3 && old.marker && old.items.length == 0 && leafAlias.n == 3);
  require(first.leaf.n == 5 && !first.marker && first.items[0] == 19);
} : Prog StructReferenceDefaultModes.C [] _)
private def legacyCompiled : Compiler.Compilation 1 (Frag.init []) legacy :=
  (Compiler.compile 1 (Frag.init []) legacy).get (by decide +kernel)
private def irCompiled : Compiler.Compilation 1 (Frag.init []) viaIR :=
  (Compiler.compile 1 (Frag.init []) viaIR).get (by decide +kernel)
attribute [irreducible] legacyCompiled irCompiled

theorem legacy_cost : allocationCostProg legacy StructReferenceDefaultExamples.initial = 19 := by decide +kernel
theorem ir_cost : allocationCostProg viaIR StructReferenceDefaultModes.initial = 19 := by decide +kernel

theorem legacy_input : legacyCompiled.Input 1 64 StructReferenceDefaultExamples.bases StructReferenceDefaultExamples.initial StructReferenceDefaultExamples.machine := by
  apply (legacyCompiled.memory_input (by decide +kernel) 1 64 StructReferenceDefaultExamples.bases StructReferenceDefaultExamples.initial StructReferenceDefaultExamples.machine).mpr
  exact ⟨StructReferenceDefaultExamples.initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 128, StructReferenceDefaultExamples.initial_repr.2, by decide +kernel⟩⟩
theorem ir_input : irCompiled.Input 1 64 StructReferenceDefaultModes.bases StructReferenceDefaultModes.initial StructReferenceDefaultModes.machine := by
  apply (irCompiled.memory_input (by decide +kernel) 1 64 StructReferenceDefaultModes.bases StructReferenceDefaultModes.initial StructReferenceDefaultModes.machine).mpr
  exact ⟨StructReferenceDefaultModes.initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 128, StructReferenceDefaultModes.initial_repr.2, by decide +kernel⟩⟩
theorem legacy_agrees : legacyCompiled.Agrees 1 64 StructReferenceDefaultExamples.bases StructReferenceDefaultExamples.initial StructReferenceDefaultExamples.machine :=
  legacyCompiled.correct legacy_input
theorem ir_agrees : irCompiled.Agrees 1 64 StructReferenceDefaultModes.bases StructReferenceDefaultModes.initial StructReferenceDefaultModes.machine := irCompiled.correct ir_input

private def observeTarget : Out → Option (List Nat)
  | .ok m _ => do
    (m.stack ++ [m.mem 0, m.mem 63] ++ (List.range 20).map (fun i => m.mem (128+i))).mapM
      fun w => match w with | .val v => some v.val | .slot _ => none
  | _ => none

theorem legacy_target : observeTarget (run legacyCompiled.code StructReferenceDefaultExamples.machine) =
    some [77,147,99,0,0,0,134,136,1,3,1,0,0,0,0,143,145,0,5,0,1,19,0] := by decide +kernel
theorem ir_target : observeTarget (run irCompiled.code StructReferenceDefaultModes.machine) =
    some [77,147,99,3,1,0,0,0,0,128,130,1,5,0,1,19,0,0,0,137,139,0,0] := by decide +kernel

private def holderName : Name := (StructReferenceDefaultExamples.C.structName? "Holder").getD ""
private def leafName : Name := (StructReferenceDefaultExamples.C.structName? "Leaf").getD ""
private def refAt? (H : HTy) (i : Nat) (R : RefTy) : Option (HRef H R) :=
  if h : H[i]? = some R then some ⟨i, h⟩ else none
private def observeSource {C : Contract} {Δ : Ctx} : TRes (Solidity.Out C [] Δ) → Option (List Int)
  | .ok o => do
    let holders := (List.range o.st.H.length).filterMap (fun i => refAt? o.st.H i (.struct holderName))
    let values ← holders.mapM fun h => do
      let leaf := o.st.heap.field (T := .ref (.struct leafName)) h (f := "leaf") rfl
      let items := o.st.heap.field (T := .ref (.array (.prim .uint))) h (f := "items") rfl
      let marker : Bool := o.st.heap.field (T := .prim .bool) h (f := "marker") rfl
      let flag : Bool := o.st.heap.field (T := .prim .bool) leaf (f := "flag") rfl
      let len := o.st.heap.len items .dyn
      let value ← if len = 0 then some 0 else do
        let v ← o.st.heap.index items .dyn (indexValue (wmod 0))
        pure v.1
      some [(o.st.heap.field leaf (f := "n") rfl).1, if flag then 1 else 0,
        if marker then 1 else 0, Int.ofNat len, value]
    some (Int.ofNat o.st.H.length :: values.flatten)
  | .error _ => none

theorem legacy_source : observeSource (legacy.run StructReferenceDefaultExamples.initial) = some [10,3,1,1,0,0,5,0,0,1,19] := by
  decide +kernel
theorem ir_source : observeSource (viaIR.run StructReferenceDefaultModes.initial) = some [10,3,1,1,0,0,5,0,0,1,19] := by
  decide +kernel

#print axioms legacy_agrees
#print axioms ir_agrees
end Solidity.Evm.Memory.StructReferenceDefaultLiterals
