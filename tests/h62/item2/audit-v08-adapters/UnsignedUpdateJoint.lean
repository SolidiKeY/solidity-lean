import Solidity.Lowering.V08.UnsignedUpdateCallableControls

/-! Guards independently feasible unsigned-update call premises and confusing
prefix/postfix returns with the caller write. The existing uint8 populated
pair/heap fixture is reused unchanged. This is the original UNCHECKED component
(checked=false), not checked-overflow semantics, target callee compilation,
ABI, runtime-frame/World correspondence or SourceSpec/H68 admission. -/
namespace H62.AuditV08Adapters.UnsignedUpdateJoint
open Solidity Source
open Solidity.Lowering.V07 Solidity.Lowering.V08
open UnsignedUpdateCallable.Controls
open UnsignedLocalUpdate

/-- Four public premise groups coexist on the SAME selected call and pair.
The alias-aware family includes both value and location reflection fields. -/
def Joint (p : Roadmap.Pipeline) : Prop :=
  IntegerCallable.Inputs (global p) {frame with checked := false} declaration t ∧
  IntegerLocalFamily t pairSlot (WordCastControls.ti t) pairLocals target.env ∧
  (t.lo ≤ 255 ∧ 255 ≤ t.hi) ∧
  pairLocals.get (pairSlot true) = .int 255 (by decide)

theorem joint (p : Roadmap.Pipeline) : Joint p :=
  ⟨inputs p, initial, by decide, rfl⟩

/-- Even the pipeline parameter has a concrete inhabitant of the joint model. -/
theorem inhabited : ∃ p : Roadmap.Pipeline, Joint p := ⟨.legacy, joint .legacy⟩

def returnedSource (inc pre : Bool) : Source.Val E.layout (.int t) :=
  if pre then Source.intWrap t (changed inc 255) else .int 255 (by decide)
def updatedTarget (inc : Bool) : PrimTy.uint.Denote :=
  integerValue t (t.wrap (changed inc 255)) (t.wrap_mem (changed inc 255))
def returnedTarget (inc pre : Bool) : PrimTy.uint.Denote :=
  if pre then updatedTarget inc else integerValue t 255 (by decide)
def call (p : Roadmap.Pipeline) (inc pre : Bool) : Source.RExpr E [.int t,.int t] (.int t) :=
  .call declaration (inputs p).signature
    (UnsignedUpdateCallable.arguments 8 (by decide) inc pre (pairSlot true))

/-- Exact full transport_context conclusion for both increment/decrement and
prefix/postfix; the entire populated source and intrinsic caller are retained. -/
theorem actual (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (inc pre : Bool) :
    (Source.evalE (global p) {frame with checked := false} (extra+17) (call p inc pre)).run
      (pairLocals,populated bytes) =
      (.ok (.val (returnedSource inc pre)),
        (pairLocals.set (pairSlot true) (Source.intWrap t (changed inc 255)),populated bytes)) ∧
    (operand 8 inc pre (WordCastControls.ti t true)).run target =
      .ok (⟨target.setLocal (WordCastControls.ti t true) (updatedTarget inc),List.prefix_refl _⟩,
        .prim (returnedTarget inc pre)) ∧
    IntValueRel t (returnedSource inc pre) (returnedTarget inc pre) ∧
    IntegerLocalFamily t pairSlot (WordCastControls.ti t)
      (pairLocals.set (pairSlot true) (Source.intWrap t (changed inc 255)))
      (TEnv.set (WordCastControls.ti t true) (updatedTarget inc) target.env) :=
  inhabited_transport p extra bytes inc pre

/-- Postfix at maximum returns 255 even though the caller is now zero. -/
theorem postfix_new_value_refused (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.evalE (global p) {frame with checked := false} (extra+17) (call p true false)).run
      (pairLocals,populated bytes) ≠
      (.ok (.val (.int 0 (by decide))),
        (pairLocals.set (pairSlot true) (Source.intWrap t (changed true 255)),populated bytes)) := by
  rw [(actual p extra bytes true false).1]
  intro bad
  have returned := congrArg Prod.fst bad
  cases returned

/-- Prefix at maximum returns zero rather than the captured old value. -/
theorem prefix_old_value_refused (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.evalE (global p) {frame with checked := false} (extra+17) (call p true true)).run
      (pairLocals,populated bytes) ≠
      (.ok (.val (.int 255 (by decide))),
        (pairLocals.set (pairSlot true) (Source.intWrap t (changed true 255)),populated bytes)) := by
  rw [(actual p extra bytes true true).1]
  intro bad
  have returned := congrArg Prod.fst bad
  cases returned

/-- Timeout occurs before the update and preserves the complete source pair. -/
theorem timeout_actual (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (inc pre : Bool) :
    (Source.evalE (global p) {frame with checked := false} 0 (call p inc pre)).run
      (pairLocals,populated bytes) = (.error .timeout,(pairLocals,populated bytes)) := rfl

#print axioms inhabited
#print axioms actual
#print axioms postfix_new_value_refused
#print axioms prefix_old_value_refused
#print axioms timeout_actual
end H62.AuditV08Adapters.UnsignedUpdateJoint
