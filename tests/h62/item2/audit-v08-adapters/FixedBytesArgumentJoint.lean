import Solidity.Lowering.V08.FixedBytesCallableArgumentControls

/-! Guards independent-model witnesses for fixed-bytes argument premises and
loss of byte width/leading-zero or caller-write observations. Existing populated
source/target memory and storage fixtures supply ALL hypotheses together for
all valid widths and arbitrary byte lists. This is argument-phase execution,
not selected callee compilation, ABI or SourceSpec admission. -/
namespace H62.AuditV08Adapters.FixedBytesArgumentJoint
open Solidity Source
open Solidity.Lowering.V07 Solidity.Lowering.V08
open FixedBytesAssignment FixedBytesAssignmentControls
open MixedAssignmentControls (C E globals)
open Source.SemanticsExamples

/-- The original typed alignment, reflection, two map equations, exact payload
length and concrete read share one source/target pair and representation. -/
def Joint (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (old rhs : List UInt8) : Prop :=
  (mapping n w).Related BindingRel (source n w old rhs).1 (target n w old rhs).env ∧
  (∀ (v : Source.Val E.layout (.fixedBytes n w)) (x : PrimTy.uint.Denote),
    BindingRel (.fixedBytes n w) (.val .uint) v x → Rel n w v x) ∧
  (mapping n w).slot (.here : Source.Idx (SrcCtx n w) (.fixedBytes n w)) =
    ⟨.val .uint,(.here : Idx TgtCtx (.val .uint))⟩ ∧
  (mapping n w).slot (.there .here : Source.Idx (SrcCtx n w) (.fixedBytes n w)) =
    ⟨.val .uint,(.there .here : Idx TgtCtx (.val .uint))⟩ ∧
  (payload n rhs).length = n ∧
  (source n w old rhs).1.get (.there .here) =
    .fixedBytes (payload n rhs) (Source.fitBytes_length n rhs)

theorem joint (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (old rhs : List UInt8) :
    Joint n w old rhs :=
  ⟨initial n w old rhs, reflect n w, rfl, rfl, Source.fitBytes_length n rhs, rfl⟩

/-- The valid-width parameter and the complete joint model are inhabited. -/
theorem inhabited : ∃ (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (old rhs : List UInt8),
    Joint n w old rhs :=
  ⟨2, by decide, [255,128], [0,1], joint _ _ _ _⟩

/-- Exact full transport_argument conclusion on the SAME shared model, with
all pipelines and checked/static flags retained and no desired-run premise. -/
theorem actual (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (p : Roadmap.Pipeline)
    (checked static : Bool) (extra : Nat) (old rhs : List UInt8) :
    (Source.evalConvArgs (globals p) {F0 with checked := checked,static := static} (extra+4)
      (FixedBytesCallableArgument.arguments n w .here (.there .here))).run (source n w old rhs) =
      (.ok (.cons (.fixedBytes (payload n rhs) (Source.fitBytes_length n rhs)) .nil),
        ((source n w old rhs).1.set .here (.fixedBytes (payload n rhs) (Source.fitBytes_length n rhs)),
          (source n w old rhs).2)) ∧
    (assignLocalOperand (.here : Idx TgtCtx (.val .uint)) (.there .here)).run (target n w old rhs) =
      .ok (⟨(target n w old rhs).setLocal .here (value n w (payload n rhs) (Source.fitBytes_length n rhs)),
        List.prefix_refl _⟩,.prim (value n w (payload n rhs) (Source.fitBytes_length n rhs))) ∧
    Rel n w (.fixedBytes (payload n rhs) (Source.fitBytes_length n rhs) :
      Source.Val E.layout (.fixedBytes n w)) (value n w (payload n rhs) (Source.fitBytes_length n rhs)) ∧
    (mapping n w).Related BindingRel
      ((source n w old rhs).1.set .here (.fixedBytes (payload n rhs) (Source.fitBytes_length n rhs)))
      (TEnv.set .here (value n w (payload n rhs) (Source.fitBytes_length n rhs)) (target n w old rhs).env) :=
  FixedBytesCallableArgument.Controls.actual_client n w p checked static extra old rhs

/-- Zero quotation horizon preserves the full source pair and times out even
though the positive model has coherent reads and representation. -/
theorem zero_timeout (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (p : Roadmap.Pipeline)
    (checked static : Bool) (old rhs : List UInt8) :
    (Source.evalConvArgs (globals p) {F0 with checked := checked,static := static} 0
      (FixedBytesCallableArgument.arguments n w .here (.there .here))).run (source n w old rhs) =
      (.error .timeout,source n w old rhs) := rfl

theorem argument_timeout (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (p : Roadmap.Pipeline)
    (checked static : Bool) (old rhs : List UInt8) :
    (Source.evalConvArgs (globals p) {F0 with checked := checked,static := static} 1
      (FixedBytesCallableArgument.arguments n w .here (.there .here))).run (source n w old rhs) =
      (.error .timeout,source n w old rhs) := rfl

/-- Reconstructing the actual returned scalar at its known width retains the
entire normalized payload, including leading zeros; this is not ABI encoding. -/
theorem decoded_payload (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (rhs : List UInt8) :
    Source.beBytes n (value n w (payload n rhs) (Source.fitBytes_length n rhs)).val.toNat =
      payload n rhs :=
  decode_value n w _ (Source.fitBytes_length n rhs)

#print axioms inhabited
#print axioms actual
#print axioms zero_timeout
#print axioms argument_timeout
#print axioms decoded_payload
end H62.AuditV08Adapters.FixedBytesArgumentJoint
