import Solidity.Lowering.Readonly.ReceiverCapture

/-! Guard receiver truncation, binder permutation and reevaluation after caller
mutation. A high-bit 160-bit address and a mixed Bool/uint binder list are used
at two nonempty caller states with different locals, storage and heap typings.
These are already-captured primitive values, not selected-function bindings,
ABI-byte transport, Source callee execution or compiler/physical-frame adequacy. -/
namespace Solidity.H62.ReadonlyAudit.CapturedValueWitnesses
open Solidity
open Solidity.Lowering.Readonly

def contract : Contract := { vars := [("flag", .prim .bool)] }
def address : Solidity.Roadmap.Address := ⟨2^159 + 7, by decide⟩
def first : State contract [.val .uint] :=
  (State.ofStorage (.cons (.prim (p := .bool) true) .nil)).push (t := .val .uint) ⟨9, by decide⟩
def second : State contract [.val .uint] :=
  { storage := .cons (.prim (p := .bool) false) .nil,
    H := [.array (.prim .bool)], heap := (⟨[true], by decide⟩, ()),
    env := (⟨4, by decide⟩, ()) }
def binders : Binders [.val .uint, .val .bool] :=
  .snoc (.snoc .nil .bool (.user "flagArg")) .uint (.user "receiverArg")
def values : TEnv contract [] [.val .uint, .val .bool] :=
  (ReceiverCapture.word address, (false, ()))

theorem receiver_exact_joint : (ReceiverCapture.word address).val = Int.ofNat address.val :=
  ReceiverCapture.exact_value address

theorem receiver_eval_joint : (ReceiverCapture.value address).evalT first = .ok (ReceiverCapture.word address) :=
  ReceiverCapture.evaluate first address

theorem receiver_stable_joint :
    (ReceiverCapture.value address).evalT first = .ok (ReceiverCapture.word address) ∧
    (ReceiverCapture.value address).evalT second = .ok (ReceiverCapture.word address) :=
  ReceiverCapture.stable first second address

theorem literal_joint : (CapturedArguments.literal .uint (ReceiverCapture.word address)).evalT first =
    .ok (ReceiverCapture.word address) :=
  CapturedArguments.literal_eval first .uint (ReceiverCapture.word address)

theorem reheap_joint : CapturedArguments.reheap (C := contract) (H := []) (H' := []) binders values = values :=
  CapturedArguments.reheap_id binders values

theorem any_heap_joint : (CapturedArguments.arguments (H := []) binders values).evalT second =
    .ok (CapturedArguments.reheap (C := contract) (H := []) (H' := second.H) binders values) :=
  CapturedArguments.eval_any_heap second binders values

theorem arguments_joint : (CapturedArguments.arguments (H := []) binders values).evalT first = .ok values :=
  CapturedArguments.eval first binders values

theorem names_joint : (CapturedArguments.arguments (C := contract) (H := []) (Ξ := [.val .uint]) binders values).names = binders.names :=
  CapturedArguments.names binders values

theorem arguments_stable_joint :
    (CapturedArguments.arguments (H := []) binders values).evalT first =
      .ok (CapturedArguments.reheap (C := contract) (H := []) (H' := first.H) binders values) ∧
    (CapturedArguments.arguments (H := []) binders values).evalT second =
      .ok (CapturedArguments.reheap (C := contract) (H := []) (H' := second.H) binders values) :=
  CapturedArguments.stable first second binders values

/-- Both the caller local and the heap typing really differ. -/
theorem caller_mutations : first.env.1 ≠ second.env.1 ∧ first.H ≠ second.H := ⟨by decide, by decide⟩

/-- Reducing the captured address to its low byte loses an observable high bit. -/
theorem truncated_receiver_refused : (ReceiverCapture.word address).val ≠ 7 := by decide

/-- The reverse-context name order cannot be exchanged. -/
theorem reordered_names_refused :
    (CapturedArguments.arguments (C := contract) (H := []) (Ξ := [.val .uint]) binders values).names ≠
      [Var.user "flagArg", Var.user "receiverArg"] := by decide

end Solidity.H62.ReadonlyAudit.CapturedValueWitnesses
