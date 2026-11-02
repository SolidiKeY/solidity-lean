import Solidity.Semantics.PrimitiveReturnProjection
import Solidity.Examples.Tactics.ExternalReturnBytes

/-! Inhabited primitive declaration/binder controls. No source/native frame is issued. -/
namespace Solidity.Examples.Tactics.PrimitiveReturnConsumer
open Solidity.PrimitiveReturnConsumer Semantics
abbrev C := Solidity.Examples.Tactics.ExternalReturnBytes.C

private instance {α : Type} [DecidableEq α] : DecidableEq (TRes α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)
private instance : DecidableEq (TEnv C ([] : HTy) [.val .int]) := by
  change DecidableEq (PrimTy.int.Denote × Unit)
  infer_instance

private instance : DecidableEq (TEnv C ([] : HTy) []) := by
  change DecidableEq Unit
  infer_instance

def integer : Declaration [.int] :=
  ⟨[.val .int], Binders.nil.snoc .int (Var.ofName "declared"), rfl⟩
def boolean : Declaration [.bool] :=
  ⟨[.val .bool], Binders.nil.snoc .bool (Var.ofName "declared"), rfl⟩
def zero : Declaration [] := ⟨[], .nil, rfl⟩
def callerInt : Binders [.val .int] := .snoc .nil .int (Var.ofName "caller")

theorem canonical_int_discard :
    consume (C := C) (H := []) integer (.discard _) (wordBytes 1) = .ok ((), []) := by
  decide +kernel

theorem canonical_int_bind :
    consume (C := C) (H := []) integer (.bind _ callerInt) (wordBytes 1) =
      .ok ((⟨1, by decide⟩, ()), []) := by decide +kernel

theorem one_byte_rejected_before_discard :
    consume (C := C) (H := []) integer (.discard _) [1] = .error .revert := rfl

theorem empty_rejected_before_discard :
    consume (C := C) (H := []) integer (.discard _) [] = .error .revert := rfl

theorem nil_decoder_unchanged :
    ExternalReturnBytes.decode (C := C) (H := []) Binders.nil [1] = .ok ((), []) := rfl

theorem zero_return_accepts_empty :
    consume (C := C) (H := []) zero (.discard _) [] = .ok ((), []) := rfl

theorem zero_return_ignores_extra_bytes :
    consume (C := C) (H := []) zero (.discard _) [1] = .ok ((), []) := rfl

theorem invalid_bool_rejected_even_if_discarded :
    consume (C := C) (H := []) boolean (.discard _) (wordBytes 2) = .error .revert := rfl

theorem incomplete_suffix_still_ignored :
    consume (C := C) (H := []) boolean (.discard _) (wordBytes 1 ++ [255]) = .ok ((), []) := by
  decide +kernel

def mixed : Declaration [.int, .bool] :=
  ⟨[.val .bool, .val .int], Solidity.Examples.Tactics.ExternalReturnBytes.mixed, rfl⟩
theorem signed_then_bool_kept :
    consume (C := C) (H := []) mixed (.bind _ mixed.binders)
      Solidity.Examples.Tactics.ExternalReturnBytes.payload =
      .ok ((true, (⟨-1, by decide⟩, ())), []) := by
  exact declared_success mixed (.bind _ mixed.binders)
    Solidity.Examples.Tactics.ExternalReturnBytes.signed_then_bool

theorem wrong_caller_type_has_no_projection :
    ¬ Nonempty (Projection integer.binders boolean.binders) := by
  intro ⟨selection⟩
  cases selection

theorem integer_is_not_a_zero_return_signature : integer.binders.toList.map Prod.fst ≠ [] := by
  decide +kernel

/-- info: 'Solidity.Examples.Tactics.PrimitiveReturnConsumer.canonical_int_discard' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canonical_int_discard

/-- info: 'Solidity.Examples.Tactics.PrimitiveReturnConsumer.canonical_int_bind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canonical_int_bind

/-- info: 'Solidity.Examples.Tactics.PrimitiveReturnConsumer.one_byte_rejected_before_discard' depends on axioms: [propext] -/
#guard_msgs in
#print axioms one_byte_rejected_before_discard

/-- info: 'Solidity.Examples.Tactics.PrimitiveReturnConsumer.empty_rejected_before_discard' depends on axioms: [propext] -/
#guard_msgs in
#print axioms empty_rejected_before_discard

/-- info: 'Solidity.Examples.Tactics.PrimitiveReturnConsumer.nil_decoder_unchanged' depends on axioms: [propext] -/
#guard_msgs in
#print axioms nil_decoder_unchanged

/-- info: 'Solidity.Examples.Tactics.PrimitiveReturnConsumer.zero_return_accepts_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms zero_return_accepts_empty

/-- info: 'Solidity.Examples.Tactics.PrimitiveReturnConsumer.zero_return_ignores_extra_bytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms zero_return_ignores_extra_bytes

/-- info: 'Solidity.Examples.Tactics.PrimitiveReturnConsumer.invalid_bool_rejected_even_if_discarded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms invalid_bool_rejected_even_if_discarded

/-- info: 'Solidity.Examples.Tactics.PrimitiveReturnConsumer.incomplete_suffix_still_ignored' depends on axioms: [propext] -/
#guard_msgs in
#print axioms incomplete_suffix_still_ignored

/-- info: 'Solidity.Examples.Tactics.PrimitiveReturnConsumer.signed_then_bool_kept' depends on axioms: [propext] -/
#guard_msgs in
#print axioms signed_then_bool_kept

/-- info: 'Solidity.Examples.Tactics.PrimitiveReturnConsumer.wrong_caller_type_has_no_projection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms wrong_caller_type_has_no_projection

/-- info: 'Solidity.Examples.Tactics.PrimitiveReturnConsumer.integer_is_not_a_zero_return_signature' depends on axioms: [propext] -/
#guard_msgs in
#print axioms integer_is_not_a_zero_return_signature
end Solidity.Examples.Tactics.PrimitiveReturnConsumer
