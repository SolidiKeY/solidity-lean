import Solidity.Semantics.ExternalReturnBytes

/-! Inhabited kernel controls of the actual primitive byte decoder. -/
namespace Solidity.Examples.Tactics.ExternalReturnBytes
open Semantics Solidity.ExternalReturnBytes

private instance {α : Type} [DecidableEq α] : DecidableEq (TRes α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

def C : Contract := contract!{}
def mixed : Binders [.val .bool, .val .int] := ((Binders.nil).snoc .int (Var.ofName "i")).snoc .bool (Var.ofName "b")
def flag : Binders [.val .bool] := (Binders.nil).snoc .bool (Var.ofName "b")
private instance : DecidableEq (TEnv C ([] : HTy) [.val .bool, .val .int]) := by
  change DecidableEq (Bool × (PrimTy.int.Denote × Unit))
  infer_instance

def payload : List UInt8 := wordBytes (2 ^ 256 - 1) ++ wordBytes 1

/-- Both word order and signed interpretation are nontrivial. -/
theorem signed_then_bool : decode (C := C) (H := []) mixed payload =
    .ok ((true, (⟨-1, by decide⟩, ())), []) := by decide +kernel

theorem complete_suffix_ignored : decode (C := C) (H := []) flag (wordBytes 1 ++ wordBytes 2) =
    .ok ((true, ()), []) := by rfl

theorem incomplete_suffix_ignored : decode (C := C) (H := []) flag (wordBytes 1 ++ [255]) =
    .ok ((true, ()), []) := by rfl

theorem invalid_bool_refused : decode (C := C) (H := []) flag (wordBytes 2) = .error .revert := by
  rfl

theorem short_word_refused : decode (C := C) (H := []) flag (List.replicate 31 0) = .error .revert := by
  rfl

/-- Error data with a noncanonical offset and extra trailing bytes is read
by the existing classifier, and is retained verbatim by a raw catch. -/
def noncanonicalError : List UInt8 := errorSelector ++ wordBytes 64 ++ wordBytes 99 ++
  wordBytes 1 ++ [42, 77]
theorem noncanonical_error_classified : classify noncanonicalError = .error [42] := by
  rfl
theorem noncanonical_error_raw : CatchKind.raw.decode noncanonicalError = some noncanonicalError := by
  rfl

def panicSuffix : List UInt8 := encodePanic 17 ++ [255]
theorem panic_suffix_classified : classify panicSuffix = .panic ⟨17, rfl⟩ := by rfl
theorem panic_suffix_raw : CatchKind.raw.decode panicSuffix = some panicSuffix := by rfl
theorem unknown_failure : classify [255, 0, 3] = .other := by rfl

/-- info: 'Solidity.Examples.Tactics.ExternalReturnBytes.signed_then_bool' depends on axioms: [propext] -/
#guard_msgs in
#print axioms signed_then_bool
/-- info: 'Solidity.Examples.Tactics.ExternalReturnBytes.invalid_bool_refused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms invalid_bool_refused
/-- info: 'Solidity.Examples.Tactics.ExternalReturnBytes.short_word_refused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms short_word_refused
/-- info: 'Solidity.Examples.Tactics.ExternalReturnBytes.noncanonical_error_classified' depends on axioms: [propext] -/
#guard_msgs in
#print axioms noncanonical_error_classified
end Solidity.Examples.Tactics.ExternalReturnBytes
