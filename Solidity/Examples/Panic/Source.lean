import Solidity.Syntax.Elab.Panic

/-!
# Source panic regressions

Kernel-checked local contracts: narrow uint8 overflow must retain code 17 even
when the uint256 operation succeeds; enum rejection retains code 33; legacy
assertions keep code 1. Data-retaining and ignoring modes remain distinct.
The emitted-order check places a divisor guard before its statement and tail.
These tests do not establish the missing runtime evaluation bridge, opaque
self-call/dispatch association, whole-program erasure or an external EVM claim.
-/

namespace Solidity.Examples.PanicSource

open Panic Panic.Source

private def u256 : PrimTy.uint.Denote := ⟨256, by decide⟩

/-- The same result fails uint8 narrowing but succeeds at full width. -/
example : OriginV2 (.narrowing (.unsigned 8 u256)) .arithmetic :=
  narrowing_origin _ (by decide)

example : (ProducerV2.narrowing (.unsigned 256 u256)).run = .ok u256 :=
  full_width _ (by decide)

example : (ProducerV2.narrowing (.unsigned 8 ⟨255, by decide⟩)).run =
    .ok ⟨255, by decide⟩ := narrowing_success _ (by decide)

example : OriginV2 (.narrowing (.signed 8 ⟨128, by decide⟩)) .arithmetic :=
  narrowing_origin _ (by decide)

example : (ProducerV2.narrowing (.signed 8 ⟨-128, by decide⟩)).run =
    .ok ⟨-128, by decide⟩ := narrowing_success _ (by decide)

example : OriginV2 (.narrowing (.signed 8 ⟨-129, by decide⟩)) .arithmetic :=
  narrowing_origin _ (by decide)

/-- A source width failure is not a failed uint256 addition. -/
example : (Producer.binary .add .uint rfl ⟨255, by decide⟩ ⟨1, by decide⟩).run =
    .ok u256 := rfl

/-- The arithmetic origin cannot be replaced by the assertion origin. -/
example : ¬ OriginV2 (.narrowing (.unsigned 8 u256)) .assertion := by
  intro h
  have bad := OriginV2.unique (narrowing_origin (.unsigned 8 u256) (by decide)) h
  cases bad

/-- Both directions of the original interface remain available. -/
example : OriginV2 (.original (.assertion false)) .assertion :=
  (original_origin_iff _ _).mpr assertion_origin

example (h : OriginV2 (.original (.assertion false)) .assertion) :
    Origin (.assertion false) .assertion := (original_origin_iff _ _).mp h

example : OriginV2 (.original (.enumConversion 256 u256)) .enumConversion :=
  enum_value_source _ _ (by decide)

variable {C : Contract} {Γ : Ctx}

/-- Retained checked failures have arithmetic bytes, not assertion bytes. -/
example : OFMode.checking.guardStmt (C := C) (Γ := Γ) (.simple (.bool false)) true =
    .ite (.simple (.bool false)) .nil
      (.cons (.revertData [.bytes (Semantics.encodePanic 17)]) .nil) := by
  rw [checking_guard_source]
  rfl

example : OFMode.checking.guardStmt (C := C) (Γ := Γ) (.simple (.bool false)) false =
    .assert (.simple (.bool false)) := rfl

example (data : Bool) :
    OFMode.ignoring.guardStmt (C := C) (Γ := Γ) (.simple (.bool false)) data =
      .ite (.simple (.bool false)) .nil (.cons .assumeFalse .nil) := rfl

/-- A division in a require is checked before both the require and its tail.
This checks emitted order only, not a theorem about evaluating the operands. -/
example (a b : PrimTy.uint.Denote) :
    (Prog.cons (C := C) (Γ := Γ)
      (.require (.binop .eqB rfl rfl
        (.binop .div rfl rfl (.simple (.lit a.val a.property))
          (.simple (.lit b.val b.property))) (.simple (.lit 0 (by decide)))))
      (.cons .assumeFalse .nil)).withPanics =
    .cons (panicStmt Site.zeroDivisor.code
      (Checked.cmpU .neB rfl rfl (.simple (.lit b.val b.property))
        (Checked.litU 0 (by decide))))
      (.cons (.require (.binop .eqB rfl rfl
        (.binop .div rfl rfl (.simple (.lit a.val a.property))
          (.simple (.lit b.val b.property))) (.simple (.lit 0 (by decide)))))
        (.cons .assumeFalse .nil)) := by
  rw [withPanics_source_cons]
  rfl

variable [FreshNames]

/-- The width bypass must precede expression checking, even for a bad name. -/
example : narrowCheck C .uint 256 (.name "undeclared") = pure [] := by
  rw [narrowCheck_source]
  rfl

/-- Data-retaining ordinary and checking narrowing produce identical output;
ignoring mode remains independent of the data-retention flag. -/
example (expression : RawExpr) (state : ECtx × Nat) :
    (narrowCheck C .uint 8 expression).runFrom
      { funs := [], retainFailureData := true } state =
    (narrowCheck C .uint 8 expression).runFrom
      { funs := [], retainFailureData := true, overflow := some .checking } state := by
  rw [narrowCheck_source]
  rfl

example (expression : RawExpr) (state : ECtx × Nat) :
    (narrowCheck C .int 8 expression).runFrom
      { funs := [], overflow := some .ignoring } state =
    (narrowCheck C .int 8 expression).runFrom
      { funs := [], retainFailureData := true, overflow := some .ignoring } state := by
  rw [narrowCheck_source]
  rfl

/-- Both data-retention entry routes produce the same enum captures and check,
including the final context and fresh counter. No membership premise is added. -/
example (members : Nat) (expression : RawExpr) (state : ECtx × Nat) :
    (enumCapture C members expression).runFrom
      { funs := [], selfFrame := true } state =
    (enumCapture C members expression).runFrom
      { funs := [], retainFailureData := true } state := by
  rw [enumCapture_source]
  rfl

/-- Actual zero-divisor instrumentation emits code 18 at any typed state. -/
example (σ : State C Γ) :
    (panicStmt 18 (Checked.cmpU .neB rfl rfl
      (Checked.litU 0 (by decide)) (Checked.litU 0 (by decide)))).runR σ =
      .error (THalt.ofData (Semantics.encodePanic 18)) :=
  (uint_divisor_source σ (Checked.litU 7 (by decide)) (Checked.litU 0 (by decide))
    ⟨7, by decide⟩ ⟨0, by decide⟩ rfl rfl rfl).2.2.2

/-- A nonzero divisor makes the actual guard true. -/
example (σ : State C Γ) :
    (Checked.cmpU .neB rfl rfl (Checked.litU 1 (by decide))
      (Checked.litU 0 (by decide))).evalT σ = .ok true :=
  uint_divisor_guard_eval σ _ ⟨1, by decide⟩ rfl

/-- A failure while reading a guard condition is not relabelled with the
outer enum code. Here the condition itself contains division by zero. -/
example (σ : State C Γ) :
    (panicStmt 33 (.binop .eqB rfl rfl
      (.binop .div rfl rfl (Checked.litU 1 (by decide)) (Checked.litU 0 (by decide)))
      (Checked.litU 0 (by decide)))).runR σ = .error .revert :=
  panic_guard_source_halt σ _ .revert rfl 33

/-- The first out-of-enum value fails the evaluated membership guard. -/
example (σ : State C Γ) :
    OriginV2 (.original (.enumConversion 1 ⟨1, by decide⟩)) .enumConversion :=
  enum_guard_origin σ (Checked.litU 1 (by decide)) ⟨1, by decide⟩ 1 (by decide) rfl rfl

end Solidity.Examples.PanicSource
