import tests.h62.item2.«audit-yul».DefaultWitnesses
import Solidity.Yul.Views.Inputs
import Solidity.Yul.Words
import Solidity.Yul.Checks.ClosedFunctions
set_option h62.auditOutput "/workspace/h62-audit-yul-evidence/h69-default-controls.jsonl"
-- Ordinary parameters must be supplied together, with no new hypothesis.
audit_joint_defaults "Solidity.Yul.pow_halve" as H62.AuditYul.Controls.pow_halve_joint
-- No closed default may manufacture an intrinsic reference to an empty context.
-- This attempt must be reported uncovered; H69's separate refutation applies.
audit_joint_defaults "Solidity.Yul.Checks.ClosedFunctions.no_external_reference" as H62.AuditYul.Controls.must_not_exist
#print axioms H62.AuditYul.Controls.pow_halve_joint
-- Includes an actual proposition-valued input, not just inhabited data types.
audit_joint_defaults "Solidity.Yul.powBits_correct" as H62.AuditYul.Controls.powBits_joint
example : ∃ (_b _e : Nat), True := H62.AuditYul.Controls.pow_halve_joint
example : ∃ (k : Nat) (_b : Solidity.Yul.Word) (e : Nat) (_h : e < 2 ^ k), True :=
  H62.AuditYul.Controls.powBits_joint
-- Synthetic utility correctness control; never counted as interface coverage.
universe u
theorem H62.AuditYul.Controls.universe_control (α : Sort u) (value : α) : value = value := rfl
audit_joint_defaults "H62.AuditYul.Controls.universe_control" as H62.AuditYul.Controls.universe_joint
example : ∃ (α : Sort u) (_value : α), True := H62.AuditYul.Controls.universe_joint.{u}
open Lean Elab Command in
run_cmd do
  if (← getEnv).contains `H62.AuditYul.Controls.must_not_exist then
    throwError "negative joint-witness control was incorrectly accepted"
#print axioms H62.AuditYul.Controls.powBits_joint
#print axioms H62.AuditYul.Controls.universe_joint
-- Aliases and lets must not hide a premise from the existential telescope.
abbrev H62.AuditYul.Controls.HiddenFalse : Prop := let P := False; P → True
abbrev H62.AuditYul.Controls.HiddenTrue : Prop := let P := True; P → True
theorem H62.AuditYul.Controls.hidden_false : H62.AuditYul.Controls.HiddenFalse :=
  fun h => False.elim h
theorem H62.AuditYul.Controls.hidden_true : H62.AuditYul.Controls.HiddenTrue :=
  fun _ => True.intro
audit_joint_defaults "H62.AuditYul.Controls.hidden_false" as H62.AuditYul.Controls.hidden_must_not_exist
audit_joint_defaults "H62.AuditYul.Controls.hidden_true" as H62.AuditYul.Controls.hidden_joint
example : ∃ (_h : True), True := H62.AuditYul.Controls.hidden_joint
open Lean Elab Command in
run_cmd do
  if (← getEnv).contains `H62.AuditYul.Controls.hidden_must_not_exist then
    throwError "let/alias premise was omitted from joint witness"
#print axioms H62.AuditYul.Controls.hidden_joint

namespace Solidity.Yul.Views.H62
/-- Word-window audit inputs use the existing residual view at a real unaligned
base and a nonempty 32-byte window; these are premise witnesses, not execution
or arbitrary-input admission theorems. -/
theorem word_window_joint : ∃ (_m : ByteView) (_a _n : Nat), True :=
  ⟨(fun _ => 0), 129, 32, True.intro⟩

theorem word_read_congr_joint :
    ∃ (m m' : ByteView) (a n : Nat)
      (_h : ∀ i, i < n → m (a + i) = m' (a + i)), True :=
  ⟨(fun _ => 0), (fun _ => 0), 129, 32,
    (fun _ _ => rfl), True.intro⟩

theorem word_load_congr_joint :
    ∃ (m m' : ByteView) (a : Nat)
      (_h : ∀ i : Fin 32, m (a + i.val) = m' (a + i.val)), True :=
  ⟨(fun _ => 0), (fun _ => 0), 129,
    (fun _ => rfl), True.intro⟩

theorem word_prefix_joint :
    ∃ (_m : ByteView) (_a : Nat) (_w : Roadmap.Word) (n : Nat) (_hn : n ≤ 32), True :=
  ⟨(fun _ => 0), 129, 2, 32, Nat.le_refl 32, True.intro⟩

theorem word_store_joint :
    ∃ (_m : ByteView) (_a : Nat) (_w : Roadmap.Word), True :=
  ⟨(fun _ => 0), 129, 2, True.intro⟩

theorem word_div_joint :
    ∃ (_m : ByteView) (_a n k : Nat) (_hk : k ≤ n), True :=
  ⟨(fun _ => 0), 129, 32, 16, by decide, True.intro⟩

theorem word_byte_joint : ∃ (_m : ByteView) (_a : Nat) (_i : Fin 32), True :=
  ⟨(fun _ => 0), 129, ⟨31, by decide⟩, True.intro⟩

theorem word_writeback_joint : ∃ (_m : ByteView) (_a : Nat), True :=
  ⟨(fun _ => 0), 129, True.intro⟩

#print axioms word_read_congr_joint
#print axioms word_load_congr_joint
#print axioms word_prefix_joint
#print axioms word_div_joint
/-- Primitive byte-operation joint inputs. Outside-region premises refer to the
same chosen nonempty intervals; copy indices use their final live byte. These
are ordinary premise witnesses, not EVM range/admission or execution claims. -/
theorem save_byte_joint : ∃ (_m : ByteView) (_a : Nat) (_v : UInt8), True :=
  ⟨(fun _ => 0), 129, 0xaa, True.intro⟩

theorem save_byte_other_joint :
    ∃ (_m : ByteView) (a b : Nat) (_v : UInt8) (_h : b ≠ a), True :=
  ⟨(fun _ => 0), 129, 128, 0xaa, by decide, True.intro⟩

theorem copy_byte_joint :
    ∃ (_dst _src : ByteView) (_to _start n i : Nat) (_hi : i < n), True :=
  ⟨(fun _ => 0), (fun _ => 0xaa), 130, 129, 32, 31, by decide, True.intro⟩

theorem copy_outside_joint :
    ∃ (_dst _src : ByteView) (to : Nat) (_start : Nat) (n a : Nat)
      (_h : ¬ (to ≤ a ∧ a < to + n)), True :=
  ⟨(fun _ => 0), (fun _ => 0xaa), 130, 129, 32, 128, by decide, True.intro⟩

theorem copy_zero_joint :
    ∃ (_dst _src : ByteView) (_to _start : Nat), True :=
  ⟨(fun _ => 0), (fun _ => 0xaa), 130, 129, True.intro⟩

theorem store_byte_joint :
    ∃ (_m : ByteView) (_a : Nat) (_w : Roadmap.Word) (_i : Fin 32), True :=
  ⟨(fun _ => 0), 129, 2, ⟨31, by decide⟩, True.intro⟩

theorem store_outside_joint :
    ∃ (_m : ByteView) (a b : Nat) (_w : Roadmap.Word)
      (_h : ¬ (a ≤ b ∧ b < a + 32)), True :=
  ⟨(fun _ => 0), 129, 128, 2, by decide, True.intro⟩

/-- Nonempty calldata with a genuinely out-of-range address jointly witnesses
both zero-padding theorem telescopes, without arbitrary-input validity claims. -/
theorem calldata_padding_joint :
    ∃ (input : List UInt8) (a : Nat) (_h : input.length ≤ a), True :=
  ⟨[0xaa], 33, by decide, True.intro⟩

/-- Hash congruence uses the existing real-Keccak instance and one common live
window. No collision premise or arbitrary hash result is introduced. -/
theorem input_hash_joint :
    ∃ (_fixed : Roadmap.Evm.Fixed) (m m' : ByteView) (a n : Nat)
      (_h : readBytes m a n = readBytes m' a n), True :=
  ⟨Roadmap.Evm.withKeccak, (fun _ => 0xaa), (fun _ => 0xaa),
    129, 32, rfl, True.intro⟩

/-- One closed value inhabits the existing bounded environment carrier; it is
not substituted for the universally supplied environment in any public law. -/
theorem input_environment_joint : ∃ (_e : Environment), True :=
  ⟨⟨0, 0, 257, 1, 0, 0, 1, 0, 0, 0, (fun _ => 0), []⟩, True.intro⟩

end Solidity.Yul.Views.H62
