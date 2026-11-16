import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Source.Value

/-!
Guarded regression: checked overflow, unchecked wrapping and zero-divisor panic
must not be conflated. Joint certificates retain width, range, layout and mode
binders from each imported Value interface. Concrete overflow and signed wrapping
exercise boundaries; general clients retain supported success and failure codes.
This is source-value feasibility, not compiler totality or historical replay.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.SourceValueWitness
open Solidity.Source

def layout : Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
def signedDecimal : FixTy := ⟨true, 8, 1, by decide⟩

theorem same_full : hypotheses_of% STy.eq_of_same := by
  exact ⟨(.bool : STy), .bool, rfl, True.intro⟩
#verify_hypotheses same_full for Solidity.Source.STy.eq_of_same
#print axioms same_full

theorem same_list_full : hypotheses_of% STy.eq_of_sameList := by
  exact ⟨[.bool], [.bool], rfl, True.intro⟩
#verify_hypotheses same_list_full for Solidity.Source.STy.eq_of_sameList
#print axioms same_list_full

theorem same_refl_full : hypotheses_of% STy.same_refl := by
  exact ⟨(.bool : STy), True.intro⟩
#verify_hypotheses same_refl_full for Solidity.Source.STy.same_refl
#print axioms same_refl_full

theorem same_list_refl_full : hypotheses_of% STy.sameList_refl := by
  exact ⟨[.bool], True.intro⟩
#verify_hypotheses same_list_refl_full for Solidity.Source.STy.sameList_refl
#print axioms same_list_refl_full

theorem power_full : hypotheses_of% two_pow_succ_pred := by
  exact ⟨8, by decide, True.intro⟩
#verify_hypotheses power_full for Solidity.Source.two_pow_succ_pred
#print axioms power_full

theorem bits_wrap_full : hypotheses_of% wrapBits_mem := by
  exact ⟨true, 8, by decide, 128, True.intro⟩
#verify_hypotheses bits_wrap_full for Solidity.Source.wrapBits_mem
#print axioms bits_wrap_full

theorem integer_bits_full : hypotheses_of% IntTy.bits_pos := by
  exact ⟨IntTy.u8, True.intro⟩
#verify_hypotheses integer_bits_full for Solidity.Source.IntTy.bits_pos
#print axioms integer_bits_full

theorem fixed_bits_full : hypotheses_of% FixTy.bits_pos := by
  exact ⟨signedDecimal, True.intro⟩
#verify_hypotheses fixed_bits_full for Solidity.Source.FixTy.bits_pos
#print axioms fixed_bits_full

theorem integer_wrap_full : hypotheses_of% IntTy.wrap_mem := by
  exact ⟨IntTy.u8, 256, True.intro⟩
#verify_hypotheses integer_wrap_full for Solidity.Source.IntTy.wrap_mem
#print axioms integer_wrap_full

theorem fixed_wrap_full : hypotheses_of% FixTy.wrap_mem := by
  exact ⟨signedDecimal, 128, True.intro⟩
#verify_hypotheses fixed_wrap_full for Solidity.Source.FixTy.wrap_mem
#print axioms fixed_wrap_full

theorem bytes_length_full : hypotheses_of% fitBytes_length := by
  exact ⟨4, [1, 2], True.intro⟩
#verify_hypotheses bytes_length_full for Solidity.Source.fitBytes_length
#print axioms bytes_length_full

theorem checked_overflow_full : hypotheses_of% intRes_overflow := by
  exact ⟨layout, IntTy.u8, 256, by decide, True.intro⟩
#verify_hypotheses checked_overflow_full for Solidity.Source.intRes_overflow
#print axioms checked_overflow_full

theorem unchecked_full : hypotheses_of% intRes_unchecked := by
  exact ⟨layout, IntTy.u8, 256, True.intro⟩
#verify_hypotheses unchecked_full for Solidity.Source.intRes_unchecked
#print axioms unchecked_full

theorem zero_divisor_full : hypotheses_of% intBin_divZero := by
  exact ⟨layout, IntTy.u8, false, 7, True.intro⟩
#verify_hypotheses zero_divisor_full for Solidity.Source.intBin_divZero
#print axioms zero_divisor_full

/-- Supported in-range operations return the supplied value in either mode. -/
theorem checked_success {D : Layout} (t : IntTy) (checked : Bool) (v : Int)
    (range : t.lo ≤ v ∧ v ≤ t.hi) :
    intRes (D := D) t checked v = .ok (.int v range) := by
  rw [intRes, dif_pos range]
  rfl

/-- An always-success result cannot replace source checked-overflow behavior. -/
theorem overflow_refuses_success {D : Layout} (t : IntTy) (v : Int)
    (outside : ¬ (t.lo ≤ v ∧ v ≤ t.hi)) (result : Val D (.int t)) :
    intRes (D := D) t true v ≠ .ok result := by
  rw [intRes_overflow t v outside]
  intro impossible
  cases impossible

/-- A reject-all result cannot replace supported source-value operations. -/
theorem supported_refuses_error {D : Layout} (t : IntTy) (checked : Bool) (v : Int)
    (range : t.lo ≤ v ∧ v ≤ t.hi) (failure : Halt) :
    intRes (D := D) t checked v ≠ .error failure := by
  rw [checked_success t checked v range]
  intro impossible
  cases impossible

example : IntTy.u8.wrap 256 = 0 := rfl
example : signedDecimal.wrap 128 = -128 := rfl
example : intBin (D := layout) IntTy.u8 false BinOp.div 7 0 = panic .divZero :=
  intBin_divZero IntTy.u8 false 7

#print axioms checked_success
#print axioms overflow_refuses_success
#print axioms supported_refuses_error
end Solidity.H62.AuditLanguage.SourceValueWitness
