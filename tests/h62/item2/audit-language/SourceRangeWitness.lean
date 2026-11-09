import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Source.Types

/-!
Guarded regression: range-containment certificates must use one shared source
and target type and a value in that source range; separately inhabited range
premises do not suffice. Unsigned-to-signed widening and nonzero decimal
rescaling exercise the exact imported leading telescopes. Only the five
unchanged range interfaces are covered. The three mapFree-dependent converted
headers remain outside this original-fidelity claim. These are local feasibility
checks, not compiler-success or a global old/new conversion equivalence.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.SourceRangeWitness
open Solidity.Source

def signed16 : IntTy := ⟨true, 16, by decide⟩
def decimal8 : FixTy := ⟨false, 8, 1, by decide⟩
def decimal16 : FixTy := ⟨false, 16, 2, by decide⟩

theorem power_order_full : hypotheses_of% two_pow_le := by
  exact ⟨8, 16, by decide, True.intro⟩
#verify_hypotheses power_order_full for Solidity.Source.two_pow_le
#print axioms power_order_full

theorem power_positive_full : hypotheses_of% two_pow_pos := by
  exact ⟨16, True.intro⟩
#verify_hypotheses power_positive_full for Solidity.Source.two_pow_pos
#print axioms power_positive_full

theorem integer_widen_full : hypotheses_of% implicit_int_range := by
  exact ⟨IntTy.u8, signed16, by decide, True.intro⟩
#verify_hypotheses integer_widen_full for Solidity.Source.implicit_int_range
#print axioms integer_widen_full

theorem decimal_rescale_full : hypotheses_of% FixTy.subsumes_inRange := by
  exact ⟨decimal8, decimal16, by decide, 7, ⟨by decide, by decide⟩, True.intro⟩
#verify_hypotheses decimal_rescale_full for Solidity.Source.FixTy.subsumes_inRange
#print axioms decimal_rescale_full

theorem constant_widen_full : hypotheses_of% Q.FitsInt.implicit := by
  exact ⟨Q.ofInt 7, IntTy.u8, signed16, ⟨by decide, by decide, by decide⟩,
    by decide, True.intro⟩
#verify_hypotheses constant_widen_full for Solidity.Source.Q.FitsInt.implicit
#print axioms constant_widen_full

-- Importing clients retain actual range results for the same witnessed values.
example : (Q.ofInt 7).FitsInt signed16 :=
  Q.FitsInt.implicit (t := IntTy.u8) ⟨by decide, by decide, by decide⟩ (by decide)

example : decimal16.lo ≤ (7 : Int) * 10 ^ (decimal16.digits - decimal8.digits) ∧
    (7 : Int) * 10 ^ (decimal16.digits - decimal8.digits) ≤ decimal16.hi :=
  FixTy.subsumes_inRange (t := decimal8) (by decide) ⟨by decide, by decide⟩

end Solidity.H62.AuditLanguage.SourceRangeWitness
