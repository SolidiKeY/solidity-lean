import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Source.Const

/-!
Guarded regression: exact fixed-point success and out-of-range rejection must
not be interchangeable. Every certificate instantiates the whole imported
hypothesis telescope on one literal/value/type tuple. Non-integral 3/2 scales
exactly to 15, while 20 exceeds signed8x1's scaled range. These certify local
constant semantics, not source compilation, gas or fork behavior.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.SourceConstantWitness
open Solidity.Source

def signedDecimal : FixTy := ⟨true, 8, 1, by decide⟩
def fraction : Q := ⟨3, 2, by decide⟩
def decimalLiteral : NumLit := .dec 15 1 0

theorem literal_full : hypotheses_of% Syn.const_lit_eq := by
  exact ⟨decimalLiteral, decimalLiteral.value, rfl, True.intro⟩
#verify_hypotheses literal_full for Solidity.Source.Syn.const_lit_eq
#print axioms literal_full

theorem integer_test_full : hypotheses_of% Q.ofInt_isInt := by
  exact ⟨-7, True.intro⟩
#verify_hypotheses integer_test_full for Solidity.Source.Q.ofInt_isInt
#print axioms integer_test_full

theorem integer_value_full : hypotheses_of% Q.ofInt_toInt := by
  exact ⟨-7, True.intro⟩
#verify_hypotheses integer_value_full for Solidity.Source.Q.ofInt_toInt
#print axioms integer_value_full

theorem integer_option_full : hypotheses_of% Q.int?_ofInt := by
  exact ⟨-7, True.intro⟩
#verify_hypotheses integer_option_full for Solidity.Source.Q.int?_ofInt
#print axioms integer_option_full

theorem exact_full : hypotheses_of% Q.toFixed?_exact := by
  exact ⟨fraction, signedDecimal, 15, by decide, True.intro⟩
#verify_hypotheses exact_full for Solidity.Source.Q.toFixed?_exact
#print axioms exact_full

theorem range_full : hypotheses_of% Q.toFixed?_inRange := by
  exact ⟨fraction, signedDecimal, 15, by decide, True.intro⟩
#verify_hypotheses range_full for Solidity.Source.Q.toFixed?_inRange
#print axioms range_full

theorem explicit_success_full : hypotheses_of% Q.toFixedExplicit?_of_toFixed? := by
  exact ⟨fraction, signedDecimal, 15, by decide, True.intro⟩
#verify_hypotheses explicit_success_full for Solidity.Source.Q.toFixedExplicit?_of_toFixed?
#print axioms explicit_success_full

theorem out_of_range_full : hypotheses_of% Q.toFixedExplicit?_none := by
  exact ⟨Q.ofInt 20, signedDecimal, Or.inr (by decide), True.intro⟩
#verify_hypotheses out_of_range_full for Solidity.Source.Q.toFixedExplicit?_none
#print axioms out_of_range_full

-- Clients apply original laws to the successful and refused inputs above.
example : fraction.toFixedExplicit? signedDecimal = some 15 :=
  Q.toFixedExplicit?_of_toFixed? (by decide)

example : (Q.ofInt 20).toFixedExplicit? signedDecimal = none :=
  Q.toFixedExplicit?_none (Or.inr (by decide))

end Solidity.H62.AuditLanguage.SourceConstantWitness
