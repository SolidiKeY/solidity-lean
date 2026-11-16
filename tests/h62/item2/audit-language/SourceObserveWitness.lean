import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Source.Observe

/-!
Guarded regression: wire observations must preserve bounded big-endian values,
signed endpoints and distinct panic codes. Each named observation interface has
its entire imported leading schema instantiated. The closed uint8 rejection is
retained explicitly but earns no input-tuple credit. Selector length makes no
cryptographic injectivity claim. These are observation clients, not compiler,
EVM gas/fork or historical-replay certificates.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.SourceObserveWitness
open Solidity.Source
open Solidity.Roadmap (Word Outcome)

def layout : Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
def signed8 : IntTy := ⟨true, 8, by decide⟩

theorem byte_length_full : hypotheses_of% beBytes_length := by
  exact ⟨2, 300, True.intro⟩
#verify_hypotheses byte_length_full for Solidity.Source.beBytes_length
#print axioms byte_length_full

theorem word_length_full : hypotheses_of% wordBytes_length := by
  exact ⟨toWord 300, True.intro⟩
#verify_hypotheses word_length_full for Solidity.Source.wordBytes_length
#print axioms word_length_full

theorem append_full : hypotheses_of% beValue_append := by
  exact ⟨[1], 44, True.intro⟩
#verify_hypotheses append_full for Solidity.Source.beValue_append
#print axioms append_full

theorem bounded_roundtrip_full : hypotheses_of% beValue_beBytes := by
  exact ⟨2, 300, by decide, True.intro⟩
#verify_hypotheses bounded_roundtrip_full for Solidity.Source.beValue_beBytes
#print axioms bounded_roundtrip_full

theorem word_roundtrip_full : hypotheses_of% wordBytes_value := by
  exact ⟨toWord 300, True.intro⟩
#verify_hypotheses word_roundtrip_full for Solidity.Source.wordBytes_value
#print axioms word_roundtrip_full

theorem integer_roundtrip_full : hypotheses_of% Val.word_int := by
  exact ⟨layout, signed8, -128, ⟨by decide, by decide⟩, True.intro⟩
#verify_hypotheses integer_roundtrip_full for Solidity.Source.Val.word_int
#print axioms integer_roundtrip_full

theorem rejection_closed_schema : hypotheses_of% readInt_reject := by
  exact True.intro
#verify_hypotheses rejection_closed_schema for Solidity.Source.readInt_reject
#print axioms rejection_closed_schema

theorem selector_full : hypotheses_of% selector_length := by
  exact ⟨"transfer(address,uint256)", True.intro⟩
#verify_hypotheses selector_full for Solidity.Source.selector_length
#print axioms selector_full

theorem code_injective_full : hypotheses_of% PanicCode.code_injective := by
  exact ⟨.arithmetic, .arithmetic, rfl, True.intro⟩
#verify_hypotheses code_injective_full for Solidity.Source.PanicCode.code_injective
#print axioms code_injective_full

theorem panic_length_full : hypotheses_of% panicData_length := by
  exact ⟨.divZero, True.intro⟩
#verify_hypotheses panic_length_full for Solidity.Source.panicData_length
#print axioms panic_length_full

theorem panic_code_full : hypotheses_of% panicData_code := by
  exact ⟨.divZero, True.intro⟩
#verify_hypotheses panic_code_full for Solidity.Source.panicData_code
#print axioms panic_code_full

theorem error_prefix_full : hypotheses_of% errorData_prefix := by
  exact ⟨[65, 66], True.intro⟩
#verify_hypotheses error_prefix_full for Solidity.Source.errorData_prefix
#print axioms error_prefix_full

theorem panic_distinct_full : hypotheses_of% panic_distinct := by
  exact ⟨.divZero, .divZero, rfl, True.intro⟩
#verify_hypotheses panic_distinct_full for Solidity.Source.panic_distinct
#print axioms panic_distinct_full

-- Retain the actual closed refusal, separately from its empty schema above.
example : readInt IntTy.u8 (toWord 300) = none := readInt_reject

/-- The full byte encoding, unlike a four-byte selector, determines a word. -/
theorem word_encoding_injective {a b : Word} (same : wordBytes a = wordBytes b) : a = b := by
  apply Fin.ext
  have values := congrArg beValue same
  rw [wordBytes_value, wordBytes_value] at values
  exact values

/-- Distinct panic codes remain different source outcomes for every pair. -/
theorem panic_outcomes_differ {a b : PanicCode} (different : a ≠ b) :
    revertOutcome (panicData a) ≠ revertOutcome (panicData b) := by
  intro same
  exact different (panic_distinct same)

/-- An observer that merges distinct panic codes cannot preserve all outcomes. -/
theorem merged_panic_observer_refused (observe : PanicCode → Outcome)
    (preserves : ∀ c, observe c = revertOutcome (panicData c))
    {a b : PanicCode} (different : a ≠ b) (merged : observe a = observe b) : False := by
  rw [preserves a, preserves b] at merged
  exact panic_outcomes_differ different merged

example : revertOutcome (panicData .arithmetic) ≠ revertOutcome (panicData .divZero) :=
  panic_outcomes_differ (by decide)

#print axioms word_encoding_injective
#print axioms panic_outcomes_differ
#print axioms merged_panic_observer_refused
end Solidity.H62.AuditLanguage.SourceObserveWitness
