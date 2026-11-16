import Solidity.Goals.AuditData

namespace Solidity.AuditData

/-- The finite checker entails the byte equality of every listed record.
Producer execution and Git provenance are established separately by the executable check. -/
theorem regeneration_check_sound : Solidity.Goals.auditDataRegenerable := by
  intro inventory retained manifest files h
  simp only [Solidity.Goals.AuditData.regenerationCheck, Bool.and_eq_true] at h
  constructor
  · simpa only [List.all_eq_true, Solidity.Goals.AuditData.recordMatches, beq_iff_eq] using h.1.2
  · simpa only [List.all_eq_true, Solidity.Goals.AuditData.recordMatches, beq_iff_eq] using h.2

/--
info: proved Solidity.Goals.auditDataRegenerable ← Solidity.AuditData.regeneration_check_sound plan r1-regen-out-of-git
-/
#guard_msgs in
#roadmap_goal Solidity.Goals.auditDataRegenerable

/--
info: 'Solidity.AuditData.regeneration_check_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms regeneration_check_sound

end Solidity.AuditData
