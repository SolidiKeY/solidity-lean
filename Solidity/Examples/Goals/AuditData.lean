import Solidity.Goals.AuditData

namespace Solidity.Goals

/--
info: open Solidity.Goals.auditDataRegenerable ← Solidity.AuditData.regeneration_check_sound plan r1-regen-out-of-git
-/
#guard_msgs in
#roadmap_goal auditDataRegenerable

open AuditData

private def a : Record := ⟨"a", [1, 2]⟩
private def b : Record := ⟨"b", [3]⟩
private def script : Record := ⟨"script", [4]⟩

#guard regenerationCheck [a, b] [script] ["a", "b"] [a, b, script]
#guard !regenerationCheck [a, b] [script] ["a", "b"] [a, script]
#guard !regenerationCheck [a, b] [script] ["a", "b"] [⟨"a", [1, 9]⟩, b, script]
#guard !regenerationCheck [a, b] [script] ["a", "b"] [⟨"wrong", [1, 2]⟩, b, script]
#guard !regenerationCheck [a, b] [script] ["a"] [a, b, script]
#guard !regenerationCheck [a, b] [script] ["a", "a"] [a, b, script]
#guard !regenerationCheck [a, b] [script] ["a", "b"] [a, b, ⟨"script", [5]⟩]
#guard !regenerationCheck [a] [a] ["a"] [a]

end Solidity.Goals
