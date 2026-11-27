import Solidity.Docs.ProseRatio

/-! Pin and controls for the plan goal `proseRatioRuleSound`. -/

namespace Solidity.Goals

/-! The Lean policy specification only: not the checker's proof, the calibrated
policy, the Python integration or CI on the merged head. -/
/--
info: proved Solidity.Goals.proseRatioRuleSound ← Solidity.Docs.prose_ratio_rule_sound plan pb2-prose-ratio-rule
-/
#guard_msgs in
#roadmap_goal proseRatioRuleSound

example : proseRatioRuleSound := Solidity.Docs.prose_ratio_rule_sound

/-- info: 'Solidity.Docs.prose_ratio_rule_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Docs.prose_ratio_rule_sound

/-! The decision model at its boundaries: equality passes and one line over fails,
mixed lines count as code, audits padding and value-equal or raised proposals change
nothing, and an unlisted area allows no prose. -/
namespace ProseRatio

def scope : Scope String where
  area p := p.headD ""
  generated := [["Solidity.lean"]]
  kind p := if p.headD "" = "Solidity" then .source
    else if p.headD "" = "docs" then .docs else .outside

/-- Comments in `Solidity`: half a line per code line, plus one. -/
def half : Allowance := ⟨⟨1, 2, by decide⟩, 1⟩

def pol : Policy String := ⟨scope, [(("Solidity", .comment), half)]⟩

def lean (code comments : Nat) : File :=
  ⟨["Solidity", "A.lean"], List.replicate code [.code "x"] ++
    List.replicate comments [.code " ", .comment "-- c"]⟩

example : accepts pol [lean 4 3] = true := by decide
example : accepts pol [lean 4 4] = false := by decide
example : accepts pol [lean 0 1] = true := by decide
example : accepts pol [⟨["Solidity", "B.lean"], [[.code "x ", .comment "-- c"],
    [.code "y", .comment "-- d"]]⟩] = true := by decide
example : accepts pol [lean 4 3, ⟨["docs", "audits", "a.md"], [[], []]⟩] = true := by decide
example : accepts pol [lean 4 3, ⟨["docs", "a.md"], [[]]⟩] = false := by decide
example : accepts pol [lean 4 3, ⟨["Solidity", "C.lean"], [[.comment "-- e"]]⟩] = false := by decide
example : accepts pol [lean 4 3, ⟨["Solidity", "C.lean"], [[.code "z"], [.code "w"]]⟩] =
    true := by decide
example : accepts (pol.shrink [(("Solidity", .comment), ⟨⟨1, 1, by decide⟩, 9⟩)])
    [lean 4 4] = false := by decide
example : accepts ((⟨scope, [(("Solidity", .comment), ⟨⟨2, 4, by decide⟩, 1⟩)]⟩ :
    Policy String).shrink [(("Solidity", .comment), half)]) [lean 4 3] = true := by decide
example : accepts (pol.shrink []) [lean 4 1] = false := by decide

end ProseRatio

end Solidity.Goals
