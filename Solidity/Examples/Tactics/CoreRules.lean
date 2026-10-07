import Solidity.Calculus.Core.Completeness

/-!
# The scoped rule table, used

`Calculus/Core/Rules.lean`'s taclets named on concrete scoped statements
(`Calculus/Core/Completeness.lean`'s `#rule_of`): the constructor whose line
matches, its side conditions holding, its premise `Stmt.step`'s.  A hole's
rule is found through the hole read off the statement (`x = people[i].age;`
is `storageFieldRead_unfold_rightFst` with `lhs` the local `x`).
-/

namespace Solidity.Examples.Tactics.CoreRules

open Solidity Solidity.Core

private abbrev SE := StandardExample

/-- `x = 3;` -/
private def assign3 : Core.Stmt SE [.val .uint] [.val .uint] := .assignLocal .here (.simple (.lit 3 rfl))
/-- `x = alice.age;` -/
private def readAge : Core.Stmt SE [.val .uint] [.val .uint] :=
  .assignLocal .here (.read (.field (.loc (.root "alice" rfl)) "age" rfl))
/-- `x = people[x].age;` -/
private def readPeople : Core.Stmt SE [.val .uint] [.val .uint] :=
  .assignLocal .here (.read (.field (.loc (.index (.arr .dyn) (.loc (.root "people" rfl))
    (.simple (.local .here)))) "age" rfl))
/-- `x = true ? x : 2;` -/
private def ternary : Core.Stmt SE [.val .uint] [.val .uint] :=
  .assignLocal .here (.ternary (.simple (.bool true)) (.simple (.local .here)) (.simple (.lit 2 rfl)))
/-- `alice.age = 3;` -/
private def writeAge : Core.Stmt SE [.val .uint] [.val .uint] :=
  .assign (.field (.loc (.root "alice" rfl)) "age" rfl) (.val (.simple (.lit 3 rfl)))
/-- `people[x].age = 3;` -/
private def writePeople : Core.Stmt SE [.val .uint] [.val .uint] :=
  .assign (.field (.loc (.index (.arr .dyn) (.loc (.root "people" rfl)) (.simple (.local .here))))
    "age" rfl) (.val (.simple (.lit 3 rfl)))
/-- `if (b) {} else {}` -/
private def iteB : Core.Stmt SE [.val .bool] [.val .bool] := .ite (.simple (.local .here)) .nil .nil
/-- `if (x < 3) {} else {}` -/
private def iteLt : Core.Stmt SE [.val .uint] [.val .uint] :=
  .ite (.binop .lt rfl rfl (.simple (.local .here)) (.simple (.lit 3 rfl))) .nil .nil

/-- info: Solidity.Core.Taclet.localValueAssign -/
#guard_msgs in #rule_of .box assign3
/-- info: Solidity.Core.Taclet.storageFieldReadFind -/
#guard_msgs in #rule_of .box readAge
/-- info: Solidity.Core.Taclet.storageFieldRead_unfold_rightFst -/
#guard_msgs in #rule_of .box readPeople
/-- info: Solidity.Core.Taclet.ternaryToIf -/
#guard_msgs in #rule_of .diamond ternary
/-- info: Solidity.Core.Taclet.storageFieldWriteSave -/
#guard_msgs in #rule_of .box writeAge
/-- info: Solidity.Core.Taclet.storageFieldWrite_unfold_leftFst -/
#guard_msgs in #rule_of .box writePeople
/-- info: Solidity.Core.Taclet.ifElseSplit -/
#guard_msgs in #rule_of .box iteB
/-- info: Solidity.Core.Taclet.ifElseUnfold -/
#guard_msgs in #rule_of .box iteLt
/-- info: Solidity.Core.Taclet.revertBox -/
#guard_msgs in #rule_of .box (Core.Stmt.revert (C := SE) (Γ := []))
/-- info: Solidity.Core.Taclet.revertDiamond -/
#guard_msgs in #rule_of .diamond (Core.Stmt.revert (C := SE) (Γ := []))
/-- info: Solidity.Core.Taclet.blockEmpty -/
#guard_msgs in #rule_of .box (Core.Stmt.block (C := SE) (Γ := []) .nil)
/-- info: Solidity.Core.LeanTaclet.loopExit -/
#guard_msgs in #rule_of .box (Core.Stmt.loop (C := SE) (Γ := []) (.unwind 0) (.simple (.bool true)) .nil)
/-- info: Solidity.Core.LeanTaclet.whileUnwind -/
#guard_msgs in #rule_of .box (Core.Stmt.loop (C := SE) (Γ := []) (.unwind 2) (.simple (.bool true)) .nil)

end Solidity.Examples.Tactics.CoreRules
