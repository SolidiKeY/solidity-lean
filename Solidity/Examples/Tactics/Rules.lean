import Solidity.Calculus.Completeness

/-!
# The scoped rule table, used

`Calculus/Rules.lean`'s taclets named on concrete scoped statements
(`Calculus/Completeness.lean`'s `#rule_of`): the constructor whose line
matches, its side conditions holding, its premise `Stmt.step`'s.  A hole's
rule is found through the hole read off the statement (`x = people[i].age;`
is `storageFieldRead_unfold_rightFst` with `lhs` the local `x`).
-/

namespace Solidity.Examples.Tactics.Rules

open Solidity Solidity

private abbrev SE := StandardExample

/-- `x = 3;` -/
private def assign3 : Stmt SE [.val .uint] [.val .uint] := .assignLocal .here (.simple (.lit 3 rfl))
/-- `x = alice.age;` -/
private def readAge : Stmt SE [.val .uint] [.val .uint] :=
  .assignLocal .here (.read (.field (.loc (.root "alice" rfl)) "age" rfl))
/-- `x = people[x].age;` -/
private def readPeople : Stmt SE [.val .uint] [.val .uint] :=
  .assignLocal .here (.read (.field (.loc (.index (.arr .dyn) (.loc (.root "people" rfl))
    (.simple (.local .here)))) "age" rfl))
/-- `x = true ? x : 2;` -/
private def ternary : Stmt SE [.val .uint] [.val .uint] :=
  .assignLocal .here (.ternary (.simple (.bool true)) (.simple (.local .here)) (.simple (.lit 2 rfl)))
/-- `alice.age = 3;` -/
private def writeAge : Stmt SE [.val .uint] [.val .uint] :=
  .assign (.field (.loc (.root "alice" rfl)) "age" rfl) (.val (.simple (.lit 3 rfl)))
/-- `people[x].age = 3;` -/
private def writePeople : Stmt SE [.val .uint] [.val .uint] :=
  .assign (.field (.loc (.index (.arr .dyn) (.loc (.root "people" rfl)) (.simple (.local .here))))
    "age" rfl) (.val (.simple (.lit 3 rfl)))
/-- `if (b) {} else {}` -/
private def iteB : Stmt SE [.val .bool] [.val .bool] := .ite (.simple (.local .here)) .nil .nil
/-- `if (x < 3) {} else {}` -/
private def iteLt : Stmt SE [.val .uint] [.val .uint] :=
  .ite (.binop .lt rfl rfl (.simple (.local .here)) (.simple (.lit 3 rfl))) .nil .nil

/-- info: Solidity.Taclet.localValueAssign -/
#guard_msgs in #rule_of .box assign3
/-- info: Solidity.Taclet.storageFieldReadFind -/
#guard_msgs in #rule_of .box readAge
/-- info: Solidity.Taclet.storageFieldRead_unfold_rightFst -/
#guard_msgs in #rule_of .box readPeople
/-- info: Solidity.Taclet.ternaryToIf -/
#guard_msgs in #rule_of .diamond ternary
/-- info: Solidity.Taclet.storageFieldWriteSave -/
#guard_msgs in #rule_of .box writeAge
/-- info: Solidity.Taclet.storageFieldWrite_unfold_leftFst -/
#guard_msgs in #rule_of .box writePeople
/-- info: Solidity.Taclet.ifElseSplit -/
#guard_msgs in #rule_of .box iteB
/-- info: Solidity.Taclet.ifElseUnfold -/
#guard_msgs in #rule_of .box iteLt
/-- info: Solidity.Taclet.revertBox -/
#guard_msgs in #rule_of .box (Stmt.revert (C := SE) (Γ := []))
/-- info: Solidity.Taclet.revertDiamond -/
#guard_msgs in #rule_of .diamond (Stmt.revert (C := SE) (Γ := []))
/-- info: Solidity.Taclet.blockEmpty -/
#guard_msgs in #rule_of .box (Stmt.block (C := SE) (Γ := []) .nil)
/-- info: Solidity.LeanTaclet.loopExit -/
#guard_msgs in #rule_of .box (Stmt.loop (C := SE) (Γ := []) (.unwind 0) (.simple (.bool true)) .nil)
/-- info: Solidity.LeanTaclet.whileUnwind -/
#guard_msgs in #rule_of .box (Stmt.loop (C := SE) (Γ := []) (.unwind 2) (.simple (.bool true)) .nil)

/-! The axioms `Rule.premise_unique` (and so every `toStep` lemma) uses. -/

/-- info: 'Solidity.Rule.premise_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Rule.premise_unique

end Solidity.Examples.Tactics.Rules
