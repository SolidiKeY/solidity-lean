import Solidity.Frontend.Testing

/-!
# Native push suffixes from Solidity source

The pinned compiler fixture exercises all nine discarded suffix forms,
including indexed receivers, RHS-before-receiver capture and arithmetic
failure. These concrete execution checks do not claim general-state closure.
-/

solc_import "../../../tests/solc/PushSuffixes.ast.json" hash 0x1afe1b8baa8f36f1
  as Solkey.Migration.PushSuffixes testing

namespace Solidity.Examples.Tactics.PushSuffixSource

/-- All helpers and public fixture functions are retained. -/
example : Solkey.Migration.PushSuffixes.report.length = 22 := rfl

/-- No source row is silently left unsupported. -/
example : (Solkey.Migration.PushSuffixes.report.all fun r =>
    decide (r.status = .elaborated)) = true := by decide +kernel

/-- A well-typed recycled primitive slot may retain an old nonzero value. -/
def dirtyStorage : Storage Solkey.Migration.PushSuffixes :=
  .cons (.array .nil (.cons (.prim ⟨99, rfl⟩) .nil) (by decide))
    (.cons (.array .nil .nil (by decide))
      (.cons (.array .nil .nil (by decide))
        (.cons (.prim ⟨0, rfl⟩) (.cons (.prim ⟨0, rfl⟩)
          (.cons (.array .nil .nil (by decide)) (.cons (.prim ⟨0, rfl⟩) .nil))))))

/-- A nonzero primitive shadow is typed but fails the tight entry check. -/
example : dirtyStorage.wtB = false := by
  unfold Storage.wtB Storage.shapeB SFields.allB
  decide +kernel

/-- The suffix resets its recycled slot before adding three. -/
example : (Prog.run ((State.init Solkey.Migration.PushSuffixes).withStorage dirtyStorage)
    Solkey.Migration.PushSuffixes.recycled).isOk = true := by decide +kernel

/-- The nine signed suffixes update the appended element. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.signedOps).isOk = true := by decide +kernel

/-- The unsigned compound forms and discarded increments succeed. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.unsignedOps).isOk = true := by decide +kernel

/-- Every suffix also accepts an indexed receiver. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.nestedOps).isOk = true := by decide +kernel

/-- The RHS increments `cursor` before the receiver increments it once more. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.effectfulIndex).isOk = true := by decide +kernel

/-- The RHS reads `seen = 0` before the receiver's `next()` changes it. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.effectfulCall).isOk = true := by decide +kernel

/-- A false postcondition fails after an otherwise successful suffix. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.falsePost).isOk = false := by decide +kernel

/-- A zero divisor reverts. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.zeroDivisor).halt? = some .revert := by decide +kernel

/-- A zero remainder divisor reverts. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.zeroRemainder).halt? = some .revert := by decide +kernel

/-- Discarding a prefix value does not hide unsigned underflow. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.preUnderflow).halt? = some .revert := by decide +kernel

/-- Discarding a postfix value does not hide unsigned underflow. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.postUnderflow).halt? = some .revert := by decide +kernel

/-- A source local named like a capture still reads before the receiver effect. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.freshLocal).isOk = true := by decide +kernel

/-- The former wrong value from a fresh-shaped source local is rejected. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.freshLocalFalse).isOk = false := by decide +kernel

/-- A fresh-shaped source parameter remains mutable. -/
example : (Prog.run ((State.init Solkey.Migration.PushSuffixes).push (t := .val .uint) ⟨0, rfl⟩)
    Solkey.Migration.PushSuffixes.freshParameter).isOk = true := by decide +kernel

/-- The false result from delaying a fresh-shaped parameter's read is rejected. -/
example : (Prog.run ((State.init Solkey.Migration.PushSuffixes).push (t := .val .uint) ⟨0, rfl⟩)
    Solkey.Migration.PushSuffixes.freshParameterFalse).isOk = false := by decide +kernel

/-- A state variable is never mistaken for an already captured local. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.freshState).isOk = true := by decide +kernel

/-- The state-variable variant of the false claim is rejected. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.freshStateFalse).isOk = false := by decide +kernel

/-- The source boundary also fixes fresh-shaped names in nested RHS arithmetic. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.freshBinary).isOk = true := by decide +kernel

/-- A nested arithmetic expression cannot prove its former wrong result. -/
example : (Prog.run (State.init Solkey.Migration.PushSuffixes)
    Solkey.Migration.PushSuffixes.freshBinaryFalse).isOk = false := by decide +kernel

end Solidity.Examples.Tactics.PushSuffixSource
