import Solidity.Frontend.Testing
import Solidity.Calculus.Chains
import Solidity.Calculus.Surface

/-! Compiled primitive and reference push sources, including copy independence,
self-copy, source effects and rejected observations. -/

solc_import "../../../tests/solc/PushSources.ast.json" hash 0xeda400449f8aace8
  as Solkey.Migration.PushSources testing

namespace Solidity.Examples.Tactics.PushSource

/-- All ten compiled source functions are retained. -/
example : Solkey.Migration.PushSources.report.length = 10 := rfl

-- A numbered upstream `source` capture retains its fresh-name identity.
#guard Var.ofName (toString (Var.fresh "source" 7)) == .fresh "source" 7

/-- The state root `source9` reserves every lower generated index. -/
example : (Fml.tt : Fml Solkey.Migration.PushSources []).fresh = 10 := rfl

/-- Ordinary roots such as `flag2` do not renumber TestSuite captures. -/
example : (Fml.tt : Fml TestSuite []).fresh = 1 := rfl

-- User locals named `source2` also contribute their index to freshness.
#guard (Var.ofName "source2").idx == 2

/-- No source case is silently dropped as unsupported. -/
example : (Solkey.Migration.PushSources.report.all fun r =>
    decide (r.status = .elaborated)) = true := by decide +kernel

/-- `values.push(rows[0][0])` reads the primitive source. -/
example : (Prog.run (State.init Solkey.Migration.PushSources)
    Solkey.Migration.PushSources.primitive).isOk = true := by decide +kernel

/-- A field's primitive value is captured as a value. -/
example : (Prog.run (State.init Solkey.Migration.PushSources)
    Solkey.Migration.PushSources.primitiveField).isOk = true := by decide +kernel

/-- The wrong primitive postcondition fails. -/
example : (Prog.run (State.init Solkey.Migration.PushSources)
    Solkey.Migration.PushSources.primitiveFalse).isOk = false := by decide +kernel

/-- Mutating the original row does not mutate its appended copy. -/
example : (Prog.run (State.init Solkey.Migration.PushSources)
    Solkey.Migration.PushSources.referenceCopy).isOk = true := by decide +kernel

/-- An alias interpretation of the reference source is refuted. -/
example : (Prog.run (State.init Solkey.Migration.PushSources)
    Solkey.Migration.PushSources.referenceFalse).isOk = false := by decide +kernel

/-- `rows.push(rows[0])` copies the source before extending the array. -/
example : (Prog.run (State.init Solkey.Migration.PushSources)
    Solkey.Migration.PushSources.selfCopy).isOk = true := by decide +kernel

/-- The increment in the source path happens once. -/
example : (Prog.run (State.init Solkey.Migration.PushSources)
    Solkey.Migration.PushSources.effectfulSource).isOk = true := by decide +kernel

/-- Receiver capture composes with reference-source capture. -/
example : (Prog.run (State.init Solkey.Migration.PushSources)
    Solkey.Migration.PushSources.complexReceiver).isOk = true := by decide +kernel

/-- An invalid source path reverts before appending any value. -/
example : (Prog.run (State.init Solkey.Migration.PushSources)
    Solkey.Migration.PushSources.badSourceIndex).halt? = some .revert := by decide +kernel

/-- Fresh-shaped source locals and state roots keep their mutable source meaning. -/
example : (Prog.run (State.init Solkey.Migration.PushSources)
    Solkey.Migration.PushSources.freshSourceNames).isOk = true := by decide +kernel

open scoped Solidity.Scoped
local instance : InContract := ⟨Solkey.Migration.PushSources⟩

/-- The printed primitive capture `source10` replays past root `source9`. -/
example :
    dl![.box]{ ⟨[ values.push(rows[0][0]); ]⟩ true }
    ~[storagePushValue_unfold_rightFstPrimitiveArgument]~>
    dl![.box]{ ⟨[ uint source10 = rows[0][0]; values.push(source10); ]⟩ true } := by
  sol_chain

/-- The reference capture also reads its numbered alias back at the same type. -/
example :
    dl![.box]{ ⟨[ copies.push(rows[0]); ]⟩ true }
    ~[storagePushValue_unfold_rightFstReferenceArgument]~>
    dl![.box]{ ⟨[ uint[] storage source10 = rows[0]; copies.push(source10); ]⟩ true } := by
  sol_chain

end Solidity.Examples.Tactics.PushSource
