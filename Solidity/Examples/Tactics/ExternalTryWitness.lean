import Solidity.Tools.Run
import Solidity.Calculus.Surface
import Solidity.Semantics.ExternalTryWitness
import Solidity.Counterexamples.DiamondTry

/-!
# Source-shaped external try controls with explicit oracle inputs

Normal completion is kernel checked; ordered storage observations are pinned
below. These are concrete deterministic executions, not universal source
obligations or compiler/EVM equivalence claims.
-/

namespace Solidity.Examples.Tactics.ExternalTryWitness
open Semantics

/-- Storage observations kept distinct across the four alternatives. -/
def Probe : Contract := contract!{ uint tag; uint reasonCode; }
local instance : InContract := ⟨Probe⟩
open scoped Scoped

/-- Source common to all four external alternatives, without a box annotation. -/
def probe : Prog Probe [] [] := sol{
  try I(7).fetch() returns (uint v) { tag = v; }
  catch Error(string memory) { tag = 2; }
  catch Panic(uint c) { tag = 3; reasonCode = c; }
  catch { tag = 4; }
}

/-- Only the transaction oracle differs between runs. -/
def input (r : ExtResult) : State Probe [] :=
  { State.init Probe with tx := { ext := [(⟨⟨7, rfl⟩, "fetch", []⟩, r)] } }

/-- Solidity's successful external return binds `v = 9`. -/
theorem success_returns : (Prog.run (input (.ok [⟨9, rfl⟩])) probe).halt? = none := by
  decide +kernel

/-- An external Error selects the Error clause. -/
theorem error_returns : (Prog.run (input (.error [])) probe).halt? = none := by
  decide +kernel

/-- An external Panic selects the Panic clause and binds its code. -/
theorem panic_returns : (Prog.run (input (.panic ⟨17, rfl⟩)) probe).halt? = none := by
  decide +kernel

/-- Other external failures select the catch-all. -/
theorem other_returns : (Prog.run (input (.other [])) probe).halt? = none := by
  decide +kernel

/-- All storage observations, in the same order for every alternative. -/
def observations (r : ExtResult) : TRes (Option String × Option String) := do
  let σ ← Prog.runT (input r) probe
  pure (Tools.fmtRoot σ.storage "tag", Tools.fmtRoot σ.storage "reasonCode")

/-- info: Except.ok (some "9", some "0") -/
#guard_msgs in #eval observations (.ok [⟨9, rfl⟩])
/-- info: Except.ok (some "2", some "0") -/
#guard_msgs in #eval observations (.error [])
/-- info: Except.ok (some "3", some "17") -/
#guard_msgs in #eval observations (.panic ⟨17, rfl⟩)
/-- info: Except.ok (some "4", some "0") -/
#guard_msgs in #eval observations (.other [])

/-- No entry means a caller revert, even though every catch would return. -/
theorem missing_entry : (Prog.run (State.init Probe) probe).halt? = some .revert := by
  decide +kernel

/-- Missing return words fail before any catch. -/
theorem malformed_return : (Prog.run (input (.ok [])) probe).halt? = some .revert := by
  decide +kernel

/-- A successful deterministic oracle does not discharge the callback diamond,
under either payment flag. -/
theorem callback_refused (pay : Bool) :
    ¬ holdsC .tt pay (input (.ok [⟨9, rfl⟩]))
      (dl!{ ⟨ try I(7).fetch() returns (uint v) { tag = v; }
        catch Error(string memory) { tag = 2; }
        catch Panic(uint c) { tag = 3; reasonCode = c; }
        catch { tag = 4; }; ⟩ true } : Fml Probe []) := by
  apply Counterexamples.DiamondTry.callback_diamond_false

end Solidity.Examples.Tactics.ExternalTryWitness
