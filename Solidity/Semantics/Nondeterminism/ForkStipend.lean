import Solidity.Semantics.Nondeterminism.Fork
import Solidity.Stipend.Rule

/-!
# The stipend rule at a fork (S6.1)

`Solidity/Stipend/Rule.lean` fixes the stipend rule to Osaka's cold costs
(`osakaCold`) and the pin's 2300-gas stipend. `ForkSpec.stipendRule` reads
both from the fork, and `ForkSpec.osaka_stipendRule` shows the existing rule
is the Osaka instance. The negative control is a fork without a stipend,
which rejects even the empty body that Osaka admits.
-/

namespace Solidity.Semantics.Nondeterminism

open Solidity.Stipend

namespace ForkSpec

/-- The stipend rule's constants at a fork. -/
def costModel (F : ForkSpec) : CostModel := ⟨F.stipendUnit, F.stipendReserve⟩

/-- **The stipend rule at a fork.** -/
def stipendRule (F : ForkSpec) (C : Contract) : Roadmap.Evm.StipendRule (Body C) where
  fits b := fitsWith F.costModel F.gas.callStipend b = true

theorem osaka_costModel : osaka.costModel = osakaCold := rfl

/-- **The existing rule is the Osaka instance.** -/
theorem osaka_stipendRule (C : Contract) : osaka.stipendRule C = rule C := rfl

/-- A fork with no stipend. -/
def noStipend : ForkSpec := { osaka with gas := { GasConstants.osaka with callStipend := 0 } }

/-- The empty `receive` body. -/
def emptyBody (C : Contract) : Body C := ⟨(.nil : Prog C [] [])⟩

/-- Osaka admits the empty body (`Stipend.empty_fits`). -/
theorem osaka_fits_empty (C : Contract) : (osaka.stipendRule C).fits (emptyBody C) := empty_fits

/-- Negative control: with no stipend the empty body does not fit. -/
theorem noStipend_rejects_empty (C : Contract) : ¬ (noStipend.stipendRule C).fits (emptyBody C) := by
  intro h
  cases h

end ForkSpec

end Solidity.Semantics.Nondeterminism
/-- info: 'Solidity.Semantics.Nondeterminism.ForkSpec.osaka_stipendRule' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkSpec.osaka_stipendRule
/-- info: 'Solidity.Semantics.Nondeterminism.ForkSpec.noStipend_rejects_empty' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkSpec.noStipend_rejects_empty
/-- info: 'Solidity.Semantics.Nondeterminism.ForkSpec.osaka_fits_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkSpec.osaka_fits_empty
