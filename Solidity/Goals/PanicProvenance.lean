import Solidity.Tools.Goal
import Solidity.Semantics.Panic.Run.Contracts

/-!
# Code provenance of the panic-carrying runner (plan w3y-panic-provenance)

A component of finish-line goal 5 (`runCarriesPanicCodes`): every intrinsic
halt of the actual runner carries the code of the site its retained origin
failed at, for every contract, context, program and state. The implication is
stated directly on `Run.program` and `Run.stmt`, with no auxiliary predicate
and no premise on the program.

This is also what keeps an external revert payload from becoming an intrinsic
halt: an origin (`Raised`) holds a producer and the proof that it failed at
its site, so bytes that encode `Panic(uint256)` cannot supply one. The nine
site codes are checked in the pin module.
-/

namespace Solidity.Goals

open Solidity.Semantics.Panic

@[goal Solidity.Correctness.Panic.code_provenance "w3y-panic-provenance"]
def panicCodeProvenance : Prop :=
  (∀ {C : Contract} {Γ Δ : Ctx} (P : Prog C Γ Δ) (σ : State C Γ) (code : Code)
      (origin : Raised), Run.program P σ = .error (.intrinsic code origin) →
    code = siteCode origin.site) ∧
  (∀ {C : Contract} {Γ Δ : Ctx} (s : Stmt C Γ Δ) (σ : State C Γ) (code : Code)
      (origin : Raised), Run.stmt s σ = .error (.intrinsic code origin) →
    code = siteCode origin.site)

end Solidity.Goals
