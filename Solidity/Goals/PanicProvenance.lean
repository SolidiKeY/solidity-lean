import Solidity.Tools.Goal
import Solidity.Semantics.Panic.Run.Contracts

/-!
# Code provenance of the panic-carrying runner (plan w3y-panic-provenance)

A component of finish-line goal 5 (`runCarriesPanicCodes`): every intrinsic
halt of the actual runner carries the code of the site its retained origin
failed at, for every contract, context, program and state; the nine sites
carry the nine solc codes; an external revert payload never becomes an
intrinsic halt. The implication is stated directly on `Run.program` and
`Run.stmt`, with no auxiliary predicate and no premise on the program.
-/

namespace Solidity.Goals

open Solidity.Panic Solidity.Semantics.Panic

@[goal Solidity.Correctness.Panic.code_provenance "w3y-panic-provenance"]
def panicCodeProvenance : Prop :=
  (∀ {C : Contract} {Γ Δ : Ctx} (P : Prog C Γ Δ) (σ : State C Γ) (code : Code)
      (origin : Raised), Run.program P σ = .error (.intrinsic code origin) →
    code = siteCode origin.site) ∧
  (∀ {C : Contract} {Γ Δ : Ctx} (s : Stmt C Γ Δ) (σ : State C Γ) (code : Code)
      (origin : Raised), Run.stmt s σ = .error (.intrinsic code origin) →
    code = siteCode origin.site) ∧
  -- The nine original sites carry the nine solc `Panic(uint256)` codes.
  (∀ site : Site, (siteCode site).code = site.code) ∧
  ((siteCode .assertion).code = 0x01 ∧ (siteCode .arithmetic).code = 0x11 ∧
    (siteCode .zeroDivisor).code = 0x12 ∧ (siteCode .enumConversion).code = 0x21 ∧
    (siteCode .storageEncoding).code = 0x22 ∧ (siteCode .emptyPop).code = 0x31 ∧
    (siteCode .bounds).code = 0x32 ∧ (siteCode .allocation).code = 0x41 ∧
    (siteCode .zeroInternalFunction).code = 0x51) ∧
  -- External revert bytes are never an intrinsic halt, even when they encode
  -- `Panic(uint256)`: the halts differ, and catching such a payload returns
  -- exactly one handler's outcome, so no origin is made from the bytes.
  (∀ (code : Code) (origin : Raised) (data : List UInt8),
    Halt.intrinsic code origin ≠ .externalRevert data) ∧
  (∀ {α : Type} (data : List UInt8) (err : Unit → EvalResult α)
      (pnc : Semantics.Word → EvalResult α) (other : Unit → EvalResult α),
    Run.catchHalt (.externalRevert data) err pnc other = err () ∨
    (∃ word, Run.catchHalt (.externalRevert data) err pnc other = pnc word) ∨
    Run.catchHalt (.externalRevert data) err pnc other = other ())

end Solidity.Goals
