import Solidity.Calculus.CallbackDerive

/-! Literal Error payloads retain their eager memory prefix. These controls
check the emitted typed program and an actual normal self-call execution. -/
namespace Solidity.Tests.LiteralReasonRetention
open Semantics

def Reverter : Contract := contract!{
  function fail() { require(false, hex"626f6f6d"); }
  function succeeds() { require(true, hex"626f6f6d"); }
  function direct() { revert(hex"626f6f6d"); }
  function dynamic() { string memory msg = hex"626f6f6d"; require(false, msg); }
}

private def failing := sol[Reverter]{ try this.fail() {} catch {} }
private def succeeding := sol[Reverter]{ try this.succeeds() {} catch {} }
private def direct := sol[Reverter]{ try this.direct() {} catch {} }
private def dynamic := sol[Reverter]{ try this.dynamic() {} catch {} }

private def isAllocator {C : Contract} {Γ Δ : Ctx} (s : Stmt C Γ Δ) : Bool :=
  match s with
  | .declMem _ _ (some (.newArr ..)) _ _ => true
  | _ => false

private def startsAllocator {C : Contract} {Γ Δ : Ctx} (p : Prog C Γ Δ) : Bool :=
  match p with
  | .cons s _ => isAllocator s
  | _ => false

private def calleeAllocatesFirst {C : Contract} {Γ Δ : Ctx} (p : Prog C Γ Δ) : Bool :=
  match p with
  | .cons (.tryCall _ _ _ _ _ _ _ _ body _) _ => startsAllocator body
  | _ => false

private def calleeData {C : Contract} {Γ Δ : Ctx} (p : Prog C Γ Δ) : Option DSet :=
  match p with
  | .cons (.tryCall _ _ _ _ _ _ _ _ body _) _ => CatchKind.reason.datas body
  | _ => none

/-- Both require outcomes and direct revert retain the allocator. -/
theorem allocationsRemain :
    (calleeAllocatesFirst failing && calleeAllocatesFirst succeeding &&
      calleeAllocatesFirst direct) = true := by decide +kernel

/-- Literal bytes remain available to the existing catch-data rule. -/
theorem exactPayload : calleeData failing = some ([encodeError [98, 111, 111, 109]], []) ∧
    calleeData direct = some ([encodeError [98, 111, 111, 109]], []) := by decide +kernel

/-- Named/dynamic memory reasons retain the existing conservative path. -/
theorem dynamicUnchanged : calleeData dynamic = none := by decide +kernel

local instance : InContract := ⟨Reverter⟩
open scoped Scoped

private def checked := sol[Reverter]{
  try this.fail() { assert(false); } catch Error(string memory reason) {
    assert(reason.length == 4);
    assert(reason[0] == 98);
    assert(reason[3] == 109);
  } catch { assert(false); }
}

/-- The caught literal's assertions end normally at the same fixed budgets. -/
theorem normalWitness :
    (Prog.runFrames { State.init Reverter with tx := { selfAddress := ⟨7, rfl⟩ } }
      checked .nil).halt? = none := by decide +kernel

#print axioms allocationsRemain
#print axioms exactPayload
#print axioms dynamicUnchanged
#print axioms normalWitness

end Solidity.Tests.LiteralReasonRetention
