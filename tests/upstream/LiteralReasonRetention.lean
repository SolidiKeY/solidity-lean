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

private def failing : Prog Reverter [] [] := sol[Reverter]{ try this.fail() {} catch {} }
private def succeeding : Prog Reverter [] [] := sol[Reverter]{ try this.succeeds() {} catch {} }
private def direct : Prog Reverter [] [] := sol[Reverter]{ try this.direct() {} catch {} }
private def dynamic : Prog Reverter [] [] := sol[Reverter]{ try this.dynamic() {} catch {} }

private def isAllocator {C : Contract} {Γ Δ : Ctx} (s : Stmt C Γ Δ) : Bool :=
  Stmt.casesOn (motive_1 := fun _ _ _ => Bool) s
    (assign := fun _ _ => false) (rebind := fun _ _ => false)
    (assignLocal := fun _ _ => false) (declLocal := fun _ _ _ => false)
    (declStorage := fun _ _ _ => false) (opAssign := fun _ _ _ _ _ => false)
    (incDec := fun _ _ _ => false) (assignIncDec := fun _ _ _ _ _ => false)
    (assignLocalPush := fun _ _ => false) (pushOpAssign := fun _ _ _ _ _ => false)
    (pushIncDec := fun _ _ _ => false) (push := fun _ _ _ => false) (pop := fun _ => false)
    (transfer := fun _ _ => false) (send := fun _ _ _ _ => false)
    (declMem := fun _ _ init _ _ => match init with
      | some (.newArr ..) => true
      | _ => false) (rebindMem := fun _ _ => false)
    (assignFromMem := fun _ _ => false) (assignMem := fun _ _ => false)
    (delete := fun _ => false) (deleteMem := fun _ _ => false)
    (assignNew := fun _ _ _ => false) (ite := fun _ _ _ => false)
    (require := fun _ => false) (assert := fun _ => false)
    (revert := false) (assumeFalse := false)
    (call := fun _ _ _ _ => false) (callReceiver := fun _ _ _ _ _ => false)
    (callReceiverPush := fun _ _ _ _ _ _ => false)
    (tryCall := fun _ _ _ _ _ _ _ _ _ _ => false) (callRec := fun _ _ _ _ _ => false)
    (loop := fun _ _ _ => false) (block := fun _ => false)
    (revertData := fun _ => false) (catchData := fun _ _ _ _ _ _ _ _ => false)

private def observeTryBody {C : Contract} {α : Type} (fallback : α)
    (observe : ∀ {Γ Δ : Ctx}, Prog C Γ Δ → α)
    {Γ Δ : Ctx} (s : Stmt C Γ Δ) : α :=
  Stmt.casesOn (motive_1 := fun _ _ _ => α) s
    (assign := fun _ _ => fallback) (rebind := fun _ _ => fallback)
    (assignLocal := fun _ _ => fallback) (declLocal := fun _ _ _ => fallback)
    (declStorage := fun _ _ _ => fallback) (opAssign := fun _ _ _ _ _ => fallback)
    (incDec := fun _ _ _ => fallback) (assignIncDec := fun _ _ _ _ _ => fallback)
    (assignLocalPush := fun _ _ => fallback) (pushOpAssign := fun _ _ _ _ _ => fallback)
    (pushIncDec := fun _ _ _ => fallback) (push := fun _ _ _ => fallback) (pop := fun _ => fallback)
    (transfer := fun _ _ => fallback) (send := fun _ _ _ _ => fallback)
    (declMem := fun _ _ _ _ _ => fallback) (rebindMem := fun _ _ => fallback)
    (assignFromMem := fun _ _ => fallback) (assignMem := fun _ _ => fallback)
    (delete := fun _ => fallback) (deleteMem := fun _ _ => fallback)
    (assignNew := fun _ _ _ => fallback) (ite := fun _ _ _ => fallback)
    (require := fun _ => fallback) (assert := fun _ => fallback)
    (revert := fallback) (assumeFalse := fallback)
    (call := fun _ _ _ _ => fallback) (callReceiver := fun _ _ _ _ _ => fallback)
    (callReceiverPush := fun _ _ _ _ _ _ => fallback)
    (tryCall := fun _ _ _ _ _ _ _ _ body _ => observe body) (callRec := fun _ _ _ _ _ => fallback)
    (loop := fun _ _ _ => fallback) (block := fun _ => fallback)
    (revertData := fun _ => fallback) (catchData := fun _ _ _ _ _ _ _ _ => fallback)

private def startsAllocator {C : Contract} {Γ Δ : Ctx} (p : Prog C Γ Δ) : Bool :=
  Prog.casesOn (motive_2 := fun _ _ _ => Bool) p false (fun s _ => isAllocator s)

private def calleeAllocatesFirst {C : Contract} {Γ Δ : Ctx} (p : Prog C Γ Δ) : Bool :=
  Prog.casesOn (motive_2 := fun _ _ _ => Bool) p false
    (fun s _ => observeTryBody false (fun body => startsAllocator body) s)

private def calleeData {C : Contract} {Γ Δ : Ctx} (p : Prog C Γ Δ) : Option DSet :=
  Prog.casesOn (motive_2 := fun _ _ _ => Option DSet) p none
    (fun s _ => observeTryBody none (fun body => CatchKind.reason.datas body) s)

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

private def checked : Prog Reverter [] [] := sol[Reverter]{
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
