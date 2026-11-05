import Solidity.Semantics.RunFrame

/-! A standalone typed caller-resumption helper. It preserves the caller skeleton, selects storage by mode and leaves ledger/balance free. The helper is not wired into opaque callback execution by this increment; invocation authentication and precise static self-execution obligations remain separate. -/
namespace Solidity
variable {C : Contract} {Γ : Ctx}

def State.resumeCall (σ : State C Γ) (mode : CallMode) (st : Storage C)
    (net : Ledger) (balance : PrimTy.uint.Denote) : State C Γ :=
  σ.havoc (match mode with | .call => st | .static => σ.storage) net balance

theorem State.resumeCall_call (σ : State C Γ) (st : Storage C)
    (net : Ledger) (balance : PrimTy.uint.Denote) :
    σ.resumeCall .call st net balance = σ.havoc st net balance := rfl

theorem State.resumeCall_static (σ : State C Γ) (st : Storage C)
    (net : Ledger) (balance : PrimTy.uint.Denote) :
    σ.resumeCall .static st net balance = σ.havoc σ.storage net balance := rfl

theorem State.resumeCall_self (σ : State C Γ) (mode : CallMode) :
    σ.resumeCall mode σ.storage σ.net σ.selfBalance = σ := by
  cases mode <;> rfl

end Solidity
