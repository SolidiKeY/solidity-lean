import Solidity.Calculus.PrimitiveReturnTransport
import Solidity.Semantics.StaticCallState

/-! Storage-only conditional callback transport. Ledger and balance may change;
no whole-state equality or actual invocation/frame producer is inferred. -/
namespace Solidity
variable {C : Contract}

/-- The actual returned bytes validate the full primitive declaration before
binding/discarding. The static frame keeps storage only; the exit invariant is
required at the changed ledger/balance. Continuation effects remain unrestricted.
Declaration and site authentication remain separate producer obligations. -/
theorem ExecS.static_tryOk_storage_only {J : StateInv C}
    {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} {σ τ : State C Γ}
    {call : ExtCall C Γ} {site : Nat} {rets : Binders ρ}
    {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
    {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
    {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool}
    {bytes : List UInt8} {types : List PrimTy}
    (declared : PrimitiveReturnConsumer.Declaration types)
    (selection : PrimitiveReturnConsumer.Projection declared.binders rets)
    (mode : call.mode = .static) (_invocation : call.invocation = .site site)
    (frame : StaticInvocation.Frame call.mode σ (.returned bytes) τ)
    (entry : J.at σ)
    (exit : J.at (σ.resumeCall call.mode τ.storage τ.net τ.selfBalance))
    {rest : List Semantics.Word} {r : TEnv C σ.H ρ}
    (decoded : PrimitiveReturnConsumer.consume declared selection bytes = .ok (r, rest)) {result : COut C σ.H Γ₁}
    (nonself : self = true → (call.addr.evalT σ).1 ≠ 0 ∧
      (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1)
    (cont : ExecP J ((σ.resumeCall call.mode τ.storage τ.net τ.selfBalance).withEnv
      (TEnv.append ρ r σ.env)) ok result) :
    ExecS J σ (.tryCall call rets ok err code pnc other sargs sbody self)
      (result.map (Out.drop ((Ext.append Γ ρ).trans ok.ext))) := by
  obtain ⟨vs, tail, read, decode⟩ :=
    PrimitiveReturnConsumer.success_reads_actual_words declared selection decoded
  exact ExecS.tryOk (J := J) (σ := σ) (call := call) (self := self)
    (st := match call.mode with | .call => τ.storage | .static => σ.storage) (nt := τ.net) (sb := τ.selfBalance)
    entry exit decode cont nonself

/-- info: 'Solidity.ExecS.static_tryOk_storage_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExecS.static_tryOk_storage_only
end Solidity
