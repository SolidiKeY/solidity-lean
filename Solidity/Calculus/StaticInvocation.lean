import Solidity.Semantics.StaticInvocation

/-! Conditional H22 callback transport from an actual intrinsic storage frame.
The existing conservative ExecS relation is not narrowed here. Byte/word ABI
correspondence and source/native adequacy remain separate obligations. -/
namespace Solidity
variable {C : Contract}

/-- Direct field hypotheses replace the old indexed call and side registry.
A site label alone supplies no source/native authentication; neither the
operational frame nor the decoder premise is inferred from it. -/
theorem ExecS.static_tryOk_of_storage_frame {J : StateInv C}
    {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} {σ τ : State C Γ}
    {call : ExtCall C Γ} {site : Nat} {rets : Binders ρ}
    {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
    {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
    {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool}
    {bytes : List UInt8}
    (mode : call.mode = .static) (_invocation : call.invocation = .site site)
    (frame : StaticInvocation.Frame call.mode σ (.returned bytes) τ)
    (ledger : τ.net = σ.net) (balance : τ.selfBalance = σ.selfBalance)
    (entry : J.at σ)
    {vs rest : List Semantics.Word} {r : TEnv C σ.H ρ}
    (decode : rets.decodeT vs = .ok (r, rest)) {result : COut C σ.H Γ₁}
    (nonself : self = true → (call.addr.evalT σ).1 ≠ 0 ∧
      (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1)
    (cont : ExecP J ((σ.havoc τ.storage τ.net τ.selfBalance).withEnv
      (TEnv.append ρ r σ.env)) ok result) :
    ExecS J σ (.tryCall call rets ok err code pnc other sargs sbody self)
      (result.map (Out.drop ((Ext.append Γ ρ).trans ok.ext))) := by
  have storage := frame.call_storage mode
  rw [storage, ledger, balance] at cont
  exact ExecS.tryOk (J := J) (σ := σ) (call := call) (self := self)
    (st := σ.storage) (nt := σ.net) (sb := σ.selfBalance)
    entry entry decode cont nonself
end Solidity
