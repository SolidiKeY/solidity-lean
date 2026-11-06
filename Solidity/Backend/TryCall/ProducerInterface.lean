import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV3

/-! Typed obligations for checked try-call emitters. This signature does not
provide an emitter, add admission, implement unknown calls, or equate core
Evm.run with EvmYul/compiled Solidity. A producer must exhibit BOTH source
outcomes at represented entries for its SAME statement and emitted plan. -/
namespace Solidity.Backend.TryCall
open Evm Evm.Memory
namespace RF
export InternalFlow.RuntimeFrame.InterfaceV1 (Emission Entry ReturnClaim BareRevertClaim Returned)
end RF

/-- The existing intrinsic tryCall constructor, with all scopes retained.
No callback/result oracle or untyped source representation is introduced. -/
structure Site (C : Contract) (Γ : Ctx) where
  returns : Ctx
  parameters : Ctx
  calleeEnd : Ctx
  panicBinder : Ctx
  okEnd : Ctx
  errorEnd : Ctx
  panicEnd : Ctx
  otherEnd : Ctx
  call : ExtCall C Γ
  returnBinders : Binders returns
  ok : Prog C (returns ++ Γ) okEnd
  error : Prog C Γ errorEnd
  code : CodeBinder panicBinder
  panic : Prog C (panicBinder ++ Γ) panicEnd
  other : Prog C Γ otherEnd
  arguments : Args C Γ parameters
  callee : Prog C (returns ++ parameters) calleeEnd
  self : Bool

def Site.statement {C : Contract} {Γ : Ctx} (site : Site C Γ) : Stmt C Γ Γ :=
  .tryCall site.call site.returnBinders site.ok site.error site.code
    site.panic site.other site.arguments site.callee site.self

/-- Signature-only producer contract. Return/bare-revert cover every actual
Entry; the two independent outcome witnesses prevent an empty-entry or
success-only certificate. These minimum V2 witnesses are NOT universal
approved-profile coverage (V3 EntryCoverage), deployment provenance or a
physical gas/fuel/host bound. There is no default instance. -/
structure Producer {C : Contract} {Γ : Ctx} (b : Nat) (fragment : Frag Γ) (site : Site C Γ) where
  plan : RF.Emission C Γ Γ
  returns : RF.ReturnClaim b fragment site.statement plan
  reverts : RF.BareRevertClaim b fragment site.statement plan
  successful : InternalFlow.RuntimeFrame.InterfaceV2.SuccessfulEntry b fragment site.statement plan
  reverting : InternalFlow.RuntimeFrame.InterfaceV2.RevertingEntry b fragment site.statement plan

end Solidity.Backend.TryCall
