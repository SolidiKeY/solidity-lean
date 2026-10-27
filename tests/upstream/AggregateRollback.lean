import Solidity.Semantics.RevertMemory
open Solidity Solidity.Semantics
namespace AggregateRollback
/-- A failing self-call's aggregate error bytes survive, while catch starts
from the caller's original full typed state, including heap and storage.
The nonzero self-address and actual callee halt premises remain explicit. -/
theorem raw_catch_restores_caller {C : Contract} {Γ ρ ps Γf Γ₁ : Ctx}
    (c : ExtCall C Γ) (rets : Binders ρ) (args : Args C Γ ps)
    (hs : Ext (ρ ++ ps) Γf) (callee : TStep C (ρ ++ ps) Γf)
    (h₁ : Ext (.mem bytesR :: Γ) Γ₁) (body : TStep C (.mem bytesR :: Γ) Γ₁)
    (σ : State C Γ) (d : List UInt8) (hlen : d.length < 2^256)
    (hnz : (c.addr.evalT σ).1 ≠ 0)
    (hself : (c.addr.evalT σ).1 = σ.tx.selfAddress.1)
    (hcall : TRun.call args (.rets rets) hs callee σ = .error (THalt.ofData d)) :
    TRun.catchData c rets args hs callee true .raw h₁ body σ =
      (TRun.litBytesT d body σ).map
        (fun o => ⟨o.st.drop ((Ext.push .refl).trans h₁), o.ext⟩) :=
  TRun.catchData_self_data c rets args hs callee .raw h₁ body σ d d hnz hself hcall (by simp only [CatchKind.decode, if_pos hlen])
#print axioms raw_catch_restores_caller
end AggregateRollback
