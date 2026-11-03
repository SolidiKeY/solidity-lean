import Solidity.Lowering.V07.SourceReads
import Solidity.Semantics.DeferredSource

/-! G16/G17 local operand interface for control-flow consumers. This uses the
published deferred operand runner, reads its value before temporary removal,
and preserves the complete caller state. Effectful operands are still open. -/
namespace Solidity.Lowering.V07

theorem local_operand_run {C : Contract} {Γ : Ctx} {p : PrimTy}
    (target : State C Γ) (j : Idx Γ (.val p)) (v : p.Denote)
    (read : TEnv.get j target.env = v) :
    (DeferredSource.Operand.ofSrc (.val (.simple (.local j)))).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim v) := by
  change (do
    let a ← (Prog.nil : Prog C Γ Γ).run target
    let value ← (Src.val (.simple (.local j)) : Src C Γ (.prim p)).valueT a.st
    pure ((⟨a.st.drop Ext.refl,a.ext⟩ : Out C target.H Γ),value)) = _
  rw [Prog.run_nil]
  change (do
    let value ← (Src.val (.simple (.local j)) : Src C Γ (.prim p)).valueT target
    pure ((⟨target,List.prefix_refl _⟩ : Out C target.H Γ),value)) = _
  change (do
    let x ← (Except.ok (TEnv.get j target.env) : TRes p.Denote)
    pure ((⟨target,List.prefix_refl _⟩ : Out C target.H Γ),SVal.prim x)) = _
  rw [read]
  rfl

theorem source_local_operand_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (t : Source.IntTy)
    (i : Source.Idx srcΓ (.int t)) (j : Idx Γ (.val (integerPrim t)))
    (x : Int) (range : t.lo ≤ x ∧ x ≤ t.hi)
    (sourceRead : source.1.get i = .int x range)
    (targetRead : TEnv.get j target.env = integerValue t x range) :
    (Source.evalE G F (fuel+1) (.local i)).run source = (.ok (.val (.int x range)),source) ∧
    (DeferredSource.Operand.ofSrc (.val (.simple (.local j)))).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim (integerValue t x range)) ∧
    IntValueRel t (.int x range : Source.Val E.layout (.int t)) (integerValue t x range) := by
  exact ⟨(source_local_transport G F fuel source target t i j x range sourceRead targetRead).1,
    local_operand_run target j _ targetRead,integer_related t x range⟩

theorem local_operand_extension {C : Contract} {Γ Δ : Ctx} {p : PrimTy}
    (target : State C Γ) (j : Idx Γ (.val p)) (v : p.Denote)
    (read : TEnv.get j target.env = v) (thin : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    ((DeferredSource.Operand.ofSrc (.val (.simple (.local j)))).wk thin).run
      (target.lift thin extra) =
    liftedT₂ thin extra (.ok ((⟨target,List.prefix_refl _⟩ : Out C target.H Γ),SVal.prim v)) := by
  rw [DeferredSource.Operand.run_wk,local_operand_run target j v read]

end Solidity.Lowering.V07
