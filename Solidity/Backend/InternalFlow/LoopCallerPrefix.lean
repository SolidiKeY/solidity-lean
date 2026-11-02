import Solidity.Backend.InternalFlow.LoopLocalTarget
/-! Source/frame consumers for healthy reached horizons. Generic target-prefix
execution remains the read-only producer's responsibility. No new evaluator
or replacement for its private MemoryTurn/iterator theorem is defined here. -/
namespace Solidity.Backend.InternalFlow.LoopCallerPrefix
open Evm Evm.Memory LocalStoreFlow
variable {C : Contract} {Γ Δ Ξ : Ctx}

/-- Public condition correctness supplies an actual word execution. -/
theorem condition_run {b L frame : Nat} {F : Frag Γ} {c : Val C Γ .bool}
    {cond : List Evm.Instr} (cert : ValFrag b F c cond)
    {σ : State C Γ} {base : Nat → Fin W} {m : Evm.Machine}
    (repr : StateRepr L b frame F σ base m) (v : Bool) (evaluated : c.evalT σ = .ok v) :
    run cond m = .ok (m.push (.val (bword v))) 0 := by
  rcases cert.correct repr with ⟨value,word,hs,hw,ht⟩ | ⟨hs,ht⟩
  · have same : value = v := Except.ok.inj (hs.symm.trans evaluated)
    subst value
    rw [hw.bool_inv] at ht
    exact ht
  · rw [evaluated] at hs; contradiction

/-- C38's per-binding source law supplies a complete protected environment
at every real running/successful horizon, including nonterminating prefixes. -/
theorem captured {body : Prog C Γ Δ} (protect : Thin Ξ Γ)
    (plans : ∀ {t : LTy} (i : Idx Ξ t), ProgPlan t body (i.wk protect))
    (c : Val C Γ .bool) (σ : State C Γ) (n : Nat) (out : Solidity.Out C σ.H Γ)
    (source : TLoop.iterN (scopedLoopBody body) (fun o => c.evalT o.st) n
      ⟨σ,List.prefix_refl _⟩ = .inl out ∨
      TLoop.iterN (scopedLoopBody body) (fun o => c.evalT o.st) n
      ⟨σ,List.prefix_refl _⟩ = .inr (.ok out)) :
    TEnv.thin protect out.st.env = TEnv.wk out.ext Ξ (TEnv.thin protect σ.env) := by
  apply TEnv.ext
  intro t i
  rw [CallerFrame.read_thin,TEnv.get_wk,CallerFrame.read_thin]
  exact (plans i).loop_prefix c σ n out source

/-- Eliminate a genuinely represented reached state into caller observations.
This DOES NOT manufacture execution/StateRepr from the source prefix. Those
producer premises are explicit and must be independently discharged. -/
theorem represented {b L frame : Nat} {F : Frag Γ} {body : Prog C Γ Δ}
    (protect : Thin Ξ Γ) (plans : ∀ {t : LTy} (i : Idx Ξ t), ProgPlan t body (i.wk protect))
    (c : Val C Γ .bool) (σ : State C Γ) (n : Nat) (out : Solidity.Out C σ.H Γ)
    (source : TLoop.iterN (scopedLoopBody body) (fun o => c.evalT o.st) n
      ⟨σ,List.prefix_refl _⟩ = .inl out ∨
      TLoop.iterN (scopedLoopBody body) (fun o => c.evalT o.st) n
      ⟨σ,List.prefix_refl _⟩ = .inr (.ok out))
    {base base' : Nat → Fin W} {m : Evm.Machine}
    (repr : StateRepr L b frame F out.st base' m) (addresses : BaseExtends σ.H base base') :
    TEnv.thin protect out.st.env = TEnv.wk out.ext Ξ (TEnv.thin protect σ.env) ∧
    (∀ (R : RefTy) (i : Idx Ξ (.mem R)) (r : HRef σ.H R),
      TEnv.get (i.wk protect) σ.env = some r → m.mem (cellOf b (i.wk protect)) = .val (base r.id)) ∧
    (∀ (p : PrimTy) (i : Idx Ξ (.val p)),
      ReprV p (TEnv.get (i.wk protect) σ.env) (m.mem (cellOf b (i.wk protect)))) := by
  have env := captured protect plans c σ n out source
  exact ⟨env,CallerView.represented out protect env repr addresses,
    fun p i => CallerView.represented_value_drop out Ext.refl protect env repr i⟩

/-- Keep the published condition error classification; no data projection
is used to identify panic, exhaustion, divergence or byte failures as revert. -/
theorem condition_revert {b L frame : Nat} {F : Frag Γ} {c : Val C Γ .bool}
    {code : List Evm.Instr} (cert : ValFrag b F c code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Evm.Machine}
    (repr : StateRepr L b frame F σ base m) (failed : c.evalT σ = .error .revert) :
    run code m = .revert := by
  rcases cert.correct repr with ⟨v,w,hs,hw,ht⟩ | ⟨hs,ht⟩
  · rw [failed] at hs; contradiction
  · exact ht

/-- Finite admitted body failure, from its real checked producer and capacity. -/
theorem program_revert {b L frame : Nat} {F : Frag Γ} {P : Prog C Γ Δ}
    (cert : Calls.Program b F P) {σ : State C Γ} {base : Nat → Fin W} {m : Evm.Machine}
    (repr : StateRepr L b frame F σ base m) (room : b + cert.need ≤ frame)
    (capacity : AllocationInput b frame (cert.cost σ) σ base m)
    (failed : P.runR σ = .error .revert) : run cert.code m = .revert := by
  rcases cert.sound repr room capacity with ⟨o,m',base',hs,rest⟩ | ⟨hs,ht⟩
  · change P.runR σ = .ok o at hs
    rw [failed] at hs; contradiction
  · exact ht
end Solidity.Backend.InternalFlow.LoopCallerPrefix
