import Solidity.Backend.InternalFlow.MixedStoreAliasFrame
import Solidity.Backend.InternalFlow.CallerView
/-! Local-only derivations over existing intrinsic syntax. Unlike FrameStmt,
these conclusions assert neither Heap.Keeps nor a global mutability frame.
Existing leaf guards are consumed unchanged; real stores have direct run laws.
Local identity does not imply old heap contents or storage-alias liveness. -/
namespace Solidity.Backend.InternalFlow.LocalStoreFlow
variable {C : Contract}
mutual
inductive StmtPlan (t : LTy) : {Γ Δ : Ctx} → Stmt C Γ Δ → Idx Γ t → Prop
  | existing {Γ Δ} (μ : Mutability) (s : Stmt C Γ Δ) (i : Idx Γ t)
      (within : s.withinM μ = true) (unwritten : (t,i.toNat) ∉ s.writesAt 0) : StmtPlan t s i
  | storage {Γ T} (l : Loc C Γ T) (v : Src C Γ T) (i : Idx Γ t) : StmtPlan t (.assign l v) i
  | memory {Γ T} (l : MLoc C Γ T) (v : MSrc C Γ T) (i : Idx Γ t) : StmtPlan t (.assignMem l v) i
  | block {Γ Δ} {body : Prog C Γ Δ} {i : Idx Γ t}
      (bodyPlan : ProgPlan t body i) : StmtPlan t (.block body) i
  | branch {Γ Δ Ε} (c : Val C Γ .bool) {thn : Prog C Γ Δ} {els : Prog C Γ Ε}
      {i : Idx Γ t} (left : ProgPlan t thn i) (right : ProgPlan t els i) :
      StmtPlan t (.ite c thn els) i
inductive ProgPlan (t : LTy) : {Γ Δ : Ctx} → Prog C Γ Δ → Idx Γ t → Prop
  | nil {Γ} (i : Idx Γ t) : ProgPlan t .nil i
  | cons {Γ Δ Ε} {s : Stmt C Γ Δ} {P : Prog C Δ Ε} {i : Idx Γ t}
      (head : StmtPlan t s i) (tail : ProgPlan t P (i.ext s.ext)) : ProgPlan t (.cons s P) i
end
mutual
 theorem StmtPlan.sound {t : LTy} : {Γ Δ : Ctx} → {s : Stmt C Γ Δ} →
    {i : Idx Γ t} → StmtPlan t s i → {σ : State C Γ} →
    {out : Out C σ.H Δ} → s.run σ = .ok out →
    TEnv.get i (TEnv.drop s.ext out.st.env) = LTy.TDenote.wk out.ext t (TEnv.get i σ.env)
  | _,_,_,_,.existing μ s i within unwritten,_,_,ran => by
    obtain ⟨_,locals⟩ := Stmt.run_frameM s within 0 ran
    exact locals t i (Nat.zero_le _) (by simpa only [Nat.sub_zero] using unwritten)
  | _,_,_,_,.storage l v i,σ,out,ran => by
    change TEnv.get i out.st.env = _
    rw [CallerView.storage_assign_environment l v ran,TEnv.get_wk]
  | _,_,_,_,.memory l v i,σ,out,ran => by
    change TEnv.get i out.st.env = _
    rw [CallerView.memory_store_environment l v ran,TEnv.get_wk]
  | _,_,_,_,.block plan,_,_,ran => by
    change (Prog.runR _ _).map _ = .ok _ at ran
    obtain ⟨out,executed,rfl⟩ := tmap_ok_inv ran
    exact ProgPlan.sound plan executed
  | _,_,_,_,.branch c left right,_,_,ran => by
    change TRun.ite c _ _ _ _ _ = .ok _ at ran
    simp only [TRun.ite] at ran
    obtain ⟨v,_,ran⟩ := tbind_ok_inv ran
    split at ran
    · obtain ⟨out,executed,rfl⟩ := tmap_ok_inv ran
      exact ProgPlan.sound left executed
    · obtain ⟨out,executed,rfl⟩ := tmap_ok_inv ran
      exact ProgPlan.sound right executed
 theorem ProgPlan.sound {t : LTy} : {Γ Δ : Ctx} → {P : Prog C Γ Δ} →
    {i : Idx Γ t} → ProgPlan t P i → {σ : State C Γ} →
    {out : Out C σ.H Δ} → P.run σ = .ok out →
    TEnv.get i (TEnv.drop P.ext out.st.env) = LTy.TDenote.wk out.ext t (TEnv.get i σ.env)
  | _,_,_,_,.nil i,σ,_,ran => by
    cases ran
    exact (LTy.TDenote.wk_refl _ t (TEnv.get i σ.env)).symm
  | _,_,.cons s P,i,.cons head tail,_,_,ran => by
    change TRun.seq _ _ _ = .ok _ at ran
    unfold TRun.seq at ran
    split at ran
    · rename_i first hfirst
      obtain ⟨last,hlast,rfl⟩ := tmap_ok_inv ran
      have hhead := StmtPlan.sound head hfirst
      have htail := ProgPlan.sound tail hlast
      show TEnv.get i (TEnv.drop (s.ext.trans P.ext) last.st.env) = _
      rw [TEnv.drop_trans]
      simp only [TEnv.get_ext_drop] at htail
      rw [htail,hhead,LTy.TDenote.wk_wk]
    · cases ran
end

open Evm Evm.Memory
/-- Plain target path transport from a syntax-derived alias frame and an
actual reached representation; no target simulation is postulated. -/
theorem ProgPlan.plain_slot {R : RefTy} {Γ Δ : Ctx} {P : Prog C Γ Δ}
    {i : Idx Γ (.alias R)} (plan : ProgPlan (.alias R) P i)
    {σ : State C Γ} {out : Out C σ.H Δ} (ran : P.run σ = .ok out)
    {r : SRef C (.ref R)} (old : TEnv.get i σ.env = some r)
    {L b frame : Nat} {F : Frag Δ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F out.st base m) (flag : F.get (i.ext P.ext) = .ok) :
    ∃ slot, m.mem (cellOf b (i.ext P.ext)) = .slot slot ∧ PathSlot C true r slot := by
  obtain ⟨found,slot,bound,word,path⟩ := repr.core.aliases (i.ext P.ext) flag
  change TEnv.get (i.ext P.ext) out.st.env = some found at bound
  have preserved := (TEnv.get_ext_drop i P.ext out.st.env).trans ((plan.sound ran).trans old)
  have same : found = r := Option.some.inj (bound.symm.trans preserved)
  subst found
  exact ⟨slot,word,path⟩
/-- Fragile liveness comes from the actual reached representation, not from
syntactic identity or an assumed live-path equation. -/
theorem ProgPlan.fragile_slot {R : RefTy} {Γ Δ : Ctx} {P : Prog C Γ Δ}
    {i : Idx Γ (.alias R)} (plan : ProgPlan (.alias R) P i)
    {σ : State C Γ} {out : Out C σ.H Δ} (ran : P.run σ = .ok out)
    {r : SRef C (.ref R)} (old : TEnv.get i σ.env = some r)
    {L b frame : Nat} {F : Frag Δ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F out.st base m) (flag : F.get (i.ext P.ext) = .fragile) :
    ∃ slot, m.mem (cellOf b (i.ext P.ext)) = .slot slot ∧ PathSlot C false r slot ∧
      ∃ sv, out.st.storage.findLive r = some sv := by
  obtain ⟨found,slot,bound,word,path,live⟩ := repr.core.fragile (i.ext P.ext) flag
  change TEnv.get (i.ext P.ext) out.st.env = some found at bound
  have preserved := (TEnv.get_ext_drop i P.ext out.st.env).trans ((plan.sound ran).trans old)
  have same : found = r := Option.some.inj (bound.symm.trans preserved)
  subst found
  exact ⟨slot,word,path,live⟩
end Solidity.Backend.InternalFlow.LocalStoreFlow
