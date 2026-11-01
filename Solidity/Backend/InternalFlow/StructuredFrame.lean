import Solidity.Backend.InternalFlow.CompletedLoopFrame

/-! Structural successful-flow consumers of existing intrinsic runs. These
proof derivations do not change withinM, compiler admission or execution.
Loops use the published body guard and actual successful execution. -/
namespace Solidity.Backend.InternalFlow
variable {C : Contract}

mutual
inductive FrameStmt (μ : Mutability) (t : LTy) : {Γ Δ : Ctx} → Stmt C Γ Δ → Idx Γ t → Prop
  | leaf {Γ Δ} (s : Stmt C Γ Δ) (i : Idx Γ t)
      (within : s.withinM μ = true) (unwritten : (t,i.toNat) ∉ s.writesAt 0) : FrameStmt μ t s i
  | loop {Γ Δ} (a : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Δ) (i : Idx Γ t)
      (reads : c.readsIn μ = true) (within : Prog.withinM μ body = true) (unwritten : (t,i.toNat) ∉ Prog.writesAt 0 body) :
      FrameStmt μ t (.loop a c body) i
  | block {Γ Δ} {body : Prog C Γ Δ} {i : Idx Γ t} (proof : FrameProg μ t body i) :
      FrameStmt μ t (.block body) i
  | branch {Γ Δ Ε} (c : Val C Γ .bool) (reads : c.readsIn μ = true)
      {thn : Prog C Γ Δ} {els : Prog C Γ Ε} {i : Idx Γ t}
      (left : FrameProg μ t thn i) (right : FrameProg μ t els i) :
      FrameStmt μ t (.ite c thn els) i
inductive FrameProg (μ : Mutability) (t : LTy) : {Γ Δ : Ctx} → Prog C Γ Δ → Idx Γ t → Prop
  | nil {Γ} (i : Idx Γ t) : FrameProg μ t .nil i
  | cons {Γ Δ Ε} {s : Stmt C Γ Δ} {P : Prog C Δ Ε} {i : Idx Γ t}
      (head : FrameStmt μ t s i) (tail : FrameProg μ t P (i.ext s.ext)) :
      FrameProg μ t (.cons s P) i
end

mutual
 theorem FrameStmt.sound {μ : Mutability} {t : LTy} :
    {Γ Δ : Ctx} → {s : Stmt C Γ Δ} → {i : Idx Γ t} → FrameStmt μ t s i →
    {σ : State C Γ} → {out : Out C σ.H Δ} → s.run σ = .ok out →
    TGFrameM μ σ out.st out.ext ∧
      TEnv.get i (TEnv.drop s.ext out.st.env) = LTy.TDenote.wk out.ext t (TEnv.get i σ.env)
  | _,_,_,_,.leaf s i within unwritten,_,_,executed => by
    obtain ⟨hg,hl⟩ := Stmt.run_frameM s within 0 executed
    exact ⟨hg,hl t i (Nat.zero_le _) (by simpa only [Nat.sub_zero] using unwritten)⟩
  | _,_,_,_,.loop a c body i _ within unwritten,σ,out,executed => by
    obtain ⟨hg,hl⟩ := scoped_loop_completed_frame μ body within a c σ out executed
    exact ⟨hg,hl t i (Nat.zero_le _) (by simpa only [Nat.sub_zero] using unwritten)⟩
  | _,_,_,_,.block proof,_,_,executed => by
    change (Prog.runR _ _).map _ = .ok _ at executed
    obtain ⟨out,h,rfl⟩ := tmap_ok_inv executed
    obtain ⟨hg,hl⟩ := FrameProg.sound proof h
    exact ⟨hg.withEnv _,hl⟩
  | _,_,_,_,.branch c _ left right,_,_,executed => by
    change TRun.ite c _ _ _ _ _ = .ok _ at executed
    simp only [TRun.ite] at executed
    obtain ⟨v,_,executed⟩ := tbind_ok_inv executed
    split at executed
    · obtain ⟨out,h,rfl⟩ := tmap_ok_inv executed
      obtain ⟨hg,hl⟩ := FrameProg.sound left h
      exact ⟨hg.withEnv _,hl⟩
    · obtain ⟨out,h,rfl⟩ := tmap_ok_inv executed
      obtain ⟨hg,hl⟩ := FrameProg.sound right h
      exact ⟨hg.withEnv _,hl⟩
 theorem FrameProg.sound {μ : Mutability} {t : LTy} :
    {Γ Δ : Ctx} → {P : Prog C Γ Δ} → {i : Idx Γ t} → FrameProg μ t P i →
    {σ : State C Γ} → {out : Out C σ.H Δ} → P.run σ = .ok out →
    TGFrameM μ σ out.st out.ext ∧
      TEnv.get i (TEnv.drop P.ext out.st.env) = LTy.TDenote.wk out.ext t (TEnv.get i σ.env)
  | _,_,_,_,.nil i,σ,_,executed => by
    cases executed
    exact ⟨TGFrameM.ofFrame (TGFrame.refl σ) _,(LTy.TDenote.wk_refl _ _ _).symm⟩
  | _,_,.cons s P,i,.cons head tail,_,_,executed => by
    change TRun.seq _ _ _ = .ok _ at executed
    unfold TRun.seq at executed
    split at executed
    · rename_i first hfirst
      obtain ⟨last,hlast,rfl⟩ := tmap_ok_inv executed
      obtain ⟨hg,hlocal⟩ := FrameStmt.sound head hfirst
      obtain ⟨kg,klocal⟩ := FrameProg.sound tail hlast
      refine ⟨hg.trans kg _,?_⟩
      show TEnv.get i (TEnv.drop (s.ext.trans P.ext) last.st.env) = _
      rw [TEnv.drop_trans]
      simp only [TEnv.get_ext_drop] at klocal
      rw [klocal,hlocal,LTy.TDenote.wk_wk]
    · cases executed
end

/-- info: 'Solidity.Backend.InternalFlow.FrameStmt.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FrameStmt.sound
/-- info: 'Solidity.Backend.InternalFlow.FrameProg.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FrameProg.sound
end Solidity.Backend.InternalFlow
