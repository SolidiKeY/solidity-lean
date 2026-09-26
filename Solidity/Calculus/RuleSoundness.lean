import Solidity.Calculus.Rules

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-! ## Two runs that end alike -/

/-- The fresh names a rule may declare at index `k`: `se`, `sp`, `ie`, `mv`. -/
def freshVars (k : Nat) : List Var :=
  [.fresh "se" k, .fresh "sp" k, .fresh "ie" k, .fresh "mv" k]

def SameOk (ns : List Var) : Res State → Res State → Prop
  | .ok a, .ok b => EnvAgreeExcept ns a b
  | .error _, .error _ => True
  | _, _ => False

theorem SameOk.of_agree {ns : List Var} {x y : Res State} (h : ResultsAgree ns x y) :
    SameOk ns x y := by
  cases x <;> cases y <;> simp_all [SameOk, ResultsAgree]

theorem Semantics.EnvAgreeExcept.setEnv_left {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) {n : Var} (hn : n ∈ ns) (b : Binding) :
    EnvAgreeExcept ns (s₁.setEnv n b) s₂ :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun m hm => by
    have hne : m ≠ n := fun heq => hm (heq ▸ hn)
    simpa [State.setEnv, lookupBy_setBy_ne hne] using h.env m hm,
    h.selfBalance⟩

theorem agree_setEnv (σ : State) (x : Var) (b : Binding) :
    EnvAgreeExcept [x] (σ.setEnv x b) σ :=
  (EnvAgreeExcept.refl [x] σ).setEnv_left (by simp) b

theorem avoids_single {x : Var} {vs : List Var} (h : x ∉ vs) : Avoids vs [x] :=
  fun y hy hm => h (by simp at hm; exact hm ▸ hy)

section
variable {σ : State} {x : Var} {b : Binding}

@[simp] theorem Simple.eval_setEnv {p : PrimTy} {s : Simple C p} (h : x ∉ s.vars) :
    s.eval (σ.setEnv x b) = s.eval σ := s.eval_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem Val.eval_setEnv {p : PrimTy} {v : Val C p} (h : x ∉ v.vars) :
    v.eval (σ.setEnv x b) = v.eval σ := v.eval_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem SPath.resolve_setEnv {T : Ty} {p : SPath C T} (h : x ∉ p.vars) :
    p.resolve (σ.setEnv x b) = p.resolve σ := p.resolve_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem Loc.resolve_setEnv {T : Ty} {l : Loc C T} (h : x ∉ l.vars) :
    l.resolve (σ.setEnv x b) = l.resolve σ := l.resolve_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem MPath.mval_setEnv {T : Ty} {p : MPath C T} (h : x ∉ p.vars) :
    p.mval (σ.setEnv x b) = p.mval σ := p.mval_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem MLoc.read_setEnv {T : Ty} {l : MLoc C T} (h : x ∉ l.vars) :
    l.read (σ.setEnv x b) = l.read σ := l.read_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem Src.value_setEnv {T : Ty} {r : Src C T} (h : x ∉ r.vars) :
    r.value (σ.setEnv x b) = r.value σ := r.value_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem MSrc.mval_setEnv {T : Ty} {r : MSrc C T} (h : x ∉ r.vars) :
    r.mval (σ.setEnv x b) = r.mval σ := r.mval_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem State.findStorage_setEnv (r : Name) (segs : List Seg) :
    (σ.setEnv x b).findStorage r segs = σ.findStorage r segs := rfl
@[simp] theorem State.getObj_setEnv (id : Nat) : (σ.setEnv x b).getObj id = σ.getObj id := rfl
end

/-- What a premise means for the statement it replaces. -/
def Premise.Correct (k : Nat) (m : Modality) (s : Stmt C) : Premise C → Prop
  | .update U => ∀ σ, SameOk [] (U.apply σ) (s.run σ)
  | .unfold P => ∀ σ, SameOk (freshVars k) (Prog.run σ P) (s.run σ)
  | .split c c' P Q => ∀ σ,
      (holds σ c → SameOk (freshVars k) (Prog.run σ P) (s.run σ)) ∧
      (holds σ c' → SameOk (freshVars k) (Prog.run σ Q) (s.run σ)) ∧
      (¬ holds σ c → ¬ holds σ c' → ∃ e, s.run σ = .error e)
  | .done b => ∀ σ, (∃ e, s.run σ = .error e) ∧ (b = true → m = .box)

macro "fresh_ne" : tactic => `(tactic| (intro h; cases h))

theorem Taclet.sound {k : Nat} {m : Modality} {s : Stmt C} {pr : Premise C}
    (d : Taclet C k m s pr) (hs : Avoids s.vars (freshVars k)) : pr.Correct k m s := by
  have hse : Var.fresh "se" k ∉ s.vars := fun h => hs _ h (by simp [freshVars])
  have hsp : Var.fresh "sp" k ∉ s.vars := fun h => hs _ h (by simp [freshVars])
  have hie : Var.fresh "ie" k ∉ s.vars := fun h => hs _ h (by simp [freshVars])
  have hmv : Var.fresh "mv" k ∉ s.vars := fun h => hs _ h (by simp [freshVars])
  clear hs
  cases d
  case storageFieldWrite_unfold_leftFst =>
    intro σ
    simp only [Stmt.vars, Loc.vars, SPath.vars, Src.vars, List.mem_append, not_or] at hse hsp hie hmv
    simp only [Prog.run, Stmt.run, ARhs.bind, Src.value, Loc.resolve, SPath.resolve, aliasPath,
      bind, Except.bind, pure, Except.pure]
    sorry
  all_goals sorry

end Solidity
