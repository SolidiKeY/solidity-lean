import Solidity.Calculus.ExactReduction

/-!
# Exact updates without memory locals or exhaustion

An update's successful symbolic guard does not by itself provide a typed
landing state: a bare memory identity may have no representative in its
heap. Contexts without memory locals admit every local-value vector, so
they supply the witness needed for the reverse implication. Push-free
updates have no exhaustion arm; ordinary failure keeps its modality.
-/

namespace Solidity.Decide

variable {C : Contract}

namespace LocalRealization

def supported : Ctx → Bool
  | [] => true
  | .mem _ :: _ => false
  | _ :: Γ => supported Γ

def env (H : HTy) : {Γ : Ctx} → (h : supported Γ = true) → LocsV C Γ → TEnv C H Γ
  | [], _, _ => ()
  | .mem _ :: _, h, _ => nomatch h
  | .val _ :: _, h, ℓ | .alias _ :: _, h, ℓ | .old :: _, h, ℓ
  | .oldNet :: _, h, ℓ | .kint :: _, h, ℓ =>
    (ℓ _ .here, env H h (fun _ i => ℓ _ (.there i)))

theorem get_env (H : HTy) {Γ : Ctx} (h : supported Γ = true) (ℓ : LocsV C Γ)
    {t : LTy} (i : Idx Γ t) : LTy.VDen.ofT t (TEnv.get i (env H h ℓ)) = ℓ t i := by
  induction Γ with
  | nil => cases i
  | cons u Γ ih =>
    cases u with
    | mem _ => cases h
    | _ =>
      cases i with
      | here => rfl
      | there j => exact ih h (fun _ k => ℓ _ (.there k)) j

def state (g : State C []) {Γ : Ctx} (h : supported Γ = true) (ℓ : LocsV C Γ) : State C Γ :=
  ⟨g.storage, g.H, g.heap, env g.H h ℓ, g.net, g.selfBalance, g.tx⟩

theorem glob_state (g : State C []) {Γ : Ctx} (h : supported Γ = true) (ℓ : LocsV C Γ) :
    (state g h ℓ).glob = g := by
  cases g
  rfl

theorem getV_state (g : State C []) {Γ : Ctx} (h : supported Γ = true) (ℓ : LocsV C Γ)
    {t : LTy} (i : Idx Γ t) : (state g h ℓ).getV i = ℓ t i :=
  get_env g.H h ℓ i

end LocalRealization

def updateGuard (m : Modality) (gd : LTm C (.val .bool)) (ψ : LFml C) : LFml C :=
  match m with
  | .box => .imp (.eq gd gd) ψ
  | .diamond => .and (.eq gd gd) ψ

theorem updateGuard_iff {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ)
    (hf : U.pushFree = true) (hl : LocalRealization.supported Δ = true)
    (g₀ : State C []) (ν : AEnv) (τ : State C Γ)
    (gd : LTm C (.val .bool)) (ψ : LFml C) (φ : Fml C Δ)
    (hg : gd.eval g₀ ν = (U.applyV τ).map (fun _ => true))
    (hr : ∀ q, U.applyV τ = some q → ∀ σ' : State C Δ,
      σ'.glob = q.1.1 → (∀ {t : LTy} (i : Idx Δ t), σ'.getV i = q.2 t i) →
      (ψ.holds g₀ ν ↔ holds σ' φ)) :
    (updateGuard m gd ψ).holds g₀ ν ↔ holds τ (.upd m U φ) := by
  change _ ↔ U.afterT m τ (holds · φ)
  rw [Upd.afterT_applyV]
  have hgd : (LFml.eq gd gd).holds g₀ ν ↔ (U.applyV τ).isSome = true := by
    rw [LFml.holds_rets, hg]
    cases U.applyV τ with
    | none => exact ⟨fun ⟨_, h⟩ => (nomatch h), fun h => (nomatch h)⟩
    | some _ => exact ⟨fun _ => rfl, fun _ => ⟨true, rfl⟩⟩
  cases hq : U.applyV τ with
  | none =>
    cases m with
    | box =>
      change ((LFml.eq gd gd).holds g₀ ν → ψ.holds g₀ ν) ↔ True ∨ _
      simp only [hgd, hq, Option.isSome_none, Bool.false_eq_true, false_implies,
        true_or, iff_self]
    | diamond =>
      change ((LFml.eq gd gd).holds g₀ ν ∧ ψ.holds g₀ ν) ↔ False ∨ _
      simp only [hgd, hq, Option.isSome_none, Bool.false_eq_true, false_and,
        Upd.exh_of_pushFree (σ₀ := τ) hf, false_or, iff_self]
  | some q =>
    have hrest : ψ.holds g₀ ν ↔ ∀ σ' : State C Δ, σ'.glob = q.1.1 →
        (∀ {t : LTy} (i : Idx Δ t), σ'.getV i = q.2 t i) → holds σ' φ :=
      ⟨fun hp σ' hglob hloc => (hr q hq σ' hglob hloc).1 hp,
        fun hp => (hr q hq (LocalRealization.state q.1.1 hl q.2)
          (LocalRealization.glob_state _ _ _) (LocalRealization.getV_state _ _ _)).2
          (hp _ (LocalRealization.glob_state _ _ _) (LocalRealization.getV_state _ _ _))⟩
    apply Iff.trans ?_ hrest
    cases m with
    | box =>
      change ((LFml.eq gd gd).holds g₀ ν → ψ.holds g₀ ν) ↔ ψ.holds g₀ ν
      simp only [hgd, hq, Option.isSome_some, true_implies]
    | diamond =>
      change ((LFml.eq gd gd).holds g₀ ν ∧ ψ.holds g₀ ν) ↔ ψ.holds g₀ ν
      simp only [hgd, hq, Option.isSome_some, true_and]

/-- Exactness relative to a symbolic state, including its locals. -/
structure ExactAt {Γ : Ctx} (ρ : SymS C Γ) (φ : Fml C Γ) where
  leaf : LFml C
  correct : ∀ (g₀ : State C []) (ν : AEnv) (τ : State C Γ),
    Agrees g₀ ν ρ τ → ρ.Fresh → (leaf.holds g₀ ν ↔ holds τ φ)

namespace ExactAt

def directional? {Γ : Ctx} (ρ : SymS C Γ) (φ : Fml C Γ) : Option (ExactAt ρ φ) := do
  match hp : φ.toLS true ρ with
  | none => none
  | some p =>
    match hn : φ.toLS false ρ with
    | none => none
    | some n =>
      if he : p.same n = true then
        let hn' : φ.toLS false ρ = some p := (LFml.eq_of_same p n he) ▸ hn
        some ⟨p, fun _ ν τ ha hf =>
          ⟨(Fml.toLS_sound φ true hp τ ν ha hf).1 rfl,
            (Fml.toLS_sound φ false hn' τ ν ha hf).2 rfl⟩⟩
      else none

def not {Γ : Ctx} {ρ : SymS C Γ} {φ : Fml C Γ} (r : ExactAt ρ φ) : ExactAt ρ (.not φ) :=
  ⟨.not r.leaf, fun g₀ ν τ ha hf => not_congr (r.correct g₀ ν τ ha hf)⟩

def and {Γ : Ctx} {ρ : SymS C Γ} {φ ψ : Fml C Γ}
    (r : ExactAt ρ φ) (s : ExactAt ρ ψ) : ExactAt ρ (.and φ ψ) :=
  ⟨.and r.leaf s.leaf, fun g₀ ν τ ha hf =>
    and_congr (r.correct g₀ ν τ ha hf) (s.correct g₀ ν τ ha hf)⟩

def imp {Γ : Ctx} {ρ : SymS C Γ} {φ ψ : Fml C Γ}
    (r : ExactAt ρ φ) (s : ExactAt ρ ψ) : ExactAt ρ (.imp φ ψ) :=
  ⟨.imp r.leaf s.leaf, fun g₀ ν τ ha hf =>
    imp_congr (r.correct g₀ ν τ ha hf) (s.correct g₀ ν τ ha hf)⟩

def all {Γ : Ctx} {ρ : SymS C Γ} (x : Var) (p : PrimTy) {φ : Fml C (.val p :: Γ)}
    (r : ExactAt (ρ.pushQ p) φ) : ExactAt ρ (.all x p φ) :=
  ⟨.all ρ.next p r.leaf, fun g₀ ν τ ha hf => forall_congr' fun v =>
    r.correct g₀ (ν.set p ρ.next v) (τ.push (t := .val p) v) (ha.pushQ hf p v) (hf.pushQ p)⟩

def update {Γ Δ : Ctx} {ρ : SymS C Γ} (m : Modality) (U : Upd C Γ Δ)
    (hf : U.pushFree = true) (hl : LocalRealization.supported Δ = true)
    {ρ' : SymS C Δ} {gd : LTm C (.val .bool)} (hu : U.toLS ρ = some (ρ', gd))
    {φ : Fml C Δ} (r : ExactAt ρ' φ) : ExactAt ρ (.upd m U φ) :=
  ⟨updateGuard m gd r.leaf, by
    intro g₀ ν τ ha hfresh
    obtain ⟨hg, hag, hf', _⟩ := Upd.toLS_sound ha hfresh U hu
    apply updateGuard_iff m U hf hl g₀ ν τ gd r.leaf φ hg
    intro q hq σ' hglob hloc
    apply r.correct g₀ ν σ' ?_ hf'
    have hloc' : σ'.locV = q.2 := funext fun _ => funext fun i => hloc i
    show AgreesV g₀ ν ρ' σ'.glob σ'.locV
    rw [hglob, hloc']
    exact hag q hq⟩

def ofFormula? : Nat → {Γ : Ctx} → (ρ : SymS C Γ) → (φ : Fml C Γ) → Option (ExactAt ρ φ)
  | 0, _, _, _ => none
  | fuel + 1, _, ρ, .not φ => (ofFormula? fuel ρ φ).map not
  | fuel + 1, _, ρ, .and φ ψ => do return and (← ofFormula? fuel ρ φ) (← ofFormula? fuel ρ ψ)
  | fuel + 1, _, ρ, .imp φ ψ => do return imp (← ofFormula? fuel ρ φ) (← ofFormula? fuel ρ ψ)
  | fuel + 1, _, ρ, .all x p φ => (ofFormula? fuel (ρ.pushQ p) φ).map (all x p)
  | fuel + 1, _, ρ, .upd m U φ =>
    if hf : U.pushFree = true then
      if hl : LocalRealization.supported _ = true then
        match hu : U.toLS ρ with
        | none => none
        | some (ρ', _) => (ofFormula? fuel ρ' φ).map (update m U hf hl hu)
      else none
    else none
  | _ + 1, _, ρ, φ => directional? ρ φ

end ExactAt

/-- A source certificate independent of which exact compiler produced it. -/
structure SourceReduction (φ : Fml C []) where
  leaf : LFml C
  meaning : ∀ σ : State C [], leaf.holds σ AEnv.dflt ↔ holds σ φ

theorem SourceReduction.elim_holds_iff {φ : Fml C []} (r : SourceReduction φ) (σ : State C []) :
    r.leaf.elim.holds σ AEnv.dflt ↔ holds σ φ :=
  (LFml.elim_holds σ r.leaf AEnv.dflt).trans (r.meaning σ)

def sourceReduction? (φ : Fml C []) : Option (SourceReduction φ) := do
  let r ← ExactAt.ofFormula? 2048 SymS.init φ
  return ⟨r.leaf, fun σ => r.correct σ AEnv.dflt σ (Agrees.init σ AEnv.dflt) SymS.Fresh.init⟩

end Solidity.Decide
