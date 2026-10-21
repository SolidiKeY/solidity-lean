import Solidity.Calculus.UpdateRules

/-!
# `allLeftHide`: a quantified premise instantiated

KeY's `allLeftHide` (`instAll`'s hiding form, FOL rules): a premise
`\forall x; φ` gives its instances `{\subst x; t}φ` at ground terms `t` of
the sequent, and is hidden.  Here an instance is the premise's body under
the declaration `{x := t}` (`Fml.substU`, `Calculus/UpdateRules.lean`): a
first-order formula of the premise's scope, which the closers read as any
other premise.  Soundness is the premise read at the value `t` returns
(`Fml.instLit_holds`): the declaration lands on the state with `x` pushed
(`Upd.lands_decl`), where `Fml.substU_holds` reads the instance as the body;
hiding a premise only strengthens the sequent (`Hyps.instAll_mono`).

Lean only: which terms.  KeY's strategy picks ground terms of the sequent;
here a term is a literal (it returns in every state and reads the same in
every scope, so it moves to the premise's scope unchanged), and the ones
`Seq.leafValid` offers are the literals the leaf indexes an array or a
mapping with (`at`, `atIn`, `mat`), at most `Seq.allLeftBudget` of them
(`Calculus/ProvesDerive.lean`).  The premise is hidden because the
closers cannot use it: `sol_close`'s `grind` fails on a goal that keeps a
`∀` over a bounded index beside its instance, and `sol_decide` does not
instantiate.  A `∀` premise with no instance is kept.  An instance is read in the
premise's scope, the goal in a deeper one: `sol_close` reads a memory
length through the locals pushed between as one (`CloseS.push_lenU`).
-/

namespace Solidity

variable {C : Contract}

/-- A candidate instance: a literal of some value type, or the local at the
position `n` counted from the outermost (a parameter the leaf indexes with:
pushing locals leaves its position), read at the binder's type. -/
inductive InstLit : Type where
  | lit (p : PrimTy) (v : p.Denote)
  | loc (n : Nat)

/-- The `n`th local of `Γ`, where it is a value of type `p`. -/
def Idx.valAt? : (Γ : Ctx) → (p : PrimTy) → Nat → Option (Idx Γ (.val p))
  | [], _, _ => none
  | .val q :: _, p, 0 => if h : q = p then some (h ▸ .here) else none
  | _ :: _, _, 0 => none
  | _ :: Γ, p, n + 1 => (Idx.valAt? Γ p n).map .there

/-- `{\subst x; t}φ`: the instance of `∀ p x. φ` at the term `t` of the
premise's scope; `none` where `Fml.substU` does not read the body. -/
def Fml.instTm {Γ : Ctx} (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) (t : Tm C Γ (.val p)) :
    Option (Fml C Γ) :=
  Fml.substU ((Upd.nil : Upd C Γ Γ).decl x (.val t)) φ

/-- `{\subst x; v}φ`: the instance at the literal `v`. -/
abbrev Fml.instLit {Γ : Ctx} (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) (v : p.Denote) :
    Option (Fml C Γ) :=
  Fml.instTm x p φ (.app0 (.lit v))

/-- **An instance of a premise that holds holds** (`allLeft`), at a term
that returns `v`. -/
theorem Fml.instTm_holds {Γ : Ctx} {x : Var} {p : PrimTy} {φ : Fml C (.val p :: Γ)}
    {t : Tm C Γ (.val p)} {φ' : Fml C Γ} (h : Fml.instTm x p φ t = some φ') (σ : State C Γ)
    {v : p.Denote} (hv : (Rhs.val t).eval σ = some (LTy.VDen.ofT (H := σ.H) (.val p) v))
    (hall : holds σ (.all x p φ)) : holds σ φ' :=
  (Fml.substU_holds (Upd.lands_decl (Upd.lands_nil σ) x hv) φ h).2 (hall v)

theorem Fml.instLit_holds {Γ : Ctx} {x : Var} {p : PrimTy} {φ : Fml C (.val p :: Γ)}
    {v : p.Denote} {φ' : Fml C Γ} (h : Fml.instLit x p φ v = some φ') (σ : State C Γ)
    (hall : holds σ (.all x p φ)) : holds σ φ' :=
  Fml.instTm_holds h σ (v := v) rfl hall

/-- The instance of `∀ p x. φ` at the candidate `c`, where it has the
binder's type. -/
def Fml.instAt {Γ : Ctx} (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) :
    InstLit → Option (Fml C Γ)
  | .lit q v => if h : q = p then Fml.instLit x p φ (h ▸ v) else none
  | .loc n => if n < Γ.length then
      (Idx.valAt? Γ p (Γ.length - 1 - n)).bind fun i => Fml.instTm x p φ (.pvV i)
    else none

theorem Fml.instAt_holds {Γ : Ctx} {x : Var} {p : PrimTy} {φ : Fml C (.val p :: Γ)}
    (c : InstLit) {φ' : Fml C Γ} (h : Fml.instAt x p φ c = some φ') (σ : State C Γ)
    (hall : holds σ (.all x p φ)) : holds σ φ' := by
  cases c with
  | lit q v =>
    simp only [Fml.instAt] at h
    split at h
    · exact Fml.instLit_holds h σ hall
    · cases h
  | loc n =>
    simp only [Fml.instAt] at h
    split at h
    · obtain ⟨i, -, h⟩ := Option.bind_eq_some_iff.1 h
      exact Fml.instTm_holds h σ rfl hall
    · cases h

/-- The instances of `∀ p x. φ` at the candidates `ts` of its type. -/
def Fml.instances {Γ : Ctx} (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ))
    (ts : List InstLit) : List (Fml C Γ) :=
  ts.filterMap (Fml.instAt x p φ)

/-- The instances of a premise: a `∀`'s, and a conjunction's conjuncts'. -/
def Fml.instancesOf {Γ : Ctx} (ts : List InstLit) : Fml C Γ → List (Fml C Γ)
  | .all x p φ => Fml.instances x p φ ts
  | .and a b => Fml.instancesOf ts a ++ Fml.instancesOf ts b
  | _ => []

theorem Fml.instancesOf_holds {Γ : Ctx} (ts : List InstLit) : (a : Fml C Γ) → (σ : State C Γ) →
    holds σ a → ∀ b ∈ a.instancesOf ts, holds σ b
  | .all x p φ, σ, ha, b, hb => by
    obtain ⟨t, -, ht⟩ := List.mem_filterMap.1 hb
    exact Fml.instAt_holds t ht σ ha
  | .and a b, σ, ha, c, hc => by
    rcases List.mem_append.1 hc with hc | hc
    · exact Fml.instancesOf_holds ts a σ ha.1 c hc
    · exact Fml.instancesOf_holds ts b σ ha.2 c hc
  | .tt, _, _, _, hb | .eq _ _, _, _, _, hb | .wellFormed _, _, _, _, hb | .not _, _, _, _, hb
  | .imp _ _, _, _, _, hb | .upd _ _ _, _, _, _, hb | .modal _ _ _ _, _, _, _, hb
  | .havoc _, _, _, _, hb | .bind _ _ _ _, _, _, _, hb | .anon _ _, _, _, _, hb
  | .allocAll _ _ _, _, _, _, hb => by cases hb

/-- What a premise with instances keeps beside them: its conjuncts that are
not a `∀` with an instance. -/
def Fml.instRest {Γ : Ctx} (ts : List InstLit) : Fml C Γ → List (Fml C Γ)
  | .and a b => Fml.instRest ts a ++ Fml.instRest ts b
  | a => if (a.instancesOf ts).isEmpty then [a] else []

theorem Fml.instRest_holds {Γ : Ctx} (ts : List InstLit) : (a : Fml C Γ) → (σ : State C Γ) →
    holds σ a → ∀ b ∈ a.instRest ts, holds σ b
  | .and a b, σ, ha, c, hc => by
    rcases List.mem_append.1 hc with hc | hc
    · exact Fml.instRest_holds ts a σ ha.1 c hc
    · exact Fml.instRest_holds ts b σ ha.2 c hc
  | .tt, _, ha, _, hb | .eq _ _, _, ha, _, hb | .wellFormed _, _, ha, _, hb | .not _, _, ha, _, hb
  | .imp _ _, _, ha, _, hb | .upd _ _ _, _, ha, _, hb | .modal _ _ _ _, _, ha, _, hb
  | .havoc _, _, ha, _, hb | .bind _ _ _ _, _, ha, _, hb | .anon _ _, _, ha, _, hb
  | .allocAll _ _ _, _, ha, _, hb | .all _ _ _, _, ha, _, hb => by
    unfold Fml.instRest at hb
    split at hb
    · rw [List.mem_singleton.1 hb]; exact ha
    · cases hb

/-- The premises `as` added to the context, the first one first. -/
def Hyps.pres {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) : List (Fml C Γ) → Hyps C Γ₀ Γ
  | [] => H
  | a :: as => (H.pre a).pres as

theorem Hyps.wrap_pres {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) (as : List (Fml C Γ)) (φ : Fml C Γ) :
    (H.pres as).wrap φ = H.wrap (as.foldr .imp φ) := by
  induction as generalizing H with
  | nil => rfl
  | cons a as ih => exact ih (H.pre a)

theorem holds_foldr_imp {Γ : Ctx} (σ : State C Γ) (φ : Fml C Γ) :
    (as : List (Fml C Γ)) → holds σ (as.foldr .imp φ) → (∀ b ∈ as, holds σ b) → holds σ φ
  | [], h, _ => h
  | a :: as, h, hs =>
    holds_foldr_imp σ φ as (h (hs a List.mem_cons_self)) fun b hb => hs b (List.mem_cons_of_mem _ hb)

/-- A premise in the context as `allLeftHide` leaves it: a `∀` with an
instance at `ts` replaced by its instances, any other premise kept. -/
def Fml.instOrSelf {Γ : Ctx} (ts : List InstLit) (a : Fml C Γ) : List (Fml C Γ) :=
  if (a.instancesOf ts).isEmpty then [a] else a.instRest ts ++ a.instancesOf ts

theorem Fml.instOrSelf_holds {Γ : Ctx} (ts : List InstLit) (a : Fml C Γ) (σ : State C Γ)
    (ha : holds σ a) : ∀ b ∈ a.instOrSelf ts, holds σ b := by
  unfold Fml.instOrSelf
  split
  · intro b hb
    rw [List.mem_singleton.1 hb]
    exact ha
  · intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact Fml.instRest_holds ts a σ ha b hb
    · exact Fml.instancesOf_holds ts a σ ha b hb

/-- **`allLeftHide` on a context**: each `∀` premise replaced by its
instances at the literals `ts` (kept where it has none). -/
def Hyps.instAll {Γ₀ : Ctx} (ts : List InstLit) : {Γ : Ctx} → Hyps C Γ₀ Γ → Hyps C Γ₀ Γ
  | _, .nil => .nil
  | _, .pre H a => (H.instAll ts).pres (a.instOrSelf ts)
  | _, .upd H m U => (H.instAll ts).upd m U
  | _, .havoc H => (H.instAll ts).havoc
  | _, .all H x p => (H.instAll ts).all x p
  | _, .bind H m x t => (H.instAll ts).bind m x t
  | _, .anon H xs => (H.instAll ts).anon xs
  | _, .allocAll H x A => (H.instAll ts).allocAll x A

/-- What the instances give, the context gives. -/
theorem Hyps.instAll_mono {Γ₀ : Ctx} (ts : List InstLit) : {Γ : Ctx} → (H : Hyps C Γ₀ Γ) →
    {φ ψ : Fml C Γ} → (∀ τ, holds τ φ → holds τ ψ) →
      ∀ σ, holds σ ((H.instAll ts).wrap φ) → holds σ (H.wrap ψ)
  | _, .nil, _, _, h, σ, hσ => h σ hσ
  | _, .pre H a, φ, ψ, h, σ, hσ => by
    rw [Hyps.instAll, Hyps.wrap_pres] at hσ
    exact Hyps.instAll_mono ts H (φ := (a.instOrSelf ts).foldr .imp φ) (ψ := .imp a ψ)
      (fun τ hτ ha => h τ (holds_foldr_imp τ φ _ hτ (Fml.instOrSelf_holds ts a τ ha))) σ hσ
  | _, .upd H m U, φ, ψ, h, σ, hσ =>
    Hyps.instAll_mono ts H (φ := .upd m U φ) (ψ := .upd m U ψ)
      (fun _ hτ => Upd.afterT_imp hτ h) σ hσ
  | _, .havoc H, φ, ψ, h, σ, hσ =>
    Hyps.instAll_mono ts H (φ := .havoc φ) (ψ := .havoc ψ) (fun _ hτ st nt => h _ (hτ st nt)) σ hσ
  | _, .all H x p, φ, ψ, h, σ, hσ =>
    Hyps.instAll_mono ts H (φ := .all x p φ) (ψ := .all x p ψ) (fun _ hτ v => h _ (hτ v)) σ hσ
  | _, .bind H m x t, φ, ψ, h, σ, hσ =>
    Hyps.instAll_mono ts H (φ := .bind m x t φ) (ψ := .bind m x t ψ)
      (fun _ hτ => Modality.forallB_imp (fun _ a => h _ a) hτ) σ hσ
  | _, .anon H xs, φ, ψ, h, σ, hσ =>
    Hyps.instAll_mono ts H (φ := .anon xs φ) (ψ := .anon xs ψ) (fun _ hτ b => h _ (hτ b)) σ hσ
  | _, .allocAll H x A, φ, ψ, h, σ, hσ =>
    Hyps.instAll_mono ts H (φ := .allocAll x A φ) (ψ := .allocAll x A ψ)
      (fun _ hτ o => h _ (hτ o)) σ hσ

/-- **`allLeft` at a leaf**: the sequent with its `∀` premises instantiated
is valid only where the sequent is. -/
theorem Hyps.instAll_valid (ts : List InstLit) {Γ : Ctx} {H : Hyps C [] Γ} {φ : Fml C Γ}
    (h : Valid ((H.instAll ts).wrap φ)) : Valid (H.wrap φ) :=
  fun σ => H.instAll_mono ts (fun _ h => h) σ (h σ)

end Solidity
