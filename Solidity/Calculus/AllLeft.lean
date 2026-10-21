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

/-- A literal of some value type: a candidate instance. -/
abbrev InstLit : Type := (p : PrimTy) × p.Denote

/-- `{\subst x; v}φ`: the instance of `∀ p x. φ` at the literal `v`; `none`
where `Fml.substU` does not read the body. -/
def Fml.instLit {Γ : Ctx} (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) (v : p.Denote) :
    Option (Fml C Γ) :=
  Fml.substU ((Upd.nil : Upd C Γ Γ).decl x (.val (.app0 (.lit v)))) φ

/-- **An instance of a premise that holds holds** (`allLeft`). -/
theorem Fml.instLit_holds {Γ : Ctx} {x : Var} {p : PrimTy} {φ : Fml C (.val p :: Γ)}
    {v : p.Denote} {φ' : Fml C Γ} (h : Fml.instLit x p φ v = some φ') (σ : State C Γ)
    (hall : holds σ (.all x p φ)) : holds σ φ' :=
  (Fml.substU_holds (Upd.lands_decl (Upd.lands_nil σ) x (v := v) rfl) φ h).2 (hall v)

/-- The instances of `∀ p x. φ` at the literals `ts` of its type. -/
def Fml.instances {Γ : Ctx} (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ))
    (ts : List InstLit) : List (Fml C Γ) :=
  ts.filterMap fun t => if h : t.1 = p then Fml.instLit x p φ (h ▸ t.2) else none

/-- The instances of a premise: none unless it is a `∀`. -/
def Fml.instancesOf {Γ : Ctx} (ts : List InstLit) : Fml C Γ → List (Fml C Γ)
  | .all x p φ => Fml.instances x p φ ts
  | _ => []

theorem Fml.instancesOf_holds {Γ : Ctx} (ts : List InstLit) (a : Fml C Γ) (σ : State C Γ)
    (ha : holds σ a) : ∀ b ∈ a.instancesOf ts, holds σ b := by
  cases a with
  | all x p φ =>
    intro b hb
    obtain ⟨t, -, ht⟩ := List.mem_filterMap.1 hb
    split at ht
    · exact Fml.instLit_holds ht σ ha
    · cases ht
  | _ => intro b hb; cases hb

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
  if (a.instancesOf ts).isEmpty then [a] else a.instancesOf ts

theorem Fml.instOrSelf_holds {Γ : Ctx} (ts : List InstLit) (a : Fml C Γ) (σ : State C Γ)
    (ha : holds σ a) : ∀ b ∈ a.instOrSelf ts, holds σ b := by
  unfold Fml.instOrSelf
  split
  · intro b hb
    rw [List.mem_singleton.1 hb]
    exact ha
  · exact Fml.instancesOf_holds ts a σ ha

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
  | _, .grow H => (H.instAll ts).grow

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
  | _, .grow H, φ, ψ, h, σ, hσ =>
    Hyps.instAll_mono ts H (φ := .grow φ) (ψ := .grow ψ) (fun _ hτ st nt => h _ (hτ st nt)) σ hσ

/-- **`allLeft` at a leaf**: the sequent with its `∀` premises instantiated
is valid only where the sequent is. -/
theorem Hyps.instAll_valid (ts : List InstLit) {Γ : Ctx} {H : Hyps C [] Γ} {φ : Fml C Γ}
    (h : Valid ((H.instAll ts).wrap φ)) : Valid (H.wrap φ) :=
  fun σ => H.instAll_mono ts (fun _ h => h) σ (h σ)

end Solidity
