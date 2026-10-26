import Solidity.Calculus.HashKinds

/-!
# Strings hashed by three kinds (M7, plan step 7)

`Fml.tk` (`Calculus/HashKinds.lean`) reads one second kind's words as
binders of their own, linked to the first kind's.  With three kinds (the
hashes of the premise are `keccak256`, `sha256` and `ripemd160`), the
third kind's words are a second layer *inside* the second's (`Fml.tk3`):
the body read past the second kind's words (`Fml.xk`) is read again by
`Fml.tkBody` for the third, under the second layer's link,

  `∀ e₂. fix₂ → link₂ → ∀ e₃. fix₃ → link₃ → ψ''`,

so each layer's link and fixing hypotheses are written in its own
context, never read past the other layer's binders.  The result has hashes
of the first kind only, which the one-kind swap reads:

* **valid** (`Fml.tk3_validH`): `Fml.tkBody_sound` twice, the inner one at
  each value of the outer layer's words;
* **refuted** (`Fml.tk3_refutes`): the instance with both layers' words
  fixed holds in a heap of the family (`tkInst_core` with the inner
  layer's `Fml.tkBody_inst_holds` as its body);
* **complete** (`Fml.tk3_complete`): the second kind's words relabeled
  first (`tkFix_core`, the inner layer, fixed, its body), then the third
  kind's under the outer layer's free binders and link, which read no
  storage (`holds_swLink_withStorage`).
-/

namespace Solidity.Decide

variable {C : Contract} {N : Nat}

/-! ## The leaf with two layers of extra words -/

/-- **The body with the second and third kinds' words**: the second kind's
layer as `Fml.tkBody` writes it, its body the third kind's layer of the
body read past the second kind's words. -/
def _root_.Solidity.Fml.tkBody3 (k₁ k₂ k₃ : HashKind) (N : Nat) (fix₂ fix₃ : Bool) {Γ : Ctx}
    (ψ : Fml C Γ) : Option (Fml C Γ) :=
  (ψ.tkBody k₁ k₂ N false).bind fun _ =>
    (ψ.xk k₂ (XMap.extras (ψ.hLevels k₂).eraseDups Γ)).bind fun ψ₂ =>
      (ψ₂.tkBody k₁ k₃ N fix₃).map fun ψ₃ =>
        Fml.allN (.user "e") (ψ.hLevels k₂).eraseDups.length
          (.imp (Fml.conjL (if fix₂ then fixE k₁ k₂ N (ψ.hLevels k₂).eraseDups else []))
            (.imp (Fml.conjL (linkE k₁ (ψ.hLevels k₂).eraseDups)) ψ₃))

/-- **The leaf with the second and third kinds' words** (`Fml.tkBody3`)
past its prefix of `∀` and fresh strings. -/
def _root_.Solidity.Fml.tk3 (k₁ k₂ k₃ : HashKind) (N : Nat) (fix₂ fix₃ : Bool) :
    {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)
  | _, .all x p φ => (Fml.tk3 k₁ k₂ k₃ N fix₂ fix₃ φ).map (.all x p)
  | _, .allocAll x R φ => (Fml.tk3 k₁ k₂ k₃ N fix₂ fix₃ φ).map (.allocAll x R)
  | _, .tt => Fml.tkBody3 k₁ k₂ k₃ N fix₂ fix₃ .tt
  | _, .eq a b => Fml.tkBody3 k₁ k₂ k₃ N fix₂ fix₃ (.eq a b)
  | _, .wellFormed s => Fml.tkBody3 k₁ k₂ k₃ N fix₂ fix₃ (.wellFormed s)
  | _, .not φ => Fml.tkBody3 k₁ k₂ k₃ N fix₂ fix₃ (.not φ)
  | _, .and φ ψ => Fml.tkBody3 k₁ k₂ k₃ N fix₂ fix₃ (.and φ ψ)
  | _, .imp φ ψ => Fml.tkBody3 k₁ k₂ k₃ N fix₂ fix₃ (.imp φ ψ)
  | _, .upd m U φ => Fml.tkBody3 k₁ k₂ k₃ N fix₂ fix₃ (.upd m U φ)
  | _, .modal .. | _, .havoc _ | _, .bind .. | _, .anon .. | _, .grow _ => none

section Body

variable {Γ : Ctx}

theorem _root_.Solidity.Fml.tkBody_len {k₁ k₂ : HashKind} {fix : Bool} {ψ φ : Fml C Γ}
    (e : ψ.tkBody k₁ k₂ N fix = some φ) : 0 < (ψ.hLevels k₂).eraseDups.length := by
  unfold Fml.tkBody at e
  dsimp only at e
  split at e
  · rename_i hcov
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hcov
    exact List.length_pos_iff.2 hcov.1.1.2
  · cases e

/-- The parts of `Fml.tkBody3`. -/
theorem _root_.Solidity.Fml.tkBody3_eq {k₁ k₂ k₃ : HashKind} {fix₂ fix₃ : Bool} {ψ φ : Fml C Γ}
    (e : ψ.tkBody3 k₁ k₂ k₃ N fix₂ fix₃ = some φ) :
    ∃ φ₂ ψ₂ ψ₃, ψ.tkBody k₁ k₂ N false = some φ₂ ∧
      ψ.xk k₂ (XMap.extras (ψ.hLevels k₂).eraseDups Γ) = some ψ₂ ∧
      ψ₂.tkBody k₁ k₃ N fix₃ = some ψ₃ ∧
      φ = Fml.allN (.user "e") (ψ.hLevels k₂).eraseDups.length
          (.imp (Fml.conjL (if fix₂ then fixE k₁ k₂ N (ψ.hLevels k₂).eraseDups else []))
            (.imp (Fml.conjL (linkE k₁ (ψ.hLevels k₂).eraseDups)) ψ₃)) := by
  unfold Fml.tkBody3 at e
  obtain ⟨φ₂, e₂, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨ψ₂, hψ₂, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨ψ₃, e₃, rfl⟩ := Option.map_eq_some_iff.1 e
  exact ⟨φ₂, ψ₂, ψ₃, e₂, hψ₂, e₃, rfl⟩

/-- `Fml.tkBody`'s condition does not read the flag. -/
theorem _root_.Solidity.Fml.tkBody_fix {k₁ k₂ : HashKind} {fix : Bool} {ψ φ : Fml C Γ}
    (e : ψ.tkBody k₁ k₂ N fix = some φ) (fix' : Bool) : ∃ φ', ψ.tkBody k₁ k₂ N fix' = some φ' := by
  unfold Fml.tkBody at e ⊢
  dsimp only at e ⊢
  split at e
  · rename_i hcov
    rw [if_pos hcov]
    obtain ⟨ψ₂, hψ₂, -⟩ := Option.map_eq_some_iff.1 e
    exact ⟨_, by rw [hψ₂]; rfl⟩
  · cases e

theorem _root_.Solidity.Fml.tkBody3_fix {k₁ k₂ k₃ : HashKind} {fix₂ fix₃ : Bool} {ψ φ : Fml C Γ}
    (e : ψ.tkBody3 k₁ k₂ k₃ N fix₂ fix₃ = some φ) (fix₂' fix₃' : Bool) :
    ∃ φ', ψ.tkBody3 k₁ k₂ k₃ N fix₂' fix₃' = some φ' := by
  obtain ⟨φ₂, ψ₂, ψ₃, e₂, hψ₂, e₃, -⟩ := Fml.tkBody3_eq e
  obtain ⟨ψ₃', e₃'⟩ := Fml.tkBody_fix e₃ fix₃'
  cases h : ψ.tkBody3 k₁ k₂ k₃ N fix₂' fix₃' with
  | some φ' => exact ⟨φ', rfl⟩
  | none =>
    unfold Fml.tkBody3 at h
    simp only [e₂, Option.bind_some, hψ₂, e₃', Option.map_some, reduceCtorEq] at h

end Body

/-! ## Binders of the premise -/

section Premise

variable {Γ : Ctx}

theorem hashIn_allN_succ {k : HashKind} {inp : Option (List Nat)} {out : PrimTy.uint.Denote} (x : Var) :
    (m : Nat) → (B : Fml C (List.replicate (m + 1) (.val .uint) ++ Γ)) → (σ : State C Γ) →
      ¬ Fml.HashIn k inp out σ (Fml.allN x (m + 1) B)
  | 0, _, _ => fun h => h
  | m + 1, B, σ => hashIn_allN_succ x m (.all x .uint B) σ

theorem hashFree_mono {σ : State C Γ} {φ ψ : Fml C Γ}
    (h : ∀ k inp out, Fml.HashIn k inp out σ φ → Fml.HashIn k inp out σ ψ) (hf : ψ.HashFree σ) :
    φ.HashFree σ :=
  fun k hk i₁ i₂ out h₁ h₂ => hf k hk i₁ i₂ out (h k _ _ h₁) (h k _ _ h₂)

/-- **The new binders' premise and body, introduced.** -/
theorem holdsS_allN_intro (x : Var) : (m : Nat) → (B : Fml C (List.replicate m (.val .uint) ++ Γ)) →
    (τ : State C Γ) → (∀ es : Fin m → PrimTy.uint.Denote, m = 0 →
      B.HashFree (τ.withEnv (envOf m es τ.env))) → (∀ es : Fin m → PrimTy.uint.Denote,
      B.HashFree (τ.withEnv (envOf m es τ.env)) → Fml.holdsS (τ.withEnv (envOf m es τ.env)) B) →
      Fml.holdsS τ (Fml.allN x m B)
  | 0, _, _, h0, h => h Fin.elim0 (h0 Fin.elim0 rfl)
  | m + 1, B, τ, _, h =>
    holdsS_allN_intro x m (.all x .uint B) τ (fun _ _ => fun _ _ _ _ _ h => h.elim)
      fun es _ v hv => h (finCons v es) hv

theorem hashIn_allN_pos {k : HashKind} {inp : Option (List Nat)} {out : PrimTy.uint.Denote} (x : Var)
    (m : Nat) (hm : 0 < m) (B : Fml C (List.replicate m (.val .uint) ++ Γ)) (σ : State C Γ) :
    ¬ Fml.HashIn k inp out σ (Fml.allN x m B) := by
  cases m with
  | zero => omega
  | succ m => exact hashIn_allN_succ x m B σ

theorem strOK_envOf {τ : State C Γ} (h : ∀ {R : RefTy} (i : Idx Γ (.mem R)), (τ.getV i).isSome) :
    (m : Nat) → (es : Fin m → PrimTy.uint.Denote) →
      ∀ {R : RefTy} (i : Idx (List.replicate m (.val .uint) ++ Γ) (.mem R)),
        Option.isSome (α := Nat) ((τ.withEnv (Δ := List.replicate m (.val .uint) ++ Γ) (envOf m es τ.env)).getV i)
  | 0, _ => h
  | m + 1, es => strOK_push (strOK_envOf h m (fun i => es i.succ)) (es 0)

end Premise

/-! ## Validity -/

/-- **The body with two layers is sound.** -/
theorem _root_.Solidity.Fml.tkBody3_sound {k₁ k₂ k₃ : HashKind} (hk₁ : k₁ ≠ .ecrecover)
    (hk₂ : k₂ ≠ .ecrecover) (hk₃ : k₃ ≠ .ecrecover) {Γ : Ctx} (ψ : Fml C Γ) {φ : Fml C Γ}
    (e : ψ.tkBody3 k₁ k₂ k₃ N false false = some φ) (τ : State C Γ)
    (hstr : ∀ {R : RefTy} (i : Idx Γ (.mem R)), (τ.getV i).isSome)
    (H : φ.HashFree τ → Fml.holdsS τ φ) (hf : ψ.HashFree τ) : Fml.holdsS τ ψ := by
  obtain ⟨φ₂, ψ₂, ψ₃, e₂, hψ₂, e₃, rfl⟩ := Fml.tkBody3_eq e
  obtain ⟨-, ψ₂', hψ₂', rfl⟩ := Fml.tkBody_eq e₂
  rw [hψ₂] at hψ₂'
  cases hψ₂'
  have hpos := Fml.tkBody_len e₂
  have hpos₃ := Fml.tkBody_len e₃
  obtain ⟨-, ψ₃', -, rfl⟩ := Fml.tkBody_eq e₃
  simp only [Bool.false_eq_true, ↓reduceIte] at H ⊢
  generalize (Fml.hLevels k₂ ψ).eraseDups = L at *
  generalize (Fml.hLevels k₃ ψ₂).eraseDups = L₃ at *
  refine Fml.tkBody_sound hk₁ hk₂ ψ e₂ τ hstr (fun _ => ?_) hf
  have hφ := H (hashFree_allN _ _ _ τ fun _ h => absurd h (by omega))
  refine holdsS_allN_intro _ _ _ τ (fun _ h => absurd h (by omega)) fun es hfB => ?_
  have hfB₃ : Fml.HashFree (τ.withEnv (envOf L.length es τ.env))
      (.imp (Fml.conjL []) (.imp (Fml.conjL (linkE k₁ L)) (Fml.allN (.user "e") L₃.length
        (.imp (Fml.conjL []) (.imp (Fml.conjL (linkE k₁ L₃)) ψ₃'))))) := by
    refine hashFree_mono (fun k inp out h => ?_) hfB
    rcases h with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact absurd h (hashIn_allN_pos _ _ hpos₃ _ _)
  intro _ hlink
  have h₃ := holdsS_allN (.user "e") _ _ τ hφ es hfB₃ trivial hlink
  refine Fml.tkBody_sound hk₁ hk₃ ψ₂ e₃ _ (strOK_envOf hstr _ es) (fun _ => h₃) ?_
  exact hashFree_mono (ψ := .imp (Fml.conjL []) (.imp (Fml.conjL (linkE k₁ L)) ψ₂))
    (fun k inp out h => Or.inr (Or.inr h)) hfB

/-- **The leaf with two layers is sound**, through its prefix. -/
theorem _root_.Solidity.Fml.tk3_sound {k₁ k₂ k₃ : HashKind} (hk₁ : k₁ ≠ .ecrecover)
    (hk₂ : k₂ ≠ .ecrecover) (hk₃ : k₃ ≠ .ecrecover) {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {φ₂ : Fml C Γ}, φ.tk3 k₁ k₂ k₃ N false false = some φ₂ → ∀ τ : State C Γ,
      (∀ {R : RefTy} (i : Idx Γ (.mem R)), (τ.getV i).isSome) →
      (φ₂.HashFree τ → Fml.holdsS τ φ₂) → φ.HashFree τ → Fml.holdsS τ φ := by
  induction φ with
  | all x p φ ih =>
    intro _ e τ hstr H _
    obtain ⟨φ₂, hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    intro v hv
    exact ih hφ _ (strOK_push hstr v) (fun hf => H (hashFree_all _ _ _ _) v hf) hv
  | allocAll x R φ ih =>
    intro _ e τ hstr H _
    obtain ⟨φ₂, hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    intro o ho
    exact ih hφ _ (strOK_alloc hstr o) (fun hf => H (hashFree_allocAll _ _ _ _) o hf) ho
  | tt | eq | wellFormed | not | and | imp | upd =>
    intro _ e τ hstr H hf
    exact Fml.tkBody3_sound hk₁ hk₂ hk₃ _ e τ hstr H hf
  | modal | havoc | bind | anon | grow => intro _ e; cases e

/-- **A valid reading with the second and third kinds' words makes the leaf
valid under its premise.** -/
theorem _root_.Solidity.Fml.tk3_validH {k₁ k₂ k₃ : HashKind} (hk₁ : k₁ ≠ .ecrecover)
    (hk₂ : k₂ ≠ .ecrecover) (hk₃ : k₃ ≠ .ecrecover) {φ φ₂ : Fml C []}
    (e : φ.tk3 k₁ k₂ k₃ N false false = some φ₂) (hv : Fml.ValidH φ₂) : Fml.ValidH φ :=
  fun σ hf => Fml.tk3_sound hk₁ hk₂ hk₃ φ e σ (fun i => nomatch i) (hv σ) hf

/-! ## Refutations -/

section Swapped

variable {Γ : Ctx}

theorem _root_.Solidity.Fml.sw_allN (k : HashKind) (x : Var) :
    (m : Nat) → (F : Fml C (List.replicate m (.val .uint) ++ Γ)) →
      (Fml.allN x m F).sw k = (F.sw k).map (Fml.allNsw x m)
  | 0, F => by simp only [Fml.allN, Fml.allNsw, Option.map_id']
  | m + 1, F => by
    show (Fml.allN x m (.all x .uint F)).sw k = _
    rw [Fml.sw_allN k x m (.all x .uint F)]
    show ((F.sw k).map (Fml.all x .uint)).map (Fml.allNsw x m) = _
    rw [Option.map_map]
    rfl

/-- A layer's instance is its swapped reading. -/
theorem swInst_allN_imp (k : HashKind) (cs : List Nat) (x : Var) (m : Nat)
    (a b : Fml C (List.replicate m (.val .uint) ++ Γ)) :
    (Fml.allN x m (.imp a b)).swInst k cs = (Fml.allN x m (.imp a b)).sw k := by
  rw [Fml.swInst_allN, Fml.sw_allN]
  rfl

end Swapped

/-- **What the body says under its premise in a heap of the family, the
instance with both layers' words fixed says.** -/
theorem _root_.Solidity.Fml.tkBody3_inst_holds {k₁ k₂ k₃ : HashKind} (hk₁ : k₁ ≠ .ecrecover)
    (hk₃ : k₃ ≠ .ecrecover) (hokA : famOKAll N = true) {Γ : Ctx} (ψ : Fml C Γ) {φF : Fml C Γ}
    (e : ψ.tkBody3 k₁ k₂ k₃ N true true = some φF) {cs : List Nat} {inst : Fml C (Ctx.sw Γ)}
    (ei : φF.swInst k₁ cs = some inst) (τ : State C Γ) (τ' : State C (Ctx.sw Γ)) (h : SwRel k₁ τ τ')
    (hF : FamHeap N τ.glob) (hstr : ∀ {R : RefTy} (i : Idx Γ (.mem R)), (τ.getV i).isSome)
    (hs : Fml.holdsS τ ψ) : holds τ' inst := by
  obtain ⟨φ₂, ψ₂, ψ₃, e₂, hψ₂, e₃, rfl⟩ := Fml.tkBody3_eq e
  obtain ⟨-, ψ₃', -, rfl⟩ := Fml.tkBody_eq e₃
  simp only [↓reduceIte] at ei e₃
  -- the inner layer's swapped reading
  have ei' := ei
  rw [Fml.swInst_allN] at ei'
  obtain ⟨B, hB, -⟩ := Option.map_eq_some_iff.1 ei'
  have hB' : Fml.sw k₁ (.imp (Fml.conjL (fixE k₁ k₂ N (Fml.hLevels k₂ ψ).eraseDups))
      (.imp (Fml.conjL (linkE k₁ (Fml.hLevels k₂ ψ).eraseDups)) (Fml.allN (.user "e")
        (Fml.hLevels k₃ ψ₂).eraseDups.length (.imp (Fml.conjL (fixE k₁ k₃ N (Fml.hLevels k₃ ψ₂).eraseDups))
          (.imp (Fml.conjL (linkE k₁ (Fml.hLevels k₃ ψ₂).eraseDups)) ψ₃'))))) = some B := hB
  obtain ⟨b₁, -, eB⟩ := Option.bind_eq_some_iff.1 hB'
  obtain ⟨Br, hBr, -⟩ := Option.map_eq_some_iff.1 eB
  obtain ⟨b₂, -, eBr⟩ := Option.bind_eq_some_iff.1 hBr
  obtain ⟨ψ₃s, hψ₃s, -⟩ := Option.map_eq_some_iff.1 eBr
  refine tkInst_core hk₁ hokA _ _ ei τ τ' h hF hstr fun es hX => ?_
  have hs₂ : Fml.holdsS (τ.withEnv (envOf _ es τ.env)) ψ₂ := by
    have := (Fml.holdsS_img_xk ψ hψ₂ _).2 ((Fml.xk_holds ψ hψ₂ τ _ hX).2 ((Fml.holdsS_of_xk ψ hψ₂ τ).1 hs))
    rwa [show (XMap.extras (Fml.hLevels k₂ ψ).eraseDups Γ).thin = Thin.dropN _ from rfl, lift_dropN] at this
  rw [lift_dropN]
  have hi₃ : (Fml.allN (.user "e") (Fml.hLevels k₃ ψ₂).eraseDups.length
      (.imp (Fml.conjL (fixE k₁ k₃ N (Fml.hLevels k₃ ψ₂).eraseDups))
        (.imp (Fml.conjL (linkE k₁ (Fml.hLevels k₃ ψ₂).eraseDups)) ψ₃'))).swInst k₁ cs = some ψ₃s := by
    rw [swInst_allN_imp]; exact hψ₃s
  have := Fml.tkBody_inst_holds hk₁ hk₃ hokA ψ₂ e₃ hi₃ _ _ (h.envOf _ es) hF (strOK_envOf hstr _ es) hs₂
  exact (Fml.sw_holds _ hψ₃s _ _ (h.envOf _ es)).1 this

theorem _root_.Solidity.Fml.tk3_allocCount {k₁ k₂ k₃ : HashKind} {fix₂ fix₃ : Bool} {Γ : Ctx}
    (φ : Fml C Γ) : ∀ {φ' : Fml C Γ}, φ.tk3 k₁ k₂ k₃ N fix₂ fix₃ = some φ' → φ'.allocCount = φ.allocCount := by
  have body : ∀ {Γ : Ctx} (ψ φ' : Fml C Γ), ψ.tkBody3 k₁ k₂ k₃ N fix₂ fix₃ = some φ' → φ'.allocCount = 0 := by
    intro Γ ψ φ' e
    obtain ⟨φ₂, ψ₂, ψ₃, -, -, -, rfl⟩ := Fml.tkBody3_eq e
    rw [allocCount_allN]
    rfl
  induction φ with
  | all x p φ ih =>
    intro _ e
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact ih hφ
  | allocAll x R φ ih =>
    intro _ e
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    show φ'.allocCount + 1 = φ.allocCount + 1
    rw [ih hφ]
  | tt | eq | wellFormed | not | and | imp | upd => intro _ e; exact body _ _ e
  | modal | havoc | bind | anon | grow => intro _ e; cases e

/-- **The leaf meets its premise in a heap of the family.** -/
theorem _root_.Solidity.Fml.tk3_hashFree {k₁ k₂ k₃ : HashKind} {fix₂ fix₃ : Bool} {Γ : Ctx}
    {φ φ' : Fml C Γ} (e : φ.tk3 k₁ k₂ k₃ N fix₂ fix₃ = some φ') (hokA : famOKAll N = true)
    (σ : State C Γ) (hF : FamHeap N σ.glob) : φ.HashFree σ := by
  cases φ with
  | all | allocAll => intro _ _ _ _ _ h; exact h.elim
  | modal | havoc | bind | anon | grow => cases e
  | _ =>
    obtain ⟨φ₂, ψ₂, ψ₃, e₂, -⟩ := Fml.tkBody3_eq e
    exact Fml.hashFree_memNodes (Fml.tkBody_memNodes e₂) hokA σ hF

/-- **What the leaf says under its premise, its strings chosen in the
family, the instance with both layers' words fixed says.** -/
theorem _root_.Solidity.Fml.tk3_inst_holds {k₁ k₂ k₃ : HashKind} (hk₁ : k₁ ≠ .ecrecover)
    (hk₃ : k₃ ≠ .ecrecover) (hokA : famOKAll N = true) {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {cs : List Nat} {φF : Fml C Γ} {inst : Fml C (Ctx.sw Γ)}, φ.tk3 k₁ k₂ k₃ N true true = some φF →
      φF.swInst k₁ cs = some inst → (∀ j ∈ cs, j < N) →
      ∀ (τ : State C Γ) (τ' : State C (Ctx.sw Γ)), SwRel k₁ τ τ' → FamHeap N τ.glob →
      (∀ {R : RefTy} (i : Idx Γ (.mem R)), (τ.getV i).isSome) → Fml.holdsS τ φ → holds τ' inst := by
  induction φ with
  | all x p φ ih =>
    intro cs _ _ e ei hcs τ τ' h hF hstr hs
    obtain ⟨φF, hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨inst, hi, rfl⟩ := Option.map_eq_some_iff.1 ei
    exact fun v => ih hφ hi hcs _ _ (h.push v) hF (strOK_push hstr v)
      (hs v (Fml.tk3_hashFree hφ hokA _ hF))
  | allocAll x R φ ih =>
    intro cs _ _ e ei hcs τ τ' h hF hstr hs
    obtain ⟨φF, hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    cases cs with
    | nil => cases ei
    | cons j cs =>
      simp only [Fml.swInst] at ei
      split at ei
      · rename_i hR
        subst hR
        obtain ⟨inst, hi, rfl⟩ := Option.map_eq_some_iff.1 ei
        have hj : j < N := hcs j (List.mem_cons_self ..)
        intro w hw
        have hw' : w = famHash k₁ j := Option.some.inj hw
        subst hw'
        let o := famObj τ.H j
        have hF' : FamHeap N (τ.alloc o).1.glob := hF.alloc hj
        have h' := (h.alloc o).pushMem (τ.alloc o).2
        rw [State.alloc_hashId_self, famObj_words] at h'
        exact ih hφ hi (fun i hi => hcs i (List.mem_cons_of_mem _ hi)) _ _ h' hF' (strOK_alloc hstr o)
          (hs o (Fml.tk3_hashFree hφ hokA _ hF'))
      · cases ei
  | tt | eq | wellFormed | not | and | imp | upd =>
    intro cs _ _ e ei _ τ τ' h hF hstr hs
    exact Fml.tkBody3_inst_holds hk₁ hk₃ hokA _ e ei τ τ' h hF hstr hs
  | modal | havoc | bind | anon | grow => intro _ _ _ e; cases e

/-- **A refutation of the instance with both layers' words fixed refutes
the leaf under its premise.** -/
theorem _root_.Solidity.Fml.tk3_refutes {k₁ k₂ k₃ : HashKind} (hk₁ : k₁ ≠ .ecrecover)
    (hk₃ : k₃ ≠ .ecrecover) (hokA : famOKAll N = true) {φ φF : Fml C []} {cs : List Nat} {inst : Fml C []}
    (e : φ.tk3 k₁ k₂ k₃ N true true = some φF) (ei : φF.swInst k₁ cs = some inst) (hcs : ∀ j ∈ cs, j < N)
    {σ : State C []} (hr : ¬ holds σ inst) : ¬ Fml.holdsH σ.noHeap φ := by
  intro hH
  have hF : FamHeap N σ.noHeap.glob := FamHeap.empty N _ rfl
  exact hr (Fml.tk3_inst_holds hk₁ hk₃ hokA φ e ei hcs σ.noHeap σ ⟨⟨rfl, rfl, rfl, rfl⟩, fun i => nomatch i⟩
    hF (fun i => nomatch i) (hH (Fml.tk3_hashFree e hokA _ hF)))

/-! ## Completeness: each layer relabeled -/

/-- **The fragment of the two relabelings**: the third kind's words in
`Fml.rl` of their own levels and roots (`Fml.tkBodyRL` of the body read
past the second kind's words), and the second kind's in `Fml.rl` of theirs
over the inner layer with its words fixed. -/
def _root_.Solidity.Fml.tkBody3RL (k₁ k₂ k₃ : HashKind) (N : Nat) {Γ : Ctx} (ψ : Fml C Γ) : Bool :=
  match ψ.xk k₂ (XMap.extras (ψ.hLevels k₂).eraseDups Γ) with
  | none => false
  | some ψ₂ =>
    ψ₂.tkBodyRL k₁ k₃ &&
      match ψ₂.tkBody k₁ k₃ N true with
      | none => false
      | some ψ₃ =>
        match Fml.sw k₁ ψ₃ with
        | none => false
        | some Rs =>
          Rs.rl (extraLevels Γ.length (ψ.hLevels k₂).eraseDups.length)
              (Rs.vRoots (extraLevels Γ.length (ψ.hLevels k₂).eraseDups.length)) &&
            kTypedB C (Rs.vRoots (extraLevels Γ.length (ψ.hLevels k₂).eraseDups.length))

/-- `Fml.tkBody3RL` past the prefix. -/
def _root_.Solidity.Fml.tk3RL (k₁ k₂ k₃ : HashKind) (N : Nat) : {Γ : Ctx} → Fml C Γ → Bool
  | _, .all _ _ φ => Fml.tk3RL k₁ k₂ k₃ N φ
  | _, .allocAll _ _ φ => Fml.tk3RL k₁ k₂ k₃ N φ
  | Γ, .tt => Fml.tkBody3RL k₁ k₂ k₃ N (C := C) (Γ := Γ) .tt
  | _, .eq a b => Fml.tkBody3RL k₁ k₂ k₃ N (.eq a b)
  | _, .wellFormed s => Fml.tkBody3RL k₁ k₂ k₃ N (.wellFormed s)
  | _, .not φ => Fml.tkBody3RL k₁ k₂ k₃ N (.not φ)
  | _, .and φ ψ => Fml.tkBody3RL k₁ k₂ k₃ N (.and φ ψ)
  | _, .imp φ ψ => Fml.tkBody3RL k₁ k₂ k₃ N (.imp φ ψ)
  | _, .upd m U φ => Fml.tkBody3RL k₁ k₂ k₃ N (.upd m U φ)
  | _, _ => false

section Complete

variable {Γ : Ctx}

/-- **A layer's link reads no storage.** -/
theorem holds_swLink_withStorage {k₁ : HashKind} (L : List Nat)
    {lk : Fml C (Ctx.sw (List.replicate L.length (.val .uint) ++ Γ))}
    (h : Fml.sw k₁ (Fml.conjL (linkE k₁ L)) = some lk)
    (σ : State C (Ctx.sw (List.replicate L.length (.val .uint) ++ Γ))) (st : Storage C) :
    holds (σ.withStorage st) lk ↔ holds σ lk := by
  rw [sw_conjL_holds _ _ h, sw_conjL_holds _ _ h]
  refine forall_congr' fun f => forall_congr' fun hf => forall_congr' fun g => forall_congr' fun hg => ?_
  obtain ⟨a, b, -, R₁, R₂, i, j, -, -, rfl⟩ := mem_linkE hf
  rw [sw_link_elem] at hg
  cases hg
  rw [holds_wordIff, holds_wordIff]
  rfl

/-- The strings' words past new binders. -/
theorem hW_envOfSw {k : HashKind} {τ : State C (Ctx.sw Γ)}
    (hW : ∀ {R : RefTy} (i : Idx Γ (.mem R)), ∃ j < N, TEnv.get i.sw τ.env = famHash k j) :
    (m : Nat) → (es : Fin m → PrimTy.uint.Denote) →
      ∀ {R : RefTy} (i : Idx (List.replicate m (.val .uint) ++ Γ) (.mem R)),
        ∃ j < N, TEnv.get i.sw (envOfSw m es τ.env) = famHash k j
  | 0, _ => hW
  | m + 1, es => fun i => by
    cases i with
    | there i' => exact hW_envOfSw hW m (fun d => es d.succ) i'

theorem _root_.Solidity.Fml.tkBody3RL_eq {k₁ k₂ k₃ : HashKind} {ψ : Fml C Γ}
    (h : ψ.tkBody3RL k₁ k₂ k₃ N = true) {ψ₂ : Fml C (List.replicate (ψ.hLevels k₂).eraseDups.length (.val .uint) ++ Γ)}
    (hψ₂ : ψ.xk k₂ (XMap.extras (ψ.hLevels k₂).eraseDups Γ) = some ψ₂) {ψ₃}
    (e₃ : ψ₂.tkBody k₁ k₃ N true = some ψ₃) :
    ψ₂.tkBodyRL k₁ k₃ = true ∧ ∃ Rs, Fml.sw k₁ ψ₃ = some Rs ∧
      Rs.rl (extraLevels Γ.length (ψ.hLevels k₂).eraseDups.length)
        (Rs.vRoots (extraLevels Γ.length (ψ.hLevels k₂).eraseDups.length)) = true ∧
      kTypedB C (Rs.vRoots (extraLevels Γ.length (ψ.hLevels k₂).eraseDups.length)) = true := by
  unfold Fml.tkBody3RL at h
  rw [hψ₂] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [e₃] at h2
  simp only at h2
  split at h2
  · cases h2
  · rename_i Rs hRs
    simp only [Bool.and_eq_true] at h2
    exact ⟨h1, Rs, hRs, h2.1, h2.2⟩

/-- **Completeness at the body**: where the instance with both layers'
words fixed is valid, the one with them free holds; the strings' words of
the first kind the family's.  The second kind's words are relabeled first
(the inner layer, its words fixed, the body `tkFix_core` reads), then the
third kind's at each value of the second kind's words. -/
theorem _root_.Solidity.Fml.tkBody3_fix_complete {k₁ k₂ k₃ : HashKind} (hk₁ : k₁ ≠ .ecrecover)
    (hk₂ : k₂ ≠ .ecrecover) (hk₃ : k₃ ≠ .ecrecover) (hokA : famOKAll N = true) (ψ : Fml C Γ)
    {φ₂ φF : Fml C Γ} (e₂ : ψ.tkBody3 k₁ k₂ k₃ N false false = some φ₂)
    (eF : ψ.tkBody3 k₁ k₂ k₃ N true true = some φF) {cs : List Nat}
    {inst₂ instF : Fml C (Ctx.sw Γ)} (ei₂ : φ₂.swInst k₁ cs = some inst₂)
    (eiF : φF.swInst k₁ cs = some instF) (hrl : ψ.tkBody3RL k₁ k₂ k₃ N = true) (τ : State C (Ctx.sw Γ))
    (hW : ∀ {R : RefTy} (i : Idx Γ (.mem R)), ∃ j < N, TEnv.get i.sw τ.env = famHash k₁ j)
    (H : ∀ st, holds (τ.withStorage st) instF) : holds τ inst₂ := by
  obtain ⟨φ₀, ψ₂, ψ₃, e₀, hψ₂, e₃, rfl⟩ := Fml.tkBody3_eq e₂
  obtain ⟨-, ψ₂', ψ₃F, -, hψ₂', e₃F, rfl⟩ := Fml.tkBody3_eq eF
  rw [hψ₂] at hψ₂'
  cases hψ₂'
  obtain ⟨hstr, -⟩ := Fml.tkBody_eq e₀
  obtain ⟨hrl₃, Rs, hRs, hrl1, hK⟩ := Fml.tkBody3RL_eq hrl hψ₂ e₃F
  simp only [Bool.false_eq_true, ↓reduceIte] at ei₂ eiF
  generalize (Fml.hLevels k₂ ψ).eraseDups = L at *
  -- the instance with the second kind's words free, the third's fixed
  have eiF' := eiF
  rw [Fml.swInst_allN] at eiF'
  obtain ⟨BF, hBF, -⟩ := Option.map_eq_some_iff.1 eiF'
  have hBF' : Fml.sw k₁ (.imp (Fml.conjL (fixE k₁ k₂ N L)) (.imp (Fml.conjL (linkE k₁ L)) ψ₃F)) =
    some BF := hBF
  obtain ⟨fx, -, eBF⟩ := Option.bind_eq_some_iff.1 hBF'
  obtain ⟨BFr, hBFr, -⟩ := Option.map_eq_some_iff.1 eBF
  have eiM : (Fml.allN (.user "e") L.length
      (.imp (Fml.conjL []) (.imp (Fml.conjL (linkE k₁ L)) ψ₃F))).swInst k₁ cs =
      some (Fml.allNsw (.user "e") L.length (.imp .tt BFr)) := by
    rw [Fml.swInst_allN]
    show (Fml.sw k₁ (.imp (Fml.conjL []) (.imp (Fml.conjL (linkE k₁ L)) ψ₃F))).map _ = _
    have : Fml.sw k₁ (.imp (Fml.conjL []) (.imp (Fml.conjL (linkE k₁ L)) ψ₃F)) = some (.imp .tt BFr) := by
      show (Fml.sw k₁ .tt).bind _ = _
      rw [show Fml.sw k₁ (.tt : Fml C (List.replicate L.length (.val .uint) ++ Γ)) = some .tt from rfl,
        Option.bind_some, hBFr]
      rfl
    rw [this]
    rfl
  have step₁ : ∀ st, holds (τ.withStorage st) (Fml.allNsw (.user "e") L.length (.imp .tt BFr)) :=
    fun st => tkFix_core hk₁ hk₂ hokA L hstr ψ₃F hRs (kTyped_of hK) hrl1 eiM eiF _ hW fun st' => H st'
  -- the third kind's words, relabeled at each value of the second kind's
  rw [Fml.swInst_allN] at ei₂
  obtain ⟨B₂, hB₂, rfl⟩ := Option.map_eq_some_iff.1 ei₂
  have hB₂' : Fml.sw k₁ (.imp (Fml.conjL []) (.imp (Fml.conjL (linkE k₁ L)) ψ₃)) = some B₂ := hB₂
  obtain ⟨T, -, eB₂⟩ := Option.bind_eq_some_iff.1 hB₂'
  obtain ⟨B₂r, hB₂r, rfl⟩ := Option.map_eq_some_iff.1 eB₂
  obtain ⟨lk, hlk, eB₂r⟩ := Option.bind_eq_some_iff.1 hB₂r
  obtain ⟨X₃, hX₃, rfl⟩ := Option.map_eq_some_iff.1 eB₂r
  obtain ⟨lk', hlk', eBFr⟩ := Option.bind_eq_some_iff.1 hBFr
  rw [hlk] at hlk'
  cases hlk'
  obtain ⟨XF, hXF, rfl⟩ := Option.map_eq_some_iff.1 eBFr
  rw [holds_allNsw]
  intro es _ hl
  have ei₃ : ψ₃.swInst k₁ cs = some X₃ := by
    obtain ⟨-, ψ₃', -, rfl⟩ := Fml.tkBody_eq e₃
    rw [swInst_allN_imp]; exact hX₃
  have eiF₃ : ψ₃F.swInst k₁ cs = some XF := by
    obtain ⟨-, ψ₃', -, rfl⟩ := Fml.tkBody_eq e₃F
    rw [swInst_allN_imp]; exact hXF
  refine Fml.tkBody_fix_complete hk₁ hk₃ hokA ψ₂ e₃ e₃F ei₃ eiF₃ hrl₃ _ (hW_envOfSw hW _ es) fun st => ?_
  have h₁ := (holds_allNsw _ _ _ _).1 (step₁ st) es
  exact h₁ trivial ((holds_swLink_withStorage L hlk _ st).2 hl)

end Complete

/-- **Completeness through the prefix.** -/
theorem _root_.Solidity.Fml.tk3_fix_complete {k₁ k₂ k₃ : HashKind} (hk₁ : k₁ ≠ .ecrecover)
    (hk₂ : k₂ ≠ .ecrecover) (hk₃ : k₃ ≠ .ecrecover) (hokA : famOKAll N = true) {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {cs : List Nat} {φ₂ φF : Fml C Γ} {inst₂ instF : Fml C (Ctx.sw Γ)},
      φ.tk3 k₁ k₂ k₃ N false false = some φ₂ → φ.tk3 k₁ k₂ k₃ N true true = some φF →
      φ₂.swInst k₁ cs = some inst₂ → φF.swInst k₁ cs = some instF → (∀ j ∈ cs, j < N) →
      φ.tk3RL k₁ k₂ k₃ N = true → ∀ τ : State C (Ctx.sw Γ),
        (∀ {R : RefTy} (i : Idx Γ (.mem R)), ∃ j < N, TEnv.get i.sw τ.env = famHash k₁ j) →
        (∀ st, holds (τ.withStorage st) instF) → holds τ inst₂ := by
  induction φ with
  | all x p φ ih =>
    intro cs _ _ _ _ e₂ eF ei₂ eiF hcs hrl τ hW H
    obtain ⟨φ₂, h₂, rfl⟩ := Option.map_eq_some_iff.1 e₂
    obtain ⟨φF, hF, rfl⟩ := Option.map_eq_some_iff.1 eF
    obtain ⟨i₂, hi₂, rfl⟩ := Option.map_eq_some_iff.1 ei₂
    obtain ⟨iF, hiF, rfl⟩ := Option.map_eq_some_iff.1 eiF
    intro v
    refine ih h₂ hF hi₂ hiF hcs hrl _ (fun i => ?_) (fun st => H st v)
    cases i with
    | there j => exact hW j
  | allocAll x R φ ih =>
    intro cs _ _ _ _ e₂ eF ei₂ eiF hcs hrl τ hW H
    obtain ⟨φ₂, h₂, rfl⟩ := Option.map_eq_some_iff.1 e₂
    obtain ⟨φF, hF, rfl⟩ := Option.map_eq_some_iff.1 eF
    cases cs with
    | nil => cases ei₂
    | cons j cs =>
      simp only [Fml.swInst] at ei₂ eiF
      split at ei₂
      · rename_i hR
        rw [if_pos hR] at eiF
        subst hR
        obtain ⟨i₂, hi₂, rfl⟩ := Option.map_eq_some_iff.1 ei₂
        obtain ⟨iF, hiF, rfl⟩ := Option.map_eq_some_iff.1 eiF
        have hj : j < N := hcs j (List.mem_cons_self ..)
        intro w hw
        have hw' : w = famHash k₁ j := Option.some.inj hw
        subst hw'
        refine ih h₂ hF hi₂ hiF (fun i hi => hcs i (List.mem_cons_of_mem _ hi)) hrl _ (fun i => ?_)
          (fun st => H st (famHash k₁ j) rfl)
        cases i with
        | here => exact ⟨j, hj, rfl⟩
        | there i => exact hW i
      · cases ei₂
  | tt | eq | wellFormed | not | and | imp | upd =>
    intro cs _ _ _ _ e₂ eF ei₂ eiF _ hrl τ hW H
    exact Fml.tkBody3_fix_complete hk₁ hk₂ hk₃ hokA _ e₂ eF ei₂ eiF hrl τ hW H
  | modal | havoc | bind | anon | grow => intro _ _ _ _ _ e; cases e

/-- **Completeness of the refutations with three kinds**: where the
reading with both layers' words is not valid, an instance at some classes
of the strings, both layers' words fixed, is not. -/
theorem _root_.Solidity.Fml.tk3_complete {k₁ k₂ k₃ : HashKind} (hk₁ : k₁ ≠ .ecrecover)
    (hk₂ : k₂ ≠ .ecrecover) (hk₃ : k₃ ≠ .ecrecover) (hokA : famOKAll N = true) {φ φ₂ φ₂' : Fml C []}
    (e₂ : φ.tk3 k₁ k₂ k₃ N false false = some φ₂)
    (e' : φ₂.swPrefix k₁ = some φ₂') {V : List Nat} {K : List Name} (hK : KTyped C K)
    (hrl : φ₂.swRL k₁ V K = true) (hpre : φ₂.prefixOK V = true) (hn : φ₂.allocCount ≤ N)
    (hrl₃ : φ.tk3RL k₁ k₂ k₃ N = true)
    (hinst : ∀ cs ∈ rgs φ₂.allocCount, ∃ φF instF, φ.tk3 k₁ k₂ k₃ N true true = some φF ∧
      φF.swInst k₁ cs = some instF)
    (hnv : ¬ Fml.Valid φ₂') :
    ∃ cs ∈ rgs φ₂.allocCount, ∃ φF instF, φ.tk3 k₁ k₂ k₃ N true true = some φF ∧
      φF.swInst k₁ cs = some instF ∧ ¬ Fml.Valid instF := by
  obtain ⟨cs, hcs, inst₂, hi₂, hnv₂⟩ := Fml.swPrefix_complete (famOKAll_ok hokA hk₁) e' hK hrl hpre hn hnv
  obtain ⟨φF, instF, hF, hiF⟩ := hinst cs hcs
  refine ⟨cs, hcs, φF, instF, hF, hiF, fun hv => hnv₂ fun σ => ?_⟩
  have hb : ∀ j ∈ cs, j < N := fun j hj => by
    have := rgsFrom_bound φ₂.allocCount 0 cs hcs j hj
    omega
  exact Fml.tk3_fix_complete hk₁ hk₂ hk₃ hokA φ e₂ hF hi₂ hiF hb hrl₃ σ (fun i => nomatch i)
    (fun st => hv (σ.withStorage st))

/-- info: 'Solidity.Fml.tk3_validH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fml.tk3_validH

/-- info: 'Solidity.Fml.tk3_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fml.tk3_refutes

/-- info: 'Solidity.Fml.tk3_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fml.tk3_complete

end Solidity.Decide
