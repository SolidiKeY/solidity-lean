import Solidity.Calculus.CallFunctionEmit

/-! # Intrinsic context-preserving shared-leaf transformation
The recognition witness is indexed by the actual update. Its constructor
refines the target context, so the old post never passes through an untyped
representation or a guessed cast. Existing updates and calculus stay intact.
-/
namespace Solidity.CallFunctionTransform
variable {C : Contract} {Γ : Ctx}

/-- Evidence for precisely the existing single UInt result assignment. -/
inductive Single (C : Contract) (Γ : Ctx) : {Δ : Ctx} → Upd C Γ Δ → Type where
  | local (target : Idx Γ (.val .uint)) (out : Tm C Γ (.val .uint)) :
      Single C Γ (Upd.nil.snoc (.local target (.val out)))

/-- Indexed recognition by constructor recursors. No context comparison or
untyped intermediate term is used; all other update shapes refuse. -/
def classify? : {Δ : Ctx} → (U : Upd C Γ Δ) → Option (Single C Γ U) := by
  intro Δ U
  cases U with
  | nil => exact none
  | decl U x r => exact none
  | pop U h => exact none
  | drop U h => exact none
  | snoc V e =>
    cases V with
    | snoc U e' => exact none
    | decl U x r => exact none
    | pop U h => exact none
    | drop U h => exact none
    | nil =>
      cases e with
      | storage s => exact none
      | memory m => exact none
      | selfBalance op a => exact none
      | net r op a => exact none
      | pay r a => exact none
      | netMt r a => exact none
      | setBalance a => exact none
      | «local» target r =>
        cases r with
        | path p => exact none
        | unset => exact none
        | mref i => exact none
        | store s => exact none
        | saveNet => exact none
        | saveNetMt => exact none
        | zint t => exact none
        | @val p out =>
          cases p with
          | bool => exact none
          | int => exact none
          | uint => exact (some (.local target out))

/-- The recognized context is refined by the witness, not guessed. -/
def update (m : Modality) {Δ : Ctx} (U : Upd C Γ Δ) (φ : Fml C Δ) : Fml C Γ :=
  match classify? U with
  | none => .upd m U φ
  | some w =>
    Single.casesOn (motive := fun {Δ} _ _ => Fml C Δ → Fml C Γ) w
      (fun target out φ => CallFunctionEmit.replace m target out φ) φ

/-- Replacement is exact at all typed states for both modalities, including
refused shapes and arbitrary continuations in their actual output context. -/
theorem holds_update (m : Modality) {Δ : Ctx} (U : Upd C Γ Δ)
    (φ : Fml C Δ) (σ : State C Γ) :
    holds σ (update m U φ) ↔ holds σ (.upd m U φ) := by
  unfold update
  split
  · rfl
  · rename_i w hw
    cases w
    exact CallFunctionEmit.holds_replace m _ _ φ σ

/-- The complete contextual update replacement never enlarges its formula. -/
theorem update_size (m : Modality) {Δ : Ctx} (U : Upd C Γ Δ) (φ : Fml C Δ) :
    (update m U φ).tmSize ≤ (Fml.upd m U φ).tmSize := by
  unfold update
  split
  · exact Nat.le_refl _
  · rename_i w hw
    cases w
    exact CallFunctionEmit.replace_size m _ _ φ

/-- Executable twin: traverse formula children only, never program bodies.
Every binder and update retains its intrinsic source/target contexts. -/
def transformM : {Γ : Ctx} → Fml C Γ → Fml C Γ
  | _, φ => Fml.casesOn (motive := fun Γ _ => Fml C Γ) φ
    .tt
    (fun a b => .eq a b)
    (fun s => .wellFormed s)
    (fun φ => .not (transformM φ))
    (fun φ ψ => .and (transformM φ) (transformM ψ))
    (fun φ ψ => .imp (transformM φ) (transformM ψ))
    (fun m U φ => update m U (transformM φ))
    (fun m P κ φ => .modal m P κ (transformM φ))
    (fun φ => .havoc (transformM φ))
    (fun x p φ => .all x p (transformM φ))
    (fun m x t φ => .bind m x t (transformM φ))
    (fun xs φ => .anon xs (transformM φ))
    (fun x R φ => .allocAll x R (transformM φ))
    (fun φ => .grow (transformM φ))
  termination_by structural _ φ => φ

/-- Complete symbolic-leaf pass by the intrinsic formula recursor. -/
@[implemented_by transformM]
def transform {Γ : Ctx} (φ : Fml C Γ) : Fml C Γ :=
  Fml.rec (motive := fun Γ _ => Fml C Γ)
    .tt
    (fun a b => .eq a b)
    (fun s => .wellFormed s)
    (fun _ ih => .not ih)
    (fun _ _ ihφ ihψ => .and ihφ ihψ)
    (fun _ _ ihφ ihψ => .imp ihφ ihψ)
    (fun m U _ ih => update m U ih)
    (fun m P κ _ ih => .modal m P κ ih)
    (fun _ ih => .havoc ih)
    (fun x p _ ih => .all x p ih)
    (fun m x t _ ih => .bind m x t ih)
    (fun xs _ ih => .anon xs ih)
    (fun x R _ ih => .allocAll x R ih)
    (fun _ ih => .grow ih) φ

/-- The executable traversal is exactly its kernel recursor definition. -/
theorem transform_eq {Γ : Ctx} (φ : Fml C Γ) : transform φ = transformM φ := by
  induction φ with
  | tt => rfl
  | eq a b => rfl
  | wellFormed s => rfl
  | not φ ih =>
    change Fml.not (transform φ) = .not (transformM φ)
    rw [ih]
  | and φ ψ ihφ ihψ =>
    change Fml.and (transform φ) (transform ψ) = .and (transformM φ) (transformM ψ)
    rw [ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
    change Fml.imp (transform φ) (transform ψ) = .imp (transformM φ) (transformM ψ)
    rw [ihφ, ihψ]
  | upd m U φ ih =>
    change update m U (transform φ) = update m U (transformM φ)
    rw [ih]
  | modal m P κ φ ih =>
    change Fml.modal m P κ (transform φ) = .modal m P κ (transformM φ)
    rw [ih]
  | havoc φ ih =>
    change Fml.havoc (transform φ) = .havoc (transformM φ)
    rw [ih]
  | all x p φ ih =>
    change Fml.all x p (transform φ) = .all x p (transformM φ)
    rw [ih]
  | bind m x t φ ih =>
    change Fml.bind m x t (transform φ) = .bind m x t (transformM φ)
    rw [ih]
  | anon xs φ ih =>
    change Fml.anon xs (transform φ) = .anon xs (transformM φ)
    rw [ih]
  | allocAll x R φ ih =>
    change Fml.allocAll x R (transform φ) = .allocAll x R (transformM φ)
    rw [ih]
  | grow φ ih =>
    change Fml.grow (transform φ) = .grow (transformM φ)
    rw [ih]

/-- Every complete transformed leaf preserves its exact observation in every
state. Updates, heap binders and program modalities transport pointwise iff. -/
theorem holds_transform {Γ : Ctx} (φ : Fml C Γ) :
    ∀ σ : State C Γ, holds σ (transform φ) ↔ holds σ φ := by
  induction φ with
  | tt => intro σ; rfl
  | eq a b => intro σ; rfl
  | wellFormed s => intro σ; rfl
  | not φ ih => intro σ; exact not_congr (ih σ)
  | and φ ψ ihφ ihψ => intro σ; exact and_congr (ihφ σ) (ihψ σ)
  | imp φ ψ ihφ ihψ => intro σ; exact imp_congr (ihφ σ) (ihψ σ)
  | upd m U φ ih =>
    intro σ
    change holds σ (update m U (transform φ)) ↔ holds σ (.upd m U φ)
    apply (holds_update m U (transform φ) σ).trans
    exact ⟨fun hp => Upd.afterT_imp hp (fun τ hτ => (ih τ).mp hτ),
      fun hq => Upd.afterT_imp hq (fun τ hτ => (ih τ).mpr hτ)⟩
  | modal m P κ φ ih =>
    intro σ
    exact Modality.afterRunTR_congr_iff m _ _ _ ih
  | havoc φ ih =>
    intro σ
    exact forall_congr' (fun _ => forall_congr' (fun _ => forall_congr' (fun _ => ih _)))
  | all x p φ ih => intro σ; exact forall_congr' (fun _ => ih _)
  | bind m x t φ ih => intro σ; exact forall_congr' (fun _ => ih _)
  | anon xs φ ih => intro σ; exact forall_congr' (fun _ => ih _)
  | allocAll x R φ ih => intro σ; exact forall_congr' (fun _ => ih _)
  | grow φ ih => intro σ; exact forall_congr' (fun _ => imp_congr Iff.rfl (ih _))

/-- Size checks on actual emitted leaves lift through every old formula
constructor. Program text and context metadata remain outside tmSize. -/
theorem transform_size {Γ : Ctx} (φ : Fml C Γ) : (transform φ).tmSize ≤ φ.tmSize := by
  induction φ with
  | tt => exact Nat.le_refl _
  | eq a b => exact Nat.le_refl _
  | wellFormed s => exact Nat.le_refl _
  | not φ ih => change 1 + (transform φ).tmSize ≤ 1 + φ.tmSize; omega
  | and φ ψ ihφ ihψ =>
    change 1 + (transform φ).tmSize + (transform ψ).tmSize ≤ 1 + φ.tmSize + ψ.tmSize
    omega
  | imp φ ψ ihφ ihψ =>
    change 1 + (transform φ).tmSize + (transform ψ).tmSize ≤ 1 + φ.tmSize + ψ.tmSize
    omega
  | upd m U φ ih =>
    have hb : (update m U (transform φ)).tmSize ≤ 1 + U.tmSize + (transform φ).tmSize :=
      update_size m U (transform φ)
    change (update m U (transform φ)).tmSize ≤ 1 + U.tmSize + φ.tmSize
    omega
  | modal m P κ φ ih => change 1 + (transform φ).tmSize ≤ 1 + φ.tmSize; omega
  | havoc φ ih => change 1 + (transform φ).tmSize ≤ 1 + φ.tmSize; omega
  | all x p φ ih => change 1 + (transform φ).tmSize ≤ 1 + φ.tmSize; omega
  | bind m x t φ ih => change 1 + (transform φ).tmSize ≤ 1 + φ.tmSize; omega
  | anon xs φ ih => change 1 + (transform φ).tmSize ≤ 1 + φ.tmSize; omega
  | allocAll x R φ ih => change 1 + (transform φ).tmSize ≤ 1 + φ.tmSize; omega
  | grow φ ih => change 1 + (transform φ).tmSize ≤ 1 + φ.tmSize; omega

/-- Exact validity transport for the original closed scoped formula. -/
theorem valid_iff (φ : Fml C []) : (transform φ).Valid ↔ φ.Valid :=
  forall_congr' (fun σ => holds_transform φ σ)

end Solidity.CallFunctionTransform
