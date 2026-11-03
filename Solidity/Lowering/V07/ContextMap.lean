import Solidity.Lowering.V07.DoubleAssignment

/-! P12 G19-CONTEXT-MAP: compiler-independent position certificates over
existing heterogeneous contexts. This is neither an AST nor a value/state
carrier. Positional identity does NOT assert heap-object alias agreement.
Value alignment is a separate pointwise predicate; no execution/compiler
preservation result occurs in it. A complete admitted-source producer is open. -/
namespace Solidity.Lowering.V07

structure ContextMap (srcΓ : Source.RCtx) (Γ : Ctx) where
  slot : {τ : Source.STy} → Source.Idx srcΓ τ → (u : LTy) × Idx Γ u
  positions : ∀ {τ σ : Source.STy} (i : Source.Idx srcΓ τ) (j : Source.Idx srcΓ σ),
    i.toNat = j.toNat ↔ (slot i).2.toNat = (slot j).2.toNat

/-- Thinning preserves and reflects positions even at DIFFERENT local types. -/
theorem idx_wk_positions : {Γ Δ : Ctx} → {u v : LTy} → (h : Thin Γ Δ) →
    (i : Idx Γ u) → (j : Idx Γ v) →
    (i.wk h).toNat = (j.wk h).toNat ↔ i.toNat = j.toNat
  | _,_,_,_,.refl,_,_ => Iff.rfl
  | _,_,_,_,.drop h,i,j => by
    simpa only [Idx.wk,Idx.toNat,Nat.add_left_inj] using idx_wk_positions h i j
  | _,_,_,_,.keep _,.here,.here => Iff.rfl
  | _,_,_,_,.keep _,.here,.there _ => by
    simp only [Idx.wk,Idx.toNat]; omega
  | _,_,_,_,.keep _,.there _,.here => by
    simp only [Idx.wk,Idx.toNat]; omega
  | _,_,_,_,.keep h,.there i,.there j => by
    simpa only [Idx.wk,Idx.toNat,Nat.add_left_inj] using idx_wk_positions h i j

namespace ContextMap

def empty : ContextMap [] [] where
  slot i := nomatch i
  positions i := nomatch i

/-- A Source binding and its intrinsic binding are fresh by context structure.
The target local type is metadata, not a claim that every Source type lowers. -/
def cons {srcΓ : Source.RCtx} {Γ : Ctx} (m : ContextMap srcΓ Γ)
    (τ : Source.STy) (u : LTy) : ContextMap (τ :: srcΓ) (u :: Γ) where
  slot i := match i with
    | .here => ⟨u,.here⟩
    | .there j => ⟨(m.slot j).1,.there (m.slot j).2⟩
  positions i j := by
    cases i with
    | here => cases j with
      | here => exact Iff.rfl
      | there j => change (0 = j.toNat+1 ↔ 0 = (m.slot j).2.toNat+1); omega
    | there i => cases j with
      | here => change (i.toNat+1 = 0 ↔ (m.slot i).2.toNat+1 = 0); omega
      | there j =>
        change (i.toNat+1 = j.toNat+1 ↔ (m.slot i).2.toNat+1 = (m.slot j).2.toNat+1)
        exact ⟨fun eq => congrArg (·+1) ((m.positions i j).mp (Nat.succ.inj eq)),
          fun eq => congrArg (·+1) ((m.positions i j).mpr (Nat.succ.inj eq))⟩

/-- Target-only capture binders and arbitrary published Thin maps. -/
def wk {srcΓ : Source.RCtx} {Γ Δ : Ctx} (m : ContextMap srcΓ Γ) (h : Thin Γ Δ) :
    ContextMap srcΓ Δ where
  slot i := ⟨(m.slot i).1,(m.slot i).2.wk h⟩
  positions i j := (m.positions i j).trans (idx_wk_positions h _ _).symm

theorem ext {srcΓ : Source.RCtx} {Γ : Ctx} (m n : ContextMap srcΓ Γ)
    (same : ∀ {τ : Source.STy} (i : Source.Idx srcΓ τ), m.slot i = n.slot i) : m = n := by
  cases m with | mk ms mp =>
    cases n with | mk ns np =>
      have eq : @ms = @ns := by funext τ i; exact same i
      cases eq
      rfl

theorem wk_identity {srcΓ : Source.RCtx} {Γ : Ctx} (m : ContextMap srcΓ Γ) :
    m.wk .refl = m := by
  apply ext
  intro τ i
  change ⟨(m.slot i).1,(m.slot i).2.wk .refl⟩ = m.slot i
  rw [Idx.wk_refl]

theorem wk_composition {srcΓ : Source.RCtx} {Γ Δ Ω : Ctx} (m : ContextMap srcΓ Γ)
    (a : Thin Γ Δ) (b : Thin Δ Ω) : (m.wk a).wk b = m.wk (a.trans b) := by
  apply ext
  intro τ i
  change (⟨(m.slot i).1,((m.slot i).2.wk a).wk b⟩ : (u : LTy) × Idx Ω u) =
    ⟨(m.slot i).1,(m.slot i).2.wk (a.trans b)⟩
  rw [Idx.wk_trans]

/-- Initial typed value alignment only. R must be a compiler-independent
relation on these existing carriers. This definition contains no evaluator,
compiler or desired preservation premise. It asserts no complete world relation. -/
def Related {D : Source.Layout} {srcΓ : Source.RCtx} {C : Contract} {H : HTy} {Γ : Ctx}
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val D τ → u.TDenote C H → Prop)
    (source : Source.Locals D srcΓ) (target : TEnv C H Γ) : Prop :=
  ∀ {τ : Source.STy} (i : Source.Idx srcΓ τ),
    R τ (m.slot i).1 (source.get i) (TEnv.get (m.slot i).2 target)

theorem related_cons {D : Source.Layout} {srcΓ : Source.RCtx} {C : Contract} {H : HTy} {Γ : Ctx}
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val D τ → u.TDenote C H → Prop)
    (source : Source.Locals D srcΓ) (target : TEnv C H Γ) (old : m.Related R source target)
    (τ : Source.STy) (u : LTy) (sv : Source.Val D τ) (tv : u.TDenote C H)
    (new : R τ u sv tv) : (m.cons τ u).Related R (.cons sv source) (tv,target) := by
  intro σ i
  cases i with
  | here => exact new
  | there i => exact old i

theorem related_wk {D : Source.Layout} {srcΓ : Source.RCtx} {C : Contract} {Γ Δ : Ctx}
    (m : ContextMap srcΓ Γ) (target : State C Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val D τ → u.TDenote C target.H → Prop)
    (source : Source.Locals D srcΓ) (old : m.Related R source target.env)
    (h : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    (m.wk h).Related R source (target.lift h extra).env := by
  intro τ i
  change R τ (m.slot i).1 (source.get i) (TEnv.get ((m.slot i).2.wk h) (target.lift h extra).env)
  rw [State.get_lift]
  exact old i

end ContextMap
end Solidity.Lowering.V07
