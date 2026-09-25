import Solidity.Kernel.Semantics

/-!
# Fresh names, weakening, and the frame lemma

A taclet that unfolds a statement introduces scratch locals (`se`, `sp`,
`ie`).  In the untyped calculus a scratch name is a fixed string, and every
rule's soundness theorem carries a hypothesis that the statement does not use
it (`stmtUsesVar … = false`).  In the kernel that is a fact about the typing:
**a term typed at `Γ` only mentions names `Γ` binds and state variables**.  So
a name `Fresh` at `Γ` — neither — cannot occur in it, and the frame lemmas
(`SPath.resolve_frame`, `Val.eval_frame`) are unconditional in the term.

Weakening moves a term to a larger context: `Ctx.Sub C Γ Γ'` says every local
keeps its binding and every state variable stays unshadowed.  Binding a fresh
name is one (`Ctx.Sub.fresh`).  Weakening changes only the proofs a term
carries, never its erasure (`SPath.erase_weaken`), so it costs nothing at run
time.
-/

namespace Solidity
namespace Kernel

open Semantics RuleSoundness

variable {C : Contract}

/-- `x` is fresh at `Γ`: no local and no state variable is called `x`. -/
def Fresh (C : Contract) (Γ : Ctx) (x : Name) : Prop :=
  lookupBy x Γ = none ∧ C.rootType x = none

instance (C : Contract) (Γ : Ctx) (x : Name) : Decidable (Fresh C Γ x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `Γ'` extends `Γ`: locals keep their bindings, state variables stay
visible. -/
structure Ctx.Sub (C : Contract) (Γ Γ' : Ctx) : Prop where
  local_ : ∀ x b, lookupBy x Γ = some b → lookupBy x Γ' = some b
  root : ∀ r, lookupBy r Γ = none → (C.rootType r).isSome → lookupBy r Γ' = none

/-- Every context extends itself. -/
theorem Ctx.Sub.refl (Γ : Ctx) : Ctx.Sub C Γ Γ := ⟨fun _ _ h => h, fun _ h _ => h⟩

/-- Extension composes: `uint se = e;` then `T storage sp = nsp;` extends by
both. -/
theorem Ctx.Sub.trans {Γ₁ Γ₂ Γ₃ : Ctx} (h₁ : Ctx.Sub C Γ₁ Γ₂) (h₂ : Ctx.Sub C Γ₂ Γ₃) :
    Ctx.Sub C Γ₁ Γ₃ :=
  ⟨fun x b h => h₂.local_ x b (h₁.local_ x b h),
   fun r h hr => h₂.root r (h₁.root r h hr) hr⟩

/-- Binding a fresh name extends the context: after `uint se = alice.age;`
with `se` fresh, `alice` is still the state variable and every local is
what it was. -/
theorem Ctx.Sub.fresh {Γ : Ctx} {x : Name} (h : Fresh C Γ x) (b : BTy) :
    Ctx.Sub C Γ (setBy x b Γ) := by
  refine ⟨fun y b' hy => ?_, fun r hr hroot => ?_⟩
  · have hne : y ≠ x := fun he => by rw [he, h.1] at hy; cases hy
    rw [lookupBy_setBy_ne hne]; exact hy
  · have hne : r ≠ x := fun he => by rw [he, h.2] at hroot; cases hroot
    rw [lookupBy_setBy_ne hne]; exact hr

/-! ## Weakening -/

mutual

def SPath.weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') : {T : Ty} → SPath C Γ T → SPath C Γ' T
  | _, .alias x hx => .alias x (h.local_ _ _ hx)
  | _, .loc l => .loc (l.weaken h)

def Loc.weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') : {T : Ty} → Loc C Γ T → Loc C Γ' T
  | _, .root r hΓ hr => .root r (h.root r hΓ (by simp [hr])) hr
  | _, .field b f hf => .field (b.weaken h) f hf
  | _, .mapIndex b i => .mapIndex (b.weaken h) (i.weaken h)
  | _, .arrIndex b i => .arrIndex (b.weaken h) (i.weaken h)

def Val.weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') : {p : PrimTy} → Val C Γ p → Val C Γ' p
  | _, .lit n hn => .lit n hn
  | _, .bool b => .bool b
  | _, .local x hx => .local x (h.local_ _ _ hx)
  | _, .read l => .read (l.weaken h)
  | _, .binop op hop a b => .binop op hop (a.weaken h) (b.weaken h)
  | _, .unop op hop a => .unop op hop (a.weaken h)

end

def Src.weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') {T : Ty} : Src C Γ T → Src C Γ' T
  | .val v => .val (v.weaken h)
  | .copy p hp => .copy (p.weaken h) hp

mutual

/-- Weakening does not change the erasure: `alice.age` is the same term at
every context that sees `alice`. -/
theorem SPath.erase_weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') :
    {T : Ty} → (p : SPath C Γ T) → (p.weaken h).erase = p.erase
  | _, .alias .. => rfl
  | _, .loc l => l.erase_weaken h

theorem Loc.erase_weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') :
    {T : Ty} → (l : Loc C Γ T) → (l.weaken h).erase = l.erase
  | _, .root .. => rfl
  | _, .field b f _ => by simp only [Loc.weaken, Loc.erase, b.erase_weaken h]
  | _, .mapIndex b i => by simp only [Loc.weaken, Loc.erase, b.erase_weaken h, i.erase_weaken h]
  | _, .arrIndex b i => by simp only [Loc.weaken, Loc.erase, b.erase_weaken h, i.erase_weaken h]

theorem Val.erase_weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') :
    {p : PrimTy} → (v : Val C Γ p) → (v.weaken h).erase = v.erase
  | _, .lit .. | _, .bool _ | _, .local .. => rfl
  | _, .read l => by simp only [Val.weaken, Val.erase, l.erase_weaken h]
  | _, .binop _ _ a b => by simp only [Val.weaken, Val.erase, a.erase_weaken h, b.erase_weaken h]
  | _, .unop _ _ a => by simp only [Val.weaken, Val.erase, a.erase_weaken h]

end

/-- Weakening does not change a source's erasure. -/
theorem Src.erase_weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') {T : Ty} :
    (r : Src C Γ T) → (r.weaken h).erase = r.erase
  | .val v => v.erase_weaken h
  | .copy p _ => p.erase_weaken h

/-! ## The frame lemma -/

section Frame

variable {ns : List Name} {σ τ : State} {Γ : Ctx}

/-- A name a term can use is not a fresh one. -/
theorem not_mem_of_bound (hns : ∀ n ∈ ns, Fresh C Γ n) {x : Name} {b : BTy}
    (hx : lookupBy x Γ = some b) : x ∉ ns := fun hm => by
  rw [(hns x hm).1] at hx; cases hx

theorem not_mem_of_root (hns : ∀ n ∈ ns, Fresh C Γ n) {r : Name} {T : Ty}
    (hr : C.rootType r = some T) : r ∉ ns := fun hm => by
  rw [(hns r hm).2] at hr; cases hr

theorem envPath_frame (hag : EnvAgreeExcept ns σ τ) {x : Name} (hx : x ∉ ns) (g : Bool) :
    envPath σ x g = envPath τ x g := by
  unfold envPath; rw [hag.env x hx]

mutual

/-- **Frame.** Two states that agree off fresh names resolve a path alike:
binding a scratch `sp` does not move `alice.account`. -/
theorem SPath.resolve_frame (hag : EnvAgreeExcept ns σ τ) (hns : ∀ n ∈ ns, Fresh C Γ n) :
    {T : Ty} → (p : SPath C Γ T) → p.resolve σ = p.resolve τ
  | _, .alias _ hx => envPath_frame hag (not_mem_of_bound hns hx) _
  | _, .loc l => l.resolve_frame hag hns

/-- **Frame**, for locations: `people[i].age` resolves alike in two states
that agree off fresh names. -/
theorem Loc.resolve_frame (hag : EnvAgreeExcept ns σ τ) (hns : ∀ n ∈ ns, Fresh C Γ n) :
    {T : Ty} → (l : Loc C Γ T) → l.resolve σ = l.resolve τ
  | _, .root _ _ hr => envPath_frame hag (not_mem_of_root hns hr) _
  | _, .field b _ _ => by simp only [Loc.resolve, b.resolve_frame hag hns]
  | _, .mapIndex b i => by simp only [Loc.resolve, b.resolve_frame hag hns, i.eval_frame hag hns]
  | _, .arrIndex b i => by simp only [Loc.resolve, b.resolve_frame hag hns, i.eval_frame hag hns]

/-- **Frame**, for values: `x + alice.age` evaluates alike in two states that
agree off fresh names. -/
theorem Val.eval_frame (hag : EnvAgreeExcept ns σ τ) (hns : ∀ n ∈ ns, Fresh C Γ n) :
    {p : PrimTy} → (v : Val C Γ p) → v.eval σ = v.eval τ
  | _, .lit .. | _, .bool _ => rfl
  | _, .local _ hx => by
    simp only [Val.eval, State.getEnv, hag.env _ (not_mem_of_bound hns hx)]
  | _, .read l => by simp only [Val.eval, l.resolve_frame hag hns, findStorage_congr hag]
  | _, .binop _ _ a b => by simp only [Val.eval, a.eval_frame hag hns, b.eval_frame hag hns]
  | _, .unop _ _ a => by simp only [Val.eval, a.eval_frame hag hns]

end

/-- **Frame**, for sources. -/
theorem Src.value_frame (hag : EnvAgreeExcept ns σ τ) (hns : ∀ n ∈ ns, Fresh C Γ n) {T : Ty} :
    (r : Src C Γ T) → r.value σ = r.value τ
  | .val v => by simp only [Src.value, v.eval_frame hag hns]
  | .copy p _ => by simp only [Src.value, p.resolve_frame hag hns, findStorage_congr hag]

/-- A write location is found alike in two states that agree off fresh names. -/
theorem Loc.target_frame (hag : EnvAgreeExcept ns σ τ) (hns : ∀ n ∈ ns, Fresh C Γ n) {T : Ty}
    (l : Loc C Γ T) : l.target σ = l.target τ := by
  cases l <;> simp only [Loc.target] <;> exact Loc.resolve_frame hag hns _

end Frame

/-! ## Weakening keeps the denotation -/

mutual

/-- A weakened path resolves as the original: `alice.account` read after
`uint se = 1;` is the path it was. -/
theorem SPath.resolve_weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') (σ : State) :
    {T : Ty} → (p : SPath C Γ T) → (p.weaken h).resolve σ = p.resolve σ
  | _, .alias .. => rfl
  | _, .loc l => l.resolve_weaken h σ

theorem Loc.resolve_weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') (σ : State) :
    {T : Ty} → (l : Loc C Γ T) → (l.weaken h).resolve σ = l.resolve σ
  | _, .root .. => rfl
  | _, .field b _ _ => by simp only [Loc.weaken, Loc.resolve, b.resolve_weaken h σ]
  | _, .mapIndex b i => by
    simp only [Loc.weaken, Loc.resolve, b.resolve_weaken h σ, i.eval_weaken h σ]
  | _, .arrIndex b i => by
    simp only [Loc.weaken, Loc.resolve, b.resolve_weaken h σ, i.eval_weaken h σ]

/-- A weakened value evaluates as the original. -/
theorem Val.eval_weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') (σ : State) :
    {p : PrimTy} → (v : Val C Γ p) → (v.weaken h).eval σ = v.eval σ
  | _, .lit .. | _, .bool _ | _, .local .. => rfl
  | _, .read l => by simp only [Val.weaken, Val.eval, l.resolve_weaken h σ]
  | _, .binop _ _ a b => by simp only [Val.weaken, Val.eval, a.eval_weaken h σ, b.eval_weaken h σ]
  | _, .unop _ _ a => by simp only [Val.weaken, Val.eval, a.eval_weaken h σ]

end

end Kernel
end Solidity
