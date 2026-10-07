import Solidity.Calculus.Core.Logic
import Solidity.Calculus.NoPanic

/-!
# Soundness of a rule on scoped statements: the statement, and its kit

What it means for one arm of `Stmt.step` (`Calculus/Core/Step.lean`) to be
sound against M3's interpreter (`Core.Stmt.run`), stated once here so that
every arm, `Calculus/Core/SoundArms.lean`'s and the call, `try` and loop
arms of `Calculus/Core/Blocks.lean`, proves the same shape
(`docs/intrinsic.md`, M6a):

* `Premise.Sound m s p σ`: in the state `σ`, the premise `p` put in front of
  any rest `ω`, frames `κ` and postcondition `φ` (`Premise.fml`) gives
  `⟨ s; ω κ ⟩ φ`;
* `Stmt.StepSound k m s`: whatever premise `s.step k m` gives is sound in
  every state whose locals are typed (`State.Typed`).

`State.Typed` is the one typing fact a rule needs that M3's untyped values
do not give: a `bool` local holds a `bool`, so a split on a simple condition
has one of its two goals (the cover goal today's split proves).  M4a's
typed values make it true of every state.

The kit: a scoped term never panics (`Tm.eval_noPanic`, from
`Calculus/NoPanic.lean`'s symbols), so neither does an update
(`Upd.apply_noPanic`), and an update rule needs only that its update ends as
the statement does (`Premise.Sound.update`); a lowered expression reads what
it evaluates to (`Val.eval_lower` and its kin, `Update.lean`'s
`Val.lower_eval`).
-/

namespace Solidity.Core

open Solidity (Modality Srt NoPanic Op0 Op1 Op2 Op3)
open Semantics (Value Res Halt)
open Solidity (readAddr)

variable {C : Contract}

/-! ## The statement -/

/-- A `bool` local holds a `bool` (M4a's typed values make it true of every
state). -/
def State.Typed {Γ : Ctx} (σ : State C Γ) : Prop :=
  ∀ i : Idx Γ (.val .bool), ∃ b : Bool, (Env.get i σ.env : Value) = .bool b

/-- **A premise is sound** for the statement `s` in `σ` under `m`: in front of
any rest, frames and postcondition, it gives `⟨ s; ω κ ⟩ φ`. -/
def Premise.Sound (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (p : Premise C Γ Γ')
    (σ : State C Γ) : Prop :=
  ∀ {Γ₁ Γ₀ : Ctx} (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀),
    holds σ (p.fml m ω κ φ) → holds σ (.modal m (.cons s ω) κ φ)

/-- **The rule of `s` is sound**: the premise `Stmt.step` gives, fresh names
at `k`, is sound in every typed state.  Each arm proves this of its
statements. -/
def Stmt.StepSound (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Prop :=
  ∀ σ : State C Γ, σ.Typed → ∀ p, s.step k m = some p → Premise.Sound m s p σ

/-- An arm that gives the premise `p` is sound when `p` is. -/
theorem Stmt.StepSound.of_eq {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (hs : s.step k m = some p)
    (h : ∀ σ : State C Γ, σ.Typed → Premise.Sound m s p σ) : Stmt.StepSound k m s := by
  intro σ hσ p' hp'
  rw [hs] at hp'
  cases hp'
  exact h σ hσ

/-! ## A term never panics -/

section NoPanic

variable {Γ : Ctx}

/-- **A scoped term never panics**: its symbols are `Update.lean`'s. -/
theorem Tm.eval_noPanic (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) → s.NoPanic (t.eval σ)
  | _, .pvV _ => NoPanic.pure _
  | _, .pvP i => by
    show NoPanic (aliasPath σ i)
    unfold aliasPath; split <;> no_panic
  | _, .pvS _ => NoPanic.pure _
  | _, .pvI _ => NoPanic.pure _
  | _, .netOf i a => by
    have ha : NoPanic (a.eval σ) := Tm.eval_noPanic σ a
    simp only [Tm.eval, Srt.NoPanic]
    no_panic
  | _, .app0 o => Op0.eval_noPanic σ.glob o
  | _, .app1 o _ a => Op1.eval_noPanic σ.glob o (Tm.eval_noPanic σ a)
  | _, .app2 o a b => Op2.eval_noPanic σ.glob o (Tm.eval_noPanic σ a) (Tm.eval_noPanic σ b)
  | _, .app3 o a b c =>
    Op3.eval_noPanic σ.glob o (Tm.eval_noPanic σ a) (Tm.eval_noPanic σ b) (Tm.eval_noPanic σ c)

theorem Rhs.eval_noPanic (σ : State C Γ) {t : LTy} (r : Rhs C Γ t) : NoPanic (r.eval σ) := by
  cases r with
  | val t => exact Tm.eval_noPanic σ t
  | path p => have := Tm.eval_noPanic σ p; simp only [Rhs.eval]; no_panic
  | unset => exact NoPanic.pure _
  | mref i => exact Tm.eval_noPanic σ i
  | store s => have := Tm.eval_noPanic σ s; simp only [Rhs.eval]; no_panic
  | saveNet => exact NoPanic.pure _
  | saveNetMt => exact NoPanic.pure _

theorem UpdElem.write_noPanic {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElem C Γ Δ) (τ : State C Δ) :
    NoPanic (e.write σ₀ τ) := by
  have hv : ∀ t : Tm C Γ .val, NoPanic (t.eval σ₀) := fun t => Tm.eval_noPanic σ₀ t
  have hs : ∀ t : Tm C Γ .st, NoPanic (t.eval σ₀) := fun t => Tm.eval_noPanic σ₀ t
  have hm : ∀ t : Tm C Γ .mem, NoPanic (t.eval σ₀) := fun t => Tm.eval_noPanic σ₀ t
  cases e with
  | «local» i r => have := Rhs.eval_noPanic σ₀ r; simp only [UpdElem.write]; no_panic
  | _ => simp only [UpdElem.write]; no_panic

/-- **An update never panics.** -/
theorem Upd.apply_noPanic (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) → NoPanic (U.apply σ₀)
  | _, .nil => NoPanic.pure _
  | _, .snoc U e =>
    NoPanic.bind (Upd.apply_noPanic σ₀ U) fun τ _ => UpdElem.write_noPanic σ₀ e τ
  | _, .decl U _ r =>
    NoPanic.bind (Upd.apply_noPanic σ₀ U) fun _ _ =>
      NoPanic.bind (Rhs.eval_noPanic σ₀ r) fun _ _ => NoPanic.pure _
  | _, .pop U h => by
    show NoPanic (State.drop h <$> U.apply σ₀)
    rw [NoPanic.map]; exact Upd.apply_noPanic σ₀ U
  | _, .drop U h => by
    show NoPanic (State.thin h <$> U.apply σ₀)
    rw [NoPanic.map]; exact Upd.apply_noPanic σ₀ U

end NoPanic

/-! ## A lowered expression reads what it evaluates to -/

section Lower

variable {Γ : Ctx} (σ : State C Γ)

mutual

theorem SPath.eval_lower : {T : Ty} → (b : SPath C Γ T) → b.lower.eval σ = b.resolve σ
  | _, .alias _ => rfl
  | _, .loc l => Loc.eval_lower l

theorem Loc.eval_lower : {T : Ty} → (l : Loc C Γ T) → l.lower.eval σ = l.resolve σ
  | _, .root .. => rfl
  | _, .field b f _ => by
    simp only [Loc.lower, Tm.eval, Op1.eval, Loc.resolve, SPath.eval_lower b]
  | _, .index _ b i => by
    simp only [Loc.lower, Tm.eval, Op2.eval, Loc.resolve, SPath.eval_lower b, Val.eval_lower i]

theorem MPath.eval_lower : {T : Ty} → (b : MPath C Γ T) →
    b.lower.eval σ = (do (← b.mval σ).asRef)
  | _, .var .. => rfl
  | _, .loc l => by
    simp only [MPath.lower, Tm.eval, Op2.eval, Op0.eval, MPath.mval, ← MLoc.eval_lower l,
      bind_assoc, pure_bind]

theorem MLoc.eval_lower : {T : Ty} → (l : MLoc C Γ T) →
    (do readAddr σ.glob (← l.lower.eval σ)) = l.read σ
  | _, .field b f _ => by
    simp only [MLoc.lower, Tm.eval, Op1.eval, MLoc.read, MPath.eval_lower b, bind_assoc, pure_bind]
    rfl
  | _, .index _ b i => by
    simp only [MLoc.lower, Tm.eval, Op2.eval, MLoc.read, MPath.eval_lower b, Val.eval_lower i,
      bind_assoc, pure_bind]
    rfl

theorem Val.eval_lower : {p : PrimTy} → (v : Val C Γ p) → v.lower.eval σ = v.eval σ
  | _, .simple s => Simple.eval_lower s σ
  | _, .read l => by
    simp only [Val.lower, Tm.eval, Op2.eval, Op0.eval, Val.eval, Loc.eval_lower l, pure_bind]
  | _, .binop _ _ _ a b => by
    simp only [Val.lower, Tm.eval, Op2.eval, Val.eval, Val.eval_lower a, Val.eval_lower b]
  | _, .unop _ _ _ a => by
    simp only [Val.lower, Tm.eval, Op1.eval, Val.eval, Val.eval_lower a]
  | _, .ternary c a b => by
    simp only [Val.lower, Tm.eval, Op3.eval, Val.eval, Val.eval_lower c, Val.eval_lower a,
      Val.eval_lower b]
  | _, .readMem l => by
    simp only [Val.lower, Tm.eval, Op2.eval, Op0.eval, Val.eval, ← MLoc.eval_lower l, bind_assoc,
      pure_bind]
  | _, .len b _ => by
    simp only [Val.lower, Tm.eval, Op2.eval, Op0.eval, Val.eval, SPath.eval_lower b, pure_bind]
  | _, .mlen b _ => by
    simp only [Val.lower, Tm.eval, Op2.eval, Op0.eval, Val.eval, MPath.eval_lower b, bind_assoc,
      pure_bind]

end

end Lower

/-! ## The premise shapes, as `Premise.Sound` -/

section Shapes

variable {Γ Γ' : Ctx} {m : Modality}

/-- **An update** is sound when it ends as the statement does. -/
theorem Premise.Sound.update {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} {σ : State C Γ}
    (hs : U.apply σ = s.run σ) : Premise.Sound m s (.update U) σ :=
  fun ω κ φ => Premise.sound_update σ hs (hs ▸ Upd.apply_noPanic σ U) ω κ φ

/-- **A block** is sound when it runs as the statement, its fresh locals
popped. -/
theorem Premise.Sound.unfold {Γ'' : Ctx} {P : Prog C Γ Γ''} {h : Ext Γ' Γ''} {s : Stmt C Γ Γ'}
    {σ : State C Γ} (hs : (Prog.run σ P).map (State.drop h) = s.run σ) :
    Premise.Sound m s (.unfold P h) σ :=
  fun ω κ φ => Premise.sound_unfold σ hs ω κ φ

/-- **A block dropping a frame** from under what it keeps. -/
theorem Premise.Sound.inline {Γ'' : Ctx} {P : Prog C Γ Γ''} {h : Thin Γ' Γ''} {s : Stmt C Γ Γ'}
    {σ : State C Γ} (hs : (Prog.run σ P).map (State.thin h) = s.run σ) :
    Premise.Sound m s (.inline P h) σ :=
  fun ω κ φ => Premise.sound_inline σ hs ω κ φ

/-- **A hidden binder** is sound when, for some value of the local, the
block runs as the statement. -/
theorem Premise.Sound.bind {x : Var} {t : LTy} {P : Prog C (t :: Γ) Γ'} {s : Stmt C Γ Γ'}
    {σ : State C Γ} (hs : ∃ v, Prog.run (σ.push v) P = s.run σ) :
    Premise.Sound m s (.bind x t P) σ :=
  fun ω κ φ => Premise.sound_bind σ hs ω κ φ

/-- **A block of a declaration and a statement on top of it**, the local
popped after: sound when the statement, from where the declaration leaves,
runs as `s`, its local popped, and `s` halts where the declaration does
(a capture: `T se = nse; s'`). -/
theorem Premise.Sound.declThen {t : LTy} {d : Stmt C Γ (t :: Γ)} {s' : Stmt C (t :: Γ) (t :: Γ)}
    {s : Stmt C Γ Γ} {σ : State C Γ}
    (hok : ∀ τ, d.run σ = .ok τ → (s'.run τ).map (State.drop (.push .refl)) = s.run σ)
    (herr : ∀ e, d.run σ = .error e → s.run σ = .error e) :
    Premise.Sound m s (.unfold (.cons d (.cons s' .nil)) (.push .refl)) σ := by
  refine Premise.Sound.unfold ?_
  rw [Prog.run_cons]
  cases hd : d.run σ with
  | error e => rw [herr e hd]; rfl
  | ok τ =>
    rw [← hok τ hd]
    show (Prog.run τ (.cons s' .nil)).map _ = _
    rw [Prog.run_cons]
    cases s'.run τ <;> rfl

/-- **A value captured**: `T se = nse; s'`. -/
theorem Premise.Sound.capture {p : PrimTy} {x : Var} {e : Val C Γ p}
    {s' : Stmt C (.val p :: Γ) (.val p :: Γ)} {s : Stmt C Γ Γ} {σ : State C Γ}
    (hok : ∀ v, e.eval σ = .ok v → (s'.run (σ.push v)).map (State.drop (.push .refl)) = s.run σ)
    (herr : ∀ h, e.eval σ = .error h → s.run σ = .error h) :
    Premise.Sound m s (.capture p x e s') σ :=
  fun ω κ φ => Premise.sound_capture σ hok herr ω κ φ

/-- **A storage path captured**: `T storage sp = nsp; s'`. -/
theorem Premise.Sound.captureSP {R : RefTy} {x : Var} {b : SPath C Γ (.ref R)}
    {s' : Stmt C (.alias R :: Γ) (.alias R :: Γ)} {s : Stmt C Γ Γ} {σ : State C Γ}
    (hok : ∀ q, b.resolve σ = .ok q →
      (s'.run (σ.push (t := .alias R) (some q))).map (State.drop (.push .refl)) = s.run σ)
    (herr : ∀ h, b.resolve σ = .error h → s.run σ = .error h) :
    Premise.Sound m s (.captureSP x b s') σ := by
  refine Premise.Sound.declThen (fun τ hτ => ?_) (fun e he => ?_)
  · have hd : Stmt.run σ (.declStorage R x (some (.path b))) =
        (do let q ← b.resolve σ; pure (σ.push (t := .alias R) (some q))) := by
      show Run.declStorage R (some (.path b)) σ = _
      simp only [Run.declStorage, ARhs.eval, bind_assoc, pure_bind]
    rw [hd] at hτ
    cases hb : b.resolve σ with
    | error => rw [hb] at hτ; cases hτ
    | ok q => rw [hb] at hτ; cases hτ; exact hok q hb
  · have hd : Stmt.run σ (.declStorage R x (some (.path b))) =
        (do let q ← b.resolve σ; pure (σ.push (t := .alias R) (some q))) := by
      show Run.declStorage R (some (.path b)) σ = _
      simp only [Run.declStorage, ARhs.eval, bind_assoc, pure_bind]
    rw [hd] at he
    cases hb : b.resolve σ with
    | error h => rw [hb] at he; cases he; exact herr _ hb
    | ok q => rw [hb] at he; cases he

/-- **A memory path captured**: `T memory mv = nmp; s'`. -/
theorem Premise.Sound.captureMV {R : RefTy} {x : Var} {b : MPath C Γ (.ref R)}
    {s' : Stmt C (.mem R :: Γ) (.mem R :: Γ)} {s : Stmt C Γ Γ} {σ : State C Γ}
    (hok : ∀ id, (do (← b.mval σ).asRef) = .ok id →
      (s'.run (σ.push (t := .mem R) id)).map (State.drop (.push .refl)) = s.run σ)
    (herr : ∀ h, (do (← b.mval σ).asRef) = .error h → s.run σ = .error h) :
    Premise.Sound m s (.captureMV x b s') σ := by
  have hd : Stmt.run σ (.declMem R x (some (.alias b)) rfl b.mapFree) =
      (do let id ← (do (← b.mval σ).asRef); pure (σ.push (t := .mem R) id)) := by
    show Run.declMem R (some (.alias b)) σ = _
    simp only [Run.declMem, MRhs.eval, bind_assoc, pure_bind]
  show Premise.Sound m s (.unfold (.cons (.declMem R x (some (.alias b)) rfl b.mapFree)
    (.cons s' .nil)) (.push .refl)) σ
  refine Premise.Sound.declThen (fun τ hτ => ?_) (fun e he => ?_)
  · rw [hd] at hτ
    revert hτ hok
    cases (do (← b.mval σ).asRef : Res Nat) with
    | error => intro _ h; cases h
    | ok id => intro hok h; cases h; exact hok id rfl
  · rw [hd] at he
    revert he herr
    cases (do (← b.mval σ).asRef : Res Nat) with
    | error h => intro herr he; cases he; exact herr _ rfl
    | ok id => intro _ h; cases h

end Shapes

/-! ## A state with a local pushed -/

section Push

variable {Γ : Ctx} {t : LTy} (σ : State C Γ) (w : t.Denote C)

theorem State.push_setLocal {u : LTy} (i : Idx Γ u) (x : u.Denote C) :
    (σ.push w).setLocal i.there x = (σ.setLocal i x).push w := rfl

theorem State.push_withGlob (g : Semantics.State) :
    (σ.push w).withGlob g = (σ.withGlob g).push w := rfl

theorem State.drop_push : (σ.push w).drop (.push .refl) = σ := rfl

theorem State.get_push_here : (Env.get .here (σ.push w).env : t.Denote C) = w := rfl

theorem State.get_push_there {u : LTy} (i : Idx Γ u) :
    (Env.get i.there (σ.push w).env : u.Denote C) = Env.get i σ.env := rfl

end Push

end Solidity.Core
