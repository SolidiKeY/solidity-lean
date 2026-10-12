import Solidity.Calculus.Step
import Solidity.Theory.Observe
import Solidity.Typing.Soundness
import Solidity.Semantics.RunFrame
import Solidity.Theory.Bridge.Denote

/-!
# Terms and updates read in a state; where an update lands

What `holds` (`Calculus/Logic.lean`) reads a term and an update by, on the
typed state with nothing erased (`docs/intrinsic.md`, W9.8.2 and W9.8.3).

* A term: `Tm.eval` (`Calculus/TermEval.lean`), and `Tm.denote`, its reading
  in the Theory (`Theory/Bridge/Denote.lean`'s symbols; a local by its
  position, its value abstracted), which an equation reads; the bridge
  `Tm.denote_eval` says the two agree where `eval` returns.
* `Rhs.eval`: what a local is set to (`LTy.VDen`): a value of its type, a
  storage reference, a storage, a ledger; a memory local's an identity,
  bare, as the sort `ident R` denotes it.
* `Upd.globT`: the typed global part an update leaves (`GlobT`: a
  `State C []` whose heap typing extends the one it was applied in, so the
  `Grown` heap of a memory element is carried, not checked).
* `Upd.held`, `Held.OK`, `Upd.Lands`, `Upd.afterT`: where it lands, a
  memory local's identity typed by the landed state's heap, which is the
  global part's grown one (`Upd.Lands.prefix`).
* `Upd.applyV`: the U1 pair, the typed global part and the locals' values
  (`LocsV`); `Upd.lands_iff_applyV`, `Upd.afterT_applyV`.

The evaluators are recursors and `casesOn` with `match` twins and link
theorems (Gate G0).
-/

namespace Solidity

open Semantics (Halt Res lookupBy setBy)
open Theory Theory.StValue

variable {C : Contract}

theorem Idx.ty_eq_of_toNat {Γ : Ctx} {t u : LTy} {i : Idx Γ t} {j : Idx Γ u}
    (h : i.toNat = j.toNat) : t = u := by
  have hi := i.getElem?_toNat
  have hj := j.getElem?_toNat
  rw [h, hj] at hi
  exact (Option.some.inj hi).symm

/-! ## What a local is set to -/

/-- What a local of type `t` is set to, typed, before the heap it lands in
is known: a memory local's an identity, bare, as the sort `ident R`
denotes it; the rest at their types. -/
@[reducible] def LTy.VDen (C : Contract) : LTy → Type
  | .val p => p.Denote
  | .alias R => Option (SRef C (.ref R))
  | .mem _ => Option Nat
  | .old => Storage C
  | .oldNet => List (Int × Int)

namespace LTy

/-- A typed local's value, its memory reference's identity. -/
def VDen.ofT {H : HTy} : (t : LTy) → t.TDenote C H → t.VDen C
  | .val _, v => v
  | .alias _, a => a
  | .mem _, r => (r : Option (HRef H _)).map (·.id)
  | .old, w => w
  | .oldNet, l => l

end LTy

variable {Γ : Ctx}

/-- A local's typed value, its memory reference's identity. -/
abbrev State.getV (σ : State C Γ) {t : LTy} (i : Idx Γ t) : t.VDen C :=
  LTy.VDen.ofT t (TEnv.get i σ.env)


/-! ## A term in the Theory -/

/-- **A term in the Theory**, read in the typed state `σ`: a local's value
abstracted, a symbol by `OpN.denote` over the global part
(`Theory/Bridge/Denote.lean`).  What an equation reads (`holds`). -/
def Tm.denote (σ : State C Γ) : {s : Srt} → Tm C Γ s → s.TDen
  | _, .pvV i => .prim (PrimTy.erase (TEnv.get i σ.env))
  | _, .pvP i => match (TEnv.get i σ.env : Option (SRef C _)) with
    | some r => r.absT
    | none => []
  | _, .pvS i => Storage.absT (TEnv.get i σ.env : Storage C)
  | _, .pvI _ => ()
  | _, .netOf i a => match a.denote σ with
    | .prim (.int n) => .prim (.int ((lookupBy n (TEnv.get i σ.env : List (Int × Int))).getD 0))
    | _ => .st .mtSt
  | _, .app0 o => o.denote σ.glob
  | _, .app1 o a => o.denote σ.glob (a.denote σ)
  | _, .app2 o a b => o.denote σ.glob (a.eval σ) (b.eval σ) (a.denote σ) (b.denote σ)
  | _, .app3 o a b c => o.denote (a.denote σ) (b.denote σ) (c.denote σ)

/-- **The term bridge**: a term's denotation agrees with its reading in a
typed state wherever the reading returns (`Srt.Bridge`). -/
theorem Tm.denote_eval (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) →
    Srt.BridgeO C σ.H s (t.denote σ) (t.eval σ)
  | _, .pvV _ => by intro x h; cases h; rfl
  | _, .pvP i => by
    intro r h
    have h' : (TEnv.get i σ.env : Option (SRef C _)) = some r := h
    simp only [Tm.denote, h']
    rfl
  | _, .pvS _ => by intro τ h; cases h; exact StValue.Equiv.refl _
  | _, .pvI _ => by intro _ _; trivial
  | _, .netOf i a => by
    intro x h
    rw [Tm.eval_eq_evalM] at h
    simp only [Tm.evalM, Option.bind_eq_some_iff] at h
    obtain ⟨n, hn, h⟩ := h
    rw [← Tm.eval_eq_evalM] at hn
    have ha := Tm.denote_eval σ a n hn
    simp only [Srt.Bridge] at ha
    simp only [Tm.denote, ha, PrimTy.erase, Srt.Bridge]
    simp only [Tm.netOfT, PrimTy.ofInt?] at h
    exact congrArg StValue.prim (PrimTy.erase_of_ofValue? (p := .int) h).symm
  | _, .app0 o => Op0.denote_eval σ.glob o
  | _, .app1 o a => Op1.denote_eval σ.glob o (Tm.denote_eval σ a)
  | _, .app2 o a b => Op2.denote_eval σ.glob o (Tm.denote_eval σ a) (Tm.denote_eval σ b)
  | _, .app3 o a b c =>
    Op3.denote_eval σ.glob o (Tm.denote_eval σ a) (Tm.denote_eval σ b) (Tm.denote_eval σ c)

namespace Rhs

/-- `eval` by `match`, its compiled form. -/
def evalM (σ₀ : State C Γ) : {t : LTy} → Rhs C Γ t → Option (t.VDen C)
  | _, .val t => t.eval σ₀
  | _, .path p => (p.eval σ₀).bind fun r => some (some r)
  | _, .unset => some none
  | _, .mref i => (i.eval σ₀).bind fun id => some (some id)
  | _, .store s => (s.eval σ₀).bind fun st => some st
  | _, .saveNet => some σ₀.net
  | _, .saveNetMt => some []

/-- What a local is set to, read in the typed state `σ₀`; `none` where a
term reverts. -/
@[implemented_by evalM]
def eval (σ₀ : State C Γ) {t : LTy} (r : Rhs C Γ t) : Option (t.VDen C) :=
  @Rhs.casesOn C Γ (fun t _ => Option (t.VDen C)) t r
    (fun {_} x => x.eval σ₀)
    (fun {_} p => (p.eval σ₀).bind fun r => some (some r))
    (fun {_} => some none)
    (fun {_} i => (i.eval σ₀).bind fun id => some (some id))
    (fun s => (s.eval σ₀).bind fun st => some st)
    (some σ₀.net)
    (some [])

theorem eval_eq_evalM (σ₀ : State C Γ) {t : LTy} (r : Rhs C Γ t) : r.eval σ₀ = r.evalM σ₀ := by
  cases r <;> rfl

end Rhs

/-! ## What an update leaves in a local -/

/-- What a local of type `t` holds after a typed update applied in `Γ`: a
local of `Γ` it kept, or the right-hand side last written to it. -/
inductive Held (C : Contract) (Γ : Ctx) (t : LTy) : Type where
  | pos (i : Idx Γ t)
  | rhs (r : Rhs C Γ t)

/-- What every local of `Δ` holds after a typed update from `Γ` to `Δ`. -/
def Subst (C : Contract) (Γ Δ : Ctx) : Type := {t : LTy} → Idx Δ t → Held C Γ t

/-- The local `i` holds `r`. -/
def Subst.set {Δ : Ctx} (s : Subst C Γ Δ) {t : LTy} (i : Idx Δ t) (r : Rhs C Γ t) :
    Subst C Γ Δ :=
  fun j => if h : i.toNat = j.toNat then .rhs (Idx.ty_eq_of_toNat h ▸ r) else s j

/-- A local pushed, holding `h`. -/
def Subst.cons {Δ : Ctx} {t : LTy} (s : Subst C Γ Δ) (h : Held C Γ t) : Subst C Γ (t :: Δ)
  | _, .here => h
  | _, .there j => s j

/-- What one element leaves: a local it sets holds its right-hand side. -/
def UpdElem.heldOn {Δ : Ctx} (e : UpdElem C Γ Δ) (s : Subst C Γ Δ) : Subst C Γ Δ :=
  @UpdElem.casesOn C Γ Δ (fun _ => Subst C Γ Δ) e
    (fun {_} i r => s.set i r) (fun _ => s) (fun _ => s) (fun _ _ => s) (fun _ _ _ => s)
    (fun _ _ => s) (fun _ _ => s) (fun _ => s)

/-- `held` by `match`, its compiled form. -/
def Upd.heldM : {Δ : Ctx} → Upd C Γ Δ → Subst C Γ Δ
  | _, .nil => fun i => .pos i
  | _, .snoc U e => e.heldOn U.heldM
  | _, .decl U _ r => Subst.cons U.heldM (.rhs r)
  | _, .pop U h => fun j => U.heldM (j.ext h)
  | _, .drop U h => fun j => U.heldM (j.wk h)

/-- What a typed update leaves in each local. -/
@[implemented_by Upd.heldM]
def Upd.held {Δ : Ctx} (U : Upd C Γ Δ) : Subst C Γ Δ :=
  @Upd.rec C Γ (fun Δ _ => Subst C Γ Δ) (fun i => .pos i)
    (fun {_} _ e ih => e.heldOn ih)
    (fun {_} {_} _ _ r ih => Subst.cons ih (.rhs r))
    (fun {_} {_} _ h ih => fun j => ih (j.ext h))
    (fun {_} {_} _ h ih => fun j => ih (j.wk h)) Δ U

theorem Upd.held_eq_heldM : {Δ : Ctx} → (U : Upd C Γ Δ) → {t : LTy} → (i : Idx Δ t) →
    U.held i = U.heldM i
  | _, .nil, _, _ => rfl
  | _, .snoc U e, _, i => by
    cases e with
    | «local» k r =>
      show Subst.set U.held k r i = Subst.set U.heldM k r i
      unfold Subst.set
      split
      · rfl
      · exact Upd.held_eq_heldM U i
    | _ => exact Upd.held_eq_heldM U i
  | _, .decl U _ _, _, i => by
    cases i with
    | here => rfl
    | there j => exact Upd.held_eq_heldM U j
  | _, .pop U h, _, i => Upd.held_eq_heldM U (i.ext h)
  | _, .drop U h, _, i => Upd.held_eq_heldM U (i.wk h)

/-! ## The global part an update leaves -/

/-- A typed global part grown from the heap typing `H`: a state with no
locals whose heap typing extends `H` (a memory element's `Grown` heap). -/
abbrev GlobT (C : Contract) (H : HTy) : Type := {g : State C [] // H <+: g.H}

/-- The global part as it is. -/
def State.globG (σ : State C Γ) : GlobT C σ.H := ⟨σ.glob, List.prefix_refl _⟩

/-- The storage replaced. -/
def GlobT.withStorage {H : HTy} (g : GlobT C H) (st : Storage C) : GlobT C H :=
  ⟨{ g.1 with storage := st }, g.2⟩

/-- The memory replaced by a heap grown from `H`. -/
def GlobT.withMem {H : HTy} (g : GlobT C H) (μ : Grown H (fun _ => Unit)) : GlobT C H :=
  ⟨State.mk g.1.storage μ.H' μ.heap () g.1.net g.1.selfBalance g.1.tx, μ.ext⟩

/-- The ledger replaced. -/
def GlobT.withNet {H : HTy} (g : GlobT C H) (nt : List (Int × Int)) : GlobT C H :=
  ⟨{ g.1 with net := nt }, g.2⟩

/-- The contract's balance replaced. -/
def GlobT.withBalance {H : HTy} (g : GlobT C H) (b : PrimTy.uint.Denote) : GlobT C H :=
  ⟨{ g.1 with selfBalance := b }, g.2⟩

/-- `globT` by `match`, its compiled form. -/
def UpdElem.globTM {Δ : Ctx} (σ₀ : State C Γ) :
    UpdElem C Γ Δ → GlobT C σ₀.H → Option (GlobT C σ₀.H)
  | .local _ r, g => (r.eval σ₀).bind fun _ => some g
  | .storage s, g => (s.eval σ₀).bind fun st => some (g.withStorage st)
  | .memory m, g => (m.eval σ₀).bind fun μ =>
    some (g.withMem μ)
  | .selfBalance op a, g => (a.eval σ₀).bind fun amt =>
    (PrimTy.uint.ofInt? (op.apply σ₀.selfBalance.1 amt.1)).bind fun b =>
      some (g.withBalance b)
  | .net r op a, g => (r.eval σ₀).bind fun addr => (a.eval σ₀).bind fun amt =>
    some (g.withNet (setBy addr.1 (op.apply ((lookupBy addr.1 g.1.net).getD 0) amt.1) g.1.net))
  | .pay r a, g => (r.eval σ₀).bind fun addr => (a.eval σ₀).bind fun amt =>
    some (g.withNet (if addr.1 = σ₀.tx.selfAddress.1 then g.1.net
      else setBy addr.1 ((lookupBy addr.1 g.1.net).getD 0 - amt.1) g.1.net))
  | .netMt r a, g => (r.eval σ₀).bind fun addr => (a.eval σ₀).bind fun amt =>
    some (g.withNet [(addr.1, amt.1)])
  | .setBalance a, g => (a.eval σ₀).bind fun amt => some (g.withBalance amt)

/-- The typed global part one element leaves, its right-hand sides read in
`σ₀` (a local's right-hand side is read for its halt). -/
@[implemented_by UpdElem.globTM]
def UpdElem.globT {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElem C Γ Δ) (g : GlobT C σ₀.H) :
    Option (GlobT C σ₀.H) :=
  @UpdElem.casesOn C Γ Δ (fun _ => Option (GlobT C σ₀.H)) e
    (fun {_} _ r => (r.eval σ₀).bind fun _ => some g)
    (fun s => (s.eval σ₀).bind fun st => some (g.withStorage st))
    (fun m => (m.eval σ₀).bind fun μ =>
      some (g.withMem μ))
    (fun op a => (a.eval σ₀).bind fun amt =>
      (PrimTy.uint.ofInt? (op.apply σ₀.selfBalance.1 amt.1)).bind fun b =>
        some (g.withBalance b))
    (fun r op a => (r.eval σ₀).bind fun addr => (a.eval σ₀).bind fun amt =>
      some (g.withNet (setBy addr.1 (op.apply ((lookupBy addr.1 g.1.net).getD 0) amt.1) g.1.net)))
    (fun r a => (r.eval σ₀).bind fun addr => (a.eval σ₀).bind fun amt =>
      some (g.withNet (if addr.1 = σ₀.tx.selfAddress.1 then g.1.net
        else setBy addr.1 ((lookupBy addr.1 g.1.net).getD 0 - amt.1) g.1.net)))
    (fun r a => (r.eval σ₀).bind fun addr => (a.eval σ₀).bind fun amt =>
      some (g.withNet [(addr.1, amt.1)]))
    (fun a => (a.eval σ₀).bind fun amt => some (g.withBalance amt))

theorem UpdElem.globT_eq_globTM {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElem C Γ Δ)
    (g : GlobT C σ₀.H) : e.globT σ₀ g = e.globTM σ₀ g := by
  cases e <;> rfl

/-- `globT` by `match`, its compiled form. -/
def Upd.globTM (σ₀ : State C Γ) : {Δ : Ctx} → Upd C Γ Δ → Option (GlobT C σ₀.H)
  | _, .nil => some σ₀.globG
  | _, .snoc U e => (U.globTM σ₀).bind (e.globT σ₀)
  | _, .decl U _ r => (U.globTM σ₀).bind fun g => (r.eval σ₀).bind fun _ => some g
  | _, .pop U _ => U.globTM σ₀
  | _, .drop U _ => U.globTM σ₀

/-- **The typed global part a typed update applied in `σ₀` leaves**;
`none` where it halts. -/
@[implemented_by Upd.globTM]
def Upd.globT (σ₀ : State C Γ) {Δ : Ctx} (U : Upd C Γ Δ) : Option (GlobT C σ₀.H) :=
  @Upd.rec C Γ (fun _ _ => Option (GlobT C σ₀.H)) (some σ₀.globG)
    (fun {_} _ e ih => ih.bind (e.globT σ₀))
    (fun {_} {_} _ _ r ih => ih.bind fun g => (r.eval σ₀).bind fun _ => some g)
    (fun {_} {_} _ _ ih => ih)
    (fun {_} {_} _ _ ih => ih) Δ U

theorem Upd.globT_eq_globTM (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    U.globT σ₀ = U.globTM σ₀
  | _, .nil => rfl
  | _, .snoc U e => by
    show (U.globT σ₀).bind _ = (U.globTM σ₀).bind _
    rw [Upd.globT_eq_globTM σ₀ U]
  | _, .decl U _ r => by
    show (U.globT σ₀).bind _ = (U.globTM σ₀).bind _
    rw [Upd.globT_eq_globTM σ₀ U]
  | _, .pop U _ => Upd.globT_eq_globTM σ₀ U
  | _, .drop U _ => Upd.globT_eq_globTM σ₀ U

/-! ## Landing -/

/-- What `U` left in the local `i` of `σ'`, read in `σ₀`: a memory local's
identity is the one `σ'` types in its heap. -/
def Held.OK {Δ : Ctx} (σ₀ : State C Γ) (σ' : State C Δ) {t : LTy} (i : Idx Δ t) :
    Held C Γ t → Prop
  | .pos j => σ'.getV i = σ₀.getV j
  | .rhs r => r.eval σ₀ = some (σ'.getV i)

/-- **`U` applied in `σ₀` lands on `σ'`**: it leaves the typed global part
`g`, which is `σ'`'s, and in each local of `σ'` what `Upd.held` says. -/
def Upd.Lands {Δ : Ctx} (σ₀ : State C Γ) (U : Upd C Γ Δ) (g : GlobT C σ₀.H)
    (σ' : State C Δ) : Prop :=
  U.globT σ₀ = some g ∧ σ'.glob = g.1 ∧ ∀ {t : LTy} (i : Idx Δ t), Held.OK σ₀ σ' i (U.held i)

/-- A landed state's heap typing extends the one the update was applied in:
the global part carries it. -/
theorem Upd.Lands.prefix {Δ : Ctx} {σ₀ : State C Γ} {U : Upd C Γ Δ} {g : GlobT C σ₀.H}
    {σ' : State C Δ} (h : U.Lands σ₀ g σ') : σ₀.H <+: σ'.H := by
  have hH : σ'.H = g.1.H := congrArg State.H h.2.1
  rw [hH]
  exact g.2

/-- `p` after `U` applied in `σ₀` under `m`: of every typed state it lands
on, or `m.onHalt` when it halts. -/
def Upd.afterT {Δ : Ctx} (m : Modality) (σ₀ : State C Γ) (U : Upd C Γ Δ)
    (p : State C Δ → Prop) : Prop :=
  match U.globT σ₀ with
  | none => m.onHalt
  | some g => ∀ σ' : State C Δ, U.Lands σ₀ g σ' → p σ'

theorem Upd.afterT_imp {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p q : State C Δ → Prop} (h : U.afterT m σ₀ p) (hpq : ∀ σ', p σ' → q σ') :
    U.afterT m σ₀ q := by
  unfold Upd.afterT at h ⊢
  split
  · rename_i he; rw [he] at h; exact h
  · rename_i g hg; rw [hg] at h; exact fun σ' hl => hpq σ' (h σ' hl)

theorem Upd.afterT.of_lands {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p : State C Δ → Prop} (h : U.afterT m σ₀ p) {g : GlobT C σ₀.H} {σ' : State C Δ}
    (hl : U.Lands σ₀ g σ') : p σ' := by
  unfold Upd.afterT at h
  rw [hl.1] at h
  exact h σ' hl

/-! ## What an update leaves, computed -/

/-- The locals of `Γ`, typed, a memory local's identity bare (`LTy.VDen`). -/
abbrev LocsV (C : Contract) (Γ : Ctx) : Type := (t : LTy) → Idx Γ t → t.VDen C

/-- A typed state's locals. -/
def State.locV (σ : State C Γ) : LocsV C Γ := fun _ i => σ.getV i

namespace LocsV

/-- A local set. -/
def set {Δ : Ctx} (ℓ : LocsV C Δ) {t : LTy} (i : Idx Δ t) (v : t.VDen C) : LocsV C Δ :=
  fun _ j => if h : i.toNat = j.toNat then Idx.ty_eq_of_toNat h ▸ v else ℓ _ j

/-- A local pushed. -/
def push {Δ : Ctx} {t : LTy} (ℓ : LocsV C Δ) (v : t.VDen C) : LocsV C (t :: Δ) :=
  fun _ j => match j with
    | .here => v
    | .there i => ℓ _ i

/-- A suffix popped. -/
def drop {Δ Δ' : Ctx} (h : Ext Δ' Δ) (ℓ : LocsV C Δ) : LocsV C Δ' := fun _ j => ℓ _ (j.ext h)

/-- A frame thinned. -/
def thin {Δ Δ' : Ctx} (h : Thin Δ' Δ) (ℓ : LocsV C Δ) : LocsV C Δ' := fun _ j => ℓ _ (j.wk h)

theorem set_same {Δ : Ctx} (ℓ : LocsV C Δ) {t : LTy} (i : Idx Δ t) (v : t.VDen C) :
    ℓ.set i v t i = v := by
  unfold LocsV.set
  rw [dif_pos rfl]

theorem set_ne {Δ : Ctx} (ℓ : LocsV C Δ) {t u : LTy} (i : Idx Δ t) (j : Idx Δ u)
    (h : i.toNat ≠ j.toNat) (v : t.VDen C) : ℓ.set i v u j = ℓ u j := by
  unfold LocsV.set
  rw [dif_neg h]

end LocsV

/-- `applyV` by `match`, its compiled form. -/
def UpdElem.applyVM {Δ : Ctx} (σ₀ : State C Γ) :
    UpdElem C Γ Δ → GlobT C σ₀.H → LocsV C Δ → Option (GlobT C σ₀.H × LocsV C Δ)
  | .local i r, g, ℓ => (r.eval σ₀).bind fun v => some (g, ℓ.set i v)
  | e, g, ℓ => (e.globT σ₀ g).bind fun g' => some (g', ℓ)

/-- One element applied to a typed global part and the locals, its
right-hand sides read in `σ₀`. -/
@[implemented_by UpdElem.applyVM]
def UpdElem.applyV {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElem C Γ Δ) (g : GlobT C σ₀.H)
    (ℓ : LocsV C Δ) : Option (GlobT C σ₀.H × LocsV C Δ) :=
  @UpdElem.casesOn C Γ Δ (fun _ => Option (GlobT C σ₀.H × LocsV C Δ)) e
    (fun {_} i r => (r.eval σ₀).bind fun v => some (g, ℓ.set i v))
    (fun _ => (e.globT σ₀ g).bind fun g' => some (g', ℓ))
    (fun _ => (e.globT σ₀ g).bind fun g' => some (g', ℓ))
    (fun _ _ => (e.globT σ₀ g).bind fun g' => some (g', ℓ))
    (fun _ _ _ => (e.globT σ₀ g).bind fun g' => some (g', ℓ))
    (fun _ _ => (e.globT σ₀ g).bind fun g' => some (g', ℓ))
    (fun _ _ => (e.globT σ₀ g).bind fun g' => some (g', ℓ))
    (fun _ => (e.globT σ₀ g).bind fun g' => some (g', ℓ))

theorem UpdElem.applyV_eq_applyVM {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElem C Γ Δ)
    (g : GlobT C σ₀.H) (ℓ : LocsV C Δ) : e.applyV σ₀ g ℓ = e.applyVM σ₀ g ℓ := by
  cases e <;> rfl

/-- `applyV` by `match`, its compiled form. -/
def Upd.applyVM (σ₀ : State C Γ) : {Δ : Ctx} → Upd C Γ Δ →
    Option (GlobT C σ₀.H × LocsV C Δ)
  | _, .nil => some (σ₀.globG, σ₀.locV)
  | _, .snoc U e => (U.applyVM σ₀).bind fun p => e.applyV σ₀ p.1 p.2
  | _, .decl U _ r => (U.applyVM σ₀).bind fun p =>
    (r.eval σ₀).bind fun v => some (p.1, p.2.push v)
  | _, .pop U h => (U.applyVM σ₀).bind fun p => some (p.1, p.2.drop h)
  | _, .drop U h => (U.applyVM σ₀).bind fun p => some (p.1, p.2.thin h)

/-- **What a typed update applied in `σ₀` leaves** (U1, typed): the typed
global part and the locals' values. -/
@[implemented_by Upd.applyVM]
def Upd.applyV (σ₀ : State C Γ) {Δ : Ctx} (U : Upd C Γ Δ) :
    Option (GlobT C σ₀.H × LocsV C Δ) :=
  @Upd.rec C Γ (fun Δ _ => Option (GlobT C σ₀.H × LocsV C Δ)) (some (σ₀.globG, σ₀.locV))
    (fun {_} _ e ih => ih.bind fun p => e.applyV σ₀ p.1 p.2)
    (fun {_} {_} _ _ r ih => ih.bind fun p => (r.eval σ₀).bind fun v => some (p.1, p.2.push v))
    (fun {_} {_} _ h ih => ih.bind fun p => some (p.1, p.2.drop h))
    (fun {_} {_} _ h ih => ih.bind fun p => some (p.1, p.2.thin h)) Δ U

theorem Upd.applyV_eq_applyVM (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    U.applyV σ₀ = U.applyVM σ₀
  | _, .nil => rfl
  | _, .snoc U _ | _, .decl U _ _ | _, .pop U _ | _, .drop U _ => by
    show (U.applyV σ₀).bind _ = (U.applyVM σ₀).bind _
    rw [Upd.applyV_eq_applyVM σ₀ U]

/-- What a local holds after an update, as a value: a local of the state
before, or a right-hand side read in it. -/
def Held.OKV {t : LTy} (σ₀ : State C Γ) (v : t.VDen C) : Held C Γ t → Prop
  | .pos j => v = σ₀.getV j
  | .rhs r => r.eval σ₀ = some v

theorem Held.OK_iff_OKV {Δ : Ctx} (σ₀ : State C Γ) (σ' : State C Δ) {t : LTy} (i : Idx Δ t)
    (x : Held C Γ t) : Held.OK σ₀ σ' i x ↔ Held.OKV σ₀ (σ'.getV i) x := by
  cases x <;> exact Iff.rfl

theorem Held.OKV.unique {t : LTy} {σ₀ : State C Γ} {v w : t.VDen C} :
    (x : Held C Γ t) → Held.OKV σ₀ v x → Held.OKV σ₀ w x → v = w
  | .pos _, h₁, h₂ => h₁.trans h₂.symm
  | .rhs _, h₁, h₂ => Option.some.inj (h₁.symm.trans h₂)

private theorem UpdElem.applyV_ok {Δ : Ctx} {σ₀ : State C Γ} (e : UpdElem C Γ Δ)
    {g g' : GlobT C σ₀.H} {ℓ ℓ' : LocsV C Δ} (h : e.applyV σ₀ g ℓ = some (g', ℓ')) :
    e.globT σ₀ g = some g' ∧
      ((∃ (u : LTy) (i : Idx Δ u) (r : Rhs C Γ u) (v : u.VDen C), e = .local i r ∧
        r.eval σ₀ = some v ∧ ℓ' = ℓ.set i v) ∨ ((∀ (u : LTy) (i : Idx Δ u) (r : Rhs C Γ u),
          e ≠ .local i r) ∧ ℓ' = ℓ)) := by
  rw [UpdElem.applyV_eq_applyVM] at h
  cases e with
  | «local» i r =>
    simp only [UpdElem.applyVM, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨v, hv, rfl, rfl⟩ := h
    refine ⟨?_, .inl ⟨_, i, r, v, rfl, hv, rfl⟩⟩
    rw [UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, hv, Option.bind_some]
  | _ =>
    simp only [UpdElem.applyVM, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨g₁, hg, rfl, rfl⟩ := h
    exact ⟨hg, .inr ⟨fun _ _ _ he => UpdElem.noConfusion he, rfl⟩⟩

/-- **What `applyV` computes is the typed global part `globT` computes and,
in each local, what `Upd.held` says.** -/
theorem Upd.applyV_ok {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    {g : GlobT C σ₀.H} → {ℓ : LocsV C Δ} → U.applyV σ₀ = some (g, ℓ) →
    U.globT σ₀ = some g ∧ ∀ {t : LTy} (i : Idx Δ t), Held.OKV σ₀ (ℓ t i) (U.held i)
  | _, .nil, g, ℓ, h => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨rfl, fun _ => rfl⟩
  | _, .snoc U e, g, ℓ, h => by
    change (U.applyV σ₀).bind (fun p => e.applyV σ₀ p.1 p.2) = some (g, ℓ) at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨⟨g₁, ℓ₁⟩, hp, h⟩ := h
    obtain ⟨hg₁, hh₁⟩ := Upd.applyV_ok U hp
    obtain ⟨hg, hl⟩ := UpdElem.applyV_ok e h
    refine ⟨?_, ?_⟩
    · show (U.globT σ₀).bind (e.globT σ₀) = some g
      rw [hg₁]
      exact hg
    · intro t i
      rcases hl with ⟨u, k, r, v, rfl, hv, rfl⟩ | ⟨hne, rfl⟩
      · show Held.OKV σ₀ _ (Subst.set U.held k r i)
        unfold Subst.set
        split
        · rename_i hki
          obtain rfl := Idx.ty_eq_of_toNat hki
          obtain rfl := Idx.toNat_inj k i hki
          show r.eval σ₀ = some (ℓ₁.set k v _ k)
          rw [LocsV.set_same]
          exact hv
        · rename_i hki
          rw [LocsV.set_ne ℓ₁ k i hki]
          exact hh₁ i
      · have hheld : (Upd.snoc U e).held i = U.held i := by
          cases e with
          | «local» k r => exact absurd rfl (hne _ k r)
          | _ => rfl
        rw [hheld]
        exact hh₁ i
  | _, .decl U _ r, g, ℓ, h => by
    change (U.applyV σ₀).bind (fun p => (r.eval σ₀).bind fun v => some (p.1, p.2.push v)) =
      some (g, ℓ) at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨g₁, ℓ₁⟩, hp, v, hv, rfl, rfl⟩ := h
    obtain ⟨hg₁, hh₁⟩ := Upd.applyV_ok U hp
    refine ⟨?_, ?_⟩
    · show (U.globT σ₀).bind (fun g => (r.eval σ₀).bind fun _ => some g) = some g₁
      rw [hg₁, Option.bind_some, hv, Option.bind_some]
    · intro t i
      cases i with
      | here => exact hv
      | there j => exact hh₁ j
  | _, .pop U hx, g, ℓ, h => by
    change (U.applyV σ₀).bind (fun p => some (p.1, p.2.drop hx)) = some (g, ℓ) at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨g₁, ℓ₁⟩, hp, rfl, rfl⟩ := h
    obtain ⟨hg₁, hh₁⟩ := Upd.applyV_ok U hp
    exact ⟨hg₁, fun i => hh₁ (i.ext hx)⟩
  | _, .drop U hx, g, ℓ, h => by
    change (U.applyV σ₀).bind (fun p => some (p.1, p.2.thin hx)) = some (g, ℓ) at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨g₁, ℓ₁⟩, hp, rfl, rfl⟩ := h
    obtain ⟨hg₁, hh₁⟩ := Upd.applyV_ok U hp
    exact ⟨hg₁, fun i => hh₁ (i.wk hx)⟩

/-- Where `globT` returns, so does `applyV`. -/
theorem Upd.applyV_of_globT {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    {g : GlobT C σ₀.H} → U.globT σ₀ = some g → ∃ ℓ, U.applyV σ₀ = some (g, ℓ)
  | _, .nil, g, h => by
    cases h
    exact ⟨_, rfl⟩
  | _, .snoc U e, g, h => by
    change (U.globT σ₀).bind (e.globT σ₀) = some g at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨g₁, hg₁, h⟩ := h
    obtain ⟨ℓ₁, hℓ₁⟩ := Upd.applyV_of_globT U hg₁
    show ∃ ℓ, (U.applyV σ₀).bind (fun p => e.applyV σ₀ p.1 p.2) = _
    rw [hℓ₁, Option.bind_some, UpdElem.applyV_eq_applyVM]
    rw [UpdElem.globT_eq_globTM] at h
    cases e with
    | «local» i r =>
      simp only [UpdElem.globTM, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨v, hv, rfl⟩ := h
      exact ⟨ℓ₁.set i v, by simp only [UpdElem.applyVM, hv, Option.bind_some]⟩
    | _ =>
      rw [← UpdElem.globT_eq_globTM] at h
      exact ⟨ℓ₁, by simp only [UpdElem.applyVM, h, Option.bind_some]⟩
  | _, .decl U _ r, g, h => by
    change (U.globT σ₀).bind (fun g => (r.eval σ₀).bind fun _ => some g) = some g at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨g₁, hg₁, v, hv, rfl⟩ := h
    obtain ⟨ℓ₁, hℓ₁⟩ := Upd.applyV_of_globT U hg₁
    exact ⟨_, by
      show (U.applyV σ₀).bind (fun p => (r.eval σ₀).bind fun v => some (p.1, p.2.push v)) = _
      rw [hℓ₁, Option.bind_some, hv, Option.bind_some]⟩
  | _, .pop U hx, g, h => by
    obtain ⟨ℓ₁, hℓ₁⟩ := Upd.applyV_of_globT (σ₀ := σ₀) U h
    exact ⟨_, by
      show (U.applyV σ₀).bind (fun p => some (p.1, p.2.drop hx)) = _
      rw [hℓ₁, Option.bind_some]⟩
  | _, .drop U hx, g, h => by
    obtain ⟨ℓ₁, hℓ₁⟩ := Upd.applyV_of_globT (σ₀ := σ₀) U h
    exact ⟨_, by
      show (U.applyV σ₀).bind (fun p => some (p.1, p.2.thin hx)) = _
      rw [hℓ₁, Option.bind_some]⟩

/-- **Landing, computed**: a typed update lands on `σ'` exactly where
`applyV` returns `σ'`'s global part and locals. -/
theorem Upd.lands_iff_applyV {Δ : Ctx} {σ₀ : State C Γ} {U : Upd C Γ Δ} {g : GlobT C σ₀.H}
    {σ' : State C Δ} : U.Lands σ₀ g σ' ↔
      ∃ ℓ, U.applyV σ₀ = some (g, ℓ) ∧ σ'.glob = g.1 ∧
        ∀ {t : LTy} (i : Idx Δ t), σ'.getV i = ℓ t i := by
  constructor
  · rintro ⟨hg, hσ, hh⟩
    obtain ⟨ℓ, hℓ⟩ := Upd.applyV_of_globT U hg
    refine ⟨ℓ, hℓ, hσ, fun i => ?_⟩
    exact Held.OKV.unique _ ((Held.OK_iff_OKV _ _ _ _).1 (hh i)) ((Upd.applyV_ok U hℓ).2 i)
  · rintro ⟨ℓ, hℓ, hσ, he⟩
    obtain ⟨hg, hh⟩ := Upd.applyV_ok U hℓ
    refine ⟨hg, hσ, fun i => (Held.OK_iff_OKV _ _ _ _).2 ?_⟩
    rw [he i]
    exact hh i

/-! ## A literal -/


/-! ## The kit

What the rules' soundness and the update laws read `afterT` by: landing
introduced and eliminated, two landings compared, the state an update
leaves by constructor, and `afterT` computed (`Upd.afterT_applyV`). -/

section Kit

variable {Γ : Ctx}

theorem Upd.afterT_and {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p q r : State C Δ → Prop} (hp : U.afterT m σ₀ p) (hq : U.afterT m σ₀ q)
    (h : ∀ σ', p σ' → q σ' → r σ') : U.afterT m σ₀ r := by
  unfold Upd.afterT at hp hq ⊢
  split
  · rename_i he; rw [he] at hp; exact hp
  · rename_i g hg
    rw [hg] at hp hq
    exact fun σ' hl => h σ' (hp σ' hl) (hq σ' hl)

/-- `afterT` from what it asks: `m.onHalt` where the update halts, `p` of
every typed state it lands on. -/
theorem Upd.afterT_intro {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p : State C Δ → Prop} (hh : U.globT σ₀ = none → m.onHalt)
    (hp : ∀ g σ', U.Lands σ₀ g σ' → p σ') : U.afterT m σ₀ p := by
  unfold Upd.afterT
  split
  · rename_i he; exact hh he
  · exact fun σ' hl => hp _ σ' hl

/-- Where an update halts, `afterT` is `m.onHalt`. -/
theorem Upd.afterT.of_none {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p : State C Δ → Prop} (h : U.afterT m σ₀ p) (he : U.globT σ₀ = none) : m.onHalt := by
  unfold Upd.afterT at h
  rw [he] at h
  exact h

/-- What a local holds after an update, as a value, decides landing: two
updates with one global part and one value per local land alike. -/
theorem Upd.lands_of {Δ : Ctx} {σ₀ : State C Γ} {U U' : Upd C Γ Δ}
    (hg : ∀ g, U.globT σ₀ = some g → U'.globT σ₀ = some g)
    (hh : ∀ {t : LTy} (i : Idx Δ t) (v : t.VDen C), Held.OKV σ₀ v (U.held i) →
      Held.OKV σ₀ v (U'.held i))
    {g : GlobT C σ₀.H} {σ' : State C Δ} (hL : U.Lands σ₀ g σ') : U'.Lands σ₀ g σ' :=
  ⟨hg g hL.1, hL.2.1, fun i => (Held.OK_iff_OKV _ _ _ _).2
    (hh i _ ((Held.OK_iff_OKV _ _ _ _).1 (hL.2.2 i)))⟩

/-- `U` gives `U'`'s `afterT` where `U` lands only where `U'` does, and
`m.onHalt` holds where `U` halts and `U'`'s `afterT` holds. -/
theorem Upd.afterT_of_lands {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U U' : Upd C Γ Δ}
    {p : State C Δ → Prop} (he : U.globT σ₀ = none → U'.afterT m σ₀ p → m.onHalt)
    (hl : ∀ g σ', U.Lands σ₀ g σ' → U'.Lands σ₀ g σ') (h : U'.afterT m σ₀ p) :
    U.afterT m σ₀ p :=
  Upd.afterT_intro (fun hU => he hU h) fun _ _ hL => h.of_lands (hl _ _ hL)

/-! ### The state an update leaves, by constructor -/

theorem State.glob_drop {Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) : (σ.drop h).glob = σ.glob :=
  rfl

theorem State.glob_thin {Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) : (σ.thin h).glob = σ.glob :=
  rfl

theorem State.glob_push {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    (σ.push v).glob = σ.glob := rfl

theorem State.glob_setLocal {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).glob = σ.glob := rfl

theorem TEnv.get_drop_ext {H : HTy} : {Γ Δ : Ctx} → (h : Ext Γ Δ) → {t : LTy} → (i : Idx Γ t) →
    (e : TEnv C H Δ) → TEnv.get i (TEnv.drop h e) = TEnv.get (i.ext h) e
  | _, _, .refl, _, _, _ => rfl
  | _, _, .push h, _, i, e => TEnv.get_drop_ext h i e.2

theorem TEnv.get_thin_wk {H : HTy} : {Δ Δ' : Ctx} → (h : Thin Δ' Δ) → {t : LTy} → (j : Idx Δ' t) →
    (e : TEnv C H Δ) → TEnv.get j (TEnv.thin h e) = TEnv.get (j.wk h) e
  | _, _, .refl, _, _, _ => rfl
  | _, _, .keep _, _, .here, _ => rfl
  | _, _, .keep h, _, .there j, e => TEnv.get_thin_wk h j e.2
  | _, _, .drop h, _, j, e => TEnv.get_thin_wk h j e.2

theorem State.getV_drop {Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) {t : LTy} (i : Idx Γ t) :
    (σ.drop h).getV i = σ.getV (i.ext h) := by
  show LTy.VDen.ofT t (TEnv.get i (TEnv.drop h σ.env)) = _
  rw [TEnv.get_drop_ext]

theorem State.getV_thin {Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) {t : LTy} (i : Idx Γ t) :
    (σ.thin h).getV i = σ.getV (i.wk h) := by
  show LTy.VDen.ofT t (TEnv.get i (TEnv.thin h σ.env)) = _
  rw [TEnv.get_thin_wk]

theorem State.getV_push_here {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    (σ.push v).getV .here = LTy.VDen.ofT t v := rfl

theorem State.getV_push_there {t u : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) (j : Idx Γ u) :
    (σ.push v).getV (.there j) = σ.getV j := rfl

theorem State.getV_setLocal_same {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).getV i = LTy.VDen.ofT t v := by
  show LTy.VDen.ofT t (TEnv.get i (TEnv.set i v σ.env)) = _
  rw [TEnv.get_set]

theorem State.getV_setLocal_ne {t u : LTy} (σ : State C Γ) (i : Idx Γ t) (j : Idx Γ u)
    (h : i.toNat ≠ j.toNat) (v : t.TDenote C σ.H) : (σ.setLocal i v).getV j = σ.getV j := by
  show LTy.VDen.ofT u (TEnv.get j (TEnv.set i v σ.env)) = _
  rw [TEnv.get_set_ne i j v σ.env h]

theorem State.anon_nil (σ : State C Γ) (b : (x : (t : LTy) × Idx Γ t) → x.1.TDenote C σ.H) :
    σ.anon [] b = σ := rfl

theorem State.anon_cons (σ : State C Γ) (x : (t : LTy) × Idx Γ t)
    (xs : List ((t : LTy) × Idx Γ t)) (b : (x : (t : LTy) × Idx Γ t) → x.1.TDenote C σ.H) :
    σ.anon (x :: xs) b = (σ.setLocal x.2 (b x)).anon xs b := rfl

theorem State.locV_push {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    (σ.push v).locV = σ.locV.push (LTy.VDen.ofT t v) := by
  funext u j
  cases j <;> rfl

theorem State.locV_drop {Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) :
    (σ.drop h).locV = σ.locV.drop h := by
  funext u j
  exact State.getV_drop h σ j

theorem State.locV_thin {Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) :
    (σ.thin h).locV = σ.locV.thin h := by
  funext u j
  exact State.getV_thin h σ j

theorem State.locV_setLocal {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).locV = σ.locV.set i (LTy.VDen.ofT t v) := by
  funext u j
  show (σ.setLocal i v).getV j = _
  by_cases h : i.toNat = j.toNat
  · obtain rfl := Idx.ty_eq_of_toNat h
    obtain rfl := Idx.toNat_inj i j h
    rw [State.getV_setLocal_same, LocsV.set_same]
  · rw [State.getV_setLocal_ne σ i j h, LocsV.set_ne _ i j h]
    rfl

/-- `{}` lands on the state it is applied in. -/
theorem Upd.lands_nil (σ : State C Γ) : (Upd.nil : Upd C Γ Γ).Lands σ σ.globG σ :=
  ⟨rfl, rfl, fun _ => rfl⟩

/-- A scope's end lands on the state with its locals popped. -/
theorem Upd.lands_pop_nil {Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) :
    (Upd.pop .nil h : Upd C Δ Γ).Lands σ σ.globG (σ.drop h) :=
  ⟨rfl, rfl, fun i => State.getV_drop h σ i⟩

/-- A thinning lands on the state with its dropped locals gone. -/
theorem Upd.lands_drop_nil {Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) :
    (Upd.drop .nil h : Upd C Δ Γ).Lands σ σ.globG (σ.thin h) :=
  ⟨rfl, rfl, fun i => State.getV_thin h σ i⟩

/-- A declaration after an update lands on the state it lands on, the
declared local pushed. -/
theorem Upd.lands_decl {Δ : Ctx} {U : Upd C Γ Δ} {σ₀ : State C Γ} {g : GlobT C σ₀.H}
    {σ' : State C Δ} (hL : U.Lands σ₀ g σ') (x : Var) {t : LTy} {r : Rhs C Γ t}
    {v : t.TDenote C σ'.H} (hr : r.eval σ₀ = some (LTy.VDen.ofT t v)) :
    (U.decl x r).Lands σ₀ g (σ'.push v) := by
  refine ⟨?_, hL.2.1, fun i => ?_⟩
  · show (U.globT σ₀).bind (fun g => (r.eval σ₀).bind fun _ => some g) = _
    rw [hL.1, Option.bind_some, hr, Option.bind_some]
  · cases i with
    | here => exact hr
    | there j => exact hL.2.2 j

/-- A local set after an update lands on the state it lands on, the local
set. -/
theorem Upd.lands_snoc_local {Δ : Ctx} {U : Upd C Γ Δ} {σ₀ : State C Γ} {g : GlobT C σ₀.H}
    {σ' : State C Δ} (hL : U.Lands σ₀ g σ') {t : LTy} (i : Idx Δ t) {r : Rhs C Γ t}
    {v : t.TDenote C σ'.H} (hr : r.eval σ₀ = some (LTy.VDen.ofT t v)) :
    (U.snoc (.local i r)).Lands σ₀ g (σ'.setLocal i v) := by
  refine ⟨?_, hL.2.1, fun j => ?_⟩
  · show (U.globT σ₀).bind (UpdElem.globT σ₀ (.local i r)) = _
    rw [hL.1, Option.bind_some, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, hr, Option.bind_some]
  · show Held.OK σ₀ (σ'.setLocal i v) j (Subst.set (Upd.held U) i r j)
    unfold Subst.set
    split
    · rename_i hij
      obtain rfl := Idx.ty_eq_of_toNat hij
      obtain rfl := Idx.toNat_inj i j hij
      show r.eval σ₀ = some ((σ'.setLocal i v).getV i)
      rw [State.getV_setLocal_same]
      exact hr
    · rename_i hij
      rw [Held.OK_iff_OKV, State.getV_setLocal_ne σ' i j hij]
      exact (Held.OK_iff_OKV _ _ _ _).1 (hL.2.2 j)

/-- **`afterT`, computed**: `p` of every typed state with the global part
and the locals `applyV` returns, or `m.onHalt` where it halts. -/
theorem Upd.afterT_applyV {Δ : Ctx} (m : Modality) (σ₀ : State C Γ) (U : Upd C Γ Δ)
    (p : State C Δ → Prop) :
    U.afterT m σ₀ p ↔ (match U.applyV σ₀ with
      | none => m.onHalt
      | some q => ∀ σ' : State C Δ, σ'.glob = q.1.1 →
          (∀ {t : LTy} (i : Idx Δ t), σ'.getV i = q.2 t i) → p σ') := by
  unfold Upd.afterT
  split
  · rename_i he
    cases ha : U.applyV σ₀ with
    | none => exact Iff.rfl
    | some q =>
      obtain ⟨g, ℓ⟩ := q
      rw [(Upd.applyV_ok U ha).1] at he; cases he
  · rename_i g hg
    obtain ⟨ℓ, hℓ⟩ := Upd.applyV_of_globT U hg
    rw [hℓ]
    refine forall_congr' fun σ' => ⟨fun h hσ he => h (Upd.lands_iff_applyV.2 ⟨ℓ, hℓ, hσ, he⟩),
      fun h hl => ?_⟩
    obtain ⟨ℓ', hℓ', hσ, he⟩ := Upd.lands_iff_applyV.1 hl
    rw [hℓ] at hℓ'
    cases hℓ'
    exact h hσ he

end Kit

/-- `{storage := save(storage, alice.age, sval(1))}`, by hand. -/
def Upd.aliceAgeWrite : Upd StandardExample [] [] :=
  .snoc .nil (.storage (.app3 .save (.app0 .storage) Tm.aliceAge (.app1 .sval (.app0 (.lit ⟨1, rfl⟩)))))

/-- It returns in the initial state, and its global part reads `1` at
`alice.age`, by the kernel. -/
example : ((Upd.aliceAgeWrite.globT (State.init StandardExample)).bind fun g =>
    ((Tm.app2 .find (.app0 .storage) Tm.aliceAge : Tm StandardExample [] (.val .uint)).eval
      g.1).map (·.1)) = some 1 := by
  decide +kernel


end Solidity
