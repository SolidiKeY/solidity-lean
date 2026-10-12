import Solidity.Calculus.Lower
import Solidity.Calculus.Logic

/-!
# Typed updates read in a state; where they land

`Calculus/Lands.lean`'s reading of an update, for the typed terms of
`Calculus/Fml.lean` (`Rhs`, `UpdElem`, `Upd`; `RhsT`, `UpdElemT`, `UpdT` before W9.8.3), on the typed state
with nothing erased (`docs/intrinsic.md`, "W9.8.2 lands record"):
* `RhsT.eval`: what a local is set to, typed (`LTy.VDen`): a value of its
  type, a storage reference, a storage, a ledger; a memory local's an
  identity, bare, as the sort `ident R` denotes it.
* `UpdT.globT`: the typed global part an update leaves (`GlobT`: a
  `State C []` whose heap typing extends the one it was applied in, so the
  `Grown` heap of a memory element is carried, not checked).
* `UpdT.held`, `HeldT.OK`, `UpdT.Lands`, `UpdT.afterT`: where it lands, a
  memory local's identity typed by the landed state's heap, which is the
  global part's grown one: no `IdOk` premise.
* `UpdT.applyV`: the U1 pair, the typed global part and the locals' values
  (`LocsV`); `UpdT.lands_iff_applyV`.
* `holdsUpdT`: `holds`' update clause over a typed update, beside `holds`.

**The bridges** against `Lands` through `.erase`, where the update is exact
(`UpdT.Exact`: every term's `TmT.Exact`, a balance written in range):
`RhsT.eval_agree`, `UpdT.globT_agree`, `UpdT.applyV_agree` both ways
(`OAgree`: `some` is `.ok` of the value erased, `none` some halt);
`UpdT.lands_iff` both ways at the typed global part; `UpdT.afterT_of_erase`
and `holdsUpdT_of_holds` one way only: the erased landing does not fix the
heap typing of an object the update allocates, so the erased clause asks
`p` of more states than the typed one.

The evaluators are recursors and `casesOn` with `match` twins and link
theorems (Gate G0).
-/

namespace Solidity

open Semantics (Halt Res lookupBy setBy)

variable {C : Contract}

/-! ## Agreement with an untyped reading -/

/-- The untyped reading `r` agrees with the typed `x` through `f`: `x`'s
value through `f`, or some halt where `x` is `none`. -/
def OAgree {α β : Type} (f : α → β) : Option α → Res β → Prop
  | some a, r => r = .ok (f a)
  | none, r => ∃ h, r = .error h

theorem OAgree.bind {α β γ δ : Type} {f : α → β} {g : γ → δ} {x : Option α} {r : Res β}
    {k : α → Option γ} {k' : β → Res δ} (h : OAgree f x r)
    (hk : ∀ a, x = some a → OAgree g (k a) (k' (f a))) : OAgree g (x.bind k) (r >>= k') := by
  cases x with
  | none =>
    obtain ⟨e, he⟩ := h
    subst he
    exact ⟨e, rfl⟩
  | some a =>
    have hr : r = .ok (f a) := h
    subst hr
    exact hk a rfl

theorem OAgree.some_iff {α β : Type} {f : α → β} {a : α} {r : Res β} :
    OAgree f (some a) r ↔ r = .ok (f a) := Iff.rfl

theorem OAgree.unique {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b)
    {x : Option α} {r : Res β} (h : OAgree f x r) {a : α} :
    x = some a ↔ r = .ok (f a) := by
  cases x with
  | none =>
    obtain ⟨e, he⟩ := h
    subst he
    exact ⟨fun h => Option.noConfusion h, fun h => Except.noConfusion h⟩
  | some b =>
    have hr : r = .ok (f b) := h
    subst hr
    exact ⟨fun h => by cases h; rfl, fun h => by rw [hf b a (Except.ok.inj h)]⟩

section Sorts

variable {g : State C []}

theorem SrtT.Agree.val {p : PrimTy} {x : Option p.Denote} {r : Semantics.Res Semantics.Value}
    (h : SrtT.Agree g (.val p) x r) : OAgree PrimTy.erase x r := by
  cases x <;> exact h

theorem SrtT.Agree.path {T : Ty} {x : Option (SRef C T)} {r : Res (Name × List Semantics.Seg)}
    (h : SrtT.Agree g (.path T) x r) : OAgree SRef.erase x r := by
  cases x <;> exact h

theorem SrtT.Agree.st {x : Option (Storage C)} {r : Res Semantics.State}
    (h : SrtT.Agree g .st x r) : OAgree (Storage.into g.globE) x r := by
  cases x <;> exact h

theorem SrtT.Agree.ident {R : RefTy} {x : Option Nat} {r : Res Nat}
    (h : SrtT.Agree g (.ident R) x r) : OAgree id x r := by
  cases x <;> exact h

theorem SrtT.Agree.mem {x : Option (Grown g.H (fun _ => Unit))} {r : Res Semantics.State}
    (h : SrtT.Agree g .mem x r) : OAgree (fun m => Heap.into g.globE m.heap) x r := by
  cases x <;> exact h

end Sorts

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
  | .old, st => st
  | .oldNet, l => l

/-- The untyped value. -/
def VDen.erase : (t : LTy) → t.VDen C → t.Denote C
  | .val p, v => PrimTy.erase (p := p) v
  | .alias _, a => a.map SRef.erase
  | .mem _, r => r
  | .old, st => Storage.erase (st : Storage C)
  | .oldNet, l => l

theorem VDen.erase_ofT {H : HTy} :
    (t : LTy) → (v : t.TDenote C H) → VDen.erase t (VDen.ofT t v) = TDenote.erase t v
  | .val _, _ | .alias _, _ | .mem _, _ | .old, _ | .oldNet, _ => rfl

end LTy

/-- A path is its segments. -/
theorem Path.erase_injective {T U : Ty} (p : Path T U) :
    ∀ q : Path T U, p.erase = q.erase → p = q := by
  induction p
  case nil =>
    intro q hq
    cases q <;> simp only [Path.erase, List.nil_eq, reduceCtorEq] at hq ⊢
  case field hl p ih =>
    intro q hq
    cases q with
    | nil => simp only [Path.erase, reduceCtorEq] at hq
    | field hl' q =>
      simp only [Path.erase, List.cons.injEq, Semantics.Seg.field.injEq] at hq
      obtain ⟨rfl, hq⟩ := hq
      obtain rfl := Option.some.inj (hl.symm.trans hl')
      rw [ih q hq]
  all_goals
    rename_i i p ih
    intro q hq
    cases q <;> simp only [Path.erase, List.cons.injEq, Semantics.Seg.at.injEq, reduceCtorEq] at hq
    obtain ⟨rfl, hq⟩ := hq
    rw [ih _ hq]

/-- A storage reference is its root and segments. -/
theorem SRef.erase_injective {U : Ty} {r r' : SRef C U} (h : r.erase = r'.erase) : r = r' := by
  obtain ⟨n, hn, p⟩ := r
  obtain ⟨n', hn', p'⟩ := r'
  simp only [SRef.erase, Prod.mk.injEq] at h
  obtain ⟨rfl, hp⟩ := h
  obtain rfl := Option.some.inj (hn.symm.trans hn')
  rw [Path.erase_injective p p' hp]

/-- A storage is its untyped one. -/
theorem Storage.erase_injective {st st' : Storage C} (h : st.erase = st'.erase) : st = st' := by
  have h₁ := SFields.ofU_erase st
  have h₂ := SFields.ofU_erase st'
  unfold Storage.erase at h
  rw [h, h₂] at h₁
  exact (Option.some.inj h₁).symm

theorem LTy.VDen.erase_injective : (t : LTy) → {v w : t.VDen C} →
    VDen.erase t v = VDen.erase t w → v = w
  | .val _, _, _, h => PrimTy.erase_injective h
  | .alias _, none, none, _ => rfl
  | .alias _, some _, some _, h => by
    simp only [VDen.erase, Option.map_some, Option.some.injEq] at h
    rw [SRef.erase_injective h]
  | .alias _, none, some _, h | .alias _, some _, none, h => by
    simp only [VDen.erase, Option.map_some, Option.map_none, reduceCtorEq] at h
  | .mem _, _, _, h => h
  | .old, _, _, h => Storage.erase_injective h
  | .oldNet, _, _, h => h

variable {Γ : Ctx}

/-- A local's typed value, its memory reference's identity. -/
abbrev State.getV (σ : State C Γ) {t : LTy} (i : Idx Γ t) : t.VDen C :=
  LTy.VDen.ofT t (TEnv.get i σ.env)

theorem State.getE_getV (σ : State C Γ) {t : LTy} (i : Idx Γ t) :
    σ.getE i = LTy.VDen.erase t (σ.getV i) :=
  (LTy.VDen.erase_ofT t _).symm

namespace RhsT

/-- `eval` by `match`, its compiled form. -/
def evalM (σ₀ : State C Γ) : {t : LTy} → RhsT C Γ t → Option (t.VDen C)
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
def eval (σ₀ : State C Γ) {t : LTy} (r : RhsT C Γ t) : Option (t.VDen C) :=
  @RhsT.casesOn C Γ (fun t _ => Option (t.VDen C)) t r
    (fun {_} x => x.eval σ₀)
    (fun {_} p => (p.eval σ₀).bind fun r => some (some r))
    (fun {_} => some none)
    (fun {_} i => (i.eval σ₀).bind fun id => some (some id))
    (fun s => (s.eval σ₀).bind fun st => some st)
    (some σ₀.net)
    (some [])

theorem eval_eq_evalM (σ₀ : State C Γ) {t : LTy} (r : RhsT C Γ t) : r.eval σ₀ = r.evalM σ₀ := by
  cases r <;> rfl

/-- Where the right-hand side is exact: its term's `TmT.Exact`. -/
def Exact (σ₀ : State C Γ) : {t : LTy} → RhsT C Γ t → Prop
  | _, .val t => t.Exact σ₀
  | _, .path p => p.Exact σ₀
  | _, .unset => True
  | _, .mref i => i.Exact σ₀
  | _, .store s => s.Exact σ₀
  | _, .saveNet => True
  | _, .saveNetMt => True

/-- **The right-hand side's bridge**: exact both ways where its term is. -/
theorem eval_agree (σ₀ : State C Γ) : {t : LTy} → (r : RhsT C Γ t) → r.Exact σ₀ →
    OAgree (LTy.VDen.erase t) (r.eval σ₀) (r.erase.eval σ₀)
  | _, .val x, h => (TmT.eval_agree σ₀ x h).val
  | _, .path p, h => OAgree.bind (TmT.eval_agree σ₀ p h).path fun _ _ => rfl
  | _, .unset, _ => rfl
  | _, .mref i, h => OAgree.bind (TmT.eval_agree σ₀ i h).ident fun _ _ => rfl
  | _, .store s, h => OAgree.bind (TmT.eval_agree σ₀ s h).st fun _ _ => rfl
  | _, .saveNet, _ => rfl
  | _, .saveNetMt, _ => rfl

end RhsT

/-! ## What an update leaves in a local -/

/-- What a local of type `t` holds after a typed update applied in `Γ`: a
local of `Γ` it kept, or the right-hand side last written to it. -/
inductive HeldT (C : Contract) (Γ : Ctx) (t : LTy) : Type where
  | pos (i : Idx Γ t)
  | rhs (r : RhsT C Γ t)

def HeldT.erase {t : LTy} : HeldT C Γ t → Held C Γ t
  | .pos i => .pos i
  | .rhs r => .rhs r.erase

/-- What every local of `Δ` holds after a typed update from `Γ` to `Δ`. -/
def SubstT (C : Contract) (Γ Δ : Ctx) : Type := {t : LTy} → Idx Δ t → HeldT C Γ t

/-- The local `i` holds `r`. -/
def SubstT.set {Δ : Ctx} (s : SubstT C Γ Δ) {t : LTy} (i : Idx Δ t) (r : RhsT C Γ t) :
    SubstT C Γ Δ :=
  fun j => if h : i.toNat = j.toNat then .rhs (Idx.ty_eq_of_toNat h ▸ r) else s j

/-- A local pushed, holding `h`. -/
def SubstT.cons {Δ : Ctx} {t : LTy} (s : SubstT C Γ Δ) (h : HeldT C Γ t) : SubstT C Γ (t :: Δ)
  | _, .here => h
  | _, .there j => s j

/-- What one element leaves: a local it sets holds its right-hand side. -/
def UpdElemT.heldOn {Δ : Ctx} (e : UpdElemT C Γ Δ) (s : SubstT C Γ Δ) : SubstT C Γ Δ :=
  @UpdElemT.casesOn C Γ Δ (fun _ => SubstT C Γ Δ) e
    (fun {_} i r => s.set i r) (fun _ => s) (fun _ => s) (fun _ _ => s) (fun _ _ _ => s)
    (fun _ _ => s) (fun _ _ => s) (fun _ => s)

/-- `held` by `match`, its compiled form. -/
def UpdT.heldM : {Δ : Ctx} → UpdT C Γ Δ → SubstT C Γ Δ
  | _, .nil => fun i => .pos i
  | _, .snoc U e => e.heldOn U.heldM
  | _, .decl U _ r => SubstT.cons U.heldM (.rhs r)
  | _, .pop U h => fun j => U.heldM (j.ext h)
  | _, .drop U h => fun j => U.heldM (j.wk h)

/-- What a typed update leaves in each local. -/
@[implemented_by UpdT.heldM]
def UpdT.held {Δ : Ctx} (U : UpdT C Γ Δ) : SubstT C Γ Δ :=
  @UpdT.rec C Γ (fun Δ _ => SubstT C Γ Δ) (fun i => .pos i)
    (fun {_} _ e ih => e.heldOn ih)
    (fun {_} {_} _ _ r ih => SubstT.cons ih (.rhs r))
    (fun {_} {_} _ h ih => fun j => ih (j.ext h))
    (fun {_} {_} _ h ih => fun j => ih (j.wk h)) Δ U

theorem UpdT.held_eq_heldM : {Δ : Ctx} → (U : UpdT C Γ Δ) → {t : LTy} → (i : Idx Δ t) →
    U.held i = U.heldM i
  | _, .nil, _, _ => rfl
  | _, .snoc U e, _, i => by
    cases e with
    | «local» k r =>
      show SubstT.set U.held k r i = SubstT.set U.heldM k r i
      unfold SubstT.set
      split
      · rfl
      · exact UpdT.held_eq_heldM U i
    | _ => exact UpdT.held_eq_heldM U i
  | _, .decl U _ _, _, i => by
    cases i with
    | here => rfl
    | there j => exact UpdT.held_eq_heldM U j
  | _, .pop U h, _, i => UpdT.held_eq_heldM U (i.ext h)
  | _, .drop U h, _, i => UpdT.held_eq_heldM U (i.wk h)

/-- **What a typed update leaves is what its erasure leaves**, erased. -/
theorem UpdT.held_erase : {Δ : Ctx} → (U : UpdT C Γ Δ) → {t : LTy} → (i : Idx Δ t) →
    (U.held i).erase = U.erase.held i
  | _, .nil, _, _ => rfl
  | _, .snoc U e, _, i => by
    cases e with
    | «local» k r =>
      show (SubstT.set U.held k r i).erase = Subst.set U.erase.held k r.erase i
      unfold SubstT.set Subst.set
      by_cases h : k.toNat = i.toNat
      · rw [dif_pos h, dif_pos h]
        obtain rfl := Idx.ty_eq_of_toNat h
        rfl
      · rw [dif_neg h, dif_neg h]
        exact UpdT.held_erase U i
    | _ => exact UpdT.held_erase U i
  | _, .decl U _ r, _, i => by
    cases i with
    | here => rfl
    | there j => exact UpdT.held_erase U j
  | _, .pop U h, _, i => UpdT.held_erase U (i.ext h)
  | _, .drop U h, _, i => UpdT.held_erase U (i.wk h)

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
def UpdElemT.globTM {Δ : Ctx} (σ₀ : State C Γ) :
    UpdElemT C Γ Δ → GlobT C σ₀.H → Option (GlobT C σ₀.H)
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
@[implemented_by UpdElemT.globTM]
def UpdElemT.globT {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElemT C Γ Δ) (g : GlobT C σ₀.H) :
    Option (GlobT C σ₀.H) :=
  @UpdElemT.casesOn C Γ Δ (fun _ => Option (GlobT C σ₀.H)) e
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

theorem UpdElemT.globT_eq_globTM {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElemT C Γ Δ)
    (g : GlobT C σ₀.H) : e.globT σ₀ g = e.globTM σ₀ g := by
  cases e <;> rfl

/-- `globT` by `match`, its compiled form. -/
def UpdT.globTM (σ₀ : State C Γ) : {Δ : Ctx} → UpdT C Γ Δ → Option (GlobT C σ₀.H)
  | _, .nil => some σ₀.globG
  | _, .snoc U e => (U.globTM σ₀).bind (e.globT σ₀)
  | _, .decl U _ r => (U.globTM σ₀).bind fun g => (r.eval σ₀).bind fun _ => some g
  | _, .pop U _ => U.globTM σ₀
  | _, .drop U _ => U.globTM σ₀

/-- **The typed global part a typed update applied in `σ₀` leaves**;
`none` where it halts. -/
@[implemented_by UpdT.globTM]
def UpdT.globT (σ₀ : State C Γ) {Δ : Ctx} (U : UpdT C Γ Δ) : Option (GlobT C σ₀.H) :=
  @UpdT.rec C Γ (fun _ _ => Option (GlobT C σ₀.H)) (some σ₀.globG)
    (fun {_} _ e ih => ih.bind (e.globT σ₀))
    (fun {_} {_} _ _ r ih => ih.bind fun g => (r.eval σ₀).bind fun _ => some g)
    (fun {_} {_} _ _ ih => ih)
    (fun {_} {_} _ _ ih => ih) Δ U

theorem UpdT.globT_eq_globTM (σ₀ : State C Γ) : {Δ : Ctx} → (U : UpdT C Γ Δ) →
    U.globT σ₀ = U.globTM σ₀
  | _, .nil => rfl
  | _, .snoc U e => by
    show (U.globT σ₀).bind _ = (U.globTM σ₀).bind _
    rw [UpdT.globT_eq_globTM σ₀ U]
  | _, .decl U _ r => by
    show (U.globT σ₀).bind _ = (U.globTM σ₀).bind _
    rw [UpdT.globT_eq_globTM σ₀ U]
  | _, .pop U _ => UpdT.globT_eq_globTM σ₀ U
  | _, .drop U _ => UpdT.globT_eq_globTM σ₀ U

/-! ### Exactness and the global part's bridge -/

/-- Where an element is exact: its terms', and a balance written in range
(the untyped one writes any integer). -/
def UpdElemT.Exact {Δ : Ctx} (σ₀ : State C Γ) : UpdElemT C Γ Δ → Prop
  | .local _ r => r.Exact σ₀
  | .storage s => s.Exact σ₀
  | .memory m => m.Exact σ₀
  | .selfBalance op a => a.Exact σ₀ ∧ ∀ amt, a.eval σ₀ = some amt →
      PrimTy.uint.inRange (op.apply σ₀.selfBalance.1 amt.1) = true
  | .net r _ a => r.Exact σ₀ ∧ a.Exact σ₀
  | .pay r a => r.Exact σ₀ ∧ a.Exact σ₀
  | .netMt r a => r.Exact σ₀ ∧ a.Exact σ₀
  | .setBalance a => a.Exact σ₀

/-- Where a typed update is exact: every element and declaration. -/
def UpdT.Exact (σ₀ : State C Γ) : {Δ : Ctx} → UpdT C Γ Δ → Prop
  | _, .nil => True
  | _, .snoc U e => U.Exact σ₀ ∧ e.Exact σ₀
  | _, .decl U _ r => U.Exact σ₀ ∧ r.Exact σ₀
  | _, .pop U _ => U.Exact σ₀
  | _, .drop U _ => U.Exact σ₀

/-- Where a held right-hand side is exact. -/
def HeldT.Exact {t : LTy} (σ₀ : State C Γ) : HeldT C Γ t → Prop
  | .pos _ => True
  | .rhs r => r.Exact σ₀

theorem UpdT.held_exact {σ₀ : State C Γ} : {Δ : Ctx} → (U : UpdT C Γ Δ) → U.Exact σ₀ →
    {t : LTy} → (i : Idx Δ t) → (U.held i).Exact σ₀
  | _, .nil, _, _, _ => trivial
  | _, .snoc U e, h, _, i => by
    cases e with
    | «local» k r =>
      show (SubstT.set U.held k r i).Exact σ₀
      unfold SubstT.set
      by_cases hk : k.toNat = i.toNat
      · rw [dif_pos hk]
        obtain rfl := Idx.ty_eq_of_toNat hk
        exact h.2
      · rw [dif_neg hk]
        exact UpdT.held_exact U h.1 i
    | _ => exact UpdT.held_exact U h.1 i
  | _, .decl U _ r, h, _, i => by
    cases i with
    | here => exact h.2
    | there j => exact UpdT.held_exact U h.1 j
  | _, .pop U hx, h, _, i => UpdT.held_exact U h (i.ext hx)
  | _, .drop U hx, h, _, i => UpdT.held_exact U h (i.wk hx)

private theorem asInt_bind {β : Type} {p : PrimTy} (hp : p ≠ .bool) (a : p.Denote)
    (k : Int → Res β) : ((PrimTy.erase a).asInt >>= k) = k (PrimTy.key a) := by
  cases p with
  | bool => exact absurd rfl hp
  | uint | int => rfl

private theorem uint_nonneg (a : PrimTy.uint.Denote) : ¬ a.1 < 0 := by
  have h := a.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  omega

/-- **An element's bridge**: exact both ways where the element is. -/
theorem UpdElemT.globT_agree {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElemT C Γ Δ) (h : e.Exact σ₀)
    (g : GlobT C σ₀.H) :
    OAgree (fun g' : GlobT C σ₀.H => g'.1.globE) (e.globT σ₀ g) (e.erase.globT σ₀ g.1.globE) := by
  rw [UpdElemT.globT_eq_globTM]
  cases e with
  | «local» _ r =>
    dsimp only [UpdElemT.globTM, UpdElemT.erase, UpdElem.globT]
    exact OAgree.bind (RhsT.eval_agree σ₀ r h) fun _ _ => rfl
  | storage s =>
    dsimp only [UpdElemT.globTM, UpdElemT.erase, UpdElem.globT]
    exact OAgree.bind (TmT.eval_agree σ₀ s h).st fun _ _ => rfl
  | memory m =>
    dsimp only [UpdElemT.globTM, UpdElemT.erase, UpdElem.globT]
    exact OAgree.bind (TmT.eval_agree σ₀ m h).mem fun _ _ => rfl
  | selfBalance op a =>
    dsimp only [UpdElemT.globTM, UpdElemT.erase, UpdElem.globT]
    refine OAgree.bind (TmT.eval_agree σ₀ a h.1).val fun amt ha => ?_
    show OAgree _ _ ((PrimTy.erase amt).asInt >>= _)
    rw [asInt_bind (by decide) amt]
    have hr := h.2 amt ha
    simp only [PrimTy.ofInt?, PrimTy.ofValue?, dif_pos hr, Option.bind_some]
    rfl
  | net r op a =>
    dsimp only [UpdElemT.globTM, UpdElemT.erase, UpdElem.globT]
    refine OAgree.bind (TmT.eval_agree σ₀ r h.1).val fun addr _ => ?_
    show OAgree _ _ ((PrimTy.erase addr).asInt >>= _)
    rw [asInt_bind (by decide) addr]
    refine OAgree.bind (TmT.eval_agree σ₀ a h.2).val fun amt ha => ?_
    show OAgree _ _ ((PrimTy.erase amt).asInt >>= _)
    rw [asInt_bind (by decide) amt]
    rfl
  | pay r a =>
    dsimp only [UpdElemT.globTM, UpdElemT.erase, UpdElem.globT]
    refine OAgree.bind (TmT.eval_agree σ₀ r h.1).val fun addr _ => ?_
    show OAgree _ _ ((PrimTy.erase addr).asInt >>= _)
    rw [asInt_bind (by decide) addr]
    refine OAgree.bind (TmT.eval_agree σ₀ a h.2).val fun amt ha => ?_
    show OAgree _ _ ((PrimTy.erase amt).asInt >>= _)
    rw [asInt_bind (by decide) amt]
    show OAgree _ _ (if amt.1 < 0 then _ else _)
    rw [if_neg (uint_nonneg amt)]
    rfl
  | netMt r a =>
    dsimp only [UpdElemT.globTM, UpdElemT.erase, UpdElem.globT]
    refine OAgree.bind (TmT.eval_agree σ₀ r h.1).val fun addr _ => ?_
    show OAgree _ _ ((PrimTy.erase addr).asInt >>= _)
    rw [asInt_bind (by decide) addr]
    refine OAgree.bind (TmT.eval_agree σ₀ a h.2).val fun amt ha => ?_
    show OAgree _ _ ((PrimTy.erase amt).asInt >>= _)
    rw [asInt_bind (by decide) amt]
    rfl
  | setBalance a =>
    dsimp only [UpdElemT.globTM, UpdElemT.erase, UpdElem.globT]
    refine OAgree.bind (TmT.eval_agree σ₀ a h).val fun amt ha => ?_
    show OAgree _ _ ((PrimTy.erase amt).asInt >>= _)
    rw [asInt_bind (by decide) amt]
    rfl

/-- **The global part's bridge**: a typed update and its erasure compute
the same global part, erased, and halt alike, where the update is exact. -/
theorem UpdT.globT_agree (σ₀ : State C Γ) : {Δ : Ctx} → (U : UpdT C Γ Δ) → U.Exact σ₀ →
    OAgree (fun g : GlobT C σ₀.H => g.1.globE) (U.globT σ₀) (U.erase.globT σ₀)
  | _, .nil, _ => rfl
  | _, .snoc U e, h =>
    OAgree.bind (UpdT.globT_agree σ₀ U h.1) fun g _ => UpdElemT.globT_agree σ₀ e h.2 g
  | _, .decl U _ r, h =>
    OAgree.bind (UpdT.globT_agree σ₀ U h.1) fun _ _ =>
      OAgree.bind (RhsT.eval_agree σ₀ r h.2) fun _ _ => rfl
  | _, .pop U _, h => UpdT.globT_agree σ₀ U h
  | _, .drop U _, h => UpdT.globT_agree σ₀ U h

/-! ## Landing -/

/-- What `U` left in the local `i` of `σ'`, read in `σ₀`: a memory local's
identity is the one `σ'` types in its heap. -/
def HeldT.OK {Δ : Ctx} (σ₀ : State C Γ) (σ' : State C Δ) {t : LTy} (i : Idx Δ t) :
    HeldT C Γ t → Prop
  | .pos j => σ'.getV i = σ₀.getV j
  | .rhs r => r.eval σ₀ = some (σ'.getV i)

/-- **`U` applied in `σ₀` lands on `σ'`**: it leaves the typed global part
`g`, which is `σ'`'s, and in each local of `σ'` what `UpdT.held` says. -/
def UpdT.Lands {Δ : Ctx} (σ₀ : State C Γ) (U : UpdT C Γ Δ) (g : GlobT C σ₀.H)
    (σ' : State C Δ) : Prop :=
  U.globT σ₀ = some g ∧ σ'.glob = g.1 ∧ ∀ {t : LTy} (i : Idx Δ t), HeldT.OK σ₀ σ' i (U.held i)

/-- A landed state's heap typing extends the one the update was applied in:
the global part carries it. -/
theorem UpdT.Lands.prefix {Δ : Ctx} {σ₀ : State C Γ} {U : UpdT C Γ Δ} {g : GlobT C σ₀.H}
    {σ' : State C Δ} (h : U.Lands σ₀ g σ') : σ₀.H <+: σ'.H := by
  have hH : σ'.H = g.1.H := congrArg State.H h.2.1
  rw [hH]
  exact g.2

/-- `p` after `U` applied in `σ₀` under `m`: of every typed state it lands
on, or `m.onHalt` when it halts. -/
def UpdT.afterT {Δ : Ctx} (m : Modality) (σ₀ : State C Γ) (U : UpdT C Γ Δ)
    (p : State C Δ → Prop) : Prop :=
  match U.globT σ₀ with
  | none => m.onHalt
  | some g => ∀ σ' : State C Δ, U.Lands σ₀ g σ' → p σ'

theorem UpdT.afterT_imp {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : UpdT C Γ Δ}
    {p q : State C Δ → Prop} (h : U.afterT m σ₀ p) (hpq : ∀ σ', p σ' → q σ') :
    U.afterT m σ₀ q := by
  unfold UpdT.afterT at h ⊢
  split
  · rename_i he; rw [he] at h; exact h
  · rename_i g hg; rw [hg] at h; exact fun σ' hl => hpq σ' (h σ' hl)

theorem UpdT.afterT.of_lands {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : UpdT C Γ Δ}
    {p : State C Δ → Prop} (h : U.afterT m σ₀ p) {g : GlobT C σ₀.H} {σ' : State C Δ}
    (hl : U.Lands σ₀ g σ') : p σ' := by
  unfold UpdT.afterT at h
  rw [hl.1] at h
  exact h σ' hl

/-! ### The landing's bridges -/

/-- **What a local holds, both ways**, where its right-hand side is exact. -/
theorem HeldT.ok_iff {Δ : Ctx} (σ₀ : State C Γ) (σ' : State C Δ) {t : LTy} (i : Idx Δ t)
    (x : HeldT C Γ t) (hx : x.Exact σ₀) : HeldT.OK σ₀ σ' i x ↔ Held.OKT σ₀ σ' i x.erase := by
  cases x with
  | pos j =>
    show σ'.getV i = σ₀.getV j ↔ σ'.getE i = σ₀.getE j
    rw [State.getE_getV, State.getE_getV]
    exact ⟨fun h => by rw [h], LTy.VDen.erase_injective t⟩
  | rhs r =>
    show r.eval σ₀ = some (σ'.getV i) ↔ r.erase.eval σ₀ = .ok (σ'.getE i)
    rw [State.getE_getV]
    exact OAgree.unique (fun _ _ => LTy.VDen.erase_injective t) (RhsT.eval_agree σ₀ r hx)

/-- **Landing, both ways**: at the typed global part `g`, a typed update
lands on `σ'` exactly where its erasure does, where the update is exact. -/
theorem UpdT.lands_iff {Δ : Ctx} {σ₀ : State C Γ} {U : UpdT C Γ Δ} (hx : U.Exact σ₀)
    (g : GlobT C σ₀.H) (σ' : State C Δ) :
    U.Lands σ₀ g σ' ↔ U.globT σ₀ = some g ∧ σ'.glob = g.1 ∧ U.erase.Lands σ₀ σ'.globE σ' := by
  have hheld : ∀ {t : LTy} (i : Idx Δ t),
      HeldT.OK σ₀ σ' i (U.held i) ↔ Held.OKT σ₀ σ' i (U.erase.held i) := fun i => by
    rw [← UpdT.held_erase]
    exact HeldT.ok_iff σ₀ σ' i _ (UpdT.held_exact U hx i)
  constructor
  · rintro ⟨hg, hσ, hh⟩
    refine ⟨hg, hσ, ?_, rfl, fun i => (hheld i).1 (hh i)⟩
    have ha := UpdT.globT_agree σ₀ U hx
    rw [hg] at ha
    rw [ha]
    show Except.ok g.1.globE = _
    rw [← hσ]
    rfl
  · rintro ⟨hg, hσ, hl⟩
    exact ⟨hg, hσ, fun i => (hheld i).2 (hl.2.2 i)⟩

/-- A typed landing is an erased one. -/
theorem UpdT.Lands.erase {Δ : Ctx} {σ₀ : State C Γ} {U : UpdT C Γ Δ} (hx : U.Exact σ₀)
    {g : GlobT C σ₀.H} {σ' : State C Δ} (h : U.Lands σ₀ g σ') :
    U.erase.Lands σ₀ σ'.globE σ' :=
  ((UpdT.lands_iff hx g σ').1 h).2.2

/-- **`afterT`'s bridge, one way**: the erased clause gives the typed one,
where the update is exact.  Not the converse: the erased landing fixes
`σ'.globE` only, and an object the update allocates erases without its
type (`MObj.erase`: an empty `uint[]` and an empty `bool[]` are both
`.array [] false`), so it admits heap typings the typed global part `g`
does not; the erased clause asks `p` of those states too. -/
theorem UpdT.afterT_of_erase {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : UpdT C Γ Δ}
    (hx : U.Exact σ₀) {p : State C Δ → Prop} (h : U.erase.afterT m σ₀ p) : U.afterT m σ₀ p := by
  have ha := UpdT.globT_agree σ₀ U hx
  unfold UpdT.afterT
  split
  · rename_i hn
    rw [hn] at ha
    obtain ⟨e, he⟩ := ha
    exact h.of_error he
  · rename_i g _
    exact fun σ' hl => h.of_lands (hl.erase hx) hl.prefix

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

/-- The untyped locals. -/
def erase {Δ : Ctx} (ℓ : LocsV C Δ) : Locs C Δ := fun t i => LTy.VDen.erase t (ℓ t i)

theorem set_same {Δ : Ctx} (ℓ : LocsV C Δ) {t : LTy} (i : Idx Δ t) (v : t.VDen C) :
    ℓ.set i v t i = v := by
  unfold LocsV.set
  rw [dif_pos rfl]

theorem set_ne {Δ : Ctx} (ℓ : LocsV C Δ) {t u : LTy} (i : Idx Δ t) (j : Idx Δ u)
    (h : i.toNat ≠ j.toNat) (v : t.VDen C) : ℓ.set i v u j = ℓ u j := by
  unfold LocsV.set
  rw [dif_neg h]

theorem erase_set {Δ : Ctx} (ℓ : LocsV C Δ) {t : LTy} (i : Idx Δ t) (v : t.VDen C) :
    (ℓ.set i v).erase = ℓ.erase.set i (LTy.VDen.erase t v) := by
  funext u j
  by_cases h : i.toNat = j.toNat
  · obtain rfl := Idx.ty_eq_of_toNat h
    obtain rfl := Idx.toNat_inj i j h
    simp only [LocsV.erase, LocsV.set_same, Locs.set_same]
  · simp only [LocsV.erase, LocsV.set_ne ℓ i j h, Locs.set_ne _ i j h]

theorem erase_push {Δ : Ctx} {t : LTy} (ℓ : LocsV C Δ) (v : t.VDen C) :
    (ℓ.push v).erase = ℓ.erase.push (LTy.VDen.erase t v) := by
  funext u j
  cases j <;> rfl

end LocsV

theorem State.locV_erase (σ : State C Γ) : σ.locV.erase = σ.loc := by
  funext t i
  exact (State.getE_getV σ i).symm

/-- `applyV` by `match`, its compiled form. -/
def UpdElemT.applyVM {Δ : Ctx} (σ₀ : State C Γ) :
    UpdElemT C Γ Δ → GlobT C σ₀.H → LocsV C Δ → Option (GlobT C σ₀.H × LocsV C Δ)
  | .local i r, g, ℓ => (r.eval σ₀).bind fun v => some (g, ℓ.set i v)
  | e, g, ℓ => (e.globT σ₀ g).bind fun g' => some (g', ℓ)

/-- One element applied to a typed global part and the locals, its
right-hand sides read in `σ₀`. -/
@[implemented_by UpdElemT.applyVM]
def UpdElemT.applyV {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElemT C Γ Δ) (g : GlobT C σ₀.H)
    (ℓ : LocsV C Δ) : Option (GlobT C σ₀.H × LocsV C Δ) :=
  @UpdElemT.casesOn C Γ Δ (fun _ => Option (GlobT C σ₀.H × LocsV C Δ)) e
    (fun {_} i r => (r.eval σ₀).bind fun v => some (g, ℓ.set i v))
    (fun _ => (e.globT σ₀ g).bind fun g' => some (g', ℓ))
    (fun _ => (e.globT σ₀ g).bind fun g' => some (g', ℓ))
    (fun _ _ => (e.globT σ₀ g).bind fun g' => some (g', ℓ))
    (fun _ _ _ => (e.globT σ₀ g).bind fun g' => some (g', ℓ))
    (fun _ _ => (e.globT σ₀ g).bind fun g' => some (g', ℓ))
    (fun _ _ => (e.globT σ₀ g).bind fun g' => some (g', ℓ))
    (fun _ => (e.globT σ₀ g).bind fun g' => some (g', ℓ))

theorem UpdElemT.applyV_eq_applyVM {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElemT C Γ Δ)
    (g : GlobT C σ₀.H) (ℓ : LocsV C Δ) : e.applyV σ₀ g ℓ = e.applyVM σ₀ g ℓ := by
  cases e <;> rfl

/-- `applyV` by `match`, its compiled form. -/
def UpdT.applyVM (σ₀ : State C Γ) : {Δ : Ctx} → UpdT C Γ Δ →
    Option (GlobT C σ₀.H × LocsV C Δ)
  | _, .nil => some (σ₀.globG, σ₀.locV)
  | _, .snoc U e => (U.applyVM σ₀).bind fun p => e.applyV σ₀ p.1 p.2
  | _, .decl U _ r => (U.applyVM σ₀).bind fun p =>
    (r.eval σ₀).bind fun v => some (p.1, p.2.push v)
  | _, .pop U h => (U.applyVM σ₀).bind fun p => some (p.1, p.2.drop h)
  | _, .drop U h => (U.applyVM σ₀).bind fun p => some (p.1, p.2.thin h)

/-- **What a typed update applied in `σ₀` leaves** (U1, typed): the typed
global part and the locals' values. -/
@[implemented_by UpdT.applyVM]
def UpdT.applyV (σ₀ : State C Γ) {Δ : Ctx} (U : UpdT C Γ Δ) :
    Option (GlobT C σ₀.H × LocsV C Δ) :=
  @UpdT.rec C Γ (fun Δ _ => Option (GlobT C σ₀.H × LocsV C Δ)) (some (σ₀.globG, σ₀.locV))
    (fun {_} _ e ih => ih.bind fun p => e.applyV σ₀ p.1 p.2)
    (fun {_} {_} _ _ r ih => ih.bind fun p => (r.eval σ₀).bind fun v => some (p.1, p.2.push v))
    (fun {_} {_} _ h ih => ih.bind fun p => some (p.1, p.2.drop h))
    (fun {_} {_} _ h ih => ih.bind fun p => some (p.1, p.2.thin h)) Δ U

theorem UpdT.applyV_eq_applyVM (σ₀ : State C Γ) : {Δ : Ctx} → (U : UpdT C Γ Δ) →
    U.applyV σ₀ = U.applyVM σ₀
  | _, .nil => rfl
  | _, .snoc U _ | _, .decl U _ _ | _, .pop U _ | _, .drop U _ => by
    show (U.applyV σ₀).bind _ = (U.applyVM σ₀).bind _
    rw [UpdT.applyV_eq_applyVM σ₀ U]

/-- **The U1 pair's bridge**: a typed update and its erasure compute the
same global part and locals, erased, and halt alike, where it is exact. -/
theorem UpdT.applyV_agree (σ₀ : State C Γ) : {Δ : Ctx} → (U : UpdT C Γ Δ) → U.Exact σ₀ →
    OAgree (fun p : GlobT C σ₀.H × LocsV C Δ => (p.1.1.globE, p.2.erase))
      (U.applyV σ₀) (U.erase.applyV σ₀)
  | _, .nil, _ => by
    show Except.ok _ = Except.ok _
    simp only [State.locV_erase]
    rfl
  | _, .snoc U e, h => by
    refine OAgree.bind (UpdT.applyV_agree σ₀ U h.1) fun p _ => ?_
    rw [UpdElemT.applyV_eq_applyVM]
    cases e with
    | «local» i r =>
      refine OAgree.bind (RhsT.eval_agree σ₀ r h.2) fun v _ => ?_
      show Except.ok _ = Except.ok _
      simp only [LocsV.erase_set]
    | _ =>
      exact OAgree.bind (UpdElemT.globT_agree σ₀ _ h.2 p.1) fun _ _ => rfl
  | _, .decl U _ r, h =>
    OAgree.bind (UpdT.applyV_agree σ₀ U h.1) fun p _ =>
      OAgree.bind (RhsT.eval_agree σ₀ r h.2) fun v _ => by
        show Except.ok _ = Except.ok _
        simp only [LocsV.erase_push]
  | _, .pop U _, h => OAgree.bind (UpdT.applyV_agree σ₀ U h) fun _ _ => rfl
  | _, .drop U _, h => OAgree.bind (UpdT.applyV_agree σ₀ U h) fun _ _ => rfl

/-- What a local holds after an update, as a value: a local of the state
before, or a right-hand side read in it. -/
def HeldT.OKV {t : LTy} (σ₀ : State C Γ) (v : t.VDen C) : HeldT C Γ t → Prop
  | .pos j => v = σ₀.getV j
  | .rhs r => r.eval σ₀ = some v

theorem HeldT.OK_iff_OKV {Δ : Ctx} (σ₀ : State C Γ) (σ' : State C Δ) {t : LTy} (i : Idx Δ t)
    (x : HeldT C Γ t) : HeldT.OK σ₀ σ' i x ↔ HeldT.OKV σ₀ (σ'.getV i) x := by
  cases x <;> exact Iff.rfl

theorem HeldT.OKV.unique {t : LTy} {σ₀ : State C Γ} {v w : t.VDen C} :
    (x : HeldT C Γ t) → HeldT.OKV σ₀ v x → HeldT.OKV σ₀ w x → v = w
  | .pos _, h₁, h₂ => h₁.trans h₂.symm
  | .rhs _, h₁, h₂ => Option.some.inj (h₁.symm.trans h₂)

private theorem UpdElemT.applyV_ok {Δ : Ctx} {σ₀ : State C Γ} (e : UpdElemT C Γ Δ)
    {g g' : GlobT C σ₀.H} {ℓ ℓ' : LocsV C Δ} (h : e.applyV σ₀ g ℓ = some (g', ℓ')) :
    e.globT σ₀ g = some g' ∧
      ((∃ (u : LTy) (i : Idx Δ u) (r : RhsT C Γ u) (v : u.VDen C), e = .local i r ∧
        r.eval σ₀ = some v ∧ ℓ' = ℓ.set i v) ∨ ((∀ (u : LTy) (i : Idx Δ u) (r : RhsT C Γ u),
          e ≠ .local i r) ∧ ℓ' = ℓ)) := by
  rw [UpdElemT.applyV_eq_applyVM] at h
  cases e with
  | «local» i r =>
    simp only [UpdElemT.applyVM, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨v, hv, rfl, rfl⟩ := h
    refine ⟨?_, .inl ⟨_, i, r, v, rfl, hv, rfl⟩⟩
    rw [UpdElemT.globT_eq_globTM]
    simp only [UpdElemT.globTM, hv, Option.bind_some]
  | _ =>
    simp only [UpdElemT.applyVM, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨g₁, hg, rfl, rfl⟩ := h
    exact ⟨hg, .inr ⟨fun _ _ _ he => UpdElemT.noConfusion he, rfl⟩⟩

/-- **What `applyV` computes is the typed global part `globT` computes and,
in each local, what `UpdT.held` says.** -/
theorem UpdT.applyV_ok {σ₀ : State C Γ} : {Δ : Ctx} → (U : UpdT C Γ Δ) →
    {g : GlobT C σ₀.H} → {ℓ : LocsV C Δ} → U.applyV σ₀ = some (g, ℓ) →
    U.globT σ₀ = some g ∧ ∀ {t : LTy} (i : Idx Δ t), HeldT.OKV σ₀ (ℓ t i) (U.held i)
  | _, .nil, g, ℓ, h => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨rfl, fun _ => rfl⟩
  | _, .snoc U e, g, ℓ, h => by
    change (U.applyV σ₀).bind (fun p => e.applyV σ₀ p.1 p.2) = some (g, ℓ) at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨⟨g₁, ℓ₁⟩, hp, h⟩ := h
    obtain ⟨hg₁, hh₁⟩ := UpdT.applyV_ok U hp
    obtain ⟨hg, hl⟩ := UpdElemT.applyV_ok e h
    refine ⟨?_, ?_⟩
    · show (U.globT σ₀).bind (e.globT σ₀) = some g
      rw [hg₁]
      exact hg
    · intro t i
      rcases hl with ⟨u, k, r, v, rfl, hv, rfl⟩ | ⟨hne, rfl⟩
      · show HeldT.OKV σ₀ _ (SubstT.set U.held k r i)
        unfold SubstT.set
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
      · have hheld : (UpdT.snoc U e).held i = U.held i := by
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
    obtain ⟨hg₁, hh₁⟩ := UpdT.applyV_ok U hp
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
    obtain ⟨hg₁, hh₁⟩ := UpdT.applyV_ok U hp
    exact ⟨hg₁, fun i => hh₁ (i.ext hx)⟩
  | _, .drop U hx, g, ℓ, h => by
    change (U.applyV σ₀).bind (fun p => some (p.1, p.2.thin hx)) = some (g, ℓ) at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨g₁, ℓ₁⟩, hp, rfl, rfl⟩ := h
    obtain ⟨hg₁, hh₁⟩ := UpdT.applyV_ok U hp
    exact ⟨hg₁, fun i => hh₁ (i.wk hx)⟩

/-- Where `globT` returns, so does `applyV`. -/
theorem UpdT.applyV_of_globT {σ₀ : State C Γ} : {Δ : Ctx} → (U : UpdT C Γ Δ) →
    {g : GlobT C σ₀.H} → U.globT σ₀ = some g → ∃ ℓ, U.applyV σ₀ = some (g, ℓ)
  | _, .nil, g, h => by
    cases h
    exact ⟨_, rfl⟩
  | _, .snoc U e, g, h => by
    change (U.globT σ₀).bind (e.globT σ₀) = some g at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨g₁, hg₁, h⟩ := h
    obtain ⟨ℓ₁, hℓ₁⟩ := UpdT.applyV_of_globT U hg₁
    show ∃ ℓ, (U.applyV σ₀).bind (fun p => e.applyV σ₀ p.1 p.2) = _
    rw [hℓ₁, Option.bind_some, UpdElemT.applyV_eq_applyVM]
    rw [UpdElemT.globT_eq_globTM] at h
    cases e with
    | «local» i r =>
      simp only [UpdElemT.globTM, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨v, hv, rfl⟩ := h
      exact ⟨ℓ₁.set i v, by simp only [UpdElemT.applyVM, hv, Option.bind_some]⟩
    | _ =>
      rw [← UpdElemT.globT_eq_globTM] at h
      exact ⟨ℓ₁, by simp only [UpdElemT.applyVM, h, Option.bind_some]⟩
  | _, .decl U _ r, g, h => by
    change (U.globT σ₀).bind (fun g => (r.eval σ₀).bind fun _ => some g) = some g at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨g₁, hg₁, v, hv, rfl⟩ := h
    obtain ⟨ℓ₁, hℓ₁⟩ := UpdT.applyV_of_globT U hg₁
    exact ⟨_, by
      show (U.applyV σ₀).bind (fun p => (r.eval σ₀).bind fun v => some (p.1, p.2.push v)) = _
      rw [hℓ₁, Option.bind_some, hv, Option.bind_some]⟩
  | _, .pop U hx, g, h => by
    obtain ⟨ℓ₁, hℓ₁⟩ := UpdT.applyV_of_globT (σ₀ := σ₀) U h
    exact ⟨_, by
      show (U.applyV σ₀).bind (fun p => some (p.1, p.2.drop hx)) = _
      rw [hℓ₁, Option.bind_some]⟩
  | _, .drop U hx, g, h => by
    obtain ⟨ℓ₁, hℓ₁⟩ := UpdT.applyV_of_globT (σ₀ := σ₀) U h
    exact ⟨_, by
      show (U.applyV σ₀).bind (fun p => some (p.1, p.2.thin hx)) = _
      rw [hℓ₁, Option.bind_some]⟩

/-- **Landing, computed**: a typed update lands on `σ'` exactly where
`applyV` returns `σ'`'s global part and locals. -/
theorem UpdT.lands_iff_applyV {Δ : Ctx} {σ₀ : State C Γ} {U : UpdT C Γ Δ} {g : GlobT C σ₀.H}
    {σ' : State C Δ} : U.Lands σ₀ g σ' ↔
      ∃ ℓ, U.applyV σ₀ = some (g, ℓ) ∧ σ'.glob = g.1 ∧
        ∀ {t : LTy} (i : Idx Δ t), σ'.getV i = ℓ t i := by
  constructor
  · rintro ⟨hg, hσ, hh⟩
    obtain ⟨ℓ, hℓ⟩ := UpdT.applyV_of_globT U hg
    refine ⟨ℓ, hℓ, hσ, fun i => ?_⟩
    exact HeldT.OKV.unique _ ((HeldT.OK_iff_OKV _ _ _ _).1 (hh i)) ((UpdT.applyV_ok U hℓ).2 i)
  · rintro ⟨ℓ, hℓ, hσ, he⟩
    obtain ⟨hg, hh⟩ := UpdT.applyV_ok U hℓ
    refine ⟨hg, hσ, fun i => (HeldT.OK_iff_OKV _ _ _ _).2 ?_⟩
    rw [he i]
    exact hh i

/-! ## `holds`' update clause over a typed update -/

/-- `holds σ (.upd m U φ)` for a typed update: `φ` of every typed state it
lands on, `m.onHalt` where it halts (beside `holds`' clause, which reads
`Upd.afterT`). -/
def holdsUpdT {Δ : Ctx} (m : Modality) (σ : State C Γ) (U : UpdT C Γ Δ) (φ : Fml C Δ) : Prop :=
  U.afterT m σ (holds · φ)

/-- **The clause's bridge, one way**: `holds`' clause on the erased update
gives the typed one, where the update is exact (`UpdT.afterT_of_erase`). -/
theorem holdsUpdT_of_holds {Δ : Ctx} {m : Modality} {σ : State C Γ} {U : UpdT C Γ Δ}
    {φ : Fml C Δ} (hx : U.Exact σ) (h : holds σ (.upd m U.erase φ)) : holdsUpdT m σ U φ :=
  UpdT.afterT_of_erase hx h

/-! ## A literal -/

/-- `{storage := save(storage, alice.age, sval(1))}`, by hand. -/
def UpdT.aliceAgeWrite : UpdT StandardExample [] [] :=
  .snoc .nil (.storage (.app3 .save (.app0 .storage) TmT.aliceAge (.app1 .sval (.app0 (.lit ⟨1, rfl⟩)))))

/-- It returns in the initial state, and its global part reads `1` at
`alice.age`, by the kernel. -/
example : ((UpdT.aliceAgeWrite.globT (State.init StandardExample)).bind fun g =>
    ((TmT.app2 .find (.app0 .storage) TmT.aliceAge : TmT StandardExample [] (.val .uint)).eval
      g.1).map (·.1)) = some 1 := by
  decide +kernel

end Solidity
