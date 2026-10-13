import Solidity.Calculus.Step
import Solidity.Typing.Soundness
import Solidity.Semantics.RunFrame
import Solidity.Theory.Bridge.Denote

/-!
# Terms and updates read in a state; where an update lands

What `holds` (`Calculus/Logic.lean`) reads a term and an update by, on the
typed state with nothing erased (`docs/intrinsic.md`, W9.8.2 and W9.8.3).

* A term: `Tm.eval` (`Calculus/TermEval.lean`), and `Tm.denote`, its reading
  in the typed Theory (`Theory/Bridge/Denote.lean`'s symbols; a local by its
  position, its value read as its observations), which an equation reads; the bridge
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
  | .kint => Int

namespace LTy

/-- A typed local's value, its memory reference's identity. -/
def VDen.ofT {H : HTy} : (t : LTy) → t.TDenote C H → t.VDen C
  | .val _, v => v
  | .alias _, a => a
  | .mem _, r => (r : Option (HRef H _)).map (·.id)
  | .old, w => w
  | .oldNet, l => l
  | .kint, n => n

end LTy

variable {Γ : Ctx}

/-- A local's typed value, its memory reference's identity. -/
abbrev State.getV (σ : State C Γ) {t : LTy} (i : Idx Γ t) : t.VDen C :=
  LTy.VDen.ofT t (TEnv.get i σ.env)


/-! ## A term in the Theory -/

/-- **A term in the Theory**, read in the typed state `σ`: a local's value
read as its observations, a symbol by `OpN.denote` over the global part
(`Theory/Bridge/Denote.lean`).  What an equation reads (`holds`). -/
def Tm.denote (σ : State C Γ) : {s : Srt} → Tm C Γ s → s.TDen C
  | _, .pvV i => some (TEnv.get i σ.env)
  | _, .pvP i => match (TEnv.get i σ.env : Option (SRef C _)) with
    | some r => .ref r
    | none => .dangling _ .nil
  | _, .pvS i => Storage.obs (TEnv.get i σ.env : Storage C)
  | _, .pvI _ => ()
  | _, .netOf i a => (a.denote σ).map fun n =>
    (lookupBy n.1 (TEnv.get i σ.env : List (Int × Int))).getD 0
  | _, .app0 o => o.denote σ.glob
  | _, .app1 o a => o.denote σ.glob (a.denote σ)
  | _, .app2 o a b => o.denote σ.glob (a.eval σ) (b.eval σ) (a.denote σ) (b.denote σ)
  | _, .app3 o a b c => o.denote (a.denote σ) (b.denote σ) (c.denote σ)
  | _, .pvZ i => some (TEnv.get i σ.env)

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
  | _, .pvS _ => by intro τ h; cases h; rfl
  | _, .pvI _ => by intro _ _; trivial
  | _, .netOf i a => by
    intro x h
    rw [Tm.eval_eq_evalM] at h
    simp only [Tm.evalM, Option.bind_eq_some_iff] at h
    obtain ⟨n, hn, h⟩ := h
    rw [← Tm.eval_eq_evalM] at hn
    have ha : a.denote σ = some n := Tm.denote_eval σ a n hn
    simp only [Tm.netOfT, Option.some.injEq] at h
    subst h
    simp only [Srt.Bridge, Tm.denote, ha, Option.map_some]
  | _, .app0 o => Op0.denote_eval σ.glob o
  | _, .app1 o a => Op1.denote_eval σ.glob o (Tm.denote_eval σ a)
  | _, .app2 o a b => Op2.denote_eval σ.glob o (Tm.denote_eval σ a) (Tm.denote_eval σ b)
  | _, .app3 o a b c =>
    Op3.denote_eval σ.glob o (Tm.denote_eval σ a) (Tm.denote_eval σ b) (Tm.denote_eval σ c)
  | _, .pvZ _ => by intro x h; cases h; rfl

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
  | _, .zint t => t.eval σ₀

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
    (fun x => x.eval σ₀)

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

/-! ## Exhaustion

A push onto `2^256 - 1` elements (`Storage.full`) is out of gas in the run
(`TRun.push`, decision 15), and both modalities accept it.  The update a
push rule leaves reads it alike: a push symbol at the top of a storage
element, its storage, array and value returning and the array full, halts
the update by exhaustion (`Upd.exh`), not by a revert, and `afterT` accepts
it under the diamond too (W9.8.5). -/

/-- A full array: the push the run is out of gas at returns nothing. -/
theorem Storage.push_of_full {E : Ty} {st : Storage C} {r : SRef C (.ref (.array E))}
    (h : st.full r = true) (val : SVal E → Option (SVal E)) : st.push r val = none := by
  cases hp : st.push r val with
  | none => rfl
  | some _ => rw [Storage.full_of_push hp] at h; cases h

theorem Storage.pushPlace_of_full {E : Ty} {st : Storage C} {r : SRef C (.ref (.array E))}
    (h : st.full r = true) : st.pushPlace r = none := by
  cases hp : st.pushPlace r with
  | none => rfl
  | some _ => rw [Storage.full_of_pushPlace hp] at h; cases h

/-- A binary symbol out of gas on its arguments: `pushSlot` or `extend` at a
full array. -/
def Op2.exhB {H : HTy} {a b s : Srt} :
    Op2 C a b s → Option (a.Den C H) → Option (b.Den C H) → Bool
  | .pushSlot, some w, some q => w.full q
  | .extend, some w, some q => w.full q
  | _, _, _ => false

/-- A ternary symbol out of gas on its arguments: `push` at a full array,
its value returning. -/
def Op3.exhB {H : HTy} {a b c s : Srt} :
    Op3 C a b c s → Option (a.Den C H) → Option (b.Den C H) → Option (c.Den C H) → Bool
  | .push, some w, some q, some _ => w.full q
  | _, _, _, _ => false

/-- **A term out of gas** in `σ`: a push symbol at a full array, its
arguments returning, or a term that returns nothing because an argument is
out of gas, its other arguments returning (they are read first, and the
run is out of gas at the push before anything reads what it would leave). -/
def Tm.exhB (σ : State C Γ) : {s : Srt} → Tm C Γ s → Bool
  | _, .netOf i a => ((Tm.netOf i a).eval σ).isNone && a.exhB σ
  | _, .app1 o x => ((Tm.app1 o x).eval σ).isNone && x.exhB σ
  | _, .app2 o x y => o.exhB (x.eval σ) (y.eval σ) ||
      (((Tm.app2 o x y).eval σ).isNone &&
        ((x.exhB σ && (y.eval σ).isSome) || (y.exhB σ && (x.eval σ).isSome)))
  | _, .app3 o x y z => o.exhB (x.eval σ) (y.eval σ) (z.eval σ) ||
      (((Tm.app3 o x y z).eval σ).isNone &&
        ((x.exhB σ && (y.eval σ).isSome && (z.eval σ).isSome) ||
          (y.exhB σ && (x.eval σ).isSome && (z.eval σ).isSome) ||
          (z.exhB σ && (x.eval σ).isSome && (y.eval σ).isSome)))
  | _, _ => false

theorem Op2.eval_of_exhB (g : State C []) {a b s : Srt} (o : Op2 C a b s)
    (x : Option (a.Den C g.H)) (y : Option (b.Den C g.H)) (h : o.exhB x y = true) :
    o.eval g x y = none := by
  rw [Op2.eval_eq_evalM]
  revert h
  cases o <;> cases x <;> cases y <;>
    simp only [Op2.exhB, Bool.false_eq_true, false_implies, Op2.evalM, Option.bind_eq_bind,
      Option.bind_none, Option.bind_some]
  · exact fun hf => Storage.push_of_full hf some
  · exact fun hf => by rw [Storage.pushPlace_of_full hf, Option.bind_none]

theorem Op3.eval_of_exhB (g : State C []) {a b c s : Srt} (o : Op3 C a b c s)
    (x : Option (a.Den C g.H)) (y : Option (b.Den C g.H)) (z : Option (c.Den C g.H))
    (h : o.exhB x y z = true) : o.eval g x y z = none := by
  rw [Op3.eval_eq_evalM]
  revert h
  cases o <;> cases x <;> cases y <;> cases z <;>
    simp only [Op3.exhB, Bool.false_eq_true, false_implies, Op3.evalM, Option.bind_eq_bind,
      Option.bind_none, Option.bind_some]
  exact fun hf => Storage.push_of_full hf _

/-- A term out of gas returns nothing. -/
theorem Tm.eval_of_exhB (σ : State C Γ) {s : Srt} : (t : Tm C Γ s) → t.exhB σ = true →
    t.eval σ = none
  | .app2 o x y, h => by
    simp only [Tm.exhB, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h, -⟩
    · exact Op2.eval_of_exhB σ.glob o _ _ h
    · exact Option.isNone_iff_eq_none.1 h
  | .app3 o x y z, h => by
    simp only [Tm.exhB, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h, -⟩
    · exact Op3.eval_of_exhB σ.glob o _ _ _ h
    · exact Option.isNone_iff_eq_none.1 h
  | .netOf _ _, h | .app1 _ _, h => by
    simp only [Tm.exhB, Bool.and_eq_true] at h
    exact Option.isNone_iff_eq_none.1 h.1
  | .pvV _, h | .pvP _, h | .pvS _, h | .pvI _, h | .app0 _, h | .pvZ _, h => by
    simp only [Tm.exhB, Bool.false_eq_true] at h

/-- A term that returns is not out of gas. -/
theorem Tm.exhB_of_eval (σ : State C Γ) {k : Srt} (t : Tm C Γ k) {v : k.Den C σ.H}
    (h : t.eval σ = some v) : t.exhB σ = false := by
  cases hx : t.exhB σ with
  | false => rfl
  | true => rw [Tm.eval_of_exhB σ t hx] at h; cases h

/-- No push symbol anywhere in the term. -/
def Op2.pushFree {a b s : Srt} : Op2 C a b s → Bool
  | .pushSlot | .extend => false
  | _ => true

def Op3.pushFree {a b c s : Srt} : Op3 C a b c s → Bool
  | .push => false
  | _ => true

/-- A term with no push symbol: it is never out of gas. -/
def Tm.pushFree : {s : Srt} → Tm C Γ s → Bool
  | _, .netOf _ a => a.pushFree
  | _, .app1 _ x => x.pushFree
  | _, .app2 o x y => o.pushFree && x.pushFree && y.pushFree
  | _, .app3 o x y z => o.pushFree && x.pushFree && y.pushFree && z.pushFree
  | _, _ => true

theorem Op2.exhB_of_pushFree {H : HTy} {a b s : Srt} {o : Op2 C a b s} (h : o.pushFree = true)
    (x : Option (a.Den C H)) (y : Option (b.Den C H)) : o.exhB x y = false := by
  cases o <;> first | rfl | exact absurd h Bool.false_ne_true

theorem Op3.exhB_of_pushFree {H : HTy} {a b c s : Srt} {o : Op3 C a b c s} (h : o.pushFree = true)
    (x : Option (a.Den C H)) (y : Option (b.Den C H)) (z : Option (c.Den C H)) :
    o.exhB x y z = false := by
  cases o <;> first | rfl | exact absurd h Bool.false_ne_true

theorem Tm.exhB_of_pushFree (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) → t.pushFree = true →
    t.exhB σ = false
  | _, .netOf _ a, h => by
    simp only [Tm.pushFree] at h
    simp only [Tm.exhB, Tm.exhB_of_pushFree σ a h, Bool.and_false]
  | _, .app1 _ x, h => by
    simp only [Tm.pushFree] at h
    simp only [Tm.exhB, Tm.exhB_of_pushFree σ x h, Bool.and_false]
  | _, .app2 o x y, h => by
    simp only [Tm.pushFree, Bool.and_eq_true] at h
    simp only [Tm.exhB, Op2.exhB_of_pushFree h.1.1, Tm.exhB_of_pushFree σ x h.1.2,
      Tm.exhB_of_pushFree σ y h.2, Bool.false_and, Bool.or_false, Bool.and_false]
  | _, .app3 o x y z, h => by
    simp only [Tm.pushFree, Bool.and_eq_true] at h
    simp only [Tm.exhB, Op3.exhB_of_pushFree h.1.1.1, Tm.exhB_of_pushFree σ x h.1.1.2,
      Tm.exhB_of_pushFree σ y h.1.2, Tm.exhB_of_pushFree σ z h.2, Bool.false_and,
      Bool.or_false, Bool.and_false]
  | _, .pvV _, _ | _, .pvP _, _ | _, .pvS _, _ | _, .pvI _, _ | _, .app0 _, _
  | _, .pvZ _, _ => rfl

/-! ### The arms' terms push nothing -/

theorem Tm.castV_pushFree {p q : PrimTy} (h : p = q) (t : Tm C Γ (.val p)) :
    (Tm.castV h t).pushFree = t.pushFree := by
  subst h; rfl

theorem Simple.lower_pushFree {p : PrimTy} (s : Simple C Γ p) : s.lower.pushFree = true := by
  cases s with
  | env k hp => simp only [Simple.lower, Tm.castV_pushFree]; rfl
  | _ => rfl

theorem Tm.keyAt_pushFree (k : PrimTy) (t : Tm C Γ (.val k)) :
    (Tm.keyAt k t).pushFree = t.pushFree := by
  cases k <;> simp only [Tm.keyAt, Tm.pushFree, Op3.pushFree, Bool.and_true, Bool.true_and]

theorem Tm.mread_pushFree (T : Ty) (a : Tm C Γ (.addr T)) :
    (Tm.mread T a).pushFree = a.pushFree := by
  cases T <;> simp only [Tm.mread, Tm.pushFree, Op2.pushFree, Bool.true_and]

mutual

theorem SPath.lower_pushFree : {T : Ty} → (b : SPath C Γ T) → b.lower.pushFree = true
  | _, .alias _ => rfl
  | _, .loc l => by simp only [SPath.lower, Loc.lower_pushFree l]

theorem Loc.lower_pushFree : {T : Ty} → (l : Loc C Γ T) → l.lower.pushFree = true
  | _, .root _ _ => rfl
  | _, .field b _ _ => by simp only [Loc.lower, Tm.pushFree, SPath.lower_pushFree b]
  | _, .index (k := k) _ b i => by
    simp only [Loc.lower, Tm.pushFree, Op2.pushFree, SPath.lower_pushFree b, Tm.keyAt_pushFree,
      Val.lower_pushFree i, Bool.and_self]

theorem MPath.lower_pushFree : {T : Ty} → (b : MPath C Γ T) → b.lower.pushFree = true
  | _, .var _ _ => rfl
  | _, .loc l => by simp only [MPath.lower, Tm.mread_pushFree, MLoc.lower_pushFree l]

theorem MLoc.lower_pushFree : {T : Ty} → (l : MLoc C Γ T) → l.lower.pushFree = true
  | _, .field b _ _ => by simp only [MLoc.lower, Tm.pushFree, MPath.lower_pushFree b]
  | _, .index _ b i => by
    simp only [MLoc.lower, Tm.pushFree, Op2.pushFree, MPath.lower_pushFree b,
      Val.lower_pushFree i, Bool.and_self]

theorem Val.lower_pushFree : {p : PrimTy} → (v : Val C Γ p) → v.lower.pushFree = true
  | _, .simple s => Simple.lower_pushFree s
  | _, .read l => by
    simp only [Val.lower, Tm.pushFree, Op2.pushFree, Loc.lower_pushFree l, Bool.and_self]
  | _, .binop _ _ hq a b => by
    simp only [Val.lower, Tm.castV_pushFree, Tm.pushFree, Op2.pushFree, Val.lower_pushFree a,
      Val.lower_pushFree b, Bool.and_self]
  | _, .unop _ _ hq a => by
    simp only [Val.lower, Tm.castV_pushFree, Tm.pushFree, Val.lower_pushFree a]
  | _, .ternary c a b => by
    simp only [Val.lower, Tm.pushFree, Op3.pushFree, Val.lower_pushFree c, Val.lower_pushFree a,
      Val.lower_pushFree b, Bool.and_self]
  | _, .readMem l => by
    simp only [Val.lower, Tm.pushFree, Op2.pushFree, MLoc.lower_pushFree l, Bool.and_self]
  | _, .len b _ => by
    simp only [Val.lower, Tm.castV_pushFree, Tm.pushFree, Op2.pushFree, SPath.lower_pushFree b,
      Bool.and_self]
  | _, .mlen b _ => by
    simp only [Val.lower, Tm.castV_pushFree, Tm.pushFree, Op2.pushFree, MPath.lower_pushFree b,
      Bool.and_self]

end

theorem Src.lower_pushFree {T : Ty} (r : Src C Γ T) : r.lower.pushFree = true := by
  cases r with
  | val v => simp only [Src.lower, Tm.pushFree, Val.lower_pushFree v]
  | copy p _ =>
    simp only [Src.lower, Tm.pushFree, Op2.pushFree, SPath.lower_pushFree p, Bool.and_self]

theorem MSrc.lower_pushFree {T : Ty} (r : MSrc C Γ T) : r.lower.pushFree = true := by
  cases r with
  | val v => simp only [MSrc.lower, Tm.pushFree, Val.lower_pushFree v]
  | ref p => simp only [MSrc.lower, Tm.pushFree, MPath.lower_pushFree p]

theorem OpLoc.cur_pushFree {p : PrimTy} (l : OpLoc C Γ p) : l.cur.pushFree = true := by
  cases l <;> first | rfl | exact Val.lower_pushFree _

theorem Tm.one_pushFree (p : PrimTy) (hp : p.isNumeric = true) :
    (Tm.one (Γ := Γ) (C := C) p hp).pushFree = true := rfl

theorem OpLoc.op_pushFree {p : PrimTy} (l : OpLoc C Γ p) (op : BinOp)
    (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true) (t : Tm C Γ (.val p)) :
    (l.op op hop hp t).pushFree = t.pushFree := by
  simp only [OpLoc.op, Tm.castV_pushFree, Tm.pushFree, Op2.pushFree, OpLoc.cur_pushFree,
    Bool.true_and]

theorem Tm.bumped_pushFree (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true)
    (t : Tm C Γ (.val p)) : (Tm.bumped op hp t).pushFree = t.pushFree := by
  unfold Tm.bumped
  split
  · simp only [Tm.castV_pushFree, Tm.pushFree, Op2.pushFree, Tm.one_pushFree, Bool.true_and,
      Bool.and_true]
  · rfl

/-- A right-hand side with no push symbol. -/
def Rhs.pushFree {t : LTy} : Rhs C Γ t → Bool
  | .val t => t.pushFree
  | .path p => p.pushFree
  | .mref i => i.pushFree
  | .store x => x.pushFree
  | .zint x => x.pushFree
  | _ => true

/-- An element with no push symbol. -/
def UpdElem.pushFree {Δ : Ctx} : UpdElem C Γ Δ → Bool
  | .local _ r => r.pushFree
  | .storage s | .memory s => s.pushFree
  | .selfBalance _ a | .setBalance a => a.pushFree
  | .net r _ a | .pay r a | .netMt r a => r.pushFree && a.pushFree

/-- An update with no push symbol: never out of gas. -/
def Upd.pushFree : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U e => Upd.pushFree U && e.pushFree
  | _, .decl U _ r => Upd.pushFree U && r.pushFree
  | _, .pop U _ | _, .drop U _ => Upd.pushFree U

theorem UpdElem.clearMem_pushFree (T : Ty) (a : Tm C Γ (.addr T)) (h : T.mapFree = true) :
    (UpdElem.clearMem T a h).pushFree = a.pushFree := by
  cases T <;> simp only [UpdElem.clearMem, UpdElem.pushFree, Tm.pushFree, Op3.pushFree,
    Bool.true_and, Bool.and_true]

theorem OpLoc.set_pushFree {p : PrimTy} (l : OpLoc C Γ p) (t : Tm C Γ (.val p)) :
    (l.set t).pushFree = t.pushFree := by
  cases l <;>
    simp only [OpLoc.set, UpdElem.pushFree, Rhs.pushFree, Tm.pushFree, Op3.pushFree,
      Loc.lower_pushFree, MLoc.lower_pushFree, Bool.true_and, Bool.and_true]

/-- What a local is set to, out of gas. -/
def Rhs.exhB (σ₀ : State C Γ) {t : LTy} : Rhs C Γ t → Bool
  | .val t => t.exhB σ₀
  | .path p => p.exhB σ₀
  | .mref i => i.exhB σ₀
  | .store x => x.exhB σ₀
  | .zint x => x.exhB σ₀
  | _ => false

/-- **An element out of gas**: one of its terms is, the others returning. -/
def UpdElem.exhB {Δ : Ctx} (σ₀ : State C Γ) : UpdElem C Γ Δ → Bool
  | .local _ r => r.exhB σ₀
  | .storage s => s.exhB σ₀
  | .memory m => m.exhB σ₀
  | .selfBalance _ a | .setBalance a => a.exhB σ₀
  | .net r _ a | .pay r a | .netMt r a =>
    (r.exhB σ₀ && (a.eval σ₀).isSome) || (a.exhB σ₀ && (r.eval σ₀).isSome)

/-- An element returns: its right-hand sides return, and a funds update
stays in range.  Read in `σ₀` alone (`UpdElem.globT_isSome`). -/
def UpdElem.okB {Δ : Ctx} (σ₀ : State C Γ) : UpdElem C Γ Δ → Bool
  | .local _ r => (r.eval σ₀).isSome
  | .storage s => (s.eval σ₀).isSome
  | .memory m => (m.eval σ₀).isSome
  | .selfBalance op a => ((a.eval σ₀).bind fun amt =>
      PrimTy.uint.ofInt? (op.apply σ₀.selfBalance.1 amt.1)).isSome
  | .net r _ a | .pay r a | .netMt r a => (r.eval σ₀).isSome && (a.eval σ₀).isSome
  | .setBalance a => (a.eval σ₀).isSome

theorem UpdElem.globT_isSome {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElem C Γ Δ)
    (g : GlobT C σ₀.H) : (e.globT σ₀ g).isSome = e.okB σ₀ := by
  rw [UpdElem.globT_eq_globTM]
  cases e with
  | selfBalance op a =>
    simp only [UpdElem.globTM, UpdElem.okB]
    cases a.eval σ₀ with
    | none => rfl
    | some amt =>
      simp only [Option.bind_some]
      cases PrimTy.uint.ofInt? (op.apply σ₀.selfBalance.1 amt.1) <;> rfl
  | «local» _ r =>
    simp only [UpdElem.globTM, UpdElem.okB]; cases r.eval σ₀ <;> rfl
  | storage x | memory x | setBalance x =>
    simp only [UpdElem.globTM, UpdElem.okB]; cases x.eval σ₀ <;> rfl
  | net r _ a | pay r a | netMt r a =>
    simp only [UpdElem.globTM, UpdElem.okB]; cases r.eval σ₀ <;> cases a.eval σ₀ <;> rfl

/-- An element out of gas does not return. -/
theorem Rhs.eval_of_exhB (σ₀ : State C Γ) {t : LTy} (r : Rhs C Γ t) (h : r.exhB σ₀ = true) :
    r.eval σ₀ = none := by
  rw [Rhs.eval_eq_evalM]
  cases r <;> simp only [Rhs.exhB, Bool.false_eq_true] at h <;>
    simp only [Rhs.evalM, Tm.eval_of_exhB σ₀ _ h, Option.bind_none]

theorem Rhs.exhB_of_eval (σ₀ : State C Γ) {t : LTy} (r : Rhs C Γ t) {v : t.VDen C}
    (h : r.eval σ₀ = some v) : r.exhB σ₀ = false := by
  cases hx : r.exhB σ₀ with
  | false => rfl
  | true => rw [Rhs.eval_of_exhB σ₀ r hx] at h; cases h

theorem UpdElem.okB_of_exhB {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElem C Γ Δ)
    (h : e.exhB σ₀ = true) : e.okB σ₀ = false := by
  cases e with
  | «local» _ r => simp only [UpdElem.okB, Rhs.eval_of_exhB σ₀ r h, Option.isSome_none]
  | storage s | memory s | setBalance s =>
    simp only [UpdElem.okB, Tm.eval_of_exhB σ₀ s h, Option.isSome_none]
  | selfBalance _ a =>
    simp only [UpdElem.okB, Tm.eval_of_exhB σ₀ a h, Option.bind_none, Option.isSome_none]
  | net r _ a | pay r a | netMt r a =>
    simp only [UpdElem.exhB, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;>
      simp only [UpdElem.okB, Tm.eval_of_exhB σ₀ _ h, Option.isSome_none, Bool.false_and,
        Bool.and_false]

/-- An element of the update is out of gas. -/
def Upd.exhAny (σ₀ : State C Γ) : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => false
  | _, .snoc U e => Upd.exhAny σ₀ U || e.exhB σ₀
  | _, .decl U _ r => Upd.exhAny σ₀ U || r.exhB σ₀
  | _, .pop U _ | _, .drop U _ => Upd.exhAny σ₀ U

/-- Every element of the update returns or is out of gas: none reverts. -/
def Upd.exhOk (σ₀ : State C Γ) : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U e => Upd.exhOk σ₀ U && (e.okB σ₀ || e.exhB σ₀)
  | _, .decl U _ r => Upd.exhOk σ₀ U && ((r.eval σ₀).isSome || r.exhB σ₀)
  | _, .pop U _ | _, .drop U _ => Upd.exhOk σ₀ U

/-- **An update out of gas** in `σ₀`: an element is a push at a full array,
and no element reverts.  The elements read `σ₀` alone, so the order they
come in does not matter, as for the run's halt in an update rule's
statement, which has one push. -/
def Upd.exh (σ₀ : State C Γ) {Δ : Ctx} (U : Upd C Γ Δ) : Bool :=
  U.exhAny σ₀ && U.exhOk σ₀

/-- An update with an element out of gas halts. -/
theorem Upd.globT_of_exhAny (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    U.exhAny σ₀ = true → U.globT σ₀ = none
  | _, .nil, h => by cases h
  | _, .snoc U e, h => by
    show (U.globT σ₀).bind (e.globT σ₀) = none
    simp only [Upd.exhAny, Bool.or_eq_true] at h
    rcases h with h | he
    · rw [Upd.globT_of_exhAny σ₀ U h, Option.bind_none]
    · cases U.globT σ₀ with
      | none => rfl
      | some g =>
        rw [Option.bind_some]
        have hs := UpdElem.globT_isSome σ₀ e g
        rw [UpdElem.okB_of_exhB σ₀ e he] at hs
        exact Option.not_isSome_iff_eq_none.1 (by rw [hs]; exact Bool.false_ne_true)
  | _, .decl U _ r, h => by
    show (U.globT σ₀).bind _ = none
    simp only [Upd.exhAny, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Upd.globT_of_exhAny σ₀ U h, Option.bind_none]
    · cases U.globT σ₀ with
      | none => rfl
      | some g => simp only [Option.bind_some, Rhs.eval_of_exhB σ₀ r h, Option.bind_none]
  | _, .pop U _, h => Upd.globT_of_exhAny σ₀ U h
  | _, .drop U _, h => Upd.globT_of_exhAny σ₀ U h

/-- An update that lands has no element out of gas. -/
theorem Upd.exhAny_of_globT {Δ : Ctx} {σ₀ : State C Γ} {U : Upd C Γ Δ} {g : GlobT C σ₀.H}
    (h : U.globT σ₀ = some g) : U.exhAny σ₀ = false := by
  cases hx : U.exhAny σ₀ with
  | false => rfl
  | true => rw [Upd.globT_of_exhAny σ₀ U hx] at h; cases h

/-- An update none of whose elements reverts, that halts, has one out of
gas. -/
theorem Upd.exhAny_of_none (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    U.exhOk σ₀ = true → U.globT σ₀ = none → U.exhAny σ₀ = true
  | _, .nil, _, h => by cases h
  | _, .snoc U e, hk, h => by
    simp only [Upd.exhOk, Bool.and_eq_true, Bool.or_eq_true] at hk
    simp only [Upd.exhAny, Bool.or_eq_true]
    change (U.globT σ₀).bind (e.globT σ₀) = none at h
    cases hU : U.globT σ₀ with
    | none => exact .inl (Upd.exhAny_of_none σ₀ U hk.1 hU)
    | some g =>
      rw [hU, Option.bind_some] at h
      have hs := UpdElem.globT_isSome σ₀ e g
      rw [h, Option.isSome_none] at hs
      rcases hk.2 with ho | hx
      · rw [← hs] at ho; cases ho
      · exact .inr hx
  | _, .decl U _ r, hk, h => by
    simp only [Upd.exhOk, Bool.and_eq_true, Bool.or_eq_true] at hk
    simp only [Upd.exhAny, Bool.or_eq_true]
    change (U.globT σ₀).bind (fun g => (r.eval σ₀).bind fun _ => some g) = none at h
    cases hU : U.globT σ₀ with
    | none => exact .inl (Upd.exhAny_of_none σ₀ U hk.1 hU)
    | some g =>
      rw [hU, Option.bind_some] at h
      rcases hk.2 with hs | hx
      · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
        rw [hv, Option.bind_some] at h
        cases h
      · exact .inr hx
  | _, .pop U _, hk, h => Upd.exhAny_of_none σ₀ U hk h
  | _, .drop U _, hk, h => Upd.exhAny_of_none σ₀ U hk h

theorem Tm.exhB_app2_pushFree (σ : State C Γ) {a b k : Srt} (o : Op2 C a b k) (x : Tm C Γ a)
    (y : Tm C Γ b) (hx : x.pushFree = true) (hy : y.pushFree = true) :
    (Tm.app2 o x y).exhB σ = o.exhB (x.eval σ) (y.eval σ) := by
  simp only [Tm.exhB, Tm.exhB_of_pushFree σ x hx, Tm.exhB_of_pushFree σ y hy, Bool.false_and,
    Bool.or_false, Bool.and_false]

theorem Tm.exhB_app3_pushFree (σ : State C Γ) {a b c k : Srt} (o : Op3 C a b c k) (x : Tm C Γ a)
    (y : Tm C Γ b) (z : Tm C Γ c) (hx : x.pushFree = true) (hy : y.pushFree = true)
    (hz : z.pushFree = true) :
    (Tm.app3 o x y z).exhB σ = o.exhB (x.eval σ) (y.eval σ) (z.eval σ) := by
  simp only [Tm.exhB, Tm.exhB_of_pushFree σ x hx, Tm.exhB_of_pushFree σ y hy,
    Tm.exhB_of_pushFree σ z hz, Bool.false_and, Bool.or_false, Bool.and_false]

theorem Rhs.exhB_of_pushFree (σ₀ : State C Γ) {t : LTy} (r : Rhs C Γ t) (h : r.pushFree = true) :
    r.exhB σ₀ = false := by
  cases r <;> first | rfl | exact Tm.exhB_of_pushFree σ₀ _ h

theorem UpdElem.exhB_of_pushFree {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElem C Γ Δ)
    (h : e.pushFree = true) : e.exhB σ₀ = false := by
  cases e with
  | «local» _ r => exact Rhs.exhB_of_pushFree σ₀ r h
  | storage s | memory s | selfBalance _ s | setBalance s => exact Tm.exhB_of_pushFree σ₀ s h
  | net r _ a | pay r a | netMt r a =>
    simp only [UpdElem.pushFree, Bool.and_eq_true] at h
    simp only [UpdElem.exhB, Tm.exhB_of_pushFree σ₀ r h.1, Tm.exhB_of_pushFree σ₀ a h.2,
      Bool.false_and, Bool.or_self]

theorem Upd.exhAny_of_pushFree (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    U.pushFree = true → U.exhAny σ₀ = false
  | _, .nil, _ => rfl
  | _, .snoc U e, h => by
    simp only [Upd.pushFree, Bool.and_eq_true] at h
    simp only [Upd.exhAny, Upd.exhAny_of_pushFree σ₀ U h.1, UpdElem.exhB_of_pushFree σ₀ e h.2,
      Bool.or_self]
  | _, .decl U _ r, h => by
    simp only [Upd.pushFree, Bool.and_eq_true] at h
    simp only [Upd.exhAny, Upd.exhAny_of_pushFree σ₀ U h.1, Rhs.exhB_of_pushFree σ₀ r h.2,
      Bool.or_self]
  | _, .pop U _, h | _, .drop U _, h => Upd.exhAny_of_pushFree σ₀ U h

theorem Upd.exh_of_exhAny {Δ : Ctx} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    (h : U.exhAny σ₀ = false) : U.exh σ₀ = false := by
  simp only [Upd.exh, h, Bool.false_and]

/-- An update that lands reverts nowhere. -/
theorem Upd.exhOk_of_globT {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    {g : GlobT C σ₀.H} → U.globT σ₀ = some g → U.exhOk σ₀ = true
  | _, .nil, _, _ => rfl
  | _, .snoc U e, g, h => by
    change (U.globT σ₀).bind (e.globT σ₀) = some g at h
    obtain ⟨g₀, hU, he⟩ := Option.bind_eq_some_iff.1 h
    have ho := UpdElem.globT_isSome σ₀ e g₀
    rw [he, Option.isSome_some] at ho
    simp only [Upd.exhOk, Upd.exhOk_of_globT U hU, ← ho, Bool.true_or, Bool.and_self]
  | _, .decl U _ r, g, h => by
    change (U.globT σ₀).bind (fun g => (r.eval σ₀).bind fun _ => some g) = some g at h
    obtain ⟨g₀, hU, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨v, hv, -⟩ := Option.bind_eq_some_iff.1 h
    simp only [Upd.exhOk, Upd.exhOk_of_globT U hU, hv, Option.isSome_some, Bool.true_or,
      Bool.and_self]
  | _, .pop U _, _, h | _, .drop U _, _, h => Upd.exhOk_of_globT U h

/-- An update with no push symbol is never out of gas. -/
theorem Upd.exh_of_pushFree {Δ : Ctx} {σ₀ : State C Γ} {U : Upd C Γ Δ} (h : U.pushFree = true) :
    U.exh σ₀ = false :=
  Upd.exh_of_exhAny (Upd.exhAny_of_pushFree σ₀ U h)

/-- An update out of gas halts. -/
theorem Upd.globT_of_exh (σ₀ : State C Γ) {Δ : Ctx} (U : Upd C Γ Δ) (h : U.exh σ₀ = true) :
    U.globT σ₀ = none :=
  Upd.globT_of_exhAny σ₀ U (Bool.and_eq_true_iff.1 h).1

/-- An update that lands is not out of gas. -/
theorem Upd.exh_of_globT {Δ : Ctx} {σ₀ : State C Γ} {U : Upd C Γ Δ} {g : GlobT C σ₀.H}
    (h : U.globT σ₀ = some g) : U.exh σ₀ = false := by
  cases hx : U.exh σ₀ with
  | false => rfl
  | true => rw [Upd.globT_of_exh σ₀ U hx] at h; cases h

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
on; when it halts, `m.onHalt`, or out of gas (`Upd.exh`), which both
modalities accept as they accept the run's. -/
def Upd.afterT {Δ : Ctx} (m : Modality) (σ₀ : State C Γ) (U : Upd C Γ Δ)
    (p : State C Δ → Prop) : Prop :=
  match U.globT σ₀ with
  | none => m.onHalt ∨ U.exh σ₀ = true
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

/-- `afterT` from what it asks: `m.onHalt` or exhaustion where the update
halts, `p` of every typed state it lands on. -/
theorem Upd.afterT_introX {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p : State C Δ → Prop} (hh : U.globT σ₀ = none → m.onHalt ∨ U.exh σ₀ = true)
    (hp : ∀ g σ', U.Lands σ₀ g σ' → p σ') : U.afterT m σ₀ p := by
  unfold Upd.afterT
  split
  · rename_i he; exact hh he
  · exact fun σ' hl => hp _ σ' hl

/-- `afterT` from what it asks: `m.onHalt` where the update halts, `p` of
every typed state it lands on. -/
theorem Upd.afterT_intro {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p : State C Δ → Prop} (hh : U.globT σ₀ = none → m.onHalt)
    (hp : ∀ g σ', U.Lands σ₀ g σ' → p σ') : U.afterT m σ₀ p :=
  Upd.afterT_introX (fun he => .inl (hh he)) hp

/-- Where an update halts, `afterT` is `m.onHalt` or exhaustion. -/
theorem Upd.afterT.of_none {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p : State C Δ → Prop} (h : U.afterT m σ₀ p) (he : U.globT σ₀ = none) :
    m.onHalt ∨ U.exh σ₀ = true := by
  unfold Upd.afterT at h
  rw [he] at h
  exact h

/-- Where an update halts and is not out of gas, `afterT` is `m.onHalt`. -/
theorem Upd.afterT.of_noExh {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    {p : State C Δ → Prop} (h : U.afterT m σ₀ p) (he : U.globT σ₀ = none)
    (hx : U.exh σ₀ = false) : m.onHalt :=
  (h.of_none he).resolve_right (by rw [hx]; exact Bool.false_ne_true)

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
`m.onHalt` or exhaustion holds where `U` halts and `U'`'s `afterT` holds. -/
theorem Upd.afterT_of_lands {Δ : Ctx} {m : Modality} {σ₀ : State C Γ} {U U' : Upd C Γ Δ}
    {p : State C Δ → Prop}
    (he : U.globT σ₀ = none → U'.afterT m σ₀ p → m.onHalt ∨ U.exh σ₀ = true)
    (hl : ∀ g σ', U.Lands σ₀ g σ' → U'.Lands σ₀ g σ') (h : U'.afterT m σ₀ p) :
    U.afterT m σ₀ p :=
  Upd.afterT_introX (fun hU => he hU h) fun _ _ hL => h.of_lands (hl _ _ hL)

/-! ### The state an update leaves, by constructor -/

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
and the locals `applyV` returns, or `m.onHalt` or exhaustion where it
halts. -/
theorem Upd.afterT_applyV {Δ : Ctx} (m : Modality) (σ₀ : State C Γ) (U : Upd C Γ Δ)
    (p : State C Δ → Prop) :
    U.afterT m σ₀ p ↔ (match U.applyV σ₀ with
      | none => m.onHalt ∨ U.exh σ₀ = true
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
