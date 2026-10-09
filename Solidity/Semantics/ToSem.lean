import Solidity.Semantics.RunFrame
import Solidity.Semantics.StateErase

/-!
# A typed state, named

`State.toSem ns` reads a typed state as `Semantics.lean`'s: its storage
and heap erased, its locals bound under the names `ns` (innermost first),
each as `Semantics.lean` binds it (`LTy.TDenote.bind`)
(`docs/intrinsic.md`, W1 lane `runlemmas`).  It is what `State.erase ns`
(`Semantics/StateErase.lean`) is for the scoped state, read straight
off the typed parts.

The lemmas say how it moves with the typed state's operations: a local
declared conses its binding, a local set replaces it in place
(`Semantics.setBy`, when the names are distinct), a scope's end drops its
names, the storage and the ledger replaced are `Semantics.State.havoc`.
A local is found under its name (`State.lookup_toSem`).  The bridge to
the scoped run (`State.toSem_eq`, `State.agree_toSem`) goes with it.
-/

namespace Solidity

open Semantics (Binding lookupBy setBy)

variable {C : Contract}

/-! ## Bindings -/

/-- A typed local as `Semantics.lean` binds it. -/
def LTy.TDenote.bind {H : HTy} : (t : LTy) → t.TDenote C H → Binding
  | .val p, v => .val (PrimTy.erase (p := p) v)
  | .alias _, some r => .spath (SRef.erase r).1 (SRef.erase r).2
  | .alias _, none => .unset
  | .mem _, some r => .mref (r : HRef H _).id
  | .mem _, none => .unset
  | .old, st => .store (Storage.erase (st : Storage C))
  | .oldNet, l => .ledger l

theorem LTy.TDenote.bind_wk {H H' : HTy} (e : H <+: H') :
    (t : LTy) → (v : t.TDenote C H) → bind t (wk e t v) = bind t v
  | .val _, _ | .alias _, none | .alias _, some _ | .mem _, none | .mem _, some _ | .old, _
  | .oldNet, _ => rfl

/-! ## Locals -/

namespace TEnv

variable {H : HTy}

/-- The locals as `Semantics.lean`'s environment, named by `ns` (innermost
first). -/
def toSem : {Γ : Ctx} → List Var → TEnv C H Γ → List (Var × Binding)
  | [], _, _ => []
  | _ :: _, [], _ => []
  | t :: _, x :: ns, e => (x, LTy.TDenote.bind t e.1) :: TEnv.toSem ns e.2

theorem toSem_keys {Γ : Ctx} (ns : List Var) (e : TEnv C H Γ) (h : ns.length = Γ.length) :
    (TEnv.toSem ns e).map Prod.fst = ns := by
  induction Γ generalizing ns with
  | nil => cases ns with
    | nil => rfl
    | cons _ _ => simp only [List.length_cons, List.length_nil, Nat.add_one_ne_zero] at h
  | cons t Γ ih => cases ns with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add,
        Nat.add_one_ne_zero] at h
    | cons x ns =>
      show x :: (TEnv.toSem ns e.2).map Prod.fst = x :: ns
      rw [ih ns e.2 (Nat.succ.inj h)]

/-- A local's binding is among the named ones. -/
theorem mem_toSem_get {Γ : Ctx} {t : LTy} (i : Idx Γ t) :
    (ns : List Var) → (e : TEnv C H Γ) → ns.length = Γ.length →
      (i.name ns, LTy.TDenote.bind t (TEnv.get i e)) ∈ TEnv.toSem ns e := by
  induction i with
  | here =>
    intro ns e h
    cases ns with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add,
        Nat.add_one_ne_zero] at h
    | cons x ns => exact List.mem_cons_self
  | there i ih =>
    intro ns e h
    cases ns with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add,
        Nat.add_one_ne_zero] at h
    | cons x ns => exact List.mem_cons_of_mem _ (ih ns e.2 (Nat.succ.inj h))

/-- A local set: its binding replaced in place, the names being distinct. -/
theorem toSem_set {Γ : Ctx} {t : LTy} (i : Idx Γ t) (v : t.TDenote C H) :
    (ns : List Var) → (e : TEnv C H Γ) → ns.length = Γ.length → ns.Nodup →
      TEnv.toSem ns (TEnv.set i v e) = setBy (i.name ns) (LTy.TDenote.bind t v) (TEnv.toSem ns e) := by
  induction i with
  | here =>
    intro ns e h _
    cases ns with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add,
        Nat.add_one_ne_zero] at h
    | cons x ns =>
      show (x, _) :: TEnv.toSem ns e.2 = setBy x _ ((x, _) :: TEnv.toSem ns e.2)
      simp only [setBy, if_true]
      rfl
  | there i ih =>
    intro ns e h hnd
    cases ns with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add,
        Nat.add_one_ne_zero] at h
    | cons x ns =>
      have hnd' := List.nodup_cons.1 hnd
      have hne : i.name ns ≠ x := fun hx => hnd'.1 (hx ▸ Idx.name_mem i ns (Nat.succ.inj h))
      show (x, _) :: TEnv.toSem ns (TEnv.set i v e.2) = setBy (i.name ns) _ ((x, _) :: _)
      simp only [setBy, hne, if_false, ih v ns e.2 (Nat.succ.inj h) hnd'.2]
      rfl

/-- A scope's locals popped: their names dropped. -/
theorem toSem_drop {Γ : Ctx} : {Δ : Ctx} → (h : Ext Γ Δ) → (qs ns : List Var) →
    (e : TEnv C H Δ) → qs.length = h.depth →
      TEnv.toSem ns (TEnv.drop h e) = (TEnv.toSem (qs ++ ns) e).drop h.depth := by
  intro Δ h
  induction h with
  | refl =>
    intro qs ns e hq
    cases qs with
    | nil => rfl
    | cons _ _ =>
      change _ = 0 at hq
      simp only [List.length_cons, Nat.add_one_ne_zero] at hq
  | push h ih =>
    intro qs ns e hq
    change _ = h.depth + 1 at hq
    cases qs with
    | nil => simp only [List.length_nil] at hq; omega
    | cons q qs =>
      show _ = ((q, _) :: TEnv.toSem (qs ++ ns) e.2).drop (h.depth + 1)
      rw [List.drop_succ_cons]
      exact ih qs ns e.2 (by simp only [List.length_cons] at hq; omega)

theorem toSem_wk {H' : HTy} (e₀ : H <+: H') : {Γ : Ctx} → (ns : List Var) → (e : TEnv C H Γ) →
    TEnv.toSem ns (TEnv.wk e₀ Γ e) = TEnv.toSem ns e
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | t :: Γ, x :: ns, e => by
    show (x, LTy.TDenote.bind t (LTy.TDenote.wk e₀ t e.1)) :: TEnv.toSem ns (TEnv.wk e₀ Γ e.2) =
      (x, _) :: TEnv.toSem ns e.2
    rw [LTy.TDenote.bind_wk, toSem_wk e₀ ns e.2]

end TEnv

/-! ## States -/

namespace State

variable {Γ : Ctx}

/-- **A typed state as `Semantics.lean`'s**: the storage and the heap
erased, the next identity the heap's length, the locals named by `ns`. -/
def toSem (ns : List Var) (σ : State C Γ) : Semantics.State :=
  { storage := σ.storage.erase, heap := σ.heap.erase, nextId := σ.H.length,
    env := TEnv.toSem ns σ.env, net := σ.net, selfBalance := σ.selfBalance.1,
    tx := σ.tx.erase }

/-- **A local is found under its name.** -/
theorem lookup_toSem (ns : List Var) (σ : State C Γ) (hlen : ns.length = Γ.length)
    (hnd : ns.Nodup) {t : LTy} (i : Idx Γ t) :
    lookupBy (i.name ns) (σ.toSem ns).env = some (LTy.TDenote.bind t (TEnv.get i σ.env)) :=
  lookupBy_of_mem_nodup (l := TEnv.toSem ns σ.env)
    (by rw [TEnv.toSem_keys ns σ.env hlen]; exact hnd) (TEnv.mem_toSem_get i ns σ.env hlen)

theorem toSem_push (ns : List Var) (σ : State C Γ) (x : Var) {t : LTy} (v : t.TDenote C σ.H) :
    (σ.push v).toSem (x :: ns) =
      { σ.toSem ns with env := (x, LTy.TDenote.bind t v) :: (σ.toSem ns).env } := rfl

theorem toSem_setLocal (ns : List Var) (σ : State C Γ) (hlen : ns.length = Γ.length)
    (hnd : ns.Nodup) {t : LTy} (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).toSem ns = (σ.toSem ns).setEnv (i.name ns) (LTy.TDenote.bind t v) := by
  simp only [toSem, setLocal, Semantics.State.setEnv, TEnv.toSem_set i v ns σ.env hlen hnd]

theorem toSem_drop {Δ : Ctx} (h : Ext Γ Δ) (qs ns : List Var) (σ : State C Δ)
    (hq : qs.length = h.depth) :
    (σ.drop h).toSem ns = { σ.toSem (qs ++ ns) with env := (σ.toSem (qs ++ ns)).env.drop h.depth } := by
  simp only [toSem, drop, TEnv.toSem_drop h qs ns σ.env hq]

theorem toSem_withStorage (ns : List Var) (σ : State C Γ) (st : Storage C) :
    (σ.withStorage st).toSem ns = { σ.toSem ns with storage := st.erase } := rfl

theorem toSem_havoc (ns : List Var) (σ : State C Γ) (st : Storage C) (nt : List (Int × Int)) :
    (σ.havoc st nt).toSem ns = (σ.toSem ns).havoc st.erase nt := rfl

theorem toSem_pay (ns : List Var) (σ : State C Γ) (a m : Int) :
    (σ.pay a m).toSem ns = { σ.toSem ns with net := (σ.pay a m).net } := rfl

/-- Weakening the locals along a grown heap names them alike. -/
theorem toSem_adopt {α : HTy → Type} (ns : List Var) (σ : State C Γ) (g : Grown σ.H α) :
    (σ.adopt g).1.toSem ns =
      { σ.toSem ns with heap := g.heap.erase, nextId := g.H'.length } := by
  simp only [toSem, adopt, TEnv.toSem_wk]

/-! ### The bridge to the scoped run -/

theorem _root_.Solidity.LTy.TDenote.bind_eq_enc {H : HTy} :
    (t : LTy) → (v : t.TDenote C H) → LTy.TDenote.bind t v = t.enc C (LTy.TDenote.erase t v)
  | .val _, _ | .alias _, none | .alias _, some _ | .mem _, none | .mem _, some _ | .old, _
  | .oldNet, _ => rfl

theorem _root_.Solidity.TEnv.toSem_eq {H : HTy} : {Γ : Ctx} → (ns : List Var) →
    (e : TEnv C H Γ) → TEnv.toSem ns e = Env.erase ns (TEnv.erase Γ e)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | t :: _, x :: ns, e => by
    show (x, _) :: TEnv.toSem ns e.2 = (x, _) :: Env.erase ns (TEnv.erase _ e.2)
    rw [LTy.TDenote.bind_eq_enc, TEnv.toSem_eq ns e.2]
    rfl

/-- The named state is the scoped state's erasure. -/
theorem toSem_eq (ns : List Var) (σ : State C Γ) : σ.toSem ns = σ.erase.erase ns := by
  simp only [toSem, erase, EState.erase, EState.glob, TEnv.toSem_eq]

/-- **A typed state agrees with its named reading** (`Agree`, `Semantics/StateErase.lean`). -/
theorem agree_toSem (ns : List Var) (σ : State C Γ) (hnd : ns.Nodup)
    (hlen : ns.length = Γ.length) : Agree ns σ.erase (σ.toSem ns) := by
  rw [toSem_eq]
  exact Agree.erase σ.erase hnd hlen

end State

end Solidity
