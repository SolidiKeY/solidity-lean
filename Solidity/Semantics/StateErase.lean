import Solidity.Semantics.Erased
import Solidity.Semantics.Agree

/-!
# A scoped state and its erasure

The bridge between `Semantics/Erased.lean`'s scoped state (`EState C Γ`: the
locals of `Γ` by position, and the global part) and `Semantics.lean`'s
untyped one (the locals a list of named bindings), which the closer's terms
read (`docs/intrinsic.md`, M3; the statements' bridge, `run_erase`, was
deleted at W4 `sem-del` with the untyped run's last typed-side users).

`EState.erase ns σ` names the locals of `σ` by `ns` and encodes each
(`LTy.enc`).  `Agree ns σ τ`: the global parts are equal, and every local of
`σ` is bound in `τ` under its name, encoded; `τ` may bind more.
`Agree.erase`: a state agrees with its erasure.
-/

namespace Solidity

open Semantics (Value SVal MVal Seg Halt Res Binding lookupBy setBy copyStToM allocDefault
  copyMem applyBinOp applyUnOp checkArith)
open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne)

variable {C : Contract}

/-! ## Erased locals -/

/-- A local's value as `Semantics.lean` binds it. -/
def LTy.enc (C : Contract) : (t : LTy) → t.Denote C → Binding
  | .val _, v => .val v
  | .alias _, some (r, segs) => .spath r segs
  | .alias _, none => .unset
  | .mem _, some id => .mref id
  | .mem _, none => .unset
  | .old, st => .store st
  | .oldNet, l => .ledger l

/-- The locals as `Semantics.lean`'s environment, named by `ns` (innermost
first). -/
def Env.erase : {Γ : Ctx} → List Var → Env C Γ → List (Var × Binding)
  | [], _, _ => []
  | _ :: _, [], _ => []
  | t :: _, x :: ns, e => (x, t.enc C e.1) :: Env.erase ns e.2

/-- A global part with these bindings. -/
abbrev withLocals (τ : Semantics.State) (e : List (Var × Binding)) : Semantics.State :=
  { τ with env := e }

/-- A state erased: its global part, its locals named by `ns`. -/
def EState.erase {Γ : Ctx} (ns : List Var) (σ : EState C Γ) : Semantics.State :=
  withLocals σ.glob (Env.erase ns σ.env)

theorem Idx.name_mem {Γ : Ctx} {t : LTy} (i : Idx Γ t) (ns : List Var)
    (h : ns.length = Γ.length) : i.name ns ∈ ns := by
  unfold Idx.name
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h ▸ i.toNat_lt)]
  exact List.getElem_mem _

theorem Idx.name_there {Γ : Ctx} {t u : LTy} (i : Idx Γ t) (x : Var) (ns : List Var) :
    (Idx.there (u := u) i).name (x :: ns) = i.name ns := by
  simp only [Idx.name, Idx.toNat, List.getD_cons_succ]

namespace Env

theorem erase_keys {Γ : Ctx} (ns : List Var) (e : Env C Γ) (h : ns.length = Γ.length) :
    (Env.erase ns e).map Prod.fst = ns := by
  induction Γ generalizing ns with
  | nil => cases ns with
    | nil => rfl
    | cons _ _ => simp only [List.length_cons, List.length_nil, Nat.add_one_ne_zero] at h
  | cons t Γ ih => cases ns with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add,
        Nat.add_one_ne_zero] at h
    | cons x ns =>
      show x :: (Env.erase ns e.2).map Prod.fst = x :: ns
      rw [ih ns e.2 (Nat.succ.inj h)]

theorem mem_erase_key {Γ : Ctx} {ns : List Var} {e : Env C Γ} {x : Var} {b : Binding}
    (h : (x, b) ∈ Env.erase ns e) : x ∈ ns := by
  induction Γ generalizing ns with
  | nil => exact absurd h List.not_mem_nil
  | cons t Γ ih => cases ns with
    | nil => exact absurd h List.not_mem_nil
    | cons y ns =>
      rcases List.mem_cons.1 h with h | h
      · cases h; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

/-- A local's binding is among the erased ones. -/
theorem mem_erase_get {Γ : Ctx} {t : LTy} (i : Idx Γ t) :
    (ns : List Var) → (e : Env C Γ) → ns.length = Γ.length →
      (i.name ns, t.enc C (Env.get i e)) ∈ Env.erase ns e := by
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
    | cons x ns =>
      exact List.mem_cons_of_mem _ (ih ns e.2 (Nat.succ.inj h))

/-- A binding of a set local: the new one, or an old one of another name. -/
theorem mem_erase_set {Γ : Ctx} {t : LTy} (i : Idx Γ t) (v : t.Denote C) :
    (ns : List Var) → (e : Env C Γ) → ns.length = Γ.length → ns.Nodup →
      ∀ m ∈ Env.erase ns (Env.set i v e),
        m = (i.name ns, t.enc C v) ∨ (m ∈ Env.erase ns e ∧ m.1 ≠ i.name ns) := by
  induction i with
  | here =>
    intro ns e h hnd m hm
    cases ns with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add,
        Nat.add_one_ne_zero] at h
    | cons x ns =>
      rcases List.mem_cons.1 hm with hm | hm
      · exact .inl hm
      · refine .inr ⟨List.mem_cons_of_mem _ hm, fun hx => ?_⟩
        have hk := mem_erase_key (b := m.2) (x := m.1) hm
        have hx' : m.1 = x := hx
        exact (List.nodup_cons.1 hnd).1 (hx' ▸ hk)
  | there i ih =>
    intro ns e h hnd m hm
    cases ns with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add,
        Nat.add_one_ne_zero] at h
    | cons x ns =>
      have hnd' := List.nodup_cons.1 hnd
      rcases List.mem_cons.1 hm with hm | hm
      · subst hm
        refine .inr ⟨List.mem_cons_self, fun hx => hnd'.1 ?_⟩
        have hx' : x = i.name ns := hx
        rw [hx']
        exact Idx.name_mem i ns (Nat.succ.inj h)
      · rcases ih v ns e.2 (Nat.succ.inj h) hnd'.2 m hm with hm' | ⟨hm', hne⟩
        · exact .inl (by rw [Idx.name_there]; exact hm')
        · exact .inr ⟨List.mem_cons_of_mem _ hm', by rw [Idx.name_there]; exact hne⟩

end Env

namespace Env

/-- A scope's locals popped: the rest are bound as they were. -/
theorem mem_erase_drop {Γ : Ctx} : {Δ : Ctx} → (h : Ext Γ Δ) → (qs ns : List Var) →
    (e : Env C Δ) → qs.length = h.depth →
      ∀ m ∈ Env.erase ns (Env.drop h e), m ∈ Env.erase (qs ++ ns) e := by
  intro Δ h
  induction h with
  | refl =>
    intro qs ns e hq m hm
    cases qs with
    | nil => exact hm
    | cons _ _ =>
      change _ = 0 at hq
      simp only [List.length_cons, Nat.add_one_ne_zero] at hq
  | push h ih =>
    intro qs ns e hq m hm
    change _ = h.depth + 1 at hq
    cases qs with
    | nil => simp only [List.length_nil] at hq; omega
    | cons q qs =>
      exact List.mem_cons_of_mem _ (ih qs ns e.2 (by
        simp only [List.length_cons] at hq; omega) m hm)

end Env

/-! ## Agreement -/

/-- A scoped state and an untyped one agree on the locals named `ns`: the
global parts are equal, and each local is bound under its name.  The untyped
state may bind more names. -/
structure Agree {Γ : Ctx} (ns : List Var) (σ : EState C Γ) (τ : Semantics.State) : Prop where
  len : ns.length = Γ.length
  nodup : ns.Nodup
  glob : withLocals σ.glob τ.env = τ
  env : ∀ m ∈ Env.erase ns σ.env, lookupBy m.1 τ.env = some m.2

namespace Agree

variable {Γ : Ctx} {ns : List Var} {σ : EState C Γ} {τ : Semantics.State}

/-- A scope's locals popped. -/
theorem drop {Δ : Ctx} {qs : List Var} {σ : EState C Δ} (hag : Agree (qs ++ ns) σ τ)
    (h : Ext Γ Δ) (hq : qs.length = h.depth) : Agree ns (σ.drop h) τ where
  len := by
    have h₁ := hag.len
    have h₂ := h.length_eq
    simp only [List.length_append] at h₁
    omega
  nodup := (List.nodup_append.1 hag.nodup).2.1
  glob := hag.glob
  env m hm := hag.env m (Env.mem_erase_drop h qs ns σ.env hq m hm)

end Agree

/-! ## A state agrees with its erasure -/

section ErasedState

variable {Γ : Ctx}

theorem lookupBy_of_mem_nodup {κ α : Type} [DecidableEq κ] :
    {l : List (κ × α)} → (l.map Prod.fst).Nodup → {m : κ × α} → m ∈ l → lookupBy m.1 l = some m.2
  | [], _, _, hm => absurd hm List.not_mem_nil
  | (k, v) :: l, hnd, m, hm => by
    have hnd' := List.nodup_cons.1 hnd
    rcases List.mem_cons.1 hm with hm | hm
    · subst hm; simp only [lookupBy, if_true]
    · have hne : m.1 ≠ k := fun h => hnd'.1 (by rw [← h]; exact List.mem_map.2 ⟨m, hm, rfl⟩)
      simp only [lookupBy, hne, if_false]
      exact lookupBy_of_mem_nodup hnd'.2 hm

/-- A state agrees with its erasure. -/
theorem Agree.erase {ns : List Var} (σ : EState C Γ) (hnd : ns.Nodup) (hlen : ns.length = Γ.length) :
    Agree ns σ (σ.erase ns) where
  len := hlen
  nodup := hnd
  glob := rfl
  env _ hm := lookupBy_of_mem_nodup (l := Env.erase ns σ.env)
    (by rw [Env.erase_keys ns σ.env hlen]; exact hnd) hm

end ErasedState

end Solidity
