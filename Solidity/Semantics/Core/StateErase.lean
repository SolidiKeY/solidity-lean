import Solidity.Semantics.Core
import Solidity.Semantics.Agree

/-!
# A scoped state and its erasure

The bridge between `Semantics/Core.lean`'s scoped state (`State C Γ`: the
locals of `Γ` by position, and the global part) and `Semantics.lean`'s
untyped one (the locals a list of named bindings), which the closer's terms
read (`docs/intrinsic.md`, M3; the statements' bridge, `run_erase`, was
deleted at W4 `sem-del` with the untyped run's last typed-side users).

`State.erase ns σ` names the locals of `σ` by `ns` and encodes each
(`LTy.enc`).  `Agree ns σ τ`: the global parts are equal, and every local of
`σ` is bound in `τ` under its name, encoded; `τ` may bind more.  `RunRel`
and `RunRelA` relate two outcomes: the same halt, or states in `Agree` whose
bindings off a set of names are untouched.  The global operations are
shared: each is natural in the locals (`*_nat`, `*_wl`), so an expression
reads alike in agreeing states (`Val.eval_erase` and its siblings), and a
write leaves agreeing states (`MLoc.write_erase`, `OpLoc.store_erase`, …).
`Agree.erase`: a state agrees with its erasure.
-/

namespace Solidity.Core

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
def State.erase {Γ : Ctx} (ns : List Var) (σ : State C Γ) : Semantics.State :=
  withLocals σ.glob (Env.erase ns σ.env)

theorem Idx.name_mem {Γ : Ctx} {t : LTy} (i : Idx Γ t) (ns : List Var)
    (h : ns.length = Γ.length) : i.name ns ∈ ns := by
  unfold Idx.name
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h ▸ i.toNat_lt)]
  exact List.getElem_mem _

theorem Idx.name_here {Γ : Ctx} {t : LTy} (x : Var) (ns : List Var) :
    (Idx.here : Idx (t :: Γ) t).name (x :: ns) = x := rfl

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

theorem get_here {Γ : Ctx} {t : LTy} (e : Env C (t :: Γ)) : Env.get .here e = e.1 := rfl

theorem get_there {Γ : Ctx} {t u : LTy} (i : Idx Γ t) (e : Env C (u :: Γ)) :
    Env.get (.there i) e = Env.get i e.2 := rfl

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

theorem erase_append {Γ : Ctx} : (ρ : Ctx) → (qs ns : List Var) → (r : Env C ρ) →
    (e : Env C Γ) → qs.length = ρ.length →
      Env.erase (qs ++ ns) (Env.append ρ r e) = Env.erase qs r ++ Env.erase ns e
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h => by simp only [List.length_cons, List.length_nil,
      Nat.add_one_ne_zero] at h
  | _ :: _, [], _, _, _, h => by simp only [List.length_nil, List.length_cons,
      Nat.right_eq_add, Nat.add_one_ne_zero] at h
  | _ :: ρ, q :: qs, ns, r, e, h => by
    show (q, _) :: Env.erase (qs ++ ns) (Env.append ρ r.2 e) = (q, _) :: Env.erase qs r.2 ++ _
    rw [erase_append ρ qs ns r.2 e (Nat.succ.inj h)]
    rfl

theorem mem_erase_take {Γ : Ctx} : (ρ : Ctx) → (qs ns : List Var) → (e : Env C (ρ ++ Γ)) →
    qs.length = ρ.length → ∀ m ∈ Env.erase qs (Env.take ρ e), m ∈ Env.erase (qs ++ ns) e
  | [], [], _, _, _, m, hm => absurd hm List.not_mem_nil
  | [], _ :: _, _, _, h, _, _ => by simp only [List.length_cons, List.length_nil,
      Nat.add_one_ne_zero] at h
  | _ :: _, [], _, _, h, _, _ => by simp only [List.length_nil, List.length_cons,
      Nat.right_eq_add, Nat.add_one_ne_zero] at h
  | _ :: ρ, q :: qs, ns, e, h, m, hm => by
    rcases List.mem_cons.1 hm with hm | hm
    · exact hm ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_erase_take ρ qs ns e.2 (Nat.succ.inj h) m hm)

end Env

/-! ## Agreement -/

/-- A scoped state and an untyped one agree on the locals named `ns`: the
global parts are equal, and each local is bound under its name.  The untyped
state may bind more names. -/
structure Agree {Γ : Ctx} (ns : List Var) (σ : State C Γ) (τ : Semantics.State) : Prop where
  len : ns.length = Γ.length
  nodup : ns.Nodup
  glob : withLocals σ.glob τ.env = τ
  env : ∀ m ∈ Env.erase ns σ.env, lookupBy m.1 τ.env = some m.2

/-- Two outcomes, from `τ₀`: the same halt, or states that agree on `ns` and
bind every name off `B` as `τ₀` did. -/
def RunRel {Γ : Ctx} (ns B : List Var) (τ₀ : Semantics.State) :
    Res (State C Γ) → Res Semantics.State → Prop
  | .error e₁, .error e₂ => e₁ = e₂
  | .ok σ, .ok τ => Agree ns σ τ ∧ ∀ y, y ∉ B → lookupBy y τ.env = lookupBy y τ₀.env
  | _, _ => False

namespace Agree

variable {Γ : Ctx} {ns : List Var} {σ : State C Γ} {τ : Semantics.State}

theorem glob_with (hag : Agree ns σ τ) (e : List (Var × Binding)) :
    withLocals σ.glob e = withLocals τ e := by
  rw [← hag.glob]

/-- A local is bound under its name. -/
theorem get (hag : Agree ns σ τ) {t : LTy} (i : Idx Γ t) :
    lookupBy (i.name ns) τ.env = some (t.enc C (Env.get i σ.env)) :=
  hag.env _ (Env.mem_erase_get i ns σ.env hag.len)

theorem getEnv (hag : Agree ns σ τ) {t : LTy} (i : Idx Γ t) :
    τ.getEnv (i.name ns) = .ok (t.enc C (Env.get i σ.env)) := by
  simp only [Semantics.State.getEnv, hag.get i]

/-- Binding a name not in `ns`. -/
theorem setOther (hag : Agree ns σ τ) {y : Var} (hy : y ∉ ns) (b : Binding) :
    Agree ns σ (τ.setEnv y b) where
  len := hag.len
  nodup := hag.nodup
  glob := hag.glob_with _
  env m hm := by
    have hne : m.1 ≠ y := fun h => hy (h ▸ Env.mem_erase_key (b := m.2) hm)
    simp only [Semantics.State.setEnv, lookupBy_setBy_ne hne, hag.env m hm]

/-- A local declared under a name not in `ns`. -/
theorem push (hag : Agree ns σ τ) {x : Var} (hx : x ∉ ns) {t : LTy} (v : t.Denote C) :
    Agree (x :: ns) (σ.push v) (τ.setEnv x (t.enc C v)) where
  len := by simp only [List.length_cons, hag.len]
  nodup := List.nodup_cons.2 ⟨hx, hag.nodup⟩
  glob := hag.glob_with _
  env m hm := by
    rcases List.mem_cons.1 hm with hm | hm
    · subst hm; exact lookupBy_setBy_self _ _ _
    · exact (hag.setOther hx _).env m hm

/-- A local set, under its name. -/
theorem setLocal (hag : Agree ns σ τ) {t : LTy} (i : Idx Γ t) (v : t.Denote C) :
    Agree ns (σ.setLocal i v) (τ.setEnv (i.name ns) (t.enc C v)) where
  len := hag.len
  nodup := hag.nodup
  glob := hag.glob_with _
  env m hm := by
    rcases Env.mem_erase_set i v ns σ.env hag.len hag.nodup m hm with h | ⟨hm, hne⟩
    · subst h; exact lookupBy_setBy_self _ _ _
    · simp only [Semantics.State.setEnv, lookupBy_setBy_ne hne, hag.env m hm]

/-- The global part replaced on both sides. -/
theorem withGlob (hag : Agree ns σ τ) (s : Semantics.State) :
    Agree ns (σ.withGlob s) (withLocals s τ.env) where
  len := hag.len
  nodup := hag.nodup
  glob := rfl
  env := hag.env

/-- A scope's locals popped. -/
theorem drop {Δ : Ctx} {qs : List Var} {σ : State C Δ} (hag : Agree (qs ++ ns) σ τ)
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

namespace RunRel

variable {Γ : Ctx} {ns B : List Var} {τ₀ : Semantics.State}

theorem mono {B' : List Var} (hB : ∀ y ∈ B, y ∈ B') :
    {x : Res (State C Γ)} → {y : Res Semantics.State} → RunRel ns B τ₀ x y →
      RunRel ns B' τ₀ x y
  | .error _, .error _, h => h
  | .ok _, .ok _, ⟨hag, hf⟩ => ⟨hag, fun y hy => hf y (fun h => hy (hB y h))⟩

/-- A shared first step. -/
theorem bind_pure {α : Type} (x : Res α) {f : α → Res (State C Γ)}
    {g : α → Res Semantics.State} (h : ∀ a, x = .ok a → RunRel ns B τ₀ (f a) (g a)) :
    RunRel ns B τ₀ (x >>= f) (x >>= g) := by
  cases x with
  | error e => exact (rfl : e = e)
  | ok a => exact h a rfl

/-- One step, then the rest from where it left. -/
theorem bind {Γ₁ : Ctx} {ns₁ B₁ B₂ : List Var} {x : Res (State C Γ₁)} {y : Res Semantics.State}
    (hxy : RunRel ns₁ B₁ τ₀ x y) {f : State C Γ₁ → Res (State C Γ)}
    {g : Semantics.State → Res Semantics.State}
    (hfg : ∀ σ τ, Agree ns₁ σ τ → (∀ z, z ∉ B₁ → lookupBy z τ.env = lookupBy z τ₀.env) →
      RunRel ns B₂ τ (f σ) (g τ))
    (h₁ : ∀ z ∈ B₁, z ∈ B) (h₂ : ∀ z ∈ B₂, z ∈ B) :
    RunRel ns B τ₀ (x >>= f) (y >>= g) := by
  match x, y, hxy with
  | .error _, .error _, h => exact h
  | .ok σ, .ok τ, ⟨hag, hf⟩ =>
    have h := hfg σ τ hag hf
    revert h
    show RunRel ns B₂ τ (f σ) (g τ) → RunRel ns B τ₀ (f σ) (g τ)
    match f σ, g τ with
    | .error _, .error _ => exact id
    | .ok _, .ok _ => exact fun ⟨hag', hf'⟩ => ⟨hag', fun z hz =>
        (hf' z (fun h => hz (h₂ z h))).trans (hf z (fun h => hz (h₁ z h)))⟩
    | .ok _, .error _ => exact False.elim
    | .error _, .ok _ => exact False.elim

/-- A scope's locals popped. -/
theorem drop {Δ : Ctx} {qs : List Var} (h : Ext Γ Δ) (hq : qs.length = h.depth) :
    {x : Res (State C Δ)} → {y : Res Semantics.State} → RunRel (qs ++ ns) B τ₀ x y →
      RunRel ns B τ₀ (x.map (State.drop h)) y
  | .error _, .error _, h => h
  | .ok _, .ok _, ⟨hag, hf⟩ => ⟨hag.drop h hq, hf⟩

end RunRel

/-! ## The global operations do not read the locals -/

/-- An operation on the global part, natural in the locals: run with other
locals, it does the same and keeps them. -/
def Natural (f : Semantics.State → Res Semantics.State) : Prop :=
  ∀ s e, f (withLocals s e) = (fun s' => withLocals s' e) <$> f s

/-- `Natural`, for an operation with a result. -/
def NaturalA {α : Type} (f : Semantics.State → Res (Semantics.State × α)) : Prop :=
  ∀ s e, f (withLocals s e) = (fun p => (withLocals p.1 e, p.2)) <$> f s

theorem saveStorage_nat (r : Name) (segs : List Seg) (v : SVal) :
    Natural (fun s => s.saveStorage r segs v) := by
  intro s e
  simp only [Semantics.State.saveStorage]
  cases lookupBy r s.storage with
  | none => rfl
  | some w => dsimp only; cases w.save segs v <;> rfl

section Natural

variable (s : Semantics.State) (e : List (Var × Binding))

theorem findStorage_wl (r : Name) (segs : List Seg) :
    (withLocals s e).findStorage r segs = s.findStorage r segs := rfl

theorem checkIndex_wl (r : Name) (segs : List Seg) (i : Int) :
    (withLocals s e).checkIndex r segs i = s.checkIndex r segs i := rfl

theorem getObj_wl (id : Nat) : (withLocals s e).getObj id = s.getObj id := rfl

theorem envVal_wl (k : EnvKey) : (withLocals s e).envVal k = s.envVal k := rfl

theorem arrayLen_wl (r : Name) (segs : List Seg) :
    arrayLen (withLocals s e) r segs = arrayLen s r segs := rfl

theorem memArrayLen_wl (id : Nat) : memArrayLen (withLocals s e) id = memArrayLen s id := rfl

theorem readLoc_wl (a : Semantics.Addr) : Semantics.readLoc (withLocals s e) a = Semantics.readLoc s a := by
  cases a <;> rfl

theorem setObj_wl (id : Nat) (o : Semantics.MObj) :
    (withLocals s e).setObj id o = withLocals (s.setObj id o) e := rfl

theorem pay_wl (a amt : Int) :
    (withLocals s e).pay a amt = withLocals (s.pay a amt) e := rfl

/-- `lookupBy` misses a key the list does not have. -/
theorem lookupBy_none_of_not_mem {κ α : Type} [DecidableEq κ] {k : κ} :
    (l : List (κ × α)) → k ∉ l.map Prod.fst → lookupBy k l = none
  | [], _ => rfl
  | (k', _) :: l, h => by
    have hne : k ≠ k' := fun hk => h (hk ▸ List.mem_cons_self)
    simp only [lookupBy, hne, if_false]
    exact lookupBy_none_of_not_mem l (fun hk => h (List.mem_cons_of_mem _ hk))

theorem copyMem_wl (v : MVal) : copyMem (withLocals s e) v = copyMem s v := by
  refine Semantics.copyMem_congr (ns := e.map Prod.fst ++ s.env.map Prod.fst)
    (s₁ := withLocals s e) (s₂ := s)
    ⟨rfl, rfl, rfl, rfl, fun n hn => ?_, rfl, rfl⟩ v
  rw [lookupBy_none_of_not_mem _ (fun h => hn (List.mem_append_left _ h)),
    lookupBy_none_of_not_mem _ (fun h => hn (List.mem_append_right _ h))]

end Natural

/-- A first step that reads, then a natural one. -/
theorem nat_bind {α : Type} (x : Res α) {f : α → Semantics.State → Res Semantics.State}
    (hf : ∀ a, Natural (f a)) (s : Semantics.State) (e : List (Var × Binding)) :
    (x >>= fun a => f a (withLocals s e)) = (fun s' => withLocals s' e) <$> (x >>= fun a => f a s) := by
  cases x with
  | error _ => rfl
  | ok a => exact hf a s e

theorem writeStorage_nat (r : Name) (segs : List Seg) (v : SVal) :
    Natural (fun s => s.writeStorage r segs v) := by
  intro s e
  simp only [Semantics.State.writeStorage]
  split
  · exact saveStorage_nat r segs _ s e
  all_goals
    rw [findStorage_wl]
    exact nat_bind _ (fun cur => saveStorage_nat r segs _) s e

theorem memWriteField_nat (id : Nat) (f : Name) (mv : MVal) :
    Natural (fun s => memWriteField s id f mv) := by
  intro s e
  simp only [memWriteField, getObj_wl]
  cases s.getObj id with
  | error _ => rfl
  | ok o => cases o <;> rfl

theorem memWriteIndex_nat (id : Nat) (i : Int) (mv : MVal) :
    Natural (fun s => memWriteIndex s id i mv) := by
  intro s e
  simp only [memWriteIndex, getObj_wl]
  cases s.getObj id with
  | error _ => rfl
  | ok o =>
    cases o with
    | struct _ => rfl
    | array elems fx =>
      show (if 0 ≤ i ∧ i.toNat < elems.length then _ else _) =
        (fun s' => withLocals s' e) <$> (if 0 ≤ i ∧ i.toNat < elems.length then _ else _)
      split <;> rfl

theorem writeAddr_nat (mv : MVal) (a : Semantics.Addr) : Natural (fun s => writeAddr s mv a) := by
  cases a
  · exact memWriteField_nat _ _ _
  · exact memWriteIndex_nat _ _ _

theorem writeLoc_nat (a : Semantics.Addr) (v : Value) :
    Natural (fun s => Semantics.writeLoc s a v) := by
  intro s e
  cases a with
  | memoryField id f =>
    simp only [Semantics.writeLoc, getObj_wl]
    cases s.getObj id with
    | error _ => rfl
    | ok o => cases o <;> rfl
  | memoryIndex id i =>
    simp only [Semantics.writeLoc, getObj_wl]
    cases s.getObj id with
    | error _ => rfl
    | ok o =>
      cases o with
      | struct _ => rfl
      | array elems fx =>
        show (if 0 ≤ i ∧ i.toNat < elems.length then _ else _) =
          (fun s' => withLocals s' e) <$> (if 0 ≤ i ∧ i.toNat < elems.length then _ else _)
        split <;> rfl

mutual

theorem copyStToM_nat (s : Semantics.State) (e : List (Var × Binding)) :
    (v : SVal) → copyStToM (withLocals s e) v =
      (fun p => (withLocals p.1 e, p.2)) <$> copyStToM s v
  | .int _ => rfl
  | .bool _ => rfl
  | .map _ _ => rfl
  | .struct fields => by
    rw [Semantics.copyStToM, Semantics.copyStToM, copyStFields_nat s e fields]
    cases Semantics.copyStFields s fields <;> rfl
  | .array elems _ fx => by
    rw [Semantics.copyStToM, Semantics.copyStToM, copyStElems_nat s e elems]
    cases Semantics.copyStElems s elems <;> rfl

theorem copyStFields_nat (s : Semantics.State) (e : List (Var × Binding)) :
    (fields : List (Name × SVal)) → Semantics.copyStFields (withLocals s e) fields =
      (fun p => (withLocals p.1 e, p.2)) <$> Semantics.copyStFields s fields
  | [] => rfl
  | (n, v) :: rest => by
    rw [Semantics.copyStFields, Semantics.copyStFields, copyStToM_nat s e v]
    cases copyStToM s v with
    | error _ => rfl
    | ok p =>
      obtain ⟨s', mv⟩ := p
      show (do let (s'', mrest) ← Semantics.copyStFields (withLocals s' e) rest
               .ok (s'', (n, mv) :: mrest)) =
        (fun p => (withLocals p.1 e, p.2)) <$>
          (do let (s'', mrest) ← Semantics.copyStFields s' rest; .ok (s'', (n, mv) :: mrest))
      rw [copyStFields_nat s' e rest]
      cases Semantics.copyStFields s' rest <;> rfl

theorem copyStElems_nat (s : Semantics.State) (e : List (Var × Binding)) :
    (elems : List SVal) → Semantics.copyStElems (withLocals s e) elems =
      (fun p => (withLocals p.1 e, p.2)) <$> Semantics.copyStElems s elems
  | [] => rfl
  | v :: rest => by
    rw [Semantics.copyStElems, Semantics.copyStElems, copyStToM_nat s e v]
    cases copyStToM s v with
    | error _ => rfl
    | ok p =>
      obtain ⟨s', mv⟩ := p
      show (do let (s'', mrest) ← Semantics.copyStElems (withLocals s' e) rest
               .ok (s'', mv :: mrest)) =
        (fun p => (withLocals p.1 e, p.2)) <$>
          (do let (s'', mrest) ← Semantics.copyStElems s' rest; .ok (s'', mv :: mrest))
      rw [copyStElems_nat s' e rest]
      cases Semantics.copyStElems s' rest <;> rfl

end

theorem allocDefault_nat (R : RefTy) : NaturalA (fun s => allocDefault s R) := by
  intro s e
  simp only [Semantics.allocDefault, copyStToM_nat s e]
  cases copyStToM s (Semantics.defaultForRef R) with
  | error _ => rfl
  | ok p =>
    obtain ⟨s', mv⟩ := p
    cases mv <;> rfl

/-- One shared first step of a natural operation: `nat_step x` splits on it. -/
macro "nat_step " x:term : tactic => `(tactic|
  (cases h : $x <;> simp only [h, SemanticsProperties.Res.ok_bind, SemanticsProperties.Res.error_bind] <;> try rfl))

theorem saveStorage_wl (s : Semantics.State) (e : List (Var × Binding)) (r : Name)
    (segs : List Seg) (v : SVal) :
    (withLocals s e).saveStorage r segs v = (fun s' => withLocals s' e) <$> s.saveStorage r segs v :=
  saveStorage_nat r segs v s e

theorem writeLoc_wl (s : Semantics.State) (e : List (Var × Binding)) (a : Semantics.Addr)
    (v : Value) :
    Semantics.writeLoc (withLocals s e) a v =
      (fun s' => withLocals s' e) <$> Semantics.writeLoc s a v :=
  writeLoc_nat a v s e

theorem allocDefault_wl (s : Semantics.State) (e : List (Var × Binding)) (R : RefTy) :
    allocDefault (withLocals s e) R = (fun p => (withLocals p.1 e, p.2)) <$> allocDefault s R :=
  allocDefault_nat R s e

theorem pushAt_nat (E : Ty) (r : Name) (segs : List Seg) (val : SVal → Res SVal) :
    Natural (fun s => pushAt s E r segs val) := by
  intro s e
  simp only [pushAt, findStorage_wl]
  cases s.findStorage r segs with
  | error _ => rfl
  | ok v =>
    cases v with
    | array elems shadow fx =>
      show (val _ >>= fun w => (withLocals s e).saveStorage r segs (.array (elems ++ [w]) _ fx)) =
        (fun s' => withLocals s' e) <$> (val _ >>= fun w => s.saveStorage r segs _)
      exact nat_bind _ (fun _ => saveStorage_nat r segs _) s e
    | _ => rfl

theorem pushPlaceAt_nat (E : Ty) (r : Name) (segs : List Seg) :
    NaturalA (fun s => pushPlaceAt s E r segs) := by
  intro s e
  simp only [pushPlaceAt, findStorage_wl]
  cases s.findStorage r segs with
  | error _ => rfl
  | ok v =>
    cases v with
    | array elems shadow fx =>
      show ((withLocals s e).saveStorage r segs _ >>= fun s' => pure (s', _)) =
        (fun p => (withLocals p.1 e, p.2)) <$> (s.saveStorage r segs _ >>= fun s' => pure (s', _))
      rw [saveStorage_wl]
      cases s.saveStorage r segs _ <;> rfl
    | _ => rfl

theorem popAt_nat (keep : Bool) (r : Name) (segs : List Seg) :
    Natural (fun s => popAt s keep r segs) := by
  intro s e
  simp only [popAt, findStorage_wl]
  cases s.findStorage r segs with
  | error _ => rfl
  | ok v =>
    cases v with
    | array elems shadow fx =>
      show (match elems.reverse with
          | [] => _
          | last :: restRev => (withLocals s e).saveStorage r segs (.array restRev.reverse
              ((if keep then last else last.defaultOf) :: shadow) fx)) =
        (fun s' => withLocals s' e) <$> (match elems.reverse with
          | [] => _
          | last :: restRev => s.saveStorage r segs (.array restRev.reverse
              ((if keep then last else last.defaultOf) :: shadow) fx))
      cases elems.reverse with
      | nil => rfl
      | cons _ _ => exact saveStorage_nat r segs _ s e
    | _ => rfl

theorem opStore_nat (op : BinOp) (p : PrimTy) (r : Name) (segs : List Seg) (v : Value) :
    Natural (fun s => opStore s op p r segs v) := by
  intro s e
  simp only [opStore, findStorage_wl]
  nat_step s.findStorage r segs
  rename_i w _
  nat_step w.asValue
  rename_i old _
  nat_step applyBinOp op old v
  rename_i new _
  nat_step checkArith (.prim p) new
  exact saveStorage_wl s e r segs _

theorem opMem_nat (op : BinOp) (p : PrimTy) (a : Semantics.Addr) (v : Value) :
    Natural (fun s => opMem s op p a v) := by
  intro s e
  simp only [opMem, readLoc_wl]
  nat_step Semantics.readLoc s a
  rename_i old _
  nat_step applyBinOp op old v
  rename_i new _
  nat_step checkArith (.prim p) new
  exact writeLoc_wl s e a _

theorem bumpStore_nat (op : IncDec) (p : PrimTy) (r : Name) (segs : List Seg) :
    NaturalA (fun s => bumpStore s op p r segs) := by
  intro s e
  simp only [bumpStore, findStorage_wl]
  nat_step s.findStorage r segs
  rename_i w _
  nat_step w.asValue
  rename_i old _
  nat_step old.asInt
  rename_i oldInt _
  nat_step checkArith (.prim p) (.int (if op.isIncrement then oldInt + 1 else oldInt - 1))
  rename_i new _
  rw [saveStorage_wl]
  cases s.saveStorage r segs new.toSVal <;> rfl

theorem bumpMem_nat (op : IncDec) (p : PrimTy) (a : Semantics.Addr) :
    NaturalA (fun s => bumpMem s op p a) := by
  intro s e
  simp only [bumpMem, readLoc_wl]
  nat_step Semantics.readLoc s a
  rename_i old _
  nat_step old.asInt
  rename_i oldInt _
  nat_step checkArith (.prim p) (.int (if op.isIncrement then oldInt + 1 else oldInt - 1))
  rename_i new _
  rw [writeLoc_wl]
  cases Semantics.writeLoc s a new <;> rfl

theorem transferAt_nat (addr amt : Int) : Natural (fun s => transferAt s addr amt) := by
  intro s e
  simp only [transferAt]
  split <;> rfl

theorem memClear_nat (a : Semantics.Addr) : (T : Ty) → Natural (fun s => memClear s a T)
  | .prim _ => writeAddr_nat _ a
  | .ref R => by
    intro s e
    simp only [memClear]
    rw [allocDefault_wl]
    cases allocDefault s R with
    | error _ => rfl
    | ok p => exact writeAddr_nat _ a p.1 e

/-! ## The global part, through agreement -/

namespace Agree

variable {Γ : Ctx} {ns : List Var} {σ : State C Γ} {τ : Semantics.State}

theorem op (hag : Agree ns σ τ) {f : Semantics.State → Res Semantics.State} (hf : Natural f) :
    f τ = (fun s' => withLocals s' τ.env) <$> f σ.glob := by
  have h := hf σ.glob τ.env
  rwa [hag.glob] at h

theorem opA (hag : Agree ns σ τ) {α : Type} {f : Semantics.State → Res (Semantics.State × α)}
    (hf : NaturalA f) : f τ = (fun p => (withLocals p.1 τ.env, p.2)) <$> f σ.glob := by
  have h := hf σ.glob τ.env
  rwa [hag.glob] at h

theorem findStorage (hag : Agree ns σ τ) (r : Name) (segs : List Seg) :
    τ.findStorage r segs = σ.glob.findStorage r segs := by
  rw [← hag.glob]; rfl

theorem checkIndex (hag : Agree ns σ τ) (r : Name) (segs : List Seg) (i : Int) :
    τ.checkIndex r segs i = σ.glob.checkIndex r segs i := by
  rw [← hag.glob]; rfl

theorem getObj (hag : Agree ns σ τ) (id : Nat) : τ.getObj id = σ.glob.getObj id := by
  rw [← hag.glob]; rfl

theorem envVal (hag : Agree ns σ τ) (k : EnvKey) : τ.envVal k = σ.glob.envVal k := by
  rw [← hag.glob]; rfl

theorem arrayLen (hag : Agree ns σ τ) (r : Name) (segs : List Seg) :
    Solidity.arrayLen τ r segs = Solidity.arrayLen σ.glob r segs := by
  rw [← hag.glob]; rfl

theorem memArrayLen (hag : Agree ns σ τ) (id : Nat) :
    Solidity.memArrayLen τ id = Solidity.memArrayLen σ.glob id := by
  rw [← hag.glob]; rfl

theorem copyMem (hag : Agree ns σ τ) (v : MVal) : Semantics.copyMem τ v = Semantics.copyMem σ.glob v := by
  rw [← hag.glob]; exact copyMem_wl _ _ v

theorem tx (hag : Agree ns σ τ) : τ.tx = σ.tx := by
  rw [← hag.glob]; rfl

end Agree

/-- Binding a name of `B` leaves every other name's binding. -/
theorem frame_setEnv {B : List Var} {τ : Semantics.State} {x : Var} {b : Binding} (hx : x ∈ B) :
    ∀ y, y ∉ B → lookupBy y (τ.setEnv x b).env = lookupBy y τ.env := fun y hy => by
  simp only [Semantics.State.setEnv]
  exact lookupBy_setBy_ne (fun h => hy (by rw [h]; exact hx)) _ _

/-- Two outcomes with a result: the same halt, or the same result in states
related as `RunRel`'s. -/
def RunRelA {Γ : Ctx} {α : Type} (ns B : List Var) (τ₀ : Semantics.State) :
    Res (State C Γ × α) → Res (Semantics.State × α) → Prop
  | .error e₁, .error e₂ => e₁ = e₂
  | .ok (σ, a), .ok (τ, b) =>
    a = b ∧ Agree ns σ τ ∧ ∀ y, y ∉ B → lookupBy y τ.env = lookupBy y τ₀.env
  | _, _ => False

namespace RunRel

variable {Γ : Ctx} {ns B : List Var} {σ : State C Γ} {τ : Semantics.State}

/-- A global step. -/
theorem glob (hag : Agree ns σ τ) {f : Semantics.State → Res Semantics.State} (hf : Natural f) :
    RunRel ns B τ (σ.withGlob <$> f σ.glob) (f τ) := by
  rw [hag.op hf]
  cases f σ.glob with
  | error _ => exact (rfl : _ = _)
  | ok s => exact ⟨hag.withGlob s, fun _ _ => rfl⟩

/-- A global step with a result, then the rest. -/
theorem bind_globA {Γ' : Ctx} {ns' : List Var} (hag : Agree ns σ τ) {α : Type}
    {f : Semantics.State → Res (Semantics.State × α)} (hf : NaturalA f)
    {k₁ : Semantics.State × α → Res (State C Γ')} {k₂ : Semantics.State × α → Res Semantics.State}
    (hk : ∀ s a, f σ.glob = .ok (s, a) → RunRel ns' B τ (k₁ (s, a)) (k₂ (withLocals s τ.env, a))) :
    RunRel ns' B τ (f σ.glob >>= k₁) (f τ >>= k₂) := by
  rw [hag.opA hf, bind_map_left]
  exact bind_pure _ fun p hp => hk p.1 p.2 hp

theorem ok_setLocal (hag : Agree ns σ τ) {t : LTy} (i : Idx Γ t) (v : t.Denote C)
    (hB : i.name ns ∈ B) :
    RunRel ns B τ (.ok (σ.setLocal i v)) (.ok (τ.setEnv (i.name ns) (t.enc C v))) :=
  ⟨hag.setLocal i v, fun y hy => by
    simp only [Semantics.State.setEnv]
    exact lookupBy_setBy_ne (fun h => hy (by rw [h]; exact hB)) _ _⟩

theorem ok_push (hag : Agree ns σ τ) {x : Var} (hx : x ∉ ns) {t : LTy} (v : t.Denote C)
    (hB : x ∈ B) :
    RunRel (x :: ns) B τ (.ok (σ.push v)) (.ok (τ.setEnv x (t.enc C v))) :=
  ⟨hag.push hx v, fun y hy => by
    simp only [Semantics.State.setEnv]
    exact lookupBy_setBy_ne (fun h => hy (by rw [h]; exact hB)) _ _⟩

theorem ok_refl (hag : Agree ns σ τ) : RunRel ns B τ (.ok σ) (.ok τ) := ⟨hag, fun _ _ => rfl⟩

end RunRel

namespace RunRelA

variable {Γ : Ctx} {ns B : List Var} {τ₀ : Semantics.State}

/-- A step with a result, then the rest. -/
theorem bind {Γ' : Ctx} {α : Type} {ns' B₂ B' : List Var} {x : Res (State C Γ × α)}
    {y : Res (Semantics.State × α)} (hxy : RunRelA ns B τ₀ x y)
    {f : State C Γ × α → Res (State C Γ')} {g : Semantics.State × α → Res Semantics.State}
    (hfg : ∀ σ τ a, Agree ns σ τ → (∀ z, z ∉ B → lookupBy z τ.env = lookupBy z τ₀.env) →
      RunRel ns' B₂ τ (f (σ, a)) (g (τ, a)))
    (h₁ : ∀ z ∈ B, z ∈ B') (h₂ : ∀ z ∈ B₂, z ∈ B') :
    RunRel ns' B' τ₀ (x >>= f) (y >>= g) := by
  match x, y, hxy with
  | .error _, .error _, h => exact h
  | .ok (σ, a), .ok (τ, b), ⟨hab, hag, hf⟩ =>
    subst hab
    have h := hfg σ τ a hag hf
    revert h
    show RunRel ns' B₂ τ (f (σ, a)) (g (τ, a)) → RunRel ns' B' τ₀ (f (σ, a)) (g (τ, a))
    match f (σ, a), g (τ, a) with
    | .error _, .error _ => exact id
    | .ok _, .ok _ => exact fun ⟨hag', hf'⟩ => ⟨hag', fun z hz =>
        (hf' z (fun h => hz (h₂ z h))).trans (hf z (fun h => hz (h₁ z h)))⟩
    | .ok _, .error _ => exact False.elim
    | .error _, .ok _ => exact False.elim

end RunRelA

/-! ## Expressions read alike -/

section Eval

variable {Γ : Ctx} {ns : List Var} {σ : State C Γ} {τ : Semantics.State}

theorem Simple.eval_erase (hag : Agree ns σ τ) {p : PrimTy} :
    (s : Simple C Γ p) → Solidity.Simple.eval τ (s.erase ns) = s.eval σ
  | .lit .. => rfl
  | .bool _ => rfl
  | .local i => by
    simp only [Simple.erase, Solidity.Simple.eval, hag.getEnv i, Simple.eval]
    rfl
  | .env k _ => by simp only [Simple.erase, Solidity.Simple.eval, hag.envVal k, Simple.eval]

theorem aliasPath_erase (hag : Agree ns σ τ) {R : RefTy} (i : Idx Γ (.alias R)) :
    Solidity.aliasPath τ (i.name ns) = aliasPath σ i := by
  simp only [Solidity.aliasPath, hag.getEnv i, aliasPath]
  generalize (Env.get i σ.env : Option (Name × List Seg)) = v
  rcases v with _ | ⟨r, segs⟩ <;> rfl

mutual

theorem SPath.resolve_erase (hag : Agree ns σ τ) :
    {T : Ty} → (p : SPath C Γ T) → Solidity.SPath.resolve τ (p.erase ns) = p.resolve σ
  | _, .alias i => aliasPath_erase hag i
  | _, .loc l => l.resolve_erase hag

theorem Loc.resolve_erase (hag : Agree ns σ τ) :
    {T : Ty} → (l : Loc C Γ T) → Solidity.Loc.resolve τ (l.erase ns) = l.resolve σ
  | _, .root .. => rfl
  | _, .field b _ _ => by
    simp only [Loc.erase, Solidity.Loc.resolve, b.resolve_erase hag, Loc.resolve]
  | _, .index _ b i => by
    simp only [Loc.erase, Solidity.Loc.resolve, b.resolve_erase hag, i.eval_erase hag,
      hag.checkIndex, Loc.resolve]

theorem MPath.mval_erase (hag : Agree ns σ τ) :
    {T : Ty} → (p : MPath C Γ T) → Solidity.MPath.mval τ (p.erase ns) = p.mval σ
  | _, .var i _ => by
    simp only [MPath.erase, Solidity.MPath.mval, hag.getEnv i, MPath.mval, memRef]
    cases Env.get i σ.env <;> rfl
  | _, .loc l => l.read_erase hag

theorem MLoc.read_erase (hag : Agree ns σ τ) :
    {T : Ty} → (l : MLoc C Γ T) → Solidity.MLoc.read τ (l.erase ns) = l.read σ
  | _, .field b _ _ => by
    simp only [MLoc.erase, Solidity.MLoc.read, b.mval_erase hag, hag.getObj, MLoc.read]
    rfl
  | _, .index _ b i => by
    simp only [MLoc.erase, Solidity.MLoc.read, b.mval_erase hag, i.eval_erase hag, hag.getObj,
      MLoc.read]
    rfl

theorem Val.eval_erase (hag : Agree ns σ τ) :
    {p : PrimTy} → (v : Val C Γ p) → Solidity.Val.eval τ (v.erase ns) = v.eval σ
  | _, .simple s => s.eval_erase hag
  | _, .read l => by
    simp only [Val.erase, Solidity.Val.eval, l.resolve_erase hag, hag.findStorage, Val.eval]
  | _, .binop _ _ _ a b => by
    simp only [Val.erase, Solidity.Val.eval, a.eval_erase hag, b.eval_erase hag, Val.eval]
  | _, .unop _ _ _ a => by
    simp only [Val.erase, Solidity.Val.eval, a.eval_erase hag, Val.eval]
  | _, .ternary c a b => by
    simp only [Val.erase, Solidity.Val.eval, c.eval_erase hag, a.eval_erase hag,
      b.eval_erase hag, Val.eval]
  | _, .readMem l => by
    simp only [Val.erase, Solidity.Val.eval, l.read_erase hag, Val.eval]
  | _, .len b _ => by
    simp only [Val.erase, Solidity.Val.eval, b.resolve_erase hag, hag.arrayLen, Val.eval]
  | _, .mlen b _ => by
    simp only [Val.erase, Solidity.Val.eval, b.mval_erase hag, hag.memArrayLen, Val.eval]

end

theorem Src.value_erase (hag : Agree ns σ τ) {T : Ty} :
    (r : Src C Γ T) → Solidity.Src.value τ (r.erase ns) = r.value σ
  | .val v => by simp only [Src.erase, Solidity.Src.value, v.eval_erase hag, Src.value]
  | .copy p _ => by
    simp only [Src.erase, Solidity.Src.value, p.resolve_erase hag, hag.findStorage, Src.value]

theorem Src.pushVal_erase (hag : Agree ns σ τ) {T : Ty} (v : Option (Src C Γ T)) :
    Solidity.Src.pushVal τ (v.map (Src.erase ns)) = Src.pushVal σ v := by
  funext slot
  cases v with
  | none => rfl
  | some r => simp only [Option.map_some, Solidity.Src.pushVal, r.value_erase hag, Src.pushVal]

theorem MSrc.mval_erase (hag : Agree ns σ τ) {T : Ty} :
    (r : MSrc C Γ T) → Solidity.MSrc.mval τ (r.erase ns) = r.mval σ
  | .val v => by simp only [MSrc.erase, Solidity.MSrc.mval, v.eval_erase hag, MSrc.mval]
  | .ref p => by simp only [MSrc.erase, Solidity.MSrc.mval, p.mval_erase hag, MSrc.mval]

theorem MLoc.addr_erase (hag : Agree ns σ τ) {T : Ty} :
    (l : MLoc C Γ T) → Solidity.MLoc.addr τ (l.erase ns) = l.addr σ
  | .field b _ _ => by simp only [MLoc.erase, Solidity.MLoc.addr, b.mval_erase hag, MLoc.addr]
  | .index _ b i => by
    simp only [MLoc.erase, Solidity.MLoc.addr, b.mval_erase hag, i.eval_erase hag, MLoc.addr]

theorem ExtCall.key_erase (hag : Agree ns σ τ) (c : ExtCall C Γ) :
    Solidity.ExtCall.key τ (c.erase ns) = c.key σ := by
  have hargs : ∀ as : List (ExtArg C Γ),
      (as.map (ExtArg.erase ns)).mapM (fun a => Solidity.Simple.eval τ a.2) =
        as.mapM (fun a => a.2.eval σ) := by
    intro as
    induction as with
    | nil => rfl
    | cons a as ih =>
      simp only [List.map_cons, List.mapM_cons, ExtArg.erase, a.2.eval_erase hag, ih]
  simp only [ExtCall.erase, Solidity.ExtCall.key, c.addr.eval_erase hag, hargs, ExtCall.key]

end Eval

/-! ## Effects alike -/

section Effects

variable {Γ : Ctx} {ns B : List Var} {σ : State C Γ} {τ : Semantics.State}

theorem MLoc.write_erase (hag : Agree ns σ τ) (mv : MVal) {T : Ty} :
    (l : MLoc C Γ T) → RunRel ns B τ (l.write σ mv) (Solidity.MLoc.write τ mv (l.erase ns))
  | .field b f _ => by
    simp only [MLoc.erase, Solidity.MLoc.write, b.mval_erase hag, MLoc.write]
    exact RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun id _ =>
      RunRel.glob hag (memWriteField_nat id f mv)
  | .index _ b i => by
    simp only [MLoc.erase, Solidity.MLoc.write, b.mval_erase hag, i.eval_erase hag, MLoc.write]
    exact RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun id _ =>
      RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun iv _ =>
      RunRel.glob hag (memWriteIndex_nat id iv mv)

theorem OpLoc.store_erase (hag : Agree ns σ τ) (hB : ∀ y ∈ ns, y ∈ B) (op : BinOp) {p : PrimTy} :
    (l : OpLoc C Γ p) → (v : Value) →
      RunRel ns B τ (l.store σ op v) (Solidity.OpLoc.store τ op (l.erase ns) v)
  | .local i, v => by
    simp only [OpLoc.erase, Solidity.OpLoc.store, Solidity.opLocal, hag.getEnv i, OpLoc.store,
      opLocal]
    exact RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun new _ =>
      RunRel.ok_setLocal hag i new (hB _ (Idx.name_mem i ns hag.len))
  | .root .., v => RunRel.glob hag (opStore_nat _ _ _ _ _)
  | .field b f h, v => by
    simp only [OpLoc.erase, Solidity.OpLoc.store, OpLoc.store]
    rw [show Solidity.Loc.field (b.erase ns) f h = (Loc.field b f h).erase ns from rfl,
      Loc.resolve_erase hag]
    exact RunRel.bind_pure _ fun _ _ => RunRel.glob hag (opStore_nat _ _ _ _ _)
  | .index it b i, v => by
    simp only [OpLoc.erase, Solidity.OpLoc.store, OpLoc.store]
    rw [show Solidity.Loc.index it (b.erase ns) (.simple (i.erase ns)) =
      (Loc.index it b (.simple i)).erase ns from rfl, Loc.resolve_erase hag]
    exact RunRel.bind_pure _ fun _ _ => RunRel.glob hag (opStore_nat _ _ _ _ _)
  | .mfield b f _, v => by
    simp only [OpLoc.erase, Solidity.OpLoc.store, b.mval_erase hag, OpLoc.store]
    exact RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun _ _ => RunRel.glob hag (opMem_nat _ _ _ _)
  | .mindex _ b i, v => by
    simp only [OpLoc.erase, Solidity.OpLoc.store, b.mval_erase hag, i.eval_erase hag, OpLoc.store]
    exact RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun _ _ =>
      RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun _ _ => RunRel.glob hag (opMem_nat _ _ _ _)

theorem RunRelA.bind_pure {α β : Type} {τ₀ : Semantics.State} (x : Res β)
    {f : β → Res (State C Γ × α)} {g : β → Res (Semantics.State × α)}
    (h : ∀ a, x = .ok a → RunRelA ns B τ₀ (f a) (g a)) :
    RunRelA ns B τ₀ (x >>= f) (x >>= g) := by
  cases x with
  | error e => exact (rfl : e = e)
  | ok a => exact h a rfl

theorem RunRelA.glob (hag : Agree ns σ τ) {α : Type} {f : Semantics.State → Res (Semantics.State × α)}
    (hf : NaturalA f) :
    RunRelA ns B τ ((fun p => (σ.withGlob p.1, p.2)) <$> f σ.glob) (f τ) := by
  rw [hag.opA hf]
  cases f σ.glob with
  | error _ => exact (rfl : _ = _)
  | ok p => exact ⟨rfl, hag.withGlob p.1, fun _ _ => rfl⟩

theorem OpLoc.bump_erase (hag : Agree ns σ τ) (hB : ∀ y ∈ ns, y ∈ B) (op : IncDec) {p : PrimTy} :
    (l : OpLoc C Γ p) → RunRelA ns B τ (l.bump σ op) (Solidity.OpLoc.bump τ op (l.erase ns))
  | .local i => by
    simp only [OpLoc.erase, Solidity.OpLoc.bump, Solidity.bumpLocal, hag.getEnv i, OpLoc.bump,
      bumpLocal]
    exact RunRelA.bind_pure _ fun _ _ => RunRelA.bind_pure _ fun new _ =>
      ⟨rfl, hag.setLocal i new, frame_setEnv (hB _ (Idx.name_mem i ns hag.len))⟩
  | .root .. => RunRelA.glob hag (bumpStore_nat _ _ _ _)
  | .field b f h => by
    simp only [OpLoc.erase, Solidity.OpLoc.bump, OpLoc.bump]
    rw [show Solidity.Loc.field (b.erase ns) f h = (Loc.field b f h).erase ns from rfl,
      Loc.resolve_erase hag]
    exact RunRelA.bind_pure _ fun _ _ => RunRelA.glob hag (bumpStore_nat _ _ _ _)
  | .index it b i => by
    simp only [OpLoc.erase, Solidity.OpLoc.bump, OpLoc.bump]
    rw [show Solidity.Loc.index it (b.erase ns) (.simple (i.erase ns)) =
      (Loc.index it b (.simple i)).erase ns from rfl, Loc.resolve_erase hag]
    exact RunRelA.bind_pure _ fun _ _ => RunRelA.glob hag (bumpStore_nat _ _ _ _)
  | .mfield b f _ => by
    simp only [OpLoc.erase, Solidity.OpLoc.bump, b.mval_erase hag, OpLoc.bump]
    exact RunRelA.bind_pure _ fun _ _ => RunRelA.bind_pure _ fun _ _ =>
      RunRelA.glob hag (bumpMem_nat _ _ _)
  | .mindex _ b i => by
    simp only [OpLoc.erase, Solidity.OpLoc.bump, b.mval_erase hag, i.eval_erase hag, OpLoc.bump]
    exact RunRelA.bind_pure _ fun _ _ => RunRelA.bind_pure _ fun _ _ =>
      RunRelA.bind_pure _ fun _ _ => RunRelA.bind_pure _ fun _ _ =>
      RunRelA.glob hag (bumpMem_nat _ _ _)

/-- A memory local bound to what `r` names: the scoped evaluation, then what
the scoped run does with it, against the untyped binding. -/
theorem MRhs.bind_erase (hag : Agree ns σ τ) {R : RefTy} (r : MRhs C Γ R) (x : Var)
    {Γ' : Ctx} {ns' B' : List Var} {k : State C Γ × Nat → Res (State C Γ')}
    (hk : ∀ σ' id τ', Agree ns σ' τ' → τ'.env = τ.env →
      RunRel ns' B' τ (k (σ', id)) (.ok (τ'.setEnv x (.mref id)))) :
    RunRel ns' B' τ (r.eval σ >>= k) (Solidity.MRhs.bind τ x (r.erase ns)) := by
  cases r with
  | alias p =>
    simp only [MRhs.erase, Solidity.MRhs.bind, p.mval_erase hag, MRhs.eval, bind_assoc, pure_bind]
    exact RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun id _ => hk σ id τ hag rfl
  | copy p _ =>
    simp only [MRhs.erase, Solidity.MRhs.bind, p.resolve_erase hag, hag.findStorage, MRhs.eval,
      bind_assoc, pure_bind]
    exact RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun sv _ =>
      RunRel.bind_globA (f := fun s => copyStToM s sv) hag (fun s e => copyStToM_nat s e sv) fun s mv _ =>
      RunRel.bind_pure _ fun id _ => hk _ id _ (hag.withGlob s) rfl
  | newArr n _ =>
    simp only [MRhs.erase, Solidity.MRhs.bind, n.eval_erase hag, MRhs.eval, bind_assoc, pure_bind]
    exact RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun _ _ =>
      RunRel.bind_globA (f := fun s => copyStToM s _) hag (fun s e => copyStToM_nat s e _) fun s mv _ =>
      RunRel.bind_pure _ fun id _ => hk _ id _ (hag.withGlob s) rfl

/-- A storage alias bound to what `r` names. -/
theorem ARhs.bind_erase (hag : Agree ns σ τ) {R : RefTy} (r : ARhs C Γ R) (x : Var)
    {Γ' : Ctx} {ns' B' : List Var} {k : State C Γ × (Name × List Seg) → Res (State C Γ')}
    (hk : ∀ σ' q τ', Agree ns σ' τ' → τ'.env = τ.env →
      RunRel ns' B' τ (k (σ', q)) (.ok (τ'.setEnv x (.spath q.1 q.2)))) :
    RunRel ns' B' τ (r.eval σ >>= k) (Solidity.ARhs.bind τ x (r.erase ns)) := by
  cases r with
  | path p =>
    simp only [ARhs.erase, Solidity.ARhs.bind, p.resolve_erase hag, ARhs.eval, bind_assoc,
      pure_bind]
    exact RunRel.bind_pure _ fun q _ => hk σ q τ hag rfl
  | push b _ =>
    simp only [ARhs.erase, Solidity.ARhs.bind, b.resolve_erase hag, ARhs.eval, bind_assoc,
      pure_bind]
    exact RunRel.bind_pure _ fun q _ =>
      RunRel.bind_globA hag (pushPlaceAt_nat _ _ _) fun s n _ =>
      hk _ (q.1, q.2 ++ [.at n]) _ (hag.withGlob s) rfl

end Effects

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
theorem Agree.erase {ns : List Var} (σ : State C Γ) (hnd : ns.Nodup) (hlen : ns.length = Γ.length) :
    Agree ns σ (σ.erase ns) where
  len := hlen
  nodup := hnd
  glob := rfl
  env _ hm := lookupBy_of_mem_nodup (l := Env.erase ns σ.env)
    (by rw [Env.erase_keys ns σ.env hlen]; exact hnd) hm

end ErasedState

end Solidity.Core
