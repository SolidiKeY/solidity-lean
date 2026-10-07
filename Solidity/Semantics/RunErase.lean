import Solidity.Semantics.Core
import Solidity.Semantics.Agree

/-!
# The bridge: a scoped run is the untyped run of its erasure

`run_erase` (`docs/intrinsic.md`, M3): running `P.erase ns` with
`Semantics.lean`'s interpreter from the erased state `σ.erase ns` agrees with
running `P` with `Semantics/Core.lean`'s from `σ`, up to the locals the scoped
run pops at the ends of its scopes, which the untyped run keeps
(`EnvAgreeExcept` off `Prog.popped`, `Semantics/Agree.lean`).

The erasure is faithful only when names do not clash: the untyped
environment is one map from names to bindings, so a local declared under a
name in scope overwrites the outer one, where the scoped run shadows it.
`Prog.Fresh out ns P` says no binder of `P` reuses a name in scope (`ns`) or
of an enclosing frame (`out`), and that a call's arguments are separated, as
`erase` needs to write the call as `Syntax.lean`'s (the elaborator's names
are fresh, so its programs are).  A scope's locals may be redeclared after
it ends (a loop's body every iteration): the untyped run overwrites the
stale binding, which nothing read.

The proof is one invariant, `Agree ns σ τ`: the global parts are equal, and
every local of `σ` is bound in `τ` under its name, encoded (`LTy.enc`).
`τ` may bind more, the popped locals among them.  `RunRel` relates two
outcomes: the same halt, or states in `Agree` whose bindings off the
statement's names (`ns` and `Stmt.binders`) are untouched, which is what a
call's caller needs of its body.  The global operations are shared: each is
natural in the locals (`*_withEnv`), so the run on `σ.glob` and on `τ` agree.
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
  | .mem _, id => .mref id
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
    simp only [MPath.erase, Solidity.MPath.mval, hag.getEnv i, MPath.mval]
    rfl
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

/-! ## Statements -/

section Stmts

variable {Γ : Ctx} {ns B : List Var} {σ : State C Γ} {τ τ₀ : Semantics.State}

namespace RunRel

theorem env_eq {Γ' : Ctx} {ns' : List Var} {τ₁ τ₂ : Semantics.State} (h : τ₁.env = τ₂.env) :
    {x : Res (State C Γ')} → {y : Res Semantics.State} → RunRel ns' B τ₁ x y → RunRel ns' B τ₂ x y
  | .error _, .error _, hr => hr
  | .ok _, .ok _, ⟨hag, hf⟩ => ⟨hag, fun z hz => (hf z hz).trans (by rw [h])⟩

/-- A global step from a state whose global part is `s`. -/
theorem glob' {s : Semantics.State} {e : List (Var × Binding)} (hag : Agree ns σ (withLocals s e))
    (he : e = τ₀.env) {f : Semantics.State → Res Semantics.State} (hf : Natural f) :
    RunRel ns B τ₀ (σ.withGlob <$> f s) (f (withLocals s e)) := by
  rw [hf s e]
  cases f s with
  | error _ => exact (rfl : _ = _)
  | ok s' => exact ⟨hag.withGlob s', fun _ _ => by rw [← he]⟩

theorem ok_setLocal' (hag : Agree ns σ τ) (henv : τ.env = τ₀.env) {t : LTy} (i : Idx Γ t)
    (v : t.Denote C) (hB : i.name ns ∈ B) :
    RunRel ns B τ₀ (.ok (σ.setLocal i v)) (.ok (τ.setEnv (i.name ns) (t.enc C v))) :=
  ⟨hag.setLocal i v, fun y hy => (frame_setEnv hB y hy).trans (by rw [henv])⟩

theorem ok_push' (hag : Agree ns σ τ) (henv : τ.env = τ₀.env) {x : Var} (hx : x ∉ ns) {t : LTy}
    (v : t.Denote C) (hB : x ∈ B) :
    RunRel (x :: ns) B τ₀ (.ok (σ.push v)) (.ok (τ.setEnv x (t.enc C v))) :=
  ⟨hag.push hx v, fun y hy => (frame_setEnv hB y hy).trans (by rw [henv])⟩

end RunRel

theorem _root_.Solidity.Prog.run_single (τ : Semantics.State) (u : Solidity.Stmt C) :
    Solidity.Prog.run τ [u] = Solidity.Stmt.run τ u := by
  simp only [Solidity.Prog.run]
  cases Solidity.Stmt.run τ u <;> rfl

end Stmts

/-! ## Names a program binds, and freshness -/

mutual

/-- The names a statement binds anywhere inside it: its declarations, a
branch's or a body's, a call's frame, a `try`'s returned values and code.
The untyped run writes no other name, but those of the locals in scope. -/
def Stmt.binders : {Γ Γ' : Ctx} → Stmt C Γ Γ' → List Var
  | _, _, .declLocal _ x _ => [x]
  | _, _, .declStorage _ x _ => [x]
  | _, _, .declMem _ x .. => [x]
  | _, _, .ite _ thn els => Prog.binders thn ++ Prog.binders els
  | _, _, .call _ args ret body => ret.names ++ args.names ++ Prog.binders body
  | _, _, .tryCall _ rets ok err code pnc other =>
    rets.names ++ Prog.binders ok ++ Prog.binders err ++ code.names ++ Prog.binders pnc ++
      Prog.binders other
  | _, _, .loop _ _ body => Prog.binders body
  | _, _, .block body => Prog.binders body
  | _, _, .assign .. | _, _, .rebind .. | _, _, .assignLocal .. | _, _, .opAssign ..
  | _, _, .incDec .. | _, _, .assignIncDec .. | _, _, .push .. | _, _, .pop ..
  | _, _, .transfer .. | _, _, .send .. | _, _, .rebindMem .. | _, _, .assignFromMem ..
  | _, _, .assignMem .. | _, _, .delete .. | _, _, .deleteMem .. | _, _, .assignNew ..
  | _, _, .require .. | _, _, .assert .. | _, _, .revert => []

def Prog.binders : {Γ Γ' : Ctx} → Prog C Γ Γ' → List Var
  | _, _, .nil => []
  | _, _, .cons s P => Stmt.binders s ++ Prog.binders P

end

/-- The names of the context a block leaves. -/
def Prog.outNames : {Γ Γ' : Ctx} → List Var → Prog C Γ Γ' → List Var
  | _, _, ns, .nil => ns
  | _, _, ns, .cons s P => Prog.outNames (s.outNames ns) P

mutual

/-- No binder of the statement reuses a name in scope (`ns`) or of an
enclosing frame (`out`), and a call's arguments are separated: what makes
the untyped run, one map from names to bindings, follow the scoped one. -/
def Stmt.Fresh (out : List Var) : {Γ Γ' : Ctx} → List Var → Stmt C Γ Γ' → Prop
  | _, _, ns, .declLocal _ x _ => x ∉ ns ∧ x ∉ out
  | _, _, ns, .declStorage _ x _ => x ∉ ns ∧ x ∉ out
  | _, _, ns, .declMem _ x .. => x ∉ ns ∧ x ∉ out
  | _, _, ns, .ite _ thn els => Prog.Fresh out ns thn ∧ Prog.Fresh out ns els
  | _, _, ns, .call _ args ret body =>
    (ret.names ++ args.names).Nodup ∧ (∀ y ∈ ret.names ++ args.names, y ∉ ns ∧ y ∉ out) ∧
      Arg.separatedFrom [] (args.erase ns) = true ∧
      Prog.Fresh (ns ++ out) (ret.names ++ args.names) body
  | _, _, ns, .tryCall _ rets ok err code pnc other =>
    rets.names.Nodup ∧ (∀ y ∈ rets.names, y ∉ ns ∧ y ∉ out) ∧ Prog.Fresh out (rets.names ++ ns) ok ∧
      Prog.Fresh out ns err ∧ (∀ y ∈ code.names, y ∉ ns ∧ y ∉ out) ∧
      Prog.Fresh out (code.names ++ ns) pnc ∧ Prog.Fresh out ns other
  | _, _, ns, .loop _ _ body => Prog.Fresh out ns body
  | _, _, ns, .block body => Prog.Fresh out ns body
  | _, _, _, .assign .. | _, _, _, .rebind .. | _, _, _, .assignLocal .. | _, _, _, .opAssign ..
  | _, _, _, .incDec .. | _, _, _, .assignIncDec .. | _, _, _, .push .. | _, _, _, .pop ..
  | _, _, _, .transfer .. | _, _, _, .send .. | _, _, _, .rebindMem .. | _, _, _, .assignFromMem ..
  | _, _, _, .assignMem .. | _, _, _, .delete .. | _, _, _, .deleteMem .. | _, _, _, .assignNew ..
  | _, _, _, .require .. | _, _, _, .assert .. | _, _, _, .revert => True

def Prog.Fresh (out : List Var) : {Γ Γ' : Ctx} → List Var → Prog C Γ Γ' → Prop
  | _, _, _, .nil => True
  | _, _, ns, .cons s P => Stmt.Fresh out ns s ∧ Prog.Fresh out (s.outNames ns) P

end

mutual

/-- A fresh statement binds no name of an enclosing frame. -/
theorem Stmt.binders_not_out {out : List Var} : {Γ Γ' : Ctx} → {ns : List Var} →
    (s : Stmt C Γ Γ') → s.Fresh out ns → ∀ y ∈ s.binders, y ∉ out
  | _, _, _, .declLocal .., h, y, hy | _, _, _, .declStorage .., h, y, hy
  | _, _, _, .declMem .., h, y, hy => by
    simp only [Stmt.binders, List.mem_singleton] at hy
    exact hy ▸ h.2
  | _, _, _, .ite _ thn els, h, y, hy => by
    simp only [Stmt.binders, List.mem_append] at hy
    rcases hy with hy | hy
    · exact Prog.binders_not_out thn h.1 y hy
    · exact Prog.binders_not_out els h.2 y hy
  | _, _, _, .call _ args ret body, h, y, hy => by
    simp only [Stmt.binders, List.mem_append] at hy
    rcases hy with (hy | hy) | hy
    · exact (h.2.1 y (List.mem_append_left _ hy)).2
    · exact (h.2.1 y (List.mem_append_right _ hy)).2
    · exact fun ho => Prog.binders_not_out body h.2.2.2 y hy (List.mem_append_right _ ho)
  | _, _, _, .tryCall _ rets ok err code pnc other, h, y, hy => by
    simp only [Stmt.binders, List.mem_append] at hy
    rcases hy with ((((hy | hy) | hy) | hy) | hy) | hy
    · exact (h.2.1 y hy).2
    · exact Prog.binders_not_out ok h.2.2.1 y hy
    · exact Prog.binders_not_out err h.2.2.2.1 y hy
    · exact (h.2.2.2.2.1 y hy).2
    · exact Prog.binders_not_out pnc h.2.2.2.2.2.1 y hy
    · exact Prog.binders_not_out other h.2.2.2.2.2.2 y hy
  | _, _, _, .loop _ _ body, h, y, hy => Prog.binders_not_out body h y hy
  | _, _, _, .block body, h, y, hy => Prog.binders_not_out body h y hy
  | _, _, _, .assign .., _, _, hy | _, _, _, .rebind .., _, _, hy
  | _, _, _, .assignLocal .., _, _, hy | _, _, _, .opAssign .., _, _, hy
  | _, _, _, .incDec .., _, _, hy | _, _, _, .assignIncDec .., _, _, hy
  | _, _, _, .push .., _, _, hy | _, _, _, .pop .., _, _, hy
  | _, _, _, .transfer .., _, _, hy | _, _, _, .send .., _, _, hy
  | _, _, _, .rebindMem .., _, _, hy | _, _, _, .assignFromMem .., _, _, hy
  | _, _, _, .assignMem .., _, _, hy | _, _, _, .delete .., _, _, hy
  | _, _, _, .deleteMem .., _, _, hy | _, _, _, .assignNew .., _, _, hy
  | _, _, _, .require .., _, _, hy | _, _, _, .assert .., _, _, hy
  | _, _, _, .revert, _, _, hy => absurd hy List.not_mem_nil

theorem Prog.binders_not_out {out : List Var} : {Γ Γ' : Ctx} → {ns : List Var} →
    (P : Prog C Γ Γ') → P.Fresh out ns → ∀ y ∈ P.binders, y ∉ out
  | _, _, _, .nil, _, _, hy => absurd hy List.not_mem_nil
  | _, _, _, .cons s P, h, y, hy => by
    simp only [Prog.binders, List.mem_append] at hy
    rcases hy with hy | hy
    · exact Stmt.binders_not_out s h.1 y hy
    · exact Prog.binders_not_out P h.2 y hy

end

/-- What a call leaves its caller: names in its frame. -/
theorem CallRet.outNames_suffix {Γ rs Γ' : Ctx} (ns : List Var) (ret : CallRet Γ rs Γ') :
    ∃ qs, ret.outNames ns = qs ++ ns ∧ ∀ y ∈ qs, y ∈ ret.names := by
  cases ret with
  | none => exact ⟨[], rfl, fun _ h => absurd h List.not_mem_nil⟩
  | val => exact ⟨[], rfl, fun _ h => absurd h List.not_mem_nil⟩
  | rets bs => exact ⟨bs.names, rfl, fun _ h => h⟩
  | mem _ r _ _ => exact ⟨[r], rfl, fun _ h => h⟩

/-- A statement pushes its own binders. -/
theorem Stmt.outNames_suffix {Γ Γ' : Ctx} (ns : List Var) (s : Stmt C Γ Γ') :
    ∃ qs, s.outNames ns = qs ++ ns ∧ ∀ y ∈ qs, y ∈ s.binders := by
  cases s with
  | declLocal _ x _ => exact ⟨[x], rfl, fun _ h => h⟩
  | declStorage _ x _ => exact ⟨[x], rfl, fun _ h => h⟩
  | declMem _ x _ _ _ => exact ⟨[x], rfl, fun _ h => h⟩
  | call _ args ret body =>
    obtain ⟨qs, hq, hm⟩ := ret.outNames_suffix ns
    exact ⟨qs, hq, fun y hy => List.mem_append_left _ (List.mem_append_left _ (hm y hy))⟩
  | _ => exact ⟨[], rfl, fun _ h => absurd h List.not_mem_nil⟩

theorem Prog.outNames_suffix : {Γ Γ' : Ctx} → (ns : List Var) → (P : Prog C Γ Γ') →
    ∃ qs, P.outNames ns = qs ++ ns ∧ ∀ y ∈ qs, y ∈ P.binders
  | _, _, _, .nil => ⟨[], rfl, fun _ h => absurd h List.not_mem_nil⟩
  | _, _, ns, .cons s P => by
    obtain ⟨qs₁, h₁, m₁⟩ := s.outNames_suffix ns
    obtain ⟨qs₂, h₂, m₂⟩ := Prog.outNames_suffix (s.outNames ns) P
    refine ⟨qs₂ ++ qs₁, ?_, fun y hy => ?_⟩
    · show P.outNames (s.outNames ns) = _
      rw [h₂, h₁, List.append_assoc]
    · rcases List.mem_append.1 hy with hy | hy
      · exact List.mem_append_right _ (m₂ y hy)
      · exact List.mem_append_left _ (m₁ y hy)

/-- The bridge for one statement: its scoped run, against the untyped run
of its erasure, from agreeing states. -/
abbrev Stmt.ErasesAt {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (ns : List Var) (σ : State C Γ)
    (τ : Semantics.State) : Prop :=
  RunRel (s.outNames ns) (ns ++ s.binders) τ (s.run σ) (Solidity.Prog.run τ (s.erase ns))

/-- The bridge for a block. -/
abbrev Prog.ErasesAt {Γ Γ' : Ctx} (P : Prog C Γ Γ') (ns : List Var) (σ : State C Γ)
    (τ : Semantics.State) : Prop :=
  RunRel (P.outNames ns) (ns ++ P.binders) τ (P.run σ) (Solidity.Prog.run τ (P.erase ns))

theorem Stmt.ErasesAt.of_leaf {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {ns : List Var} {σ : State C Γ}
    {τ : Semantics.State} {u : Solidity.Stmt C} (he : s.erase ns = [u])
    (h : RunRel (s.outNames ns) (ns ++ s.binders) τ (s.run σ) (Solidity.Stmt.run τ u)) :
    s.ErasesAt ns σ τ := by
  unfold Stmt.ErasesAt
  rw [he, Solidity.Prog.run_single]
  exact h

/-! ## The statements without sub-programs -/

section Leaves

variable {Γ : Ctx} {ns : List Var} {σ : State C Γ} {τ : Semantics.State}

/-- The leaves' common preamble: the scoped step and the untyped statement. -/
macro "leaf_pre" : tactic => `(tactic| dsimp only [Stmt.run, Stmt.runR, Stmt.outNames, Stmt.binders])

theorem Stmt.erases_assign (hag : Agree ns σ τ) {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    (Stmt.assign l r).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Run.assign, Solidity.Stmt.run, r.value_erase hag, l.resolve_erase hag]
  exact RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun _ _ =>
    RunRel.glob hag (writeStorage_nat _ _ _))

theorem Stmt.erases_rebind (hag : Agree ns σ τ) {R : RefTy} (i : Idx Γ (.alias R))
    (r : ARhs C Γ R) : (Stmt.rebind i r).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Run.rebind, Solidity.Stmt.run]
  exact r.bind_erase hag _ fun σ' q τ' hag' he =>
    RunRel.ok_setLocal' hag' he i (some q) (List.mem_append_left _ (Idx.name_mem i ns hag.len)))

theorem Stmt.erases_assignLocal (hag : Agree ns σ τ) {p : PrimTy} (i : Idx Γ (.val p))
    (r : Val C Γ p) : (Stmt.assignLocal i r).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Run.assignLocal, Solidity.Stmt.run, r.eval_erase hag]
  exact RunRel.bind_pure _ fun v _ =>
    RunRel.ok_setLocal hag i v (List.mem_append_left _ (Idx.name_mem i ns hag.len)))

theorem Stmt.erases_declLocal (hag : Agree ns σ τ) (p : PrimTy) {x : Var} (hx : x ∉ ns)
    (init : Option (Val C Γ p)) : (Stmt.declLocal p x init).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  cases init with
  | none => exact RunRel.ok_push hag hx (t := .val p) _ (List.mem_append_right _ List.mem_cons_self)
  | some e =>
    simp only [Run.declLocal, Solidity.Stmt.run, Option.map_some, e.eval_erase hag]
    exact RunRel.bind_pure _ fun v _ =>
      RunRel.ok_push hag hx (t := .val p) v (List.mem_append_right _ List.mem_cons_self))

theorem Stmt.erases_declStorage (hag : Agree ns σ τ) (R : RefTy) {x : Var} (hx : x ∉ ns)
    (init : Option (ARhs C Γ R)) : (Stmt.declStorage R x init).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  cases init with
  | none =>
    exact RunRel.ok_push hag hx (t := LTy.alias R) Option.none
      (List.mem_append_right _ List.mem_cons_self)
  | some r =>
    simp only [Run.declStorage, Solidity.Stmt.run, Option.map_some]
    exact r.bind_erase hag _ fun σ' q τ' hag' he =>
      RunRel.ok_push' hag' he hx (t := .alias R) (some q)
        (List.mem_append_right _ List.mem_cons_self))

theorem Stmt.erases_opAssign (hag : Agree ns σ τ) {p : PrimTy} (op : BinOp) (hop) (hp)
    (l : OpLoc C Γ p) (r : Val C Γ p) : (Stmt.opAssign op hop hp l r).ErasesAt ns σ τ :=
  .of_leaf rfl (by
  leaf_pre
  simp only [Run.opAssign, Solidity.Stmt.run, r.eval_erase hag]
  exact RunRel.bind_pure _ fun v _ =>
    l.store_erase hag (fun _ h => List.mem_append_left _ h) op v)

theorem Stmt.erases_incDec (hag : Agree ns σ τ) {p : PrimTy} (op : IncDec) (hp)
    (l : OpLoc C Γ p) : (Stmt.incDec op hp l).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Run.incDec, Solidity.Stmt.run]
  exact RunRelA.bind (l.bump_erase hag (fun _ h => List.mem_append_left _ h) op)
    (fun _ _ _ hag' _ => RunRel.ok_refl hag') (fun _ h => h) (fun _ h => h))

theorem Stmt.erases_assignIncDec (hag : Agree ns σ τ) {p : PrimTy} (i : Idx Γ (.val p))
    (op : IncDec) (hp) (l : OpLoc C Γ p) (hs) : (Stmt.assignIncDec i op hp l hs).ErasesAt ns σ τ :=
  .of_leaf rfl (by
  leaf_pre
  simp only [Run.assignIncDec, Solidity.Stmt.run]
  exact RunRelA.bind (l.bump_erase hag (fun _ h => List.mem_append_left _ h) op)
    (fun _ _ v hag' _ => RunRel.ok_setLocal hag' i v
      (List.mem_append_left _ (Idx.name_mem i ns hag.len))) (fun _ h => h) (fun _ h => h))

theorem Stmt.erases_push (hag : Agree ns σ τ) {E : Ty} (b : SPath C Γ (.array E))
    (v : Option (Src C Γ E)) (hd) : (Stmt.push b v hd).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Run.push, Solidity.Stmt.run, b.resolve_erase hag, Src.pushVal_erase hag]
  exact RunRel.bind_pure _ fun _ _ => RunRel.glob hag (pushAt_nat _ _ _ _))

theorem Stmt.erases_pop (hag : Agree ns σ τ) {E : Ty} (b : SPath C Γ (.array E)) :
    (Stmt.pop b).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Run.pop, Solidity.Stmt.run, b.resolve_erase hag]
  exact RunRel.bind_pure _ fun _ _ => RunRel.glob hag (popAt_nat _ _ _))

theorem Stmt.erases_transfer (hag : Agree ns σ τ) (r a : Val C Γ .uint) :
    (Stmt.transfer r a).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Run.transfer, Solidity.Stmt.run, r.eval_erase hag, a.eval_erase hag]
  exact RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun _ _ =>
    RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun _ _ =>
    RunRel.glob hag (transferAt_nat _ _))

theorem Stmt.erases_send (hag : Agree ns σ τ) (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) :
    (Stmt.send pv r a).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Run.send, Solidity.Stmt.run, r.eval_erase hag, a.eval_erase hag]
  refine RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun addr _ =>
    RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun amt _ => ?_
  have hB : pv.name ns ∈ ns ++ [] := List.mem_append_left _ (Idx.name_mem pv ns hag.len)
  simp only [Solidity.sendAt, sendAt, hag.tx]
  split
  · exact (rfl : Halt.revert = Halt.revert)
  · have hpay : τ.pay addr amt = withLocals (σ.glob.pay addr amt) τ.env := by
      rw [← hag.glob]; rfl
    have hT := RunRel.ok_setLocal' (hag.withGlob (σ.glob.pay addr amt)) rfl pv (.bool true) hB
    have hF := RunRel.ok_setLocal hag pv (.bool false) hB
    rw [hpay]
    rcases lookupBy (sendKey addr amt) σ.tx.ext with _ | ⟨_ | _ | _ | _⟩
    · exact hT
    · exact hT
    · exact hF
    · exact hF
    · exact hF)

theorem Stmt.erases_declMem (hag : Agree ns σ τ) (R : RefTy) {x : Var} (hx : x ∉ ns)
    (init : Option (MRhs C Γ R)) (hd) (hm) : (Stmt.declMem R x init hd hm).ErasesAt ns σ τ :=
  .of_leaf rfl (by
  leaf_pre
  cases init with
  | none =>
    simp only [Run.declMem, Solidity.Stmt.run, Option.map_none]
    exact RunRel.bind_globA hag (allocDefault_nat R) fun s id _ =>
      RunRel.ok_push' (hag.withGlob s) rfl hx (t := .mem R) id
        (List.mem_append_right _ List.mem_cons_self)
  | some r =>
    simp only [Run.declMem, Solidity.Stmt.run, Option.map_some]
    exact r.bind_erase hag _ fun σ' id τ' hag' he =>
      RunRel.ok_push' hag' he hx (t := .mem R) id (List.mem_append_right _ List.mem_cons_self))

theorem Stmt.erases_rebindMem (hag : Agree ns σ τ) {R : RefTy} (i : Idx Γ (.mem R))
    (r : MRhs C Γ R) : (Stmt.rebindMem i r).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Run.rebindMem, Solidity.Stmt.run]
  exact r.bind_erase hag _ fun σ' id τ' hag' he =>
    RunRel.ok_setLocal' hag' he i id (List.mem_append_left _ (Idx.name_mem i ns hag.len)))

theorem Stmt.erases_assignFromMem (hag : Agree ns σ τ) {R : RefTy} (l : Loc C Γ (.ref R))
    (p : MPath C Γ (.ref R)) : (Stmt.assignFromMem l p).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Run.assignFromMem, Solidity.Stmt.run, p.mval_erase hag, l.resolve_erase hag,
    hag.copyMem]
  exact RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun _ _ =>
    RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun _ _ =>
    RunRel.glob hag (writeStorage_nat _ _ _))

theorem Stmt.erases_assignMem (hag : Agree ns σ τ) {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    (Stmt.assignMem l r).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Run.assignMem, Solidity.Stmt.run, r.mval_erase hag]
  exact RunRel.bind_pure _ fun mv _ => l.write_erase hag mv)

theorem Stmt.erases_delete (hag : Agree ns σ τ) {T : Ty} (l : Loc C Γ T) :
    (Stmt.delete l).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Run.delete, Solidity.Stmt.run, l.resolve_erase hag, hag.findStorage]
  exact RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun _ _ =>
    RunRel.glob hag (saveStorage_nat _ _ _))

theorem Stmt.erases_deleteMem (hag : Agree ns σ τ) {T : Ty} (p : MPath C Γ T) (hd) :
    (Stmt.deleteMem p hd).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  cases p with
  | var i _ =>
    simp only [Run.deleteMem, Solidity.Stmt.run, MPath.erase]
    exact RunRel.bind_globA hag (allocDefault_nat _) fun s id _ =>
      RunRel.ok_setLocal' (hag.withGlob s) rfl i id
        (List.mem_append_left _ (Idx.name_mem i ns hag.len))
  | loc l =>
    simp only [Run.deleteMem, Solidity.Stmt.run, MPath.erase, l.addr_erase hag]
    exact RunRel.bind_pure _ fun _ _ => RunRel.glob hag (memClear_nat _ _))

theorem Stmt.erases_assignNew (hag : Agree ns σ τ) {R : RefTy} (l : NewLhs C Γ R)
    (n : Simple C Γ .uint) (h) : (Stmt.assignNew l n h).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Run.assignNew, Solidity.Stmt.run, n.eval_erase hag]
  refine RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun k _ =>
    RunRel.bind_globA (f := fun s => copyStToM s (newArrVal R k)) hag
      (fun s e => copyStToM_nat s e _) fun s mv _ => RunRel.bind_pure _ fun id _ => ?_
  have hag' := hag.withGlob s
  cases l with
  | store l =>
    simp only [NewLhs.erase, copyMem_wl, l.resolve_erase hag']
    exact RunRel.bind_pure _ fun _ _ => RunRel.bind_pure _ fun _ _ =>
      RunRel.glob' hag' rfl (writeStorage_nat _ _ _)
  | mem l => exact RunRel.env_eq rfl (l.write_erase hag' _))

theorem Stmt.erases_require (hag : Agree ns σ τ) (c : Val C Γ .bool) :
    (Stmt.require c).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Solidity.Stmt.run, c.eval_erase hag]
  refine RunRel.bind_pure _ fun v _ => ?_
  cases v with
  | int _ => exact (rfl : Halt.stuck = Halt.stuck)
  | bool b =>
    cases b
    · exact (rfl : Halt.revert = Halt.revert)
    · exact RunRel.ok_refl hag)

theorem Stmt.erases_assert (hag : Agree ns σ τ) (c : Val C Γ .bool) :
    (Stmt.assert c).ErasesAt ns σ τ := .of_leaf rfl (by
  leaf_pre
  simp only [Solidity.Stmt.run, c.eval_erase hag]
  refine RunRel.bind_pure _ fun v _ => ?_
  cases v with
  | int _ => exact (rfl : Halt.stuck = Halt.stuck)
  | bool b =>
    cases b
    · exact (rfl : Halt.panic = Halt.panic)
    · exact RunRel.ok_refl hag)

theorem Stmt.erases_revert : (Stmt.revert : Stmt C Γ Γ).ErasesAt ns σ τ :=
  .of_leaf rfl (rfl : Halt.revert = Halt.revert)

end Leaves

/-! ## Loops in step -/

section Loops

/-- Two iterations in step: both running, related by `R`, or both done,
related by `Q`. -/
def StepRel₂ {α β : Type} (R : α → β → Prop) (Q : Res α → Res β → Prop) :
    α ⊕ Res α → β ⊕ Res β → Prop
  | .inl a, .inl b => R a b
  | .inr r, .inr r' => Q r r'
  | _, _ => False

theorem Loop.run_of_forall {α : Type} {body : α → Res α} {c : α → Res Value} {σ : α}
    (h : ∀ n r, Loop.iterN body c n σ ≠ .inr r) : Loop.run body c σ = .error .diverge := by
  have hex : ¬ ∃ r n, Loop.iterN body c n σ = .inr r := fun ⟨r, n, h'⟩ => h n r h'
  simp only [Loop.run, hex, dite_false]

/-- **A scoped loop and an untyped one run alike** when their iterations go in
step (`Solidity.Loop.run_rel`, across the two state types). -/
theorem Loop.run_rel₂ {α : Type} {body₁ : α → Res α} {c₁ : α → Res Value}
    {body₂ : Semantics.State → Res Semantics.State} {c₂ : Semantics.State → Res Value}
    {R : α → Semantics.State → Prop} {Q : Res α → Res Semantics.State → Prop}
    {σ : α} {σ' : Semantics.State} (h0 : R σ σ')
    (hstep : ∀ a b, R a b →
      StepRel₂ R Q (Loop.step body₁ c₁ a) (Solidity.Loop.step body₂ c₂ b))
    (hdiv : Q (.error .diverge) (.error .diverge)) :
    Q (Loop.run body₁ c₁ σ) (Solidity.Loop.run body₂ c₂ σ') := by
  have hiter : ∀ n a b, R a b →
      StepRel₂ R Q (Loop.iterN body₁ c₁ n a) (Solidity.Loop.iterN body₂ c₂ n b) := by
    intro n
    induction n with
    | zero => intro a b h; exact h
    | succ n ih =>
      intro a b h
      have hs := hstep a b h
      simp only [Loop.iterN, Solidity.Loop.iterN]
      revert hs
      cases Loop.step body₁ c₁ a <;> cases Solidity.Loop.step body₂ c₂ b <;>
        simp only [StepRel₂, false_imp_iff, imp_self] <;> exact ih _ _
  by_cases hex : ∃ r n, Loop.iterN body₁ c₁ n σ = .inr r
  · obtain ⟨r, n, h⟩ := hex
    have hn := hiter n σ σ' h0
    rw [h] at hn
    revert hn
    cases h' : Solidity.Loop.iterN body₂ c₂ n σ' with
    | inl _ => simp only [StepRel₂, false_imp_iff]
    | inr r' =>
      intro hq
      rw [Loop.run_of_iterN h, Solidity.Loop.run_of_iterN h']
      exact hq
  · have hσ : ∀ n r, Loop.iterN body₁ c₁ n σ ≠ .inr r := fun n r h => hex ⟨r, n, h⟩
    have hσ' : ∀ n r, Solidity.Loop.iterN body₂ c₂ n σ' ≠ .inr r := by
      intro n r h
      have hn := hiter n σ σ' h0
      rw [h] at hn
      revert hn
      cases h'' : Loop.iterN body₁ c₁ n σ with
      | inl _ => simp only [StepRel₂, false_imp_iff]
      | inr r'' => exact fun _ => hσ n r'' h''
    rw [Loop.run_of_forall hσ, Solidity.Loop.run_of_forall hσ']
    exact hdiv

end Loops

/-! ## The statements with sub-programs -/

section Scopes

variable {Γ : Ctx} {ns B : List Var} {τ₀ : Semantics.State}

/-- A scope's locals popped, the names of `ns` left. -/
theorem RunRel.pop {Δ : Ctx} (h : Ext Γ Δ) {ns' qs : List Var} (hns : ns.length = Γ.length)
    (hq : ns' = qs ++ ns) : {x : Res (State C Δ)} → {y : Res Semantics.State} →
      RunRel ns' B τ₀ x y → RunRel ns B τ₀ (x.map (State.drop h)) y
  | .error _, .error _, hr => hr
  | .ok _, .ok _, ⟨hag, hf⟩ => by
    subst hq
    have h₁ := hag.len
    have h₂ := h.length_eq
    simp only [List.length_append] at h₁
    exact ⟨hag.drop h (by omega), hf⟩

/-- A block's run, its locals popped, from its bridge. -/
theorem Prog.erases_pop {Γ₁ : Ctx} {ns : List Var} {σ : State C Γ} {τ : Semantics.State}
    (P : Prog C Γ Γ₁) (hns : ns.length = Γ.length) (ih : P.ErasesAt ns σ τ) :
    RunRel ns (ns ++ P.binders) τ ((P.run σ).map (State.drop P.ext))
      (Solidity.Prog.run τ (P.erase ns)) :=
  have ⟨_, hq, _⟩ := P.outNames_suffix ns
  RunRel.pop P.ext hns hq ih

variable {ns : List Var} {σ : State C Γ} {τ : Semantics.State}

theorem Stmt.erases_block {Γ₁ : Ctx} (hag : Agree ns σ τ) (body : Prog C Γ Γ₁)
    (ih : body.ErasesAt ns σ τ) : (Stmt.block body).ErasesAt ns σ τ :=
  body.erases_pop hag.len ih

theorem Stmt.erases_ite {Γ₁ Γ₂ : Ctx} (hag : Agree ns σ τ) (c : Val C Γ .bool)
    (thn : Prog C Γ Γ₁) (els : Prog C Γ Γ₂) (ih₁ : thn.ErasesAt ns σ τ)
    (ih₂ : els.ErasesAt ns σ τ) : (Stmt.ite c thn els).ErasesAt ns σ τ := .of_leaf rfl (by
  dsimp only [Stmt.run, Stmt.runR, Stmt.outNames, Stmt.binders]
  simp only [Run.ite, Solidity.Stmt.run, c.eval_erase hag]
  refine RunRel.bind_pure _ fun v _ => ?_
  cases v with
  | int _ => exact (rfl : Halt.stuck = Halt.stuck)
  | bool b =>
    cases b
    · exact (els.erases_pop hag.len ih₂).mono fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · exact List.mem_append_left _ hy
        · exact List.mem_append_right _ (List.mem_append_right _ hy)
    · exact (thn.erases_pop hag.len ih₁).mono fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · exact List.mem_append_left _ hy
        · exact List.mem_append_right _ (List.mem_append_left _ hy))

/-- One iteration of each, from agreeing states: the conditions read alike,
and the bodies run alike. -/
theorem Loop.step_rel {B : List Var} {τ b : Semantics.State} {a : State C Γ}
    {body₁ : State C Γ → Res (State C Γ)} {c₁ : State C Γ → Res Value}
    {body₂ : Semantics.State → Res Semantics.State} {c₂ : Semantics.State → Res Value}
    (hc : c₂ b = c₁ a) (hab : Agree ns a b)
    (hf : ∀ z, z ∉ B → lookupBy z b.env = lookupBy z τ.env)
    (hbody : RunRel ns B b (body₁ a) (body₂ b)) :
    StepRel₂ (fun a b => Agree ns a b ∧ ∀ z, z ∉ B → lookupBy z b.env = lookupBy z τ.env)
      (RunRel ns B τ) (Loop.step body₁ c₁ a) (Solidity.Loop.step body₂ c₂ b) := by
  simp only [Loop.step, Solidity.Loop.step, hc]
  cases c₁ a with
  | error e => exact (rfl : e = e)
  | ok v =>
    cases v with
    | int _ => exact (rfl : Halt.stuck = Halt.stuck)
    | bool b' =>
      cases b'
      · exact ⟨hab, hf⟩
      · revert hbody
        cases body₁ a <;> cases body₂ b
        · exact id
        · exact False.elim
        · exact False.elim
        · exact fun ⟨hag', hf'⟩ => ⟨hag', fun z hz => (hf' z hz).trans (hf z hz)⟩

theorem Stmt.erases_loop {Γ₁ : Ctx} (hag : Agree ns σ τ) (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) (ih : ∀ σ' τ', Agree ns σ' τ' → body.ErasesAt ns σ' τ') :
    (Stmt.loop a c body).ErasesAt ns σ τ := .of_leaf rfl (by
  dsimp only [Stmt.run, Stmt.runR, Stmt.outNames, Stmt.binders]
  simp only [Run.loop, Solidity.Stmt.run]
  refine Loop.run_rel₂ (R := fun a b => Agree ns a b ∧
      ∀ y, y ∉ ns ++ body.binders → lookupBy y b.env = lookupBy y τ.env)
    (Q := RunRel ns (ns ++ body.binders) τ) ⟨hag, fun _ _ => rfl⟩ ?_ (rfl : Halt.diverge = _)
  intro a b ⟨hab, hf⟩
  exact Loop.step_rel (c.eval_erase hab) hab hf (body.erases_pop hab.len (ih a b hab)))

end Scopes

/-! ## Calls -/

section Calls

variable {Γ : Ctx} {ns : List Var} {σ : State C Γ} {τ : Semantics.State}

/-- Agreement carried to a state with the same locals and other bindings
that agree on `ns`. -/
theorem Agree.reglob (hag : Agree ns σ τ) {σ' : State C Γ} {τ' : Semantics.State}
    (henv : σ'.env = σ.env) (hglob : withLocals σ'.glob τ'.env = τ')
    (hns : ∀ y ∈ ns, lookupBy y τ'.env = lookupBy y τ.env) : Agree ns σ' τ' where
  len := hag.len
  nodup := hag.nodup
  glob := hglob
  env m hm := by
    rw [henv] at hm
    rw [hns m.1 (Env.mem_erase_key (b := m.2) hm)]
    exact hag.env m hm

theorem Arg.bindSeq_append (l₁ l₂ : List (Arg C)) (τ : Semantics.State) :
    Arg.bindSeq (l₁ ++ l₂) τ = Arg.bindSeq l₁ τ >>= Arg.bindSeq l₂ := by
  induction l₁ generalizing τ with
  | nil => rfl
  | cons a l₁ ih =>
    simp only [List.cons_append, Arg.bindSeq]
    cases Solidity.Val.eval τ a.e with
    | error _ => rfl
    | ok v => exact ih _

theorem Args.eval_snoc {ps : Ctx} (as : Args C Γ ps) (p : PrimTy) (x : Var) (e : Val C Γ p) :
    (Args.snoc as p x e).eval σ = (do let r ← as.eval σ; let v ← e.eval σ; pure (v, r)) := rfl

/-- A call's arguments: read in the caller's state and bound to the
parameters, alike. -/
theorem Args.bindSeq_erase (hag : Agree ns σ τ) : {ps : Ctx} → (args : Args C Γ ps) →
    args.names.Nodup → (∀ y ∈ args.names, y ∉ ns) →
    (∃ e, args.eval σ = .error e ∧ Arg.bindSeq (args.erase ns) τ = .error e) ∨
    (∃ a τ₁, args.eval σ = .ok a ∧ Arg.bindSeq (args.erase ns) τ = .ok τ₁ ∧
      Agree args.names (State.ofGlob σ.glob a : State C ps) τ₁ ∧
      ∀ y, y ∉ args.names → lookupBy y τ₁.env = lookupBy y τ.env)
  | _, .nil, _, _ => .inr ⟨(), τ, rfl, rfl,
      ⟨rfl, List.nodup_nil, hag.glob, fun _ h => absurd h List.not_mem_nil⟩, fun _ _ => rfl⟩
  | _, .snoc as p x e, hnd, hdis => by
    have hnd' := List.nodup_cons.1 hnd
    rw [Args.eval_snoc]
    have hE : (Args.snoc as p x e).erase ns = as.erase ns ++ [⟨p, x, e.erase ns⟩] := rfl
    rw [hE, Arg.bindSeq_append]
    rcases Args.bindSeq_erase hag as hnd'.2 (fun y hy => hdis y (List.mem_cons_of_mem _ hy)) with
      ⟨err, h₁, h₂⟩ | ⟨r, τ₁, h₁, h₂, hag₁, hf₁⟩
    · exact .inl ⟨err, by rw [h₁]; rfl, by rw [h₂]; rfl⟩
    · have hagσ : Agree ns σ τ₁ := hag.reglob rfl hag₁.glob fun y hy =>
        hf₁ y fun h => hdis y (List.mem_cons_of_mem _ h) hy
      rw [h₁, h₂]
      simp only [SemanticsProperties.Res.ok_bind, Arg.bindSeq, e.eval_erase hagσ]
      cases e.eval σ with
      | error err => exact .inl ⟨err, rfl, rfl⟩
      | ok v =>
        refine .inr ⟨(v, r), τ₁.setEnv x (.val v), rfl, rfl, hag₁.push hnd'.1 (t := .val p) v,
          fun y hy => ?_⟩
        rw [frame_setEnv (B := x :: as.names) List.mem_cons_self y hy]
        exact hf₁ y fun h => hy (List.mem_cons_of_mem _ h)

theorem CallRet.enterAll_append (l₁ l₂ : List (PrimTy × Var)) (τ : Semantics.State) :
    Solidity.CallRet.enterAll (l₁ ++ l₂) τ =
      Solidity.CallRet.enterAll l₂ (Solidity.CallRet.enterAll l₁ τ) := by
  induction l₁ generalizing τ with
  | nil => rfl
  | cons a l₁ ih => exact ih _

/-- Return variables declared at their defaults, alike. -/
theorem Binders.enterAll_erase {ps : Ctx} {qs : List Var} {τ₁ : Semantics.State}
    {g : State C ps} (hag₁ : Agree qs g τ₁) :
    {ρ : Ctx} → (bs : Binders ρ) → (bs.names ++ qs).Nodup →
      Agree (bs.names ++ qs) (g.withEnv (Env.append ρ (Binders.defaults bs) g.env))
        (Solidity.CallRet.enterAll bs.toList τ₁) ∧
      ∀ y, y ∉ bs.names → lookupBy y (Solidity.CallRet.enterAll bs.toList τ₁).env =
        lookupBy y τ₁.env
  | _, .nil, _ => ⟨hag₁, fun _ _ => rfl⟩
  | _, .snoc bs p x, hnd => by
    have hnd' := List.nodup_cons.1 hnd
    obtain ⟨ih, hf⟩ := Binders.enterAll_erase hag₁ bs hnd'.2
    have hx : x ∉ bs.names ++ qs := hnd'.1
    have hT : (Binders.snoc bs p x).toList = bs.toList ++ [(p, x)] := rfl
    rw [hT, CallRet.enterAll_append]
    refine ⟨ih.push hx (t := .val p) (PrimTy.default p), fun y hy => ?_⟩
    rw [show Solidity.CallRet.enterAll [(p, x)] (Solidity.CallRet.enterAll bs.toList τ₁) =
      (Solidity.CallRet.enterAll bs.toList τ₁).setEnv x (.val (PrimTy.default p)) from rfl,
      frame_setEnv (B := x :: bs.names) List.mem_cons_self y hy]
    exact hf y fun h => hy (List.mem_cons_of_mem _ h)

/-- Entering a call's frame: the return variables at their defaults (a memory
return a fresh object, which the erased body declares first), alike. -/
theorem CallRet.enter_erase {ps rs Γ' : Ctx} {qs : List Var} {a : Env C ps}
    {τ₁ : Semantics.State} (hag₁ : Agree qs (State.ofGlob σ.glob a : State C ps) τ₁)
    (ret : CallRet Γ rs Γ') (hnd : (ret.names ++ qs).Nodup) :
    (∃ e, (ret.enter σ.glob : Res (Semantics.State × Env C rs)) = .error e ∧
      Solidity.Prog.run (Solidity.CallRet.enter τ₁ (ret.erase ns)) (ret.pre (C := C)) = .error e) ∨
    (∃ τg r τ₂, (ret.enter σ.glob : Res (Semantics.State × Env C rs)) = .ok (τg, r) ∧
      Solidity.Prog.run (Solidity.CallRet.enter τ₁ (ret.erase ns)) (ret.pre (C := C)) = .ok τ₂ ∧
      Agree (ret.names ++ qs) (State.ofGlob τg (Env.append rs r a) : State C (rs ++ ps)) τ₂ ∧
      ∀ y, y ∉ ret.names → lookupBy y τ₂.env = lookupBy y τ₁.env) := by
  cases ret with
  | none => exact .inr ⟨σ.glob, (), τ₁, rfl, rfl, hag₁, fun _ _ => rfl⟩
  | val p r res =>
    exact .inr ⟨σ.glob, (PrimTy.default p, ()), τ₁.setEnv r (.val (PrimTy.default p)), rfl, rfl,
      hag₁.push (List.nodup_cons.1 hnd).1 (t := .val p) _,
      frame_setEnv (B := [r]) List.mem_cons_self⟩
  | rets bs =>
    obtain ⟨h₁, h₂⟩ := Binders.enterAll_erase hag₁ bs hnd
    exact .inr ⟨σ.glob, Binders.defaults bs, _, rfl, rfl, h₁, h₂⟩
  | mem R r hd hm =>
    have hal : allocDefault τ₁ R =
        (fun p => (withLocals p.1 τ₁.env, p.2)) <$> allocDefault σ.glob R :=
      hag₁.opA (allocDefault_nat R)
    simp only [CallRet.pre, CallRet.erase, Solidity.Prog.run_single, Solidity.CallRet.enter,
      Solidity.Stmt.run, hal]
    have hen : ((CallRet.mem R r hd hm : CallRet Γ _ _).enter σ.glob :
        Res (Semantics.State × Env C [.mem R])) =
        (do let (τ', id) ← allocDefault σ.glob R; pure (τ', (id, ()))) := rfl
    rw [hen]
    cases allocDefault σ.glob R with
    | error e => exact .inl ⟨e, rfl, rfl⟩
    | ok p =>
      exact .inr ⟨p.1, (p.2, ()), _, rfl, rfl,
        (hag₁.withGlob p.1).push (List.nodup_cons.1 hnd).1 (t := .mem R) p.2,
        frame_setEnv (B := [r]) List.mem_cons_self⟩

/-- Leaving a call: the caller's locals, and what the call leaves them,
alike. -/
theorem CallRet.leave_erase (hag : Agree ns σ τ) {rs Γ' ps Γf : Ctx} (ret : CallRet Γ rs Γ')
    {qs : List Var} (hb : Ext (rs ++ ps) Γf) {υ : State C Γf} {τ₃ : Semantics.State}
    (hagF : Agree (ret.names ++ qs) (υ.drop hb) τ₃)
    (hns : ∀ y ∈ ns, lookupBy y τ₃.env = lookupBy y τ.env)
    (hdis : ∀ y ∈ ret.names, y ∉ ns) :
    RunRel (ret.outNames ns) ns τ₃
      (pure (υ.withEnv (ret.leave σ.env (Env.take rs (Env.drop hb υ.env)))))
      (Solidity.CallRet.leave (C := C) τ₃ (ret.erase ns)) := by
  have base : Agree ns (υ.withEnv σ.env) τ₃ := hag.reglob rfl hagF.glob hns
  cases ret with
  | none => exact ⟨base, fun _ _ => rfl⟩
  | val p r res =>
    cases res with
    | none => exact ⟨base, fun _ _ => rfl⟩
    | some j =>
      have hg : τ₃.getEnv r = .ok (.val (Env.get .here (Env.drop hb υ.env))) :=
        hagF.getEnv (Idx.here : Idx (.val p :: ps) (.val p))
      simp only [CallRet.erase, Option.map_some, Solidity.CallRet.leave, Solidity.Simple.eval, hg]
      exact RunRel.ok_setLocal base j _ (Idx.name_mem j ns hag.len)
  | rets bs =>
    have hlen : bs.names.length = rs.length := bs.length_names
    refine ⟨⟨by show (bs.names ++ ns).length = _; simp only [List.length_append, hlen, hag.len],
      ?_, hagF.glob, fun m hm => ?_⟩,
      fun _ _ => rfl⟩
    · refine List.nodup_append.2 ⟨(List.nodup_append.1 hagF.nodup).1, hag.nodup, ?_⟩
      intro y hy z hz hyz
      exact hdis y hy (hyz ▸ hz)
    · show lookupBy m.1 τ₃.env = some m.2
      have hm' : m ∈ Env.erase (bs.names ++ ns)
          (Env.append rs (Env.take rs (Env.drop hb υ.env)) σ.env) := hm
      rw [Env.erase_append _ _ _ _ _ hlen] at hm'
      rcases List.mem_append.1 hm' with hm' | hm'
      · exact hagF.env m (Env.mem_erase_take rs bs.names qs _ hlen m hm')
      · exact base.env m hm'
  | mem R r hd hm =>
    refine ⟨⟨by simp only [CallRet.outNames, List.length_cons, hag.len], ?_, hagF.glob,
      fun m hm => ?_⟩, fun _ _ => rfl⟩
    · exact List.nodup_cons.2 ⟨hdis r List.mem_cons_self, hag.nodup⟩
    · rcases List.mem_cons.1 hm with hm | hm
      · subst hm
        exact hagF.get (Idx.here : Idx (.mem R :: ps) (.mem R))
      · exact base.env m hm

end Calls
