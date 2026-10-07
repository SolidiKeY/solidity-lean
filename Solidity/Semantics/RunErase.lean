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
