import Solidity.Semantics.Erased
import Solidity.Semantics.Agree

/-!
# A scoped state and its erasure

The bridge between `Semantics/Erased.lean`'s scoped state (`State C Γ`: the
locals of `Γ` by position, and the global part) and `Semantics.lean`'s
untyped one (the locals a list of named bindings), which the closer's terms
read (`docs/intrinsic.md`, M3; the statements' bridge, `run_erase`, was
deleted at W4 `sem-del` with the untyped run's last typed-side users).

`State.erase ns σ` names the locals of `σ` by `ns` and encodes each
(`LTy.enc`).  `Agree ns σ τ`: the global parts are equal, and every local of
`σ` is bound in `τ` under its name, encoded; `τ` may bind more.  The global
operations the closer's updates run are natural in the locals (`*_nat`,
`*_wl`), so an expression reads alike in agreeing states (`Val.eval_erase`
and its siblings).  `Agree.erase`: a state agrees with its erasure.
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

theorem arrayLen_wl (r : Name) (segs : List Seg) :
    arrayLen (withLocals s e) r segs = arrayLen s r segs := rfl

theorem memArrayLen_wl (id : Nat) : memArrayLen (withLocals s e) id = memArrayLen s id := rfl

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

/-! ## The global part, through agreement -/

namespace Agree

variable {Γ : Ctx} {ns : List Var} {σ : EState C Γ} {τ : Semantics.State}

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

end Agree

/-! ## Expressions read alike -/

section Eval

variable {Γ : Ctx} {ns : List Var} {σ : EState C Γ} {τ : Semantics.State}

theorem Simple.eval_erase (hag : Agree ns σ τ) {p : PrimTy} :
    (s : Simple C Γ p) → Surface.Simple.eval τ (s.erase ns) = s.eval σ
  | .lit .. => rfl
  | .bool _ => rfl
  | .local i => by
    simp only [Simple.erase, Surface.Simple.eval, hag.getEnv i, Simple.eval]
    rfl
  | .env k _ => by simp only [Simple.erase, Surface.Simple.eval, hag.envVal k, Simple.eval]

theorem aliasPath_erase (hag : Agree ns σ τ) {R : RefTy} (i : Idx Γ (.alias R)) :
    Semantics.aliasPath τ (i.name ns) = aliasPath σ i := by
  simp only [Semantics.aliasPath, hag.getEnv i, aliasPath]
  generalize (Env.get i σ.env : Option (Name × List Seg)) = v
  rcases v with _ | ⟨r, segs⟩ <;> rfl

mutual

theorem SPath.resolve_erase (hag : Agree ns σ τ) :
    {T : Ty} → (p : SPath C Γ T) → Surface.SPath.resolve τ (p.erase ns) = p.resolve σ
  | _, .alias i => aliasPath_erase hag i
  | _, .loc l => l.resolve_erase hag

theorem Loc.resolve_erase (hag : Agree ns σ τ) :
    {T : Ty} → (l : Loc C Γ T) → Surface.Loc.resolve τ (l.erase ns) = l.resolve σ
  | _, .root .. => rfl
  | _, .field b _ _ => by
    simp only [Loc.erase, Surface.Loc.resolve, b.resolve_erase hag, Loc.resolve]
  | _, .index _ b i => by
    simp only [Loc.erase, Surface.Loc.resolve, b.resolve_erase hag, i.eval_erase hag,
      hag.checkIndex, Loc.resolve]

theorem MPath.mval_erase (hag : Agree ns σ τ) :
    {T : Ty} → (p : MPath C Γ T) → Surface.MPath.mval τ (p.erase ns) = p.mval σ
  | _, .var i _ => by
    simp only [MPath.erase, Surface.MPath.mval, hag.getEnv i, MPath.mval, memRef]
    cases Env.get i σ.env <;> rfl
  | _, .loc l => l.read_erase hag

theorem MLoc.read_erase (hag : Agree ns σ τ) :
    {T : Ty} → (l : MLoc C Γ T) → Surface.MLoc.read τ (l.erase ns) = l.read σ
  | _, .field b _ _ => by
    simp only [MLoc.erase, Surface.MLoc.read, b.mval_erase hag, hag.getObj, MLoc.read]
    rfl
  | _, .index _ b i => by
    simp only [MLoc.erase, Surface.MLoc.read, b.mval_erase hag, i.eval_erase hag, hag.getObj,
      MLoc.read]
    rfl

theorem Val.eval_erase (hag : Agree ns σ τ) :
    {p : PrimTy} → (v : Val C Γ p) → Surface.Val.eval τ (v.erase ns) = v.eval σ
  | _, .simple s => s.eval_erase hag
  | _, .read l => by
    simp only [Val.erase, Surface.Val.eval, l.resolve_erase hag, hag.findStorage, Val.eval]
  | _, .binop _ _ _ a b => by
    simp only [Val.erase, Surface.Val.eval, a.eval_erase hag, b.eval_erase hag, Val.eval]
  | _, .unop _ _ _ a => by
    simp only [Val.erase, Surface.Val.eval, a.eval_erase hag, Val.eval]
  | _, .ternary c a b => by
    simp only [Val.erase, Surface.Val.eval, c.eval_erase hag, a.eval_erase hag,
      b.eval_erase hag, Val.eval]
  | _, .readMem l => by
    simp only [Val.erase, Surface.Val.eval, l.read_erase hag, Val.eval]
  | _, .len b _ => by
    simp only [Val.erase, Surface.Val.eval, b.resolve_erase hag, hag.arrayLen, Val.eval]
  | _, .mlen b _ => by
    simp only [Val.erase, Surface.Val.eval, b.mval_erase hag, hag.memArrayLen, Val.eval]

end

end Eval

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
