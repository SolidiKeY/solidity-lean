import Solidity.Calculus.DecideScoped
import Solidity.Calculus.Graft
import Solidity.Calculus.SoundLoops
import Solidity.Calculus.ProvesSound

/-!
# The scoped reduction, sound over the typed state

`Fml.toLS` (`Calculus/DecideScoped.lean`) pushes a scoped leaf's updates in
by position.  Its soundness is proved here on the leaf itself, over the
typed state and its run (`holds`, `Calculus/Logic.lean`), not through the
leaf's erasure (decision 83's rest): `Fml.toLS_sound` follows the leaf's
binders, updates and connectives as `holds` reads them, and
`Valid.of_reduceS` puts it together with the elimination (`LFml.elim_holds`).

What relates a position of the context to the reduction's state is
`RelU σ ρ τ τu`: the scoped state `τ` (an `EState`, what a typed state
erases to), the reduction's state `ρ`, the state `σ` the reduction is read
in, and an untyped state `τu` that holds every *bound* position (one an
update or a binder gave a symbol) under its key (`SymS.key`, a position of
the leaf's context counted along its binders) and otherwise reads as `σ`.
The symbols are untyped (decision 83: a scoped term reads its symbols on
the state's global part), so a term's reading goes through `τu` and the
reduction's lemmas over the untyped interpreter (`Term.toL_eval`, …); a
position no update bound (a hidden binder at a memory type before its
update binds it) is in `τ` only, and the fragment never reads it
(`Tm.inLS`).

The binders: a quantifier is the reduction's `LFml.all` over its key, and
its local the atom `pos k`, which the state read binds at the key and `τu`
holds there; a hidden binder pushes a position bound to nothing, and `τu`
does not change (the update that follows binds it).  A pop or a frame's
drop leaves `τu` as it is.

What a term reads goes through `τu` (`Tm.eval_eraseB`, the bound positions
only); what an element writes is its erasure's write under the keys
(`UpdElem.write_eraseB`), its guard and the binding it leaves the erased
reduction's (`Surface.UpdElem.toL_sound`, `pair_sound`).

Polarity: the fragment takes updates, hidden binders and modalities only
in positive positions (`Fml.inLS true`), where the reduction need only
imply the formula; under a negation or on the left of an implication the
formula is first-order and the two agree both ways.
-/

namespace Solidity

namespace Decide

open Semantics SemanticsProperties

variable {C : Contract}

/-! ## Agreeing on the bound positions -/

section Agree

/-- The locals an erased term reads are bound in `E`. -/
def _root_.Solidity.Surface.Tm.ReadsIn (E : List (Var × SymB)) :
    {s : Srt} → Surface.Tm C s → Prop
  | _, .pvV x | _, .pvP x | _, .pvS x | _, .pvI x => (lookupBy x E).isSome = true
  | _, .app0 _ => True
  | _, .app1 o a =>
    (match o with
      | .netOf x => (lookupBy x E).isSome = true
      | _ => True) ∧ a.ReadsIn E
  | _, .app2 _ a b => a.ReadsIn E ∧ b.ReadsIn E
  | _, .app3 _ a b c => a.ReadsIn E ∧ b.ReadsIn E ∧ c.ReadsIn E

variable {Γ : Ctx}

/-- A scoped state and an untyped one agree on the positions `E` binds:
the global parts are equal, and each such local is bound under its key
(`Agree`, on the bound positions only). -/
structure AgreeB (E : List (Var × SymB)) (ns : List Var) (σ : EState C Γ)
    (τ : Semantics.State) : Prop where
  len : ns.length = Γ.length
  nodup : ns.Nodup
  glob : withLocals σ.glob τ.env = τ
  env : ∀ m ∈ Env.erase ns σ.env, (lookupBy m.1 E).isSome = true → lookupBy m.1 τ.env = some m.2

variable {E : List (Var × SymB)} {ns : List Var} {σ : EState C Γ} {τ : Semantics.State}

theorem AgreeB.getEnv (hag : AgreeB E ns σ τ) {t : LTy} (i : Idx Γ t)
    (hb : (lookupBy (i.name ns) E).isSome = true) :
    τ.getEnv (i.name ns) = .ok (t.enc C (Env.get i σ.env)) := by
  simp only [Semantics.State.getEnv, hag.env _ (Env.mem_erase_get i ns σ.env hag.len) hb]

theorem AgreeB.wl (hag : AgreeB E ns σ τ) : τ = withLocals σ.glob τ.env := hag.glob.symm

theorem AgreeB.glob_with (hag : AgreeB E ns σ τ) (e : List (Var × Binding)) :
    withLocals σ.glob e = withLocals τ e := by
  rw [← hag.glob]

/-- The bindings named the same. -/
theorem AgreeB.congrE {E' : List (Var × SymB)} (hag : AgreeB E ns σ τ)
    (hE : ∀ x, (lookupBy x E').isSome = true → (lookupBy x E).isSome = true) :
    AgreeB E' ns σ τ :=
  ⟨hag.len, hag.nodup, hag.glob, fun m hm hb => hag.env m hm (hE _ hb)⟩

/-- A name not among the positions set. -/
theorem AgreeB.setOther (hag : AgreeB E ns σ τ) {y : Var} (hy : y ∉ ns) (b : Binding) :
    AgreeB E ns σ (τ.setEnv y b) where
  len := hag.len
  nodup := hag.nodup
  glob := hag.glob_with _
  env m hm hb := by
    have hne : m.1 ≠ y := fun h => hy (h ▸ Env.mem_erase_key (b := m.2) hm)
    simp only [Semantics.State.setEnv, lookupBy_setBy_ne hne, hag.env m hm hb]

/-- A local set, under its name, and bound. -/
theorem AgreeB.setLocal (hag : AgreeB E ns σ τ) {t : LTy} (i : Idx Γ t) (v : t.Denote C)
    (b : SymB) :
    AgreeB ((i.name ns, b) :: E) ns (σ.setLocal i v) (τ.setEnv (i.name ns) (t.enc C v)) where
  len := hag.len
  nodup := hag.nodup
  glob := hag.glob_with _
  env m hm hb := by
    rcases Env.mem_erase_set i v ns σ.env hag.len hag.nodup m hm with h | ⟨hm, hne⟩
    · subst h; exact lookupBy_setBy_self _ _ _
    · simp only [lookupBy, hne, ↓reduceIte] at hb
      simp only [Semantics.State.setEnv, lookupBy_setBy_ne hne, hag.env m hm hb]

/-- A local declared under a fresh name, and bound. -/
theorem AgreeB.push (hag : AgreeB E ns σ τ) {x : Var} (hx : x ∉ ns) {t : LTy} (v : t.Denote C)
    (b : SymB) :
    AgreeB ((x, b) :: E) (x :: ns) (σ.push v) (τ.setEnv x (t.enc C v)) where
  len := by simp only [List.length_cons, hag.len]
  nodup := List.nodup_cons.2 ⟨hx, hag.nodup⟩
  glob := hag.glob_with _
  env m hm hb := by
    rcases List.mem_cons.1 hm with hm | hm
    · subst hm; exact lookupBy_setBy_self _ _ _
    · have hne : m.1 ≠ x := fun h => hx (h ▸ Env.mem_erase_key (b := m.2) hm)
      simp only [lookupBy, hne, ↓reduceIte] at hb
      simp only [Semantics.State.setEnv, lookupBy_setBy_ne hne, hag.env m hm hb]

/-- A local declared under a name `E` does not bind: not read. -/
theorem AgreeB.pushFree (hag : AgreeB E ns σ τ) {x : Var} (hx : x ∉ ns)
    (hE : lookupBy x E = none) {t : LTy} (v : t.Denote C) :
    AgreeB E (x :: ns) (σ.push v) τ where
  len := by simp only [List.length_cons, hag.len]
  nodup := List.nodup_cons.2 ⟨hx, hag.nodup⟩
  glob := hag.glob
  env m hm hb := by
    rcases List.mem_cons.1 hm with hm | hm
    · subst hm; simp only [hE, Option.isSome_none, Bool.false_eq_true] at hb
    · exact hag.env m hm hb

/-- A scope's locals popped. -/
theorem AgreeB.drop {Γ' : Ctx} {σ : EState C Γ'} (hag : AgreeB E ns σ τ) (h : Ext Γ Γ') :
    AgreeB E (ns.drop h.depth) (σ.drop h) τ := by
  have hl : (ns.take h.depth).length = h.depth := by
    rw [List.length_take, hag.len, h.length_eq]; omega
  have hag' : AgreeB E (ns.take h.depth ++ ns.drop h.depth) σ τ := by
    rw [List.take_append_drop]; exact hag
  exact ⟨by have h₁ := hag'.len; have h₂ := h.length_eq
            simp only [List.length_append] at h₁; omega,
    (List.nodup_append.1 hag'.nodup).2.1, hag.glob,
    fun m hm hb => hag'.env m (Env.mem_erase_drop h _ _ σ.env hl m hm) hb⟩

/-- A frame dropped from under what it keeps. -/
theorem AgreeB.thin {Γ' : Ctx} {σ : EState C Γ'} (hag : AgreeB E ns σ τ) (h : Thin Γ Γ') :
    AgreeB E (h.names ns) (σ.thin h) τ where
  len := Thin.names_length h ns hag.len
  nodup := (Thin.names_sublist h ns).nodup hag.nodup
  glob := hag.glob
  env m hm hb := hag.env m (Env.mem_erase_thin h ns σ.env hag.len m hm) hb

/-- The global part replaced on both sides. -/
theorem AgreeB.withGlob (hag : AgreeB E ns σ τ) (g : Semantics.State) :
    AgreeB E ns (σ.withGlob g) (withLocals g τ.env) :=
  ⟨hag.len, hag.nodup, rfl, hag.env⟩

theorem aliasPath_eraseB (hag : AgreeB E ns σ τ) {R : RefTy} (i : Idx Γ (.alias R))
    (hb : (lookupBy (i.name ns) E).isSome = true) :
    Semantics.aliasPath τ (i.name ns) = aliasPath σ i := by
  simp only [Semantics.aliasPath, hag.getEnv i hb, aliasPath]
  generalize (Env.get i σ.env : Option (Name × List Seg)) = v
  rcases v with _ | ⟨r, segs⟩ <;> rfl

/-- **A term reads as its erasure** where the positions it reads are bound
(`Tm.eval_erase`, on the bound positions only). -/
theorem Tm.eval_eraseB (hag : AgreeB E ns σ τ) : {s : Srt} → (t : Tm C Γ s) →
    (t.erase ns).ReadsIn E → (t.erase ns).eval τ = Srt.wl τ.env s (t.eval σ)
  | _, .pvV i, hr => by
    simp only [Tm.erase, Surface.Tm.eval, hag.getEnv i hr]; rfl
  | _, .pvP i, hr => aliasPath_eraseB hag i hr
  | _, .pvS i, hr => by
    simp only [Tm.erase, Surface.Tm.eval, hag.getEnv i hr]
    rw [hag.wl]; rfl
  | _, .pvI i, hr => by
    simp only [Tm.erase, Surface.Tm.eval, hag.getEnv i hr, Tm.eval, memRef]
    cases Env.get i σ.env <;> rfl
  | _, .netOf i a, hr => by
    show Op1.eval τ (.netOf (i.name ns)) ((a.erase ns).eval τ) = _
    rw [Tm.eval_eraseB hag a hr.2]
    simp only [Op1.eval, hag.getEnv i hr.1]
    rfl
  | _, .app0 o, _ => by
    show o.eval τ = _
    rw [hag.wl]; exact Op0.eval_wl _ _ o
  | _, .app1 o ho x, hr => by
    show o.eval τ ((x.erase ns).eval τ) = _
    rw [Tm.eval_eraseB hag x hr.2, hag.wl]
    exact Op1.eval_wl _ _ o ho _
  | _, .app2 o x y, hr => by
    show o.eval τ ((x.erase ns).eval τ) ((y.erase ns).eval τ) = _
    rw [Tm.eval_eraseB hag x hr.1, Tm.eval_eraseB hag y hr.2, hag.wl]
    exact Op2.eval_wl _ _ o _ _
  | _, .app3 o x y z, hr => by
    show o.eval τ ((x.erase ns).eval τ) ((y.erase ns).eval τ) ((z.erase ns).eval τ) = _
    rw [Tm.eval_eraseB hag x hr.1, Tm.eval_eraseB hag y hr.2.1, Tm.eval_eraseB hag z hr.2.2,
      Op3.eval_wl]
    rfl

end Agree

/-! ## The fragment reads bound positions only -/

section Reads

variable {Γ : Ctx} {ns : List Var} {ρ : SymS}

theorem Op1.inL_arg {a s : Srt} (o : Op1 a s) (x : a.LTy) {h : Bool} (ho : o.inL x h = true) :
    h = true := by
  cases h
  · cases o <;> simp_all only [Op1.inL, Bool.false_and, Bool.false_eq_true]
  · rfl

theorem readsIn_of_storLocal {t : Tm C Γ .st} (hok : ρ.Ok ns) (hl : ns.length = Γ.length)
    (h : (t.storLocalS ρ).isSome = true) : (t.erase ns).ReadsIn ρ.sym.env := by
  cases t with
  | pvS i =>
    simp only [Tm.storLocalS, Idx.toNatR_eq, SymS.get_of_ok hok hl i] at h
    simp only [Tm.erase, Surface.Tm.ReadsIn]
    revert h
    rcases lookupBy (i.name ns) ρ.sym.env with _ | b
    · exact id
    · exact fun _ => rfl
  | _ => simp only [Tm.storLocalS, Option.isSome_none, Bool.false_eq_true] at h

theorem readsIn_of_isStorage {s : Srt} {t : Tm C Γ s} (h : t.isStorageS = true) :
    (t.erase ns).ReadsIn ρ.sym.env := by
  cases t with
  | app0 o => exact trivial
  | _ => simp only [Tm.isStorageS, Bool.false_eq_true] at h

theorem readsIn_of_fresh {m : Tm C Γ .mem} {v : Tm C Γ .mv} {z : Option (LMV × LTerm)}
    (h : (freshRefS ρ m v z).isSome = true) (hz : z = none) : (v.erase ns).ReadsIn ρ.sym.env := by
  subst hz
  unfold freshRefS at h
  split at h
  · rename_i R R' _ hv
    unfold allocRefOfS? at hv
    split at hv
    · simp only [Tm.erase, Surface.Tm.ReadsIn, and_true]
    · cases hv
  · cases h

/-- **The fragment reads bound positions only.** -/
theorem _root_.Solidity.Tm.readsIn_of_inLSM (hok : ρ.Ok ns) (hl : ns.length = Γ.length) :
    {s : Srt} → (t : Tm C Γ s) → t.inLSM ρ = true → (t.erase ns).ReadsIn ρ.sym.env
  | _, .pvV i, h => by
    simp only [Tm.inLSM, SymS.get_of_ok hok hl i] at h
    exact h
  | _, .pvP i, h => by
    simp only [Tm.inLSM, SymS.get_of_ok hok hl i] at h
    simp only [Tm.erase, Surface.Tm.ReadsIn]
    revert h
    rcases lookupBy (i.name ns) ρ.sym.env with _ | b
    · exact id
    · exact fun _ => rfl
  | _, .pvS _, h => by simp only [Tm.inLSM, Bool.false_eq_true] at h
  | _, .pvI i, h => by
    simp only [Tm.inLSM, SymS.get_of_ok hok hl i] at h
    simp only [Tm.erase, Surface.Tm.ReadsIn]
    revert h
    rcases lookupBy (i.name ns) ρ.sym.env with _ | b
    · exact id
    · exact fun _ => rfl
  | _, .netOf _ _, h => by simp only [Tm.inLSM, Bool.false_eq_true] at h
  | _, .app0 _, _ => trivial
  | _, .app1 o ho a, h => by
    simp only [Tm.inLSM] at h
    refine ⟨?_, Tm.readsIn_of_inLSM hok hl a (Op1.inL_arg o _ h)⟩
    cases o <;> first | trivial | simp only [Op1.named, Bool.true_eq_false] at ho
  | _, .app2 o a b, h => by
    simp only [Tm.inLSM] at h
    have ha := Tm.readsIn_of_inLSM hok hl a
    have hb := Tm.readsIn_of_inLSM hok hl b
    cases o <;> simp only [Op2.inLS, Bool.and_eq_true, Bool.or_eq_true, Bool.false_eq_true] at h <;>
      first
      | exact ⟨ha h.1, hb h.2⟩
      | exact ⟨ha h.1.1, hb h.1.2⟩
      | exact ⟨ha h.1.1.1, hb h.1.1.2⟩
      | exact ⟨readsIn_of_isStorage h.1, hb h.2⟩
      | exact ⟨h.1.elim readsIn_of_isStorage (readsIn_of_storLocal hok hl), hb h.2⟩
  | _, .app3 o a b c, h => by
    simp only [Tm.inLSM] at h
    have ha := Tm.readsIn_of_inLSM hok hl a
    have hb := Tm.readsIn_of_inLSM hok hl b
    have hc := Tm.readsIn_of_inLSM hok hl c
    cases o with
    | ite =>
      simp only [Op3.inLS, Bool.and_eq_true] at h
      exact ⟨ha h.1.1, hb h.1.2, hc h.2⟩
    | save =>
      simp only [Op3.inLS, Bool.and_eq_true] at h
      exact ⟨readsIn_of_isStorage h.1.1.1, hb h.1.1.2, hc h.1.2⟩
    | push =>
      cases c with
      | app1 o' _ _ =>
        cases o' <;> simp only [Op3.inLS, Bool.and_eq_true, Bool.false_eq_true] at h <;>
          exact ⟨readsIn_of_isStorage h.1.1, hb h.1.2, hc h.2⟩
      | app2 o' _ _ =>
        cases o' <;> simp only [Op3.inLS, Bool.and_eq_true, Bool.false_eq_true] at h <;>
          exact ⟨readsIn_of_isStorage h.1.1, hb h.1.2, hc h.2⟩
      | _ => simp only [Op3.inLS, Bool.false_eq_true] at h
    | write =>
      simp only [Op3.inLS, Bool.and_eq_true, Bool.or_eq_true] at h
      exact ⟨ha h.1.1.1, hb h.1.1.2, h.1.2.elim hc fun hf => readsIn_of_fresh hf rfl⟩
    | _ => simp only [Op3.inLS, Bool.false_eq_true] at h

theorem _root_.Solidity.Tm.readsIn_of_inLS (hok : ρ.Ok ns) (hl : ns.length = Γ.length) {s : Srt}
    (t : Tm C Γ s) (h : t.inLS ρ = true) : (t.erase ns).ReadsIn ρ.sym.env :=
  Tm.readsIn_of_inLSM hok hl t ((Tm.inLS_eq_inLSM ρ t) ▸ h)

end Reads

/-! ## The relation, by position -/

section RelU

variable {Γ : Ctx}

/-- The positions of `τ` are `ρ`'s keys, each bound one held by `τu` under
its key (`AgreeB`); no key from `ρ.next` on is taken yet. -/
structure AgreeU (ρ : SymS) (τ : EState C Γ) (τu : Semantics.State) : Prop where
  ok : ρ.Ok ρ.names
  agree : AgreeB ρ.sym.env ρ.names τ τu
  fresh : ∀ m, ρ.next ≤ m → slotVar m ∉ ρ.names ∧ lookupBy (slotVar m) ρ.sym.env = none

/-- **The reduction's state `ρ` stands for the scoped state `τ`**, read in
`σ`, through `τu`: `AgreeU`, and `ρ`'s symbols read in `σ` what `τu` holds
(`Rel`). -/
structure RelU (σ : Semantics.State) (ρ : SymS) (τ : EState C Γ) (τu : Semantics.State) :
    Prop where
  toAgreeU : AgreeU ρ τ τu
  rel : Rel σ ρ.sym τu

variable {σ : Semantics.State} {ρ : SymS} {τ : EState C Γ} {τu : Semantics.State}

theorem RelU.ok (h : RelU σ ρ τ τu) : ρ.Ok ρ.names := h.toAgreeU.ok
theorem RelU.agree (h : RelU σ ρ τ τu) : AgreeB ρ.sym.env ρ.names τ τu := h.toAgreeU.agree
theorem AgreeU.len (h : AgreeU ρ τ τu) : ρ.names.length = Γ.length := h.agree.len
theorem RelU.len (h : RelU σ ρ τ τu) : ρ.names.length = Γ.length := h.agree.len

theorem RelU.toL (h : RelU σ ρ τ τu) {s : Srt} (t : Tm C Γ s) :
    t.toLS ρ = (t.erase ρ.names).toL ρ.sym :=
  Tm.toLS_eq h.ok h.len t

theorem RelU.inL (h : RelU σ ρ τ τu) {s : Srt} {t : Tm C Γ s} (hf : t.inLS ρ = true) :
    (t.erase ρ.names).inL ρ.sym = true :=
  Tm.inLS_imp h.ok h.len t hf

theorem RelU.eval (h : RelU σ ρ τ τu) {s : Srt} {t : Tm C Γ s} (hf : t.inLS ρ = true) :
    (t.erase ρ.names).eval τu = Srt.wl τu.env s (t.eval τ) :=
  Tm.eval_eraseB h.agree t (Tm.readsIn_of_inLS h.ok h.len t hf)

/-- A value term reads, pushed in by position, what it reads in `τ`. -/
theorem RelU.val (h : RelU σ ρ τ τu) {t : Tm C Γ .val} (hf : t.inLS ρ = true) :
    Sim ((t.toLS ρ).eval σ) (t.eval τ) := by
  have := Term.toL_eval h.rel (t.erase ρ.names) (h.inL hf)
  rw [← h.toL t, h.eval hf] at this
  exact this

end RelU

/-! ## The relation through binders, pops and writes -/

section Steps

theorem slotVar_inj {m n : Nat} (h : slotVar m = slotVar n) : m = n := by
  simp only [slotVar, Var.fresh.injEq, true_and] at h
  exact h

/-- Binding a quantifier's position keeps the relation: the position read
by no symbol so far, it is the atom `pos n` (`Rel.free`, by position). -/
theorem Rel.freePos {σ τ : Semantics.State} {ρ : Sym} (h : Rel σ ρ τ) {n : Nat}
    (hx : slotVar n ∉ ρ.vars) (v : Value) :
    Rel (σ.setEnv (slotVar n) (.val v))
      { ρ with env := (slotVar n, .val (.var (.pos n))) :: ρ.env }
      (τ.setEnv (slotVar n) (.val v)) := by
  simp only [Sym.vars, List.mem_append, not_or] at hx
  obtain ⟨⟨hx₁, hx₂⟩, hx₃⟩ := hx
  have hB : LMem.births (σ.setEnv (slotVar n) (.val v)) ρ.mem = ρ.mem.births σ :=
    LMem.births_setEnv hx₃
  refine ⟨?_, fun y => ?_, fun k => by
    rw [State.envVal_setEnv, State.envVal_setEnv, h.tx k], ?_⟩
  · show LStor.eval (σ.setEnv (slotVar n) (.val v)) ρ.stor = _
    rw [LStor.eval_setEnv _ hx₁]; exact h.stor
  · show EnvRel _ _ (LMem.births (σ.setEnv (slotVar n) (.val v)) ρ.mem) _ _
    rw [hB]
    by_cases hy : y = slotVar n
    · subst hy
      simp only [lookupBy, if_true, EnvRel, LTerm.eval, Atom.key]
      exact ⟨v, by simp only [State.getEnv_setEnv_self]; rfl,
          by simp only [State.getEnv_setEnv_self]⟩
    · have hl : lookupBy y ((slotVar n, SymB.val (.var (.pos n))) :: ρ.env) =
          lookupBy y ρ.env := by
        simp only [lookupBy, hy, ↓reduceIte]
      rw [hl]
      have he := h.env y
      rcases hb : lookupBy y ρ.env with _ | ⟨t⟩ | ⟨q⟩ | ⟨q⟩ | ⟨S⟩ | ⟨k⟩ | _ <;> rw [hb] at he <;>
        simp only [EnvRel] at he ⊢ <;>
        simp only [State.getEnv_setEnv_ne hy]
      · exact he
      · have hv := lookupBy_vars (x := slotVar n) ρ.env hb hx₂
        simp only [SymB.vars] at hv
        rw [LTerm.eval_setEnv _ hv]; exact he
      · have hv := lookupBy_vars (x := slotVar n) ρ.env hb hx₂
        simp only [SymB.vars] at hv
        rw [LPath.eval_setEnv _ hv]; exact he
      · have hv := lookupBy_vars (x := slotVar n) ρ.env hb hx₂
        simp only [SymB.vars] at hv
        rw [LPath.eval_setEnv _ hv]; exact he
      · have hv := lookupBy_vars (x := slotVar n) ρ.env hb hx₂
        simp only [SymB.vars] at hv
        rw [LStor.eval_setEnv _ hv]; exact he
      · exact he
      · exact he
  · obtain ⟨μ, B, hr, hh⟩ := h.mem
    exact ⟨μ, B, by rw [LMem.run_setEnv _ hx₃]; exact hr, hh.1, hh.2⟩

variable {Γ : Ctx} {σ : Semantics.State} {ρ : SymS} {τ : EState C Γ} {τu : Semantics.State}

/-- A scope's locals popped. -/
theorem AgreeU.pop {Γ' : Ctx} {τ : EState C Γ'} (h : AgreeU ρ τ τu) (hx : Ext Γ Γ') :
    AgreeU ⟨ρ.loc.drop hx.depth, ρ.sym, ρ.next⟩ (τ.drop hx) τu := by
  have hn : SymS.names ⟨ρ.loc.drop hx.depth, ρ.sym, ρ.next⟩ = ρ.names.drop hx.depth := by
    simp only [SymS.names, List.map_drop]
  have hok := h.ok
  unfold SymS.Ok at hok
  refine ⟨?_, ?_, fun m hm => ?_⟩
  · unfold SymS.Ok
    rw [hn]
    show ρ.loc.drop hx.depth = _
    rw [hok, List.map_drop]
  · rw [hn]; exact h.agree.drop hx
  · rw [hn]
    exact ⟨fun hm' => (h.fresh m hm).1 (List.mem_of_mem_drop hm'), (h.fresh m hm).2⟩

/-- A frame dropped from under what it keeps. -/
theorem AgreeU.thin {Γ' : Ctx} {τ : EState C Γ'} (h : AgreeU ρ τ τu) (hx : Thin Γ Γ') :
    AgreeU ⟨Thin.sel hx ρ.loc, ρ.sym, ρ.next⟩ (τ.thin hx) τu := by
  have hn : SymS.names ⟨Thin.sel hx ρ.loc, ρ.sym, ρ.next⟩ = hx.names ρ.names := by
    simp only [SymS.names, ← Thin.sel_map, Thin.sel_eq_names]
  have hok := h.ok
  unfold SymS.Ok at hok
  refine ⟨?_, ?_, fun m hm => ?_⟩
  · unfold SymS.Ok
    rw [hn]
    show Thin.sel hx ρ.loc = _
    rw [hok, Thin.sel_map, Thin.sel_eq_names]
  · rw [hn]; exact h.agree.thin hx
  · rw [hn]
    exact ⟨fun hm' => (h.fresh m hm).1 ((Thin.names_sublist hx _).subset hm'), (h.fresh m hm).2⟩

theorem RelU.pop {Γ' : Ctx} {τ : EState C Γ'} (h : RelU σ ρ τ τu) (hx : Ext Γ Γ') :
    RelU σ ⟨ρ.loc.drop hx.depth, ρ.sym, ρ.next⟩ (τ.drop hx) τu :=
  ⟨h.toAgreeU.pop hx, h.rel⟩

theorem RelU.thin {Γ' : Ctx} {τ : EState C Γ'} (h : RelU σ ρ τ τu) (hx : Thin Γ Γ') :
    RelU σ ⟨Thin.sel hx ρ.loc, ρ.sym, ρ.next⟩ (τ.thin hx) τu :=
  ⟨h.toAgreeU.thin hx, h.rel⟩

theorem AgreeU.key_fresh (h : AgreeU ρ τ τu) : ρ.key ∉ ρ.names ∧ lookupBy ρ.key ρ.sym.env = none :=
  h.fresh ρ.next (Nat.le_refl _)

/-- The fresh keys past a push. -/
theorem AgreeU.fresh_push (h : AgreeU ρ τ τu) {E : List (Var × SymB)}
    (hE : ∀ y, y ≠ ρ.key → lookupBy y E = lookupBy y ρ.sym.env) (m : Nat) (hm : ρ.next + 1 ≤ m) :
    slotVar m ∉ ρ.key :: ρ.names ∧ lookupBy (slotVar m) E = none := by
  have hne : slotVar m ≠ ρ.key := fun he => by
    have := slotVar_inj he; omega
  refine ⟨fun hm' => ?_, by rw [hE _ hne]; exact (h.fresh m (by omega)).2⟩
  rcases List.mem_cons.1 hm' with hm' | hm'
  · exact hne hm'
  · exact (h.fresh m (by omega)).1 hm'

/-- A local pushed: bound by the act (`AgreeB` given for it), or to
nothing. -/
theorem AgreeU.push (h : AgreeU ρ τ τu) (a : Act) (ha : a = .keep ∨ ∃ b, a = .bind b) {t : LTy}
    (v : t.Denote C) {τu' : Semantics.State}
    (hag : AgreeB (ρ.push a).sym.env (ρ.key :: ρ.names) (τ.push v) τu') :
    AgreeU (ρ.push a) (τ.push v) τu' := by
  obtain ⟨hk, -⟩ := h.key_fresh
  have hn : (ρ.push a).names = ρ.key :: ρ.names := by
    rcases ha with rfl | ⟨b, rfl⟩ <;> simp only [SymS.push, SymS.names, List.map_cons]
  refine ⟨?_, by rw [hn]; exact hag, fun m hm => ?_⟩
  · rw [hn]; exact (SymS.push_ok h.ok a ha hk).1
  · have hnx : (ρ.push a).next = ρ.next + 1 := by
      rcases ha with rfl | ⟨b, rfl⟩ <;> rfl
    rw [hn]
    refine h.fresh_push (fun y hy => ?_) m (hnx ▸ hm)
    rcases ha with rfl | ⟨b, rfl⟩
    · rfl
    · simp only [SymS.push, lookupBy, hy, ↓reduceIte]

/-- A local pushed bound to nothing: a hidden binder at a memory type. -/
theorem RelU.pushFree (h : RelU σ ρ τ τu) {t : LTy} (v : t.Denote C) :
    RelU σ (ρ.push .keep) (τ.push v) τu := by
  obtain ⟨hk, he⟩ := h.toAgreeU.key_fresh
  exact ⟨h.toAgreeU.push .keep (.inl rfl) v (h.agree.pushFree hk he v), h.rel⟩

/-- A quantifier's local: the atom of its position, the state read
binding it. -/
theorem RelU.pushQ (h : RelU σ ρ τ τu) (hx : ρ.sym.vars.contains ρ.key = false) (w : Value)
    {p : PrimTy} :
    RelU (σ.setEnv ρ.key (.val w)) ρ.pushQ (τ.push (t := .val p) w)
      (τu.setEnv ρ.key (.val w)) := by
  obtain ⟨hk, -⟩ := h.toAgreeU.key_fresh
  have hx' : ρ.key ∉ ρ.sym.vars := by
    simpa only [List.contains_eq_mem, decide_eq_false_iff_not] using hx
  exact ⟨h.toAgreeU.push _ (.inr ⟨_, rfl⟩) (t := .val p) w (h.agree.push hk (t := .val p) w _),
    Rel.freePos h.rel hx' w⟩

/-- An element's act, the state it leaves agreeing on the positions the act
binds. -/
theorem AgreeU.act (h : AgreeU ρ τ τu) {Γ₀ : Ctx} (e : UpdElem C Γ₀ Γ) (a : Act)
    (ha : ∀ b, a = .bind b → e.tgt.isSome = true) {τ' : EState C Γ} {τu' : Semantics.State}
    {E' : List (Var × SymB)} (hag : AgreeB E' ρ.names τ' τu')
    (hE : ∀ x, (lookupBy x (ρ.act e.tgt a).sym.env).isSome = true →
      (lookupBy x E').isSome = true) :
    AgreeU (ρ.act e.tgt a) τ' τu' := by
  obtain ⟨hok, hsym⟩ := SymS.act_ok h.ok h.agree.nodup h.len e a ha
  have hn : (ρ.act e.tgt a).names = ρ.names := SymS.names_of_ok hok
  refine ⟨by rw [hn]; exact hok, by rw [hn]; exact hag.congrE hE, fun m hm => ?_⟩
  have hnx : (ρ.act e.tgt a).next = ρ.next := by
    cases a with
    | keep | write | mem => rfl
    | bind b =>
      cases e.tgt with
      | none => rfl
      | some n => rfl
  rw [hn]
  refine ⟨(h.fresh m (hnx ▸ hm)).1, ?_⟩
  rw [hsym]
  have hf := (h.fresh m (hnx ▸ hm))
  cases a with
  | keep => exact hf.2
  | mem M => exact hf.2
  | write S =>
    simp only [Act.named, NAct.apply, lookupBy_map_snd, hf.2, Option.map_none]
  | bind b =>
    simp only [Act.named, NAct.apply, lookupBy]
    have hmem : e.tgtName ρ.names ∈ ρ.names := by
      cases e with
      | «local» i r => exact Idx.name_mem i _ h.len
      | _ => exact absurd (ha b rfl) (by simp only [UpdElem.tgt, Option.isSome_none,
          Bool.false_eq_true, not_false_eq_true])
    have hne : slotVar m ≠ e.tgtName ρ.names := fun he => hf.1 (he ▸ hmem)
    simp only [hne, ↓reduceIte, hf.2]

end Steps

/-! ## Writes on the bound positions -/

section Writes

variable {Γ : Ctx} {E₀ : List (Var × SymB)} {ns : List Var} {σ₀ : EState C Γ}
  {τ₀ : Semantics.State}

/-- The terms a right-hand side reads are bound. -/
def _root_.Solidity.Rhs.ReadsB (E₀ : List (Var × SymB)) (ns : List Var) :
    {t : LTy} → Rhs C Γ t → Prop
  | _, .val a => (a.erase ns).ReadsIn E₀
  | _, .path p => (p.erase ns).ReadsIn E₀
  | _, .mref i => (i.erase ns).ReadsIn E₀
  | _, .store s => (s.erase ns).ReadsIn E₀
  | _, .unset | _, .saveNet | _, .saveNetMt => True

theorem Rhs.write_eraseB (hag : AgreeB E₀ ns σ₀ τ₀) {t : LTy} (r : Rhs C Γ t) (x : Var)
    (τ : Semantics.State) (hr : r.ReadsB E₀ ns) :
    (r.erase ns x).write τ₀ τ = (fun v => τ.setEnv x (t.enc C v)) <$> r.eval σ₀ := by
  cases r with
  | val a =>
    simp only [Rhs.erase, Surface.UpdElem.write, Tm.eval_eraseB hag a hr, Srt.wl, Rhs.eval]
    cases a.eval σ₀ <;> rfl
  | path p =>
    simp only [Rhs.erase, Surface.UpdElem.write, Tm.eval_eraseB hag p hr, Srt.wl, Rhs.eval]
    cases p.eval σ₀ <;> rfl
  | unset => rfl
  | mref i =>
    simp only [Rhs.erase, Surface.UpdElem.write, Tm.eval_eraseB hag i hr, Srt.wl, Rhs.eval]
    cases i.eval σ₀ <;> rfl
  | store st =>
    simp only [Rhs.erase, Surface.UpdElem.write, Tm.eval_eraseB hag st hr, Srt.wl, Rhs.eval]
    cases st.eval σ₀ <;> rfl
  | saveNet => simp only [Rhs.erase, Surface.UpdElem.write, Rhs.eval]; rw [hag.wl]; rfl
  | saveNetMt => rfl

/-- The terms an element reads are bound. -/
def _root_.Solidity.UpdElem.ReadsB (E₀ : List (Var × SymB)) (ns : List Var) {Δ : Ctx} :
    UpdElem C Γ Δ → Prop
  | .local _ r => r.ReadsB E₀ ns
  | .storage s => (s.erase ns).ReadsIn E₀
  | .memory m => (m.erase ns).ReadsIn E₀
  | .selfBalance _ a | .setBalance a => (a.erase ns).ReadsIn E₀
  | .net r _ a | .pay r a | .netMt r a => (r.erase ns).ReadsIn E₀ ∧ (a.erase ns).ReadsIn E₀

/-- **An element writes as its erasure**, its right-hand sides read in
states agreeing on what they read, into states agreeing on the bound
positions: both halt alike, or agree after, the assigned local bound. -/
theorem UpdElem.write_eraseB (hag₀ : AgreeB E₀ ns σ₀ τ₀) {Δ : Ctx} {E : List (Var × SymB)}
    {ms : List Var} {σ : EState C Δ} {τ : Semantics.State} (hag : AgreeB E ms σ τ)
    (e : UpdElem C Γ Δ) (hr : e.ReadsB E₀ ns) (b : SymB) :
    Res.Rel (AgreeB (match e with
        | .local i _ => (i.name ms, b) :: E
        | _ => E) ms) (e.write σ₀ σ) ((e.erase ns ms).write τ₀ τ) := by
  rw [hag.wl]
  cases e with
  | «local» i r =>
    rw [← hag.wl]
    simp only [UpdElem.erase, UpdElem.write, Rhs.write_eraseB hag₀ r _ _ hr]
    cases r.eval σ₀ with
    | error => rfl
    | ok v => exact hag.setLocal i v b
  | storage st =>
    simp only [UpdElem.erase, UpdElem.write, Surface.UpdElem.write, Tm.eval_eraseB hag₀ st hr,
      Srt.wl]
    cases st.eval σ₀ with
    | error => rfl
    | ok g => exact hag.withGlob _
  | memory mm =>
    simp only [UpdElem.erase, UpdElem.write, Surface.UpdElem.write, Tm.eval_eraseB hag₀ mm hr,
      Srt.wl]
    cases mm.eval σ₀ with
    | error => rfl
    | ok g => exact hag.withGlob _
  | selfBalance op a =>
    simp only [UpdElem.erase, UpdElem.write, Surface.UpdElem.write, Tm.eval_eraseB hag₀ a hr,
      Srt.wl]
    rw [hag₀.wl]
    exact Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun _ _ => hag.withGlob _
  | net r op a =>
    simp only [UpdElem.erase, UpdElem.write, Surface.UpdElem.write, Tm.eval_eraseB hag₀ r hr.1,
      Tm.eval_eraseB hag₀ a hr.2, Srt.wl]
    exact Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun _ _ =>
      Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun _ _ => hag.withGlob _
  | pay r a =>
    simp only [UpdElem.erase, UpdElem.write, Surface.UpdElem.write, Tm.eval_eraseB hag₀ r hr.1,
      Tm.eval_eraseB hag₀ a hr.2, Srt.wl]
    rw [hag₀.wl]
    refine Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun _ _ =>
      Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun k _ => ?_
    by_cases hk : k < 0
    · simp only [hk, ↓reduceIte]; rfl
    · simp only [hk, ↓reduceIte]; exact hag.withGlob _
  | netMt r a =>
    simp only [UpdElem.erase, UpdElem.write, Surface.UpdElem.write, Tm.eval_eraseB hag₀ r hr.1,
      Tm.eval_eraseB hag₀ a hr.2, Srt.wl]
    exact Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun _ _ =>
      Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun _ _ => hag.withGlob _
  | setBalance a =>
    simp only [UpdElem.erase, UpdElem.write, Surface.UpdElem.write, Tm.eval_eraseB hag₀ a hr,
      Srt.wl]
    exact Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun _ _ => hag.withGlob _

end Writes

/-! ## Updates -/

section Updates

theorem Res.Rel.ok_iff {α β : Type} {R : α → β → Prop} {x : Res α} {y : Res β}
    (h : Res.Rel R x y) : (∃ a, x = .ok a) ↔ ∃ b, y = .ok b := by
  cases x <;> cases y <;> simp_all only [Res.Rel, Except.ok.injEq, exists_eq', reduceCtorEq,
    exists_false]

theorem Res.Rel.of_ok {α β : Type} {R : α → β → Prop} {x : Res α} {y : Res β}
    (h : Res.Rel R x y) {a : α} (hx : x = .ok a) : ∃ b, y = .ok b ∧ R a b := by
  subst hx
  cases y with
  | ok b => exact ⟨b, rfl, h⟩
  | error => exact h.elim

variable {Γ : Ctx} {σ : Semantics.State} {ρ₀ : SymS} {τ₀ : EState C Γ} {τu : Semantics.State}

theorem UView.add_ne_zero (v : UView C Γ) (a : ElemS C Γ) : v.add a ≠ .zero := by
  cases v <;> simp only [UView.add, ne_eq, reduceCtorEq, not_false_eq_true]

theorem UView.add_eq_one {v : UView C Γ} {a b : ElemS C Γ} (h : v.add a = .one b) :
    v = .zero ∧ a = b := by
  cases v <;> simp only [UView.add, UView.one.injEq, reduceCtorEq] at h
  exact ⟨rfl, h⟩

theorem UView.add_eq_two {v : UView C Γ} {a b c : ElemS C Γ} (h : v.add a = .two b c) :
    v = .one b ∧ a = c := by
  cases v <;> simp only [UView.add, UView.two.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem readsIn_of_slotPath {ns : List Var} {ρ : SymS} (hok : ρ.Ok ns)
    (hl : ns.length = Γ.length) {u : Srt} (t : Tm C Γ u) (h : (t.slotPathS ρ).isSome = true) :
    (t.erase ns).ReadsIn ρ.sym.env := by
  induction t with
  | pvP i =>
    simp only [Tm.slotPathS, Idx.toNatR_eq, SymS.get_of_ok hok hl i] at h
    simp only [Tm.erase, Surface.Tm.ReadsIn]
    revert h
    rcases lookupBy (i.name ns) ρ.sym.env with _ | b
    · exact id
    · exact fun _ => rfl
  | app1 o _ p ih =>
    cases o with
    | field f =>
      simp only [Tm.slotPathS, Option.isSome_map] at h
      exact ⟨trivial, ih h⟩
    | _ => simp only [Tm.slotPathS, Option.isSome_none, Bool.false_eq_true] at h
  | _ => simp only [Tm.slotPathS, Option.isSome_none, Bool.false_eq_true] at h

theorem readsIn_of_inLSt {ns : List Var} {ρ : SymS} (hok : ρ.Ok ns)
    (hl : ns.length = Γ.length) (s : Tm C Γ .st) (h : s.inLSt ρ = true) :
    (s.erase ns).ReadsIn ρ.sym.env := by
  unfold Tm.inLSt at h
  cases hw : s.staleWriteS ρ with
  | none =>
    rw [hw] at h
    exact Tm.readsIn_of_inLS hok hl s h
  | some w =>
    rw [hw] at h
    obtain ⟨op, q, t⟩ := w
    unfold Tm.staleWriteS at hw
    split at hw
    · next p _ t' =>
      obtain ⟨q', hq, he⟩ := Option.map_eq_some_iff.1 hw
      cases he
      exact ⟨trivial, readsIn_of_slotPath hok hl p (by rw [hq]; rfl),
        ⟨trivial, Tm.readsIn_of_inLS hok hl _ h⟩⟩
    · next p _ t' =>
      obtain ⟨q', hq, he⟩ := Option.map_eq_some_iff.1 hw
      cases he
      exact ⟨trivial, readsIn_of_slotPath hok hl p (by rw [hq]; rfl),
        ⟨trivial, Tm.readsIn_of_inLS hok hl _ h⟩⟩
    · cases hw

theorem Rhs.readsB_of_inLS {ns : List Var} {ρ : SymS} (hok : ρ.Ok ns)
    (hl : ns.length = Γ.length) {t : LTy} (r : Rhs C Γ t) (h : r.inLS ρ = true) :
    r.ReadsB ρ.sym.env ns := by
  cases r <;> simp only [Rhs.inLS, Bool.false_eq_true] at h <;>
    first | exact Tm.readsIn_of_inLS hok hl _ h | trivial

theorem UpdElem.readsB_of_inLS {ns : List Var} {ρ : SymS} (hok : ρ.Ok ns)
    (hl : ns.length = Γ.length) {Δ : Ctx} (e : UpdElem C Γ Δ) (h : e.toElemS.inLS ρ = true) :
    e.ReadsB ρ.sym.env ns := by
  cases e with
  | «local» i r => exact Rhs.readsB_of_inLS hok hl r h
  | storage s => exact readsIn_of_inLSt hok hl s h
  | memory m =>
    simp only [UpdElem.toElemS, ElemS.inLS, Bool.and_eq_true] at h
    exact Tm.readsIn_of_inLS hok hl m h.1
  | net r op a | pay r a =>
    simp only [UpdElem.toElemS, ElemS.inLS, Bool.and_eq_true] at h
    exact ⟨Tm.readsIn_of_inLS hok hl r h.1, Tm.readsIn_of_inLS hok hl a h.2⟩
  | _ => simp only [UpdElem.toElemS, ElemS.inLS, Bool.false_eq_true] at h

/-- An update with no element leaves the reduction's symbols. -/
theorem replayS_sym_zero (aE : ∀ {Δ : Ctx}, UpdElem C Γ Δ → Act)
    (aR : ∀ {t : LTy}, Rhs C Γ t → Act) (ρ : SymS) : {Δ : Ctx} → (U : Upd C Γ Δ) →
      U.view = .zero → (U.replayS aE aR ρ).sym = ρ.sym
  | _, .nil, _ => rfl
  | _, .snoc U e, hv => absurd hv (UView.add_ne_zero U.view e.toElemS)
  | _, .decl U _ r, hv => absurd hv (UView.add_ne_zero U.view (.rhs r))
  | _, .pop U _, hv => replayS_sym_zero aE aR ρ U hv
  | _, .drop U _, hv => replayS_sym_zero aE aR ρ U hv

/-- An update with no element: it returns, its pops and drops applied. -/
theorem AgreeU.zero (aE : ∀ {Δ : Ctx}, UpdElem C Γ Δ → Act) (aR : ∀ {t : LTy}, Rhs C Γ t → Act)
    (h : AgreeU ρ₀ τ₀ τu) : {Δ : Ctx} → (U : Upd C Γ Δ) → U.view = .zero →
      ∃ τ', U.apply τ₀ = .ok τ' ∧ AgreeU (U.replayS aE aR ρ₀) τ' τu ∧
        (U.replayS aE aR ρ₀).sym = ρ₀.sym
  | _, .nil, _ => ⟨τ₀, rfl, h, rfl⟩
  | _, .snoc U e, hv => absurd hv (UView.add_ne_zero U.view e.toElemS)
  | _, .decl U _ r, hv => absurd hv (UView.add_ne_zero U.view (.rhs r))
  | _, .pop U hx, hv => by
    obtain ⟨τ', hτ, h', hs⟩ := AgreeU.zero aE aR h U hv
    exact ⟨τ'.drop hx, by show (U.apply τ₀).map _ = _; rw [hτ]; rfl, h'.pop hx, hs⟩
  | _, .drop U hx, hv => by
    obtain ⟨τ', hτ, h', hs⟩ := AgreeU.zero aE aR h U hv
    exact ⟨τ'.thin hx, by show (U.apply τ₀).map _ = _; rw [hτ]; rfl, h'.thin hx, hs⟩

/-- **One element, written**: its guard returns exactly where it writes,
and the state it leaves is its act's (through the erased element's step,
`Surface.UpdElem.toL_sound`). -/
theorem RelU.elem (h₀ : RelU σ ρ₀ τ₀ τu) {Δ : Ctx} {ρ₁ : SymS} {τ₁ : EState C Δ}
    (h₁ : AgreeU ρ₁ τ₁ τu) (hs : ρ₁.sym = ρ₀.sym) (e : UpdElem C Γ Δ)
    (ha : e.toElemS.inLS ρ₀ = true) :
    ((∃ v, (e.toElemS.guard ρ₀).eval σ = .ok v) ↔ ∃ τ', e.write τ₀ τ₁ = .ok τ') ∧
      ∀ τ', e.write τ₀ τ₁ = .ok τ' → ∃ τu', RelU σ (ρ₁.act e.tgt (e.actS ρ₀)) τ' τu' := by
  have hE' := UpdElem.erase_toElemS (ns := ρ₀.names) ρ₁.names e
  have hg : ((e.erase ρ₀.names ρ₁.names).toL ρ₀.sym).1 = e.toElemS.guard ρ₀ := by
    rw [hE']; exact ElemS.guard_eq h₀.ok h₀.len _ _
  have hin : (e.erase ρ₀.names ρ₁.names).inL ρ₀.sym = true := by
    rw [hE']; exact ElemS.inLS_imp h₀.ok h₀.len _ _ ha
  obtain ⟨hiff, hrel⟩ := Surface.UpdElem.toL_sound h₀.rel _ hin
  have hsim := UpdElem.write_eraseB h₀.agree h₁.agree e
    (UpdElem.readsB_of_inLS h₀.ok h₀.len e ha) .unset
  refine ⟨by rw [← hg]; exact hiff.trans (Res.Rel.ok_iff hsim).symm, fun τ' hτ => ?_⟩
  obtain ⟨τu', hw, hag⟩ := Res.Rel.of_ok hsim hτ
  obtain ⟨hok, hsym⟩ := SymS.act_ok h₁.ok h₁.agree.nodup h₁.len e (e.actS ρ₀)
    (UpdElem.actS_bind e)
  have hs' : (ρ₁.act e.tgt (e.actS ρ₀)).sym = ((e.erase ρ₀.names ρ₁.names).toL ρ₀.sym).2 := by
    rw [hsym, hs, Surface.UpdElem.toL_snd, UpdElem.nact_eq h₀.ok h₀.len]
  refine ⟨τu', ⟨h₁.act e _ (UpdElem.actS_bind e) hag fun x hx => ?_,
    by rw [hs']; exact hrel τu' hw⟩⟩
  rw [hsym] at hx
  cases e with
  | «local» i r =>
    show (lookupBy x ((i.name ρ₁.names, SymB.unset) :: ρ₁.sym.env)).isSome = true
    by_cases hxe : x = i.name ρ₁.names
    · simp only [lookupBy, hxe, ↓reduceIte, Option.isSome_some]
    · simp only [lookupBy, hxe, ↓reduceIte]
      simp only [UpdElem.actS] at hx
      cases hb : r.actS ρ₀ with
      | none => simpa only [hb, Act.ofOpt, Act.named, NAct.apply] using hx
      | some b =>
        simpa only [hb, Act.ofOpt, Act.named, NAct.apply, lookupBy, UpdElem.tgtName, hxe,
          ↓reduceIte] using hx
  | storage s =>
    simp only [UpdElem.actS, Act.named, NAct.apply, lookupBy_map_snd, Option.isSome_map] at hx
    exact hx
  | memory m =>
    simp only [UpdElem.actS] at hx
    split at hx
    · split at hx <;> simpa only [Act.named, NAct.apply] using hx
    · simpa only [Act.named, NAct.apply] using hx
  | _ => simpa only [UpdElem.actS, Act.named, NAct.apply] using hx

/-- **A declaration, written**: its guard returns exactly where its
right-hand side does, and the state it leaves binds the new position. -/
theorem RelU.decl (h₀ : RelU σ ρ₀ τ₀ τu) {Δ : Ctx} {ρ₁ : SymS} {τ₁ : EState C Δ}
    (h₁ : AgreeU ρ₁ τ₁ τu) (hs : ρ₁.sym = ρ₀.sym) {t : LTy} (r : Rhs C Γ t)
    (ha : r.inLS ρ₀ = true) :
    ((∃ v, (r.guardS ρ₀).eval σ = .ok v) ↔ ∃ d, r.eval τ₀ = .ok d) ∧
      ∀ d, r.eval τ₀ = .ok d →
        ∃ τu', RelU σ (ρ₁.push (.ofOpt (r.actS ρ₀))) (τ₁.push d) τu' := by
  have hg : ((r.erase ρ₀.names ρ₁.key).toL ρ₀.sym).1 = r.guardS ρ₀ :=
    ElemS.guard_eq h₀.ok h₀.len ρ₁.key (.rhs r)
  have hin : (r.erase ρ₀.names ρ₁.key).inL ρ₀.sym = true :=
    ElemS.inLS_imp h₀.ok h₀.len ρ₁.key (.rhs r) ha
  obtain ⟨hiff, hrel⟩ := Surface.UpdElem.toL_sound h₀.rel _ hin
  have hw := Rhs.write_eraseB h₀.agree r ρ₁.key τu (Rhs.readsB_of_inLS h₀.ok h₀.len r ha)
  refine ⟨by
    rw [← hg, hiff, hw]
    constructor
    · rintro ⟨τ', hτ⟩
      cases hd : r.eval τ₀ with
      | error e => rw [hd] at hτ; cases hτ
      | ok d => exact ⟨d, rfl⟩
    · rintro ⟨d, hd⟩
      exact ⟨_, by rw [hd]; rfl⟩, fun d hd => ?_⟩
  obtain ⟨hk, he⟩ := h₁.key_fresh
  have hr := hrel (τu.setEnv ρ₁.key (t.enc C d)) (by rw [hw, hd]; rfl)
  have hsym := (SymS.push_ok h₁.ok (.ofOpt (r.actS ρ₀)) (Act.ofOpt_cases _) hk).2
  rw [Surface.UpdElem.toL_snd, Rhs.nact_eq h₀.ok h₀.len, ← hs, ← hsym] at hr
  refine ⟨_, h₁.push _ (Act.ofOpt_cases _) d ?_, hr⟩
  rcases hb : r.actS ρ₀ with _ | b
  · have hag := (h₁.agree.setOther hk (t.enc C d)).pushFree hk he d
    simpa only [Act.ofOpt, SymS.push] using hag
  · simpa only [Act.ofOpt, SymS.push] using h₁.agree.push hk d b

/-- **An update of one element**: its guard returns exactly where the
update does, and the state it leaves is the replay's. -/
theorem RelU.one (h₀ : RelU σ ρ₀ τ₀ τu) : {Δ : Ctx} → (U : Upd C Γ Δ) → {a : ElemS C Γ} →
    U.view = .one a → a.inLS ρ₀ = true →
    ((∃ v, (a.guard ρ₀).eval σ = .ok v) ↔ ∃ τ', U.apply τ₀ = .ok τ') ∧
      ∀ τ', U.apply τ₀ = .ok τ' →
        ∃ τu', RelU σ (U.replayS (UpdElem.actS ρ₀) (fun r => .ofOpt (r.actS ρ₀)) ρ₀) τ' τu'
  | _, .nil, _, hv, _ => UView.noConfusion hv
  | _, .snoc U e, _, hv, ha => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_one hv
    obtain ⟨τ₁, hτ₁, h₁, hs⟩ :=
      h₀.toAgreeU.zero (UpdElem.actS ρ₀) (fun r => .ofOpt (r.actS ρ₀)) U hz
    have happ : (Upd.snoc U e).apply τ₀ = e.write τ₀ τ₁ := by
      show (do e.write τ₀ (← U.apply τ₀)) = _
      rw [hτ₁]; rfl
    rw [happ]
    exact RelU.elem h₀ h₁ hs e ha
  | _, .decl U x r, _, hv, ha => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_one hv
    obtain ⟨τ₁, hτ₁, h₁, hs⟩ :=
      h₀.toAgreeU.zero (UpdElem.actS ρ₀) (fun r => .ofOpt (r.actS ρ₀)) U hz
    obtain ⟨hg, hr⟩ := RelU.decl h₀ h₁ hs r ha
    have happ : (Upd.decl U x r).apply τ₀ = (fun d => τ₁.push d) <$> r.eval τ₀ := by
      show (do let τ ← U.apply τ₀; pure (τ.push (← r.eval τ₀))) = _
      rw [hτ₁]
      cases r.eval τ₀ <;> rfl
    rw [happ]
    refine ⟨hg.trans ⟨fun ⟨d, hd⟩ => ⟨_, by rw [hd]; rfl⟩, fun ⟨τ', h⟩ => ?_⟩, fun τ' h => ?_⟩
    · cases hd : r.eval τ₀ with
      | error => rw [hd] at h; cases h
      | ok d => exact ⟨d, rfl⟩
    · cases hd : r.eval τ₀ with
      | error => rw [hd] at h; cases h
      | ok d =>
        rw [hd] at h
        cases h
        exact hr d hd
  | _, .pop U hx, _, hv, ha => by
    obtain ⟨hg, hr⟩ := RelU.one h₀ U hv ha
    refine ⟨hg.trans ?_, fun τ' h => ?_⟩
    · show (∃ τ', U.apply τ₀ = .ok τ') ↔ ∃ τ', (U.apply τ₀).map (EState.drop hx) = .ok τ'
      cases U.apply τ₀ with
      | error => simp only [Except.map, reduceCtorEq, exists_false]
      | ok τ₁ => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
    · change (U.apply τ₀).map (EState.drop hx) = .ok τ' at h
      cases h₁ : U.apply τ₀ with
      | error => rw [h₁] at h; cases h
      | ok τ₁ =>
        rw [h₁] at h
        cases h
        obtain ⟨τu', h'⟩ := hr τ₁ h₁
        exact ⟨τu', h'.pop hx⟩
  | _, .drop U hx, _, hv, ha => by
    obtain ⟨hg, hr⟩ := RelU.one h₀ U hv ha
    refine ⟨hg.trans ?_, fun τ' h => ?_⟩
    · show (∃ τ', U.apply τ₀ = .ok τ') ↔ ∃ τ', (U.apply τ₀).map (EState.thin hx) = .ok τ'
      cases U.apply τ₀ with
      | error => simp only [Except.map, reduceCtorEq, exists_false]
      | ok τ₁ => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
    · change (U.apply τ₀).map (EState.thin hx) = .ok τ' at h
      cases h₁ : U.apply τ₀ with
      | error => rw [h₁] at h; cases h
      | ok τ₁ =>
        rw [h₁] at h
        cases h
        obtain ⟨τu', h'⟩ := hr τ₁ h₁
        exact ⟨τu', h'.thin hx⟩

end Updates

/-! ## An allocation's pair -/

section Pair

variable {Γ : Ctx} {σ : Semantics.State} {ρ₀ : SymS} {τ₀ : EState C Γ} {τu : Semantics.State}

/-- The identity the first element of an allocation's pair binds. -/
def mrefOf : ElemS C Γ → Option (Tm C Γ .ident)
  | .rhs (.mref i) | .glob (.local _ (.mref i)) => some i
  | _ => none

theorem pairViewS_some {a b : ElemS C Γ} {i : Tm C Γ .ident} {mm : Tm C Γ .mem}
    (h : pairViewS a b = some (i, mm)) :
    mrefOf a = some i ∧ ∃ Δ : Ctx, b = @ElemS.glob C Γ Δ (.memory mm) := by
  rcases a with r | (⟨_, r⟩ | _ | _ | _ | _ | _ | _ | _) <;>
    rcases b with r' | (⟨_, r'⟩ | _ | _ | _ | _ | _ | _ | _) <;>
    (try cases r) <;> (try cases r') <;>
    first
    | (cases h; done)
    | (injection h with h; injection h with h₁ h₂; subst h₁ h₂; exact ⟨rfl, _, rfl⟩)

theorem Res.Rel.mono {α β : Type} {R S : α → β → Prop} {x : Res α} {y : Res β}
    (h : Res.Rel R x y) (hf : ∀ a b, R a b → S a b) : Res.Rel S x y := by
  cases x <;> cases y <;> first | exact h | exact hf _ _ h

/-- What an allocation's pair reads is bound where its memory's is. -/
theorem readsIn_of_allocPair {E : List (Var × SymB)} {i : Surface.Tm C .ident}
    {mm : Surface.Tm C .mem} (h : allocPair? i mm = true) (hm : mm.ReadsIn E) : i.ReadsIn E := by
  unfold allocPair? at h
  split at h
  · exact ⟨trivial, trivial⟩
  · simp only [decide_eq_true_eq] at h
    subst h
    exact ⟨trivial, hm.2⟩
  · cases h

theorem readsIn_of_pairInS {ns : List Var} {ρ : SymS} (hok : ρ.Ok ns) (hl : ns.length = Γ.length)
    {mm : Tm C Γ .mem} (h : pairInS ρ mm = true) : (mm.erase ns).ReadsIn ρ.sym.env := by
  unfold pairInS at h
  cases hc : copyOfS? mm with
  | none =>
    rw [hc] at h
    exact Tm.readsIn_of_inLS hok hl mm h
  | some p =>
    rw [hc] at h
    unfold copyOfS? at hc
    split at hc
    · cases hc
      exact ⟨trivial, trivial, Tm.readsIn_of_inLS hok hl _ h⟩
    · cases hc

/-- **The first element of an allocation's pair**, its pops and drops
around it: it writes as its erasure, binding its local `x` to the root of
the next ordinal. -/
theorem AgreeU.half (h₀ : RelU σ ρ₀ τ₀ τu) (M : LMem) {i : Tm C Γ .ident}
    (hi : (i.erase ρ₀.names).ReadsIn ρ₀.sym.env) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → {a : ElemS C Γ} → U.view = .one a → mrefOf a = some i →
      ∃ x, Res.Rel (fun τ' τu' => AgreeU (U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀) τ' τu')
          (U.apply τ₀) ((Surface.UpdElem.mref x (i.erase ρ₀.names)).write τu τu) ∧
        (U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀).sym =
          { ρ₀.sym with env := (x, idRef ρ₀) :: ρ₀.sym.env }
  | _, .nil, _, hv, _ => UView.noConfusion hv
  | _, .snoc U e, a, hv, ha => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_one hv
    obtain ⟨τ₁, hτ₁, h₁, hs⟩ := h₀.toAgreeU.zero (pairActE ρ₀ M) (pairActR ρ₀) U hz
    cases e with
    | «local» j r =>
      cases r with
      | mref i' =>
        simp only [UpdElem.toElemS, mrefOf, Option.some.injEq] at ha
        subst ha
        refine ⟨j.name (U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀).names, ?_, ?_⟩
        · have happ : (Upd.snoc U (.local j (.mref i'))).apply τ₀ =
              (UpdElem.local j (.mref i')).write τ₀ τ₁ := by
            show (do UpdElem.write τ₀ _ (← U.apply τ₀)) = _
            rw [hτ₁]; rfl
          rw [happ]
          have hsim := UpdElem.write_eraseB h₀.agree h₁.agree (.local j (.mref i')) hi
            (idRef ρ₀)
          refine Res.Rel.mono hsim fun τ' τu' hag => ?_
          refine h₁.act (.local j (.mref i')) (pairActE ρ₀ M (.local j (.mref i')))
            (fun _ _ => rfl) hag fun x hx => ?_
          obtain ⟨-, hsym⟩ := SymS.act_ok h₁.ok h₁.agree.nodup h₁.len (.local j (.mref i'))
            (pairActE ρ₀ M (.local j (.mref i'))) (fun _ _ => rfl)
          rw [hsym] at hx
          exact hx
        · obtain ⟨-, hsym⟩ := SymS.act_ok h₁.ok h₁.agree.nodup h₁.len (.local j (.mref i'))
            (pairActE ρ₀ M (.local j (.mref i'))) (fun _ _ => rfl)
          show ((U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀).act _ _).sym = _
          rw [hsym, hs]
          rfl
      | _ => simp only [UpdElem.toElemS, mrefOf, reduceCtorEq] at ha
    | _ => simp only [UpdElem.toElemS, mrefOf, reduceCtorEq] at ha
  | _, .decl U y r, a, hv, ha => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_one hv
    obtain ⟨τ₁, hτ₁, h₁, hs⟩ := h₀.toAgreeU.zero (pairActE ρ₀ M) (pairActR ρ₀) U hz
    cases r with
    | @mref R i' =>
      simp only [mrefOf, Option.some.injEq] at ha
      subst ha
      obtain ⟨hk, -⟩ := h₁.key_fresh
      refine ⟨(U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀).key, ?_, ?_⟩
      · have happ : (Upd.decl U y (.mref (R := R) i')).apply τ₀ = (fun d => τ₁.push d) <$>
            Rhs.eval τ₀ (.mref (R := R) i') := by
          show (do let τ ← U.apply τ₀; pure (τ.push (← Rhs.eval τ₀ _))) = _
          rw [hτ₁]
          cases Rhs.eval τ₀ _ <;> rfl
        rw [happ]
        have hw := Rhs.write_eraseB h₀.agree (.mref (R := R) i')
          (U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀).key τu hi
        change Res.Rel _ _ ((Rhs.mref (R := R) i').erase ρ₀.names _ |>.write τu τu)
        rw [hw]
        cases Rhs.eval τ₀ (.mref (R := R) i') with
        | error => rfl
        | ok d =>
          exact h₁.push _ (.inr ⟨_, rfl⟩) d (h₁.agree.push hk d (idRef ρ₀))
      · change ((U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀).push (.bind (idRef ρ₀))).sym = _
        rw [(SymS.push_ok h₁.ok _ (.inr ⟨_, rfl⟩) hk).2, hs]
        rfl
    | _ => simp only [mrefOf, reduceCtorEq] at ha
  | _, .pop U hx, a, hv, ha => by
    obtain ⟨x, hr, hs⟩ := AgreeU.half h₀ M hi U hv ha
    exact ⟨x, Res.Rel.map_left hr fun _ _ h => h.pop hx, hs⟩
  | _, .drop U hx, a, hv, ha => by
    obtain ⟨x, hr, hs⟩ := AgreeU.half h₀ M hi U hv ha
    exact ⟨x, Res.Rel.map_left hr fun _ _ h => h.thin hx, hs⟩

/-- **An allocation's pair**, its pops and drops around it: its guard
returns exactly where it does (`pair_sound`, on its erasure), and the
state it leaves binds the identity to the root of the next ordinal and the
memory to the allocation. -/
theorem RelU.two (h₀ : RelU σ ρ₀ τ₀ τu) {i : Tm C Γ .ident} {mm : Tm C Γ .mem} {g : LTerm}
    {M : LMem} (hq : pairLS ρ₀ i mm = some (g, M)) (hin : pairInS ρ₀ mm = true) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → {a b : ElemS C Γ} → U.view = .two a b →
      pairViewS a b = some (i, mm) →
      ((∃ v, g.eval σ = .ok v) ↔ ∃ τ', U.apply τ₀ = .ok τ') ∧
        ∀ τ', U.apply τ₀ = .ok τ' →
          ∃ τu', RelU σ (U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀) τ' τu'
  | _, .nil, _, _, hv, _ => UView.noConfusion hv
  | _, .snoc U e, a, b, hv, hp => by
    obtain ⟨hU, rfl⟩ := UView.add_eq_two hv
    obtain ⟨hai, hb⟩ := pairViewS_some hp
    have hm := readsIn_of_pairInS h₀.ok h₀.len hin
    have hap : allocPairS? ρ₀ i mm = true := by
      unfold pairLS at hq
      split at hq
      · assumption
      · cases hq
    have hi : (i.erase ρ₀.names).ReadsIn ρ₀.sym.env := by
      unfold allocPairS? at hap
      rw [Tm.eraseR_eq, Tm.eraseR_eq, SymS.names_of_ok h₀.ok] at hap
      exact readsIn_of_allocPair hap hm
    obtain ⟨Δb, hb⟩ := hb
    cases e with
    | memory mm' =>
      simp only [UpdElem.toElemS] at hb
      injection hb with hΔ hb
      subst hΔ
      injection (eq_of_heq hb) with hb
      subst mm'
      obtain ⟨x, hr₁, hs₁⟩ := AgreeU.half h₀ M hi U hU hai
      have hq' := pairLS_eq h₀.ok h₀.len x i mm
      rw [hq, Option.map_some] at hq'
      obtain ⟨hg, hrel⟩ := pair_sound h₀.rel hq' (pairInS_imp h₀.ok h₀.len mm hin)
      have hsim : Res.Rel (AgreeB (U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀).sym.env
          (U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀).names)
          ((Upd.snoc U (.memory mm)).apply τ₀)
          (Surface.Upd.apply [.mref x (i.erase ρ₀.names), .memory (mm.erase ρ₀.names)] τu) := by
        simp only [Surface.Upd.apply, List.foldlM_cons, List.foldlM_nil, bind_pure]
        show Res.Rel _ (do UpdElem.write τ₀ (.memory mm) (← U.apply τ₀)) _
        refine Res.Rel.bind hr₁ fun τ₁ τu₁ h₁ => ?_
        exact UpdElem.write_eraseB h₀.agree h₁.agree (.memory mm) hm .unset
      refine ⟨hg.trans (Res.Rel.ok_iff hsim).symm, fun τ' hτ => ?_⟩
      obtain ⟨τu', hw, hag⟩ := Res.Rel.of_ok hsim hτ
      refine ⟨τu', ⟨?_, ?_⟩⟩
      · obtain ⟨τ₁, hτ₁⟩ : ∃ τ₁, U.apply τ₀ = .ok τ₁ := by
          change (do UpdElem.write τ₀ (.memory mm) (← U.apply τ₀)) = _ at hτ
          cases h : U.apply τ₀ with
          | error => rw [h] at hτ; cases hτ
          | ok τ₁ => exact ⟨τ₁, rfl⟩
        obtain ⟨τu₁, -, h₁⟩ := Res.Rel.of_ok hr₁ hτ₁
        exact h₁.act (.memory mm) (.mem M) (fun _ h => by cases h) hag fun x hx => hx
      · show Rel σ ((U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀).act none (.mem M)).sym τu'
        simp only [SymS.act]
        rw [hs₁]
        exact hrel τu' hw
    | _ => simp only [UpdElem.toElemS] at hb; cases hb
  | _, .decl U y r, a, b, hv, hp => by
    obtain ⟨-, rfl⟩ := UView.add_eq_two hv
    obtain ⟨-, _, hb⟩ := pairViewS_some hp
    cases hb
  | _, .pop U hx, a, b, hv, hp => by
    obtain ⟨hg, hr⟩ := RelU.two h₀ hq hin U hv hp
    refine ⟨hg.trans ?_, fun τ' h => ?_⟩
    · show (∃ τ', U.apply τ₀ = .ok τ') ↔ ∃ τ', (U.apply τ₀).map (EState.drop hx) = .ok τ'
      cases U.apply τ₀ with
      | error => simp only [Except.map, reduceCtorEq, exists_false]
      | ok τ₁ => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
    · change (U.apply τ₀).map (EState.drop hx) = .ok τ' at h
      cases h₁ : U.apply τ₀ with
      | error => rw [h₁] at h; cases h
      | ok τ₁ =>
        rw [h₁] at h
        cases h
        obtain ⟨τu', h'⟩ := hr τ₁ h₁
        exact ⟨τu', h'.pop hx⟩
  | _, .drop U hx, a, b, hv, hp => by
    obtain ⟨hg, hr⟩ := RelU.two h₀ hq hin U hv hp
    refine ⟨hg.trans ?_, fun τ' h => ?_⟩
    · show (∃ τ', U.apply τ₀ = .ok τ') ↔ ∃ τ', (U.apply τ₀).map (EState.thin hx) = .ok τ'
      cases U.apply τ₀ with
      | error => simp only [Except.map, reduceCtorEq, exists_false]
      | ok τ₁ => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
    · change (U.apply τ₀).map (EState.thin hx) = .ok τ' at h
      cases h₁ : U.apply τ₀ with
      | error => rw [h₁] at h; cases h
      | ok τ₁ =>
        rw [h₁] at h
        cases h
        obtain ⟨τu', h'⟩ := hr τ₁ h₁
        exact ⟨τu', h'.thin hx⟩

end Pair

/-! ## Through the constructors the erasure drops -/

section Peel

variable {σ : Semantics.State} {τu : Semantics.State}

/-- An update of pops and drops, on a typed state: it ends in the typed
state its pops and drops leave. -/
theorem zero_typed {Γ : Ctx} (aE : ∀ {Δ : Ctx}, UpdElem C Γ Δ → Act)
    (aR : ∀ {t : LTy}, Rhs C Γ t → Act) (τ : State C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → U.view = .zero →
      ∃ τ' : State C Δ, U.apply τ.erase = .ok τ'.erase ∧ τ'.H = τ.H
  | _, .nil, _ => ⟨τ, rfl, rfl⟩
  | _, .snoc U e, hv => absurd hv (UView.add_ne_zero U.view e.toElemS)
  | _, .decl U _ r, hv => absurd hv (UView.add_ne_zero U.view (.rhs r))
  | _, .pop U hx, hv => by
    obtain ⟨τ', hτ, hH⟩ := zero_typed aE aR τ U hv
    exact ⟨τ'.drop hx, by show (U.apply τ.erase).map _ = _; rw [hτ, State.drop_erase]; rfl, hH⟩
  | _, .drop U hx, hv => by
    obtain ⟨τ', hτ, hH⟩ := zero_typed aE aR τ U hv
    exact ⟨τ'.thin hx, by show (U.apply τ.erase).map _ = _; rw [hτ, State.thin_erase]; rfl, hH⟩

/-- **Peeling keeps the relation, the reduction's symbols and its shape.** -/
theorem peel_sym : ∀ {Γ : Ctx} (φ : Fml C Γ) {ρ : SymS} {Γ' : Ctx} {ρ' : SymS} {φ' : Fml C Γ'},
    φ.peelS ρ = ⟨Γ', ρ', φ'⟩ → ρ'.sym = ρ.sym := by
  intro Γ φ
  induction φ with
  | upd m U φ ih =>
    intro ρ Γ' ρ' φ' hp
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    split at hp
    · rw [← Fml.peelS_eq_peelSM] at hp
      have := ih (ρ := U.replayS noActE noActR ρ) hp
      rw [this]
      rename_i hv
      exact replayS_sym_zero noActE noActR ρ U hv
    · cases hp; rfl
  | bind m x t φ ih =>
    intro ρ Γ' ρ' φ' hp
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    rw [← Fml.peelS_eq_peelSM] at hp
    exact ih (ρ := ρ.push .keep) hp
  | _ => intro ρ Γ' ρ' φ' hp; cases hp; rfl

/-- **Peeling, read one way**: a formula holds where what it peels to holds
in every typed state the peeled constructors reach. -/
theorem peel_pos : ∀ {Γ : Ctx} (φ : Fml C Γ) {ρ : SymS} {Γ' : Ctx} {ρ' : SymS} {φ' : Fml C Γ'},
    φ.peelS ρ = ⟨Γ', ρ', φ'⟩ → ∀ τ : State C Γ, RelU σ ρ τ.erase τu →
      (∀ τ' : State C Γ', RelU σ ρ' τ'.erase τu → holds τ' φ') → holds τ φ := by
  intro Γ φ
  induction φ with
  | upd m U φ ih =>
    intro ρ Γ' ρ' φ' hp τ h hk
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    split at hp
    · rename_i hv
      rw [← Fml.peelS_eq_peelSM] at hp
      obtain ⟨τe, hτ, h', hs⟩ := h.toAgreeU.zero noActE noActR U hv
      show m.afterC (fun τ' => ∀ σ' : State C _, σ'.erase = τ' → τ.H <+: σ'.H → holds σ' φ)
        (U.apply τ.erase)
      rw [hτ]
      intro σ' he _
      refine ih (ρ := U.replayS noActE noActR ρ) hp σ' ⟨he ▸ h', by rw [hs]; exact h.rel⟩ hk
    · cases hp; exact hk τ h
  | bind m x t φ ih =>
    intro ρ Γ' ρ' φ' hp τ h hk
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    rw [← Fml.peelS_eq_peelSM] at hp
    intro v
    refine ih (ρ := ρ.push .keep) hp (τ.push v) ?_ hk
    rw [State.push_erase]
    exact h.pushFree _
  | _ => intro ρ Γ' ρ' φ' hp τ h hk; cases hp; exact hk τ h

/-- **Peeling, read the other way**: where a formula holds, what it peels
to holds in a typed state the peeled constructors reach. -/
theorem peel_neg : ∀ {Γ : Ctx} (φ : Fml C Γ) {ρ : SymS} {Γ' : Ctx} {ρ' : SymS} {φ' : Fml C Γ'},
    φ.peelS ρ = ⟨Γ', ρ', φ'⟩ → ∀ τ : State C Γ, RelU σ ρ τ.erase τu → holds τ φ →
      ∃ τ' : State C Γ', RelU σ ρ' τ'.erase τu ∧ holds τ' φ' := by
  intro Γ φ
  induction φ with
  | upd m U φ ih =>
    intro ρ Γ' ρ' φ' hp τ h hφ
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    split at hp
    · rename_i hv
      rw [← Fml.peelS_eq_peelSM] at hp
      obtain ⟨τe, hτ, h', hs⟩ := h.toAgreeU.zero noActE noActR U hv
      obtain ⟨τ'', hτ'', hH⟩ := zero_typed noActE noActR τ U hv
      rw [hτ''] at hτ
      cases hτ
      change m.afterC (fun τ' => ∀ σ' : State C _, σ'.erase = τ' → τ.H <+: σ'.H → holds σ' φ)
        (U.apply τ.erase) at hφ
      rw [hτ''] at hφ
      exact ih (ρ := U.replayS noActE noActR ρ) hp τ'' ⟨h', by rw [hs]; exact h.rel⟩
        (hφ τ'' rfl (hH ▸ List.prefix_refl _))
    · cases hp; exact ⟨τ, h, hφ⟩
  | bind m x t φ ih =>
    intro ρ Γ' ρ' φ' hp τ h hφ
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    rw [← Fml.peelS_eq_peelSM] at hp
    obtain ⟨v⟩ := LTy.tdenote_nonempty (C := C) (H := τ.H) t
    refine ih (ρ := ρ.push .keep) hp (τ.push v) ?_ (hφ v)
    rw [State.push_erase]
    exact h.pushFree _
  | _ => intro ρ Γ' ρ' φ' hp τ h hφ; cases hp; exact ⟨τ, h, hφ⟩

/-- Peeling reaches a typed state. -/
theorem peel_exists : ∀ {Γ : Ctx} (φ : Fml C Γ) {ρ : SymS} {Γ' : Ctx} {ρ' : SymS}
    {φ' : Fml C Γ'}, φ.peelS ρ = ⟨Γ', ρ', φ'⟩ → ∀ τ : State C Γ, RelU σ ρ τ.erase τu →
      ∃ τ' : State C Γ', RelU σ ρ' τ'.erase τu := by
  intro Γ φ
  induction φ with
  | upd m U φ ih =>
    intro ρ Γ' ρ' φ' hp τ h
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    split at hp
    · rename_i hv
      rw [← Fml.peelS_eq_peelSM] at hp
      obtain ⟨τe, hτ, h', hs⟩ := h.toAgreeU.zero noActE noActR U hv
      obtain ⟨τ'', hτ'', -⟩ := zero_typed noActE noActR τ U hv
      rw [hτ''] at hτ
      cases hτ
      exact ih (ρ := U.replayS noActE noActR ρ) hp τ'' ⟨h', by rw [hs]; exact h.rel⟩
    · cases hp; exact ⟨τ, h⟩
  | bind m x t φ ih =>
    intro ρ Γ' ρ' φ' hp τ h
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    rw [← Fml.peelS_eq_peelSM] at hp
    obtain ⟨v⟩ := LTy.tdenote_nonempty (C := C) (H := τ.H) t
    refine ih (ρ := ρ.push .keep) hp (τ.push v) ?_
    rw [State.push_erase]
    exact h.pushFree _
  | _ => intro ρ Γ' ρ' φ' hp τ h; cases hp; exact ⟨τ, h⟩

theorem Fml.asDefinedS_some {Γ : Ctx} {φ : Fml C Γ} {a : Tm C Γ .val}
    (h : φ.asDefinedS = some a) : φ = .defined a := by
  cases φ <;> simp only [Fml.asDefinedS, reduceCtorEq, Option.some.injEq] at h
  rw [h]

theorem Fml.asAndS_some {Γ : Ctx} {φ ψ₁ ψ₂ : Fml C Γ} (h : φ.asAndS = some (ψ₁, ψ₂)) :
    φ = .and ψ₁ ψ₂ := by
  cases φ <;> simp only [Fml.asAndS, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  rw [h.1, h.2]

theorem Fml.asEqS_some {Γ : Ctx} {φ : Fml C Γ} {a b : Tm C Γ .val}
    (h : φ.asEqS = some (a, b)) : φ = .eq a b := by
  cases φ <;> simp only [Fml.asEqS, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  rw [h.1, h.2]

theorem sameAt_erase {Γ Δ : Ctx} {ρa ρb : SymS} {a : Tm C Γ .val} {b : Tm C Δ .val}
    (h : sameAt ρa a ρb b = true) : a.erase ρa.names = b.erase ρb.names := by
  simp only [sameAt, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← Tm.eraseR_eq, ← Tm.eraseR_eq]
  exact h.2

/-- What `eqDViewS` recognises: `defined a ∧ (defined b ∧ a' = b')`
through peeled constructors, `a'` and `b'` the same terms as `a` and `b`. -/
theorem eqDViewS_spec {Γ : Ctx} {ρ : SymS} {φ ψ : Fml C Γ} {A B : (Γ' : Ctx) × SymS × Tm C Γ' .val}
    (h : eqDViewS ρ φ ψ = some (A, B)) :
    φ.peelS ρ = ⟨A.1, A.2.1, .defined A.2.2⟩ ∧
      ∃ (Γ' : Ctx) (ρ' : SymS) (ψ₁ ψ₂ : Fml C Γ'), ψ.peelS ρ = ⟨Γ', ρ', .and ψ₁ ψ₂⟩ ∧
        ψ₁.peelS ρ' = ⟨B.1, B.2.1, .defined B.2.2⟩ ∧
        ∃ (Γc : Ctx) (ρc : SymS) (a' b' : Tm C Γc .val), ψ₂.peelS ρ' = ⟨Γc, ρc, .eq a' b'⟩ ∧
          sameAt A.2.1 A.2.2 ρc a' = true ∧ sameAt B.2.1 B.2.2 ρc b' = true := by
  unfold eqDViewS at h
  dsimp only at h
  split at h
  · rename_i a₀ ψ₁ ψ₂ ha hb
    split at h
    · rename_i b₀ a' b' h₁ h₂
      split at h
      · rename_i hs
        simp only [Bool.and_eq_true] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, (ψ.peelS ρ).1, (ψ.peelS ρ).2.1, ψ₁, ψ₂, ?_, ?_,
          (ψ₂.peelS (ψ.peelS ρ).2.1).1, (ψ₂.peelS (ψ.peelS ρ).2.1).2.1, a', b', ?_, hs.1, hs.2⟩
        · rw [← Fml.asDefinedS_some ha]
        · rw [← Fml.asAndS_some hb]
        · rw [← Fml.asDefinedS_some h₁]
        · rw [← Fml.asEqS_some h₂]
      · cases h
    · cases h
  · cases h

end Peel

/-! ## The reduction is sound -/

section Sound

variable {Γ : Ctx}

/-- A literal, `msg.sender` or a local reads a value. -/
theorem Tm.eval_of_atomLike {t : Tm C Γ .val} (τ : EState C Γ)
    (h : t.isLitLikeS = true ∨ t.isAtomS = true) : ∃ x, t.eval τ = .ok x := by
  cases t with
  | app0 o => cases o <;> exact ⟨_, rfl⟩
  | pvV i => exact ⟨_, rfl⟩
  | _ => rcases h with h | h <;> simp only [Tm.isLitLikeS, Tm.isAtomS, Bool.false_eq_true] at h

/-- Between two terms that return, the equation is equality of the
values. -/
theorem holds_eq_of_eval {τ : State C Γ} {a b : Tm C Γ .val} {x y : Value}
    (ha : a.eval τ.erase = .ok x) (hb : b.eval τ.erase = .ok y) :
    holds τ (.eq a b) ↔ x = y := by
  show Theory.StValue.Equiv (a.denote τ.erase) (b.denote τ.erase) ↔ x = y
  rw [Tm.denote_eval τ.erase a x ha, Tm.denote_eval τ.erase b y hb,
    Theory.StValue.Equiv.prim_iff]
  exact ⟨fun h => by injection h, fun h => h ▸ rfl⟩

/-- **An equation through peeled constructors** (`eqDViewS`): both
readings return one value, read in every typed state the peels reach. -/
theorem eqD_sound {φ ψ : Fml C Γ} {σ : Semantics.State} {ρ : SymS} {τu : Semantics.State}
    {τ : State C Γ} (h : RelU σ ρ τ.erase τu) {Γa Γb : Ctx} {ρa ρb : SymS} {a : Tm C Γa .val}
    {b : Tm C Γb .val} (hv : eqDViewS ρ φ ψ = some (⟨Γa, ρa, a⟩, ⟨Γb, ρb, b⟩))
    (ha : a.inLS ρa = true) (hb : b.inLS ρb = true) :
    holds τ (.and φ ψ) ↔ (LFml.eq (a.toLS ρa) (b.toLS ρb)).holds σ := by
  obtain ⟨hpa, Γ', ρ', ψ₁, ψ₂, hpb, hp₁, Γc, ρc, a', b', hp₂, hsa, hsb⟩ := eqDViewS_spec hv
  have sa := peel_sym φ hpa
  have s' := peel_sym ψ hpb
  have sb := peel_sym ψ₁ hp₁
  have sc := peel_sym ψ₂ hp₂
  obtain ⟨τa, hra⟩ := peel_exists φ hpa τ h
  obtain ⟨τ₁, hr₁⟩ := peel_exists ψ hpb τ h
  obtain ⟨τb, hrb⟩ := peel_exists ψ₁ hp₁ τ₁ hr₁
  have ea := sameAt_erase hsa
  have eb := sameAt_erase hsb
  -- the values, read through `τu`
  have A1 : ∀ τa' : State C Γa, RelU σ ρa τa'.erase τu →
      a.eval τa'.erase = (a.erase ρa.names).eval τu := fun _ hr => (hr.eval ha).symm
  have B1 : ∀ τb' : State C Γb, RelU σ ρb τb'.erase τu →
      b.eval τb'.erase = (b.erase ρb.names).eval τu := fun _ hr => (hr.eval hb).symm
  have A2 : Sim ((a.toLS ρa).eval σ) ((a.erase ρa.names).eval τu) := by
    rw [← A1 τa hra]; exact hra.val ha
  have B2 : Sim ((b.toLS ρb).eval σ) ((b.erase ρb.names).eval τu) := by
    rw [← B1 τb hrb]; exact hrb.val hb
  have A3 : ∀ τc : State C Γc, RelU σ ρc τc.erase τu →
      a'.eval τc.erase = (a.erase ρa.names).eval τu := by
    intro τc hrc
    have hrd : (a'.erase ρc.names).ReadsIn ρc.sym.env := by
      rw [← ea, sc, s', ← sa]; exact Tm.readsIn_of_inLS hra.ok hra.len a ha
    rw [ea]; exact (Tm.eval_eraseB hrc.agree a' hrd).symm
  have B3 : ∀ τc : State C Γc, RelU σ ρc τc.erase τu →
      b'.eval τc.erase = (b.erase ρb.names).eval τu := by
    intro τc hrc
    have hrd : (b'.erase ρc.names).ReadsIn ρc.sym.env := by
      rw [← eb, sc, ← sb]; exact Tm.readsIn_of_inLS hrb.ok hrb.len b hb
    rw [eb]; exact (Tm.eval_eraseB hrc.agree b' hrd).symm
  rw [LFml.holds_eq_iff]
  constructor
  · rintro ⟨hφ, hψ⟩
    obtain ⟨τa', hra', ⟨x, hx⟩⟩ := peel_neg φ hpa τ h hφ
    obtain ⟨τ₂, hr₂, hψ₁, hψ₂⟩ := peel_neg ψ hpb τ h hψ
    obtain ⟨τb', hrb', ⟨y, hy⟩⟩ := peel_neg ψ₁ hp₁ τ₂ hr₂ hψ₁
    obtain ⟨τc, hrc, hc⟩ := peel_neg ψ₂ hp₂ τ₂ hr₂ hψ₂
    rw [A1 τa' hra'] at hx
    rw [B1 τb' hrb'] at hy
    have hxy := (holds_eq_of_eval (by rw [A3 τc hrc]; exact hx) (by rw [B3 τc hrc]; exact hy)).1 hc
    subst hxy
    exact ⟨x, (A2 x).2 hx, (B2 x).2 hy⟩
  · rintro ⟨x, hx, hy⟩
    have hx' := (A2 x).1 hx
    have hy' := (B2 x).1 hy
    refine ⟨peel_pos φ hpa τ h fun τa' hra' => ⟨x, by rw [A1 τa' hra']; exact hx'⟩,
      peel_pos ψ hpb τ h fun τ₂ hr₂ => ⟨peel_pos ψ₁ hp₁ τ₂ hr₂ fun τb' hrb' =>
        ⟨x, by rw [B1 τb' hrb']; exact hy'⟩, peel_pos ψ₂ hp₂ τ₂ hr₂ fun τc hrc =>
        (holds_eq_of_eval (by rw [A3 τc hrc]; exact hx') (by rw [B3 τc hrc]; exact hy')).2 rfl⟩⟩

/-- **The scoped reduction is sound**, over the typed state, at the
polarity `pos`: where the fragment takes a formula, its reduction read in
`σ` gives the formula in every typed state `ρ` stands for (positive), and
the formula gives its reduction (negative, where it is first-order). -/
theorem _root_.Solidity.Fml.toLSM_sound : ∀ {Γ : Ctx} (φ : Fml C Γ) (pos : Bool)
    {σ : Semantics.State} {ρ : SymS} {τu : Semantics.State} (τ : State C Γ),
    RelU σ ρ τ.erase τu → φ.inLSM pos ρ = true →
    (pos = true → (φ.toLSM ρ).holds σ → holds τ φ) ∧
      (pos = false → holds τ φ → (φ.toLSM ρ).holds σ) := by
  intro Γ φ
  induction φ with
  | tt => intro pos σ ρ τu τ h hf; exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  | eq a b =>
    intro pos σ ρ τu τ h hf
    simp only [Fml.inLSM, Bool.and_eq_true] at hf
    obtain ⟨⟨hl, ha⟩, hb⟩ := hf
    have key : holds τ (.eq a b) ↔ (Fml.toLSM ρ (.eq a b)).holds σ := by
      have hab : (a.isLitLikeS = true ∨ a.isAtomS = true) ∧
          (b.isLitLikeS = true ∨ b.isAtomS = true) := by
        simp only [Tm.eqLitS, Bool.or_eq_true, Bool.and_eq_true] at hl
        rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨.inl h1, .inr h2⟩
        · exact ⟨.inr h2, .inl h1⟩
      obtain ⟨x, hx⟩ := Tm.eval_of_atomLike τ.erase hab.1
      obtain ⟨y, hy⟩ := Tm.eval_of_atomLike τ.erase hab.2
      rw [holds_eq_of_eval hx hy]
      simp only [Fml.toLSM]
      rw [LFml.holds_eq_iff]
      have sa := h.val ha
      have sb := h.val hb
      constructor
      · rintro rfl; exact ⟨x, (sa x).2 hx, (sb x).2 hy⟩
      · rintro ⟨z, hz₁, hz₂⟩
        have e1 := (sa z).1 hz₁
        have e2 := (sb z).1 hz₂
        rw [hx] at e1; rw [hy] at e2
        cases e1; cases e2; rfl
    exact ⟨fun _ hL => key.2 hL, fun _ hφ => key.1 hφ⟩
  | defined t =>
    intro pos σ ρ τu τ h hf
    simp only [Fml.inLSM] at hf
    have st := h.val hf
    have key : holds τ (.defined t) ↔ (Fml.toLSM ρ (.defined t)).holds σ := by
      simp only [Fml.toLSM]
      rw [holds_eq_self]
      show (∃ x, t.eval τ.erase = .ok x) ↔ _
      exact ⟨fun ⟨x, hx⟩ => ⟨x, (st x).2 hx⟩, fun ⟨x, hx⟩ => ⟨x, (st x).1 hx⟩⟩
    exact ⟨fun _ hL => key.2 hL, fun _ hφ => key.1 hφ⟩
  | not φ ih =>
    intro pos σ ρ τu τ h hf
    simp only [Fml.inLSM] at hf
    have hi := ih (!pos) τ h hf
    simp only [Fml.toLSM, LFml.holds]
    refine ⟨fun hp hL hφ => ?_, fun hp hφ hL => ?_⟩
    · subst hp; exact hL (hi.2 rfl hφ)
    · subst hp; exact hφ (hi.1 rfl hL)
  | and φ ψ ihφ ihψ =>
    intro pos σ ρ τu τ h hf
    cases hv : eqDViewS ρ φ ψ with
    | none =>
      simp only [Fml.inLSM, hv, Bool.and_eq_true] at hf
      have h1 := ihφ pos τ h hf.1
      have h2 := ihψ pos τ h hf.2
      simp only [Fml.toLSM, hv, LFml.holds]
      exact ⟨fun hp hL => ⟨h1.1 hp hL.1, h2.1 hp hL.2⟩,
        fun hp hφ => ⟨h1.2 hp hφ.1, h2.2 hp hφ.2⟩⟩
    | some AB =>
      obtain ⟨⟨Γa, ρa, a⟩, ⟨Γb, ρb, b⟩⟩ := AB
      simp only [Fml.inLSM, hv, Bool.and_eq_true] at hf
      have key := eqD_sound h hv hf.1 hf.2
      simp only [Fml.toLSM, hv]
      exact ⟨fun _ hL => key.2 hL, fun _ hφ => key.1 hφ⟩
  | imp φ ψ ihφ ihψ =>
    intro pos σ ρ τu τ h hf
    simp only [Fml.inLSM, Bool.and_eq_true] at hf
    have h1 := ihφ (!pos) τ h hf.1
    have h2 := ihψ pos τ h hf.2
    simp only [Fml.toLSM, LFml.holds]
    refine ⟨fun hp hL hφ => h2.1 hp (hL (h1.2 (by rw [hp]; rfl) hφ)),
      fun hp hφψ hL => h2.2 hp (hφψ (h1.1 (by rw [hp]; rfl) hL))⟩
  | upd m U φ ih =>
    intro pos σ ρ τu τ h hf
    simp only [Fml.inLSM, Bool.and_eq_true] at hf
    obtain ⟨rfl, hf⟩ := hf
    refine ⟨fun _ hL => ?_, fun hp => Bool.noConfusion hp⟩
    show m.afterC (fun τ' => ∀ σ' : State C _, σ'.erase = τ' → τ.H <+: σ'.H → holds σ' φ)
      (U.apply τ.erase)
    cases hv : U.view with
    | zero =>
      simp only [Fml.toLSM, hv] at hL
      simp only [hv] at hf
      obtain ⟨τe, hτ, h', hs⟩ := h.toAgreeU.zero noActE noActR U hv
      rw [hτ]
      intro σ' he _
      exact (ih true σ' (by rw [he]; exact ⟨h', by rw [hs]; exact h.rel⟩) hf).1 rfl hL
    | one a =>
      simp only [Fml.toLSM, hv] at hL
      simp only [hv, Bool.and_eq_true] at hf
      obtain ⟨hg, hr⟩ := RelU.one h U hv hf.1
      cases hap : U.apply τ.erase with
      | error e =>
        cases m with
        | box => trivial
        | diamond =>
          rw [guardM_diamond] at hL
          obtain ⟨τ', h'⟩ := hg.1 hL.1
          rw [hap] at h'; cases h'
      | ok τe =>
        intro σ' he _
        have hgret : ∃ v, (a.guard ρ).eval σ = .ok v := hg.2 ⟨τe, hap⟩
        have hL' : (φ.toLSM (U.replayS (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ)).holds σ := by
          cases m with
          | box => exact (guardM_box σ _ _).1 hL hgret
          | diamond => exact ((guardM_diamond σ _ _).1 hL).2
        obtain ⟨τu', hrel⟩ := hr τe hap
        exact (ih true σ' (by rw [he]; exact hrel) hf.2).1 rfl hL'
    | two a b =>
      simp only [Fml.toLSM, hv] at hL
      simp only [hv] at hf
      cases hp : pairViewS a b with
      | none => simp only [hp, Bool.false_eq_true] at hf
      | some p =>
        obtain ⟨i, mm⟩ := p
        cases hq : pairLS ρ i mm with
        | none => simp only [hp, hq, Bool.false_eq_true] at hf
        | some q =>
          obtain ⟨g, M⟩ := q
          simp only [hp, hq, Bool.and_eq_true] at hf hL
          obtain ⟨hg, hr⟩ := RelU.two h hq hf.1.1 U hv hp
          cases hap : U.apply τ.erase with
          | error e =>
            cases m with
            | box => trivial
            | diamond =>
              rw [guardM_diamond] at hL
              obtain ⟨τ', h'⟩ := hg.1 hL.1
              rw [hap] at h'; cases h'
          | ok τe =>
            intro σ' he _
            have hgret : ∃ v, g.eval σ = .ok v := hg.2 ⟨τe, hap⟩
            have hL' : (φ.toLSM (U.replayS (pairActE ρ M) (pairActR ρ) ρ)).holds σ := by
              cases m with
              | box => exact (guardM_box σ _ _).1 hL hgret
              | diamond => exact ((guardM_diamond σ _ _).1 hL).2
            obtain ⟨τu', hrel⟩ := hr τe hap
            exact (ih true σ' (by rw [he]; exact hrel) hf.2).1 rfl hL'
    | many => simp only [hv, Bool.false_eq_true] at hf
  | modal m P κ φ ih =>
    intro pos σ ρ τu τ h hf
    simp only [Fml.inLSM] at hf
    subst hf
    refine ⟨fun _ hL => ?_, fun hp => Bool.noConfusion hp⟩
    simp only [Fml.toLSM, LFml.holds] at hL
    exact absurd trivial hL
  | havoc φ ih =>
    intro pos σ ρ τu τ h hf
    simp only [Fml.inLSM, Bool.false_eq_true] at hf
  | anon xs φ ih =>
    intro pos σ ρ τu τ h hf
    simp only [Fml.inLSM, Bool.false_eq_true] at hf
  | all x p φ ih =>
    intro pos σ ρ τu τ h hf
    simp only [Fml.inLSM, Bool.and_eq_true, Bool.not_eq_true'] at hf
    obtain ⟨hx, hf⟩ := hf
    simp only [Fml.toLSM, LFml.holds]
    refine ⟨fun hp hL v => ?_, fun hp hφ w hw => ?_⟩
    · exact (ih pos (τ.push v) (by rw [State.push_erase]; exact h.pushQ hx (PrimTy.erase v))
        hf).1 hp (hL _ (PrimTy.admits_erase v))
    · obtain ⟨v, rfl⟩ := PrimTy.exists_of_admits hw
      exact (ih pos (τ.push v) (by rw [State.push_erase]; exact h.pushQ hx (PrimTy.erase v))
        hf).2 hp (hφ v)
  | bind m x t φ ih =>
    intro pos σ ρ τu τ h hf
    simp only [Fml.inLSM, Bool.and_eq_true] at hf
    obtain ⟨rfl, hf⟩ := hf
    refine ⟨fun _ hL => ?_, fun hp => Bool.noConfusion hp⟩
    simp only [Fml.toLSM] at hL
    intro v
    exact (ih true (τ.push v) (by rw [State.push_erase]; exact h.pushFree _) hf).1 rfl hL

/-- **The boundary, scoped**: a leaf is valid where its reduction, computed
on the leaf itself, holds in every state; the fragment is checked on the
leaf (`Fml.inLS`).  Proved over the typed state (`Fml.toLSM_sound`), not
through the leaf's erasure. -/
theorem _root_.Solidity.Valid.of_reduceS {φ : Fml C []} (hf : φ.inLS true SymS.empty = true)
    (h : ∀ σ, φ.reduceS.holds σ) : Valid φ := by
  intro τ
  let σ : Semantics.State := withLocals τ.erase.glob []
  have hr : RelU σ SymS.empty τ.erase σ :=
    ⟨⟨rfl, ⟨rfl, List.nodup_nil, rfl, fun _ hm => nomatch hm⟩,
      fun _ _ => ⟨List.not_mem_nil, rfl⟩⟩, Rel.empty σ⟩
  have hL : (φ.toLSM SymS.empty).holds σ := by
    rw [← Fml.toLS_eq_toLSM]
    exact (LFml.elim_holds σ _).1 (h σ)
  exact (Fml.toLSM_sound φ true τ hr (by rw [← Fml.inLS_eq_inLSM]; exact hf)).1 rfl hL

end Sound

end Decide

end Solidity
