import Solidity.Calculus.Core.Logic
import Solidity.Semantics.RunErase

/-!
# A scoped formula holds where its erasure does

`holds_erase` (`docs/intrinsic.md`, M6a): a scoped formula holds in `σ`
exactly where its erasure (`Fml.erase`, `Calculus/Core/Fml.lean`) holds,
by `Update.lean`'s `holds`, in any untyped state that agrees with `σ` on the
locals named `ns` (`Agree`, `Semantics/RunErase.lean`).  The pieces:

* a term reads alike (`Tm.eval_erase`): a value, a path, an identity the
  same, a storage or memory the same up to the locals the untyped state
  carries (`StEq`), since every symbol reads the global part only (the
  `*_nat`/`*_wl` lemmas of `Semantics/RunErase.lean`); it denotes the same
  (`Tm.denote_erase`);
* an update ends in agreeing states (`Upd.apply_erase`), a declaration under
  a fresh name;
* a modality's program is `run_erase`'s (`Prog.erasesAt`), its frames the
  statements they hold, a scope's end nothing (the untyped state keeps the
  popped locals, which `Agree` allows).

The formulas are `Fml.Plain`: every binder fresh (a declaration, a `∀`, a
block's locals: `Prog.Fresh`), and no hidden binder or anonymising update,
whose untyped readings range over more than the typed ones (the untyped
`anon` over every binding, the erased hidden binder over whatever the name
held before).
-/

namespace Solidity.Core

open Semantics (Value SVal MVal Seg Halt Res Binding lookupBy setBy)
open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract}

/-! ## Readings alike -/

/-- Two global parts alike up to the locals they carry. -/
def StEq (s₁ s₂ : Semantics.State) : Prop := withLocals s₁ [] = withLocals s₂ []

theorem StEq.refl (s : Semantics.State) : StEq s s := rfl
theorem StEq.symm {s₁ s₂ : Semantics.State} (h : StEq s₁ s₂) : StEq s₂ s₁ := Eq.symm h
theorem StEq.trans {s₁ s₂ s₃ : Semantics.State} (h : StEq s₁ s₂) (h' : StEq s₂ s₃) : StEq s₁ s₃ :=
  Eq.trans h h'

theorem StEq.wl (s : Semantics.State) (e e' : List (Var × Binding)) :
    StEq (withLocals s e) (withLocals s e') := rfl

/-- A state is its global part with its locals. -/
theorem wl_env (s : Semantics.State) : withLocals (withLocals s []) s.env = s := rfl

/-- Two outcomes alike: the same halt, or related results. -/
def Res.Rel {α β : Type} (R : α → β → Prop) : Res α → Res β → Prop
  | .ok a, .ok b => R a b
  | .error e, .error e' => e = e'
  | _, _ => False

theorem Res.Rel.of_eq {α : Type} {R : α → α → Prop} (hR : ∀ a, R a a) {x y : Res α} (h : x = y) :
    Res.Rel R x y := by
  subst h; cases x <;> simp only [Res.Rel, hR]

theorem Res.Rel.bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {x : Res α} {y : Res β}
    (h : Res.Rel R x y) {f : α → Res γ} {g : β → Res δ} (hfg : ∀ a b, R a b → Res.Rel S (f a) (g b)) :
    Res.Rel S (x >>= f) (y >>= g) := by
  cases x with
  | ok a => cases y with
    | ok b => exact hfg a b h
    | error => exact h.elim
  | error e => cases y with
    | ok => exact h.elim
    | error e' => exact h

theorem Res.Rel.bind_same {α γ δ : Type} {S : γ → δ → Prop} (x : Res α) {f : α → Res γ}
    {g : α → Res δ} (h : ∀ a, x = .ok a → Res.Rel S (f a) (g a)) : Res.Rel S (x >>= f) (x >>= g) := by
  cases hx : x with
  | ok a => exact h a hx
  | error e => rfl

theorem Res.Rel.map_left {α β γ : Type} {R : α → β → Prop} {S : γ → β → Prop} {x : Res α}
    {y : Res β} (h : Res.Rel R x y) {f : α → γ} (hf : ∀ a b, R a b → S (f a) b) :
    Res.Rel S (x.map f) y := by
  cases x with
  | ok a => cases y with
    | ok b => exact hf a b h
    | error => exact h.elim
  | error e => cases y with
    | ok => exact h.elim
    | error e' => exact h

theorem Res.Rel.map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {x : Res α} {y : Res β}
    (h : Res.Rel R x y) {f : α → γ} {g : β → δ} (hfg : ∀ a b, R a b → S (f a) (g b)) :
    Res.Rel S (f <$> x) (g <$> y) := by
  cases x with
  | ok a => cases y with
    | ok b => exact hfg a b h
    | error => exact h.elim
  | error e => cases y with
    | ok => exact h.elim
    | error e' => exact h

/-- How a term's reading is alike: a storage or a memory up to the locals,
anything else the same. -/
def Srt.EvRel : (s : Srt) → s.Ev → s.Ev → Prop
  | .st, x, y => Res.Rel StEq x y
  | .mem, x, y => Res.Rel StEq x y
  | .val, x, y => x = y
  | .path, x, y => x = y
  | .sv, x, y => x = y
  | .ident, x, y => x = y
  | .addr, x, y => x = y
  | .mv, x, y => x = y

/-- An operation on the global part, natural in the locals, does alike on
alike parts. -/
theorem Natural.rel {f : Semantics.State → Res Semantics.State} (hf : Natural f)
    {s₁ s₂ : Semantics.State} (h : StEq s₁ s₂) : Res.Rel StEq (f s₁) (f s₂) := by
  have h₁ : f s₁ = (fun s' => withLocals s' s₁.env) <$> f (withLocals s₁ []) := hf (withLocals s₁ []) s₁.env
  have h₂ : f s₂ = (fun s' => withLocals s' s₂.env) <$> f (withLocals s₂ []) := hf (withLocals s₂ []) s₂.env
  rw [h₁, h₂, show withLocals s₁ [] = withLocals s₂ [] from h]
  cases f (withLocals s₂ []) with
  | error => rfl
  | ok u => exact StEq.wl u _ _

theorem NaturalA.rel {α : Type} {f : Semantics.State → Res (Semantics.State × α)} (hf : NaturalA f)
    {s₁ s₂ : Semantics.State} (h : StEq s₁ s₂) :
    Res.Rel (fun a b => StEq a.1 b.1 ∧ a.2 = b.2) (f s₁) (f s₂) := by
  have h₁ : f s₁ = (fun p => (withLocals p.1 s₁.env, p.2)) <$> f (withLocals s₁ []) := hf (withLocals s₁ []) s₁.env
  have h₂ : f s₂ = (fun p => (withLocals p.1 s₂.env, p.2)) <$> f (withLocals s₂ []) := hf (withLocals s₂ []) s₂.env
  rw [h₁, h₂, show withLocals s₁ [] = withLocals s₂ [] from h]
  cases f (withLocals s₂ []) with
  | error => rfl
  | ok u => exact ⟨StEq.wl u.1 _ _, rfl⟩

/-- A reading of the global part reads alike parts alike. -/
theorem StEq.read {α : Type} {f : Semantics.State → α}
    (hf : ∀ s e, f (withLocals s e) = f s) {s₁ s₂ : Semantics.State} (h : StEq s₁ s₂) :
    f s₁ = f s₂ := by
  have h₁ : f s₁ = f (withLocals s₁ []) := hf (withLocals s₁ []) s₁.env
  have h₂ : f s₂ = f (withLocals s₂ []) := hf (withLocals s₂ []) s₂.env
  rw [h₁, h₂]
  exact congrArg f h

/-! ## Symbols read the global part -/

/-- A reading with the locals `e` put back into its storage or memory. -/
def Srt.wl (e : List (Var × Binding)) : (s : Srt) → s.Ev → s.Ev
  | .st, x => (withLocals · e) <$> x
  | .mem, x => (withLocals · e) <$> x
  | .val, x => x
  | .path, x => x
  | .sv, x => x
  | .ident, x => x
  | .addr, x => x
  | .mv, x => x

section Ops

variable (g : Semantics.State) (e : List (Var × Binding))

theorem Op0.eval_wl {s : Srt} (o : Op0 s) : o.eval (withLocals g e) = Srt.wl e s (o.eval g) := by
  cases o <;> rfl

theorem Op1.eval_wl {a s : Srt} (o : Op1 a s) (ho : o.named = false) (x : a.Ev) :
    o.eval (withLocals g e) (Srt.wl e a x) = Srt.wl e s (o.eval g x) := by
  cases o with
  | netOf => cases ho
  | select r =>
    show (do let τ ← (withLocals · e) <$> x; _) = (withLocals · e) <$> (do let τ ← x; _)
    cases x with
    | error => rfl
    | ok τ =>
      have h₁ : ((withLocals · e) <$> (Except.ok τ : Res Semantics.State)) = .ok (withLocals τ e) := rfl
      rw [h₁]
      simp only [bind, Except.bind, findStorage_wl]
      cases τ.findStorage r [] with
      | error => rfl
      | ok v => cases v <;> rfl
  | alloc R =>
    show (do let τ ← (withLocals · e) <$> x; return (← Semantics.allocDefault τ R).2) =
      (do let τ ← x; return (← Semantics.allocDefault τ R).2)
    cases x with
    | error => rfl
    | ok τ =>
      show (do return (← Semantics.allocDefault (withLocals τ e) R).2) = _
      have h := allocDefault_nat R τ e
      simp only at h
      rw [h]
      simp only [bind, Except.bind, Functor.map, Except.map]
      cases Semantics.allocDefault τ R <;> rfl
  | addM R =>
    show (do let τ ← (withLocals · e) <$> x; return (← Semantics.allocDefault τ R).1) =
      (withLocals · e) <$> (do let τ ← x; return (← Semantics.allocDefault τ R).1)
    cases x with
    | error => rfl
    | ok τ =>
      show (do return (← Semantics.allocDefault (withLocals τ e) R).1) = _
      have h := allocDefault_nat R τ e
      simp only at h
      rw [h]
      simp only [bind, Except.bind, Functor.map, Except.map]
      cases Semantics.allocDefault τ R <;> rfl
  | wt vs =>
    cases x with
    | error => rfl
    | ok τ => rfl
  | _ => rfl

end Ops

section OpLemmas

variable (s : Semantics.State) (e : List (Var × Binding))

theorem saveStorage_wl' (r : Name) (segs : List Seg) (v : SVal) :
    (withLocals s e).saveStorage r segs v = (withLocals · e) <$> s.saveStorage r segs v :=
  saveStorage_nat r segs v s e

theorem writeStorage_wl' (r : Name) (segs : List Seg) (v : SVal) :
    (withLocals s e).writeStorage r segs v = (withLocals · e) <$> s.writeStorage r segs v :=
  writeStorage_nat r segs v s e

theorem pushAt_wl' (E : Ty) (r : Name) (segs : List Seg) (val : SVal → Res SVal) :
    pushAt (withLocals s e) E r segs val = (withLocals · e) <$> pushAt s E r segs val :=
  pushAt_nat E r segs val s e

theorem popAt_wl' (keep : Bool) (r : Name) (segs : List Seg) :
    popAt (withLocals s e) keep r segs = (withLocals · e) <$> popAt s keep r segs :=
  popAt_nat keep r segs s e

theorem pushPlaceAt_wl' (E : Ty) (r : Name) (segs : List Seg) :
    pushPlaceAt (withLocals s e) E r segs =
      (fun p => (withLocals p.1 e, p.2)) <$> pushPlaceAt s E r segs :=
  pushPlaceAt_nat E r segs s e

theorem writeAddr_wl' (mv : MVal) (a : Semantics.Addr) :
    writeAddr (withLocals s e) mv a = (withLocals · e) <$> writeAddr s mv a :=
  writeAddr_nat mv a s e

theorem readAddr_wl (a : Semantics.Addr) : readAddr (withLocals s e) a = readAddr s a := by
  cases a <;> rfl

end OpLemmas

/-- The monad laws the readings are normalized with. -/
macro "wl_norm" : tactic => `(tactic| simp only [Srt.wl, Op2.eval, Op3.eval, findStorage_wl,
  checkIndex_wl, arrayLen_wl, memArrayLen_wl, copyMem_wl, readAddr_wl, saveStorage_wl',
  writeStorage_wl', pushAt_wl', popAt_wl', pushPlaceAt_wl', writeAddr_wl', copyStToM_nat,
  map_bind, bind_map_left, bind_assoc, pure_bind, map_pure, Functor.map_map])

section Ops2

variable (g : Semantics.State) (e : List (Var × Binding))

theorem Op2.eval_wl {a b s : Srt} (o : Op2 a b s) (x : a.Ev) (y : b.Ev) :
    o.eval (withLocals g e) (Srt.wl e a x) (Srt.wl e b y) = Srt.wl e s (o.eval g x y) := by
  cases o <;> wl_norm

theorem Op3.eval_wl {a b c s : Srt} (o : Op3 a b c s) (x : a.Ev) (y : b.Ev) (z : c.Ev) :
    o.eval (withLocals g e) (Srt.wl e a x) (Srt.wl e b y) (Srt.wl e c z) =
      Srt.wl e s (o.eval (withLocals g e) x y z) := by
  cases o <;> wl_norm

end Ops2

/-! ## A term reads and denotes as its erasure -/

section Terms

variable {Γ : Ctx} {ns : List Var} {σ : State C Γ} {τ : Semantics.State}

theorem Agree.wl (hag : Agree ns σ τ) : τ = withLocals σ.glob τ.env := hag.glob.symm

/-- **A term reads as its erasure**: the storage and memory it reads to carry
the untyped state's locals. -/
theorem Tm.eval_erase (hag : Agree ns σ τ) : {s : Srt} → (t : Tm C Γ s) →
    (t.erase ns).eval τ = Srt.wl τ.env s (t.eval σ)
  | _, .pvV i => by
    simp only [Tm.erase, Solidity.Tm.eval, hag.getEnv i]; rfl
  | _, .pvP i => aliasPath_erase hag i
  | _, .pvS i => by
    simp only [Tm.erase, Solidity.Tm.eval, hag.getEnv i]
    rw [hag.wl]; rfl
  | _, .pvI i => by
    simp only [Tm.erase, Solidity.Tm.eval, hag.getEnv i]; rfl
  | _, .netOf i a => by
    show Op1.eval τ (.netOf (i.name ns)) ((a.erase ns).eval τ) = _
    rw [Tm.eval_erase hag a]
    simp only [Op1.eval, hag.getEnv i]
    rfl
  | _, .app0 o => by
    show o.eval τ = _
    rw [hag.wl]; exact Op0.eval_wl _ _ o
  | _, .app1 o ho x => by
    show o.eval τ ((x.erase ns).eval τ) = _
    rw [Tm.eval_erase hag x, hag.wl]
    exact Op1.eval_wl _ _ o ho _
  | _, .app2 o x y => by
    show o.eval τ ((x.erase ns).eval τ) ((y.erase ns).eval τ) = _
    rw [Tm.eval_erase hag x, Tm.eval_erase hag y, hag.wl]
    exact Op2.eval_wl _ _ o _ _
  | _, .app3 o x y z => by
    show o.eval τ ((x.erase ns).eval τ) ((y.erase ns).eval τ) ((z.erase ns).eval τ) = _
    rw [Tm.eval_erase hag x, Tm.eval_erase hag y, Tm.eval_erase hag z, Op3.eval_wl]
    rfl

end Terms

section Denote

variable (g : Semantics.State) (e : List (Var × Binding))

theorem Op0.denote_wl {s : Srt} (o : Op0 s) : o.denote (withLocals g e) = o.denote g := by
  cases o <;> rfl

theorem Op1.denote_wl {a s : Srt} (o : Op1 a s) (ho : o.named = false) (d : a.Den) :
    o.denote (withLocals g e) d = o.denote g d := by
  cases o with
  | netOf => cases ho
  | _ => rfl

theorem Op2.denote_wl {a b s : Srt} (o : Op2 a b s) (x : a.Ev) (y : b.Ev) (dx : a.Den) (dy : b.Den) :
    o.denote (withLocals g e) (Srt.wl e a x) (Srt.wl e b y) dx dy = o.denote g x y dx dy := by
  cases o with
  | read => simp only [Op2.denote]; rw [Op2.eval_wl]; rfl
  | mlen => simp only [Op2.denote]; rw [Op2.eval_wl]; rfl
  | copyMem => simp only [Op2.denote]; rw [Op2.eval_wl]; rfl
  | _ => rfl

end Denote

section TermsDenote

variable {Γ : Ctx} {ns : List Var} {σ : State C Γ} {τ : Semantics.State}

/-- **A term denotes as its erasure.** -/
theorem Tm.denote_erase (hag : Agree ns σ τ) : {s : Srt} → (t : Tm C Γ s) →
    (t.erase ns).denote τ = t.denote σ
  | _, .pvV i => by simp only [Tm.erase, Solidity.Tm.denote, hag.getEnv i]; rfl
  | _, .pvP i => by simp only [Tm.erase, Solidity.Tm.denote, aliasPath_erase hag i]; rfl
  | _, .pvS i => by simp only [Tm.erase, Solidity.Tm.denote, hag.getEnv i]; rfl
  | _, .pvI i => rfl
  | _, .netOf i a => by
    show Op1.denote τ (.netOf (i.name ns)) ((a.erase ns).denote τ) = _
    rw [Tm.denote_erase hag a]
    simp only [Op1.denote, hag.getEnv i, Tm.denote]
    generalize a.denote σ = d
    cases d with
    | prim v => cases v <;> rfl
    | st => rfl
  | _, .app0 o => by
    show o.denote τ = _
    rw [hag.wl]; exact Op0.denote_wl _ _ o
  | _, .app1 o ho x => by
    show o.denote τ ((x.erase ns).denote τ) = _
    rw [Tm.denote_erase hag x, hag.wl]
    exact Op1.denote_wl _ _ o ho _
  | _, .app2 o x y => by
    show o.denote τ ((x.erase ns).eval τ) ((y.erase ns).eval τ) ((x.erase ns).denote τ)
      ((y.erase ns).denote τ) = _
    rw [Tm.denote_erase hag x, Tm.denote_erase hag y, Tm.eval_erase hag x, Tm.eval_erase hag y,
      hag.wl]
    exact Op2.denote_wl _ _ o _ _ _ _
  | _, .app3 o x y z => by
    show o.denote ((x.erase ns).denote τ) ((y.erase ns).denote τ) ((z.erase ns).denote τ) = _
    rw [Tm.denote_erase hag x, Tm.denote_erase hag y, Tm.denote_erase hag z]
    rfl

end TermsDenote

/-! ## A thinning keeps a sublist of the names -/

section Thin

theorem Thin.names_length : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (ns : List Var) →
    ns.length = Δ.length → (h.names ns).length = Γ.length
  | _, _, .refl, _, hl => hl
  | _, _, .keep h, n :: ns, hl => by
    simp only [Thin.names, List.length_cons] at hl ⊢
    rw [Thin.names_length h ns (by omega)]
  | _, _, .keep _, [], hl => by simp only [List.length_nil, List.length_cons] at hl; omega
  | _, _, .drop h, ns, hl => by
    simp only [Thin.names]
    exact Thin.names_length h ns.tail (by simp only [List.length_tail, hl, List.length_cons]; omega)

theorem Thin.names_sublist : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (ns : List Var) →
    (h.names ns).Sublist ns
  | _, _, .refl, _ => List.Sublist.refl _
  | _, _, .keep h, n :: ns => (Thin.names_sublist h ns).cons₂ n
  | _, _, .keep h, [] => Thin.names_sublist h []
  | _, _, .drop h, ns => (Thin.names_sublist h ns.tail).trans (List.tail_sublist ns)

theorem Env.mem_erase_thin : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (ns : List Var) → (e : Env C Δ) →
    ns.length = Δ.length → ∀ m ∈ Env.erase (h.names ns) (Env.thin h e), m ∈ Env.erase ns e
  | _, _, .refl, _, _, _, m, hm => hm
  | _, _, .keep h, n :: ns, e, hl, m, hm => by
    simp only [Thin.names, Env.thin, Env.erase, List.mem_cons] at hm ⊢
    rcases hm with hm | hm
    · exact .inl hm
    · exact .inr (Env.mem_erase_thin h ns e.2 (by simp only [List.length_cons] at hl; omega) m hm)
  | _, _, .keep _, [], _, hl, _, _ => by simp only [List.length_nil, List.length_cons] at hl; omega
  | _, _, .drop h, n :: ns, e, hl, m, hm => by
    simp only [Thin.names, Env.thin, List.tail_cons] at hm
    simp only [Env.erase, List.mem_cons]
    exact .inr (Env.mem_erase_thin h ns e.2 (by simp only [List.length_cons] at hl; omega) m hm)
  | _, _, .drop _, [], _, hl, _, _ => by simp only [List.length_nil, List.length_cons] at hl; omega

/-- A frame dropped from under what it keeps: the kept locals are still
bound under their names. -/
theorem Agree.thin {Γ Δ : Ctx} {ns : List Var} {σ : State C Δ} {τ : Semantics.State}
    (hag : Agree ns σ τ) (h : Thin Γ Δ) : Agree (h.names ns) (σ.thin h) τ where
  len := Thin.names_length h ns hag.len
  nodup := (Thin.names_sublist h ns).nodup hag.nodup
  glob := hag.glob
  env m hm := hag.env m (Env.mem_erase_thin h ns σ.env hag.len m hm)

/-- A scope's locals popped, the names of what is left. -/
theorem Agree.dropNames {Γ Δ : Ctx} {ns : List Var} {σ : State C Δ} {τ : Semantics.State}
    (hag : Agree ns σ τ) (h : Ext Γ Δ) : Agree (ns.drop h.depth) (σ.drop h) τ := by
  have hl : (ns.take h.depth).length = h.depth := by
    rw [List.length_take, hag.len, h.length_eq]; omega
  exact Agree.drop (by rw [List.take_append_drop]; exact hag) h hl

end Thin

/-! ## An update ends in agreeing states -/

/-- Every local an update declares takes a name not in scope. -/
def Upd.Fresh {Γ : Ctx} (ns : List Var) : {Δ : Ctx} → Upd C Γ Δ → Prop
  | _, .nil => True
  | _, .snoc U _ => U.Fresh ns
  | _, .decl U x _ => U.Fresh ns ∧ x ∉ U.names ns
  | _, .pop U _ => U.Fresh ns
  | _, .drop U _ => U.Fresh ns

section Updates

variable {Γ : Ctx} {ns : List Var} {σ₀ : State C Γ} {τ₀ : Semantics.State}

theorem Rhs.write_erase (hag : Agree ns σ₀ τ₀) {t : LTy} (r : Rhs C Γ t) (x : Var)
    (τ : Semantics.State) :
    (r.erase ns x).write τ₀ τ = (fun v => τ.setEnv x (t.enc C v)) <$> r.eval σ₀ := by
  cases r with
  | val a =>
    simp only [Rhs.erase, Solidity.UpdElem.write, Tm.eval_erase hag a, Srt.wl, Rhs.eval]
    cases a.eval σ₀ <;> rfl
  | path p =>
    simp only [Rhs.erase, Solidity.UpdElem.write, Tm.eval_erase hag p, Srt.wl, Rhs.eval]
    cases p.eval σ₀ <;> rfl
  | unset => rfl
  | mref i =>
    simp only [Rhs.erase, Solidity.UpdElem.write, Tm.eval_erase hag i, Srt.wl, Rhs.eval]
    cases i.eval σ₀ <;> rfl
  | store st =>
    simp only [Rhs.erase, Solidity.UpdElem.write, Tm.eval_erase hag st, Srt.wl, Rhs.eval]
    cases st.eval σ₀ <;> rfl
  | saveNet => simp only [Rhs.erase, Solidity.UpdElem.write, Rhs.eval]; rw [hag.wl]; rfl
  | saveNetMt => rfl

/-- One element written into agreeing states, read in agreeing ones. -/
theorem UpdElem.write_erase (hag : Agree ns σ₀ τ₀) {Δ : Ctx} {ms : List Var} {σ : State C Δ}
    {τ : Semantics.State} (hag' : Agree ms σ τ) (e : UpdElem C Γ Δ) :
    Res.Rel (Agree ms) (e.write σ₀ σ) ((e.erase ns ms).write τ₀ τ) := by
  rw [hag'.wl]
  cases e with
  | «local» i r =>
    rw [← hag'.wl]
    simp only [UpdElem.erase, UpdElem.write, Rhs.write_erase hag]
    cases r.eval σ₀ with
    | error => rfl
    | ok v => exact hag'.setLocal i v
  | storage st =>
    simp only [UpdElem.erase, UpdElem.write, Solidity.UpdElem.write, Tm.eval_erase hag st, Srt.wl]
    cases st.eval σ₀ with
    | error => rfl
    | ok g => exact hag'.withGlob _
  | memory mm =>
    simp only [UpdElem.erase, UpdElem.write, Solidity.UpdElem.write, Tm.eval_erase hag mm, Srt.wl]
    cases mm.eval σ₀ with
    | error => rfl
    | ok g => exact hag'.withGlob _
  | selfBalance op a =>
    simp only [UpdElem.erase, UpdElem.write, Solidity.UpdElem.write, Tm.eval_erase hag a, Srt.wl]
    rw [hag.wl]
    exact Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun _ _ => hag'.withGlob _
  | net r op a =>
    simp only [UpdElem.erase, UpdElem.write, Solidity.UpdElem.write, Tm.eval_erase hag r,
      Tm.eval_erase hag a, Srt.wl]
    exact Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun _ _ =>
      Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun _ _ => hag'.withGlob _
  | pay r a =>
    simp only [UpdElem.erase, UpdElem.write, Solidity.UpdElem.write, Tm.eval_erase hag r,
      Tm.eval_erase hag a, Srt.wl]
    rw [hag.wl]
    refine Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun _ _ =>
      Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun k _ => ?_
    by_cases hk : k < 0
    · simp only [hk, ↓reduceIte]; rfl
    · simp only [hk, ↓reduceIte]; exact hag'.withGlob _
  | netMt r a =>
    simp only [UpdElem.erase, UpdElem.write, Solidity.UpdElem.write, Tm.eval_erase hag r,
      Tm.eval_erase hag a, Srt.wl]
    exact Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun _ _ =>
      Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun _ _ => hag'.withGlob _
  | setBalance a =>
    simp only [UpdElem.erase, UpdElem.write, Solidity.UpdElem.write, Tm.eval_erase hag a, Srt.wl]
    exact Res.Rel.bind_same _ fun _ _ => Res.Rel.bind_same _ fun _ _ => hag'.withGlob _

/-- **An update ends in agreeing states**: the untyped update of its
erasure, read in an agreeing state, halts alike or agrees on the names of
the context it leaves. -/
theorem Upd.apply_erase (hag : Agree ns σ₀ τ₀) : {Δ : Ctx} → (U : Upd C Γ Δ) → U.Fresh ns →
    Res.Rel (Agree (U.names ns)) (U.apply σ₀) (Solidity.Upd.apply (U.erase ns) τ₀)
  | _, .nil, _ => hag
  | _, .snoc U e, hU => by
    show Res.Rel _ (do e.write σ₀ (← U.apply σ₀))
      ((U.erase ns ++ [e.erase ns (U.names ns)]).foldlM (fun τ e => e.write τ₀ τ) τ₀)
    rw [List.foldlM_append]
    refine Res.Rel.bind (Upd.apply_erase hag U hU) fun σ' τ' h' => ?_
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
    exact UpdElem.write_erase hag h' e
  | _, .decl U x r, hU => by
    show Res.Rel _ (do let τ ← U.apply σ₀; pure (τ.push (← r.eval σ₀)))
      ((U.erase ns ++ [r.erase ns x]).foldlM (fun τ e => e.write τ₀ τ) τ₀)
    rw [List.foldlM_append]
    refine Res.Rel.bind (Upd.apply_erase hag U hU.1) fun σ' τ' h' => ?_
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure, Rhs.write_erase hag]
    cases r.eval σ₀ with
    | error => rfl
    | ok v => exact h'.push hU.2 v
  | _, .pop U h, hU => by
    show Res.Rel _ ((U.apply σ₀).map (State.drop h)) (Solidity.Upd.apply (U.erase ns) τ₀)
    exact (Upd.apply_erase hag U hU).map_left fun _ _ h' => h'.dropNames h
  | _, .drop U h, hU => by
    show Res.Rel _ ((U.apply σ₀).map (State.thin h)) (Solidity.Upd.apply (U.erase ns) τ₀)
    exact (Upd.apply_erase hag U hU).map_left fun _ _ h' => h'.thin h

end Updates

/-! ## A modality runs as its erasure -/

/-- Every block the frames hold binds fresh names. -/
def Frames.Fresh : {Γ Γ₀ : Ctx} → List Var → Frames C Γ Γ₀ → Prop
  | _, _, _, .nil => True
  | _, _, ns, .seq ω κ => ω.Fresh [] ns ∧ κ.Fresh (ω.outNames ns)
  | _, _, ns, .pop _ h κ => κ.Fresh (ns.drop h.depth)
  | _, _, ns, .drop h κ => κ.Fresh (h.names ns)

section Runs

theorem RunRel.toRel {Γ : Ctx} {ns B : List Var} {τ₀ : Semantics.State} :
    {x : Res (State C Γ)} → {y : Res Semantics.State} → RunRel ns B τ₀ x y → Res.Rel (Agree ns) x y
  | .error _, .error _, h => h
  | .ok _, .ok _, h => h.1

/-- A block runs as its erasure (`run_erase`, from any agreeing state). -/
theorem Prog.run_rel {Γ Γ' : Ctx} {ns : List Var} {σ : State C Γ} {τ : Semantics.State}
    (hag : Agree ns σ τ) (P : Prog C Γ Γ') (hP : P.Fresh [] ns) :
    Res.Rel (Agree (P.outNames ns)) (P.run σ) (Solidity.Prog.run τ (P.erase ns)) :=
  (Prog.erasesAt P hP hag).toRel

/-- The frames run as the statements they hold, a scope's end nothing. -/
theorem Frames.run_erase {Γ₀ : Ctx} : {Γ : Ctx} → (κ : Frames C Γ Γ₀) → {ns : List Var} →
    κ.Fresh ns → {σ : State C Γ} → {τ : Semantics.State} → Agree ns σ τ →
    Res.Rel (Agree (κ.outNames ns)) (Frames.run σ κ) (Solidity.Prog.run τ (κ.erase ns))
  | _, .nil, _, _, _, _, hag => hag
  | _, .seq ω κ, _, hκ, _, _, hag => by
    show Res.Rel _ (do Frames.run (← Prog.run _ ω) κ) (Solidity.Prog.run _ (ω.erase _ ++ κ.erase _))
    rw [Solidity.SemanticsProperties.Prog.run_append]
    exact Res.Rel.bind (Prog.run_rel hag ω hκ.1) fun _ _ h => Frames.run_erase κ hκ.2 h
  | _, .pop _ h κ, _, hκ, _, _, hag => Frames.run_erase κ hκ (hag.dropNames h)
  | _, .drop h κ, _, hκ, _, _, hag => Frames.run_erase κ hκ (hag.thin h)

end Runs

/-! ## The formulas -/

/-- A formula whose binders are all fresh, and with no hidden binder nor an
anonymising update: their untyped readings range over more states than the
typed ones (the untyped `anon` over any binding, the erased hidden binder
over whatever the name held). -/
def Fml.Plain : {Γ : Ctx} → List Var → Fml C Γ → Prop
  | _, _, .tt => True
  | _, _, .eq _ _ => True
  | _, _, .defined _ => True
  | _, ns, .not φ => φ.Plain ns
  | _, ns, .and φ ψ => φ.Plain ns ∧ ψ.Plain ns
  | _, ns, .imp φ ψ => φ.Plain ns ∧ ψ.Plain ns
  | _, ns, .upd _ U φ => U.Fresh ns ∧ φ.Plain (U.names ns)
  | _, ns, .modal _ P κ φ =>
    P.Fresh [] ns ∧ κ.Fresh (P.outNames ns) ∧ φ.Plain (κ.outNames (P.outNames ns))
  | _, ns, .havoc φ => φ.Plain ns
  | _, ns, .all x _ φ => x ∉ ns ∧ φ.Plain (x :: ns)
  | _, _, .bind .. => False
  | _, _, .anon .. => False

theorem _root_.Solidity.Modality.afterC_rel (m : Modality) {α : Type} {p : α → Prop} {q : Semantics.State → Prop}
    {R : α → Semantics.State → Prop} {x : Res α} {y : Res Semantics.State} (h : Res.Rel R x y)
    (hpq : ∀ a b, R a b → (p a ↔ q b)) : m.afterC p x ↔ m.after q y := by
  cases x with
  | ok a => cases y with
    | ok b => exact hpq a b h
    | error => exact h.elim
  | error e => cases y with
    | ok => exact h.elim
    | error e' => exact Iff.rfl

theorem _root_.Solidity.Modality.afterRunC_rel (m : Modality) {α : Type} {p : α → Prop} {q : Semantics.State → Prop}
    {R : α → Semantics.State → Prop} {x : Res α} {y : Res Semantics.State} (h : Res.Rel R x y)
    (hpq : ∀ a b, R a b → (p a ↔ q b)) : m.afterRunC p x ↔ m.afterRun q y := by
  cases x with
  | ok a => cases y with
    | ok b =>
      show m.afterC p (.ok a) ∧ _ ↔ m.after q (.ok b) ∧ _
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_true]
      exact hpq a b h
    | error => exact h.elim
  | error e => cases y with
    | ok => exact h.elim
    | error e' =>
      cases (h : e = e')
      simp only [Modality.afterRunC, Modality.afterRun, Modality.afterC, Modality.after, ne_eq,
        Except.error.injEq]

/-- **A scoped formula holds where its erasure does** (`Update.lean`'s
`holds`), in every untyped state that agrees with `σ` on the locals named
`ns`. -/
theorem holds_erase : {Γ : Ctx} → (φ : Fml C Γ) → {ns : List Var} → φ.Plain ns →
    {σ : State C Γ} → {τ : Semantics.State} → Agree ns σ τ →
    (holds σ φ ↔ Solidity.holds τ (φ.erase ns))
  | _, .tt, _, _, _, _, _ => Iff.rfl
  | _, .eq a b, _, _, _, _, hag => by
    show _ ↔ Theory.StValue.Equiv ((a.erase _).denote _) ((b.erase _).denote _)
    rw [Tm.denote_erase hag a, Tm.denote_erase hag b]; rfl
  | _, .defined t, _, _, _, _, hag => by
    show _ ↔ ∃ x, (t.erase _).eval _ = .ok x
    rw [Tm.eval_erase hag t]; rfl
  | _, .not φ, _, hφ, _, _, hag => not_congr (holds_erase φ hφ hag)
  | _, .and φ ψ, _, hφ, _, _, hag => and_congr (holds_erase φ hφ.1 hag) (holds_erase ψ hφ.2 hag)
  | _, .imp φ ψ, _, hφ, _, _, hag => imp_congr (holds_erase φ hφ.1 hag) (holds_erase ψ hφ.2 hag)
  | _, .upd m U φ, ns, hφ, σ, τ, hag => by
    have hU := Upd.apply_erase hag U hφ.1
    show m.afterC (holds · φ) (U.apply σ) ↔ Solidity.holds τ (Fml.erase ns (.upd m U φ))
    simp only [Fml.erase]
    split
    · rename_i hnil
      rw [hnil] at hU
      revert hU
      cases U.apply σ with
      | error => exact False.elim
      | ok σ' => exact fun h => holds_erase φ hφ.2 h
    · rename_i U' hne
      show _ ↔ m.after _ (Solidity.Upd.apply (U.erase ns) τ)
      exact m.afterC_rel hU fun _ _ h => holds_erase φ hφ.2 h
  | _, .modal m P κ φ, ns, hφ, σ, τ, hag => by
    show _ ↔ m.afterRun _ (Solidity.Prog.run τ (P.erase ns ++ κ.erase (P.outNames ns)))
    rw [Solidity.SemanticsProperties.Prog.run_append]
    exact m.afterRunC_rel (Res.Rel.bind (Prog.run_rel hag P hφ.1) fun _ _ h =>
      Frames.run_erase κ hφ.2.1 h) fun _ _ h => holds_erase φ hφ.2.2 h
  | _, .havoc φ, _, hφ, σ, τ, hag => by
    show (∀ st nt, holds (σ.withGlob (σ.glob.havoc st nt)) φ) ↔ ∀ st nt, Solidity.holds _ _
    refine forall_congr' fun st => forall_congr' fun nt => ?_
    have h := hag.withGlob (σ.glob.havoc st nt)
    have e : τ.havoc st nt = withLocals (σ.glob.havoc st nt) τ.env := by
      have hw := hag.wl
      generalize τ.env = env at hw ⊢
      subst hw; rfl
    rw [e]
    exact holds_erase φ hφ h
  | _, .all x p φ, _, hφ, σ, τ, hag => by
    show (∀ v, p.admits v → holds (σ.push v) φ) ↔ ∀ v, p.admits v → Solidity.holds _ _
    exact forall_congr' fun v => imp_congr_right fun _ => holds_erase φ hφ.2 (hag.push (t := .val p) hφ.1 v)
  | _, .bind .., _, hφ, _, _, _ => hφ.elim
  | _, .anon .., _, hφ, _, _, _ => hφ.elim

end Solidity.Core
