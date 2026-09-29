import Solidity.Calculus.Close
import Solidity.Calculus.UpdateRules

/-!
# The steps after the program, KeY's way

What symbolic execution leaves is closed as KeY closes it: the updates
merged, the terms rewritten inside the sequent, the goal closed.  The
rewriting itself is the calculus's: a Theory equation `Term.Theq`
(`Calculus/TermRules.lean`) applied by `Proves.theoryRw`, sound once for
every law, and the laws are the Theory's own read-backs
(`Calculus/TheoryLaws.lean`: `findOnSave`, `findOnDelAt`, the frames), not
taclets with a soundness proof each.  This module adds

* `Proves.mergeStorage`, `sequentialToParallel` over a storage write
  (`Proves.merge` takes only updates of locals): `s` substituted for
  `storage` in the second update (`withSt`), exact for terms whose every
  storage read is a `storage` term (`stExplicit`);
* `Proves.eqClose`, `v ≐ v` behind a context with no diamond, and
  `Proves.eqDClose`, the same for `v = v` (`Fml.eqD`);
* `rw [h]` on a sequent, `h` a Theory equation (`Term.Theq`): every
  equation of the sequent rewritten (`Proves.theoryRw`);
* the steps after it, under the box: `a = b` split into `defined(a)`,
  `defined(b)` and `a ≐ b` (`Proves.eqDSplit`, `Proves.andSplit`), a storage
  write applied to the goal and dropped (`Proves.applyStorageBox`; an update
  of locals, or the merged locals-and-storage update of `mergeStorage` under a
  goal that reads no storage, is `Proves.applyOnRigidBox`,
  `Calculus/UpdateRules.lean`; both are `sol_apply_upd`), and `t ≐ t` closed (`Proves.eqRefl`).

KeY applies the updates to the formula and drops them (`applyOnRigid`).
Here a dropped update that could halt takes with it the fact that it did
not, which is no loss under the box — a halting box update proves what
follows — for the Theory equation, total, whose terms need not return.  What
does need the run, a `defined` conjunct, is proved first, from the update
that wrote the local (`Proves.definedWritten`).

These rules are derived through `close`, as `Proves.merge` is, so they apply
to a sequent with no modality left.
-/

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-! ## Closing -/

/-- **`eqClose`**: `v ≐ v`, behind a context with no diamond. -/
theorem Proves.eqClose {R : RuleSet} {Γ : List (Hyp C)} {v : Value}
    (hb : Hyp.boxOnly Γ = true := by rfl)
    (hφ : (Hyp.wrap Γ (.eq (.lit v) (.lit v))).modalFree = true := by first | rfl | decide) :
    Proves R Γ (.eq (.lit v) (.lit v)) :=
  .close (fun σ => Hyp.wrap_of_reaches Γ hb σ (fun _ _ => Theory.StValue.Equiv.refl _)) hφ

/-- **`eqDClose`**: `v = v` as a program comparison writes it (`Fml.eqD`),
behind a context with no diamond: a literal is defined everywhere. -/
theorem Proves.eqDClose {R : RuleSet} {Γ : List (Hyp C)} {v : Value}
    (hb : Hyp.boxOnly Γ = true := by rfl)
    (hφ : (Hyp.wrap Γ (Fml.eqD (.lit v) (.lit v))).modalFree = true := by first | rfl | decide) :
    Proves R Γ (Fml.eqD (.lit v) (.lit v)) :=
  .close (fun σ => Hyp.wrap_of_reaches Γ hb σ (fun _ _ => holds_eqD_iff.2 ⟨v, rfl, rfl⟩)) hφ

/-! ## Updates in parallel: `sequentialToParallel` over a storage write

`Proves.merge` joins `{U}{V}` only when `U` writes locals.  A storage write
`{storage := s}` joins too, KeY's `{storage := s ‖ {storage := s}V}`: `V`'s
right-hand sides read `storage` after the write, so `s` is substituted for
`storage` in them (`withSt`), and they are read before it.  The substitution
is exact only where every storage read is a `storage` term: a path through
an index (`a[i]`) or one past the end (`a[a.length]`) checks the array in
the state it is read in, which is not a term (`stExplicit`).

A storage term changes the storage and nothing else (`State.Keeps`), which
is what lets the substituted term read the post-state's locals, heap and
funds off the pre-state. -/

/-- `τ` is `σ` with another storage. -/
def Semantics.State.Keeps (σ τ : State) : Prop := { σ with storage := τ.storage } = τ

theorem Semantics.State.Keeps.refl (σ : State) : σ.Keeps σ := rfl

theorem Semantics.State.Keeps.trans {σ ρ τ : State} (h₁ : σ.Keeps ρ) (h₂ : ρ.Keeps τ) : σ.Keeps τ := by
  unfold Semantics.State.Keeps at *
  rw [← h₂, ← h₁]

theorem Semantics.State.saveStorage_keeps {σ τ : State} {r : Name} {segs : List Seg} {v : SVal}
    (h : σ.saveStorage r segs v = .ok τ) : σ.Keeps τ :=
  Close.saveStorage_restore h

theorem Semantics.State.writeStorage_keeps {σ τ : State} {r : Name} {segs : List Seg} {v : SVal}
    (h : σ.writeStorage r segs v = .ok τ) : σ.Keeps τ := by
  unfold State.writeStorage at h
  cases v with
  | prim _ => exact State.saveStorage_keeps h
  | struct _ | array _ _ _ | map _ _ =>
    cases hf : σ.findStorage r segs with
    | error _ => rw [hf] at h; cases h
    | ok _ => rw [hf] at h; exact State.saveStorage_keeps h

theorem pushAt_keeps {σ τ : State} {E : Ty} {r : Name} {segs : List Seg} {val : SVal → Res SVal}
    (h : pushAt σ E r segs val = .ok τ) : σ.Keeps τ := by
  unfold pushAt at h
  cases hf : σ.findStorage r segs with
  | error _ => rw [hf] at h; cases h
  | ok cur =>
    rw [hf] at h
    cases cur with
    | array elems shadow fx =>
      cases hv : val (pushSlot E shadow).1 with
      | error _ => simp only [hv, bind, Except.bind] at h; cases h
      | ok _ => simp only [hv, bind, Except.bind] at h; exact State.saveStorage_keeps h
    | prim _ | struct _ | map _ _ => cases h

theorem popAt_keeps {σ τ : State} {keep : Bool} {r : Name} {segs : List Seg}
    (h : popAt σ keep r segs = .ok τ) : σ.Keeps τ := by
  unfold popAt at h
  cases hf : σ.findStorage r segs with
  | error _ => rw [hf] at h; cases h
  | ok cur =>
    rw [hf] at h
    cases cur with
    | array elems shadow fx =>
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · exact State.saveStorage_keeps h
    | prim _ | struct _ | map _ _ => cases h

theorem pushPlaceAt_keeps {σ τ : State} {E : Ty} {r : Name} {segs : List Seg} {k : Int}
    (h : pushPlaceAt σ E r segs = .ok (τ, k)) : σ.Keeps τ := by
  unfold pushPlaceAt at h
  cases hf : σ.findStorage r segs with
  | error _ => rw [hf] at h; cases h
  | ok cur =>
    rw [hf] at h
    cases cur with
    | array elems shadow fx =>
      cases hs : σ.saveStorage r segs (.array (elems ++ [(pushSlot E shadow).1]) (pushSlot E shadow).2 fx) with
      | error _ => simp only [hs, bind, Except.bind] at h; cases h
      | ok σ' =>
        simp only [hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact State.saveStorage_keeps hs
    | prim _ | struct _ | map _ _ => cases h

/-- A storage term changes the storage only. -/
theorem STerm.eval_keeps {σ τ : State} : (s : STerm C) → s.eval σ = .ok τ → σ.Keeps τ
  | .storage, h => by cases h; exact State.Keeps.refl σ
  | .pv x, h => by
    simp only [STerm.eval] at h
    obtain ⟨b, -, h⟩ := bind_ok_inv h
    cases b with
    | store st => cases h; rfl
    | val _ | spath _ _ | mref _ | ledger _ => cases h
  | .save s p v, h => by
    simp only [STerm.eval] at h
    obtain ⟨_, -, h⟩ := bind_ok_inv h
    obtain ⟨τ₀, h₀, h⟩ := bind_ok_inv h
    obtain ⟨⟨_, _⟩, -, h⟩ := bind_ok_inv h
    exact (s.eval_keeps h₀).trans (State.writeStorage_keeps h)
  | .delAt s p, h => by
    simp only [STerm.eval] at h
    obtain ⟨τ₀, h₀, h⟩ := bind_ok_inv h
    obtain ⟨⟨_, _⟩, -, h⟩ := bind_ok_inv h
    obtain ⟨_, -, h⟩ := bind_ok_inv h
    exact (s.eval_keeps h₀).trans (State.saveStorage_keeps h)
  | .push s p v, h => by
    simp only [STerm.eval] at h
    obtain ⟨τ₀, h₀, h⟩ := bind_ok_inv h
    obtain ⟨⟨_, _⟩, -, h⟩ := bind_ok_inv h
    exact (s.eval_keeps h₀).trans (pushAt_keeps h)
  | .pushSlot s p E, h => by
    simp only [STerm.eval] at h
    obtain ⟨τ₀, h₀, h⟩ := bind_ok_inv h
    obtain ⟨⟨_, _⟩, -, h⟩ := bind_ok_inv h
    exact (s.eval_keeps h₀).trans (pushAt_keeps h)
  | .pop s p, h => by
    simp only [STerm.eval] at h
    obtain ⟨τ₀, h₀, h⟩ := bind_ok_inv h
    obtain ⟨⟨_, _⟩, -, h⟩ := bind_ok_inv h
    exact (s.eval_keeps h₀).trans (popAt_keeps h)
  | .shrink s p, h => by
    simp only [STerm.eval] at h
    obtain ⟨τ₀, h₀, h⟩ := bind_ok_inv h
    obtain ⟨⟨_, _⟩, -, h⟩ := bind_ok_inv h
    exact (s.eval_keeps h₀).trans (popAt_keeps h)
  | .extend s p E, h => by
    simp only [STerm.eval] at h
    obtain ⟨τ₀, h₀, h⟩ := bind_ok_inv h
    obtain ⟨⟨_, _⟩, -, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ', _⟩, hp, h⟩ := bind_ok_inv h
    cases h
    exact (s.eval_keeps h₀).trans (pushPlaceAt_keeps hp)

/-! ### Substituting a storage term for `storage` -/

/-- The storage term a write installs, substituted for `storage` by `withSt`.
(A structure rather than an `STerm` argument, so that the substitution is
structural recursion on the term alone.) -/
structure StWrite (C : Contract) where
  s : STerm C

mutual

/-- `{storage := s}e`: `s` for every `storage` in `e`. -/
def Term.withSt (w : StWrite C) : Term C → Term C
  | .binop op p a b => .binop op p (a.withSt w) (b.withSt w)
  | .unop op p a => .unop op p (a.withSt w)
  | .find s' p => .find (s'.withSt w) (p.withSt w)
  | .len s' p => .len (s'.withSt w) (p.withSt w)
  | .ite c a b => .ite (c.withSt w) (a.withSt w) (b.withSt w)
  | .lit v => .lit v
  | .pv x => .pv x
  | .env k => .env k
  | .read m a => .read m a
  | .mlen m i => .mlen m i
  | .net a => .net (a.withSt w)
  | .netOf x a => .netOf x (a.withSt w)

def PTerm.withSt (w : StWrite C) : PTerm C → PTerm C
  | .root r => .root r
  | .pv x => .pv x
  | .field p f => .field (p.withSt w) f
  | .at p i => .at (p.withSt w) (i.withSt w)
  | .next p => .next (p.withSt w)

def STerm.withSt (w : StWrite C) : STerm C → STerm C
  | .storage => w.s
  | .pv x => .pv x
  | .save s' p v => .save (s'.withSt w) (p.withSt w) (v.withSt w)
  | .delAt s' p => .delAt (s'.withSt w) (p.withSt w)
  | .push s' p v => .push (s'.withSt w) (p.withSt w) (v.withSt w)
  | .pushSlot s' p E => .pushSlot (s'.withSt w) (p.withSt w) E
  | .pop s' p => .pop (s'.withSt w) (p.withSt w)
  | .shrink s' p => .shrink (s'.withSt w) (p.withSt w)
  | .extend s' p E => .extend (s'.withSt w) (p.withSt w) E

def SValT.withSt (w : StWrite C) : SValT C → SValT C
  | .val t => .val (t.withSt w)
  | .find s' p => .find (s'.withSt w) (p.withSt w)
  | .copyMem m i => .copyMem m i
  | .newArr R n => .newArr R (n.withSt w)

end

mutual

/-- Every storage read of the term is a `storage` term: no index check, no
push slot, no memory. -/
def Term.stExplicit : Term C → Bool
  | .lit _ | .pv _ | .env _ => true
  | .binop _ _ a b => a.stExplicit && b.stExplicit
  | .unop _ _ a | .net a | .netOf _ a => a.stExplicit
  | .find s p | .len s p => s.stExplicit && p.stExplicit
  | .ite c a b => c.stExplicit && a.stExplicit && b.stExplicit
  | .read .. | .mlen .. => false

def PTerm.stExplicit : PTerm C → Bool
  | .root _ | .pv _ => true
  | .field p _ => p.stExplicit
  | .at .. | .next _ => false

def STerm.stExplicit : STerm C → Bool
  | .storage | .pv _ => true
  | .save s p v | .push s p v => s.stExplicit && p.stExplicit && v.stExplicit
  | .delAt s p | .pop s p | .shrink s p | .pushSlot s p _ | .extend s p _ =>
    s.stExplicit && p.stExplicit

def SValT.stExplicit : SValT C → Bool
  | .val t | .newArr _ t => t.stExplicit
  | .find s p => s.stExplicit && p.stExplicit
  | .copyMem .. => false

end

section WithSt

variable {w : StWrite C} {σ τ : State}

mutual

/-- Read before `{storage := s}`, the substituted term reads what the term
reads after it. -/
theorem Term.withSt_eval (hs : w.s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (e : Term C) → e.stExplicit = true → (e.withSt w).eval σ = e.eval τ
  | .lit _, _ => rfl
  | .pv _, _ | .env _, _ => by rw [← hk]; rfl
  | .binop _ _ a b, he => by
    simp only [Term.stExplicit, Bool.and_eq_true] at he
    simp only [Term.withSt, Term.eval, Term.withSt_eval hs hk a he.1, Term.withSt_eval hs hk b he.2]
  | .unop _ _ a, he => by
    simp only [Term.stExplicit] at he
    simp only [Term.withSt, Term.eval, Term.withSt_eval hs hk a he]
  | .find s' p, he | .len s' p, he => by
    simp only [Term.stExplicit, Bool.and_eq_true] at he
    simp only [Term.withSt, Term.eval, STerm.withSt_eval hs hk s' he.1, PTerm.withSt_eval hs hk p he.2]
  | .ite c a b, he => by
    simp only [Term.stExplicit, Bool.and_eq_true] at he
    simp only [Term.withSt, Term.eval, Term.withSt_eval hs hk c he.1.1, Term.withSt_eval hs hk a he.1.2,
      Term.withSt_eval hs hk b he.2]
  | .read .., he | .mlen .., he => by simp only [Term.stExplicit, Bool.false_eq_true] at he
  | .net a, he | .netOf _ a, he => by
    simp only [Term.stExplicit] at he
    simp only [Term.withSt, Term.eval, Term.withSt_eval hs hk a he]
    rw [← hk]; rfl

theorem PTerm.withSt_eval (hs : w.s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (p : PTerm C) → p.stExplicit = true → (p.withSt w).eval σ = p.eval τ
  | .root _, _ => rfl
  | .pv _, _ => by rw [← hk]; rfl
  | .field p _, he => by
    simp only [PTerm.stExplicit] at he
    simp only [PTerm.withSt, PTerm.eval, PTerm.withSt_eval hs hk p he]
  | .at .., he | .next _, he => by simp only [PTerm.stExplicit, Bool.false_eq_true] at he

theorem STerm.withSt_eval (hs : w.s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (s' : STerm C) → s'.stExplicit = true → (s'.withSt w).eval σ = s'.eval τ
  | .storage, _ => hs
  | .pv _, _ => by rw [← hk]; rfl
  | .save s' p v, he | .push s' p v, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.eval, STerm.withSt_eval hs hk s' he.1.1, PTerm.withSt_eval hs hk p he.1.2,
      SValT.withSt_eval hs hk v he.2]
  | .delAt s' p, he | .pop s' p, he | .shrink s' p, he | .pushSlot s' p _, he
  | .extend s' p _, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.eval, STerm.withSt_eval hs hk s' he.1, PTerm.withSt_eval hs hk p he.2]

theorem SValT.withSt_eval (hs : w.s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (v : SValT C) → v.stExplicit = true → (v.withSt w).eval σ = v.eval τ
  | .val t, he | .newArr _ t, he => by
    simp only [SValT.stExplicit] at he
    simp only [SValT.withSt, SValT.eval, Term.withSt_eval hs hk t he]
  | .find s' p, he => by
    simp only [SValT.stExplicit, Bool.and_eq_true] at he
    simp only [SValT.withSt, SValT.eval, STerm.withSt_eval hs hk s' he.1, PTerm.withSt_eval hs hk p he.2]
  | .copyMem .., he => by simp only [SValT.stExplicit, Bool.false_eq_true] at he

end

end WithSt

/-! ### The merge -/

def UpdElem.withSt (s : STerm C) : UpdElem C → UpdElem C
  | .val x t => .val x (t.withSt ⟨s⟩)
  | .path x p => .path x (p.withSt ⟨s⟩)
  | .storage s' => .storage (s'.withSt ⟨s⟩)
  | .store x s' => .store x (s'.withSt ⟨s⟩)
  | .transfer r a => .transfer (r.withSt ⟨s⟩) (a.withSt ⟨s⟩)
  | .mref x i => .mref x i
  | .memory m => .memory m
  | .saveNet x => .saveNet x
  | .book a => .book (a.withSt ⟨s⟩)

def UpdElem.stExplicit : UpdElem C → Bool
  | .val _ t => t.stExplicit
  | .path _ p => p.stExplicit
  | .storage s | .store _ s => s.stExplicit
  | .transfer r a => r.stExplicit && a.stExplicit
  | .saveNet _ => true
  | .book a => a.stExplicit
  | .mref .. | .memory _ => false

/-- `{storage := s}V`: `s` substituted for `storage` in `V`'s right-hand sides. -/
def Upd.withSt (s : STerm C) (V : Upd C) : Upd C := V.map (·.withSt s)

theorem UpdElem.withSt_write {s : STerm C} {σ τ : State} (hs : s.eval σ = .ok τ)
    (hk : σ.Keeps τ) (ρ : State) :
    (e : UpdElem C) → e.stExplicit = true → (e.withSt s).write σ ρ = e.write τ ρ
  | .val _ t, he => by
    simp only [UpdElem.withSt, UpdElem.write, Term.withSt_eval (w := ⟨s⟩) hs hk t he]
  | .path _ p, he => by
    simp only [UpdElem.withSt, UpdElem.write, PTerm.withSt_eval (w := ⟨s⟩) hs hk p he]
  | .storage s', he | .store _ s', he => by
    simp only [UpdElem.withSt, UpdElem.write, STerm.withSt_eval (w := ⟨s⟩) hs hk s' he]
  | .transfer r a, he => by
    simp only [UpdElem.stExplicit, Bool.and_eq_true] at he
    simp only [UpdElem.withSt, UpdElem.write, Term.withSt_eval (w := ⟨s⟩) hs hk r he.1,
      Term.withSt_eval (w := ⟨s⟩) hs hk a he.2]
  | .saveNet _, _ => by simp only [UpdElem.withSt, UpdElem.write]; rw [← hk]
  | .book a, he => by
    simp only [UpdElem.stExplicit] at he
    simp only [UpdElem.withSt, UpdElem.write, Term.withSt_eval (w := ⟨s⟩) hs hk a he]
    rw [← hk]; rfl
  | .mref .., he | .memory _, he => by simp only [UpdElem.stExplicit, Bool.false_eq_true] at he

theorem Upd.withSt_foldl {s : STerm C} {σ τ : State} (hs : s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (V : Upd C) → V.all (·.stExplicit) = true → ∀ ρ,
      (V.withSt s).foldlM (fun ρ e => e.write σ ρ) ρ = V.foldlM (fun ρ e => e.write τ ρ) ρ
  | [], _, _ => rfl
  | e :: V, hV, ρ => by
    simp only [List.all_cons, Bool.and_eq_true] at hV
    simp only [Upd.withSt, List.map_cons, List.foldlM_cons, UpdElem.withSt_write hs hk ρ e hV.1]
    congr 1
    funext ρ'
    exact Upd.withSt_foldl hs hk V hV.2 ρ'

/-- **`sequentialToParallel`** over a storage write:
`{storage := s}{V} ψ ⟺ {storage := s ‖ {storage := s}V} ψ`. -/
theorem Upd.mergeStorage_holds (m : Modality) (s : STerm C) (V : Upd C)
    (hV : V.all (·.stExplicit) = true) (ψ : Fml C) (σ : State) :
    holds σ (.upd m (.storage s :: V.withSt s) ψ) ↔ holds σ (.upd m [.storage s] (.upd m V ψ)) := by
  simp only [holds, Upd.apply, List.foldlM_cons, List.foldlM_nil, Close.UpdElem.write_storage]
  cases hs : s.eval σ with
  | error _ => exact Iff.rfl
  | ok τ =>
    have hk : σ.Keeps τ := STerm.eval_keeps s hs
    simp only [Res.ok_bind]
    rw [hk, Upd.withSt_foldl hs hk V hV τ]
    exact Iff.rfl

/-- `sequentialToParallel` in a derivation, for a storage write followed by
an update whose storage reads are all `storage` terms. -/
theorem Proves.mergeStorage {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {s : STerm C}
    {V : Upd C} {φ : Fml C} (h : Proves R (Γ ++ [.upd m (.storage s :: V.withSt s)]) φ)
    (hV : V.all (·.stExplicit) = true := by rfl)
    (hφ : (Hyp.wrap (Γ ++ [.upd m [.storage s]] ++ [.upd m V]) φ).modalFree = true := by
      first | rfl | decide) :
    Proves R (Γ ++ [.upd m [.storage s]] ++ [.upd m V]) φ :=
  .close (fun σ => by
    have := h.sound σ
    simp only [List.append_assoc, List.cons_append, List.nil_append, Hyp.wrap_append,
      Hyp.wrap] at this ⊢
    exact Hyp.wrap_mono (fun τ hτ => (Upd.mergeStorage_holds m s V hV φ τ).1 hτ) Γ σ this) hφ

/-! ## `rw` on a sequent

`rw [h]`, with `h : Term.Theq t t'` rather than an `=`, is `Proves.theoryRw
h`: `t` becomes `t'` in every equation of the sequent at once, so there is no
position to find.  It fails when the sequent does not change.  `rw [← h]` is
`Term.Theq.symm h`, and `rw [h₁, h₂]` is one rewrite after the other.  Scoped
to `Proves`, where the derivations are written; elsewhere, and for an `=`,
`rw` is Lean's. -/

open Lean Elab Tactic Meta in
/-- Close a side condition of a law, `h : p.hasSeg = true` and the like, by
`rfl` and then `decide`: once the law's terms are known the condition is a
closed `Bool` computation.  A failure is `sol_rw`'s, naming the condition,
rather than the error of whichever tactic was tried last. -/
def solRwSide (h : Lean.Term) (g : MVarId) : TacticM Unit := do
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let g ← g.replaceTargetDefEq ty
  let closed ← try
      let gs ← Term.withoutErrToSorry <|
        Tactic.run g (evalTactic (← `(tactic| first | rfl | decide)))
      pure gs.isEmpty
    catch _ => pure false
  unless closed do
    throwError "sol_rw: the side condition{indentExpr ty}\nof {h} closes by neither \
      `rfl` nor `decide`"

open Lean Elab Tactic Meta in
/-- Rewrite the main goal, a sequent, with the Theory equation `h` (right to
left if `symm`).  An argument of `h` left open is found as Lean's `rw` finds
it: at the first instance of the left-hand side in the sequent (`kabstract`).
So a bare law's name is elaborated as `@h`, every argument open, and its
side conditions (`hp : p.hasSeg = true`, whose default `by rfl` could not
run before `p` is known) are closed after the match, by `solRwSide`; a
condition left pending by an application `h a` is run then too.
The rewritten sequent is then computed (`Term.rw` unfolded, each `if` decided
where the terms settle it), so the next step sees terms, not a pending
rewrite; an `if` left shows an occurrence that the rewrite could not settle,
such as `find(save(storage, p, w), p)` against `find(save(storage, p, v), p)`
with `w` and `v` unknown. -/
def solRw (h : Lean.Term) (symm : Bool) : TacticM Unit := withMainContext do
  let before ← instantiateMVars (← getMainTarget)
  unless (← whnfR before).isAppOf ``Proves do
    throwError "sol_rw: the goal is not a sequent `Γ ⟹ φ`"
  let pf ← match h with
    | `($id:ident) => elabTerm (← `(@$id)) none (mayPostpone := true)
    | _ => elabTerm h none (mayPostpone := true)
  let (args, _, ty) ← forallMetaTelescope (← instantiateMVars (← inferType pf))
  let pf ← if symm then mkAppM ``Term.Theq.symm #[mkAppN pf args] else pure (mkAppN pf args)
  let ty ← if symm then inferType pf else pure ty
  let_expr Term.Theq _ lhs _ ← (← whnfR (← instantiateMVars ty))
    | throwError "sol_rw: {h} is not a Theory equation `Term.Theq t t'`"
  let lhs ← instantiateMVars lhs
  if lhs.hasMVar then
    let abst ← kabstract before lhs
    unless abst.hasLooseBVars do
      throwError "sol_rw: {lhs} does not occur in the sequent"
  for a in args do
    let g := a.mvarId!
    if !(← g.isAssigned) && (← isProp (← g.getType)) then solRwSide h g
  try Term.synthesizeSyntheticMVarsNoPostponing
  catch e => throwError "sol_rw: a side condition of {h} failed:{indentD e.toMessageData}"
  let pf ← instantiateMVars pf
  if pf.hasExprMVar then
    throwError "sol_rw: could not instantiate {pf}"
  -- without recovery, an elaboration error is thrown rather than logged
  withoutRecover <| evalTactic (← `(tactic| refine Proves.theoryRw $(← Term.exprToSyntax pf) ?_))
  evalTactic (← `(tactic| simp (config := { decide := true }) only
    [Hyp.rwEq, Fml.rwEq, Term.rw, PTerm.rw, STerm.rw, SValT.rw, Term.pick, ↓reduceIte,
      reduceCtorEq, and_true, true_and, and_false, false_and, and_self,
      Term.lit.injEq, Term.pv.injEq, Term.binop.injEq, Term.unop.injEq, Term.find.injEq,
      Term.len.injEq, Term.read.injEq, Term.ite.injEq, Term.mlen.injEq, Term.env.injEq,
      Term.net.injEq, Term.netOf.injEq, PTerm.root.injEq, PTerm.pv.injEq, PTerm.field.injEq,
      PTerm.at.injEq, PTerm.next.injEq, STerm.pv.injEq, STerm.save.injEq, STerm.delAt.injEq,
      STerm.push.injEq, STerm.pushSlot.injEq, STerm.pop.injEq, STerm.shrink.injEq,
      STerm.extend.injEq, SValT.val.injEq, SValT.find.injEq, SValT.copyMem.injEq,
      SValT.newArr.injEq]))
  let after ← instantiateMVars (← getMainTarget)
  if after == before then
    throwError "sol_rw: {h} rewrites nothing in the sequent"

/-- `sol_rw h`: rewrite every equation of a sequent with the Theory equation
`h : Term.Theq t t'`. -/
elab "sol_rw " h:term : tactic => solRw h false

/-- `sol_rw ← h`: `sol_rw h`, right to left. -/
elab "sol_rw " "← " h:term : tactic => solRw h true

namespace Proves

open Lean Elab Tactic Meta in
/-- `rw [h₁, …]` on a sequent is `sol_rw h₁; …`.  An elaborator, not a
macro: Lean tries a tactic's macros first and its elaborators after, and
reports the error of the last one tried, so as an elaborator this rule runs
after Lean's `rw` (which keeps an `=` rewrite on a sequent Lean's) and its
error is the one shown.  On a goal that is not a sequent it steps aside
(`throwUnsupportedSyntax`), leaving Lean's error. -/
scoped elab_rules : tactic
  | `(tactic| rw [$rs,*]) => do
    let isSeq ← try
        withMainContext do pure ((← whnfR (← instantiateMVars (← getMainTarget))).isAppOf ``Proves)
      catch _ => pure false
    unless isSeq do throwUnsupportedSyntax
    for r in rs.getElems do
      withRef r <| solRw ⟨r.raw[1]⟩ !r.raw[0].isNone

end Proves

/-! ## Under the box: splitting, closing, applying a storage write

The steps that finish a goal once the program is gone, in KeY's order: a
program comparison `a = b` (`Fml.eqD`) splits into its two `defined`
conjuncts and its Theory equation (`Proves.eqDSplit`, `Proves.andSplit`);
a local's `defined` is proved from the update that wrote it
(`Proves.definedWritten`, `Calculus/UpdateRules.lean`) and a literal's from
nothing (`Proves.definedLit`); the updates are applied to the equation and
dropped (`Proves.applyOnRigidBox` for locals, or locals and a storage write
under a storage-free goal; `Proves.applyStorageBox` for a storage write), the Theory rewrites it (`rw [h]`), and `t ≐ t` closes
(`Proves.eqRefl`).  Each is derived through `close`, so it applies to a
sequent with no modality left; each needs only that the context has no
diamond (`Hyp.boxOnly`), since behind a halting box update everything
holds. -/

/-- **`andRight`**: a conjunction from each conjunct, in the same context. -/
theorem Proves.andSplit {R : RuleSet} {Γ : List (Hyp C)} {φ ψ : Fml C}
    (h₁ : Proves R Γ φ) (h₂ : Proves R Γ ψ)
    (hφ : (Hyp.wrap Γ (.and φ ψ)).modalFree = true := by first | rfl | decide) :
    Proves R Γ (.and φ ψ) :=
  .close (fun σ => Hyp.wrap_mono₃ (ψ₁ := φ) (ψ₂ := ψ) (ψ₃ := φ) (φ := .and φ ψ)
    (fun _ a b _ => ⟨a, b⟩) Γ σ (h₁.sound σ) (h₂.sound σ)
    (h₁.sound σ)) hφ

/-- A program comparison `a = b` (`Fml.eqD`) from its three parts: `a` and
`b` return, and they are equal in the Theory.

Example: `x = 42` from `defined(x)`, `defined(42)` and `x ≐ 42`. -/
theorem Proves.eqDSplit {R : RuleSet} {Γ : List (Hyp C)} {a b : Term C}
    (ha : Proves R Γ (.defined a)) (hb : Proves R Γ (.defined b)) (he : Proves R Γ (.eq a b))
    (hφ : (Hyp.wrap Γ (Fml.eqD a b)).modalFree = true := by first | rfl | decide) :
    Proves R Γ (Fml.eqD a b) :=
  .close (fun σ => Hyp.wrap_mono₃ (ψ₁ := .defined a) (ψ₂ := .defined b) (ψ₃ := .eq a b)
    (φ := Fml.eqD a b) (fun _ x y z => ⟨x, y, z⟩) Γ σ (ha.sound σ) (hb.sound σ)
    (he.sound σ)) hφ

/-- **`eqClose`** for any term: `t ≐ t`, behind a context with no diamond.
The Theory equation is total, so a term that halts is equal to itself too
(`StValue.Equiv.refl`). -/
theorem Proves.eqRefl {R : RuleSet} {Γ : List (Hyp C)} {t : Term C}
    (hb : Hyp.boxOnly Γ = true := by first | rfl | decide)
    (hφ : (Hyp.wrap Γ (.eq t t)).modalFree = true := by first | rfl | decide) :
    Proves R Γ (.eq t t) :=
  .close (fun σ => Hyp.wrap_of_reaches Γ hb σ (fun _ _ => Theory.StValue.Equiv.refl _)) hφ

/-- A literal is defined, behind a context with no diamond. -/
theorem Proves.definedLit {R : RuleSet} {Γ : List (Hyp C)} {v : Value}
    (hb : Hyp.boxOnly Γ = true := by first | rfl | decide)
    (hφ : (Hyp.wrap Γ (.defined (.lit v))).modalFree = true := by first | rfl | decide) :
    Proves R Γ (.defined (.lit v)) :=
  .close (fun σ => Hyp.wrap_of_reaches Γ hb σ (fun _ _ => ⟨v, rfl⟩)) hφ

/-! ### A storage write applied to a first-order formula

`{storage := s} φ ⇝ φ[s/storage]` (KeY's `applyOnRigidFormula` with
`applyOnPV` at `storage`): `withSt`, as `mergeStorage` substitutes into an
update, now into a formula.  An equation reads its terms through `denote`,
so the substitution is exact up to `Equiv` where every storage read is a
`storage` term (`stExplicit`): the storage `s` denotes is the storage its run
leaves (`STerm.denote_eval`), and every other part of the state is the same
on both sides (`State.Keeps`).  As for `Proves.applyOnRigidBox`, only the
direction the box needs holds without knowing that `s` runs. -/

section WithStDenote

open Theory Theory.StValue

variable {w : StWrite C} {σ τ : State}

/-- A storage term leaves the environment as it was. -/
theorem Semantics.State.Keeps.getEnv (hk : σ.Keeps τ) (x : Var) : τ.getEnv x = σ.getEnv x := by
  rw [← hk]; rfl

mutual

/-- Read before `{storage := s}`, the substituted term denotes, up to
`Equiv`, what the term denotes after it. -/
theorem Term.withSt_denote (hs : w.s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (e : Term C) → e.stExplicit = true → Equiv ((e.withSt w).denote σ) (e.denote τ)
  | .lit _, _ => Equiv.refl _
  | .pv x, _ => by
    simp only [Term.withSt, Term.denote, hk.getEnv x]
    exact Equiv.refl _
  | .env k, _ => by
    rw [← hk]
    exact Equiv.refl _
  | .binop op p a b, he => by
    simp only [Term.stExplicit, Bool.and_eq_true] at he
    simp only [Term.withSt, Term.denote, (Term.withSt_denote hs hk a he.1).toRes,
      (Term.withSt_denote hs hk b he.2).toRes]
    exact Equiv.refl _
  | .unop op p a, he => by
    simp only [Term.stExplicit] at he
    simp only [Term.withSt, Term.denote, (Term.withSt_denote hs hk a he).toRes]
    exact Equiv.refl _
  | .find s' p, he => by
    simp only [Term.stExplicit, Bool.and_eq_true] at he
    simp only [Term.withSt, Term.denote, PTerm.withSt_denote hs hk p he.2]
    exact Equiv.findSt (STerm.withSt_denote hs hk s' he.1) _
  | .len s' p, he => by
    simp only [Term.stExplicit, Bool.and_eq_true] at he
    simp only [Term.withSt, Term.denote, PTerm.withSt_denote hs hk p he.2]
    exact Equiv.findSt (STerm.withSt_denote hs hk s' he.1) _
  | .ite c a b, he => by
    simp only [Term.stExplicit, Bool.and_eq_true] at he
    have ea : Equiv ((a.withSt w).denote σ) (a.denote τ) := Term.withSt_denote hs hk a he.1.2
    have eb : Equiv ((b.withSt w).denote σ) (b.denote τ) := Term.withSt_denote hs hk b he.2
    simp only [Term.withSt, Term.denote]
    rcases (Term.withSt_denote hs hk c he.1.1).eq_or_st with hc | ⟨s, t, hc, hc'⟩
    · rw [hc]
      split
      · exact ea
      · exact eb
      · exact Equiv.refl _
    · rw [hc, hc']
      exact Equiv.refl _
  | .read .., he | .mlen .., he => by simp only [Term.stExplicit, Bool.false_eq_true] at he
  | .net a, he => by
    simp only [Term.stExplicit] at he
    have hn : τ.net = σ.net := by rw [← hk]
    simp only [Term.withSt, Term.denote, State.getNet, hn]
    rcases (Term.withSt_denote hs hk a he).eq_or_st with ha | ⟨s, t, ha, ha'⟩
    · rw [ha]
      exact Equiv.refl _
    · rw [ha, ha']
      exact Equiv.refl _
  | .netOf x a, he => by
    simp only [Term.stExplicit] at he
    simp only [Term.withSt, Term.denote, hk.getEnv x]
    rcases (Term.withSt_denote hs hk a he).eq_or_st with ha | ⟨s, t, ha, ha'⟩
    · rw [ha]
      exact Equiv.refl _
    · rw [ha, ha']
      rcases σ.getEnv x with _ | b
      · exact Equiv.refl _
      · cases b <;> exact Equiv.refl _

/-- Read before `{storage := s}`, the substituted path denotes the path the
path denotes after it. -/
theorem PTerm.withSt_denote (hs : w.s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (p : PTerm C) → p.stExplicit = true → (p.withSt w).denote σ = p.denote τ
  | .root _, _ => rfl
  | .pv x, _ => by
    simp only [PTerm.withSt, PTerm.denote, aliasPath, hk.getEnv x]
  | .field p _, he => by
    simp only [PTerm.stExplicit] at he
    simp only [PTerm.withSt, PTerm.denote, PTerm.withSt_denote hs hk p he]
  | .at .., he | .next _, he => by simp only [PTerm.stExplicit, Bool.false_eq_true] at he

/-- Read before `{storage := s}`, the substituted storage denotes, up to
`Equiv`, what the storage term denotes after it; `storage` itself becomes
`s`, which denotes the storage its run leaves (`STerm.denote_eval`). -/
theorem STerm.withSt_denote (hs : w.s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (s' : STerm C) → s'.stExplicit = true → Struct.Equiv ((s'.withSt w).denote σ) (s'.denote τ)
  | .storage, _ => STerm.denote_eval hs
  | .pv x, _ => by
    simp only [STerm.withSt, STerm.denote, hk.getEnv x]
    exact Equiv.refl _
  | .save s' p v, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.denote, PTerm.withSt_denote hs hk p he.1.2]
    exact Struct.Equiv.copyTo (STerm.withSt_denote hs hk s' he.1.1)
      (SValT.withSt_denote hs hk v he.2) _
  | .delAt s' p, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.denote, PTerm.withSt_denote hs hk p he.2]
    exact Struct.Equiv.delAt (STerm.withSt_denote hs hk s' he.1) _
  | .push s' p v, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.denote, PTerm.withSt_denote hs hk p he.1.2]
    exact Struct.Equiv.pushT (STerm.withSt_denote hs hk s' he.1.1)
      (Equiv.stripVal (SValT.withSt_denote hs hk v he.2)) _
  | .pushSlot s' p _, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.denote, PTerm.withSt_denote hs hk p he.2]
    exact Struct.Equiv.pushSlotT _ _ (STerm.withSt_denote hs hk s' he.1) _
  | .extend s' p _, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.denote, PTerm.withSt_denote hs hk p he.2]
    exact Struct.Equiv.pushSlotT _ _ (STerm.withSt_denote hs hk s' he.1) _
  | .pop s' p, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.denote, PTerm.withSt_denote hs hk p he.2]
    exact Struct.Equiv.popT (STerm.withSt_denote hs hk s' he.1) _
  | .shrink s' p, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.denote, PTerm.withSt_denote hs hk p he.2]
    exact Struct.Equiv.shrinkT (STerm.withSt_denote hs hk s' he.1) _

/-- Read before `{storage := s}`, the substituted stored value denotes, up
to `Equiv`, what it denotes after it. -/
theorem SValT.withSt_denote (hs : w.s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (v : SValT C) → v.stExplicit = true → Equiv ((v.withSt w).denote σ) (v.denote τ)
  | .val t, he => Term.withSt_denote hs hk t he
  | .newArr R n, he => by
    simp only [SValT.stExplicit] at he
    simp only [SValT.withSt, SValT.denote, (Term.withSt_denote hs hk n he).asInt]
    exact Equiv.refl _
  | .find s' p, he => by
    simp only [SValT.stExplicit, Bool.and_eq_true] at he
    simp only [SValT.withSt, SValT.denote, PTerm.withSt_denote hs hk p he.2]
    exact Equiv.findSt (STerm.withSt_denote hs hk s' he.1) _
  | .copyMem .., he => by simp only [SValT.stExplicit, Bool.false_eq_true] at he

end

end WithStDenote

/-- `{storage := s} φ` for a first-order `φ`: `s` for every `storage` in its
terms. -/
def Fml.withSt (s : STerm C) : Fml C → Fml C
  | .eq a b => .eq (a.withSt ⟨s⟩) (b.withSt ⟨s⟩)
  | .defined t => .defined (t.withSt ⟨s⟩)
  | .not φ => .not (φ.withSt s)
  | .and φ ψ => .and (φ.withSt s) (ψ.withSt s)
  | .imp φ ψ => .imp (φ.withSt s) (ψ.withSt s)
  | φ => φ

/-- Every storage read of the formula's terms is a `storage` term
(`Term.stExplicit`). -/
def Fml.stExplicit : Fml C → Bool
  | .eq a b => a.stExplicit && b.stExplicit
  | .defined t => t.stExplicit
  | .not φ => φ.stExplicit
  | .and φ ψ | .imp φ ψ => φ.stExplicit && ψ.stExplicit
  | _ => true

/-- A first-order formula with `s` substituted for `storage` holds before
the write as the formula holds after it. -/
theorem Fml.withSt_holds {s : STerm C} {σ τ : State} (hs : s.eval σ = .ok τ) :
    (φ : Fml C) → φ.rigid = true → φ.stExplicit = true → (holds σ (φ.withSt s) ↔ holds τ φ)
  | .tt, _, _ => Iff.rfl
  | .eq a b, _, he => by
    simp only [Fml.stExplicit, Bool.and_eq_true] at he
    have hk : σ.Keeps τ := STerm.eval_keeps s hs
    have ea : Theory.StValue.Equiv ((a.withSt ⟨s⟩).denote σ) (a.denote τ) :=
      Term.withSt_denote (w := ⟨s⟩) hs hk a he.1
    have eb : Theory.StValue.Equiv ((b.withSt ⟨s⟩).denote σ) (b.denote τ) :=
      Term.withSt_denote (w := ⟨s⟩) hs hk b he.2
    simp only [Fml.withSt, holds]
    exact ⟨fun e => (ea.symm.trans e).trans eb, fun e => (ea.trans e).trans eb.symm⟩
  | .defined t, _, he => by
    simp only [Fml.stExplicit] at he
    simp only [Fml.withSt, holds,
      Term.withSt_eval (w := ⟨s⟩) hs (STerm.eval_keeps s hs) t he]
  | .not φ, hr, he => by
    simp only [Fml.rigid] at hr
    simp only [Fml.stExplicit] at he
    simp only [Fml.withSt, holds, Fml.withSt_holds hs φ hr he]
  | .and φ ψ, hr, he => by
    simp only [Fml.rigid, Bool.and_eq_true] at hr
    simp only [Fml.stExplicit, Bool.and_eq_true] at he
    simp only [Fml.withSt, holds, Fml.withSt_holds hs φ hr.1 he.1, Fml.withSt_holds hs ψ hr.2 he.2]
  | .imp φ ψ, hr, he => by
    simp only [Fml.rigid, Bool.and_eq_true] at hr
    simp only [Fml.stExplicit, Bool.and_eq_true] at he
    simp only [Fml.withSt, holds, Fml.withSt_holds hs φ hr.1 he.1, Fml.withSt_holds hs ψ hr.2 he.2]
  | .upd .., hr, _ | .modal .., hr, _ | .havoc _, hr, _ | .all .., hr, _ => by
    simp only [Fml.rigid, Bool.false_eq_true] at hr

/-- Under the box, a first-order formula with `s` for `storage` gives the
formula behind `{storage := s}`: where `s` runs, `Fml.withSt_holds`; where it
halts, the box holds. -/
theorem Fml.withSt_box {s : STerm C} {φ : Fml C} (hr : φ.rigid = true)
    (he : φ.stExplicit = true) (σ : State) (h : holds σ (φ.withSt s)) :
    holds σ (.upd .box [.storage s] φ) := by
  simp only [holds, Upd.apply, List.foldlM_cons, List.foldlM_nil, Close.UpdElem.write_storage]
  cases hs : s.eval σ with
  | error _ => trivial
  | ok τ =>
    have hk : σ.Keeps τ := STerm.eval_keeps s hs
    simp only [Res.ok_bind]
    rw [hk]
    exact (Fml.withSt_holds hs φ hr he).1 h

/-- **`applyOnRigidFormula` for a storage write, under the box**: the last
update of the context, `{storage := s}`, is applied to a first-order goal and
dropped — `s` for every `storage` of the goal.

Example: `{ storage := save(storage, alice.age, 42) } ⟹ find(storage, alice.age) ≐ 42`
becomes `⟹ find(save(storage, alice.age, 42), alice.age) ≐ 42`, which the
Theory's `find_copyTo_same` rewrites to `42 ≐ 42`. -/
theorem Proves.applyStorageBox {R : RuleSet} {Γ : List (Hyp C)} {s : STerm C} {φ : Fml C}
    (h : Proves R Γ (φ.withSt s))
    (hr : φ.rigid = true := by first | rfl | decide)
    (he : φ.stExplicit = true := by first | rfl | decide)
    (hφ : (Hyp.wrap (Γ ++ [.upd .box [.storage s]]) φ).modalFree = true := by
      first | rfl | decide) :
    Proves R (Γ ++ [.upd .box [.storage s]]) φ :=
  .close (fun σ => by
    have hσ : holds σ (Hyp.wrap Γ (φ.withSt s)) := h.sound σ
    rw [Hyp.wrap_append]
    exact Hyp.wrap_mono (fun τ hτ => Fml.withSt_box hr he τ hτ) Γ σ hσ) hφ

/-- `sol_apply_upd`: apply the last update of the context to the first-order
goal and drop it — `Proves.applyStorageBox` for `{storage := s}`,
`Proves.applyOnRigidBox` for an update of locals, or the merged update of
`mergeStorage` under a goal that reads no storage — then compute the
substituted goal, so that the next `rw [h]` finds its terms (it matches
syntactically, and `Fml.subst`/`Fml.withSt` left folded hide them). -/
macro "sol_apply_upd" : tactic => `(tactic| (
  first
    | refine Proves.applyStorageBox ?_
    | refine Proves.applyOnRigidBox ?_
  simp (config := { decide := true }) only [Fml.withSt, Term.withSt, PTerm.withSt, STerm.withSt,
    SValT.withSt, Fml.subst, Term.subst, PTerm.subst, STerm.subst, SValT.subst, ITerm.subst,
    MAddr.subst, MTerm.subst, MValT.subst, Upd.valOf, Upd.pathOf, Upd.refOf, Upd.storOf,
    Upd.lastWrite, UpdElem.var?, Upd.withSt, UpdElem.withSt, List.map_cons, List.map_nil,
    ↓reduceIte]))

end Solidity
