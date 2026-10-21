import Solidity.Calculus.Quote

/-!
# The target language of `sol_decide`, typed

The terms `Calculus/Decide.lean` pushes the updates into and eliminates the
reads of writes from, each read in the state a formula starts in
(`LTm.eval`), and the formulas over them (`LFml`).  The language is the
typed signature itself (`Signature.lean`'s symbols `Op0` … `Op3`, at its
sorts `Srt`), with what a reduction adds:

* **atoms** (`var k`): the local at a position `k` of the scoped leaf's
  context, which a quantifier of the reduction binds (`LFml.all`), read in a
  valuation of the positions (`AEnv`);
* **guards**: `seq d a` (`a`, once `d` returns), `orElse a b` (`a`, or `b`
  where `a` halts), `kite a b t e` (`t` where the words `a` and `b` are
  equal, `e` where they differ), `err` (halts);
* **a path step unchecked** (`index`): `p[i]` as a reference, its index not
  checked against any storage (`Op2.at` checks it against the storage it is
  read in); the elimination writes the paths it reads through it;
* **the starting storage observed** (`obsW`, `obsL`, `obsH`): the word, the
  live length, and whether a location is there, of the storage the formula
  starts in, as the typed Theory observes it (`Storage.obs`,
  `Theory/Typed/Obs.lean`).  These are the atoms the elimination leaves; a
  location that is not there shows the default word and length `0`.

A term denotes what the symbols denote (`OpN.eval` on the starting global
part `g`), `none` where it reverts: so a term pushed in reads what the
scoped term read (`Calculus/DecideScoped.lean`), and the elimination keeps
what a term reads, as an equality.

`LTm.eval` is written with the recursor (Gate G0, conditions 1 and 2) and is
read in proofs only, so it has no compiled twin; its equations are `rfl`.
-/

namespace Solidity

namespace Decide

open Semantics

variable {C : Contract}

/-! ## Atoms -/

/-- A valuation of the positions a reduction quantifies over: at each
primitive type, a value for every position. -/
structure AEnv where
  b : Nat → Bool
  u : Nat → PrimTy.uint.Denote
  i : Nat → PrimTy.int.Denote

/-- The value of the position `k` at the type `p`. -/
def AEnv.get (ν : AEnv) : (p : PrimTy) → Nat → p.Denote
  | .bool => ν.b
  | .uint => ν.u
  | .int => ν.i

/-- The position `k` bound to `v`. -/
def AEnv.set (ν : AEnv) : (p : PrimTy) → Nat → p.Denote → AEnv
  | .bool, k, v => { ν with b := fun j => if j = k then v else ν.b j }
  | .uint, k, v => { ν with u := fun j => if j = k then v else ν.u j }
  | .int, k, v => { ν with i := fun j => if j = k then v else ν.i j }

/-- Every position at its default. -/
def AEnv.dflt : AEnv := ⟨fun _ => PrimTy.dflt .bool, fun _ => PrimTy.dflt .uint,
  fun _ => PrimTy.dflt .int⟩

instance : Inhabited AEnv := ⟨AEnv.dflt⟩

@[simp] theorem AEnv.get_set_self (ν : AEnv) (p : PrimTy) (k : Nat) (v : p.Denote) :
    (ν.set p k v).get p k = v := by
  cases p <;> simp only [AEnv.set, AEnv.get, if_true]

theorem AEnv.get_set_ne (ν : AEnv) (p q : PrimTy) {k j : Nat} (v : p.Denote) (h : j ≠ k) :
    (ν.set p k v).get q j = ν.get q j := by
  cases p <;> cases q <;> simp only [AEnv.set, AEnv.get, h, if_false]

/-! ## Terms -/

/-- **A term of the reduction** at a sort: the typed signature, the atoms,
the guards, an unchecked path step, the starting storage observed. -/
inductive LTm (C : Contract) : Srt → Type where
  /-- The local at the position `k`: an atom. -/
  | var {p : PrimTy} (k : Nat) : LTm C (.val p)
  | app0 {s : Srt} (o : Op0 C s) : LTm C s
  | app1 {a s : Srt} (o : Op1 C a s) (x : LTm C a) : LTm C s
  | app2 {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) : LTm C s
  | app3 {a b c s : Srt} (o : Op3 C a b c s) (x : LTm C a) (y : LTm C b) (z : LTm C c) : LTm C s
  /-- `q[i]`, not checked: a reference one step further. -/
  | index {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (q : LTm C (.path (.ref R)))
      (i : LTm C (.val k)) : LTm C (.path V)
  /-- The word of the starting storage at `q` (its default where nothing is). -/
  | obsW {p : PrimTy} (q : LTm C (.path (.prim p))) : LTm C (.val p)
  /-- The live length of the starting storage's array at `q` (`0` where none). -/
  | obsL {E : Ty} (q : LTm C (.path (.ref (.array E)))) : LTm C (.val .uint)
  /-- Whether the starting storage has a location at `q`. -/
  | obsH {T : Ty} (q : LTm C (.path T)) : LTm C (.val .bool)
  /-- `d`, then `a`: `a` guarded by `d` returning. -/
  | seq {s' s : Srt} (d : LTm C s') (a : LTm C s) : LTm C s
  /-- `a`, or `b` where `a` halts. -/
  | orElse {s : Srt} (a b : LTm C s) : LTm C s
  /-- `t` where the words `a` and `b` are equal, `e` where they differ. -/
  | kite {p : PrimTy} {s : Srt} (a b : LTm C (.val p)) (t e : LTm C s) : LTm C s
  /-- Halts. -/
  | err {s : Srt} : LTm C s

instance {s : Srt} : Inhabited (LTm C s) := ⟨.err⟩

/-- **What a term reads** in the global part `g`, its atoms in `ν`: `none`
where it reverts. -/
noncomputable def LTm.eval (g : State C []) (ν : AEnv) {s : Srt} (t : LTm C s) :
    Option (s.Den C g.H) :=
  @LTm.rec C (fun s _ => Option (s.Den C g.H))
    (fun {p} k => some (ν.get p k))
    (fun o => o.eval g)
    (fun o _ x => o.eval g x)
    (fun o _ _ x y => o.eval g x y)
    (fun o _ _ _ x y z => o.eval g x y z)
    (fun it _ _ q i => q.bind fun r => i.bind fun k => some (r.index it k))
    (fun _ q => q.bind fun r => some (g.storage.obs.word (.ref r)))
    (fun _ q => q.bind fun r => some (uintOfNat (g.storage.obs.len (.ref r))))
    (fun _ q => q.bind fun r => some (g.storage.obs.has (.ref r)))
    (fun _ _ d a => d.bind fun _ => a)
    (fun _ _ a b => a.or b)
    (fun _ _ _ _ a b t e => a.bind fun x => b.bind fun y => if x = y then t else e)
    none s t

section Eval

variable (g : State C []) (ν : AEnv)

theorem LTm.eval_var {p : PrimTy} (k : Nat) :
    ((LTm.var k : LTm C (.val p)).eval g ν : Option p.Denote) = some (ν.get p k) := rfl
theorem LTm.eval_app0 {s : Srt} (o : Op0 C s) : (LTm.app0 o).eval g ν = o.eval g := rfl
theorem LTm.eval_app1 {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    (LTm.app1 o x).eval g ν = o.eval g (x.eval g ν) := rfl
theorem LTm.eval_app2 {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    (LTm.app2 o x y).eval g ν = o.eval g (x.eval g ν) (y.eval g ν) := rfl
theorem LTm.eval_app3 {a b c s : Srt} (o : Op3 C a b c s) (x : LTm C a) (y : LTm C b)
    (z : LTm C c) : (LTm.app3 o x y z).eval g ν = o.eval g (x.eval g ν) (y.eval g ν) (z.eval g ν) :=
  rfl
theorem LTm.eval_index {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    (q : LTm C (.path (.ref R))) (i : LTm C (.val k)) :
    ((LTm.index it q i).eval g ν : Option (SRef C V)) =
      (q.eval g ν : Option (SRef C (.ref R))).bind fun r =>
        (i.eval g ν : Option k.Denote).bind fun j => some (r.index it j) := rfl
theorem LTm.eval_obsW {p : PrimTy} (q : LTm C (.path (.prim p))) :
    ((LTm.obsW q).eval g ν : Option p.Denote) =
      (q.eval g ν : Option (SRef C (.prim p))).bind fun r => some (g.storage.obs.word (.ref r)) :=
  rfl
theorem LTm.eval_obsL {E : Ty} (q : LTm C (.path (.ref (.array E)))) :
    ((LTm.obsL q).eval g ν : Option PrimTy.uint.Denote) =
      (q.eval g ν : Option (SRef C (.ref (.array E)))).bind fun r =>
        some (uintOfNat (g.storage.obs.len (.ref r))) := rfl
theorem LTm.eval_obsH {T : Ty} (q : LTm C (.path T)) :
    ((LTm.obsH q).eval g ν : Option Bool) =
      (q.eval g ν : Option (SRef C T)).bind fun r => some (g.storage.obs.has (.ref r)) := rfl
theorem LTm.eval_seq {s' s : Srt} (d : LTm C s') (a : LTm C s) :
    (LTm.seq d a).eval g ν = (d.eval g ν).bind fun _ => a.eval g ν := rfl
theorem LTm.eval_orElse {s : Srt} (a b : LTm C s) :
    (LTm.orElse a b).eval g ν = (a.eval g ν).or (b.eval g ν) := rfl
theorem LTm.eval_kite {p : PrimTy} {s : Srt} (a b : LTm C (.val p)) (t e : LTm C s) :
    (LTm.kite a b t e).eval g ν =
      (a.eval g ν : Option p.Denote).bind fun x => (b.eval g ν : Option p.Denote).bind fun y =>
        if x = y then t.eval g ν else e.eval g ν := rfl

end Eval

/-! ## Formulas -/

/-- **A first-order formula over the terms.** -/
inductive LFml (C : Contract) where
  | tt
  /-- Both sides return, and agree. -/
  | eq {p : PrimTy} (a b : LTm C (.val p))
  | not (φ : LFml C)
  | and (φ ψ : LFml C)
  | imp (φ ψ : LFml C)
  /-- For every value of the type, the position `k` holding it: a
  quantifier of the scoped leaf (a parameter, a specification's `\forall`). -/
  | all (k : Nat) (p : PrimTy) (φ : LFml C)

instance : Inhabited (LFml C) := ⟨.tt⟩

/-- `false`. -/
abbrev LFml.ff : LFml C := .not .tt

/-- A hidden binder's local read as a quantifier: a value's, at the
position `k`; any other binds nothing. -/
def LFml.allB (t : LTy) (k : Nat) (φ : LFml C) : LFml C :=
  match t with
  | .val p => .all k p φ
  | _ => φ

/-- **A formula holds** in the global part `g`, its atoms in `ν`. -/
def LFml.holds (g : State C []) : AEnv → LFml C → Prop
  | _, .tt => True
  | ν, @LFml.eq _ p a b =>
    match (a.eval g ν : Option p.Denote), (b.eval g ν : Option p.Denote) with
    | some x, some y => x = y
    | _, _ => False
  | ν, .not φ => ¬ φ.holds g ν
  | ν, .and φ ψ => φ.holds g ν ∧ ψ.holds g ν
  | ν, .imp φ ψ => φ.holds g ν → ψ.holds g ν
  | ν, .all k p φ => ∀ v : p.Denote, φ.holds g (ν.set p k v)

/-- `ψ` holds in every global part and every valuation of its atoms. -/
def LFml.Valid (ψ : LFml C) : Prop := ∀ (g : State C []) (ν : AEnv), ψ.holds g ν

theorem LFml.holds_eq_iff (g : State C []) (ν : AEnv) {p : PrimTy} (a b : LTm C (.val p)) :
    (LFml.eq a b).holds g ν ↔ ∃ x, (a.eval g ν : Option p.Denote) = some x ∧
      (b.eval g ν : Option p.Denote) = some x := by
  simp only [LFml.holds]
  cases (a.eval g ν : Option p.Denote) <;> cases (b.eval g ν : Option p.Denote) <;>
    simp only [Option.some.injEq, exists_eq_left', reduceCtorEq, false_and, exists_false,
      and_false, eq_comm]

/-- `t` returns: `t = t`. -/
abbrev LFml.rets {p : PrimTy} (t : LTm C (.val p)) : LFml C := .eq t t

theorem LFml.holds_rets (g : State C []) (ν : AEnv) {p : PrimTy} (t : LTm C (.val p)) :
    (LFml.eq t t).holds g ν ↔ ∃ x, (t.eval g ν : Option p.Denote) = some x := by
  rw [LFml.holds_eq_iff]
  simp only [and_self]

/-! ## Builders -/

/-- A literal. -/
abbrev LTm.lit {p : PrimTy} (v : p.Denote) : LTm C (.val p) := .app0 (.lit v)

/-- `true`. -/
abbrev LTm.tt : LTm C (.val .bool) := .lit (p := .bool) true

/-- The term is the literal `true`. -/
def LTm.isTT (t : LTm C (.val .bool)) : Bool :=
  match t with
  | .app0 (.lit v) => v
  | _ => false

/-- The term is the literal `false`. -/
def LTm.isFF (t : LTm C (.val .bool)) : Bool :=
  match t with
  | .app0 (.lit v) => !v
  | _ => false

theorem LTm.isFF_eval {g : State C []} {ν : AEnv} {t : LTm C (.val .bool)} (h : t.isFF = true) :
    (t.eval g ν : Option Bool) = some false := by
  cases t with
  | app0 o =>
    cases o with
    | lit v =>
      have hv : (v : Bool) = false := by simpa only [LTm.isFF, Bool.not_eq_true'] using h
      show some v = some false
      rw [hv]
    | _ => simp only [LTm.isFF, reduceCtorEq] at h
  | _ => simp only [LTm.isFF, reduceCtorEq] at h

theorem LTm.isTT_eval {g : State C []} {ν : AEnv} {t : LTm C (.val .bool)} (h : t.isTT = true) :
    (t.eval g ν : Option Bool) = some true := by
  cases t with
  | app0 o =>
    cases o with
    | lit v =>
      have hv : (v : Bool) = true := h
      show some v = some true
      rw [hv]
    | _ => simp only [LTm.isTT, reduceCtorEq] at h
  | _ => simp only [LTm.isTT, reduceCtorEq] at h

/-- A literal `uint`. -/
def LTm.nat (n : Nat) : LTm C (.val .uint) := .lit (uintOfNat n)

/-- A unary symbol that returns where its argument does: a member path. -/
def _root_.Solidity.Op1.retsStep {a s : Srt} : Op1 C a s → Bool
  | .field _ => true
  | _ => false

/-- An operator that returns on every pair of operands it takes: a
comparison or a connective. -/
def _root_.Solidity.BinOp.isCmp : BinOp → Bool
  | .lt | .gt | .le | .ge | .eqB | .neB | .and | .or => true
  | _ => false

theorem binopT_isSome (op : BinOp) (hc : op.isCmp = true) {p : PrimTy}
    (h : op.accepts p = true) (a : p.Denote) {y : Option p.Denote} (hy : y.isSome = true) :
    (binopT op h a y).isSome = true := by
  obtain ⟨b, rfl⟩ := Option.isSome_iff_exists.1 hy
  unfold binopT
  split
  · rfl
  · show (op.evalT h a b).isSome = true
    cases p <;> cases op <;> simp only [BinOp.isCmp, Bool.false_eq_true] at hc <;>
      first | rfl | exact absurd h (by decide)

/-- A binary symbol that returns where its arguments do: a comparison. -/
def _root_.Solidity.Op2.retsStep {a b s : Srt} : Op2 C a b s → Bool
  | .binop op _ => op.isCmp
  | _ => false

/-- `LTm.retsS`'s compiled twin. -/
def LTm.retsSM : {s : Srt} → LTm C s → Bool
  | _, .var _ | _, .app0 _ => true
  | _, .app1 o x => o.retsStep && x.retsSM
  | _, .app2 o x y => o.retsStep && x.retsSM && y.retsSM
  | _, .index _ q i => q.retsSM && i.retsSM
  | _, .obsW q | _, .obsL q | _, .obsH q => q.retsSM
  | _, .seq d a => d.retsSM && a.retsSM
  | _, .kite a b t e => a.retsSM && b.retsSM && t.retsSM && e.retsSM
  | _, _ => false

/-- **The term always returns**: an atom, a constant, a path of members
and unchecked indices below a root, the starting storage read at one, a
comparison of such terms, and a guard or a choice between them (the
starting storage's reads after a delete keep these).  By the recursor. -/
@[implemented_by LTm.retsSM]
def LTm.retsS {s : Srt} (t : LTm C s) : Bool :=
  @LTm.rec C (fun _ _ => Bool)
    (@fun _ _ => true) (@fun _ _ => true)
    (@fun _ _ o _ ihx => o.retsStep && ihx)
    (@fun _ _ _ o _ _ ihx ihy => o.retsStep && ihx && ihy)
    (@fun _ _ _ _ _ _ _ _ _ _ _ => false)
    (@fun _ _ _ _ _ _ ihq ihi => ihq && ihi)
    (@fun _ _ ih => ih) (@fun _ _ ih => ih) (@fun _ _ ih => ih)
    (@fun _ _ _ _ ihd iha => ihd && iha) (@fun _ _ _ _ _ => false)
    (@fun _ _ _ _ _ _ iha ihb iht ihe => iha && ihb && iht && ihe) (@fun _ => false) s t

theorem LTm.retsS_eq_retsSM {s : Srt} (t : LTm C s) : t.retsS = t.retsSM := by
  induction t with
  | var | app0 | app3 | orElse | err => rfl
  | app1 o x ih | obsW x ih | obsL x ih | obsH x ih => simp only [LTm.retsSM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.retsSM, ← ihx, ← ihy]; rfl
  | index it q i ihq ihi => simp only [LTm.retsSM, ← ihq, ← ihi]; rfl
  | seq d a ihd iha => simp only [LTm.retsSM, ← ihd, ← iha]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.retsSM, ← iha, ← ihb, ← iht, ← ihe]; rfl

theorem Op0.eval_isSome (g : State C []) {s : Srt} (o : Op0 C s) : (o.eval g).isSome = true := by
  cases o <;> rfl

theorem LTm.retsS_eval {g : State C []} {ν : AEnv} {s : Srt} {t : LTm C s} (h : t.retsS = true) :
    ∃ v, t.eval g ν = some v := by
  induction t with
  | var k => exact ⟨_, rfl⟩
  | app0 o => exact Option.isSome_iff_exists.1 (Op0.eval_isSome g o)
  | app1 o x ih =>
    have h' : o.retsStep = true ∧ x.retsS = true := Bool.and_eq_true_iff.1 h
    obtain ⟨v, hv⟩ := ih h'.2
    have h1 := h'.1
    cases o <;> simp only [Op1.retsStep, Bool.false_eq_true] at h1
    exact ⟨_, by rw [LTm.eval_app1, hv]; rfl⟩
  | index it q i ihq ihi =>
    have h' : q.retsS = true ∧ i.retsS = true := Bool.and_eq_true_iff.1 h
    obtain ⟨v, hv⟩ := ihq h'.1
    obtain ⟨w, hw⟩ := ihi h'.2
    exact ⟨_, by rw [LTm.eval_index, hv, hw]; rfl⟩
  | obsW q ih | obsL q ih | obsH q ih =>
    obtain ⟨v, hv⟩ := ih h
    exact ⟨_, by show (q.eval g ν).bind _ = _; rw [hv]; rfl⟩
  | app2 o x y ihx ihy =>
    have h' : (o.retsStep && x.retsS) = true ∧ y.retsS = true := Bool.and_eq_true_iff.1 h
    have h'' : o.retsStep = true ∧ x.retsS = true := Bool.and_eq_true_iff.1 h'.1
    obtain ⟨v, hv⟩ := ihx h''.2
    obtain ⟨w, hw⟩ := ihy h'.2
    have h1 := h''.1
    cases o with
    | binop op hp =>
      have hs := binopT_isSome op h1 hp v (y := some w) rfl
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hs
      exact ⟨r, by rw [LTm.eval_app2, hv, hw]; exact hr⟩
    | _ => simp only [Op2.retsStep, Bool.false_eq_true] at h1
  | seq d a ihd iha =>
    have h' : d.retsS = true ∧ a.retsS = true := Bool.and_eq_true_iff.1 h
    obtain ⟨v, hv⟩ := ihd h'.1
    obtain ⟨w, hw⟩ := iha h'.2
    exact ⟨w, by rw [LTm.eval_seq, hv]; exact hw⟩
  | kite a b t e iha ihb iht ihe =>
    simp only [LTm.retsS, Bool.and_eq_true] at h
    obtain ⟨⟨⟨ha, hb⟩, ht⟩, he⟩ := h
    obtain ⟨x, hx⟩ := iha ha
    obtain ⟨y, hy⟩ := ihb hb
    obtain ⟨u, hu⟩ := iht ht
    obtain ⟨w, hw⟩ := ihe he
    rw [LTm.eval_kite, hx, hy]
    by_cases hxy : x = y
    · exact ⟨u, by simp only [Option.bind_some, hxy, if_true]; exact hu⟩
    · exact ⟨w, by simp only [Option.bind_some, hxy, if_false]; exact hw⟩
  | _ => simp only [LTm.retsS, Bool.false_eq_true] at h

/-- `a`, guarded by `g` returning; `a` alone after a term that always
returns. -/
def seqL {s' s : Srt} (g : LTm C s') (a : LTm C s) : LTm C s :=
  if g.retsS then a else .seq g a

theorem seqL_eval (g₀ : State C []) (ν : AEnv) {s' s : Srt} (g : LTm C s') (a : LTm C s) :
    (seqL g a).eval g₀ ν = (g.eval g₀ ν).bind fun _ => a.eval g₀ ν := by
  unfold seqL
  split
  · rename_i h
    obtain ⟨v, hv⟩ := LTm.retsS_eval (g := g₀) (ν := ν) h
    rw [hv]; rfl
  · rfl

/-- `true` where `c` is `true`, halting where it is `false`: a guard. -/
def LTm.assert (c : LTm C (.val .bool)) : LTm C (.val .bool) :=
  if c.isTT then .tt else .app3 .ite c .tt .err

theorem LTm.eval_assert (g : State C []) (ν : AEnv) (c : LTm C (.val .bool)) :
    ((LTm.assert c).eval g ν : Option Bool) =
      (c.eval g ν : Option Bool).bind fun b => if (b : Bool) = true then some true else none := by
  unfold LTm.assert
  split
  · rename_i h
    rw [LTm.isTT_eval h]; rfl
  · rw [LTm.eval_app3]
    cases h : (c.eval g ν : Option Bool) with
    | none => rfl
    | some b => cases b <;> rfl

/-! ## Printing

A term in solkey's notation (`docs/lean-key-rule-map.md`): `find(s, q)`,
`save(s, q, v)`, `delAt(s, q)`, the starting storage read as
`find(storage, q)`, `find(storage, q.length)`, `has(storage, q)`,
`if(a = b) then t else e` a key test, `(g; a)` a term `a` behind the guards
`g` (only Lean has guards, `orElse` and `err`). -/

/-- A value of a primitive type, printed. -/
def ppVal : (p : PrimTy) → p.Denote → String
  | .bool, b => toString (show Bool from b)
  | .uint, v => toString (v : {n : Int // PrimTy.uint.inRange n = true}).1
  | .int, v => toString (v : {n : Int // PrimTy.int.inRange n = true}).1

/-- The term a sequence returns, its guards dropped. -/
def LTm.seqValue {s : Srt} : LTm C s → LTm C s
  | .seq _ a => a.seqValue
  | t => t

mutual
/-- A term, printed, a position by `nm`. -/
partial def LTm.ppWith (nm : Nat → String) {s : Srt} : LTm C s → String
  | .var k => nm k
  | .app0 o => match o with
    | @Op0.lit _ p v => ppVal p v
    | .env k => k.toStr
    | .root r _ => r
    | .storage => "storage"
    | .memory => "memory"
    | .mtSt => "mtSt"
    | .member _ f _ => f
    | .zlit n => toString n
  | .app1 o x => match o with
    | .unop op _ => op.show (x.ppArg nm)
    | @Op1.field _ _ f _ _ => s!"{x.ppWith nm}.{f}"
    | @Op1.mfield _ _ f _ _ => s!"{x.ppWith nm}.{f}"
    | @Op1.fieldIn _ _ _ f _ _ => s!"{x.ppWith nm}.{f}"
    | .sval | .mval | .ref => x.ppWith nm
    | @Op1.fixedCopy _ _ _ R _ => s!"fixedCopy({(Ty.ref R).toStr}, {x.ppWith nm})"
    | .next => s!"next({x.ppWith nm})"
    | .toInt => s!"toInt({x.ppWith nm})"
    | .net => s!"net({x.ppWith nm})"
    | .delValue => s!"delValue({x.ppWith nm})"
    | .wt => s!"wt({x.ppWith nm})"
    | .cleanTail => s!"cleanTail({x.ppWith nm})"
    | .newArr _ => s!"newArr({x.ppWith nm})"
    | .alloc R _ => s!"alloc({x.ppWith nm}, {(Ty.ref R).toStr})"
    | .addM R _ => s!"addM({x.ppWith nm}, {(Ty.ref R).toStr})"
    | .select r _ => s!"select({x.ppWith nm}, {r})"
    | .selectIn _ => s!"selectIn({x.ppWith nm})"
  | .app2 o x y => match o with
    | .binop op _ => s!"{x.ppArg nm} {op.sym} {y.ppArg nm}"
    | .find => s!"find({x.ppWith nm}, {y.ppWith nm})"
    | .len => s!"find({x.ppWith nm}, {y.ppWith nm}.length)"
    | .sfind => s!"select({x.ppWith nm}, {y.ppWith nm})"
    | .delAt => s!"delAt({x.ppWith nm}, {y.ppWith nm})"
    | .pushSlot => s!"pushSlot({x.ppWith nm}, {y.ppWith nm})"
    | .pop => s!"pop({x.ppWith nm}, {y.ppWith nm})"
    | .shrink => s!"shrink({x.ppWith nm}, {y.ppWith nm})"
    | .extend => s!"extend({x.ppWith nm}, {y.ppWith nm})"
    | .at _ => s!"{x.ppWith nm}[{y.ppWith nm}]"
    | .nextIn => s!"next({x.ppWith nm}, {y.ppWith nm})"
    | .read => s!"read({x.ppWith nm}, {y.ppWith nm})"
    | .mlen => s!"size({x.ppWith nm}, {y.ppWith nm})"
    | .hash k => s!"{k.toStr}({x.ppWith nm}, {y.ppWith nm})"
    | .copyMem => s!"copyMem({x.ppWith nm}, {y.ppWith nm})"
    | .iread => s!"read({x.ppWith nm}, {y.ppWith nm})"
    | .copy _ => s!"copy({x.ppWith nm}, {y.ppWith nm})"
    | .mat _ => s!"{x.ppWith nm}[{y.ppWith nm}]"
    | .copySt _ => s!"copySt({x.ppWith nm}, {y.ppWith nm})"
    | .findIn => s!"find({x.ppWith nm}, {y.ppWith nm})"
    | .delAtIn => s!"delAt({x.ppWith nm}, {y.ppWith nm})"
    | .sfindIn => s!"select({x.ppWith nm}, {y.ppWith nm})"
    | .zbin op _ => s!"{x.ppArg nm} {op.sym} {y.ppArg nm}"
    | .zcmp op _ => s!"{x.ppArg nm} {op.sym} {y.ppArg nm}"
  | .app3 o x y z => match o with
    | .ite => s!"if({x.ppWith nm}) then {y.ppArg nm} else {z.ppWith nm}"
    | .save => s!"save({x.ppWith nm}, {y.ppWith nm}, {z.ppWith nm})"
    | .push => s!"push({x.ppWith nm}, {y.ppWith nm}, {z.ppWith nm})"
    | .atIn _ => s!"{y.ppWith nm}[{z.ppWith nm}]"
    | .write => s!"write({x.ppWith nm}, {y.ppWith nm}, {z.ppWith nm})"
    | .saveIn => s!"save({x.ppWith nm}, {y.ppWith nm}, {z.ppWith nm})"
    | .modular op => s!"{op.toStr}({x.ppWith nm}, {y.ppWith nm}, {z.ppWith nm})"
  | .index _ q i => s!"{q.ppWith nm}[{i.ppWith nm}]"
  | .obsW q => s!"find(storage, {q.ppWith nm})"
  | .obsL q => s!"find(storage, {q.ppWith nm}.length)"
  | .obsH q => s!"has(storage, {q.ppWith nm})"
  | t@(.seq ..) =>
    let gs := LTm.ppGuards nm t
    let v := t.seqValue
    if gs.isEmpty then v.ppWith nm else s!"({", ".intercalate gs}; {v.ppWith nm})"
  | .orElse a b => s!"orElse({a.ppWith nm}, {b.ppWith nm})"
  | .kite a b t e => s!"if({a.ppWith nm} = {b.ppWith nm}) then {t.ppArg nm} else {e.ppWith nm}"
  | .err => "err"

/-- A term as an operand: parenthesised unless it is atomic. -/
partial def LTm.ppArg (nm : Nat → String) {s : Srt} : LTm C s → String
  | t@(.app2 (.binop ..) ..) | t@(.app3 .ite ..) | t@(.kite ..) => s!"({t.ppWith nm})"
  | t => t.ppWith nm

/-- The guards of a sequence, printed, the ones that are literals dropped. -/
partial def LTm.ppGuards (nm : Nat → String) {s : Srt} : LTm C s → List String
  | .seq d a => LTm.ppGuard nm d ++ LTm.ppGuards nm a
  | _ => []

/-- A guard, printed: its own guards and the term, a literal dropped. -/
partial def LTm.ppGuard (nm : Nat → String) {s : Srt} : LTm C s → List String
  | .seq d a => LTm.ppGuard nm d ++ LTm.ppGuard nm a
  | .app0 (.lit _) => []
  | g@(.app3 .ite ..) | g@(.kite ..) => [s!"({g.ppWith nm})"]
  | g => [g.ppWith nm]
end

/-- A term, printed, the position `k` as `pos(k)`. -/
def LTm.pp {s : Srt} (t : LTm C s) : String := t.ppWith fun k => s!"pos({k})"

/-- A formula, printed, a position by `nm`, a quantifier's local named by
`nm` too. -/
partial def LFml.ppWith (nm : Nat → String) (tyStr : PrimTy → String) : LFml C → String
  | .tt => "true"
  | .eq a b => s!"{a.ppArg nm} = {b.ppArg nm}"
  | .not φ => s!"¬{atom φ}"
  | .and φ ψ => s!"{conj φ} ∧ {conj ψ}"
  | .imp φ ψ => s!"{conj φ} → {LFml.ppWith nm tyStr ψ}"
  | .all k p φ => s!"∀ {tyStr p} {nm k}; {LFml.ppWith nm tyStr φ}"
where
  atom : LFml C → String
    | φ@(.tt) | φ@(.not _) | φ@(.eq ..) => LFml.ppWith nm tyStr φ
    | φ => s!"({LFml.ppWith nm tyStr φ})"
  conj : LFml C → String
    | φ@(.imp ..) | φ@(.all ..) => s!"({LFml.ppWith nm tyStr φ})"
    | φ => LFml.ppWith nm tyStr φ

/-- A formula, printed, the position `k` as `pos(k)`. -/
def LFml.pp (φ : LFml C) : String := φ.ppWith (fun k => s!"pos({k})") PrimTy.toStr

/-! ## Quoting

The reduction is computed by compiled code and quoted back for the kernel
to check (`sol_reduce`).  `LTm` is an indexed family, so its quoter is
written by hand, over `Calculus/Quote.lean`'s quoters of the symbols. -/

open Lean (Expr mkAppN mkConst mkApp mkApp2 mkApp3 toExpr) in
/-- A term, quoted. -/
partial def LTm.quote : {s : Srt} → LTm C s → QM Expr
  | _, @LTm.var _ p k => do return mkApp3 (mkConst ``LTm.var) (← Quote.contract) (toExpr p) (toExpr k)
  | s, .app0 o => do return mkAppN (mkConst ``LTm.app0) #[← Quote.contract, toExpr s, ← Quote.qOp0 o]
  | s, @LTm.app1 _ a _ o x => do
    return mkAppN (mkConst ``LTm.app1) #[← Quote.contract, toExpr a, toExpr s, ← Quote.qOp1 o,
      ← x.quote]
  | s, @LTm.app2 _ a b _ o x y => do
    return mkAppN (mkConst ``LTm.app2) #[← Quote.contract, toExpr a, toExpr b, toExpr s,
      ← Quote.qOp2 o, ← x.quote, ← y.quote]
  | s, @LTm.app3 _ a b c _ o x y z => do
    return mkAppN (mkConst ``LTm.app3) #[← Quote.contract, toExpr a, toExpr b, toExpr c, toExpr s,
      ← Quote.qOp3 o, ← x.quote, ← y.quote, ← z.quote]
  | _, @LTm.index _ R k V it q i => do
    return mkAppN (mkConst ``LTm.index) #[← Quote.contract, toExpr R, toExpr k, toExpr V,
      IndexTy.quote it, ← q.quote, ← i.quote]
  | _, @LTm.obsW _ p q => do return mkApp3 (mkConst ``LTm.obsW) (← Quote.contract) (toExpr p) (← q.quote)
  | _, @LTm.obsL _ E q => do return mkApp3 (mkConst ``LTm.obsL) (← Quote.contract) (toExpr E) (← q.quote)
  | _, @LTm.obsH _ T q => do return mkApp3 (mkConst ``LTm.obsH) (← Quote.contract) (toExpr T) (← q.quote)
  | s, @LTm.seq _ s' _ d a => do
    return mkAppN (mkConst ``LTm.seq) #[← Quote.contract, toExpr s', toExpr s, ← d.quote, ← a.quote]
  | s, .orElse a b => do
    return mkAppN (mkConst ``LTm.orElse) #[← Quote.contract, toExpr s, ← a.quote, ← b.quote]
  | s, @LTm.kite _ p _ a b t e => do
    return mkAppN (mkConst ``LTm.kite) #[← Quote.contract, toExpr p, toExpr s, ← a.quote, ← b.quote,
      ← t.quote, ← e.quote]
  | s, .err => do return mkApp2 (mkConst ``LTm.err) (← Quote.contract) (toExpr s)

open Lean (Expr mkAppN mkConst mkApp mkApp2 mkApp3 toExpr) in
/-- A formula, quoted. -/
partial def LFml.quote : LFml C → QM Expr
  | .tt => do return mkApp (mkConst ``LFml.tt) (← Quote.contract)
  | @LFml.eq _ p a b => do
    return mkAppN (mkConst ``LFml.eq) #[← Quote.contract, toExpr p, ← a.quote, ← b.quote]
  | .not φ => do return mkApp2 (mkConst ``LFml.not) (← Quote.contract) (← φ.quote)
  | .and φ ψ => do return mkApp3 (mkConst ``LFml.and) (← Quote.contract) (← φ.quote) (← ψ.quote)
  | .imp φ ψ => do return mkApp3 (mkConst ``LFml.imp) (← Quote.contract) (← φ.quote) (← ψ.quote)
  | .all k p φ => do
    return mkAppN (mkConst ``LFml.all) #[← Quote.contract, toExpr k, toExpr p, ← φ.quote]

end Decide

end Solidity
