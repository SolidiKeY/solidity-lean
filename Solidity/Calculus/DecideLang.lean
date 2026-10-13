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

theorem AEnv.get_set_ty (ν : AEnv) {p q : PrimTy} (k j : Nat) (v : p.Denote) (h : q ≠ p) :
    (ν.set p k v).get q j = ν.get q j := by
  cases p <;> cases q <;> first | exact absurd rfl h | rfl

/-- A length as a `uint`, the default past the bound (no storage has an
array that long: `SVal.array`'s `hn`). -/
def uintOfNat (n : Nat) : PrimTy.uint.Denote :=
  if h : n < 2 ^ 256 then lenU n h else PrimTy.dflt .uint

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
      (i : LTm C (.val k.keyTy)) : LTm C (.path V)
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
    (fun it _ _ q i => q.bind fun r => i.bind fun k => some (r.index it (PrimTy.key k)))
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
    (q : LTm C (.path (.ref R))) (i : LTm C (.val k.keyTy)) :
    ((LTm.index it q i).eval g ν : Option (SRef C V)) =
      (q.eval g ν : Option (SRef C (.ref R))).bind fun r =>
        (i.eval g ν : Option k.keyTy.Denote).bind fun j => some (r.index it (PrimTy.key j)) := rfl
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
theorem LTm.eval_err {s : Srt} : (LTm.err : LTm C s).eval g ν = none := rfl

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

/-- A literal `uint`. -/
def LTm.nat (n : Nat) : LTm C (.val .uint) := .lit (uintOfNat n)

/-- The literal a term is, if it is one. -/
def LTm.lit? {s : Srt} : LTm C s → Option (Σ' (p : PrimTy) (_ : s = .val p), p.Denote)
  | .app0 o => match o with
    | @Op0.lit _ p v => some ⟨p, rfl, v⟩
    | _ => none
  | _ => none

/-- The term always returns: an atom or a constant. -/
def LTm.retsS {s : Srt} (t : LTm C s) : Bool :=
  @LTm.casesOn C (fun _ _ => Bool) s t (fun _ => true) (fun _ => true) (fun _ _ => false)
    (fun _ _ _ => false) (fun _ _ _ _ => false) (fun _ _ _ => false) (fun _ => false)
    (fun _ => false) (fun _ => false) (fun _ _ => false) (fun _ _ => false)
    (fun _ _ _ _ => false) false

theorem Op0.eval_isSome (g : State C []) {s : Srt} (o : Op0 C s) : (o.eval g).isSome = true := by
  cases o <;> rfl

theorem LTm.retsS_eval {g : State C []} {ν : AEnv} {s : Srt} {t : LTm C s} (h : t.retsS = true) :
    ∃ v, t.eval g ν = some v := by
  cases t with
  | var k => exact ⟨_, rfl⟩
  | app0 o => exact Option.isSome_iff_exists.1 (Op0.eval_isSome g o)
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
def LTm.assert (c : LTm C (.val .bool)) : LTm C (.val .bool) := .app3 .ite c .tt .err

theorem LTm.eval_assert (g : State C []) (ν : AEnv) (c : LTm C (.val .bool)) :
    ((LTm.assert c).eval g ν : Option Bool) =
      (c.eval g ν : Option Bool).bind fun b => if (b : Bool) = true then some true else none := by
  rw [LTm.assert, LTm.eval_app3]
  cases h : (c.eval g ν : Option Bool) with
  | none => rfl
  | some b => cases b <;> rfl

/-- `a ⊕ b`, folded where both are literals and it returns. -/
def LTm.mkBin (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (a b : LTm C (.val p)) :
    LTm C (.val (op.ret p)) :=
  let t : LTm C (.val (op.ret p)) := .app2 (.binop op h) a b
  match a.lit?, b.lit? with
  | some ⟨_, ea, x⟩, some ⟨_, eb, y⟩ =>
    match (Srt.val.inj ea), (Srt.val.inj eb) with
    | rfl, rfl =>
      match binopT op x (some y) with
      | some r => .lit r
      | none => t
  | _, _ => t

/-- An index under a bound: `i < n` as a guard. -/
def ltG (i n : LTm C (.val .uint)) : LTm C (.val .bool) := LTm.assert (.app2 (.binop .lt rfl) i n)

/-! ## Printing

A term in solkey's notation (`docs/lean-key-rule-map.md`): `find(s, q)`,
`len(s, q)`, `save(s, q, v)`, `W(q)`/`L(q)`/`H(q)` the starting storage
observed, `if(a = b) then t else e` a key test, `(d; a)` a guard. -/

/-- A value of a primitive type, printed. -/
def ppVal : (p : PrimTy) → p.Denote → String
  | .bool, b => toString (show Bool from b)
  | .uint, v => toString (v : {n : Int // PrimTy.uint.inRange n = true}).1
  | .int, v => toString (v : {n : Int // PrimTy.int.inRange n = true}).1

/-- A term, printed. -/
partial def LTm.pp : {s : Srt} → LTm C s → String
  | _, .var k => s!"pos({k})"
  | _, .app0 o => match o with
    | @Op0.lit _ p v => ppVal p v
    | .env k => k.toStr
    | .root r _ => r
    | .storage => "storage"
    | .memory => "memory"
    | .mtSt => "mtSt"
    | .member _ f _ => f
    | .zlit n => toString n
  | _, .app1 o x => match o with
    | .unop op _ => s!"{op.sym}{x.pp}"
    | @Op1.field _ _ f _ _ => s!"{x.pp}.{f}"
    | .sval => x.pp
    | .next => s!"next({x.pp})"
    | .toInt => s!"int({x.pp})"
    | .delValue => s!"delValue({x.pp})"
    | _ => s!"op1({x.pp})"
  | _, .app2 o x y => match o with
    | .binop op _ => s!"({x.pp} {op.sym} {y.pp})"
    | .find => s!"find({x.pp}, {y.pp})"
    | .len => s!"len({x.pp}, {y.pp})"
    | .sfind => s!"select({x.pp}, {y.pp})"
    | .delAt => s!"delAt({x.pp}, {y.pp})"
    | .pushSlot => s!"pushSlot({x.pp}, {y.pp})"
    | .pop => s!"pop({x.pp}, {y.pp})"
    | .shrink => s!"shrink({x.pp}, {y.pp})"
    | .extend => s!"extend({x.pp}, {y.pp})"
    | .at _ => s!"{x.pp}[{y.pp}]"
    | .nextIn => s!"next({x.pp}, {y.pp})"
    | .read => s!"read({x.pp}, {y.pp})"
    | .mlen => s!"size({x.pp}, {y.pp})"
    | _ => s!"op2({x.pp}, {y.pp})"
  | _, .app3 o x y z => match o with
    | .ite => s!"(if({x.pp}) then {y.pp} else {z.pp})"
    | .save => s!"save({x.pp}, {y.pp}, {z.pp})"
    | .push => s!"push({x.pp}, {y.pp}, {z.pp})"
    | .atIn _ => s!"at({x.pp}, {y.pp}, {z.pp})"
    | .write => s!"write({x.pp}, {y.pp}, {z.pp})"
    | .saveIn => s!"saveIn({x.pp}, {y.pp}, {z.pp})"
  | _, .index _ q i => s!"{q.pp}[{i.pp}]"
  | _, .obsW q => s!"W({q.pp})"
  | _, .obsL q => s!"L({q.pp})"
  | _, .obsH q => s!"H({q.pp})"
  | _, .seq d a => s!"({d.pp}; {a.pp})"
  | _, .orElse a b => s!"orElse({a.pp}, {b.pp})"
  | _, .kite a b t e => s!"(if({a.pp} = {b.pp}) then {t.pp} else {e.pp})"
  | _, .err => "err"

/-- A formula, printed. -/
partial def LFml.pp : LFml C → String
  | .tt => "true"
  | .eq a b => s!"{a.pp} = {b.pp}"
  | .not φ => s!"!({φ.pp})"
  | .and φ ψ => s!"({φ.pp} & {ψ.pp})"
  | .imp φ ψ => s!"({φ.pp} -> {ψ.pp})"
  | .all k p φ => s!"(\\forall {p.toStr} pos({k}); {φ.pp})"

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
