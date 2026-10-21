import Solidity.Calculus.ReadWrite
import Solidity.Theory.Bridge.Denote

/-!
# What the closer knows of a run and of the symbols

The lemmas `sol_close`'s set `close_rw_s` (`Calculus/CloseScoped.lean`)
reads a scoped leaf with, below its term equations: weakest preconditions
(`Modality.wp`) over a result (`TRes`), a few facts of integers and
ledgers, and the typed symbols `Op0`–`Op3` (`Signature.lean`) read one
constructor at a time on the typed global part (`Close.Op2.eval_find`, …,
each its `casesOn` arm by `rfl`), from which the scoped set's term
equations follow.  The untyped interpreter's write-naming lemmas
(`Modality.wp_box_saveStorage`, …) went with `close_rw` at W10.5.1.
-/

namespace Solidity

open Semantics

/-! ## Weakest preconditions -/

/-- `P` of what `x` returns, or `m.onHalt` when it halts: under the box
`[ alice.age = 1; ] φ` holds of a state without `alice`, under the diamond
it does not. -/
def Modality.wp {α : Type} (m : Modality) (x : TRes α) (P : α → Prop) : Prop :=
  match x with
  | .ok a => P a
  | .error _ => m.onHalt

section WP

variable {α β : Type} {m : Modality}

/-- A run that returns: `uint x = 10;` leaves `x == 10` to check. -/
@[simp] theorem Modality.wp_ok {a : α} {P : α → Prop} : m.wp (.ok a) P ↔ P a := Iff.rfl

/-- `wp_ok` for `pure`. -/
@[simp] theorem Modality.wp_pure {a : α} {P : α → Prop} : m.wp (pure a) P ↔ P a := Iff.rfl

/-- A run that halts: `revert();` proves every box formula, no diamond one. -/
@[simp] theorem Modality.wp_error {e : THalt} {P : α → Prop} : m.wp (.error e) P ↔ m.onHalt :=
  Iff.rfl

/-- Under the box a halt is fine: `[ revert(); ] false`. -/
@[simp] theorem Modality.onHalt_box : Modality.box.onHalt = True := rfl

/-- Under the diamond it is not: `⟨ revert(); ⟩ true` fails. -/
@[simp] theorem Modality.onHalt_diamond : Modality.diamond.onHalt = False := rfl

/-- Sequencing: `y = x + 1` evaluates `x`, then adds, then range-checks, and
the postcondition is asked of the last. -/
theorem Modality.wp_bind {x : TRes α} {f : α → TRes β} {P : β → Prop} :
    m.wp (x >>= f) P ↔ m.wp x (fun a => m.wp (f a) P) := by
  cases x <;> exact Iff.rfl

/-- A range check: `y = x + 1` at `uint` returns `x + 1` when it is below
`2²⁵⁶`, and reverts otherwise. -/
theorem Modality.wp_ite {c : Prop} [Decidable c] {x y : TRes α} {P : α → Prop} :
    m.wp (if c then x else y) P ↔ (c → m.wp x P) ∧ (¬ c → m.wp y P) := by
  by_cases h : c <;> simp [h]

/-- The box, of a step nothing is known about: whatever it returns. -/
theorem Modality.wp_box {x : TRes α} {P : α → Prop} :
    Modality.box.wp x P ↔ ∀ a, x = .ok a → P a := by
  cases x <;> simp [Modality.wp, Modality.onHalt]

/-- The diamond: it returns, and what it returns satisfies `P`. -/
theorem Modality.wp_diamond {x : TRes α} {P : α → Prop} :
    Modality.diamond.wp x P ↔ ∃ a, x = .ok a ∧ P a := by
  cases x <;> simp [Modality.wp, Modality.onHalt]

end WP

namespace Close

/-! ## Values, operators, ledgers -/

/-- A bounds check returns nothing to name: `∀ u : Unit, …` is the one case. -/
theorem forall_unit {P : PUnit.{1} → Prop} : (∀ u, P u) ↔ P PUnit.unit :=
  ⟨fun h => h _, fun h u => by cases u; exact h⟩
/-- The same under the diamond. -/
theorem exists_unit {P : PUnit.{1} → Prop} : (∃ u, P u) ↔ P PUnit.unit :=
  ⟨fun ⟨u, h⟩ => by cases u; exact h, fun h => ⟨_, h⟩⟩
/-- `pure` in a run is `ok`. -/
theorem pure_eq_ok {α : Type} (a : α) : (pure a : TRes α) = .ok a := rfl
/-- A run followed by nothing is the run. -/
theorem bind_ok_right {α : Type} (x : TRes α) : (x >>= fun a => Except.ok a) = x := by
  cases x <;> rfl

/-- `12 & 10` on numerals: `Nat`'s `&&&`, which `Nat.reduceAnd` computes.  An
operand is a numeral or the cast of one, a result computed before. -/
theorem uintBitwise_ofNat (f : Nat → Nat → Nat) (a b : Nat) :
    uintBitwise f (no_index (OfNat.ofNat a)) (no_index (OfNat.ofNat b)) = ((f a b : Nat) : Int) :=
  rfl
theorem uintBitwise_ofNat_cast (f : Nat → Nat → Nat) (a b : Nat) :
    uintBitwise f (no_index (OfNat.ofNat a)) (b : Int) = ((f a b : Nat) : Int) := rfl
theorem uintBitwise_cast_ofNat (f : Nat → Nat → Nat) (a b : Nat) :
    uintBitwise f (a : Int) (no_index (OfNat.ofNat b)) = ((f a b : Nat) : Int) := rfl

/-- solkey's `binaryAndZeroRight`: `i & 0` is `0`. -/
theorem uintBitwise_and_zero_right (x : Int) : uintBitwise (· &&& ·) x 0 = 0 := by
  cases x <;> simp [uintBitwise, signedOf, wordOf]
/-- solkey's `binaryAndZeroLeft`: `0 & i` is `0`. -/
theorem uintBitwise_and_zero_left (x : Int) : uintBitwise (· &&& ·) 0 x = 0 := by
  cases x <;> simp [uintBitwise, signedOf, wordOf]
/-- solkey's `binaryAndOne`: `i & 1` is `i`'s parity, `i % 2` (solkey's
`\if(mod(i, 2) = 0) \then(0) \else(1)`; an `if` in a value slows `simp`). -/
theorem uintBitwise_and_one_right (x : Int) :
    uintBitwise (· &&& ·) x 1 = x % 2 := by
  have h1 : wordOf 1 = 1 := rfl
  cases x with
  | ofNat a => simp only [uintBitwise, Nat.and_one_is_mod, Int.ofNat_eq_coe]; omega
  | negSucc n =>
    simp only [uintBitwise, h1, Nat.and_one_is_mod, signedOf]
    simp only [wordOf]; split <;> omega
/-- solkey's `binaryAndOneLeft`: `1 & i` is `i`'s parity. -/
theorem uintBitwise_and_one_left (x : Int) :
    uintBitwise (· &&& ·) 1 x = x % 2 := by
  have h1 : wordOf 1 = 1 := rfl
  cases x with
  | ofNat a => simp only [uintBitwise, Nat.one_and_eq_mod_two, Int.ofNat_eq_coe]; omega
  | negSucc n =>
    have h1' : wordOf (Int.ofNat 1) = 1 := rfl
    simp only [uintBitwise, h1, h1', Nat.one_and_eq_mod_two, signedOf]
    simp only [wordOf]; split <;> omega
/-- solkey's `binaryAndIdentity`: `i & i` is `i`, at an `int256` (two's
complement reads a word back as the integer it was). -/
theorem uintBitwise_and_self (x : Int) (h : -57896044618658097711785492504343953926634992332820282019728792003956564819968 ≤ x) :
    uintBitwise (· &&& ·) x x = x := by
  cases x <;> simp only [uintBitwise, signedOf, wordOf, Nat.and_self] <;> split <;> omega

/-- solkey's `smod_geZero`, a non-positive dividend: its remainder is not
positive (`Int.tmod_nonneg` the other side). -/
theorem tmod_nonpos {a : Int} (b : Int) (h : a ≤ 0) : a.tmod b ≤ 0 := by
  have := Int.tmod_nonneg b (show 0 ≤ -a by omega)
  rw [Int.neg_tmod] at this
  omega

/-- A ledger entry after a payment: the entry of the ledger the payment chose. -/
theorem lookupBy_ite (c : Prop) [Decidable c] (k : PrimTy.uint.Denote) (l l' : Ledger) :
    lookupBy k (if c then l else l') = if c then lookupBy k l else lookupBy k l' := by
  split <;> rfl
/-- A ledger entry after a write: the written amount at that address, the old
one elsewhere. -/
theorem lookupBy_setBy_int (k k' : PrimTy.uint.Denote) (v : Int) (l : Ledger) :
    lookupBy k (setBy k' v l) = if k = k' then some v else lookupBy k l := by
  split
  · subst_vars; exact Semantics.lookupBy_setBy_self _ _ _
  · exact Semantics.lookupBy_setBy_ne ‹_› _ _

/-- Equal address observations select the same ledger entry. This is ordinary
function congruence through the address's range proof. -/
theorem lookupBy_uint_congr (a b : PrimTy.uint.Denote) (l : Ledger) (h : a.1 = b.1) :
    lookupBy a l = lookupBy b l := congrArg (fun k => lookupBy k l) (Subtype.ext h)

/-! ## The symbols, one at a time -/

section Ops

/-! The typed symbols (`Signature.lean`) on the typed global part `g`, one
constructor at a time: each is its `casesOn` arm, by `rfl`, so the kernel
reads no `match`.  An argument is an `Option` (a revert is `none`); no
symbol is `undef`, and none converts a value (`asInt`, `asBool`, `asRef`,
`toSVal`, `toMVal` are gone: a typed argument is at its type already). -/

variable {C : Contract} (g : State C [])

theorem Op0.eval_lit {p : PrimTy} (v : p.Denote) : Op0.eval g (.lit v) = some v := rfl
theorem Op0.eval_env (k : EnvKey) : Op0.eval g (.env k) = some (g.envVal k) := rfl
theorem Op0.eval_root (r : Name) {T : Ty} (h : C.rootType r = some T) :
    Op0.eval g (.root r h) = some (SRef.ofRoot r h) := rfl
theorem Op0.eval_storage : Op0.eval g .storage = some g.storage := rfl
theorem Op0.eval_memory : Op0.eval g .memory = some g.memT := rfl
theorem Op0.eval_mtSt : Op0.eval g .mtSt = some (Storage.init C) := rfl
theorem Op0.eval_zlit (n : Int) : Op0.eval g (.zlit n) = some n := rfl

theorem Op1.eval_unop (op : UnOp) {p : PrimTy} (h : op.accepts p = true)
    (x : Option p.Denote) : Op1.eval g (.unop op h) x = x.bind (op.evalT h) := rfl
theorem Op1.eval_net (x : Option PrimTy.uint.Denote) : Op1.eval g .net x =
    x.map fun n => (lookupBy n g.net).getD 0 := rfl
theorem Op1.eval_field {s f : Name} {T : Ty} (h : C.fieldType s f = some T)
    (x : Option (SRef C (.ref (.struct s)))) : Op1.eval g (.field h) x = x.map (·.field h) := rfl
theorem Op1.eval_next {E : Ty} (x : Option (SRef C (.ref (.array E)))) :
    Op1.eval g .next x = x.bind g.storage.nextT := rfl
theorem Op1.eval_sval {p : PrimTy} (x : Option p.Denote) :
    Op1.eval g .sval x = x.map .prim := rfl
theorem Op1.eval_mval {p : PrimTy} (x : Option p.Denote) : Op1.eval g .mval x = x := rfl
theorem Op1.eval_ref {R : RefTy} (x : Option Nat) : Op1.eval g (.ref (R := R)) x = x := rfl

theorem Op1.eval_delValue {p : PrimTy} (x : Option p.Denote) :
    Op1.eval g .delValue x = x.map fun _ => PrimTy.dflt p := rfl
theorem Op1.eval_newArr {R : RefTy} (h : R.newArrOk = true) (x : Option PrimTy.uint.Denote) :
    Op1.eval g (.newArr h) x = x.map fun n => newArrT R n h := rfl
theorem Op1.eval_alloc (R : RefTy) (h : (Ty.ref R).mapFree = true)
    (x : Option (Grown g.H (fun _ => Unit))) :
    Op1.eval g (.alloc R h) x = x.map fun m => (m.heap.allocDefault R h).val.id := rfl
theorem Op1.eval_mfield {s f : Name} {T : Ty} (h : C.fieldType s f = some T) (x : Option Nat) :
    Op1.eval g (.mfield h) x = x.map fun id => .field id h := rfl
theorem Op1.eval_addM (R : RefTy) (h : (Ty.ref R).mapFree = true)
    (x : Option (Grown g.H (fun _ => Unit))) :
    Op1.eval g (.addM R h) x = x.map fun m => m.then (m.heap.allocDefault R h) := rfl
theorem Op1.eval_wt (x : Option (Storage C)) : Op1.eval g .wt x = x.bind Storage.wtT := rfl
theorem Op1.eval_cleanTail (x : Option (Storage C)) :
    Op1.eval g .cleanTail x = x.bind Storage.cleanTailT := rfl
theorem Op1.eval_toInt (x : Option PrimTy.uint.Denote) :
    Op1.eval g .toInt x = x.map fun n => n.1 := rfl
theorem Op1.eval_select {s : Name} (r : Name) (h : C.rootType r = some (.ref (.struct s)))
    (x : Option (Storage C)) :
    Op1.eval g (.select r h) x = x.map fun st => Storage.selectT st h := rfl

theorem Op2.eval_binop (op : BinOp) {p : PrimTy} (h : op.accepts p = true)
    (x y : Option p.Denote) : Op2.eval g (.binop op h) x y = x.bind fun a => binopT op h a y := rfl
theorem Op2.eval_find {p : PrimTy} (x : Option (Storage C)) (y : Option (SRef C (.prim p))) :
    Op2.eval g .find x y =
      x.bind fun st => y.bind fun r => (st.find r).bind fun v => some v.view := rfl
theorem Op2.eval_sfind {T : Ty} (x : Option (Storage C)) (y : Option (SRef C T)) :
    Op2.eval g .sfind x y = x.bind fun st => y.bind fun r => st.find r := rfl
theorem Op2.eval_delAt {T : Ty} (x : Option (Storage C)) (y : Option (SRef C T)) :
    Op2.eval g .delAt x y = x.bind fun st => y.bind fun r => st.delete r := rfl
theorem Op2.eval_at {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    (x : Option (SRef C (.ref R))) (y : Option k.Denote) :
    Op2.eval g (.at it) x y = x.bind fun r => y.bind fun i => g.storage.atT it r i := rfl

theorem Op2.eval_len {E : Ty} (x : Option (Storage C)) (y : Option (SRef C (.ref (.array E)))) :
    Op2.eval g .len x y = x.bind fun st => y.bind fun r => st.len r := rfl
theorem Op2.eval_read {p : PrimTy} (x : Option (Grown g.H (fun _ => Unit)))
    (y : Option (MAddrT (.prim p))) :
    Op2.eval g .read x y = x.bind fun m => y.bind fun a => m.readT a := rfl
theorem Op2.eval_pushSlot {E : Ty} (x : Option (Storage C))
    (y : Option (SRef C (.ref (.array E)))) :
    Op2.eval g .pushSlot x y = x.bind fun st => y.bind fun r => st.push r some := rfl
theorem Op2.eval_pop {E : Ty} (x : Option (Storage C)) (y : Option (SRef C (.ref (.array E)))) :
    Op2.eval g .pop x y = x.bind fun st => y.bind fun r => st.pop false r := rfl
theorem Op2.eval_shrink {E : Ty} (x : Option (Storage C))
    (y : Option (SRef C (.ref (.array E)))) :
    Op2.eval g .shrink x y = x.bind fun st => y.bind fun r => st.pop true r := rfl
theorem Op2.eval_mat {R : RefTy} {E : Ty} (a : ArrTy R E) (x : Option Nat)
    (y : Option PrimTy.uint.Denote) :
    Op2.eval g (.mat a) x y = x.bind fun id => y.bind fun i => some (.index id a i) := rfl

theorem Op2.eval_extend {E : Ty} (x : Option (Storage C))
    (y : Option (SRef C (.ref (.array E)))) :
    Op2.eval g .extend x y = x.bind fun st => y.bind fun r => (st.pushPlace r).bind fun q => some q.1 :=
      rfl
theorem Op2.eval_nextIn {E : Ty} (x : Option (Storage C))
    (y : Option (SRef C (.ref (.array E)))) :
    Op2.eval g .nextIn x y = x.bind fun st => y.bind fun r => st.nextT r := rfl
theorem Op2.eval_mlen {E : Ty} (x : Option (Grown g.H (fun _ => Unit))) (y : Option Nat) :
    Op2.eval g (.mlen (E := E)) x y = x.bind fun m => y.bind fun id =>
      (HRef.ofId? m.H' (.array E) id).bind fun r => some (m.heap.lenU r) := rfl
theorem Op2.eval_hash {k : HashKind} {R : RefTy} (x : Option (Grown g.H (fun _ => Unit))) (y : Option Nat) :
    Op2.eval g (.hash (R := R) k) x y = x.bind fun m => y.bind fun id =>
      some (m.hashId k R id) := rfl
theorem Op2.eval_copyMem {R : RefTy} (x : Option (Grown g.H (fun _ => Unit))) (y : Option Nat) :
    Op2.eval g (.copyMem (R := R)) x y = x.bind fun m => y.bind fun id =>
      (HRef.ofId? m.H' R id).bind fun r =>
        some ( MVal.copyMToSt m.heap (T := .ref R) r) := rfl
theorem Op2.eval_iread {R : RefTy} (x : Option (Grown g.H (fun _ => Unit)))
    (y : Option (MAddrT (.ref R))) :
    Op2.eval g .iread x y = x.bind fun m => y.bind fun a =>
      (m.readT a).bind fun (r : HRef _ R) => some r.id := rfl
theorem Op2.eval_copy {R : RefTy} (h : (Ty.ref R).mapFree = true)
    (x : Option (Grown g.H (fun _ => Unit))) (y : Option (SVal (.ref R))) :
    Op2.eval g (.copy h) x y = x.bind fun m => y.bind fun v =>
      some (v.copyStToM m.heap h).val.id := rfl
theorem Op2.eval_copySt {T : Ty} (h : T.mapFree = true)
    (x : Option (Grown g.H (fun _ => Unit))) (y : Option (SVal T)) :
    Op2.eval g (.copySt h) x y = x.bind fun m => y.bind fun v =>
      some (m.then (v.copyStToM m.heap h)) := rfl

theorem Op3.eval_ite {p : PrimTy} (x : Option Bool) (y z : Option p.Denote) :
    Op3.eval g .ite x y z = x.bind fun c => cond c y z := rfl
theorem Op3.eval_save {T : Ty} (x : Option (Storage C)) (y : Option (SRef C T))
    (z : Option (SVal T)) :
    Op3.eval g .save x y z = x.bind fun st => y.bind fun r => z.bind fun v => st.write r v := rfl

theorem Op3.eval_push {E : Ty} (x : Option (Storage C)) (y : Option (SRef C (.ref (.array E))))
    (z : Option (SVal E)) :
    Op3.eval g .push x y z = x.bind fun st => y.bind fun r => st.push r fun _ => z.map SVal.strip :=
  rfl
theorem Op3.eval_write {T : Ty} (x : Option (Grown g.H (fun _ => Unit))) (y : Option (MAddrT T))
    (z : Option (MvT T)) :
    Op3.eval g .write x y z = x.bind fun m => y.bind fun a => z.bind fun v => m.writeT a v := rfl

theorem Op2.eval_zbin (op : BinOp) (h : op.zArith = true) (x y : Option Int) :
    Op2.eval g (.zbin op h) x y = x.bind fun a => y.bind fun b => some (op.evalZ a b) := rfl
theorem Op2.eval_zcmp (op : BinOp) (h : op.zCmp = true) (x y : Option Int) :
    Op2.eval g (.zcmp op h) x y = x.bind fun a => y.bind fun b => some (op.cmpZ a b) := rfl

end Ops

end Close

end Solidity
