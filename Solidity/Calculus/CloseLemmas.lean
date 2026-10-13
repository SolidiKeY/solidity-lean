import Solidity.Theory.StateWrites
import Solidity.Calculus.ReadWrite
import Solidity.Theory.Bridge.Denote

/-!
# What both closers know of the interpreter

The lemmas `sol_close` reads the interpreter with, shared by its two sets:
`close_rw` (`Calculus/Close.lean`, the interpreter's states and values) and
`close_rw_s` (`Calculus/CloseScoped.lean`, a scoped leaf's terms).  Each is about
`Semantics.State` and its operations, never about a formula or a term
language: weakest preconditions (`Modality.wp`, a write named with what is
known of its result), values read back, the operators; and the typed
symbols `Op0`–`Op3` (`Signature.lean`) read one constructor at a time on
the typed global part (`Close.Op2.eval_find`, …, each its `casesOn` arm by
`rfl`), from which the scoped set's term equations follow.

The untyped interpreter's names are written qualified (`Semantics.State`,
`Semantics.SVal`): `Signature.lean` brings the typed `State`/`SVal` into
`Solidity`, which a bare name resolves to first.
-/

namespace Solidity

open Semantics SemanticsProperties

/-! ## Weakest preconditions -/

/-- `P` of what `x` returns, or `m.onHalt` when it halts: under the box
`[ alice.age = 1; ] φ` holds of a state without `alice`, under the diamond
it does not. -/
def Modality.wp {α : Type} (m : Modality) (x : Res α) (P : α → Prop) : Prop :=
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
@[simp] theorem Modality.wp_error {e : Halt} {P : α → Prop} : m.wp (.error e) P ↔ m.onHalt :=
  Iff.rfl

/-- Under the box a halt is fine: `[ revert(); ] false`. -/
@[simp] theorem Modality.onHalt_box : Modality.box.onHalt = True := rfl

/-- Under the diamond it is not: `⟨ revert(); ⟩ true` fails. -/
@[simp] theorem Modality.onHalt_diamond : Modality.diamond.onHalt = False := rfl

/-- Sequencing: `y = x + 1` evaluates `x`, then adds, then range-checks, and
the postcondition is asked of the last. -/
theorem Modality.wp_bind {x : Res α} {f : α → Res β} {P : β → Prop} :
    m.wp (x >>= f) P ↔ m.wp x (fun a => m.wp (f a) P) := by
  cases x <;> exact Iff.rfl

/-- A range check: `y = x + 1` at `uint` returns `x + 1` when it is below
`2²⁵⁶`, and reverts otherwise. -/
theorem Modality.wp_ite {c : Prop} [Decidable c] {x y : Res α} {P : α → Prop} :
    m.wp (if c then x else y) P ↔ (c → m.wp x P) ∧ (¬ c → m.wp y P) := by
  by_cases h : c <;> simp [h]

/-- The box, of a step nothing is known about: whatever it returns. -/
theorem Modality.wp_box {x : Res α} {P : α → Prop} :
    Modality.box.wp x P ↔ ∀ a, x = .ok a → P a := by
  cases x <;> simp [Modality.wp, Modality.onHalt]

/-- The diamond: it returns, and what it returns satisfies `P`. -/
theorem Modality.wp_diamond {x : Res α} {P : α → Prop} :
    Modality.diamond.wp x P ↔ ∃ a, x = .ok a ∧ P a := by
  cases x <;> simp [Modality.wp, Modality.onHalt]

/-- **A storage write under the box**, named with what is known of its
result: in `[ alice.age = 10; bob = alice; ] bob.age == 10`, the state `τ`
after the first write reads `10` at `alice.age` and below it, reads as `σ`
does at `bob` and at `alice.account`, and has the locals, the heap and the
`net` ledger of `σ` (so a ledger read crosses it: `[ to.transfer(5); total =
1; ] net(to) = 2`). -/
theorem Modality.wp_box_saveStorage {σ : Semantics.State} {r : Name} {p : List Seg} {v :
    Semantics.SVal}
    {P : Semantics.State → Prop} :
    Modality.box.wp (σ.saveStorage r p v) P ↔
      ∀ τ, σ.saveStorage r p v = .ok τ → τ.findStorage r p = .ok v →
        (∀ q, Close.Prefix p q → τ.findStorage r q = v.find (Close.after p q)) →
        (∀ r' q, r' ≠ r ∨ Close.Diverge p q → τ.findStorage r' q = σ.findStorage r' q) →
        (∀ r' q k, r' ≠ r ∨ ¬ Close.Prefix p q → τ.checkIndex r' q k = σ.checkIndex r' q k) →
        (∀ q k, Close.Prefix p q → τ.checkIndex r q k = v.find (Close.after p q) >>= Close.idxOk k) →
        (∀ x, τ.getEnv x = σ.getEnv x) → (∀ a, readAddr τ a = readAddr σ a) →
        (∀ a, Close.readVal τ a = Close.readVal σ a) →
        τ.tx = σ.tx → τ.selfBalance = σ.selfBalance → τ.net = σ.net → P τ := by
  rw [Modality.wp_box]
  exact ⟨fun h τ hs _ _ _ _ _ _ _ _ _ _ _ => h τ hs, fun h τ hs =>
    h τ hs (State.findStorage_saveStorage_same hs)
      (fun _ hq => Close.findStorage_saveStorage_below hs hq)
      (fun _ _ hd => Close.findStorage_saveStorage_apart hs hd)
      (fun _ _ k hq => Close.checkIndex_saveStorage_apart k hs hq)
      (fun _ k hq => Close.checkIndex_saveStorage_below k hs hq)
      (Close.getEnv_saveStorage hs) (Close.readAddr_saveStorage hs)
      (fun a => by simp [Close.readVal, Close.readAddr_saveStorage hs])
      (Close.env_saveStorage hs).1 (Close.env_saveStorage hs).2
      (SemanticsProperties.State.saveStorage_frame hs).2.2.2.1⟩

/-- **A subtree read under the box**: in `[ bob = alice; ] bob.age ==
alice.age`, the tree `a` read at `alice` reads at `age` what the storage
reads at `alice.age`. -/
theorem Modality.wp_box_findStorage {σ : Semantics.State} {r : Name} {p : List Seg}
    {P : Semantics.SVal → Prop} :
    Modality.box.wp (σ.findStorage r p) P ↔
      ∀ a, σ.findStorage r p = .ok a → (∀ q, a.find q = σ.findStorage r (p ++ q)) → P a := by
  rw [Modality.wp_box]
  exact ⟨fun h a hs _ => h a hs, fun h a hs => h a hs (Close.find_findStorage hs)⟩

/-- **A memory write under the box**: after `m.age = 5;` the state reads `5`
at `m.age`, as before at every address apart from it, and has the storage
and the locals of the state before. -/
theorem Modality.wp_box_writeAddr {σ : Semantics.State} {mv : Semantics.MVal} {a : Addr} {P :
    Semantics.State → Prop} :
    Modality.box.wp (writeAddr σ mv a) P ↔
      ∀ τ, writeAddr σ mv a = .ok τ → readAddr τ a = .ok mv → Close.readVal τ a = mv.asValue →
        (∀ a', Close.Apart a a' → readAddr τ a' = readAddr σ a') →
        (∀ a', Close.Apart a a' → Close.readVal τ a' = Close.readVal σ a') →
        (∀ r q, τ.findStorage r q = σ.findStorage r q) →
        (∀ r q k, τ.checkIndex r q k = σ.checkIndex r q k) → (∀ x, τ.getEnv x = σ.getEnv x) →
        τ.tx = σ.tx → τ.selfBalance = σ.selfBalance → P τ := by
  rw [Modality.wp_box]
  refine ⟨fun h τ hs _ _ _ _ _ _ _ _ _ => h τ hs, fun h τ hs => ?_⟩
  obtain ⟨id, obj, rfl, hap⟩ := Close.writeAddr_setObj hs
  have hsame := Close.readAddr_writeAddr_same hs
  exact h _ hs hsame (by simp only [Close.readVal, hsame]; rfl) hap
    (fun a' ha => by simp [Close.readVal, hap a' ha]) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ => rfl) rfl rfl

/-- **A copy into memory under the box**: after `Person memory m = alice;`,
`m.age` reads what `alice.age` held; storage and locals are as before. -/
theorem Modality.wp_box_copyStToM {σ : Semantics.State} {v : Semantics.SVal} {P : Semantics.State ×
    Semantics.MVal → Prop} :
    Modality.box.wp (copyStToM σ v) P ↔
      ∀ τ mv, copyStToM σ v = .ok (τ, mv) →
        (∀ id f, mv = .ref id → f ≠ "length" →
          Close.readVal τ (.memoryField id f) = v.find [.field f] >>= SVal.asValue) →
        (∀ r q, τ.findStorage r q = σ.findStorage r q) →
        (∀ r q k, τ.checkIndex r q k = σ.checkIndex r q k) → (∀ x, τ.getEnv x = σ.getEnv x) →
        τ.tx = σ.tx → τ.selfBalance = σ.selfBalance → P (τ, mv) := by
  rw [Modality.wp_box]
  refine ⟨fun h τ mv hs _ _ _ _ _ _ => h _ hs, fun h ⟨τ, mv⟩ hs => ?_⟩
  obtain ⟨hst, hen⟩ := Close.copyStToM_frame' hs
  exact h τ mv hs (fun id f hid hf => by subst hid; exact Close.copyStToM_member hs hf) hst
    (Close.checkIndex_of_findStorage hst) hen (Close.env_copyStToM hs).1 (Close.env_copyStToM hs).2

/-- **A fresh memory object under the box**: `Person memory m;` binds `m` to
an object whose members read the defaults of `Person`'s. -/
theorem Modality.wp_box_allocDefault {σ : Semantics.State} {R : RefTy} {P : Semantics.State × Nat →
    Prop} :
    Modality.box.wp (allocDefault σ R) P ↔
      ∀ τ id, allocDefault σ R = .ok (τ, id) →
        (∀ f, f ≠ "length" →
          Close.readVal τ (.memoryField id f) =
            (defaultForRef R).find [.field f] >>= SVal.asValue) →
        (∀ r q, τ.findStorage r q = σ.findStorage r q) →
        (∀ r q k, τ.checkIndex r q k = σ.checkIndex r q k) → (∀ x, τ.getEnv x = σ.getEnv x) →
        τ.tx = σ.tx → τ.selfBalance = σ.selfBalance → P (τ, id) := by
  rw [Modality.wp_box]
  refine ⟨fun h τ id hs _ _ _ _ _ _ => h _ hs, fun h ⟨τ, id⟩ hs => ?_⟩
  have hc := Close.allocDefault_copy hs
  obtain ⟨hst, hen⟩ := Close.copyStToM_frame' hc
  exact h τ id hs (fun f hf => Close.copyStToM_member hc hf) hst
    (Close.checkIndex_of_findStorage hst) hen (Close.env_copyStToM hc).1 (Close.env_copyStToM hc).2

/-- **A copy out of memory under the box**: after `alice = m;`, `alice.age`
holds what `m.age` held. -/
theorem Modality.wp_box_copyMem {σ : Semantics.State} {id : Nat} {P : Semantics.SVal → Prop} :
    Modality.box.wp (copyMem σ (.ref id)) P ↔
      ∀ v, copyMem σ (.ref id) = .ok v →
        (∀ f, f ≠ "length" → v.find [.field f] =
          readAddr σ (.memoryField id f) >>= Close.copyLeaf σ id) → P v := by
  rw [Modality.wp_box]
  exact ⟨fun h v hs _ => h v hs, fun h v hs => h v hs (fun _ hf => Close.copyMem_member hs hf)⟩

/-- **A transfer under the box**: `to.transfer(5);` leaves the storage, the
locals, the heap, `msg.sender` and `address(this).balance` as they were, and
moves `5` on the ledger from `this` to `to` (`State.pay`). -/
theorem Modality.wp_box_transferAt {σ : Semantics.State} {addr amt : Int} {P : Semantics.State →
    Prop} :
    Modality.box.wp (transferAt σ addr amt) P ↔
      ∀ τ, transferAt σ addr amt = .ok τ →
        (∀ r q, τ.findStorage r q = σ.findStorage r q) →
        (∀ r q k, τ.checkIndex r q k = σ.checkIndex r q k) → (∀ x, τ.getEnv x = σ.getEnv x) →
        (∀ a, readAddr τ a = readAddr σ a) → (∀ a, Close.readVal τ a = Close.readVal σ a) →
        τ.tx = σ.tx → τ.selfBalance = σ.selfBalance →
        τ.net = (σ.pay addr amt).net → P τ := by
  rw [Modality.wp_box]
  refine ⟨fun h τ hs _ _ _ _ _ _ _ _ => h τ hs, fun h τ hs => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := Close.transferAt_frame hs
  obtain ⟨h₄, h₅, h₆⟩ := Close.transferAt_env hs
  exact h τ hs h₁ (Close.checkIndex_of_findStorage h₁) h₂ h₃ (fun a => by simp [Close.readVal, h₃])
    h₄ h₅ h₆

end WP

namespace Close

/-! ## Values, operators, ledgers -/

/-- An index read as an integer is one: `balances[k]` needs `k` a `uint`. -/
@[simp] theorem asInt_eq_ok {v : Value} {i : Int} : v.asInt = .ok i ↔ v = .int i := by
  cases v <;> simp [Value.asInt]
/-- A condition read as a boolean is one: `!flag` needs `flag` a `bool`. -/
theorem asBool_eq_ok {v : Value} {b : Bool} : v.asBool = .ok b ↔ v = .bool b := by
  cases v <;> simp [Value.asBool]
/-- A memory slot read as a reference holds one. -/
theorem asRef_eq_ok {mv : Semantics.MVal} {id : Nat} : mv.asRef = .ok id ↔ mv = .ref id := by
  cases mv <;> simp [MVal.asRef, pure, Except.pure]
/-- `alice.age = 10;` stores the word `10`. -/
@[simp] theorem toSVal_int (v : Int) : Value.toSVal (.int v) = .int v := rfl
/-- `flags[k] = true;` stores the word `true`. -/
@[simp] theorem toSVal_bool (b : Bool) : Value.toSVal (.bool b) = .bool b := rfl
/-- A value is stored in memory as the primitive it is: `m.age = 5;`. -/
theorem toMVal_eq (v : Value) : Value.toMVal v = .prim v := by
  cases v <;> rfl
/-- A stored value reads back as itself: `age = amount;` then `age` is
`amount`, whatever it holds. -/
theorem asValue_toSVal (v : Value) : (Value.toSVal v).asValue = .ok v := by
  cases v <;> rfl
/-- The same for a value stored in memory: `m.age = amount;`. -/
theorem asValue_toMVal (v : Value) : (Value.toMVal v).asValue = .ok v := by
  cases v <;> rfl
/-- Reading the word `10` gives `10`. -/
@[simp] theorem asValue_int (v : Int) : (SVal.int v).asValue = .ok (.int v) := rfl
/-- Reading the word `true` gives `true`. -/
@[simp] theorem asValue_bool (b : Bool) : (SVal.bool b).asValue = .ok (.bool b) := rfl
/-- A read that gives a word read one: `delete balances[a];` then leaves that
word's default. -/
theorem asValue_eq_ok {v : Semantics.SVal} {p : PrimVal} : v.asValue = .ok p ↔ v = .prim p := by
  rcases v with p' | _ | _ | _ <;> (try cases p') <;> cases p <;> simp [SVal.asValue]
/-- A memory slot holding `10` reads `10`. -/
theorem mval_asValue_prim (p : PrimVal) : (MVal.prim p).asValue = .ok p := by
  cases p <;> rfl
/-- A memory slot holding a reference reads no value. -/
theorem mval_asValue_ref (id : Nat) : (MVal.ref id).asValue = .error .undef := rfl
/-- A memory slot holding the object `3` references it. -/
theorem mval_asRef_ref (id : Nat) : (MVal.ref id).asRef = .ok id := rfl
/-- `delete alice.age;` leaves `0`. -/
@[simp] theorem defaultOf_int (v : Int) : (SVal.int v).defaultOf = .int 0 := rfl
/-- `delete flags[k];` leaves `false`. -/
@[simp] theorem defaultOf_bool (b : Bool) : (SVal.bool b).defaultOf = .bool false := rfl
/-- The index `1` of `values[1]` is the integer `1`. -/
@[simp] theorem asInt_int (v : Int) : Value.asInt (.int v) = .ok v := rfl
/-- The condition `true` is the boolean `true`. -/
theorem asBool_bool (b : Bool) : Value.asBool (.bool b) = .ok b := rfl
/-- A bounds check returns nothing to name: `∀ u : Unit, …` is the one case. -/
theorem forall_unit {P : PUnit.{1} → Prop} : (∀ u, P u) ↔ P PUnit.unit :=
  ⟨fun h => h _, fun h u => by cases u; exact h⟩
/-- The same under the diamond. -/
theorem exists_unit {P : PUnit.{1} → Prop} : (∃ u, P u) ↔ P PUnit.unit :=
  ⟨fun ⟨u, h⟩ => by cases u; exact h, fun h => ⟨_, h⟩⟩
/-- `pure` in a run is `ok`. -/
theorem pure_eq_ok {α : Type} (a : α) : (pure a : Res α) = .ok a := rfl
/-- A run followed by nothing is the run. -/
theorem bind_ok_right {α : Type} (x : Res α) : (x >>= fun a => Except.ok a) = x := by
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

/-- Every operator but `&&` and `||` reads both operands: `x + 1` reads `x`,
then `1`, adds, and range-checks the sum. -/
theorem evalBinop_strict {op : BinOp} (h₁ : op ≠ .and) (h₂ : op ≠ .or) (p : PrimTy) (lv : Value)
    (b : Res Value) :
    evalBinop op p lv b =
      b >>= fun rv => applyBinOp op lv rv >>= checkArith (op.retTy (.prim p)) := by
  cases op <;> first | exact absurd rfl h₁ | exact absurd rfl h₂ | rfl

/-- `a && b` reads `b` only when `a` is not `false`. -/
theorem evalBinop_and (p : PrimTy) (lv : Value) (b : Res Value) :
    evalBinop .and p lv b = if lv = .bool false then .ok (.bool false) else
      b >>= fun rv => applyBinOp .and lv rv >>= checkArith (BinOp.and.retTy (.prim p)) := by
  unfold evalBinop
  split <;> simp_all [pure, Except.pure]

/-- `a || b` reads `b` only when `a` is not `true`. -/
theorem evalBinop_or (p : PrimTy) (lv : Value) (b : Res Value) :
    evalBinop .or p lv b = if lv = .bool true then .ok (.bool true) else
      b >>= fun rv => applyBinOp .or lv rv >>= checkArith (BinOp.or.retTy (.prim p)) := by
  unfold evalBinop
  split <;> simp_all [pure, Except.pure]

/-- `c ? a : b` on a condition that is `true`, `false`, or not a boolean. -/
theorem pickBranch_eq (cv : Value) (t e : Res Value) :
    pickBranch cv t e =
      if cv = .bool true then t else if cv = .bool false then e else .error .undef := by
  cases cv with
  | int _ => rfl
  | bool b => cases b <;> rfl

/-- A ledger entry after a payment: the entry of the ledger the payment chose. -/
theorem lookupBy_ite (c : Prop) [Decidable c] (k : Int) (l l' : List (Int × Int)) :
    lookupBy k (if c then l else l') = if c then lookupBy k l else lookupBy k l' := by
  split <;> rfl
/-- A ledger entry after a write: the written amount at that address, the old
one elsewhere. -/
theorem lookupBy_setBy_int (k k' v : Int) (l : List (Int × Int)) :
    lookupBy k (setBy k' v l) = if k = k' then some v else lookupBy k l := by
  split
  · subst_vars; exact SemanticsProperties.lookupBy_setBy_self _ _ _
  · exact SemanticsProperties.lookupBy_setBy_ne ‹_› _ _

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
    (x : Option p.Denote) : Op1.eval g (.unop op h) x = x.bind op.evalT := rfl
theorem Op1.eval_net (x : Option PrimTy.uint.Denote) : Op1.eval g .net x =
    x.map fun n => (lookupBy n.1 g.net).getD 0 := rfl
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
theorem Op1.eval_toInt (x : Option PrimTy.uint.Denote) :
    Op1.eval g .toInt x = x.map fun n => n.1 := rfl
theorem Op1.eval_select {s : Name} (r : Name) (h : C.rootType r = some (.ref (.struct s)))
    (x : Option (Storage C)) :
    Op1.eval g (.select r h) x = x.map fun st => Storage.selectT st h := rfl

theorem Op2.eval_binop (op : BinOp) {p : PrimTy} (h : op.accepts p = true)
    (x y : Option p.Denote) : Op2.eval g (.binop op h) x y = x.bind fun a => binopT op a y := rfl
theorem Op2.eval_find {p : PrimTy} (x : Option (Storage C)) (y : Option (SRef C (.prim p))) :
    Op2.eval g .find x y =
      x.bind fun st => y.bind fun r => (st.find r).bind fun v => some v.view := rfl
theorem Op2.eval_sfind {T : Ty} (x : Option (Storage C)) (y : Option (SRef C T)) :
    Op2.eval g .sfind x y = x.bind fun st => y.bind fun r => st.find r := rfl
theorem Op2.eval_delAt {T : Ty} (x : Option (Storage C)) (y : Option (SRef C T)) :
    Op2.eval g .delAt x y = x.bind fun st => y.bind fun r => st.delete r := rfl
theorem Op2.eval_at {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    (x : Option (SRef C (.ref R))) (y : Option k.keyTy.Denote) :
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
    Op2.eval g (.mat a) x y = x.bind fun id => y.bind fun i => some (.index id a i.1) := rfl

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
