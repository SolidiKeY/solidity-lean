import Solidity.Calculus.Notation
import Solidity.Calculus.ReadWrite
import Solidity.Theory.Bridge.Denote

/-!
# Closing the first-order goal: `sol_close`

`sol_symex` leaves `{U₁} … {Uₙ} φ` with no modality in it.  Its updates are
not rewritten away, as mini-solkey's `Ch14_Updates` does: a term here *is* a
call of the interpreter (`Term.eval`, `STerm.eval`), so applying an update
in an arbitrary state `σ` is running it, and what remains is a statement
about what `saveStorage`, `findStorage`, `readAddr` and `getEnv` return on a
`σ` nobody knows.  `sol_close` proves that statement with one contextual
`simp` over the `close_rw` set, then `omega` or `grind` for the arithmetic.

**Weakest preconditions.**  `Modality.wp m x P` is `P` of what `x` returns,
or `m.onHalt` when it halts; `Modality.after` is its instance at `State`.
Pushed through the binds of the evaluators (`Modality.wp_bind`, and one
equation per constructor below), it turns the goal into a nest of `∀ τ,
x = .ok τ → …` (the box) or `∃ τ, x = .ok τ ∧ …` (the diamond).  A
`split` on the unfolded `match`es does not get there: it splits the
outermost one only, and leaves the evaluator's inner matches in
hypotheses.

**Read after write.**  Under the box, a write is named on the spot, together
with what `ReadWrite.lean` knows of the state it returns: a storage write
(`Modality.wp_box_saveStorage`) reads back at and below the path written
and as before apart from it, a memory write (`wp_box_writeAddr`) likewise
at an address, a copy (`wp_box_copyStToM`, `wp_box_copyMem`) member by
member, and each leaves the other components alone.  A read of a subtree
(`wp_box_findStorage`) is named with the reads below it, which is what
settles a read above a write.  The `simp` is contextual, so every such
fact rewrites what follows it; the apartness of concrete paths is decided
by computation, that of symbolic keys (`balances[k]`, `balances[j]`) by a
hypothesis `k != j` of the formula or a branch.  Every step is a lemma or a
hypothesis: nothing evaluated is trusted, the kernel checks the proof.

What does not close, and why:

* a write under the diamond: `⊨` quantifies over every state, including
  those without `alice`, where `alice.age = 1;` is stuck, so
  `⟨ alice.age = 1; ⟩ true` is not valid.  Write the box, or put the
  well-formedness of the storage in the premise;
* two symbolic keys the formula does not tell apart: there is no case
  split on `k = j`, so `[ balances[k] = 5; balances[j] = 6; ] balances[k] == 5`
  stays open (it is false at `k = j`);
* two memory objects: nothing says that two allocations are different
  objects, since `⊨` includes states whose heap already holds an object at
  `nextId`;
* a read of an array a push wrote, the array known only by its shape:
  `[ uint n = values.length; values.push(42); ] values.length == n + 1`
  stays open, since the push's write is left as `saveStorage … = .ok τ`
  with none of the facts `wp_box_saveStorage` names
  (`Examples/CallOperands.lean` pins it open, and writes its push rows as
  chains for this);
* a default read out of a fresh memory object (`Person memory m;
  uint x = m.age;`): the default of a struct type is a well-founded
  definition (`defaultForTy`) that `simp` does not unfold;
* the ledger a `transfer` books: no term reads `net`, so what is observable
  of it is its frame — a write before it reads the same after — and the
  funds it spends, `address(this).balance`, `5` less after
  `to.transfer(5);` (`Modality.wp_box_transferAt`).
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

/-- `Modality.after` is `wp` at `State`: `⟨ x = 1; ⟩ x == 1` holds where
running `x = 1;` returns a state with `x == 1`. -/
theorem Modality.after_eq_wp (p : State → Prop) (r : Res State) : m.after p r = m.wp r p := by
  cases r <;> rfl

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
does at `bob` and at `alice.account`, and has the locals and the heap of
`σ`. -/
theorem Modality.wp_box_saveStorage {σ : State} {r : Name} {p : List Seg} {v : SVal}
    {P : State → Prop} :
    Modality.box.wp (σ.saveStorage r p v) P ↔
      ∀ τ, σ.saveStorage r p v = .ok τ → τ.findStorage r p = .ok v →
        (∀ q, Close.Prefix p q → τ.findStorage r q = v.find (Close.after p q)) →
        (∀ r' q, r' ≠ r ∨ Close.Diverge p q → τ.findStorage r' q = σ.findStorage r' q) →
        (∀ r' q k, r' ≠ r ∨ ¬ Close.Prefix p q → τ.checkIndex r' q k = σ.checkIndex r' q k) →
        (∀ q k, Close.Prefix p q → τ.checkIndex r q k = v.find (Close.after p q) >>= Close.idxOk k) →
        (∀ x, τ.getEnv x = σ.getEnv x) → (∀ a, readAddr τ a = readAddr σ a) →
        (∀ a, Close.readVal τ a = Close.readVal σ a) →
        τ.tx = σ.tx → τ.selfBalance = σ.selfBalance → P τ := by
  rw [Modality.wp_box]
  exact ⟨fun h τ hs _ _ _ _ _ _ _ _ _ _ => h τ hs, fun h τ hs =>
    h τ hs (State.findStorage_saveStorage_same hs)
      (fun _ hq => Close.findStorage_saveStorage_below hs hq)
      (fun _ _ hd => Close.findStorage_saveStorage_apart hs hd)
      (fun _ _ k hq => Close.checkIndex_saveStorage_apart k hs hq)
      (fun _ k hq => Close.checkIndex_saveStorage_below k hs hq)
      (Close.getEnv_saveStorage hs) (Close.readAddr_saveStorage hs)
      (fun a => by simp [Close.readVal, Close.readAddr_saveStorage hs])
      (Close.env_saveStorage hs).1 (Close.env_saveStorage hs).2⟩

/-- **A subtree read under the box**: in `[ bob = alice; ] bob.age ==
alice.age`, the tree `a` read at `alice` reads at `age` what the storage
reads at `alice.age`. -/
theorem Modality.wp_box_findStorage {σ : State} {r : Name} {p : List Seg}
    {P : SVal → Prop} :
    Modality.box.wp (σ.findStorage r p) P ↔
      ∀ a, σ.findStorage r p = .ok a → (∀ q, a.find q = σ.findStorage r (p ++ q)) → P a := by
  rw [Modality.wp_box]
  exact ⟨fun h a hs _ => h a hs, fun h a hs => h a hs (Close.find_findStorage hs)⟩

/-- **A memory write under the box**: after `m.age = 5;` the state reads `5`
at `m.age`, as before at every address apart from it, and has the storage
and the locals of the state before. -/
theorem Modality.wp_box_writeAddr {σ : State} {mv : MVal} {a : Addr} {P : State → Prop} :
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
theorem Modality.wp_box_copyStToM {σ : State} {v : SVal} {P : State × MVal → Prop} :
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
theorem Modality.wp_box_allocDefault {σ : State} {R : RefTy} {P : State × Nat → Prop} :
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
theorem Modality.wp_box_copyMem {σ : State} {id : Nat} {P : SVal → Prop} :
    Modality.box.wp (copyMem σ (.ref id)) P ↔
      ∀ v, copyMem σ (.ref id) = .ok v →
        (∀ f, f ≠ "length" → v.find [.field f] =
          readAddr σ (.memoryField id f) >>= Close.copyLeaf σ id) → P v := by
  rw [Modality.wp_box]
  exact ⟨fun h v hs _ => h v hs, fun h v hs => h v hs (fun _ hf => Close.copyMem_member hs hf)⟩

/-- **A transfer under the box**: `to.transfer(5);` leaves the storage, the
locals, the heap and `msg.sender` as they were, and takes `5` off
`address(this).balance`. -/
theorem Modality.wp_box_transferAt {σ : State} {addr amt : Int} {P : State → Prop} :
    Modality.box.wp (transferAt σ addr amt) P ↔
      ∀ τ, transferAt σ addr amt = .ok τ →
        (∀ r q, τ.findStorage r q = σ.findStorage r q) →
        (∀ r q k, τ.checkIndex r q k = σ.checkIndex r q k) → (∀ x, τ.getEnv x = σ.getEnv x) →
        (∀ a, readAddr τ a = readAddr σ a) → (∀ a, Close.readVal τ a = Close.readVal σ a) →
        τ.tx = σ.tx → τ.selfBalance = σ.selfBalance - amt → P τ := by
  rw [Modality.wp_box]
  refine ⟨fun h τ hs _ _ _ _ _ _ _ => h τ hs, fun h τ hs => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := Close.transferAt_frame hs
  exact h τ hs h₁ (Close.checkIndex_of_findStorage h₁) h₂ h₃ (fun a => by simp [Close.readVal, h₃])
    (Close.transferAt_env hs).1 (Close.transferAt_env hs).2

end WP

namespace Close

/-! ## Evaluation, one constructor at a time

The evaluators' own equations end in `match`es on a binding or a pair,
which `simp` cannot see through while the scrutinee is unknown.  These
restate them as binds of named functions, so that `Modality.wp_bind`
applies and the scrutinee is named first.  A read of memory stays whole
(`readVal`), since what is known of it is known of the value. -/

/-- `oldNet` bound to a ledger reads it. -/
@[simp] theorem bindingLedger_ledger (l : List (Int × Int)) :
    bindingLedger (.ledger l) = .ok l := rfl

/-- `old` bound to a storage reads it. -/
@[simp] theorem bindingStore_store (st : List (Name × SVal)) :
    bindingStore (.store st) = .ok st := rfl

/-- `x` bound to `10` reads `10`. -/
@[simp] theorem bindingVal_val (v : Value) : bindingVal (.val v) = .ok v := rfl
/-- `p` bound to `alice.account` reads that path. -/
@[simp] theorem bindingPath_spath (r : Name) (segs : List Seg) :
    bindingPath (.spath r segs) = .ok (r, segs) := rfl
/-- `m` bound to the object `3` reads `3`. -/
theorem bindingRef_mref (id : Nat) : bindingRef (.mref id) = .ok id := rfl
/-- A local read as a value was bound to one: `a == 1` says `a` holds `1`. -/
@[simp] theorem bindingVal_eq_ok {b : Binding} {v : Value} :
    bindingVal b = .ok v ↔ b = .val v := by
  cases b <;> simp [bindingVal]
/-- A local read as an object was bound to one. -/
theorem bindingRef_eq_ok {b : Binding} {id : Nat} :
    bindingRef b = .ok id ↔ b = .mref id := by
  cases b <;> simp [bindingRef]
/-- An index read as an integer is one: `balances[k]` needs `k` a `uint`. -/
@[simp] theorem asInt_eq_ok {v : Value} {i : Int} : v.asInt = .ok i ↔ v = .int i := by
  cases v <;> simp [Value.asInt]
/-- A condition read as a boolean is one: `!flag` needs `flag` a `bool`. -/
theorem asBool_eq_ok {v : Value} {b : Bool} : v.asBool = .ok b ↔ v = .bool b := by
  cases v <;> simp [Value.asBool]
/-- A memory slot read as a reference holds one. -/
theorem asRef_eq_ok {mv : MVal} {id : Nat} : mv.asRef = .ok id ↔ mv = .ref id := by
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
theorem asValue_eq_ok {v : SVal} {p : PrimVal} : v.asValue = .ok p ↔ v = .prim p := by
  rcases v with p' | _ | _ | _ <;> (try cases p') <;> cases p <;> simp [SVal.asValue]
/-- A memory slot holding `10` reads `10`. -/
theorem mval_asValue_prim (p : PrimVal) : (MVal.prim p).asValue = .ok p := by
  cases p <;> rfl
/-- A memory slot holding a reference reads no value. -/
theorem mval_asValue_ref (id : Nat) : (MVal.ref id).asValue = .error .stuck := rfl
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

/-- `p.age`, with `p` an alias, is the path `p` holds, then `age`. -/
theorem aliasPath_eq (σ : State) (x : Var) : aliasPath σ x = σ.getEnv x >>= bindingPath := rfl

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
      if cv = .bool true then t else if cv = .bool false then e else .error .stuck := by
  cases cv with
  | int _ => rfl
  | bool b => cases b <;> rfl

section Eval

variable {C : Contract} (σ : State)

/-- `10` is `10`. -/
theorem Term.eval_lit (v : Value) : (Term.lit v : Term C).eval σ = .ok v := rfl
/-- `x` is what `x` is bound to. -/
theorem Term.eval_pv (x : Var) : (Term.pv x : Term C).eval σ = σ.getEnv x >>= bindingVal := rfl
/-- `x + 1`: `x`, then the operator on `1`. -/
theorem Term.eval_binop (op : BinOp) (p : PrimTy) (a b : Term C) : (Term.binop op p a b).eval σ =
    a.eval σ >>= fun x => evalBinop op p x (b.eval σ) := rfl
/-- `-x`, `!flag`: the operand, the operator, the range check. -/
theorem Term.eval_unop (op : UnOp) (p : PrimTy) (a : Term C) : (Term.unop op p a).eval σ =
    a.eval σ >>= fun x => applyUnOp op x >>= unopCheck op p := rfl
/-- `find(storage, alice.age)`: the storage, the path, the word there. -/
theorem Term.eval_find (s : STerm C) (p : PTerm C) : (Term.find s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs => τ.findStorage rs.1 rs.2 >>= SVal.asValue := rfl
/-- `values.length`: the array there, counted. -/
theorem Term.eval_len (s : STerm C) (p : PTerm C) : (Term.len s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs => τ.findStorage rs.1 rs.2 >>= arrLen := by
  simp only [Term.eval, bind, Except.bind]
  cases s.eval σ <;> try rfl
  all_goals cases p.eval σ <;> try rfl
  all_goals exact arrayLen_eq _ _ _
/-- `read(memory, m.age)`: the memory, the address, the value there. -/
theorem Term.eval_read (m : MTerm C) (a : MAddr C) : (Term.read m a).eval σ =
    m.eval σ >>= fun τ => a.eval σ >>= fun addr => readVal τ addr := rfl
/-- `c ? a : b`: the condition, then the branch it picks. -/
theorem Term.eval_ite (c a b : Term C) : (Term.ite c a b).eval σ =
    c.eval σ >>= fun cv => pickBranch cv (a.eval σ) (b.eval σ) := rfl
/-- `msg.sender` is the transaction's, `address(this).balance` the funds. -/
theorem Term.eval_env (k : EnvKey) :
    (Term.env k : Term C).eval σ = .ok (.int (σ.envVal k)) := rfl
/-- `net(a)`: the address, then the ledger's entry for it. -/
theorem Term.eval_net (a : Term C) : (Term.net a).eval σ =
    a.eval σ >>= Value.asInt >>= fun n => .ok (.int (σ.getNet n)) := by
  simp only [Term.eval, bind, Except.bind]
  cases a.eval σ <;> rfl
/-- `net(oldNet, a)`: the ledger `oldNet` holds, then its entry for the address. -/
theorem Term.eval_netOf (x : Var) (a : Term C) : (Term.netOf x a).eval σ =
    σ.getEnv x >>= bindingLedger >>= fun l => a.eval σ >>= Value.asInt >>= fun n =>
      .ok (.int ((lookupBy n l).getD 0)) := by
  simp only [Term.eval, bind, Except.bind]
  cases σ.getEnv x with
  | error _ => rfl
  | ok b =>
    cases b <;> try rfl
    cases a.eval σ <;> rfl
/-- `alice` is the root `alice`. -/
theorem PTerm.eval_root (r : Name) : (PTerm.root r : PTerm C).eval σ = .ok (r, []) := rfl
/-- `p`, an alias, is the path it holds. -/
theorem PTerm.eval_pv (x : Var) : (PTerm.pv x : PTerm C).eval σ = σ.getEnv x >>= bindingPath :=
  aliasPath_eq σ x
/-- `alice.age` is `alice`, then `age`. -/
theorem PTerm.eval_field (p : PTerm C) (f : Name) : (PTerm.field p f).eval σ =
    p.eval σ >>= fun rs => .ok (rs.1, rs.2 ++ [.field f]) := rfl
/-- `balances[k]` is `balances`, then the integer `k` holds, checked against
the array's length where the receiver is one. -/
theorem PTerm.eval_at (p : PTerm C) (i : Term C) : (PTerm.at p i).eval σ =
    p.eval σ >>= fun rs => i.eval σ >>= Value.asInt >>= fun k =>
      σ.checkIndex rs.1 rs.2 k >>= fun _ => .ok (rs.1, rs.2 ++ [.at k]) := by
  simp only [PTerm.eval, bind, Except.bind]
  cases p.eval σ <;> try rfl
  cases i.eval σ <;> rfl
/-- `values[values.length]`: the slot one past the end. -/
theorem PTerm.eval_next (p : PTerm C) : (PTerm.next p).eval σ =
    p.eval σ >>= fun rs => σ.findStorage rs.1 rs.2 >>= Close.pastEnd rs := by
  simp only [PTerm.eval, bind, Except.bind]
  cases p.eval σ <;> rfl
/-- `storage` is the storage of the state it is read in. -/
theorem STerm.eval_storage : (STerm.storage : STerm C).eval σ = .ok σ := rfl
/-- `old` is the storage it was bound to, in the state it is read in. -/
theorem STerm.eval_pv (x : Var) : (STerm.pv x : STerm C).eval σ =
    σ.getEnv x >>= bindingStore >>= fun st => .ok { σ with storage := st } := by
  simp only [STerm.eval, bind, Except.bind]
  cases σ.getEnv x with
  | error _ => rfl
  | ok b => cases b <;> rfl
/-- `save(storage, alice.age, 10)`: the value, the storage, the path, the
write. -/
theorem STerm.eval_save (s : STerm C) (p : PTerm C) (t : Term C) :
    (STerm.save s p (.val t)).eval σ =
    t.eval σ >>= fun x => s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.saveStorage rs.1 rs.2 x.toSVal := by
  simp only [STerm.eval, SValT.eval, bind_assoc, pure_bind, State.writeStorage_toSVal]
/-- `save(storage, alice, find(storage, bob))`: `bob`'s tree laid over
`alice`'s (`SVal.overlay`). -/
theorem STerm.eval_save_find (s s' : STerm C) (p p' : PTerm C) :
    (STerm.save s p (.find s' p')).eval σ =
    (SValT.find s' p').eval σ >>= fun sv => s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= fun cur => τ.saveStorage rs.1 rs.2 (cur.overlay sv) := by
  simp only [STerm.eval, Close.writeStorage_eq]
/-- `save(storage, alice, copyMem(mtSt, memory, m))`: the memory object laid
over `alice`'s tree. -/
theorem STerm.eval_save_copyMem (s : STerm C) (p : PTerm C) (m : MTerm C) (i : ITerm C) :
    (STerm.save s p (.copyMem m i)).eval σ =
    (SValT.copyMem m i).eval σ >>= fun sv => s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= fun cur => τ.saveStorage rs.1 rs.2 (cur.overlay sv) := by
  simp only [STerm.eval, Close.writeStorage_eq]
/-- `delAt(storage, alice.age)`: the word there, reset to its default. -/
theorem STerm.eval_delAt (s : STerm C) (p : PTerm C) : (STerm.delAt s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs => τ.findStorage rs.1 rs.2 >>= fun cur =>
      τ.saveStorage rs.1 rs.2 cur.defaultOf := rfl
/-- `values.push(5)`: the array, then the array one longer written back. -/
theorem STerm.eval_push (s : STerm C) (p : PTerm C) (v : SValT C) : (STerm.push s p v).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>=
        pushOn τ .uint rs.1 rs.2 (fun _ => v.eval σ >>= fun sv => pure sv.strip) := by
  simp only [STerm.eval, bind, Except.bind]
  cases s.eval σ <;> try rfl
  all_goals cases p.eval σ <;> try rfl
  all_goals exact pushAt_eq _ _ _ _ _
/-- `persons.push()`: the recycled or default slot appended. -/
theorem STerm.eval_pushSlot (s : STerm C) (p : PTerm C) (E : Ty) :
    (STerm.pushSlot s p E).eval σ = s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= pushOn τ E rs.1 rs.2 pure := by
  simp only [STerm.eval, bind, Except.bind]
  cases s.eval σ <;> try rfl
  all_goals cases p.eval σ <;> try rfl
  all_goals exact pushAt_eq _ _ _ _ _
/-- `values.pop()`: the array, then the array one shorter written back. -/
theorem STerm.eval_pop (s : STerm C) (p : PTerm C) : (STerm.pop s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= popOn τ false rs.1 rs.2 := by
  simp only [STerm.eval, bind, Except.bind]
  cases s.eval σ <;> try rfl
  all_goals cases p.eval σ <;> try rfl
  all_goals exact popAt_eq _ _ _ _
/-- `m.pop()` on an array of mappings: the array one shorter, the element
kept. -/
theorem STerm.eval_shrink (s : STerm C) (p : PTerm C) : (STerm.shrink s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= popOn τ true rs.1 rs.2 := by
  simp only [STerm.eval, bind, Except.bind]
  cases s.eval σ <;> try rfl
  all_goals cases p.eval σ <;> try rfl
  all_goals exact popAt_eq _ _ _ _
/-- The `10` of `alice.age = 10;`, as a word to store. -/
theorem SValT.eval_val (t : Term C) : (SValT.val t).eval σ = t.eval σ >>= fun v => .ok v.toSVal :=
  rfl
/-- The `bob` of `alice = bob;`: the subtree read there. -/
theorem SValT.eval_find (s : STerm C) (p : PTerm C) : (SValT.find s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs => τ.findStorage rs.1 rs.2 := rfl
/-- The `m` of `alice = m;`: the memory object, copied out. -/
theorem SValT.eval_copyMem (m : MTerm C) (i : ITerm C) : (SValT.copyMem m i).eval σ =
    m.eval σ >>= fun τ => i.eval σ >>= fun id => copyMem τ (.ref id) := rfl
/-- `m`, a memory local, is the object it holds. -/
theorem ITerm.eval_pv (x : Var) : (ITerm.pv x : ITerm C).eval σ = σ.getEnv x >>= bindingRef :=
  rfl
/-- `m.account`, a reference held in memory. -/
theorem ITerm.eval_read (m : MTerm C) (a : MAddr C) : (ITerm.read m a).eval σ =
    m.eval σ >>= fun τ => a.eval σ >>= fun addr => readAddr τ addr >>= MVal.asRef := rfl
/-- `freshId(addM(memory))`: the object a default allocation takes. -/
theorem ITerm.eval_alloc (m : MTerm C) (R : RefTy) : (ITerm.alloc m R).eval σ =
    m.eval σ >>= fun τ => allocDefault τ R >>= fun r => .ok r.2 := rfl
/-- `freshId(copySt(memory, alice))`: the object a copy takes. -/
theorem ITerm.eval_copy (m : MTerm C) (v : SValT C) : (ITerm.copy m v).eval σ =
    v.eval σ >>= fun sv => m.eval σ >>= fun τ => copyStToM τ sv >>= fun r => r.2.asRef := rfl
/-- `m.age` is the member `age` of the object `m` holds. -/
theorem MAddr.eval_field (i : ITerm C) (f : Name) : (MAddr.field i f).eval σ =
    i.eval σ >>= fun id => .ok (.memoryField id f) := rfl
/-- `xs[k]` is the element `k` of the object `xs` holds. -/
theorem MAddr.eval_at (i : ITerm C) (k : Term C) : (MAddr.at i k).eval σ =
    i.eval σ >>= fun id => k.eval σ >>= Value.asInt >>= fun j => .ok (.memoryIndex id j) := by
  simp only [MAddr.eval, bind, Except.bind]
  cases i.eval σ <;> try rfl
  cases k.eval σ <;> rfl
/-- `memory` is the memory of the state it is read in. -/
theorem MTerm.eval_memory : (MTerm.memory : MTerm C).eval σ = .ok σ := rfl
/-- `write(memory, m.age, 5)`: the value, the memory, the address, the write. -/
theorem MTerm.eval_write (m : MTerm C) (a : MAddr C) (v : MValT C) : (MTerm.write m a v).eval σ =
    v.eval σ >>= fun mv => m.eval σ >>= fun τ => a.eval σ >>= fun addr => writeAddr τ mv addr :=
  rfl
/-- `addM(memory)`: the memory with a default object allocated. -/
theorem MTerm.eval_addM (m : MTerm C) (R : RefTy) : (MTerm.addM m R).eval σ =
    m.eval σ >>= fun τ => allocDefault τ R >>= fun r => .ok r.1 := rfl
/-- `copySt(memory, alice)`: the memory with a copy of `alice` in it. -/
theorem MTerm.eval_copySt (m : MTerm C) (v : SValT C) : (MTerm.copySt m v).eval σ =
    v.eval σ >>= fun sv => m.eval σ >>= fun τ => copyStToM τ sv >>= fun r => .ok r.1 := rfl
/-- The `5` of `m.age = 5;`, as a memory value. -/
theorem MValT.eval_val (t : Term C) : (MValT.val t).eval σ = t.eval σ >>= fun v => .ok v.toMVal :=
  rfl
/-- The `n` of `m.account = n;`: a reference. -/
theorem MValT.eval_ref (i : ITerm C) :
    (MValT.ref i).eval σ = i.eval σ >>= fun id => .ok (.ref id) := rfl
/-- `{y := alice.age}` reads `alice.age` in the state it is applied in and
binds `y`. -/
theorem UpdElem.write_val (σ₀ τ : State) (x : Var) (t : Term C) : (UpdElem.val x t).write σ₀ τ =
    t.eval σ₀ >>= fun v => .ok (τ.setEnv x (.val v)) := rfl
/-- `{p := alice}` binds the alias `p`. -/
theorem UpdElem.write_path (σ₀ τ : State) (x : Var) (p : PTerm C) :
    (UpdElem.path x p).write σ₀ τ = p.eval σ₀ >>= fun rs => .ok (τ.setEnv x (.spath rs.1 rs.2)) :=
  rfl
/-- `{m := freshId(addM(memory))}` binds the memory local `m`. -/
theorem UpdElem.write_mref (σ₀ τ : State) (x : Var) (i : ITerm C) :
    (UpdElem.mref x i).write σ₀ τ = i.eval σ₀ >>= fun id => .ok (τ.setEnv x (.mref id)) := rfl
/-- `{storage := save(…)}` replaces the storage, and nothing else. -/
theorem UpdElem.write_storage (σ₀ τ : State) (s : STerm C) : (UpdElem.storage s).write σ₀ τ =
    s.eval σ₀ >>= fun τ' => .ok { τ with storage := τ'.storage } := rfl
/-- `{old := storage}` binds the storage variable `old` to the storage. -/
theorem UpdElem.write_store (σ₀ τ : State) (x : Var) (s : STerm C) :
    (UpdElem.store x s).write σ₀ τ = s.eval σ₀ >>= fun τ' => .ok (τ.setEnv x (.store τ'.storage)) :=
  rfl
/-- `{memory := write(…)}` replaces the heap, and nothing else. -/
theorem UpdElem.write_memory (σ₀ τ : State) (m : MTerm C) : (UpdElem.memory m).write σ₀ τ =
    m.eval σ₀ >>= fun μ => .ok { τ with heap := μ.heap, nextId := μ.nextId } := rfl
/-- `{selfBalance := selfBalance - 5}`: the amount, then the funds. -/
theorem UpdElem.write_selfBalance (σ₀ τ : State) (op : IntOp) (a : Term C) :
    (UpdElem.selfBalance op a).write σ₀ τ = a.eval σ₀ >>= Value.asInt >>= fun amt =>
      .ok { τ with selfBalance := op.apply σ₀.selfBalance amt } := by
  simp only [UpdElem.write, bind, Except.bind]
  cases a.eval σ₀ <;> rfl
/-- `{net := store(net, at(to), net(to) - 5)}`: the address, the amount, then
the entry. -/
theorem UpdElem.write_net (σ₀ τ : State) (r : Term C) (op : IntOp) (a : Term C) :
    (UpdElem.net r op a).write σ₀ τ =
      r.eval σ₀ >>= Value.asInt >>= fun addr => a.eval σ₀ >>= Value.asInt >>= fun amt =>
        .ok { τ with net := setBy addr (op.apply (σ₀.getNet addr) amt) σ₀.net } := by
  simp only [UpdElem.write, bind, Except.bind]
  cases r.eval σ₀ with
  | error => rfl
  | ok v =>
    cases v with
    | bool b => rfl
    | int addr =>
      cases a.eval σ₀ with
      | error => rfl
      | ok w => cases w <;> rfl

/-- `{oldNet := net}` binds the ledger variable `oldNet` to the ledger. -/
theorem UpdElem.write_saveNet (σ₀ τ : State) (x : Var) :
    (UpdElem.saveNet x : UpdElem C).write σ₀ τ = .ok (τ.setEnv x (.ledger σ₀.net)) := rfl
/-- Binding a local leaves the ledger. -/
theorem net_setEnv (σ : State) (x : Var) (b : Binding) : (σ.setEnv x b).net = σ.net := rfl
/-- A ledger entry after a write: the written amount at that address, the old
one elsewhere. -/
theorem lookupBy_setBy_int (k k' v : Int) (l : List (Int × Int)) :
    lookupBy k (setBy k' v l) = if k = k' then some v else lookupBy k l := by
  split
  · subst_vars; exact SemanticsProperties.lookupBy_setBy_self _ _ _
  · exact SemanticsProperties.lookupBy_setBy_ne ‹_› _ _

/-- `true` holds. -/
theorem holds_tt : holds σ (Fml.tt : Fml C) ↔ True := Iff.rfl
/-- `¬ φ`. -/
theorem holds_not (φ : Fml C) : holds σ (.not φ) ↔ ¬ holds σ φ := Iff.rfl
/-- `φ ∧ ψ`. -/
theorem holds_and (φ ψ : Fml C) : holds σ (.and φ ψ) ↔ holds σ φ ∧ holds σ ψ := Iff.rfl
/-- `a == 1 → …`. -/
theorem holds_imp (φ ψ : Fml C) : holds σ (.imp φ ψ) ↔ (holds σ φ → holds σ ψ) := Iff.rfl
/-- `y == 10` (`Fml.eqD`) holds when both sides are defined and equal: as a
diamond on each side, since a side that halts makes it false. -/
theorem holds_eqD (a b : Term C) : holds σ (Fml.eqD a b) ↔
    Modality.diamond.wp (a.eval σ) fun x => Modality.diamond.wp (b.eval σ) fun y => x = y := by
  rw [holds_eqD_iff]
  cases a.eval σ <;> cases b.eval σ <;>
    simp only [Modality.wp, Modality.onHalt, Except.ok.injEq, reduceCtorEq, false_and, and_false,
      and_self, exists_false, exists_eq_left', eq_comm]
/-- `se1 ≐ true` (`Fml.eq`, the total equation a taclet writes): the Theory
values of the two sides agree.  Of a literal and a bound local, which is
what a branch condition compares, that is their values
(`Term.denote_lit`, `Term.denote_pv`, `Theory.StValue.Equiv.prim_iff`). -/
theorem holds_eq (a b : Term C) : holds σ (.eq a b) ↔
    Theory.StValue.Equiv (a.denote σ) (b.denote σ) := Iff.rfl
/-- A literal denotes its value. -/
theorem Term.denote_lit (v : Value) : (Term.lit v : Term C).denote σ = .prim v := rfl
/-- A local denotes its value, if it is bound to one. -/
theorem Term.denote_pv (x : Var) : (Term.pv x : Term C).denote σ = match σ.getEnv x with
    | .ok (.val v) => .prim v
    | _ => .st .mtSt := rfl
/-- `Equiv.prim_iff` with the primitive on the left. -/
theorem equiv_prim_left_iff {p : Value} {v : Theory.StValue} :
    Theory.StValue.Equiv (.prim p) v ↔ Theory.StValue.prim p = v :=
  ⟨fun h => (Theory.StValue.Equiv.prim_iff.1 h.symm).symm,
    fun h => h ▸ Theory.StValue.Equiv.refl _⟩
/-- `defined t`: `t` returns, a diamond with nothing after. -/
theorem holds_defined (t : Term C) : holds σ (.defined t) ↔
    Modality.diamond.wp (t.eval σ) fun _ => True := by
  simp only [holds]
  cases t.eval σ <;> simp [Modality.wp, Modality.onHalt]
/-- `{y := alice.age} y == 10`: apply the update, under the modality it was
produced in. -/
theorem holds_upd (m : Modality) (U : Upd C) (φ : Fml C) :
    holds σ (.upd m U φ) ↔ m.wp (U.apply σ) (holds · φ) := by
  simp only [holds, Modality.after_eq_wp]
/-- `∀ uint a; φ`: `φ` for every `a` of the type. -/
theorem holds_all (x : Var) (p : PrimTy) (φ : Fml C) :
    holds σ (.all x p φ) ↔ ∀ v, p.admits v → holds (σ.setEnv x (.val v)) φ := Iff.rfl

end Eval

end Close

/-! ## The tactic -/

-- `Fml.eqD` is a conjunction: its lemma goes first, ahead of `holds_and`.
attribute [close_rw high] Close.holds_eqD

attribute [close_rw]
  -- formulas and updates
  Close.holds_tt Close.holds_not Close.holds_and Close.holds_imp Close.holds_upd
  Close.holds_defined Close.holds_all
  Close.holds_eq Close.Term.denote_lit Close.Term.denote_pv Close.equiv_prim_left_iff
  Theory.StValue.Equiv.prim_iff Theory.StValue.prim.injEq
  Hyp.wrap Upd.apply List.foldlM_cons List.foldlM_nil
  Close.UpdElem.write_val Close.UpdElem.write_path Close.UpdElem.write_mref
  Close.UpdElem.write_storage Close.UpdElem.write_store Close.UpdElem.write_memory
  Close.UpdElem.write_selfBalance Close.UpdElem.write_net Close.UpdElem.write_saveNet IntOp.apply
  -- terms
  Close.Term.eval_lit Close.Term.eval_pv Close.Term.eval_binop Close.Term.eval_unop
  Close.Term.eval_find Close.Term.eval_len Close.Term.eval_read Close.Term.eval_ite
  Close.Term.eval_env State.envVal Close.Term.eval_net Close.Term.eval_netOf State.getNet
  Close.PTerm.eval_root Close.PTerm.eval_field Close.PTerm.eval_at Close.PTerm.eval_next
  Close.PTerm.eval_pv Close.idxOk_array Close.idxOk_map Close.pastEnd_array
  Close.forall_unit Close.exists_unit
  Close.find_overlay_fields Close.layAt_prim Close.fieldPath_nil Close.fieldPath_field
  Close.fieldPath_at
  Close.STerm.eval_storage Close.STerm.eval_pv Close.STerm.eval_save Close.STerm.eval_save_find
  Close.STerm.eval_save_copyMem Close.STerm.eval_delAt Close.STerm.eval_push
  Close.STerm.eval_pushSlot Close.STerm.eval_pop Close.STerm.eval_shrink
  Close.SValT.eval_val Close.SValT.eval_find Close.SValT.eval_copyMem
  Close.ITerm.eval_pv Close.ITerm.eval_read Close.ITerm.eval_alloc Close.ITerm.eval_copy
  Close.MAddr.eval_field Close.MAddr.eval_at
  Close.MTerm.eval_memory Close.MTerm.eval_write Close.MTerm.eval_addM Close.MTerm.eval_copySt
  Close.MValT.eval_val Close.MValT.eval_ref
  -- operators
  Close.evalBinop_strict Close.evalBinop_and Close.evalBinop_or applyBinOp applyUnOp unopCheck
  Close.pickBranch_eq BinOp.retTy BinOp.isArith checkArith uintBound intBound
  Close.uintBitwise_ofNat Close.uintBitwise_ofNat_cast Close.uintBitwise_cast_ofNat
  uintBitwise_natCast Nat.reduceAnd Nat.reduceOr Nat.reduceXor
  -- runs
  Modality.wp_ok Modality.wp_pure Modality.wp_error Modality.wp_bind Modality.wp_ite
  Modality.wp_diamond Modality.onHalt_box Modality.onHalt_diamond
  Close.pure_eq_ok Res.ok_bind Res.error_bind Close.bind_ok_right bind_assoc
  Close.saveStorage_bind_restore Close.writeAddr_bind_restore
  -- values
  Close.bindingVal_val Close.bindingPath_spath Close.bindingRef_mref Close.bindingStore_store
  Close.bindingLedger_ledger
  Close.bindingVal_eq_ok
  Close.bindingRef_eq_ok Close.asInt_eq_ok Close.asBool_eq_ok Close.asRef_eq_ok Close.toMVal_eq
  Close.toSVal_int Close.toSVal_bool Close.asValue_toSVal Close.asValue_toMVal Close.asValue_int
  Close.asValue_bool Close.mval_asValue_prim Close.mval_asValue_ref Close.mval_asRef_ref
  Close.defaultOf_int Close.defaultOf_bool Close.asInt_int Close.asBool_bool
  -- states
  State.findStorage_setEnv State.checkIndex_setEnv Close.checkIndex_mk
  State.getEnv_setEnv_self State.getEnv_setEnv_ne Close.findStorage_mk
  Close.getEnv_mk Close.readAddr_mk Close.readVal_mk Close.readAddr_setEnv Close.readVal_setEnv
  Close.tx_setEnv Close.selfBalance_setEnv Close.net_setEnv Close.lookupBy_setBy_int
  -- paths, arrays, copies
  Close.diverge_cons' Close.not_diverge_nil_left Close.not_diverge_nil_right Close.prefix_nil
  Close.prefix_cons Close.prefix_cons_nil Close.after_nil Close.after_cons SVal.find_nil
  List.nil_append List.cons_append List.append_nil
  Close.arrLen_array Close.arrLen_eq_ok Close.pushOn_array Close.popOn_push Close.popOn_push_keep Close.find_push_last
  Close.copyLeaf_prim Close.apart_field Close.apart_index Close.apart_field_index
  Close.apart_index_field
  -- logic
  Except.ok.injEq Binding.val.injEq Binding.mref.injEq Binding.store.injEq Binding.ledger.injEq
  PrimVal.int.injEq
  PrimVal.bool.injEq
  MVal.prim.injEq MVal.ref.injEq SVal.prim.injEq Prod.mk.injEq Seg.field.injEq Seg.at.injEq
  Var.user.injEq Var.fresh.injEq Int.ofNat.injEq
  forall_eq' forall_eq exists_eq_left' exists_eq_left forall_exists_index and_imp
  true_and and_true and_self implies_true forall_const ne_eq not_false_eq_true not_true_eq_false
  true_or or_true or_false false_or not_and not_exists Classical.not_not true_implies
  false_implies decide_eq_true_eq decide_eq_false_iff_not
  Bool.and_true Bool.and_false Bool.true_and Bool.false_and Bool.or_true Bool.or_false
  Bool.true_or Bool.false_or Bool.not_true Bool.not_false Bool.not_not
  Bool.not_eq_true' Bool.not_eq_false' Bool.and_eq_true Bool.or_eq_true Bool.and_eq_false_iff
  Bool.or_eq_false_iff
  -- computation
  reduceCtorEq reduceIte reduceDIte String.reduceEq Nat.reduceEqDiff Nat.reducePow Int.reduceEq
  Int.reduceAdd Int.reduceSub Int.reduceMul Int.reduceNeg Int.reduceLT Int.reduceLE

-- A write, a subtree read, a copy is named together with what is known of it.
attribute [close_rw] Modality.wp_box_saveStorage Modality.wp_box_findStorage
  Modality.wp_box_writeAddr Modality.wp_box_copyStToM Modality.wp_box_allocDefault
  Modality.wp_box_copyMem Modality.wp_box_transferAt

-- The bare box names a result with nothing, so it waits in a set of its own
-- (`close_rw_last`, consulted after `close_rw`) until every fact is in scope:
-- a push is not named before the array it pushes onto is known.  The diamond
-- is named at once, since what a premise says is what the rest needs.
attribute [close_rw_last] Modality.wp_box

/-- The first pass of `sol_close`: evaluate, and name every write with what
is known of it. -/
macro "sol_close_eval" : tactic => `(tactic| simp only [close_rw])

/-- The second: each premise in scope for what follows it, so that the facts
about a write rewrite the reads after it.  Nothing is named bare yet: a
result a later fact decides (the array a push lands on) is decided first. -/
macro "sol_close_facts" : tactic => `(tactic|
  simp (config := { contextual := true, maxSteps := 400000 }) only [close_rw])

/-- The third: what is left is named bare, under the box. -/
macro "sol_close_reads" : tactic => `(tactic|
  simp (config := { contextual := true, maxSteps := 400000 }) only [close_rw, close_rw_last])

/-- `sol_close_reads` on the goal and every hypothesis. -/
macro "sol_close_reads_all" : tactic => `(tactic|
  simp_all (config := { maxSteps := 400000 }) only [close_rw, close_rw_last])

open Lean Elab Tactic Meta in
/-- The goal `refine close ?_` leaves, `Valid (Hyp.wrap Γ φ)`, with the context
put back and the taclet's instance computed (`normValid`): its terms are
still the premise's, `(Simple.lit 1 _).lower` for `1`. -/
elab "sol_close_unwrap" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  if ty.isAppOf ``Valid && (ty.find? (·.isConstOf ``Hyp.wrap)).isSome then
    replaceMainGoal [← normValid g]

/-- `sol_close`: prove a formula with no modality left in an arbitrary state
(`Close.lean`).  Run `sol_symex` first; with no goal left it does nothing. -/
macro "sol_close" : tactic => `(tactic|
  all_goals
   (sol_close_unwrap
    intro σ
    sol_close_eval
    all_goals try sol_close_facts
    all_goals try sol_close_reads
    all_goals try (intros; sol_close_reads_all)
    all_goals try (subst_vars; sol_close_reads_all)
    all_goals (try intros)
    -- a bounds check returns `()`: nothing is left to choose
    all_goals (try simp only [Close.exists_unit, Close.forall_unit, exists_const, forall_const] at *)
    all_goals first | omega | grind))

end Solidity
