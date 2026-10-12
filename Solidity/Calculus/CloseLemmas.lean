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
known of its result), values read back, the operators, and the symbols
`Op0`–`Op3` read one constructor at a time (`Close.Op2.eval_find`, …), from
which each set's term equations follow.
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
locals, the heap, `msg.sender` and `address(this).balance` as they were, and
moves `5` on the ledger from `this` to `to` (`State.pay`). -/
theorem Modality.wp_box_transferAt {σ : State} {addr amt : Int} {P : State → Prop} :
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
/-- `Equiv.prim_iff` with the primitive on the left. -/
theorem equiv_prim_left_iff {p : Value} {v : Theory.StValue} :
    Theory.StValue.Equiv (.prim p) v ↔ Theory.StValue.prim p = v :=
  ⟨fun h => (Theory.StValue.Equiv.prim_iff.1 h.symm).symm,
    fun h => h ▸ Theory.StValue.Equiv.refl _⟩

/-- The state a `{havoc}` leaves, as the structure: its locals, heap,
funds and transaction `σ`'s. -/
theorem State.havoc_eq_mk (σ : State) (st : List (Name × SVal)) (nt : List (Int × Int)) :
    σ.havoc st nt = State.mk st σ.heap σ.nextId σ.env nt σ.selfBalance σ.tx := rfl

/-! ## The symbols, one at a time -/

section Ops

variable (σ : State)

theorem Op0.eval_lit (v : Value) : Op0.eval σ (.lit v) = .ok v := rfl
theorem Op0.eval_env (k : EnvKey) : Op0.eval σ (.env k) = .ok (.int (σ.envVal k)) := rfl
theorem Op0.eval_root (r : Name) : Op0.eval σ (.root r) = .ok (r, []) := rfl
theorem Op0.eval_storage : Op0.eval σ .storage = .ok σ := rfl
theorem Op0.eval_memory : Op0.eval σ .memory = .ok σ := rfl
theorem Op0.eval_mtSt (vs : List (Name × Ty)) : Op0.eval σ (.mtSt vs) =
    .ok { σ with storage := vs.map fun (n, T) => (n, defaultForTy T) } := rfl

theorem Op1.eval_unop (op : UnOp) (p : PrimTy) (ra : Res Value) : Op1.eval σ (.unop op p) ra =
    ra >>= fun x => applyUnOp op x >>= unopCheck op p := rfl
theorem Op1.eval_net (ra : Res Value) : Op1.eval σ .net ra =
    ra >>= Value.asInt >>= fun n => .ok (.int (σ.getNet n)) := by
  simp only [Op1.eval, bind, Except.bind]
  cases ra <;> rfl
theorem Op1.eval_field (f : Name) (rp : Res (Name × List Seg)) : Op1.eval σ (.field f) rp =
    rp >>= fun rs => .ok (rs.1, rs.2 ++ [.field f]) := rfl
theorem Op1.eval_next (rp : Res (Name × List Seg)) : Op1.eval σ .next rp =
    rp >>= fun rs => σ.findStorage rs.1 rs.2 >>= Close.pastEnd rs := by
  simp only [Op1.eval, bind, Except.bind]
  cases rp <;> rfl
theorem Op1.eval_sval (rt : Res Value) : Op1.eval σ .sval rt = rt >>= fun v => .ok v.toSVal := rfl
theorem Op1.eval_alloc (R : RefTy) (rm : Res State) : Op1.eval σ (.alloc R) rm =
    rm >>= fun τ => allocDefault τ R >>= fun r => .ok r.2 := rfl
theorem Op1.eval_mfield (f : Name) (ri : Res Nat) : Op1.eval σ (.mfield f) ri =
    ri >>= fun id => .ok (.memoryField id f) := rfl
theorem Op1.eval_addM (R : RefTy) (rm : Res State) : Op1.eval σ (.addM R) rm =
    rm >>= fun τ => allocDefault τ R >>= fun r => .ok r.1 := rfl
theorem Op1.eval_mval (rt : Res Value) : Op1.eval σ .mval rt = rt >>= fun v => .ok v.toMVal := rfl
theorem Op1.eval_ref (ri : Res Nat) : Op1.eval σ .ref ri = ri >>= fun id => .ok (.ref id) := rfl

theorem Op2.eval_binop (op : BinOp) (p : PrimTy) (ra rb : Res Value) :
    Op2.eval σ (.binop op p) ra rb = ra >>= fun x => evalBinop op p x rb := rfl
theorem Op2.eval_find (rs : Res State) (rp : Res (Name × List Seg)) : Op2.eval σ .find rs rp =
    rs >>= fun τ => rp >>= fun r => τ.findStorage r.1 r.2 >>= SVal.asValue := rfl
theorem Op2.eval_len (rs : Res State) (rp : Res (Name × List Seg)) : Op2.eval σ .len rs rp =
    rs >>= fun τ => rp >>= fun r => τ.findStorage r.1 r.2 >>= arrLen := by
  simp only [Op2.eval, bind, Except.bind]
  cases rs <;> try rfl
  all_goals cases rp <;> try rfl
  all_goals exact arrayLen_eq _ _ _
theorem Op2.eval_read (rm : Res State) (ra : Res Addr) : Op2.eval σ .read rm ra =
    rm >>= fun τ => ra >>= fun addr => readVal τ addr := rfl
theorem Op2.eval_at (rp : Res (Name × List Seg)) (ri : Res Value) : Op2.eval σ .at rp ri =
    rp >>= fun rs => ri >>= Value.asInt >>= fun k =>
      σ.checkIndex rs.1 rs.2 k >>= fun _ => .ok (rs.1, rs.2 ++ [.at k]) := by
  simp only [Op2.eval, bind, Except.bind]
  cases rp <;> try rfl
  cases ri <;> rfl
theorem Op2.eval_delAt (rs : Res State) (rp : Res (Name × List Seg)) : Op2.eval σ .delAt rs rp =
    rs >>= fun τ => rp >>= fun r => τ.findStorage r.1 r.2 >>= fun cur =>
      τ.saveStorage r.1 r.2 cur.defaultOf := rfl
theorem Op2.eval_pushSlot (E : Ty) (rs : Res State) (rp : Res (Name × List Seg)) :
    Op2.eval σ (.pushSlot E) rs rp = rs >>= fun τ => rp >>= fun r =>
      τ.findStorage r.1 r.2 >>= pushOn τ E r.1 r.2 pure := by
  simp only [Op2.eval, bind, Except.bind]
  cases rs <;> try rfl
  all_goals cases rp <;> try rfl
  all_goals exact pushAt_eq _ _ _ _ _
theorem Op2.eval_pop (rs : Res State) (rp : Res (Name × List Seg)) : Op2.eval σ .pop rs rp =
    rs >>= fun τ => rp >>= fun r => τ.findStorage r.1 r.2 >>= popOn τ false r.1 r.2 := by
  simp only [Op2.eval, bind, Except.bind]
  cases rs <;> try rfl
  all_goals cases rp <;> try rfl
  all_goals exact popAt_eq _ _ _ _
theorem Op2.eval_shrink (rs : Res State) (rp : Res (Name × List Seg)) : Op2.eval σ .shrink rs rp =
    rs >>= fun τ => rp >>= fun r => τ.findStorage r.1 r.2 >>= popOn τ true r.1 r.2 := by
  simp only [Op2.eval, bind, Except.bind]
  cases rs <;> try rfl
  all_goals cases rp <;> try rfl
  all_goals exact popAt_eq _ _ _ _
theorem Op2.eval_sfind (rs : Res State) (rp : Res (Name × List Seg)) : Op2.eval σ .sfind rs rp =
    rs >>= fun τ => rp >>= fun r => τ.findStorage r.1 r.2 := rfl
theorem Op2.eval_copyMem (rm : Res State) (ri : Res Nat) : Op2.eval σ .copyMem rm ri =
    rm >>= fun τ => ri >>= fun id => copyMem τ (.ref id) := rfl
theorem Op2.eval_iread (rm : Res State) (ra : Res Addr) : Op2.eval σ .iread rm ra =
    rm >>= fun τ => ra >>= fun addr => readAddr τ addr >>= MVal.asRef := rfl
theorem Op2.eval_copy (rm : Res State) (rv : Res SVal) : Op2.eval σ .copy rm rv =
    rv >>= fun sv => rm >>= fun τ => copyStToM τ sv >>= fun r => r.2.asRef := rfl
theorem Op2.eval_mat (ri : Res Nat) (rk : Res Value) : Op2.eval σ .mat ri rk =
    ri >>= fun id => rk >>= Value.asInt >>= fun j => .ok (.memoryIndex id j) := by
  simp only [Op2.eval, bind, Except.bind]
  cases ri <;> try rfl
  cases rk <;> rfl
theorem Op2.eval_copySt (rm : Res State) (rv : Res SVal) : Op2.eval σ .copySt rm rv =
    rv >>= fun sv => rm >>= fun τ => copyStToM τ sv >>= fun r => .ok r.1 := rfl

theorem Op3.eval_ite (rc ra rb : Res Value) : Op3.eval σ .ite rc ra rb =
    rc >>= fun cv => pickBranch cv ra rb := rfl
theorem Op3.eval_save_val (rs : Res State) (rp : Res (Name × List Seg)) (rt : Res Value) :
    Op3.eval σ .save rs rp (Op1.eval σ .sval rt) =
      rt >>= fun x => rs >>= fun τ => rp >>= fun r => τ.saveStorage r.1 r.2 x.toSVal := by
  simp only [Op3.eval, Op1.eval, bind_assoc, pure_bind, State.writeStorage_toSVal]
theorem Op3.eval_save_find (rs rs' : Res State) (rp rp' : Res (Name × List Seg)) :
    Op3.eval σ .save rs rp (Op2.eval σ .sfind rs' rp') =
      Op2.eval σ .sfind rs' rp' >>= fun sv => rs >>= fun τ => rp >>= fun r =>
        τ.findStorage r.1 r.2 >>= fun cur => τ.saveStorage r.1 r.2 (cur.overlay sv) := by
  simp only [Op3.eval, Close.writeStorage_eq]
theorem Op3.eval_save_copyMem (rs rm : Res State) (rp : Res (Name × List Seg)) (ri : Res Nat) :
    Op3.eval σ .save rs rp (Op2.eval σ .copyMem rm ri) =
      Op2.eval σ .copyMem rm ri >>= fun sv => rs >>= fun τ => rp >>= fun r =>
        τ.findStorage r.1 r.2 >>= fun cur => τ.saveStorage r.1 r.2 (cur.overlay sv) := by
  simp only [Op3.eval, Close.writeStorage_eq]
theorem Op3.eval_push (rs : Res State) (rp : Res (Name × List Seg)) (rv : Res SVal) :
    Op3.eval σ .push rs rp rv = rs >>= fun τ => rp >>= fun r =>
      τ.findStorage r.1 r.2 >>=
        pushOn τ .uint r.1 r.2 (fun _ => rv >>= fun sv => pure sv.strip) := by
  simp only [Op3.eval, bind, Except.bind]
  cases rs <;> try rfl
  all_goals cases rp <;> try rfl
  all_goals exact pushAt_eq _ _ _ _ _
theorem Op3.eval_write (rm : Res State) (ra : Res Addr) (rv : Res MVal) :
    Op3.eval σ .write rm ra rv = rv >>= fun mv => rm >>= fun τ => ra >>= fun addr =>
      writeAddr τ mv addr := rfl

end Ops

end Close

end Solidity
