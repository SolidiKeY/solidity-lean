import Solidity.Semantics
import Solidity.Semantics.NoPanicSimp

/-!
# The term model's operations never panic

`Halt.panic` is the one halt no modality accepts.  The untyped operations
the term model keeps halt with `revert` or `undef` only: the state's reads
and writes, the evaluation of a program expression, the copies and
allocations, a payment.  A term or an update reads the state through these
operations, so neither panics (`Calculus/NoPanic.lean`).

Each lemma follows its operation's definition, the recursive ones by the same
recursion; `no_panic` discharges an unfolded definition.  Split out of
today's `Semantics/NoPanic`, deleted at W4 `sem-del` (`docs/intrinsic.md`):
the term model keeps these.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-- A computation that does not end in a panic. -/
abbrev NoPanic {α : Type} (x : Res α) : Prop := x ≠ .error .panic

theorem NoPanic.bind {α β : Type} {x : Res α} {f : α → Res β} (hx : NoPanic x)
    (hf : ∀ a, x = .ok a → NoPanic (f a)) : NoPanic (x >>= f) := by
  cases x with
  | error e =>
    exact fun h => hx (by simpa only [Except.error.injEq, Bind.bind, Except.bind] using h)
  | ok a => exact hf a rfl

/-- The halt of a computation that does not panic is not a panic. -/
theorem NoPanic.ne_of_eq {α : Type} {x : Res α} {e : Halt} (hx : NoPanic x)
    (h : x = .error e) : e ≠ .panic :=
  fun hp => hx (by rw [h, hp])

@[no_panic_simp] theorem NoPanic.ok {α : Type} (a : α) : NoPanic (.ok a : Res α) := nofun
@[no_panic_simp] theorem NoPanic.pure {α : Type} (a : α) : NoPanic (Pure.pure a : Res α) := nofun
@[no_panic_simp] theorem NoPanic.revert {α : Type} : NoPanic (.error .revert : Res α) := nofun
@[no_panic_simp] theorem NoPanic.undef {α : Type} : NoPanic (.error .undef : Res α) := nofun
@[no_panic_simp] theorem NoPanic.map {α β : Type} (f : α → β) (x : Res α) :
    NoPanic (f <$> x) ↔ NoPanic x := by
  cases x <;> simp only [Functor.map, Except.map, ne_eq, Except.error.injEq, NoPanic.ok,
      not_false_eq_true]

/-- Discharge an unfolded operation: binds by `NoPanic.bind`, matches and
conditionals by `split`, the operations below by their `no_panic_simp` lemmas. -/
syntax "no_panic" : tactic
macro_rules
  | `(tactic| no_panic) => `(tactic| first
    | (simp only [no_panic_simp, ne_eq, not_false_eq_true, reduceCtorEq]; done)
    | (simp only [no_panic_simp, ne_eq, not_false_eq_true, reduceCtorEq, *, pickBranch_noPanic,
        evalBinop_noPanic, pushAt_noPanic]; done)
    | ((refine NoPanic.bind (by first | assumption |
          simp only [no_panic_simp, ne_eq, not_false_eq_true, reduceCtorEq, *]) fun _ _ => ?_);
        no_panic)
    | (split <;> no_panic))

@[no_panic_simp]
theorem Semantics.SVal.find_noPanic (v : SVal) (segs : List Seg) : NoPanic (v.find segs) := by
  fun_induction SVal.find v segs <;> simp_all only [ne_eq, NoPanic.ok, not_false_eq_true,
      Except.error.injEq, reduceCtorEq, List.get_eq_getElem, List.length_append, not_and,
      Int.toNat_lt, Int.natCast_add, Int.not_lt, Bool.not_eq_true, imp_false]

@[no_panic_simp] theorem Semantics.SVal.save_noPanic (v : SVal) (segs : List Seg) (new : SVal) :
    NoPanic (v.save segs new) := by
  fun_induction SVal.save v segs new <;> simp_all only [ne_eq, NoPanic.ok, not_false_eq_true,
      implies_true, NoPanic.bind, Except.error.injEq, reduceCtorEq, List.get_eq_getElem,
      List.length_append, not_and, Int.toNat_lt, Int.natCast_add, Int.not_lt]

@[no_panic_simp] theorem Semantics.State.findStorage_noPanic (σ : State) (r : Name) (segs : List Seg) :
    NoPanic (σ.findStorage r segs) := by
  unfold State.findStorage; split <;> simp_all only [ne_eq, SVal.find_noPanic, not_false_eq_true,
      Except.error.injEq, reduceCtorEq]

@[no_panic_simp]
theorem Semantics.State.saveStorage_noPanic (σ : State) (r : Name) (segs : List Seg) (new : SVal) :
    NoPanic (σ.saveStorage r segs new) := by
  unfold State.saveStorage; split <;> simp_all only [ne_eq, SVal.save_noPanic, not_false_eq_true,
      NoPanic.ok, implies_true, NoPanic.bind, Except.error.injEq, reduceCtorEq]

@[no_panic_simp]
theorem Semantics.State.writeStorage_noPanic (σ : State) (r : Name) (segs : List Seg) (new : SVal) :
    NoPanic (σ.writeStorage r segs new) := by
  unfold State.writeStorage; split <;> simp_all only [ne_eq, saveStorage_noPanic,
      not_false_eq_true, findStorage_noPanic, implies_true, NoPanic.bind]

@[no_panic_simp]
theorem Semantics.State.checkIndex_noPanic (σ : State) (r : Name) (segs : List Seg) (i : Int) :
    NoPanic (σ.checkIndex r segs i) := by
  unfold State.checkIndex
  refine NoPanic.bind (by simp only [ne_eq, findStorage_noPanic, not_false_eq_true]) fun a _ => ?_
  split <;> (try split) <;> simp only [ne_eq, NoPanic.pure, not_false_eq_true, Except.error.injEq,
      reduceCtorEq]

@[no_panic_simp] theorem Semantics.State.getEnv_noPanic (σ : State) (x : Var) : NoPanic (σ.getEnv x) := by
  unfold State.getEnv; split <;> simp only [ne_eq, NoPanic.ok, not_false_eq_true,
      Except.error.injEq, reduceCtorEq]

@[no_panic_simp] theorem Semantics.State.getObj_noPanic (σ : State) (id : Nat) : NoPanic (σ.getObj id) := by
  unfold State.getObj; split <;> simp only [ne_eq, NoPanic.ok, not_false_eq_true,
      Except.error.injEq, reduceCtorEq]

mutual
theorem copyStToM_noPanic (σ : State) : (v : SVal) → NoPanic (copyStToM σ v)
  | .prim p => by cases p <;> simp only [copyStToM, ne_eq, NoPanic.ok, not_false_eq_true]
  | .struct fields => by
    simp only [copyStToM]
    exact NoPanic.bind (copyStFields_noPanic σ fields) fun _ _ => by simp only [ne_eq, NoPanic.ok,
        not_false_eq_true]
  | .array elems _ _ => by
    simp only [copyStToM]
    exact NoPanic.bind (copyStElems_noPanic σ elems) fun _ _ => by simp only [ne_eq, NoPanic.ok,
        not_false_eq_true]
  | .map _ _ => by simp only [copyStToM, ne_eq, Except.error.injEq, reduceCtorEq, not_false_eq_true]

theorem copyStFields_noPanic (σ : State) :
    (fs : List (Name × SVal)) → NoPanic (copyStFields σ fs)
  | [] => by simp only [copyStFields, ne_eq, NoPanic.ok, not_false_eq_true]
  | (_, v) :: rest => by
    simp only [copyStFields]
    exact NoPanic.bind (copyStToM_noPanic σ v) fun (σ', _) _ =>
      NoPanic.bind (copyStFields_noPanic σ' rest) fun _ _ => by simp only [ne_eq, NoPanic.ok,
          not_false_eq_true]

theorem copyStElems_noPanic (σ : State) : (vs : List SVal) → NoPanic (copyStElems σ vs)
  | [] => by simp only [copyStElems, ne_eq, NoPanic.ok, not_false_eq_true]
  | v :: rest => by
    simp only [copyStElems]
    exact NoPanic.bind (copyStToM_noPanic σ v) fun (σ', _) _ =>
      NoPanic.bind (copyStElems_noPanic σ' rest) fun _ _ => by simp only [ne_eq, NoPanic.ok,
          not_false_eq_true]
end

@[no_panic_simp]
theorem allocDefault_noPanic (σ : State) (R : RefTy) : NoPanic (allocDefault σ R) := by
  unfold allocDefault; split <;> simp only [ne_eq, NoPanic.ok, not_false_eq_true,
      Except.error.injEq, reduceCtorEq]

mutual
theorem copyMToSt_noPanic (σ : State) (rem : List Nat) : (v : MVal) → NoPanic (copyMToSt σ rem v)
  | .prim p => by cases p <;> simp only [copyMToSt, ne_eq, NoPanic.ok, not_false_eq_true]
  | .ref id => by
    by_cases hmem : id ∈ rem
    · rw [copyMToSt, dif_pos hmem]
      split
      · exact NoPanic.bind (copyMFields_noPanic σ (rem.erase id) _) fun _ _ => by simp only [ne_eq,
          NoPanic.ok, not_false_eq_true]
      · exact NoPanic.bind (copyMElems_noPanic σ (rem.erase id) _) fun _ _ => by simp only [ne_eq,
          NoPanic.ok, not_false_eq_true]
      · rename_i e h
        exact fun hp => NoPanic.ne_of_eq (State.getObj_noPanic σ id) h (Except.error.inj hp)
    · rw [copyMToSt, dif_neg hmem]; simp only [ne_eq, Except.error.injEq, reduceCtorEq,
        not_false_eq_true]
termination_by _ => (rem.length, 0)
decreasing_by all_goals
  (apply Prod.Lex.left
   have h1 := List.length_erase_of_mem hmem
   have h2 := List.length_pos_of_mem hmem
   omega)

theorem copyMFields_noPanic (σ : State) (rem : List Nat) :
    (fs : List (Name × MVal)) → NoPanic (copyMFields σ rem fs)
  | [] => by simp only [copyMFields, ne_eq, NoPanic.ok, not_false_eq_true]
  | (_, v) :: rest => by
    rw [copyMFields]
    exact NoPanic.bind (copyMToSt_noPanic σ rem v) fun _ _ =>
      NoPanic.bind (copyMFields_noPanic σ rem rest) fun _ _ => by simp only [ne_eq, NoPanic.ok,
          not_false_eq_true]
termination_by fs => (rem.length, fs.length + 1)
decreasing_by all_goals (apply Prod.Lex.right; simp only [List.length_cons,
    Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, Nat.lt_add_one] <;> omega)

theorem copyMElems_noPanic (σ : State) (rem : List Nat) :
    (vs : List MVal) → NoPanic (copyMElems σ rem vs)
  | [] => by simp only [copyMElems, ne_eq, NoPanic.ok, not_false_eq_true]
  | v :: rest => by
    rw [copyMElems]
    exact NoPanic.bind (copyMToSt_noPanic σ rem v) fun _ _ =>
      NoPanic.bind (copyMElems_noPanic σ rem rest) fun _ _ => by simp only [ne_eq, NoPanic.ok,
          not_false_eq_true]
termination_by vs => (rem.length, vs.length + 1)
decreasing_by all_goals (apply Prod.Lex.right; simp only [List.length_cons,
    Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, Nat.lt_add_one] <;> omega)
end

attribute [no_panic_simp] copyStToM_noPanic copyMToSt_noPanic

@[no_panic_simp] theorem copyMem_noPanic (σ : State) (v : MVal) : NoPanic (copyMem σ v) :=
  copyMToSt_noPanic _ _ _

@[no_panic_simp] theorem Semantics.Value.asInt_noPanic (v : Value) : NoPanic v.asInt := by
  cases v <;> simp only [Value.asInt, ne_eq, NoPanic.ok, not_false_eq_true, Except.error.injEq,
      reduceCtorEq]

@[no_panic_simp] theorem Semantics.Value.keyAt_noPanic (k : PrimTy) (v : Value) : NoPanic (v.keyAt k) := by
  cases k <;> cases v <;> simp only [Value.keyAt, Value.asInt, Value.asBool, bind, Except.bind,
    pure, Except.pure, ne_eq, NoPanic.ok, not_false_eq_true, Except.error.injEq, reduceCtorEq]

@[no_panic_simp] theorem Semantics.Value.asBool_noPanic (v : Value) : NoPanic v.asBool := by
  cases v <;> simp only [Value.asBool, ne_eq, Except.error.injEq, reduceCtorEq, not_false_eq_true,
      NoPanic.ok]

@[no_panic_simp] theorem Semantics.SVal.asValue_noPanic (v : SVal) : NoPanic v.asValue := by
  unfold SVal.asValue; split <;> simp only [ne_eq, NoPanic.ok, not_false_eq_true,
      Except.error.injEq, reduceCtorEq]

@[no_panic_simp] theorem Semantics.MVal.asValue_noPanic (v : MVal) : NoPanic v.asValue := by
  unfold MVal.asValue; split <;> simp only [ne_eq, NoPanic.ok, not_false_eq_true,
      Except.error.injEq, reduceCtorEq]

@[no_panic_simp] theorem Semantics.MVal.asRef_noPanic (v : MVal) : NoPanic v.asRef := by
  unfold MVal.asRef; split <;> simp only [ne_eq, NoPanic.pure, not_false_eq_true,
      Except.error.injEq, reduceCtorEq]

@[no_panic_simp]
theorem applyBinOp_noPanic (op : BinOp) (l r : Value) : NoPanic (applyBinOp op l r) := by
  unfold applyBinOp; split <;> no_panic

@[no_panic_simp] theorem applyUnOp_noPanic (op : UnOp) (v : Value) : NoPanic (applyUnOp op v) := by
  unfold applyUnOp; split <;> simp_all only [ne_eq, Value.asInt_noPanic, not_false_eq_true,
      NoPanic.ok, implies_true, NoPanic.bind, Value.asBool_noPanic]

@[no_panic_simp] theorem checkArith_noPanic (ty : Ty) (v : Value) : NoPanic (checkArith ty v) := by
  unfold checkArith; repeat' split
  all_goals simp only [ne_eq, NoPanic.ok, not_false_eq_true, Except.error.injEq, reduceCtorEq]

@[no_panic_simp] theorem unopCheck_noPanic (op : UnOp) (p : PrimTy) (v : Value) :
    NoPanic (unopCheck op p v) := by
  unfold unopCheck; split <;> simp only [ne_eq, checkArith_noPanic, not_false_eq_true, NoPanic.pure]

theorem pickBranch_noPanic (cv : Value) {t e : Res Value} (ht : NoPanic t) (he : NoPanic e) :
    NoPanic (pickBranch cv t e) := by
  unfold pickBranch; split <;> simp_all only [ne_eq, not_false_eq_true, Except.error.injEq,
      reduceCtorEq]

theorem evalBinop_noPanic (op : BinOp) (p : PrimTy) (lv : Value) {b : Res Value}
    (hb : NoPanic b) : NoPanic (evalBinop op p lv b) := by
  unfold evalBinop; split <;> simp_all only [ne_eq, NoPanic.pure, not_false_eq_true, imp_false,
      applyBinOp_noPanic, checkArith_noPanic, implies_true, NoPanic.bind]

@[no_panic_simp] theorem aliasPath_noPanic (σ : State) (x : Var) : NoPanic (aliasPath σ x) := by
  unfold aliasPath; no_panic

@[no_panic_simp] theorem arrayLen_noPanic (σ : State) (r : Name) (segs : List Seg) :
    NoPanic (arrayLen σ r segs) := by
  unfold arrayLen; no_panic

@[no_panic_simp]
theorem memArrayLen_noPanic (σ : State) (id : Nat) : NoPanic (memArrayLen σ id) := by
  unfold memArrayLen; no_panic

@[no_panic_simp] theorem writeAddr_noPanic (σ : State) (mv : MVal) (a : Addr) :
    NoPanic (writeAddr σ mv a) := by
  unfold writeAddr memWriteField memWriteIndex; no_panic

theorem pushAt_noPanic (σ : State) (E : Ty) (r : Name) (segs : List Seg) {val : SVal → Res SVal}
    (hv : ∀ x, NoPanic (val x)) : NoPanic (pushAt σ E r segs val) := by
  unfold pushAt; no_panic

@[no_panic_simp] theorem pushPlaceAt_noPanic (σ : State) (E : Ty) (r : Name) (segs : List Seg) :
    NoPanic (pushPlaceAt σ E r segs) := by
  unfold pushPlaceAt; no_panic

@[no_panic_simp] theorem popAt_noPanic (σ : State) (keep : Bool) (r : Name) (segs : List Seg) :
    NoPanic (popAt σ keep r segs) := by
  unfold popAt; no_panic

/-! ## Program expressions

A statement's halt and its update's halt may come from different reads (the
two evaluate in another order); neither is a panic. -/

@[no_panic_simp] theorem Surface.Simple.eval_noPanic (σ : State) {p : PrimTy} (s : Surface.Simple C p) :
    NoPanic (s.eval σ) := by
  cases s <;> simp only [Surface.Simple.eval] <;> no_panic

mutual
theorem Surface.SPath.resolve_noPanic (σ : State) : {T : Ty} → (p : Surface.SPath C T) → NoPanic (p.resolve σ)
  | _, .alias x => by simp only [Surface.SPath.resolve, ne_eq, aliasPath_noPanic, not_false_eq_true]
  | _, .loc l => by simp only [Surface.SPath.resolve]; exact Surface.Loc.resolve_noPanic σ l

theorem Surface.Loc.resolve_noPanic (σ : State) : {T : Ty} → (l : Surface.Loc C T) → NoPanic (l.resolve σ)
  | _, .root r _ => by simp only [Surface.Loc.resolve, ne_eq, NoPanic.pure, not_false_eq_true]
  | _, .field b f _ => by
    have hb := Surface.SPath.resolve_noPanic σ b
    simp only [Surface.Loc.resolve]; no_panic
  | _, .index _ b i => by
    have hb := Surface.SPath.resolve_noPanic σ b
    have hi := Surface.Val.eval_noPanic σ i
    simp only [Surface.Loc.resolve]; no_panic

theorem Surface.MPath.mval_noPanic (σ : State) : {T : Ty} → (p : Surface.MPath C T) → NoPanic (p.mval σ)
  | _, .var x _ => by simp only [Surface.MPath.mval]; no_panic
  | _, .loc l => by simp only [Surface.MPath.mval]; exact Surface.MLoc.read_noPanic σ l

theorem Surface.MLoc.read_noPanic (σ : State) : {T : Ty} → (l : Surface.MLoc C T) → NoPanic (l.read σ)
  | _, .field b f _ => by
    have hb := Surface.MPath.mval_noPanic σ b
    simp only [Surface.MLoc.read]; no_panic
  | _, .index _ b i => by
    have hb := Surface.MPath.mval_noPanic σ b
    have hi := Surface.Val.eval_noPanic σ i
    simp only [Surface.MLoc.read]; no_panic

theorem Surface.Val.eval_noPanic (σ : State) : {p : PrimTy} → (v : Surface.Val C p) → NoPanic (v.eval σ)
  | _, .simple s => by simp only [Surface.Val.eval, ne_eq, Surface.Simple.eval_noPanic, not_false_eq_true]
  | _, .read l => by
    have hl := Surface.Loc.resolve_noPanic σ l
    simp only [Surface.Val.eval]; no_panic
  | _, .binop _ _ _ a b => by
    have ha := Surface.Val.eval_noPanic σ a
    have hb := Surface.Val.eval_noPanic σ b
    simp only [Surface.Val.eval]
    exact NoPanic.bind ha fun _ _ => evalBinop_noPanic _ _ _ hb
  | _, .unop _ _ _ a => by
    have ha := Surface.Val.eval_noPanic σ a
    simp only [Surface.Val.eval]; no_panic
  | _, .ternary c a b => by
    have hc := Surface.Val.eval_noPanic σ c
    have ha := Surface.Val.eval_noPanic σ a
    have hb := Surface.Val.eval_noPanic σ b
    simp only [Surface.Val.eval]
    exact NoPanic.bind hc fun _ _ => pickBranch_noPanic _ ha hb
  | _, .readMem l => by
    have hl := Surface.MLoc.read_noPanic σ l
    simp only [Surface.Val.eval]; no_panic
  | _, .len b _ => by
    have hb := Surface.SPath.resolve_noPanic σ b
    simp only [Surface.Val.eval]; no_panic
  | _, .mlen b _ => by
    have hb := Surface.MPath.mval_noPanic σ b
    simp only [Surface.Val.eval]; no_panic
end

attribute [no_panic_simp] Surface.SPath.resolve_noPanic Surface.Loc.resolve_noPanic Surface.MPath.mval_noPanic
  Surface.MLoc.read_noPanic Surface.Val.eval_noPanic

theorem NoPanic.mapM {α β : Type} {f : α → Res β} (hf : ∀ a, NoPanic (f a)) :
    (l : List α) → NoPanic (l.mapM f)
  | [] => by simp only [List.mapM_nil, ne_eq, NoPanic.pure, not_false_eq_true]
  | a :: l => by
    simp only [List.mapM_cons]
    exact NoPanic.bind (hf a) fun _ _ => NoPanic.bind (NoPanic.mapM hf l) fun _ _ => by simp only [
        ne_eq, NoPanic.pure, not_false_eq_true]

@[no_panic_simp]
theorem bindData_noPanic : (xs : List (PrimTy × Var)) → (vs : List Value) → (σ : State) →
    NoPanic (bindData xs vs σ)
  | [], _, σ => by simp only [bindData, ne_eq, NoPanic.pure, not_false_eq_true]
  | (p, x) :: xs, v :: vs, σ => by
    simp only [bindData]
    split
    · exact bindData_noPanic xs vs _
    · simp only [ne_eq, Except.error.injEq, reduceCtorEq, not_false_eq_true]
  | _ :: _, [], _ => by simp only [bindData, ne_eq, Except.error.injEq, reduceCtorEq,
      not_false_eq_true]

@[no_panic_simp] theorem transferAt_noPanic (σ : State) (addr amt : Int) :
    NoPanic (transferAt σ addr amt) := by
  unfold transferAt; split <;> simp only [ne_eq, Except.error.injEq, reduceCtorEq,
      not_false_eq_true, NoPanic.ok]

@[no_panic_simp] theorem readLoc_noPanic (σ : State) (a : Addr) : NoPanic (readLoc σ a) := by
  unfold readLoc; no_panic

@[no_panic_simp] theorem writeLoc_noPanic (σ : State) (a : Addr) (v : Value) :
    NoPanic (writeLoc σ a v) := by
  unfold writeLoc; no_panic

@[no_panic_simp]
theorem memClear_noPanic (σ : State) (a : Addr) (T : Ty) : NoPanic (memClear σ a T) := by
  cases T <;> simp only [memClear] <;> no_panic

end Solidity
