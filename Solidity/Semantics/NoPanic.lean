import Solidity.Semantics

/-!
# Only an `assert` panics

`Halt.panic` is the one halt no modality accepts, and the interpreter raises
it in one place, a failed `assert` (`assertOk`).  Every other operation halts
with `revert` or `stuck`, so a statement with no `assert` in it never panics
(`Prog.run_noPanic`), and neither does a term or an update, which read the
state through these operations (`Calculus/NoPanic.lean`).

Each lemma follows its operation's definition, the recursive ones by the same
recursion; `no_panic` discharges an unfolded definition.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-- A computation that does not end in a panic. -/
abbrev NoPanic {α : Type} (x : Res α) : Prop := x ≠ .error .panic

theorem NoPanic.bind {α β : Type} {x : Res α} {f : α → Res β} (hx : NoPanic x)
    (hf : ∀ a, x = .ok a → NoPanic (f a)) : NoPanic (x >>= f) := by
  cases x with
  | error e => exact fun h => hx (by simpa [Bind.bind, Except.bind] using h)
  | ok a => exact hf a rfl

@[simp] theorem NoPanic.ok {α : Type} (a : α) : NoPanic (.ok a : Res α) := nofun
@[simp] theorem NoPanic.pure {α : Type} (a : α) : NoPanic (Pure.pure a : Res α) := nofun
@[simp] theorem NoPanic.revert {α : Type} : NoPanic (.error .revert : Res α) := nofun
@[simp] theorem NoPanic.stuck {α : Type} : NoPanic (.error .stuck : Res α) := nofun
@[simp] theorem NoPanic.map {α β : Type} (f : α → β) (x : Res α) :
    NoPanic (f <$> x) ↔ NoPanic x := by
  cases x <;> simp [Functor.map, Except.map]

/-- Discharge an unfolded operation: binds by `NoPanic.bind`, matches and
conditionals by `split`, the operations below by `simp`. -/
syntax "no_panic" : tactic
macro_rules
  | `(tactic| no_panic) => `(tactic| first
    | (simp; done)
    | (simp [*, pickBranch_noPanic, evalBinop_noPanic, pushAt_noPanic]; done)
    | ((refine NoPanic.bind (by first | assumption | simp [*]) fun _ _ => ?_); no_panic)
    | (split <;> no_panic))

@[simp] theorem SVal.find_noPanic (v : SVal) (segs : List Seg) : NoPanic (v.find segs) := by
  fun_induction SVal.find v segs <;> simp_all

@[simp] theorem SVal.save_noPanic (v : SVal) (segs : List Seg) (new : SVal) :
    NoPanic (v.save segs new) := by
  fun_induction SVal.save v segs new <;> simp_all [NoPanic.bind]

@[simp] theorem State.findStorage_noPanic (σ : State) (r : Name) (segs : List Seg) :
    NoPanic (σ.findStorage r segs) := by
  unfold State.findStorage; split <;> simp_all

@[simp] theorem State.saveStorage_noPanic (σ : State) (r : Name) (segs : List Seg) (new : SVal) :
    NoPanic (σ.saveStorage r segs new) := by
  unfold State.saveStorage; split <;> simp_all [NoPanic.bind]

@[simp] theorem State.writeStorage_noPanic (σ : State) (r : Name) (segs : List Seg) (new : SVal) :
    NoPanic (σ.writeStorage r segs new) := by
  unfold State.writeStorage; split <;> simp_all [NoPanic.bind]

@[simp] theorem State.checkIndex_noPanic (σ : State) (r : Name) (segs : List Seg) (i : Int) :
    NoPanic (σ.checkIndex r segs i) := by
  unfold State.checkIndex
  refine NoPanic.bind (by simp) fun a _ => ?_
  split <;> (try split) <;> simp

@[simp] theorem State.getEnv_noPanic (σ : State) (x : Var) : NoPanic (σ.getEnv x) := by
  unfold State.getEnv; split <;> simp

@[simp] theorem State.getObj_noPanic (σ : State) (id : Nat) : NoPanic (σ.getObj id) := by
  unfold State.getObj; split <;> simp

mutual
theorem copyStToM_noPanic (σ : State) : (v : SVal) → NoPanic (copyStToM σ v)
  | .prim p => by cases p <;> simp [copyStToM]
  | .struct fields => by
    simp only [copyStToM]
    exact NoPanic.bind (copyStFields_noPanic σ fields) fun _ _ => by simp
  | .array elems _ _ => by
    simp only [copyStToM]
    exact NoPanic.bind (copyStElems_noPanic σ elems) fun _ _ => by simp
  | .map _ _ => by simp [copyStToM]

theorem copyStFields_noPanic (σ : State) :
    (fs : List (Name × SVal)) → NoPanic (copyStFields σ fs)
  | [] => by simp [copyStFields]
  | (_, v) :: rest => by
    simp only [copyStFields]
    exact NoPanic.bind (copyStToM_noPanic σ v) fun (σ', _) _ =>
      NoPanic.bind (copyStFields_noPanic σ' rest) fun _ _ => by simp

theorem copyStElems_noPanic (σ : State) : (vs : List SVal) → NoPanic (copyStElems σ vs)
  | [] => by simp [copyStElems]
  | v :: rest => by
    simp only [copyStElems]
    exact NoPanic.bind (copyStToM_noPanic σ v) fun (σ', _) _ =>
      NoPanic.bind (copyStElems_noPanic σ' rest) fun _ _ => by simp
end

@[simp] theorem allocDefault_noPanic (σ : State) (R : RefTy) : NoPanic (allocDefault σ R) := by
  unfold allocDefault; split <;> simp

mutual
theorem copyMToSt_noPanic (σ : State) (rem : List Nat) : (v : MVal) → NoPanic (copyMToSt σ rem v)
  | .prim p => by cases p <;> simp [copyMToSt]
  | .ref id => by
    by_cases hmem : id ∈ rem
    · rw [copyMToSt, dif_pos hmem]
      split
      · exact NoPanic.bind (copyMFields_noPanic σ (rem.erase id) _) fun _ _ => by simp
      · exact NoPanic.bind (copyMElems_noPanic σ (rem.erase id) _) fun _ _ => by simp
      · rename_i e h
        have h' : NoPanic (σ.getObj id) := State.getObj_noPanic σ id
        rw [h] at h'
        simp only [ne_eq, Except.error.injEq] at h' ⊢
        exact h'
    · rw [copyMToSt, dif_neg hmem]; simp
termination_by _ => (rem.length, 0)
decreasing_by all_goals
  (apply Prod.Lex.left
   have h1 := List.length_erase_of_mem hmem
   have h2 := List.length_pos_of_mem hmem
   omega)

theorem copyMFields_noPanic (σ : State) (rem : List Nat) :
    (fs : List (Name × MVal)) → NoPanic (copyMFields σ rem fs)
  | [] => by simp [copyMFields]
  | (_, v) :: rest => by
    rw [copyMFields]
    exact NoPanic.bind (copyMToSt_noPanic σ rem v) fun _ _ =>
      NoPanic.bind (copyMFields_noPanic σ rem rest) fun _ _ => by simp
termination_by fs => (rem.length, fs.length + 1)
decreasing_by all_goals (apply Prod.Lex.right; simp <;> omega)

theorem copyMElems_noPanic (σ : State) (rem : List Nat) :
    (vs : List MVal) → NoPanic (copyMElems σ rem vs)
  | [] => by simp [copyMElems]
  | v :: rest => by
    rw [copyMElems]
    exact NoPanic.bind (copyMToSt_noPanic σ rem v) fun _ _ =>
      NoPanic.bind (copyMElems_noPanic σ rem rest) fun _ _ => by simp
termination_by vs => (rem.length, vs.length + 1)
decreasing_by all_goals (apply Prod.Lex.right; simp <;> omega)
end

attribute [simp] copyStToM_noPanic copyMToSt_noPanic

@[simp] theorem copyMem_noPanic (σ : State) (v : MVal) : NoPanic (copyMem σ v) :=
  copyMToSt_noPanic _ _ _

@[simp] theorem Value.asInt_noPanic (v : Value) : NoPanic v.asInt := by
  cases v <;> simp [Value.asInt]

@[simp] theorem Value.asBool_noPanic (v : Value) : NoPanic v.asBool := by
  cases v <;> simp [Value.asBool]

@[simp] theorem SVal.asValue_noPanic (v : SVal) : NoPanic v.asValue := by
  unfold SVal.asValue; split <;> simp

@[simp] theorem MVal.asValue_noPanic (v : MVal) : NoPanic v.asValue := by
  unfold MVal.asValue; split <;> simp

@[simp] theorem MVal.asRef_noPanic (v : MVal) : NoPanic v.asRef := by
  unfold MVal.asRef; split <;> simp

@[simp] theorem applyBinOp_noPanic (op : BinOp) (l r : Value) : NoPanic (applyBinOp op l r) := by
  unfold applyBinOp; split <;> no_panic

@[simp] theorem applyUnOp_noPanic (op : UnOp) (v : Value) : NoPanic (applyUnOp op v) := by
  unfold applyUnOp; split <;> simp_all [NoPanic.bind]

@[simp] theorem checkArith_noPanic (ty : Ty) (v : Value) : NoPanic (checkArith ty v) := by
  unfold checkArith; repeat' split
  all_goals simp

@[simp] theorem unopCheck_noPanic (op : UnOp) (p : PrimTy) (v : Value) :
    NoPanic (unopCheck op p v) := by
  unfold unopCheck; split <;> simp

theorem pickBranch_noPanic (cv : Value) {t e : Res Value} (ht : NoPanic t) (he : NoPanic e) :
    NoPanic (pickBranch cv t e) := by
  unfold pickBranch; split <;> simp_all

theorem evalBinop_noPanic (op : BinOp) (p : PrimTy) (lv : Value) {b : Res Value}
    (hb : NoPanic b) : NoPanic (evalBinop op p lv b) := by
  unfold evalBinop; split <;> simp_all [NoPanic.bind]

@[simp] theorem aliasPath_noPanic (σ : State) (x : Var) : NoPanic (aliasPath σ x) := by
  unfold aliasPath; no_panic

@[simp] theorem arrayLen_noPanic (σ : State) (r : Name) (segs : List Seg) :
    NoPanic (arrayLen σ r segs) := by
  unfold arrayLen; no_panic

@[simp] theorem memArrayLen_noPanic (σ : State) (id : Nat) : NoPanic (memArrayLen σ id) := by
  unfold memArrayLen; no_panic

@[simp] theorem writeAddr_noPanic (σ : State) (mv : MVal) (a : Addr) :
    NoPanic (writeAddr σ mv a) := by
  unfold writeAddr memWriteField memWriteIndex; no_panic

theorem pushAt_noPanic (σ : State) (E : Ty) (r : Name) (segs : List Seg) {val : SVal → Res SVal}
    (hv : ∀ x, NoPanic (val x)) : NoPanic (pushAt σ E r segs val) := by
  unfold pushAt; no_panic

@[simp] theorem pushPlaceAt_noPanic (σ : State) (E : Ty) (r : Name) (segs : List Seg) :
    NoPanic (pushPlaceAt σ E r segs) := by
  unfold pushPlaceAt; no_panic

@[simp] theorem popAt_noPanic (σ : State) (keep : Bool) (r : Name) (segs : List Seg) :
    NoPanic (popAt σ keep r segs) := by
  unfold popAt; no_panic

/-! ## Program expressions

A statement's halt and its update's halt may come from different reads (the
two evaluate in another order); neither is a panic. -/

@[simp] theorem Simple.eval_noPanic (σ : State) {p : PrimTy} (s : Simple C p) :
    NoPanic (s.eval σ) := by
  cases s <;> simp only [Simple.eval] <;> no_panic

mutual
theorem SPath.resolve_noPanic (σ : State) : {T : Ty} → (p : SPath C T) → NoPanic (p.resolve σ)
  | _, .alias x => by simp [SPath.resolve]
  | _, .loc l => by simp only [SPath.resolve]; exact Loc.resolve_noPanic σ l

theorem Loc.resolve_noPanic (σ : State) : {T : Ty} → (l : Loc C T) → NoPanic (l.resolve σ)
  | _, .root r _ => by simp [Loc.resolve]
  | _, .field b f _ => by
    have hb := SPath.resolve_noPanic σ b
    simp only [Loc.resolve]; no_panic
  | _, .index _ b i => by
    have hb := SPath.resolve_noPanic σ b
    have hi := Val.eval_noPanic σ i
    simp only [Loc.resolve]; no_panic

theorem MPath.mval_noPanic (σ : State) : {T : Ty} → (p : MPath C T) → NoPanic (p.mval σ)
  | _, .var x => by simp only [MPath.mval]; no_panic
  | _, .loc l => by simp only [MPath.mval]; exact MLoc.read_noPanic σ l

theorem MLoc.read_noPanic (σ : State) : {T : Ty} → (l : MLoc C T) → NoPanic (l.read σ)
  | _, .field b f _ => by
    have hb := MPath.mval_noPanic σ b
    simp only [MLoc.read]; no_panic
  | _, .index _ b i => by
    have hb := MPath.mval_noPanic σ b
    have hi := Val.eval_noPanic σ i
    simp only [MLoc.read]; no_panic

theorem Val.eval_noPanic (σ : State) : {p : PrimTy} → (v : Val C p) → NoPanic (v.eval σ)
  | _, .simple s => by simp [Val.eval]
  | _, .read l => by
    have hl := Loc.resolve_noPanic σ l
    simp only [Val.eval]; no_panic
  | _, .binop _ _ _ a b => by
    have ha := Val.eval_noPanic σ a
    have hb := Val.eval_noPanic σ b
    simp only [Val.eval]
    exact NoPanic.bind ha fun _ _ => evalBinop_noPanic _ _ _ hb
  | _, .unop _ _ _ a => by
    have ha := Val.eval_noPanic σ a
    simp only [Val.eval]; no_panic
  | _, .ternary c a b => by
    have hc := Val.eval_noPanic σ c
    have ha := Val.eval_noPanic σ a
    have hb := Val.eval_noPanic σ b
    simp only [Val.eval]
    exact NoPanic.bind hc fun _ _ => pickBranch_noPanic _ ha hb
  | _, .readMem l => by
    have hl := MLoc.read_noPanic σ l
    simp only [Val.eval]; no_panic
  | _, .len b _ => by
    have hb := SPath.resolve_noPanic σ b
    simp only [Val.eval]; no_panic
  | _, .mlen b _ => by
    have hb := MPath.mval_noPanic σ b
    simp only [Val.eval]; no_panic
end

attribute [simp] SPath.resolve_noPanic Loc.resolve_noPanic MPath.mval_noPanic MLoc.read_noPanic
  Val.eval_noPanic

@[simp] theorem Src.value_noPanic (σ : State) {T : Ty} (r : Src C T) : NoPanic (r.value σ) := by
  cases r <;> simp only [Src.value] <;> no_panic

@[simp] theorem MSrc.mval_noPanic (σ : State) {T : Ty} (r : MSrc C T) : NoPanic (r.mval σ) := by
  cases r <;> simp only [MSrc.mval] <;> no_panic

@[simp] theorem MLoc.addr_noPanic (σ : State) {T : Ty} (l : MLoc C T) : NoPanic (l.addr σ) := by
  cases l <;> simp only [MLoc.addr] <;> no_panic

@[simp] theorem Arg.bindSeq_noPanic : (args : List (Arg C)) → (σ : State) →
    NoPanic (Arg.bindSeq args σ)
  | [], σ => by simp [Arg.bindSeq]
  | a :: as, σ => by
    simp only [Arg.bindSeq]
    exact NoPanic.bind (Val.eval_noPanic σ a.e) fun _ _ => Arg.bindSeq_noPanic as _

theorem NoPanic.mapM {α β : Type} {f : α → Res β} (hf : ∀ a, NoPanic (f a)) :
    (l : List α) → NoPanic (l.mapM f)
  | [] => by simp
  | a :: l => by
    simp only [List.mapM_cons]
    exact NoPanic.bind (hf a) fun _ _ => NoPanic.bind (NoPanic.mapM hf l) fun _ _ => by simp

@[simp] theorem ExtCall.key_noPanic (σ : State) (c : ExtCall C) : NoPanic (c.key σ) := by
  have hm : NoPanic (c.args.mapM fun a => a.2.eval σ) :=
    NoPanic.mapM (fun _ => Simple.eval_noPanic σ _) _
  unfold ExtCall.key; no_panic

@[simp] theorem bindData_noPanic : (xs : List (PrimTy × Var)) → (vs : List Value) → (σ : State) →
    NoPanic (bindData xs vs σ)
  | [], _, σ => by simp [bindData]
  | (p, x) :: xs, v :: vs, σ => by
    simp only [bindData]
    split
    · exact bindData_noPanic xs vs _
    · simp
  | _ :: _, [], _ => by simp [bindData]

@[simp] theorem transferAt_noPanic (σ : State) (addr amt : Int) :
    NoPanic (transferAt σ addr amt) := by
  unfold transferAt; split <;> simp

/-- A `transfer` never panics. -/
theorem Stmt.run_transfer_noPanic (σ : State) (r a : Val C .uint) :
    NoPanic ((Stmt.transfer r a).run σ) := by
  simp only [Stmt.run]; no_panic

/-! ## Statements

A statement panics only through an `assert` it runs: one of its own, or one in
a branch, a callee or a clause. -/

mutual

/-- Whether an `assert` occurs in the statement, in a branch, a callee or a
clause included. -/
def Stmt.mayPanic : Stmt C → Bool
  | .assert _ => true
  | .ite _ thn els => Prog.mayPanic thn || Prog.mayPanic els
  | .call _ _ _ _ body => Prog.mayPanic body
  | .tryCall _ _ ok err _ pnc other =>
    Prog.mayPanic ok || Prog.mayPanic err || Prog.mayPanic pnc || Prog.mayPanic other
  | _ => false

def Prog.mayPanic : List (Stmt C) → Bool
  | [] => false
  | s :: P => s.mayPanic || Prog.mayPanic P

end

@[simp] theorem readLoc_noPanic (σ : State) (a : Addr) : NoPanic (readLoc σ a) := by
  unfold readLoc; no_panic

@[simp] theorem writeLoc_noPanic (σ : State) (a : Addr) (v : Value) :
    NoPanic (writeLoc σ a v) := by
  unfold writeLoc; no_panic

@[simp] theorem guardOk_noPanic (v : Value) (σ : State) : NoPanic (guardOk v σ) := by
  unfold guardOk; no_panic

@[simp] theorem memClear_noPanic (σ : State) (a : Addr) (T : Ty) : NoPanic (memClear σ a T) := by
  cases T <;> simp only [memClear] <;> no_panic

@[simp] theorem OpLoc.store_noPanic (σ : State) (op : BinOp) {p : PrimTy} (l : OpLoc C p)
    (v : Value) : NoPanic (l.store σ op v) := by
  cases l <;> simp only [OpLoc.store, opLocal, opStore, opMem] <;> no_panic

@[simp] theorem OpLoc.bump_noPanic (σ : State) (op : IncDec) {p : PrimTy} (l : OpLoc C p) :
    NoPanic (l.bump σ op) := by
  cases l <;> simp only [OpLoc.bump, bumpLocal, bumpStore, bumpMem] <;> no_panic

@[simp] theorem ARhs.bind_noPanic (σ : State) (x : Var) {R : RefTy} (r : ARhs C R) :
    NoPanic (r.bind σ x) := by
  cases r <;> simp only [ARhs.bind] <;> no_panic

@[simp] theorem MRhs.bind_noPanic (σ : State) (x : Var) {R : RefTy} (r : MRhs C R) :
    NoPanic (r.bind σ x) := by
  cases r <;> simp only [MRhs.bind] <;> no_panic

@[simp] theorem MLoc.write_noPanic (σ : State) (mv : MVal) {T : Ty} (l : MLoc C T) :
    NoPanic (l.write σ mv) := by
  cases l <;> simp only [MLoc.write, memWriteField, memWriteIndex] <;> no_panic

@[simp] theorem Src.pushVal_noPanic (σ : State) {T : Ty} (o : Option (Src C T)) (slot : SVal) :
    NoPanic (Src.pushVal σ o slot) := by
  cases o <;> simp only [Src.pushVal] <;> no_panic

@[simp] theorem CallRet.leave_noPanic (σ : State) (ret : CallRet) :
    NoPanic (CallRet.leave (C := C) σ ret) := by
  unfold CallRet.leave; no_panic

mutual

/-- **Only an `assert` panics**: a statement with none in it never does. -/
theorem Stmt.run_noPanic (σ : State) : (s : Stmt C) → s.mayPanic = false → NoPanic (s.run σ)
  | .assign .., _ | .rebind .., _ | .assignLocal .., _ | .declLocal .., _ | .declStorage .., _
  | .opAssign .., _ | .incDec .., _ | .assignIncDec .., _ | .push .., _ | .pop .., _
  | .transfer .., _ | .declMem .., _ | .rebindMem .., _ | .assignFromMem .., _
  | .assignMem .., _ | .delete .., _ | .deleteMem .., _ | .assignNew .., _ | .require _, _
  | .revert, _ => by
    simp only [Stmt.run] <;> no_panic
  | .assert _, h => by simp [Stmt.mayPanic] at h
  | .ite c thn els, h => by
    simp only [Stmt.mayPanic, Bool.or_eq_false_iff] at h
    have h₁ := fun τ => Prog.run_noPanic τ thn h.1
    have h₂ := fun τ => Prog.run_noPanic τ els h.2
    simp only [Stmt.run]
    refine NoPanic.bind (by simp) fun _ _ => ?_
    split <;> simp [*]
  | .call _ args _ ret body, h => by
    simp only [Stmt.mayPanic] at h
    have h₁ := fun τ => Prog.run_noPanic τ body h
    simp only [Stmt.run]; no_panic
  | .tryCall call rets ok err code pnc other, h => by
    simp only [Stmt.mayPanic, Bool.or_eq_false_iff] at h
    have h₁ := fun τ => Prog.run_noPanic τ ok h.1.1.1
    have h₂ := fun τ => Prog.run_noPanic τ err h.1.1.2
    have h₃ := fun τ => Prog.run_noPanic τ pnc h.1.2
    have h₄ := fun τ => Prog.run_noPanic τ other h.2
    simp only [Stmt.run]
    refine NoPanic.bind (by simp) fun _ _ => ?_
    split
    · simp
    · exact NoPanic.bind (by simp) fun _ _ => h₁ _
    · exact h₂ _
    · exact NoPanic.bind (by simp) fun _ _ => h₃ _
    · exact h₄ _

theorem Prog.run_noPanic (σ : State) : (P : List (Stmt C)) → Prog.mayPanic P = false →
    NoPanic (Prog.run σ P)
  | [], _ => by simp [Prog.run]
  | s :: P, h => by
    simp only [Prog.mayPanic, Bool.or_eq_false_iff] at h
    simp only [Prog.run]
    exact NoPanic.bind (Stmt.run_noPanic σ s h.1) fun τ _ => Prog.run_noPanic τ P h.2

end

end Solidity
