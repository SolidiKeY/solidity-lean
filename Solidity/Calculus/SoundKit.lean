import Solidity.Calculus.Rules

/-!
# The soundness kit

What the per-taclet soundness proofs are made of (`SoundUpdate.lean`,
`SoundUnfold.lean`, `RuleSoundness.lean`): `SameOk`, the agreement an
unfolding rule owes (two runs end alike off the fresh names, or both halt);
`Premise.Correct`, what a premise means for the statement it replaces; and
the lemmas and tactics that put an update and a statement, or a premise's
statements and the original, into the same shape.  Most of them name a read
both sides share (`envVal`, `envRef`) or move a fresh binding outward, so
that `res_split` can split both runs on the same atoms.
-/

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-! ## Two runs that end alike -/

/-- The fresh names a rule may declare at index `k`: `se`, `sp`, `ie`, `mv`. -/
def freshVars (k : Nat) : List Var :=
  [.fresh "se" k, .fresh "sp" k, .fresh "ie" k, .fresh "mv" k]

def SameOk (ns : List Var) : Res State → Res State → Prop
  | .ok a, .ok b => EnvAgreeExcept ns a b
  | .error _, .error _ => True
  | _, _ => False

theorem SameOk.of_agree {ns : List Var} {x y : Res State} (h : ResultsAgree ns x y) :
    SameOk ns x y := by
  cases x <;> cases y <;> simp_all [SameOk, ResultsAgree]

theorem Semantics.EnvAgreeExcept.setEnv_left {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) {n : Var} (hn : n ∈ ns) (b : Binding) :
    EnvAgreeExcept ns (s₁.setEnv n b) s₂ :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun m hm => by
    have hne : m ≠ n := fun heq => hm (heq ▸ hn)
    simpa [State.setEnv, lookupBy_setBy_ne hne] using h.env m hm,
    h.selfBalance⟩

theorem agree_setEnv (σ : State) (x : Var) (b : Binding) :
    EnvAgreeExcept [x] (σ.setEnv x b) σ :=
  (EnvAgreeExcept.refl [x] σ).setEnv_left (by simp) b

theorem avoids_single {x : Var} {vs : List Var} (h : x ∉ vs) : Avoids vs [x] :=
  fun y hy hm => h (by simp at hm; exact hm ▸ hy)

section
variable {σ : State} {x : Var} {b : Binding}

@[simp] theorem Simple.eval_setEnv {p : PrimTy} {s : Simple C p} (h : x ∉ s.vars) :
    s.eval (σ.setEnv x b) = s.eval σ := s.eval_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem Val.eval_setEnv {p : PrimTy} {v : Val C p} (h : x ∉ v.vars) :
    v.eval (σ.setEnv x b) = v.eval σ := v.eval_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem SPath.resolve_setEnv {T : Ty} {p : SPath C T} (h : x ∉ p.vars) :
    p.resolve (σ.setEnv x b) = p.resolve σ := p.resolve_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem Loc.resolve_setEnv {T : Ty} {l : Loc C T} (h : x ∉ l.vars) :
    l.resolve (σ.setEnv x b) = l.resolve σ := l.resolve_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem MPath.mval_setEnv {T : Ty} {p : MPath C T} (h : x ∉ p.vars) :
    p.mval (σ.setEnv x b) = p.mval σ := p.mval_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem MLoc.read_setEnv {T : Ty} {l : MLoc C T} (h : x ∉ l.vars) :
    l.read (σ.setEnv x b) = l.read σ := l.read_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem Src.value_setEnv {T : Ty} {r : Src C T} (h : x ∉ r.vars) :
    r.value (σ.setEnv x b) = r.value σ := r.value_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem MSrc.mval_setEnv {T : Ty} {r : MSrc C T} (h : x ∉ r.vars) :
    r.mval (σ.setEnv x b) = r.mval σ := r.mval_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem State.findStorage_setEnv (r : Name) (segs : List Seg) :
    (σ.setEnv x b).findStorage r segs = σ.findStorage r segs := rfl
@[simp] theorem State.getObj_setEnv (id : Nat) : (σ.setEnv x b).getObj id = σ.getObj id := rfl
end

/-- What a premise means for the statement it replaces. -/
def Premise.Correct (k : Nat) (m : Modality) (s : Stmt C) : Premise C → Prop
  | .update U => ∀ σ, SameOk [] (U.apply σ) (s.run σ)
  | .unfold P => ∀ σ, SameOk (freshVars k) (Prog.run σ P) (s.run σ)
  | .split c c' P Q => ∀ σ,
      (holds σ c → SameOk (freshVars k) (Prog.run σ P) (s.run σ)) ∧
      (holds σ c' → SameOk (freshVars k) (Prog.run σ Q) (s.run σ)) ∧
      (¬ holds σ c → ¬ holds σ c' → ∃ e, s.run σ = .error e)
  | .done b => ∀ σ, (∃ e, s.run σ = .error e) ∧ (b = true → m = .box)


theorem State.saveStorage_with (σ : State) (r segs v) :
    (σ.saveStorage r segs v >>= fun τ => pure { σ with storage := τ.storage }) =
      σ.saveStorage r segs v := by
  unfold State.saveStorage
  split
  · cases h : SVal.save _ segs v <;> rfl
  · rfl

@[simp] theorem Upd.apply_single (e : UpdElem C) (σ : State) :
    Upd.apply [e] σ = e.write σ σ := by
  simp [Upd.apply]

theorem upd_val (x : Var) {p : PrimTy} (e : Val C p) (σ : State) :
    Upd.apply [.val x e.lower] σ = (Stmt.assignLocal x e).run σ := by
  simp [UpdElem.write, Val.lower_eval, Stmt.run]

theorem upd_assign {T : Ty} (l : Loc C T) (r : Src C T) (σ : State) :
    Upd.apply [.storage (.save .storage l.lower r.lower)] σ = (Stmt.assign l r).run σ := by
  have hr : r.lower.eval σ = r.value σ := by
    cases r <;> simp [Src.lower, SValT.eval, Src.value, Val.lower_eval, STerm.eval, SPath.lower_eval]
  simp only [Upd.apply_single, UpdElem.write, STerm.eval, hr, Loc.lower_eval, Stmt.run, bind_assoc,
    pure_bind, State.saveStorage_with]

theorem upd_rebind (x : Var) {R : RefTy} (p : SPath C (.ref R)) (σ : State) :
    Upd.apply [.path x p.lower] σ = (Stmt.rebind x (.path p)).run σ := by
  simp [UpdElem.write, SPath.lower_eval, Stmt.run, ARhs.bind]

theorem upd_delete {T : Ty} (l : Loc C T) (σ : State) :
    Upd.apply [.storage (.delAt .storage l.lower)] σ = (Stmt.delete l).run σ := by
  simp only [Upd.apply_single, UpdElem.write, STerm.eval, Loc.lower_eval, Stmt.run, bind_assoc,
    pure_bind]
  cases l.resolve σ with
  | error _ => rfl
  | ok rs =>
    simp only [bind, Except.bind]
    cases σ.findStorage rs.1 rs.2 with
    | error _ => rfl
    | ok cur => exact State.saveStorage_with σ _ _ _

theorem SameOk.of_eq {ns : List Var} {x y : Res State} (h : x = y) : SameOk ns x y := by
  subst h; cases x <;> simp [SameOk, EnvAgreeExcept.refl]

theorem evalBinop_compound {op : BinOp} (hop : op.hasCompoundAssign = true) (p : PrimTy) (lv : Value)
    (b : Res Value) : evalBinop op p lv b = (do checkArith (.prim p) (← applyBinOp op lv (← b))) := by
  cases op <;> simp [BinOp.hasCompoundAssign] at hop <;> rfl

@[simp] theorem SameOk.self (ns : List Var) (x : Res State) : SameOk ns x x := by
  cases x <;> simp [SameOk, EnvAgreeExcept.refl]
@[simp] theorem SameOk.error_error (ns : List Var) (a b : Halt) :
    SameOk ns (.error a : Res State) (.error b) := trivial
@[simp] theorem SameOk.ok_ok (ns : List Var) (a b : State) :
    SameOk ns (.ok a) (.ok b) ↔ EnvAgreeExcept ns a b := Iff.rfl
@[simp] theorem SameOk.ok_error (ns : List Var) (a : State) (b : Halt) :
    ¬ SameOk ns (.ok a) (.error b) := id
@[simp] theorem SameOk.error_ok (ns : List Var) (a : Halt) (b : State) :
    ¬ SameOk ns (.error a) (.ok b) := id

/-- Close `SameOk ns x y` between two runs made of the same pure reads and one
write: split every `Except` match, and compare. -/
macro "res_split" : tactic => `(tactic| (
  simp only [bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals (try simp_all [EnvAgreeExcept.refl])))

theorem upd_opStore {op : BinOp} (hop : op.hasCompoundAssign = true) {p : PrimTy}
    (l : Loc C (.prim p)) (se : Simple C p) (σ : State) :
    SameOk [] (Upd.apply [.storage (.save .storage l.lower
        (.val (.binop op p (.find .storage l.lower) se.lower)))] σ)
      (do let v ← se.eval σ; let (r, segs) ← l.resolve σ; opStore σ op p r segs v) := by
  simp only [Upd.apply_single, UpdElem.write, STerm.eval, SValT.eval, Term.eval, Loc.lower_eval,
    Simple.lower_eval, bind_assoc, pure_bind, evalBinop_compound hop, State.saveStorage_with, opStore]
  res_split

theorem evalBinop_bump (op : IncDec) (p : PrimTy) (lv : Value) (b : Res Value) :
    evalBinop op.binOp p lv b = (do
      checkArith (.prim p) (← applyBinOp op.binOp lv (← b))) := by
  cases op <;> rfl

theorem applyBinOp_bump (op : IncDec) (lv : Value) :
    applyBinOp op.binOp lv (.int 1) =
      (do let n ← lv.asInt; pure (.int (if op.isIncrement then n + 1 else n - 1))) := by
  cases op <;> cases lv <;> rfl

/-! ### Shared reads

The update and the statement read the same things through differently shaped
code; these name the reads, so both sides split on the same atoms. -/

/-- A stack local's value. -/
def envVal (σ : State) (x : Var) : Res Value := do
  match ← σ.getEnv x with
  | .val v => pure v
  | .spath .. | .mref _ => .error .stuck

/-- A memory local's identity. -/
def envRef (σ : State) (x : Var) : Res Nat := do
  match ← σ.getEnv x with
  | .mref id => pure id
  | .val _ | .spath .. => .error .stuck

@[simp] theorem Term.eval_pv (σ : State) (x : Var) : (Term.pv x : Term C).eval σ = envVal σ x := rfl
@[simp] theorem Simple.eval_local (σ : State) {p : PrimTy} (x : Var) :
    (Simple.local x : Simple C p).eval σ = envVal σ x := rfl
@[simp] theorem ITerm.eval_pv (σ : State) (x : Var) : (ITerm.pv x : ITerm C).eval σ = envRef σ x := rfl
@[simp] theorem MPath.mval_var (σ : State) {R : RefTy} (x : Var) :
    (MPath.var x : MPath C (.ref R)).mval σ = (do pure (MVal.ref (← envRef σ x))) := by
  simp only [MPath.mval, envRef, bind, Except.bind]
  cases σ.getEnv x with
  | error _ => rfl
  | ok b => cases b <;> rfl
@[simp] theorem MVal.asRef_ref (id : Nat) : (MVal.ref id).asRef = pure id := rfl

@[simp] theorem bumpLocal_eq (σ : State) (op : IncDec) (p : PrimTy) (x : Var) :
    bumpLocal σ op p x = (do
      let old ← envVal σ x
      let oldInt ← old.asInt
      let new ← checkArith (.prim p) (.int (if op.isIncrement then oldInt + 1 else oldInt - 1))
      pure (σ.setEnv x (.val new), if op.isPre then new else old)) := by
  simp only [bumpLocal, envVal, bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals simp_all

@[simp] theorem opLocal_eq (σ : State) (op : BinOp) (p : PrimTy) (x : Var) (v : Value) :
    opLocal σ op p x v = (do
      let old ← envVal σ x
      let new ← applyBinOp op old v
      let new ← checkArith (.prim p) new
      pure (σ.setEnv x (.val new))) := by
  simp only [opLocal, envVal, bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals simp_all

@[simp] theorem readLoc_eq (σ : State) (a : Addr) : readLoc σ a = (do (← readAddr σ a).asValue) := by
  cases a with
  | memoryField id f =>
    simp only [readLoc, readAddr, bind, Except.bind, pure, Except.pure]
    repeat' split
    all_goals simp_all
  | memoryIndex id i =>
    simp only [readLoc, readAddr, bind, Except.bind, pure, Except.pure]
    cases σ.getObj id with
    | error _ => rfl
    | ok o =>
      cases o with
      | struct _ => rfl
      | array elems => by_cases hh : 0 ≤ i ∧ i.toNat < elems.length <;> simp [hh]

@[simp] theorem writeLoc_eq (σ : State) (a : Addr) (v : Value) :
    writeLoc σ a v = writeAddr σ v.toMVal a := by
  cases a <;> rfl

@[simp] theorem MLoc.read_field (σ : State) {s f : Name} {T : Ty} (b : MPath C (.struct s))
    (h : C.fieldType s f = some T) :
    (MLoc.field b f h).read σ = (do readAddr σ (.memoryField (← (← b.mval σ).asRef) f)) := by
  simp only [MLoc.read, readAddr]; rfl

@[simp] theorem MLoc.read_index (σ : State) {E : Ty} (b : MPath C (.array E)) (i : Val C .uint) :
    (MLoc.index b i).read σ =
      (do let id ← (← b.mval σ).asRef; readAddr σ (.memoryIndex id (← (← i.eval σ).asInt))) := by
  simp only [MLoc.read, readAddr]; rfl

theorem writeAddr_with (σ : State) (mv : MVal) (a : Addr) :
    (writeAddr σ mv a >>= fun μ => pure { σ with heap := μ.heap, nextId := μ.nextId }) =
      writeAddr σ mv a := by
  cases a with
  | memoryField id f =>
    simp only [writeAddr, memWriteField, bind, Except.bind, pure, Except.pure]
    cases σ.getObj id with
    | error _ => rfl
    | ok o => cases o <;> rfl
  | memoryIndex id i =>
    simp only [writeAddr, memWriteIndex, bind, Except.bind, pure, Except.pure]
    cases σ.getObj id with
    | error _ => rfl
    | ok o =>
      cases o with
      | struct _ => rfl
      | array elems => by_cases hh : 0 ≤ i ∧ i.toNat < elems.length <;> simp [hh] <;> rfl

/-- The simp set that unfolds an update and a statement to their reads and writes. -/
macro "upd_unfold" : tactic => `(tactic| simp only [Upd.apply, List.foldlM, UpdElem.write,
    STerm.eval, SValT.eval, Term.eval_pv, Term.eval, PTerm.eval, ITerm.eval_pv, ITerm.eval,
    MTerm.eval, MValT.eval, MAddr.eval, SPath.lower_eval, Loc.lower_eval, Val.lower_eval,
    Simple.lower_eval, Stmt.run, Src.value, Val.eval, Simple.eval_local, bind_assoc, pure_bind,
    bind_pure, State.saveStorage_with, writeAddr_with, OpLoc.store, OpLoc.bump, opStore, bumpStore,
    opLocal_eq, bumpLocal_eq, opMem, bumpMem, readLoc_eq, writeLoc_eq, ARhs.bind, MRhs.bind,
    MSrc.mval, MLoc.write, MPath.mval_var, MVal.asRef_ref, MLoc.read_field, MLoc.read_index,
    Loc.resolve, SPath.resolve, Src.pushVal, evalBinop_bump, applyBinOp_bump, Term.bumped])

open Lean Elab Tactic in
elab "show_tags" : tactic => do
  let gs ← getGoals
  logInfo m!"{gs.length}: {← gs.mapM fun g => return (← g.getTag)}"

end Solidity
