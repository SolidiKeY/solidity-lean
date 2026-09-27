import Solidity.Calculus.SoundKit

/-!
# Taclets that unfold a statement

`Taclet.sound_unfold`: a rule whose premise is statements runs like the
statement it replaces, off its fresh names.  The captured part is evaluated
first, the fresh binding moves outward past every later read (it is fresh,
so nothing reads it but the statements that were given it), and the two final
states agree everywhere but on the fresh names.
-/

namespace Solidity

open Semantics

variable {C : Contract}

@[simp] theorem envVal_setEnv_self (σ : State) (x : Var) (v : Value) :
    envVal (σ.setEnv x (.val v)) x = pure v := by
  simp [envVal, State.getEnv, State.setEnv, SemanticsProperties.lookupBy_setBy_self]; rfl

theorem envVal_setEnv_ne (σ : State) {x y : Var} (h : y ≠ x) (b : Binding) :
    envVal (σ.setEnv x b) y = envVal σ y := by
  simp [envVal, State.getEnv, State.setEnv, SemanticsProperties.lookupBy_setBy_ne h]

@[simp] theorem envRef_setEnv_self (σ : State) (x : Var) (id : Nat) :
    envRef (σ.setEnv x (.mref id)) x = pure id := by
  simp [envRef, State.getEnv, State.setEnv, SemanticsProperties.lookupBy_setBy_self]; rfl

theorem envRef_setEnv_ne (σ : State) {x y : Var} (h : y ≠ x) (b : Binding) :
    envRef (σ.setEnv x b) y = envRef σ y := by
  simp [envRef, State.getEnv, State.setEnv, SemanticsProperties.lookupBy_setBy_ne h]

@[simp] theorem aliasPath_setEnv_self (σ : State) (x : Var) (r : Name) (segs : List Seg) :
    aliasPath (σ.setEnv x (.spath r segs)) x = pure (r, segs) := by
  simp [aliasPath, State.getEnv, State.setEnv, SemanticsProperties.lookupBy_setBy_self]; rfl

theorem aliasPath_setEnv_ne (σ : State) {x y : Var} (h : y ≠ x) (b : Binding) :
    aliasPath (σ.setEnv x b) y = aliasPath σ y := by
  simp [aliasPath, State.getEnv, State.setEnv, SemanticsProperties.lookupBy_setBy_ne h]

@[simp] theorem Var.fresh_ne_fresh {a b : String} {k : Nat} (h : a ≠ b) :
    Var.fresh a k ≠ Var.fresh b k := by simp [h]

theorem State.saveStorage_setEnv (σ : State) (x : Var) (b : Binding) (r : Name) (segs : List Seg)
    (v : SVal) : (σ.setEnv x b).saveStorage r segs v =
      (do let τ ← σ.saveStorage r segs v; pure (τ.setEnv x b)) := by
  simp only [State.saveStorage, State.setEnv]
  split <;> simp_all [bind, Except.bind] <;> split <;> rfl

/-- `EnvAgreeExcept ns (…(σ.setEnv a _)….setEnv b _) σ` with `a b ∈ ns`. -/
macro "agree_tac" : tactic => `(tactic| (
  repeat (first
    | exact EnvAgreeExcept.refl _ _
    | refine EnvAgreeExcept.setEnv_both ?_ _ _
    | refine EnvAgreeExcept.setEnv_left ?_ (by simp [freshVars]) _)))

/-! ### Moving a fresh binding past the state operations -/

section
variable (σ : State) (x : Var) (b : Binding)

theorem State.setObj_setEnv (id : Nat) (o : MObj) :
    (σ.setEnv x b).setObj id o = (σ.setObj id o).setEnv x b := rfl

theorem guardOk_setEnv (v : Value) :
    guardOk v (σ.setEnv x b) = (do let τ ← guardOk v σ; pure (τ.setEnv x b)) := by
  unfold guardOk; split <;> rfl

theorem memWriteField_setEnv (id : Nat) (f : Name) (mv : MVal) :
    memWriteField (σ.setEnv x b) id f mv = (do let τ ← memWriteField σ id f mv; pure (τ.setEnv x b)) := by
  simp only [memWriteField, State.getObj_setEnv, bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals (try simp_all)
  all_goals (subst_vars; rfl)

theorem memWriteIndex_setEnv (id : Nat) (i : Int) (mv : MVal) :
    memWriteIndex (σ.setEnv x b) id i mv = (do let τ ← memWriteIndex σ id i mv; pure (τ.setEnv x b)) := by
  simp only [memWriteIndex, State.getObj_setEnv, bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals (try simp_all)
  all_goals (subst_vars; rfl)

theorem readLoc_setEnv (a : Addr) : readLoc (σ.setEnv x b) a = readLoc σ a := by
  cases a <;> rfl

theorem writeLoc_setEnv (a : Addr) (v : Value) :
    writeLoc (σ.setEnv x b) a v = (do let τ ← writeLoc σ a v; pure (τ.setEnv x b)) := by
  cases a <;> simp only [writeLoc, State.getObj_setEnv, bind, Except.bind, pure, Except.pure] <;>
    repeat' split
  all_goals (try simp_all)
  all_goals (subst_vars; rfl)

theorem opMem_setEnv (op : BinOp) (p : PrimTy) (a : Addr) (v : Value) :
    opMem (σ.setEnv x b) op p a v = (do let τ ← opMem σ op p a v; pure (τ.setEnv x b)) := by
  simp only [opMem, readLoc_setEnv, writeLoc_setEnv, bind_assoc]

theorem bumpMem_setEnv (op : IncDec) (p : PrimTy) (a : Addr) :
    bumpMem (σ.setEnv x b) op p a =
      (do let r ← bumpMem σ op p a; pure (r.1.setEnv x b, r.2)) := by
  simp only [bumpMem, readLoc_setEnv, writeLoc_setEnv, bind_assoc, pure_bind]

theorem opStore_setEnv (op : BinOp) (p : PrimTy) (r : Name) (segs : List Seg) (v : Value) :
    opStore (σ.setEnv x b) op p r segs v = (do let τ ← opStore σ op p r segs v; pure (τ.setEnv x b)) := by
  simp only [opStore, State.findStorage_setEnv, State.saveStorage_setEnv, bind_assoc]

theorem bumpStore_setEnv (op : IncDec) (p : PrimTy) (r : Name) (segs : List Seg) :
    bumpStore (σ.setEnv x b) op p r segs =
      (do let q ← bumpStore σ op p r segs; pure (q.1.setEnv x b, q.2)) := by
  simp only [bumpStore, State.findStorage_setEnv, State.saveStorage_setEnv, bind_assoc, pure_bind]

theorem pushAt_setEnv (E : Ty) (r : Name) (segs : List Seg) (f : SVal → Res SVal) :
    pushAt (σ.setEnv x b) E r segs f = (do let τ ← pushAt σ E r segs f; pure (τ.setEnv x b)) := by
  simp only [pushAt, State.findStorage_setEnv, State.saveStorage_setEnv, bind_assoc]
  simp only [bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals (try simp_all)
  all_goals (subst_vars; rfl)

theorem pushPlaceAt_setEnv (E : Ty) (r : Name) (segs : List Seg) :
    pushPlaceAt (σ.setEnv x b) E r segs =
      (do let q ← pushPlaceAt σ E r segs; pure (q.1.setEnv x b, q.2)) := by
  simp only [pushPlaceAt, State.findStorage_setEnv, State.saveStorage_setEnv, bind_assoc]
  simp only [bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals (try simp_all)
  all_goals (subst_vars; rfl)

theorem popAt_setEnv (r : Name) (segs : List Seg) :
    popAt (σ.setEnv x b) r segs = (do let τ ← popAt σ r segs; pure (τ.setEnv x b)) := by
  simp only [popAt, State.findStorage_setEnv, State.saveStorage_setEnv, bind_assoc]
  simp only [bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals (try simp_all)
  all_goals (subst_vars; rfl)

theorem transferAt_setEnv (addr amt : Int) :
    transferAt (σ.setEnv x b) addr amt = (do let τ ← transferAt σ addr amt; pure (τ.setEnv x b)) := by
  have e : (σ.setEnv x b).selfBalance = σ.selfBalance := rfl
  unfold transferAt
  rw [e]
  by_cases h1 : amt < 0
  · simp only [h1, if_true]; rfl
  by_cases h2 : σ.selfBalance < amt
  · simp only [h1, h2, if_true, if_false]; rfl
  · simp only [h1, h2, if_false]; rfl

theorem copyMem_setEnv (v : MVal) : copyMem (σ.setEnv x b) v = copyMem σ v :=
  copyMem_congr (agree_setEnv σ x b) v
end

theorem envVal_setEnv_ne' (σ : State) {x y : Var} (h : x ≠ y) (b : Binding) :
    envVal (σ.setEnv x b) y = envVal σ y := envVal_setEnv_ne σ (Ne.symm h) b

theorem envRef_setEnv_ne' (σ : State) {x y : Var} (h : x ≠ y) (b : Binding) :
    envRef (σ.setEnv x b) y = envRef σ y := envRef_setEnv_ne σ (Ne.symm h) b

theorem aliasPath_setEnv_ne' (σ : State) {x y : Var} (h : x ≠ y) (b : Binding) :
    aliasPath (σ.setEnv x b) y = aliasPath σ y := aliasPath_setEnv_ne σ (Ne.symm h) b

theorem MPath.mval_loc (σ : State) {T : Ty} (l : MLoc C T) : (MPath.loc l).mval σ = l.read σ := rfl

/-- A push whose element fails fails. -/
@[simp] theorem SameOk.error_pushAt (ns : List Var) (σ : State) (E : Ty) (r : Name)
    (segs : List Seg) (e e' : Halt) :
    SameOk ns (.error e') (pushAt σ E r segs fun _ => .error e) := by
  unfold pushAt
  cases σ.findStorage r segs with
  | error _ => trivial
  | ok v => cases v <;> trivial

/-- `res_split`, knowing that a push whose element fails fails. -/
macro "res_split'" : tactic => `(tactic| (
  simp only [bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals (try simp_all [EnvAgreeExcept.refl, SameOk.error_pushAt])))

theorem evalBinop_noShort {op : BinOp} (h : op.shortCircuits = false) (p : PrimTy) (lv : Value)
    (b : Res Value) :
    evalBinop op p lv b = (do let r ← b; checkArith (op.retTy (.prim p)) (← applyBinOp op lv r)) := by
  cases op <;> simp [BinOp.shortCircuits] at h <;> rfl

@[simp] theorem Simple.eval_bool (σ : State) (b : Bool) :
    (Simple.bool b : Simple C .bool).eval σ = pure (.bool b) := rfl
@[simp] theorem Simple.eval_lit (σ : State) {p : PrimTy} (n : Int) (h : p.isNumeric = true) :
    (Simple.lit n h : Simple C p).eval σ = pure (.int n) := rfl

/-- The four fresh names avoid `vs` when each does. -/
theorem avoids_fresh {vs : List Var} {k : Nat} (h1 : Var.fresh "se" k ∉ vs)
    (h2 : Var.fresh "sp" k ∉ vs) (h3 : Var.fresh "ie" k ∉ vs) (h4 : Var.fresh "mv" k ∉ vs) :
    Avoids vs (freshVars k) := by
  intro y hy hf
  simp only [freshVars, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> contradiction

/-- A deep copy into memory, bound to `x`, from two agreeing states. -/
theorem copyStToM_bind_agree {ns : List Var} {σ τ : State} (hag : EnvAgreeExcept ns σ τ)
    (sv : SVal) (x : Var) :
    SameOk ns (do let r ← copyStToM σ sv; let id ← r.snd.asRef; pure (r.fst.setEnv x (.mref id)))
      (do let r ← copyStToM τ sv; let id ← r.snd.asRef; pure (r.fst.setEnv x (.mref id))) := by
  have h := copyStToM_agree hag sv
  revert h
  cases copyStToM σ sv with
  | error _ => cases copyStToM τ sv <;> simp [ResAgree, SameOk, bind, Except.bind]
  | ok a =>
    cases copyStToM τ sv with
    | error _ => simp [ResAgree]
    | ok b =>
      obtain ⟨σ', mv⟩ := a
      obtain ⟨τ', mv'⟩ := b
      intro ⟨he, hs⟩
      subst he
      simp only [bind, Except.bind]
      cases mv.asRef with
      | error _ => trivial
      | ok id => exact hs.setEnv_both _ _

theorem Res.ok_bind {α β : Type} (a : α) (f : α → Res β) : (Except.ok a >>= f) = f a := rfl

@[simp] theorem Src.pushVal_none (σ : State) {T : Ty} :
    Src.pushVal (C := C) (T := T) σ none = fun slot => pure slot := rfl
@[simp] theorem Src.pushVal_some (σ : State) {T : Ty} (r : Src C T) :
    Src.pushVal σ (some r) = fun _ => r.value σ := rfl

open Lean Elab Tactic Meta in
/-- Case on a `Hole`/`MHole`/`VHole` (or a source, target, right-hand side) in context. -/
elab "cases_holes" : tactic => do
  let g ← getMainGoal
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let t ← whnf (← instantiateMVars d.type)
    if [``Hole, ``MHole, ``VHole, ``OpLoc, ``MSrc, ``Src, ``ARhs, ``MRhs, ``MLoc].any t.isAppOf then
      let gs ← g.cases d.fvarId
      replaceMainGoal (gs.map (·.mvarId)).toList
      return
  throwError "no hole"

set_option hygiene false in
/-- Flatten the four freshness hypotheses to atoms. -/
macro "vars_simp" : tactic => `(tactic|
    simp only [Stmt.vars, Prog.vars, Loc.vars, SPath.vars, Src.vars, Val.vars,
      MPath.vars, MLoc.vars, ARhs.vars, MRhs.vars, MSrc.vars, OpLoc.vars, optVars, Hole.fill,
      MHole.fill, VHole.fill, List.mem_append, List.mem_cons, List.not_mem_nil, not_or,
      List.append_nil] at hse hsp hie hmv)

set_option hygiene false in
/-- Unfold both runs to their reads, moving the reads past the fresh bindings. -/
macro "unf_simp" : tactic => `(tactic|
    simp only [Prog.run, Stmt.run, Hole.fill, MHole.fill, VHole.fill, Src.value, Val.eval,
      Simple.eval_local, SPath.resolve, Loc.resolve, ARhs.bind, MRhs.bind, MSrc.mval, MLoc.write,
      MPath.mval_var, bind_assoc, pure_bind, bind_pure, envVal_setEnv_self, envRef_setEnv_self,
      aliasPath_setEnv_self, envVal_setEnv_ne, envRef_setEnv_ne, aliasPath_setEnv_ne,
      Var.fresh.injEq, String.reduceEq, false_and, MVal.asRef_ref, State.saveStorage_setEnv,
      Val.eval_setEnv, SPath.resolve_setEnv, Loc.resolve_setEnv, MPath.mval_setEnv,
      MLoc.read_setEnv, Src.value_setEnv, MSrc.mval_setEnv, State.findStorage_setEnv,
      State.getObj_setEnv, Simple.eval_setEnv, OpLoc.store, OpLoc.bump, guardOk_setEnv,
      memWriteField_setEnv, memWriteIndex_setEnv, readLoc_setEnv, writeLoc_setEnv, opMem_setEnv,
      bumpMem_setEnv, opStore_setEnv, bumpStore_setEnv, pushAt_setEnv, pushPlaceAt_setEnv,
      popAt_setEnv, transferAt_setEnv, copyMem_setEnv, Src.pushVal_none, Src.pushVal_some,
      MLoc.read, MPath.mval_loc, opLocal_eq, bumpLocal_eq, envVal_setEnv_ne', envRef_setEnv_ne',
      aliasPath_setEnv_ne', pickBranch, evalBinop_noShort, Simple.eval_bool, Simple.eval_lit,
      SemanticsProperties.State.setEnv_setEnv_absorb,
      ne_eq, not_false_eq_true, reduceCtorEq, *])

set_option maxHeartbeats 4000000 in
theorem Taclet.sound_unfold {k : Nat} {m : Modality} {s : Stmt C} {P : Prog C}
    (d : Taclet C k m s (.unfold P)) (hs : Avoids s.vars (freshVars k)) :
    ∀ σ, SameOk (freshVars k) (Prog.run σ P) (s.run σ) := by
  have hse : Var.fresh "se" k ∉ s.vars := fun h => hs _ h (by simp [freshVars])
  have hsp : Var.fresh "sp" k ∉ s.vars := fun h => hs _ h (by simp [freshVars])
  have hie : Var.fresh "ie" k ∉ s.vars := fun h => hs _ h (by simp [freshVars])
  have hmv : Var.fresh "mv" k ∉ s.vars := fun h => hs _ h (by simp [freshVars])
  clear hs
  cases d
  all_goals clear_side
  all_goals intro σ
  all_goals repeat' cases_holes
  all_goals vars_simp
  all_goals (try (unf_simp; res_split'; all_goals agree_tac; done))
  case logicalAndShortCircuitRhs =>
    rename_i v se nse
    unf_simp
    rcases Simple.eval σ se with _ | (_ | (_ | _)) <;> rcases Val.eval σ nse with _ | (_ | (_ | _)) <;>
      simp [bind, Except.bind, pure, Except.pure, evalBinop, applyBinOp, checkArith, Value.asBool]
  case logicalOrShortCircuitRhs =>
    rename_i v se nse
    unf_simp
    rcases Simple.eval σ se with _ | (_ | (_ | _)) <;> rcases Val.eval σ nse with _ | (_ | (_ | _)) <;>
      simp [bind, Except.bind, pure, Except.pure, evalBinop, applyBinOp, checkArith, Value.asBool]
  case memoryStorageCopyUnfold =>
    unf_simp
    cases SPath.resolve σ ‹SPath C _› with
    | error _ => trivial
    | ok rs =>
      simp only [Res.ok_bind]
      cases σ.findStorage rs.1 rs.2 with
      | error _ => trivial
      | ok sv =>
        simp only [Res.ok_bind]
        refine copyStToM_bind_agree ?_ sv _
        agree_tac
  case ifElseUnfold =>
    unf_simp
    cases Val.eval σ ‹Val C .bool› with
    | error _ => trivial
    | ok v =>
      simp only [bind, Except.bind]
      split
      · exact SameOk.of_agree (Prog.run_frame (by agree_tac) _
          (avoids_fresh hse.1.2 hsp.1.2 hie.1.2 hmv.1.2))
      · exact SameOk.of_agree (Prog.run_frame (by agree_tac) _
          (avoids_fresh hse.2 hsp.2 hie.2 hmv.2))
      · trivial

end Solidity
