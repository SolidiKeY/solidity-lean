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

theorem State.writeStorage_setEnv (σ : State) (x : Var) (b : Binding) (r : Name) (segs : List Seg)
    (v : SVal) : (σ.setEnv x b).writeStorage r segs v =
      (do let τ ← σ.writeStorage r segs v; pure (τ.setEnv x b)) := by
  unfold State.writeStorage
  split
  · exact State.saveStorage_setEnv σ x b r segs _
  all_goals
    simp only [State.findStorage_setEnv, State.saveStorage_setEnv, bind_assoc]

theorem State.checkIndex_setEnv (σ : State) (x : Var) (b : Binding) (r : Name) (segs : List Seg)
    (i : Int) : (σ.setEnv x b).checkIndex r segs i = σ.checkIndex r segs i := by
  unfold State.checkIndex
  simp only [State.findStorage_setEnv]

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

theorem popAt_setEnv (keep : Bool) (r : Name) (segs : List Seg) :
    popAt (σ.setEnv x b) keep r segs = (do let τ ← popAt σ keep r segs; pure (τ.setEnv x b)) := by
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
    Src.pushVal σ (some r) = fun _ => r.value σ >>= fun v => pure v.strip := rfl

open Lean Elab Tactic Meta in
/-- Case on a `Hole`/`MHole`/`VHole` (or a source, target, right-hand side) in context. -/
elab "cases_holes" : tactic => do
  let g ← getMainGoal
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let t ← whnf (← instantiateMVars d.type)
    if [``Hole, ``MHole, ``VHole, ``OpLoc, ``MSrc, ``Src, ``ARhs, ``MRhs, ``MLoc, ``NewLhs].any
        t.isAppOf then
      let gs ← g.cases d.fvarId
      replaceMainGoal (gs.map (·.mvarId)).toList
      return
  throwError "no hole"

set_option hygiene false in
/-- Flatten the four freshness hypotheses to atoms. -/
macro "vars_simp" : tactic => `(tactic|
    simp only [Stmt.vars, Prog.vars, Loc.vars, SPath.vars, Src.vars, Val.vars,
      MPath.vars, MLoc.vars, ARhs.vars, MRhs.vars, MSrc.vars, OpLoc.vars, NewLhs.vars, optVars,
      Hole.fill, MHole.fill, VHole.fill, NewLhs.fill, List.mem_append, List.mem_cons, List.not_mem_nil, not_or,
      List.append_nil] at hse hsp hie hmv)

set_option hygiene false in
/-- Unfold both runs to their reads, moving the reads past the fresh bindings. -/
macro "unf_simp" : tactic => `(tactic|
    simp only [Prog.run, Stmt.run, Hole.fill, MHole.fill, VHole.fill, NewLhs.fill, Src.value,
      Val.eval, MLoc.addr, arrayLen_setEnv, memArrayLen_setEnv, MLoc.addr_setEnv,
      Simple.eval_local, SPath.resolve, Loc.resolve, ARhs.bind, MRhs.bind, MSrc.mval, MLoc.write,
      MPath.mval_var, bind_assoc, pure_bind, bind_pure, envVal_setEnv_self, envRef_setEnv_self,
      aliasPath_setEnv_self, envVal_setEnv_ne, envRef_setEnv_ne, aliasPath_setEnv_ne,
      Var.fresh.injEq, String.reduceEq, false_and, MVal.asRef_ref, State.saveStorage_setEnv,
      State.writeStorage_setEnv, State.checkIndex_setEnv, State.writeStorage_toSVal,
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

/-- Two runs that read the same first, then continue alike. -/
theorem SameOk.bind_same {ns : List Var} {α : Type} (r : Res α) {f g : α → Res State}
    (h : ∀ a, SameOk ns (f a) (g a)) : SameOk ns (r >>= f) (r >>= g) := by
  cases r with
  | error _ => trivial
  | ok a => exact h a

/-! ## Calls

A call binds its arguments as they were read in the caller's state; its
inlining binds them one after another.  The two agree when every argument is
ready (`Arg.ready`): a literal, or a local no earlier parameter rebinds. -/

/-- A block of two parts runs the first, then the second. -/
theorem Prog.run_append (σ : State) :
    (P Q : Prog C) → Prog.run σ (P ++ Q) = (do Prog.run (← Prog.run σ P) Q)
  | [], Q => by simp [Prog.run]
  | s :: P, Q => by
    simp only [List.cons_append, Prog.run, bind_assoc]
    cases s.run σ with
    | error _ => rfl
    | ok τ => exact Prog.run_append τ P Q

/-- The parameters declared one after another are the call's binding. -/
theorem Arg.decls_run : (args : List (Arg C)) → ∀ σ, Prog.run σ (args.map Arg.decl) = Arg.bindSeq args σ
  | [], _ => rfl
  | a :: as, σ => by
    simp only [List.map_cons, Prog.run, Arg.decl, Stmt.run, Arg.bindSeq, bind_assoc, pure_bind]
    cases a.e.eval σ with
    | error _ => rfl
    | ok v => exact Arg.decls_run as _

/-- **A call runs as its inlining** (`functionBodyExpand`). -/
theorem Stmt.run_call_expand (σ : State) {f : Name} {args : List (Arg C)}
    {hsep : Arg.separatedFrom [] args = true} {ret : CallRet} {body : List (Stmt C)} :
    (Stmt.call f args hsep ret body).run σ = Prog.run σ (Stmt.expandBody args ret body) := by
  simp only [Stmt.expandBody, List.append_assoc, Prog.run_append, Arg.decls_run, Stmt.run]
  cases Arg.bindSeq args σ with
  | error _ => rfl
  | ok σ₁ =>
    simp only [bind, Except.bind]
    have he : Prog.run σ₁ (CallRet.decl (C := C) ret) = pure (ret.enter σ₁) := by
      cases ret <;> rfl
    rw [he]
    simp only [pure, Except.pure]
    cases Prog.run (ret.enter σ₁) body with
    | error _ => rfl
    | ok σ₂ =>
      rcases ret with _ | ⟨p, r, _ | y⟩ <;>
        simp [CallRet.leave, CallRet.result, Prog.run, Stmt.run, Val.eval, bind, Except.bind,
          pure, Except.pure] <;> split <;> rfl

theorem Arg.mem_vars {y : Var} {a : Arg C} :
    {args : List (Arg C)} → a ∈ args → y ∈ a.e.vars → y ∈ Arg.vars args
  | b :: bs, hm, hy => by
    rcases List.mem_cons.1 hm with rfl | hm
    · simp [Arg.vars, hy]
    · simp [Arg.vars, Arg.mem_vars hm hy]

theorem Arg.x_mem_vars {a : Arg C} : {args : List (Arg C)} → a ∈ args → a.x ∈ Arg.vars args
  | b :: bs, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · simp [Arg.vars]
    · simp [Arg.vars, Arg.x_mem_vars hm]

theorem Arg.firstNonSimple_spec {a : Arg C} :
    {args : List (Arg C)} → Arg.firstNonSimple args = some a → a ∈ args ∧ a.e.isSimple = false
  | [], h => nomatch h
  | b :: bs, h => by
    simp only [Arg.firstNonSimple] at h
    split at h
    · exact ⟨List.mem_cons_of_mem _ (Arg.firstNonSimple_spec h).1, (Arg.firstNonSimple_spec h).2⟩
    · cases h; exact ⟨List.mem_cons_self, Bool.eq_false_iff.2 ‹_›⟩

/-- In a separated call, an argument that is not simple reads none of the
parameters bound before it. -/
theorem Arg.separatedFrom_avoids {a : Arg C} {y : Var} :
    {bound : List Var} → {args : List (Arg C)} → Arg.separatedFrom bound args = true →
      a ∈ args → a.e.isSimple = false → y ∈ bound → y ∉ a.e.vars
  | bound, b :: bs, h, hm, hs, hy => by
    simp only [Arg.separatedFrom, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
      Bool.not_eq_true'] at h
    rcases List.mem_cons.1 hm with rfl | hm
    · rcases h.1 with h1 | h1
      · simp_all
      · intro hv; have := h1 y hv; simp_all
    · exact Arg.separatedFrom_avoids h.2 hm hs (List.mem_cons_of_mem _ hy)

/-- Binding a separated call's arguments, the first argument that is not
simple read beforehand into `se` and passed as `se`, binds what the call
does, off the fresh names. -/
theorem Arg.bindSeq_capture {ns : List Var} {se : Var} (hse : se ∈ ns) {v : Value} :
    {bound : List Var} → {args : List (Arg C)} → Arg.separatedFrom bound args = true →
      Avoids (Arg.vars args) ns → {a : Arg C} → Arg.firstNonSimple args = some a →
      ∀ {σ τ : State}, EnvAgreeExcept ns τ σ → (Simple.local se : Simple C a.p).eval τ = .ok v →
        a.e.eval σ = .ok v →
        ResultsAgree ns (Arg.bindSeq (Arg.captureFirst se args) τ) (Arg.bindSeq args σ)
  | _, [], _, _, _, h, _, _, _, _, _ => nomatch h
  | bound, b :: bs, hsep, hav, a, h, σ, τ, hag, hτ, hσ => by
    have hsep' := hsep
    simp only [Arg.separatedFrom, Bool.and_eq_true] at hsep'
    simp only [Arg.firstNonSimple] at h
    simp only [Arg.captureFirst]
    split
    · rename_i hb
      simp only [hb, if_true] at h
      simp only [Arg.bindSeq]
      rw [b.e.eval_frame hag (fun x hx => hav x (by simp [Arg.vars, hx]))]
      cases b.e.eval σ with
      | error _ => exact rfl
      | ok w =>
        simp only [Res.ok_bind]
        have hbx : se ≠ b.x := fun he => hav se (by simp [Arg.vars, he]) hse
        have ha := Arg.firstNonSimple_spec h
        refine Arg.bindSeq_capture (v := v) hse hsep'.2 (fun x hx => hav x (by simp [Arg.vars, hx])) h
          (EnvAgreeExcept.setEnv_both hag _ _) ?_ ?_
        · rw [Simple.eval_setEnv (by simp [Simple.vars, Ne.symm hbx])]; exact hτ
        · rw [Val.eval_setEnv (Arg.separatedFrom_avoids hsep'.2 ha.1 ha.2 List.mem_cons_self)]
          exact hσ
    · rename_i hb
      simp only [hb] at h
      cases h
      simp only [Arg.bindSeq]
      have hτ' : (Val.simple (Simple.local se) : Val C b.p).eval τ = .ok v := hτ
      rw [hτ', hσ]
      simp only [Res.ok_bind]
      exact Arg.bindSeq_frame bs (fun x hx => hav x (by simp [Arg.vars, hx]))
        (EnvAgreeExcept.setEnv_both hag _ _)

/-- A separated call whose first argument that is not simple fails to
evaluate fails too. -/
theorem Arg.bindSeq_error {e : Halt} :
    {bound : List Var} → {args : List (Arg C)} → Arg.separatedFrom bound args = true →
      {a : Arg C} → Arg.firstNonSimple args = some a → ∀ {σ : State}, a.e.eval σ = .error e →
        ∃ e', Arg.bindSeq args σ = .error e'
  | _, [], _, _, h, _, _ => nomatch h
  | bound, b :: bs, hsep, a, h, σ, he => by
    simp only [Arg.separatedFrom, Bool.and_eq_true] at hsep
    simp only [Arg.firstNonSimple] at h
    simp only [Arg.bindSeq]
    split at h
    · cases b.e.eval σ with
      | error e' => exact ⟨e', rfl⟩
      | ok w =>
        have ha := Arg.firstNonSimple_spec h
        refine Arg.bindSeq_error (e := e) hsep.2 h ?_
        rw [Val.eval_setEnv (Arg.separatedFrom_avoids hsep.2 ha.1 ha.2 List.mem_cons_self)]
        exact he
    · cases h
      exact ⟨e, by simp [he, bind, Except.bind]⟩

/-- `functionCallArgCapture`: the capture reads the argument where the call
would, so the two runs differ only on the fresh local. -/
theorem Stmt.call_capture_sound {k : Nat} {f : Name} {args : List (Arg C)}
    {hsep : Arg.separatedFrom [] args = true} {ret : CallRet}
    {body : List (Stmt C)} {a : Arg C} (h : Arg.firstNonSimple args = some a)
    (hs : Avoids (Stmt.call f args hsep ret body).vars (freshVars k)) (σ : State) :
    SameOk (freshVars k)
      (Prog.run σ [.declLocal a.p (.fresh "se" k) (some a.e),
        .call f (Arg.captureFirst (.fresh "se" k) args) (Arg.separatedFrom_captureFirst hsep) ret body])
      ((Stmt.call f args hsep ret body).run σ) := by
  have hse : Var.fresh "se" k ∈ freshVars k := by simp [freshVars]
  have hargs : Avoids (Arg.vars args) (freshVars k) := fun x hx => hs x (by simp [Stmt.vars, hx])
  have hav : Var.fresh "se" k ∉ a.e.vars := fun hv =>
    hargs _ (Arg.mem_vars (Arg.firstNonSimple_spec h).1 hv) hse
  simp only [Prog.run, bind_pure]
  simp only [Stmt.run, bind_assoc, pure_bind]
  cases hev : a.e.eval σ with
  | error e =>
    obtain ⟨e', he'⟩ := Arg.bindSeq_error hsep h hev
    simp [bind, Except.bind, he']
  | ok v =>
    simp only [Res.ok_bind]
    have hag : EnvAgreeExcept (freshVars k) (σ.setEnv (.fresh "se" k) (.val v)) σ :=
      (EnvAgreeExcept.refl (freshVars k) σ).setEnv_left hse _
    have hτ : (Simple.local (.fresh "se" k) : Simple C a.p).eval (σ.setEnv (.fresh "se" k) (.val v))
        = .ok v := by
      simp [Simple.eval, State.getEnv, State.setEnv, SemanticsProperties.lookupBy_setBy_self]; rfl
    refine SameOk.of_agree (ResultsAgree.bind (Arg.bindSeq_capture hse hsep hargs h hag hτ hev)
      fun _ _ h₁ => ResultsAgree.bind (Prog.run_frame (CallRet.enter_frame h₁ ret) body ?_)
        fun _ _ h₂ => CallRet.leave_frame h₂ ret ?_)
    · exact fun x hx => hs x (by simp [Stmt.vars, hx])
    · exact fun x hx => hs x (by simp [Stmt.vars, hx])

set_option maxHeartbeats 4000000 in
theorem Taclet.sound_unfold {k : Nat} {m : Modality} {s : Stmt C} {P : Prog C}
    (d : Taclet C k m s (.unfold P)) (hs : Avoids s.vars (freshVars k)) :
    ∀ σ, SameOk (freshVars k) (Prog.run σ P) (s.run σ) := by
  have hse : Var.fresh "se" k ∉ s.vars := fun h => hs _ h (by simp [freshVars])
  have hsp : Var.fresh "sp" k ∉ s.vars := fun h => hs _ h (by simp [freshVars])
  have hie : Var.fresh "ie" k ∉ s.vars := fun h => hs _ h (by simp [freshVars])
  have hmv : Var.fresh "mv" k ∉ s.vars := fun h => hs _ h (by simp [freshVars])
  cases d
  case functionBodyExpand => intro σ; rw [Stmt.run_call_expand σ]; exact SameOk.self _ _
  all_goals clear hs
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
  -- a memory `delete` past a fresh binding: the reset reads and allocates alike
  case memoryFieldDelete_unfold_leftFst =>
    unf_simp
    exact SameOk.bind_same _ fun _ => SameOk.bind_same _ fun _ =>
      SameOk.of_agree (memClear_agree (by agree_tac) _ _)
  case memoryIndexDelete_unfold_leftFst =>
    unf_simp
    exact SameOk.bind_same _ fun _ => SameOk.bind_same _ fun _ => SameOk.bind_same _ fun _ =>
      SameOk.bind_same _ fun _ => SameOk.of_agree (memClear_agree (by agree_tac) _ _)
  case memoryIndexDeleteNonSimpleIndexCapture =>
    unf_simp
    cases Val.eval σ ‹Val C .uint› with
    | error _ =>
      cases envRef σ ‹Var› <;> trivial
    | ok v =>
      simp only [Res.ok_bind]
      cases envRef σ ‹Var› with
      | error _ => trivial
      | ok id =>
        simp only [Res.ok_bind]
        exact SameOk.bind_same _ fun _ => SameOk.of_agree (memClear_agree (by agree_tac) _ _)
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
