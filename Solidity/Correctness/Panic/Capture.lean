import Solidity.Syntax.Elab.Panic

/-!
# Capture linkage and guard order of source panics

Two local facts about the generated panic checks, each stated on existing
public names only.

* **Capture linkage.** A capture `p se = value;` evaluates its operand once;
  the local it declares then reads that same value, so a check of the local is
  a check of the operand's value. For `enumCapture` this ties the failed
  membership check to `Panic.Source.OriginV2` at the operand's own value, in
  the data-retaining mode (`panicStmt`) and in the legacy one (`.assert`).
* **Guard order.** In the statement list `Prog.withPanics` emits, the first
  guard that reads `false` decides the panic code, and a guard that halts
  before it decides the halt. The list equations give the emitted order of
  every producer with more than one guard.

Nothing here relates the emitted order to the order in which the unguarded
statement reads its operands; that needs the statement of the module's last
section, which is not proved.
-/

namespace Solidity.Correctness.Panic

open Solidity Semantics Checked

variable {C : Contract} {Γ Γ' : Ctx}

/-- A sequence runs its first statement, then the rest. -/
private theorem cons_run {Γ₁ : Ctx} (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ') (σ : State C Γ) :
    (Prog.cons s P).runR σ = TRun.seq s.runR P.runR σ := rfl

/-! ## Capture linkage -/

/-- A capture evaluates its operand once and declares a local holding it. -/
theorem capture_decl_run (σ : State C Γ) (p : PrimTy) (name : Var) (value : Val C Γ p)
    (v : p.Denote) (read : value.evalT σ = .ok v) :
    (Stmt.declLocal p name (some value)).runR σ =
      .ok ⟨σ.push (t := .val p) v, List.prefix_refl _⟩ := by
  show TRun.declLocal p (some value) σ = _
  simp [TRun.declLocal, read, bind, Except.bind, pure, Except.pure]

/-- A capture whose operand halts halts there: no later check is reached. -/
theorem capture_decl_halt (σ : State C Γ) (p : PrimTy) (name : Var) (value : Val C Γ p)
    (halt : THalt) (read : value.evalT σ = .error halt) :
    (Stmt.declLocal p name (some value)).runR σ = .error halt := by
  show TRun.declLocal p (some value) σ = _
  simp [TRun.declLocal, read, bind, Except.bind]

/-- The captured local reads the value the declaration stored. -/
theorem captured_local_eval (σ : State C Γ) (p : PrimTy) (v : p.Denote) :
    (Val.simple (C := C) (.local (Idx.here (t := .val p) (Γ := Γ)))).evalT
      (σ.push (t := .val p) v) = .ok v := rfl

/-- **Capture linkage**, for every scalar capture: once the operand reads `v`,
the declaration returns and the captured local reads the same `v`. -/
theorem capture_linkage (σ : State C Γ) (p : PrimTy) (name : Var) (value : Val C Γ p)
    (v : p.Denote) (read : value.evalT σ = .ok v) :
    ∃ out, (Stmt.declLocal p name (some value)).runR σ = .ok out ∧
      (Val.simple (.local Idx.here)).evalT out.st = .ok v :=
  ⟨_, capture_decl_run σ p name value v read, captured_local_eval σ p v⟩

/-- The enum membership check of the captured local decides membership of the
operand's value. -/
theorem enum_capture_guard_eval (σ : State C Γ) (v : PrimTy.uint.Denote) (members : Nat)
    (range : PrimTy.uint.inRange (members : Int) = true) :
    (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU members range)).evalT
      (σ.push (t := .val .uint) v) = .ok (decide (v.val < (members : Int))) := by
  simp [cmpU, litU, Val.evalT, BinOp.shortT, Simple.evalT, PrimTy.ofLit, BinOp.evalT,
    BinOp.evalNum, TRes.ofOpt, bind, Except.bind, State.push, TEnv.get]

/-- A failed check of the captured local is an enum conversion failure of the
operand's own value. -/
theorem enum_capture_origin (σ : State C Γ) (v : PrimTy.uint.Denote) (members : Nat)
    (range : PrimTy.uint.inRange (members : Int) = true)
    (failed : (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU members range)).evalT
      (σ.push (t := .val .uint) v) = .ok false) :
    Panic.Source.OriginV2 (.original (.enumConversion members v)) .enumConversion :=
  enum_guard_origin (σ.push (t := .val .uint) v) _ v members range
    (captured_local_eval σ .uint v) failed

/-- **Enum capture, data-retaining mode.** The two statements `enumCapture`
emits in a self-call frame, before any tail: when the operand reads a value
outside the enum, the run halts with `Panic(0x21)` data, and that failure
originates at the operand's own value. -/
theorem enum_capture_panic_run (σ : State C Γ) (name : Var) (value : Val C Γ .uint)
    (v : PrimTy.uint.Denote) (members : Nat)
    (range : PrimTy.uint.inRange (members : Int) = true)
    (tail : Prog C (.val .uint :: Γ) Γ')
    (read : value.evalT σ = .ok v) (outside : ¬v.val < (members : Int)) :
    (Prog.cons (.declLocal .uint name (some value))
      (.cons (panicStmt Panic.Site.enumConversion.code
        (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU members range))) tail)).runR σ =
      .error (THalt.ofData (encodePanic Panic.Site.enumConversion.code)) ∧
    Panic.Source.OriginV2 (.original (.enumConversion members v)) .enumConversion := by
  have failed := enum_capture_guard_eval σ v members range
  rw [decide_eq_false outside] at failed
  refine ⟨?_, enum_capture_origin σ v members range failed⟩
  simp only [cons_run, TRun.seq, capture_decl_run σ .uint name value v read,
    panic_guard_source_failure _ _ failed]
  rfl

/-- **Enum capture, legacy mode.** Outside a data-retaining frame the check
is an assertion: the same failure is the bare panic, with the same origin. -/
theorem enum_capture_assert_run (σ : State C Γ) (name : Var) (value : Val C Γ .uint)
    (v : PrimTy.uint.Denote) (members : Nat)
    (range : PrimTy.uint.inRange (members : Int) = true)
    (tail : Prog C (.val .uint :: Γ) Γ')
    (read : value.evalT σ = .ok v) (outside : ¬v.val < (members : Int)) :
    (Prog.cons (.declLocal .uint name (some value))
      (.cons (.assert
        (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU members range))) tail)).runR σ =
      .error .panic ∧
    Panic.Source.OriginV2 (.original (.enumConversion members v)) .enumConversion := by
  have failed := enum_capture_guard_eval σ v members range
  rw [decide_eq_false outside] at failed
  refine ⟨?_, enum_capture_origin σ v members range failed⟩
  have check : (Stmt.assert (cmpU .lt rfl rfl (.simple (.local Idx.here))
      (litU (C := C) members range))).runR (σ.push (t := .val .uint) v) = .error .panic := by
    show TRun.assert _ _ = _
    simp [TRun.assert, failed, bind, Except.bind]
  simp only [cons_run, TRun.seq, capture_decl_run σ .uint name value v read, check]
  rfl

/-- **Any guard of a captured local.** A capture followed by a generated
check that reads `false` in the state the capture leaves halts with that
check's code: the narrowing and index checks of a captured local are this. -/
theorem capture_guard_panic_run (σ : State C Γ) (p : PrimTy) (name : Var) (value : Val C Γ p)
    (v : p.Denote) (code : Nat) (guard : Val C (.val p :: Γ) .bool)
    (tail : Prog C (.val p :: Γ) Γ') (read : value.evalT σ = .ok v)
    (failed : guard.evalT (σ.push (t := .val p) v) = .ok false) :
    (Prog.cons (.declLocal p name (some value))
      (.cons (panicStmt code guard) tail)).runR σ =
      .error (THalt.ofData (encodePanic code)) := by
  simp only [cons_run, TRun.seq, capture_decl_run σ p name value v read,
    panic_guard_source_failure _ _ failed]
  rfl

/-- A failed unsigned range check of a narrowing capture is a narrow overflow
of the operand's own value. -/
theorem uint_narrow_capture_origin (σ : State C Γ) (v : PrimTy.uint.Denote) (width : Nat)
    (narrow : width < 256)
    (range : PrimTy.uint.inRange (((2 ^ width - 1 : Nat) : Int)) = true)
    (failed : (cmpU .le rfl rfl (.simple (.local Idx.here))
      (litU ((2 ^ width - 1 : Nat) : Int) range)).evalT (σ.push (t := .val .uint) v) =
        .ok false) :
    Panic.Source.OriginV2 (.narrowing (.unsigned width v)) .arithmetic :=
  uint_narrow_guard_origin (σ.push (t := .val .uint) v) _ v width narrow range
    (captured_local_eval σ .uint v) failed

/-- The signed range check of a narrowing capture, likewise. -/
theorem int_narrow_capture_origin (σ : State C Γ) (v : PrimTy.int.Denote) (width : Nat)
    (narrow : width < 256)
    (lo : PrimTy.int.inRange (-((2 ^ (width - 1) : Nat) : Int)) = true)
    (hi : PrimTy.int.inRange ((2 ^ (width - 1) - 1 : Nat) : Int) = true)
    (failed : (andB
      (cmpI .le rfl rfl (litI (-((2 ^ (width - 1) : Nat) : Int)) lo) (.simple (.local Idx.here)))
      (cmpI .le rfl rfl (.simple (.local Idx.here))
        (litI ((2 ^ (width - 1) - 1 : Nat) : Int) hi))).evalT (σ.push (t := .val .int) v) =
        .ok false) :
    Panic.Source.OriginV2 (.narrowing (.signed width v)) .arithmetic :=
  int_narrow_guard_origin (σ.push (t := .val .int) v) _ v width narrow lo hi
    (captured_local_eval σ .int v) failed

/-! ## The elaborated checks read the captured local

`check` and `synth` are well-founded definitions, not `partial`: their
equations rewrite. The newest local is declared under `Var.ofName` of the
capture's printed name, which is what the check's name resolves to, so no
round trip through `FreshNames` is assumed. -/

section Elaborated

private theorem litAt_inRange (Γ : NCtx) (p : PrimTy) (n : Int) (range : p.inRange n = true) :
    litAt C Γ p n = .ok (.lit n range) := by
  unfold litAt
  split
  · rfl
  · rename_i h; rw [range] at h; cases h

private theorem name_const (s : String) (n : Nat) (op : BinOp) :
    (RawExpr.binop op (.name s) (.num n)).constRat? = none := by
  simp [RawExpr.constRat?]

variable [FreshNames]

private theorem num_check (Γ : NCtx) (n : Nat) (p : PrimTy)
    (range : p.inRange (n : Int) = true) :
    check C Γ p (.num n) = .ok (.simple (.lit n range)) := by
  simp [check, litAt_inRange _ _ _ range, bind, Except.bind, pure, Except.pure]

private theorem neg_check (Γ : NCtx) (m : Nat) (lo : PrimTy.int.inRange (-(m : Int)) = true) :
    check C Γ .int (.unop .neg (.num m)) = .ok (.simple (.lit (-(m : Int)) lo)) := by
  unfold check
  simp only [↓reduceIte, litAt_inRange _ _ _ lo, bind, Except.bind, pure, Except.pure]

/-- The newest local, looked up by its own name, is the innermost position. -/
theorem captured_name_idx (Γ : NCtx) (s : String) (p : PrimTy) :
    NCtx.idx ((Var.ofName s, .val p) :: Γ) (Var.ofName s) (.val p) = .ok Idx.here := by
  simp [NCtx.idx, NCtx.find, Except.map]

/-- The capture's name synthesises to a read of the innermost local. -/
theorem captured_name_synth (Γ : NCtx) (s : String) (p : PrimTy) :
    synth C ((Var.ofName s, .val p) :: Γ) (.name s) =
      .ok (.val p (.simple (.local Idx.here))) := by
  simp [synth, NCtx.lookupTy, captured_name_idx, bind, Except.bind, pure, Except.pure]

/-- And checks to it at its type. -/
theorem captured_name_check (Γ : NCtx) (s : String) (p : PrimTy) :
    check C ((Var.ofName s, .val p) :: Γ) p (.name s) = .ok (.simple (.local Idx.here)) := by
  simp [check, checkVia, captured_name_synth, TExpr.toVal?, bind, Except.bind, pure, Except.pure]

/-- The condition `enumCapture` elaborates is the typed membership check of
the captured local. -/
theorem enum_condition_check (Γ : NCtx) (s : String) (members : Nat)
    (range : PrimTy.uint.inRange (members : Int) = true) :
    check C ((Var.ofName s, .val .uint) :: Γ) .bool (.binop .lt (.name s) (.num members)) =
      .ok (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU members range)) := by
  have inner : synth C ((Var.ofName s, .val .uint) :: Γ)
      (.binop .lt (.name s) (.num members)) =
      .ok (.val .bool (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU members range))) := by
    simp [synth, name_const, RawExpr.isLit, captured_name_synth, captured_name_check,
      num_check _ _ _ range, TExpr.toVal?, bind, Except.bind, pure, Except.pure]
    rfl
  simp [check, checkVia, name_const, RawExpr.isLit, inner, TExpr.toVal?, bind, Except.bind,
    pure, Except.pure]

/-- The condition `narrowCheck` elaborates at `uint` on a captured local is
the typed upper-bound check of that local. -/
theorem uint_narrow_condition_check (Γ : NCtx) (s : String) (width : Nat)
    (range : PrimTy.uint.inRange (((2 ^ width - 1 : Nat) : Int)) = true) :
    check C ((Var.ofName s, .val .uint) :: Γ) .bool (inTyCond .uint width (.name s)) =
      .ok (cmpU .le rfl rfl (.simple (.local Idx.here))
        (litU ((2 ^ width - 1 : Nat) : Int) range)) := by
  have inner : synth C ((Var.ofName s, .val .uint) :: Γ)
      (.binop .le (.name s) (.num (2 ^ width - 1))) =
      .ok (.val .bool (cmpU .le rfl rfl (.simple (.local Idx.here))
        (litU ((2 ^ width - 1 : Nat) : Int) range))) := by
    simp [synth, name_const, RawExpr.isLit, captured_name_synth, captured_name_check,
      num_check _ _ _ range, TExpr.toVal?, bind, Except.bind, pure, Except.pure]
    rfl
  simp [inTyCond, check, checkVia, name_const, RawExpr.isLit, inner, TExpr.toVal?, bind,
    Except.bind, pure, Except.pure]

/-- At `int`, the lower bound first, then the upper bound, of that local. -/
theorem int_narrow_condition_check (Γ : NCtx) (s : String) (width : Nat)
    (lo : PrimTy.int.inRange (-((2 ^ (width - 1) : Nat) : Int)) = true)
    (hi : PrimTy.int.inRange ((2 ^ (width - 1) - 1 : Nat) : Int) = true) :
    check C ((Var.ofName s, .val .int) :: Γ) .bool (inTyCond .int width (.name s)) =
      .ok (andB
        (cmpI .le rfl rfl (litI (-((2 ^ (width - 1) : Nat) : Int)) lo)
          (.simple (.local Idx.here)))
        (cmpI .le rfl rfl (.simple (.local Idx.here))
          (litI ((2 ^ (width - 1) - 1 : Nat) : Int) hi))) := by
  have lower : synth C ((Var.ofName s, .val .int) :: Γ)
      (.binop .le (.unop .neg (.num (2 ^ (width - 1)))) (.name s)) =
      .ok (.val .bool (cmpI .le rfl rfl (litI (-((2 ^ (width - 1) : Nat) : Int)) lo)
        (.simple (.local Idx.here)))) := by
    simp only [synth, RawExpr.constRat?, RawExpr.isLit, captured_name_synth,
      captured_name_check, neg_check _ _ lo, TExpr.toVal?, bind, Except.bind, pure, Except.pure]
    simp
    rfl
  have upper : synth C ((Var.ofName s, .val .int) :: Γ)
      (.binop .le (.name s) (.num (2 ^ (width - 1) - 1))) =
      .ok (.val .bool (cmpI .le rfl rfl (.simple (.local Idx.here))
        (litI ((2 ^ (width - 1) - 1 : Nat) : Int) hi))) := by
    simp [synth, name_const, RawExpr.isLit, captured_name_synth, captured_name_check,
      num_check _ _ _ hi, TExpr.toVal?, bind, Except.bind, pure, Except.pure]
    rfl
  simp [inTyCond, check, checkVia, synth, RawExpr.constRat?, RawExpr.isLit, lower, upper,
    TExpr.toVal?, bind, Except.bind, pure, Except.pure]
  rfl

private theorem toNCtx_cons (s : String) (p : PrimTy) (bits : Nat) (Γe : ECtx) :
    ECtx.toNCtx ((s, .val p bits) :: Γe) = (Var.ofName s, .val p) :: ECtx.toNCtx Γe := rfl

/-- **`enumCapture`, run.** Where the operand checks to `value` and the fresh
name is free, the producer emits exactly the capture of `value` and, in the
context that capture leaves, the membership check of the innermost local:
the statements of `enum_capture_panic_run` and `enum_capture_assert_run`. -/
theorem enumCapture_linked (members : Nat) (e : RawExpr) (scope : ElabScope) (Γe : ECtx)
    (k : Nat) (value : Val C (ECtx.toNCtx Γe).ctx .uint)
    (operand : check C (ECtx.toNCtx Γe) .uint e = .ok value)
    (fresh : checkFresh C Γe (toString (Var.fresh "se" k)) = .ok ())
    (range : PrimTy.uint.inRange (members : Int) = true) :
    (enumCapture C members e).runFrom scope (Γe, k) =
      .ok (([.of (ECtx.toNCtx Γe) (.declLocal .uint (.fresh "se" k) (some value)),
             .of (ECtx.toNCtx ((toString (Var.fresh "se" k), .val .uint) :: Γe))
               (if scope.selfFrame || scope.retainFailureData then
                 panicStmt Panic.Site.enumConversion.code
                   (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU members range))
                else .assert (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU members range)))],
            .name (toString (Var.fresh "se" k))),
          ((toString (Var.fresh "se" k), .val .uint) :: Γe, k + 1)) := by
  rw [enumCapture_source]
  simp [ElabM.runFrom, nctx, checkIn, ElabM.lift, captureAs, freshCapture, declare, operand,
    fresh, toNCtx_cons, enum_condition_check _ _ _ range, bind, ReaderT.bind, StateT.bind,
    Except.bind, pure, ReaderT.pure, StateT.pure, Except.pure, ReaderT.run, StateT.run,
    StateT.run', get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, read, readThe,
    MonadReaderOf.read, ReaderT.read, StateT.lift, liftM, monadLift, MonadLift.monadLift,
    Functor.map, Except.map]

/-- **`narrowCapture`, run**, at `uint`: the capture of the narrow operation,
then `narrowCheck`'s statement for the innermost local, in each mode. -/
theorem narrowCapture_uint_linked (e : RawExpr) (width : Nat) (scope : ElabScope) (Γe : ECtx)
    (k : Nat) (value : Val C (ECtx.toNCtx Γe).ctx .uint)
    (operation : checkedNarrow? C Γe e = some (.uint, width)) (narrow : width < 256)
    (operand : check C (ECtx.toNCtx Γe) .uint e = .ok value)
    (fresh : checkFresh C Γe (toString (Var.fresh "se" k)) = .ok ())
    (range : PrimTy.uint.inRange (((2 ^ width - 1 : Nat) : Int)) = true) :
    (narrowCapture C e).runFrom scope (Γe, k) =
      .ok (([.of (ECtx.toNCtx Γe) (.declLocal .uint (.fresh "se" k) (some value)),
             .of (ECtx.toNCtx ((toString (Var.fresh "se" k), .val .uint width) :: Γe))
              (match scope.overflow with
               | some mode => mode.guardStmt
                   (cmpU .le rfl rfl (.simple (.local Idx.here))
                     (litU ((2 ^ width - 1 : Nat) : Int) range))
                   (scope.selfFrame || scope.retainFailureData)
               | none => if scope.selfFrame || scope.retainFailureData then
                   panicStmt Panic.Site.arithmetic.code
                     (cmpU .le rfl rfl (.simple (.local Idx.here))
                       (litU ((2 ^ width - 1 : Nat) : Int) range))
                 else .require
                     (cmpU .le rfl rfl (.simple (.local Idx.here))
                       (litU ((2 ^ width - 1 : Nat) : Int) range)))],
            .name (toString (Var.fresh "se" k))),
          ((toString (Var.fresh "se" k), .val .uint width) :: Γe, k + 1)) := by
  unfold narrowCapture
  simp [narrowCheck_source, ElabM.runFrom, nctx, ctx, checkIn, ElabM.lift, captureAs,
    freshCapture, declare, operand, fresh, operation, Nat.not_le.mpr narrow, toNCtx_cons,
    uint_narrow_condition_check _ _ _ range, bind, ReaderT.bind, StateT.bind, Except.bind,
    pure, ReaderT.pure, StateT.pure, Except.pure, ReaderT.run, StateT.run, StateT.run', get,
    getThe, MonadStateOf.get, StateT.get, set, StateT.set, read, readThe, MonadReaderOf.read,
    ReaderT.read, StateT.lift, liftM, monadLift, MonadLift.monadLift, Functor.map, Except.map]
  first | rfl | (split <;> rfl)

end Elaborated

end Solidity.Correctness.Panic
