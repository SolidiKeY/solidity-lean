import Solidity.Correctness.Lowering.Sim.Coverage.SpellingObstruction
import Solidity.Correctness.Lowering.Sim.Coverage.BooleanCoverage
import Solidity.Correctness.Lowering.Sim.Coverage.Alignment
import Solidity.Correctness.Lowering.Sim.Coverage.LoweringReceipt
import Solidity.Examples.Lowering.Sim.Match
import Solidity.Correctness.Lowering.Sim.Expr.Operand
import Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip.Leaves

/-!
# Coverage obstructions and independent smoke facts

The requested use of `diagram_total` cannot be supplied for the frozen v1
statement: the first example refutes it under the authorized kernel hypothesis.
The second checks that versioned production retains the v1 receipt; the third
shows that caller placement alone does not repair the frozen spelling relation.
The final checks establish decoding, alignment, acceptance of the existing
materialized program, and actual lowering of the smoke separately. The generated
flag declaration, condition capture, captured assignment, and flag write have
exact elaboration receipts below; the complete loop production receipt is still outstanding.
-/
namespace Solidity.Examples.Lowering.Sim.Coverage

open Solidity.Goals.Shrink.Lowering
open Solidity.Correctness.Lowering.Sim
open Solidity.Correctness.Lowering.Sim.Coverage

example (hk : Solidity.Goals.elabKernelTotal) :
    ¬ @Diagram.Total productionNames diagram := not_total hk

example (hk : Solidity.Goals.elabKernelTotal) :
    @Production productionNames uncheckedBody uncheckedEmitted :=
  (unchecked_production hk).toProduction

example (hk : Solidity.Goals.elabKernelTotal) :
    ¬ @TotalV2 productionNames diagram := not_totalV2 hk

/-- The existing decoder computes the smoke’s actual Source resolution. -/
theorem smoke_decoded
    (out : Solidity.Correctness.Lowering.Checker.Output Match.C [.val .bool, .val .bool]) :
    Solidity.Correctness.Lowering.Total.Decode.decode (request Match.body (Match.emitted out)) =
      some (Solidity.Correctness.Lowering.Total.SourceProgram.ofStmt Match.body.input.resolved) := by
  rfl

/-- The existing smoke supplies an aligned map from its actual typing, before
any restriction predicate or successful-production premise is selected. -/
example (out : Solidity.Correctness.Lowering.Checker.Output Match.C [.val .bool, .val .bool]) :
    ∃ m : Solidity.Lowering.V07.ContextMap Match.body.ctx
      (request Match.body (Match.emitted out)).context.ctx, Aligned m :=
  spells_aligned (r := request Match.body (Match.emitted out))
    (s := Solidity.Correctness.Lowering.Total.SourceProgram.ofStmt Match.body.input.resolved)
    (Solidity.Correctness.Lowering.Total.decode_spells (smoke_decoded out))

/-- Acceptance of the existing materialized while/break program. This is a
kernel check of that exact program, not its still-needed production receipt. -/
example : Solidity.Backend.AbiWorld.PublicCompilerTotal.ProgOk []
    Solidity.Correctness.Lowering.Checker.IntrinsicProbe.actual.program.2 := by
  repeat constructor

/-- The exact smoke has an actual lowering receipt, independently of the
still-needed elaboration receipt. -/
example : ∃ (out : List RawStmt)
    (after : Solidity.Correctness.Lowering.Checker.Snapshot),
    (((@lowerAt productionNames none Match.raw).run Match.body.input.scope).run
      Match.body.input.before.locals).run Match.body.input.before.memo =
        .ok ((out, after.locals), after.memo) := by
  letI : FreshNames := productionNames
  have h := Solidity.Correctness.Lowering.Total.Coverage.Template.whileBreak
    none (.assign (.name "i") (.name "a")) Match.body.input.before
    (Solidity.Correctness.Lowering.Total.Coverage.hasIncDec_assign _ _)
  exact ⟨_, _, lowerAt_of_lowersTo (h.lowers Match.body.input.scope)⟩

/-- The actual `while (i = a) break;` smoke belongs to the selected syntax
boundary, independently of decoder success and production receipts. -/
theorem smoke_in_domain (out : Solidity.Correctness.Lowering.Checker.Output Match.C [.val .bool, .val .bool]) :
    BooleanDomain.Input Match.body (Match.emitted out) := by
  refine ⟨rfl, rfl, rfl, rfl, ["i", "a"], _, _, rfl, rfl, ?_, ?_⟩
  · exact .assign (by decide) (.name (by decide))
  · exact .cons .brk .nil

/-- Use the general raw-syntax decoding theorem on the exact selected smoke. -/
example (out : Solidity.Correctness.Lowering.Checker.Output Match.C [.val .bool, .val .bool]) :
    ∃ t, Solidity.Correctness.Lowering.Total.Decode.items .body Match.body.input.raw = some t :=
  (smoke_in_domain out).syntax_decoded

/-- The general expression theorem runs Source inference on the existing
smoke condition; it does not assert statement or production completeness. -/
example : ∃ t, Solidity.Correctness.Lowering.Total.Spells.Expr
    (.assign (.name "i") (.name "a")) t ∧
    ∃ d : Source.Typed (Match.context.at Match.names) t .bool,
      Source.Typed.infer (Match.context.at Match.names) t = some ⟨.bool, d⟩ := by
  obtain ⟨t, ht, hi⟩ := BooleanDomain.Expr.inferred
    (Γ := Match.context.at Match.names) (names := ["i", "a"])
    (raw := .assign (.name "i") (.name "a")) rfl
    (BooleanDomain.Expr.assign (by decide) (.name (by decide)))
  obtain ⟨d, hd⟩ := hi.2 (t.nodes.length + 1) (Nat.lt_succ_self _)
  exact ⟨t, ht, d, hd⟩

/-- The general grammar theorem decodes the exact smoke to a singleton
resolved statement, without relying on the precomputed smoke decoder proof. -/
example (out : Solidity.Correctness.Lowering.Checker.Output Match.C [.val .bool, .val .bool]) :
    ∃ (C : Source.Ctx) (L : List (String × Source.STy)) (s : Source.Syn (.stmt .body))
      (d : Source.StmtD C L s L),
      Solidity.Correctness.Lowering.Total.Decode.decode (request Match.body (Match.emitted out)) =
        some (Solidity.Correctness.Lowering.Total.SourceProgram.ofStmt d.toR) :=
  (smoke_in_domain out).decoded_stmt

/-- Restricted coverage specializes to the existing Match smoke. The actual
production receipt is still a hypothesis, not a nonvacuity claim. -/
example (out : Solidity.Correctness.Lowering.Checker.Output Match.C [.val .bool, .val .bool])
    (production : @ProductionV2 productionNames Match.body (Match.emitted out))
    (accepted : Accepted (Match.emitted out)) :
    ∃ b' : Body, b'.SameInput Match.body ∧ ∃ m, diagram.Assoc b' (Match.emitted out) m :=
  diagram_total_boolean Match.body (Match.emitted out) (smoke_in_domain out) production accepted

private theorem narrow_bool : narrowTy? "bool" = none := by
  rw [Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip.narrowTy?_mk]; rfl
private theorem bytes_bool : bytesTy? "bool" = none := by
  rw [Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip.bytesTy?_mk]; rfl
private theorem fn_bool : fnTy? "bool" = false := by
  rw [Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws.fnTy?_mk]; rfl

private theorem bool_decl_type : elabDeclTy Match.C (.named "bool") = .ok (.prim .bool, 256) := by
  unfold elabDeclTy
  simp only [narrow_bool, bytes_bool, fn_bool, Bool.false_eq_true, if_false]
  rw [elabTy]
  rfl

private theorem bool_checked (Γ : NCtx) : check Match.C Γ .bool (.bool false) =
    .ok (.simple (.bool false)) := by
  rw [check, checkVia, synth]
  all_goals first | rfl | (intros; contradiction)

private theorem bool_rows : bytesRowsOf Match.C (.named "bool") = .ok [] := by
  simp only [bytesRowsOf, fn_bool, bytes_bool, Bool.false_eq_true, if_false]
  rfl

/-- The exact first elaborated instruction of the lowered Match smoke. -/
def smokeFlagProgram : SProg Match.C :=
  letI : FreshNames := productionNames
  [.of (ECtx.toNCtx Match.locals)
    (.declLocal .bool (Var.ofName "brk0") (some (.simple (.bool false))))]

/-- The actual declaration arm preserves the counter and memo and adds only
the generated Boolean flag. The enclosing block sets `top := false`.
Its equation comes from the kernel hypothesis. -/
theorem smoke_flag (hk : Solidity.Goals.elabKernelTotal) :
    (((@elabStmtP Match.C productionNames
      (.decl (.named "bool") "brk0" (some (.bool false)))).run { funs := [], top := false }).run
      (Match.locals, 1)).run {} =
      .ok ((smokeFlagProgram, (("brk0", .val .bool) :: Match.locals, 1)), {}) := by
  letI : FreshNames := productionNames
  have hp : elabStmtP Match.C = elabStmtPWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.1
  rw [hp]
  conv => lhs; whnf
  simp only [RawStmt.mapExprsM, Option.mapM, fnPure_other]
  conv => lhs; whnf
  simp only [bytesStmt, RawStmt.mapExprsM, Option.mapM, bytesPure_other]
  conv => lhs; whnf
  simp only [RawStmt.exprs, Option.toList, List.map_cons, List.map_nil, List.forIn_cons, List.forIn_nil,
    Bool.false_eq_true, if_false, narrowWholeUse?_other]
  conv => lhs; whnf
  simp only [narrowPure_other]
  conv => lhs; whnf
  rw [(hk.1 Match.C).1.2.2.2.1]
  unfold elabStmt1With
  dsimp only
  rw [bool_decl_type]
  dsimp only [ElabM.lift, StateT.lift, ReaderT.run, StateT.run, Bind.bind,
    ReaderT.bind, StateT.bind, Pure.pure, ReaderT.pure, StateT.pure, Except.bind, Except.pure]
  simp only [Option.mapM, checkIn, bool_checked, bool_rows]
  conv => lhs; whnf
  rfl

private theorem synth_bool [FreshNames] (C : Contract) (Γ : NCtx) (b : Bool) :
    synth C Γ (.bool b) = .ok (.val .bool (.simple (.bool b))) := by
  rw [synth]
  rfl

private theorem nctx_run [FreshNames] (sc : ElabScope) (st : ECtx × Nat) (memo : CallMemo) :
    (nctx : ElabM NCtx) sc st memo = .ok ((ECtx.toNCtx st.1, st), memo) := rfl

private theorem hoist_assign_bool [FreshNames] (C : Contract)
    (H : RawExpr → ElabM (SProg C × RawExpr)) (x : String) (b : Bool)
    (hx : H (.name x) = pure ([], .name x))
    (hb : H (.bool b) = pure ([], .bool b)) :
    hoistAssignWith C H (.name x) (.bool b) = pure ([], .assign (.name x) (.bool b)) := by
  change (show ElabM (SProg C × RawStmt) from do
    let (P, l, r) ← (do
      let (P, r) ← hoistTopWith C H (.bool b)
      let (P, r) ← do
        let Γ ← nctx
        let rec shape : RawExpr → RawExpr
          | .index e _ => .index (shape e) (.num 0)
          | .field e f => .field (shape e) f
          | e => e
        match synth C Γ (shape (.name x)), synth C Γ r with
        | .ok (.mpath (.ref _) (.loc _)), .ok (.path (.ref R) sp) =>
          match hm : (Ty.ref R).mapFree with
          | true =>
            let v ← captureRef C "mv" (.mem R) r
            pure (P ++ [SStmt.of Γ (.declMem R v (some (.copy sp hm)) rfl hm)], RawExpr.name (toString v))
          | false => throw "a copy into memory of a type that holds a mapping"
        | _, _ => pure (P, r)
      let (Pc, r) ← if (RawExpr.name x).hasIncDec then captureExpr C r else pure ([], r)
      let (Q, l) ← H (.name x)
      pure (P ++ Pc ++ Q, l, r))
    pure (P, RawStmt.assign l r)) = _
  have htop : hoistTopWith C H (.bool b) = H (.bool b) := rfl
  rw [htop, hb]
  have hi : (RawExpr.name x).hasIncDec = false := by
    unfold RawExpr.hasIncDec
    rw [RawExpr.any]
    rfl
  simp only [pure_bind, synth_bool, hx, hi, Bool.false_eq_true, if_false,
    List.nil_append, List.append_nil]
  funext sc st memo
  conv => lhs; whnf
  dsimp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [nctx_run]
  dsimp only [Pure.pure, ReaderT.pure, StateT.pure, Except.pure]
  generalize hs : synth C (ECtx.toNCtx st.1) _ = q
  cases q with
  | error e => rfl
  | ok t =>
    cases t with
    | mpath T p => cases T <;> cases p <;> rfl
    | _ => rfl

private theorem kernel_hoist_assign_bool [FreshNames] (hk : Solidity.Goals.elabKernelTotal)
    (C : Contract) (x : String) (b : Bool) :
    hoistAssign C (.name x) (.bool b) = pure ([], .assign (.name x) (.bool b)) := by
  have hh : hoist C = hoistWith C (elabRec C ()) := (hk.1 C).1.2.2.2.2.2
  change hoistAssignWith C (hoist C) (.name x) (.bool b) = _
  apply hoist_assign_bool
  · rw [hh]
    exact Solidity.Correctness.Lowering.Sim.hoist_name C (elabRec C ()) x
  · rw [hh]
    exact Solidity.Correctness.Lowering.Sim.hoist_bool C (elabRec C ()) b

private theorem check_bool [FreshNames] (C : Contract) (Γ : NCtx) (b : Bool) :
    check C Γ .bool (.bool b) = .ok (.simple (.bool b)) := by
  rw [check, checkVia, synth_bool]
  all_goals first | rfl | (intros; contradiction)

private theorem synth_second_bool [FreshNames] (C : Contract) (Γ : NCtx) (x y : String)
    (h : Var.ofName y ≠ Var.ofName x) :
    synth C ((Var.ofName y, .val .bool) :: (Var.ofName x, .val .bool) :: Γ) (.name x) =
      .ok (.val .bool (.simple (.local (.there .here)))) := by
  rw [synth]
  simp only [NCtx.lookupTy, if_neg h, NCtx.idx, NCtx.find, dif_neg h]
  rfl

/-- The named locals used by the body after its condition capture. -/
def smokeCapturedLocals : ECtx :=
  ("se1", .val .bool) :: ("brk0", .val .bool) :: Match.locals

/-- The flag write at the post-capture context. -/
def smokeSetFlagProgram : SProg Match.C :=
  letI : FreshNames := productionNames
  [.of (ECtx.toNCtx smokeCapturedLocals)
    (.assignLocal (.there .here) (.simple (.bool true)))]

private theorem capture_ne_flag :
    @Var.ofName productionNames "se1" ≠ @Var.ofName productionNames "brk0" := by decide

private theorem synth_flag :
    @synth Match.C productionNames (@ECtx.toNCtx productionNames smokeCapturedLocals) (.name "brk0") =
      .ok (.val .bool (.simple (.local (.there .here)))) := by
  letI : FreshNames := productionNames
  exact synth_second_bool Match.C (ECtx.toNCtx Match.locals) "brk0" "se1" capture_ne_flag

private theorem narrow_flag (sc : ElabScope) (k : Nat) (memo : CallMemo) :
    @narrowPost Match.C productionNames (.name "brk0") (.bool true) sc (smokeCapturedLocals, k) memo =
      .ok (([], (smokeCapturedLocals, k)), memo) := by
  rfl

/-- The generated flag write at its post-capture locals keeps the full state. -/
theorem smoke_set_flag (hk : Solidity.Goals.elabKernelTotal) (k : Nat) :
    (((@elabStmtP Match.C productionNames (.assign (.name "brk0") (.bool true))).run
      { funs := [], top := false }).run (smokeCapturedLocals, k)).run {} =
      .ok ((smokeSetFlagProgram, (smokeCapturedLocals, k)), {}) := by
  letI : FreshNames := productionNames
  have hp : elabStmtP Match.C = elabStmtPWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.1
  have ha : (elabRec Match.C ()).hoistAssign (.name "brk0") (.bool true) =
      pure ([], .assign (.name "brk0") (.bool true)) :=
    kernel_hoist_assign_bool hk Match.C "brk0" true
  rw [hp]
  conv => lhs; whnf
  simp only [RawStmt.mapExprsM, fnPure_other]
  conv => lhs; whnf
  simp only [bytesStmt, RawStmt.mapExprsM, bytesPure_other]
  conv => lhs; whnf
  simp only [RawStmt.exprs, List.map_cons, List.map_nil, List.forIn_cons, List.forIn_nil,
    Bool.false_eq_true, if_false, narrowWholeUse?_other, narrowWholeUse?_name]
  conv => lhs; whnf
  simp only [narrowPure_other]
  conv => lhs; whnf
  rw [(hk.1 Match.C).1.2.2.2.2.1]
  unfold hoistStmtWith
  dsimp only
  rw [ha]
  dsimp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind, Pure.pure,
    ReaderT.pure, StateT.pure, Except.pure]
  rw [nctx_run]
  conv => lhs; whnf
  dsimp only
  rw [(hk.1 Match.C).1.2.2.2.1]
  unfold elabStmt1With
  dsimp only
  conv => lhs; whnf
  dsimp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [narrow_flag]
  dsimp only
  unfold synthM
  dsimp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [nctx_run]
  dsimp only
  rw [synth_flag]
  dsimp only [ElabM.lift, StateT.lift, Bind.bind, ReaderT.bind, StateT.bind,
    Pure.pure, ReaderT.pure, StateT.pure, Except.bind, Except.pure]
  simp only [checkIn, check_bool]
  rfl


/-- The condition captures `a` before assigning it to `i`. -/
def smokeCaptureProgram : SProg Match.C :=
  letI : FreshNames := productionNames
  [.of (ECtx.toNCtx (("brk0", .val .bool) :: Match.locals))
    (.declLocal .bool (Var.ofName "se1")
      (some (.simple (.local (.there (.there .here))))))]

private theorem synth_capture_a :
    @synth Match.C productionNames
      (@ECtx.toNCtx productionNames (("brk0", .val .bool) :: Match.locals)) (.name "a") =
      .ok (.val .bool (.simple (.local (.there (.there .here))))) := by
  rw [synth]
  rfl

/-- Exact capture of `a` in the lowered smoke, including the fresh counter. -/
theorem smoke_capture :
    @captureExpr Match.C productionNames (.name "a")
      { funs := [], top := false } ((("brk0", .val .bool) :: Match.locals), 1) {} =
      .ok (((smokeCaptureProgram, .name "se1"), (smokeCapturedLocals, 2)), {}) := by
  unfold captureExpr
  conv => lhs; whnf
  unfold synthM
  dsimp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [nctx_run]
  dsimp only
  rw [synth_capture_a]
  rfl

private theorem hoist_assign_names_run [FreshNames] (C : Contract)
    (H : RawExpr → ElabM (SProg C × RawExpr)) (x y : String)
    (hx : H (.name x) = pure ([], .name x))
    (hy : H (.name y) = pure ([], .name y))
    (sc : ElabScope) (st : ECtx × Nat) (memo : CallMemo)
    (v : Val C (ECtx.toNCtx st.1).ctx .bool)
    (hs : synth C (ECtx.toNCtx st.1) (.name x) = .ok (.val .bool v)) :
    hoistAssignWith C H (.name x) (.name y) sc st memo =
      .ok ((([], .assign (.name x) (.name y)), st), memo) := by
  have expand : hoistAssignWith C H (.name x) (.name y) = (show ElabM (SProg C × RawStmt) from do
    let (P, l, r) ← (do
      let (P, r) ← hoistTopWith C H (.name y)
      let (P, r) ← do
        let Γ ← nctx
        match synth C Γ (.name x), synth C Γ r with
        | .ok (.mpath (.ref _) (.loc _)), .ok (.path (.ref R) sp) =>
          match hm : (Ty.ref R).mapFree with
          | true =>
            let v ← captureRef C "mv" (.mem R) r
            pure (P ++ [SStmt.of Γ (.declMem R v (some (.copy sp hm)) rfl hm)], RawExpr.name (toString v))
          | false => throw "a copy into memory of a type that holds a mapping"
        | _, _ => pure (P, r)
      let (Pc, r) ← if (RawExpr.name x).hasIncDec then captureExpr C r else pure ([], r)
      let (Q, l) ← H (.name x)
      pure (P ++ Pc ++ Q, l, r))
    pure (P, RawStmt.assign l r)) := by rfl
  have htop : hoistTopWith C H (.name y) = H (.name y) := rfl
  have hi : (RawExpr.name x).hasIncDec = false := by
    unfold RawExpr.hasIncDec
    rw [RawExpr.any]
    rfl
  rw [expand, htop, hy]
  simp only [pure_bind, hx, hi, Bool.false_eq_true, if_false,
    List.nil_append, List.append_nil]
  conv => lhs; whnf
  dsimp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [nctx_run]
  dsimp only
  rw [hs]
  rfl

private theorem synth_smoke_i :
    @synth Match.C productionNames (@ECtx.toNCtx productionNames smokeCapturedLocals) (.name "i") =
      .ok (.val .bool (.simple (.local (.there (.there .here))))) := by
  rw [synth]
  rfl

private theorem synth_smoke_se :
    @synth Match.C productionNames (@ECtx.toNCtx productionNames smokeCapturedLocals) (.name "se1") =
      .ok (.val .bool (.simple (.local .here))) := by
  rw [synth]
  rfl

private theorem smoke_hoist_write (hk : Solidity.Goals.elabKernelTotal)
    (sc : ElabScope) (k : Nat) (memo : CallMemo) :
    @hoistAssign Match.C productionNames (.name "i") (.name "se1") sc
      (smokeCapturedLocals, k) memo =
      .ok ((([], .assign (.name "i") (.name "se1")), (smokeCapturedLocals, k)), memo) := by
  letI : FreshNames := productionNames
  have hn (x : String) : hoist Match.C (.name x) = pure ([], .name x) := by
    have hh : hoist Match.C = hoistWith Match.C (elabRec Match.C ()) :=
      (hk.1 Match.C).1.2.2.2.2.2
    rw [hh]
    exact Solidity.Correctness.Lowering.Sim.hoist_name Match.C (elabRec Match.C ()) x
  exact hoist_assign_names_run Match.C (hoist Match.C) "i" "se1"
    (hn "i") (hn "se1") sc (smokeCapturedLocals, k) memo _ synth_smoke_i

private theorem check_smoke_se :
    @check Match.C productionNames (@ECtx.toNCtx productionNames smokeCapturedLocals)
      .bool (.name "se1") = .ok (.simple (.local .here)) := by
  rw [check, checkVia, synth_smoke_se]
  all_goals first | rfl | (intros; contradiction)

private theorem narrow_smoke_write (sc : ElabScope) (k : Nat) (memo : CallMemo) :
    @narrowPost Match.C productionNames (.name "i") (.name "se1") sc (smokeCapturedLocals, k) memo =
      .ok (([], (smokeCapturedLocals, k)), memo) := rfl

/-- The generated assignment reads the condition capture and writes `i`. -/
def smokeWriteProgram : SProg Match.C :=
  letI : FreshNames := productionNames
  [.of (ECtx.toNCtx smokeCapturedLocals)
    (.assignLocal (.there (.there .here)) (.simple (.local .here)))]

/-- Exact elaboration of `i = se1;` after the smoke condition capture. -/
theorem smoke_write (hk : Solidity.Goals.elabKernelTotal) (k : Nat) :
    @elabStmtP Match.C productionNames (.assign (.name "i") (.name "se1"))
      { funs := [], top := false } (smokeCapturedLocals, k) {} =
      .ok ((smokeWriteProgram, (smokeCapturedLocals, k)), {}) := by
  letI : FreshNames := productionNames
  have hp : elabStmtP Match.C = elabStmtPWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.1
  have ha : (elabRec Match.C ()).hoistAssign (.name "i") (.name "se1")
      { funs := [], top := false } (smokeCapturedLocals, k) {} =
      .ok ((([], .assign (.name "i") (.name "se1")), (smokeCapturedLocals, k)), {}) :=
    smoke_hoist_write hk _ k _
  rw [hp]
  conv => lhs; whnf
  simp only [RawStmt.mapExprsM, fnPure_other]
  conv => lhs; whnf
  simp only [bytesStmt, RawStmt.mapExprsM, bytesPure_other]
  conv => lhs; whnf
  simp only [RawStmt.exprs, List.map_cons, List.map_nil, List.forIn_cons, List.forIn_nil,
    Bool.false_eq_true, if_false, narrowWholeUse?_other, narrowWholeUse?_name]
  conv => lhs; whnf
  simp only [narrowPure_other]
  conv => lhs; whnf
  rw [(hk.1 Match.C).1.2.2.2.2.1]
  unfold hoistStmtWith
  dsimp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  dsimp only [Pure.pure, ReaderT.pure, StateT.pure, Except.pure]
  rw [nctx_run]
  dsimp only
  rw [ha]
  dsimp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind, Pure.pure,
    ReaderT.pure, StateT.pure, Except.pure]
  conv => lhs; whnf
  dsimp only
  rw [(hk.1 Match.C).1.2.2.2.1]
  unfold elabStmt1With
  dsimp only
  conv => lhs; whnf
  dsimp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [narrow_smoke_write]
  dsimp only
  unfold synthM
  dsimp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [nctx_run]
  dsimp only
  rw [synth_smoke_i]
  dsimp only [ElabM.lift, StateT.lift, Bind.bind, ReaderT.bind, StateT.bind,
    Pure.pure, ReaderT.pure, StateT.pure, Except.bind, Except.pure]
  simp only [checkIn, check_smoke_se]
  rfl

end Solidity.Examples.Lowering.Sim.Coverage

#print axioms Solidity.Correctness.Lowering.Sim.Coverage.spells_aligned

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_decoded

#print axioms Solidity.Correctness.Lowering.Sim.Coverage.lowerAt_of_lowersTo

#print axioms Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain.Input.syntax_decoded

#print axioms Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain.Expr.inferred

#print axioms Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain.Stmt.inferred
#print axioms Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain.Input.decoded_stmt
#print axioms Solidity.Correctness.Lowering.Sim.Coverage.diagram_total_boolean

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_flag

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_set_flag

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_capture

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_write
