import Solidity.Correctness.Lowering.Sim.CoverageControl
import Solidity.Correctness.Lowering.Sim.CoverageBranch
import Solidity.Correctness.Lowering.Sim.Coverage.SpellingObstruction
import Solidity.Correctness.Lowering.Sim.Coverage.BooleanCoverage
import Solidity.Correctness.Lowering.Sim.Coverage.BooleanBlocksV3
import Solidity.Correctness.Lowering.Sim.Coverage.BooleanStatements
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
exact elaboration receipts below. The flag and condition instructions also have
placement and acceptance checks. The owned branch/control interfaces compose
the condition hoisting and first conditional, including its complete
preprocessing. Both guards, the complete body scope, and the primitive loop
also have receipts. Complete loop preprocessing and outer-block/list composition
now establish actual accepted production of the smoke under `elabKernelTotal`.
`smoke_coverage` applies the approved restricted v2 theorem to that run; it does
not establish the frozen unrestricted `Diagram.Total`.
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

/-- The condition's capture followed by its assignment, in the flag context. -/
def smokeConditionBlock : Blk Match.C [.val .bool, .val .bool, .val .bool] :=
  letI : FreshNames := productionNames
  ⟨[.val .bool, .val .bool, .val .bool, .val .bool],
    .cons (.declLocal .bool (Var.ofName "se1")
      (some (.simple (.local (.there (.there .here))))))
      (.cons (.assignLocal (.there (.there .here)) (.simple (.local .here))) .nil)⟩

/-- Actual placement of the two independently proved condition instructions.
This is a `chain` receipt, not a claim about list elaboration or loop production. -/
theorem smoke_condition_placed :
    @SProg.chain Match.C productionNames
      (@ECtx.toNCtx productionNames (("brk0", .val .bool) :: Match.locals)).names
      [.val .bool, .val .bool, .val .bool]
      (smokeCaptureProgram ++ smokeWriteProgram) = .ok smokeConditionBlock := by
  rfl

/-- The placed capture/assignment block is accepted by the production checker. -/
theorem smoke_condition_accepted :
    Solidity.Backend.AbiWorld.PublicCompilerTotal.ProgOk [] smokeConditionBlock.2 := by
  repeat constructor

/-- The generated flag declaration, placed under the exact caller names. -/
def smokeFlagBlock : Blk Match.C [.val .bool, .val .bool] :=
  letI : FreshNames := productionNames
  ⟨[.val .bool, .val .bool, .val .bool],
    .cons (.declLocal .bool (Var.ofName "brk0") (some (.simple (.bool false)))) .nil⟩

/-- Actual caller-context placement of the generated flag instruction. -/
theorem smoke_flag_placed :
    @SProg.chain Match.C productionNames (@ECtx.toNCtx productionNames Match.locals).names
      [.val .bool, .val .bool] smokeFlagProgram = .ok smokeFlagBlock := by
  rfl

/-- Acceptance of the placed flag declaration, separately from the loop. -/
theorem smoke_flag_accepted :
    Solidity.Backend.AbiWorld.PublicCompilerTotal.ProgOk [] smokeFlagBlock.2 := by
  repeat constructor

/-- The owned list-composition theorem lifts the exact captured assignment. -/
theorem smoke_write_list (hk : Solidity.Goals.elabKernelTotal) (k : Nat) :
    @elabStmtsP Match.C productionNames [.assign (.name "i") (.name "se1")]
      { funs := [], top := false } (smokeCapturedLocals, k) {} =
      .ok ((smokeWriteProgram, (smokeCapturedLocals, k)), {}) := by
  letI : FreshNames := productionNames
  have h := CoverageBranch.actual_list
    (CoverageBranch.Children.cons (smoke_write hk k)
      (CoverageBranch.Children.nil (smokeCapturedLocals, k) ({} : CallMemo)))
  simpa only [List.append_nil] using h

/-- Actual hoisting of the smoke condition captures `a` and then writes `i`. -/
theorem smoke_condition_hoist (hk : Solidity.Goals.elabKernelTotal) :
    @hoist Match.C productionNames (.assign (.name "i") (.name "a"))
      { funs := [], top := false } ((("brk0", .val .bool) :: Match.locals), 1) {} =
      .ok ((((smokeCaptureProgram ++ smokeWriteProgram), .name "se1"),
        (smokeCapturedLocals, 2)), {}) := by
  letI : FreshNames := productionNames
  have hh : hoist Match.C = hoistWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.2.2.2
  have hm : storageMappingAlias? Match.C (("brk0", .val .bool) :: Match.locals)
      (.name "i") = false := by
    unfold storageMappingAlias?
    rw [synth]
    rfl
  have hl : (elabRec Match.C ()).elabStmtsP [.assign (.name "i") (.name "se1")]
      { funs := [], top := false } (smokeCapturedLocals, 2) {} =
      .ok ((smokeWriteProgram, (smokeCapturedLocals, 2)), {}) := smoke_write_list hk 2
  rw [hh]
  conv => lhs; whnf
  rw [hm]
  conv => lhs; whnf
  rw [smoke_capture]
  conv => lhs; whnf
  rw [hl]
  rfl

/-- Negating the smoke condition introduces no further Boolean capture. -/
theorem smoke_condition_not_hoist (hk : Solidity.Goals.elabKernelTotal) :
    @hoist Match.C productionNames (.unop .not (.assign (.name "i") (.name "a")))
      { funs := [], top := false } ((("brk0", .val .bool) :: Match.locals), 1) {} =
      .ok ((((smokeCaptureProgram ++ smokeWriteProgram), .unop .not (.name "se1")),
        (smokeCapturedLocals, 2)), {}) := by
  letI : FreshNames := productionNames
  have hh : hoist Match.C = hoistWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.2.2.2
  have hc : (elabRec Match.C ()).hoist (.assign (.name "i") (.name "a"))
      { funs := [], top := false } ((("brk0", .val .bool) :: Match.locals), 1) {} =
      .ok ((((smokeCaptureProgram ++ smokeWriteProgram), .name "se1"),
        (smokeCapturedLocals, 2)), {}) := by
    rw [(hk.1 Match.C).2.1.1]
    exact smoke_condition_hoist hk
  have hn : narrowCapture Match.C (.unop .not (.name "se1"))
      { funs := [], top := false } (smokeCapturedLocals, 2) {} =
      .ok ((([], .unop .not (.name "se1")), (smokeCapturedLocals, 2)), {}) := rfl
  rw [hh, Solidity.Correctness.Lowering.Sim.hoist_unop _ _ _ _ rfl]
  dsimp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [hc]
  dsimp only
  rw [hn]
  simp only [List.append_nil]
  rfl

/-- The branch instruction setting the generated flag after capture. -/
def smokeSetFlagBlock : Blk Match.C [.val .bool, .val .bool, .val .bool, .val .bool] :=
  ⟨_, .cons (.assignLocal (.there .here) (.simple (.bool true))) .nil⟩

/-- The owned scope theorem composes the actual flag-write child receipt. -/
theorem smoke_set_flag_scope (hk : Solidity.Goals.elabKernelTotal) (k : Nat) :
    @elabScope Match.C productionNames (@ECtx.toNCtx productionNames smokeCapturedLocals)
      [.assign (.name "brk0") (.bool true)] { funs := [], top := false }
      (smokeCapturedLocals, k) {} =
      .ok ((smokeSetFlagBlock, (smokeCapturedLocals, k)), {}) := by
  letI : FreshNames := productionNames
  apply CoverageBranch.actual_scope (sc := { funs := [], top := false })
    (CoverageBranch.Children.cons (smoke_set_flag hk k)
      (CoverageBranch.Children.nil (smokeCapturedLocals, k) ({} : CallMemo)))
  rfl

private theorem check_not_se :
    @check Match.C productionNames (@ECtx.toNCtx productionNames smokeCapturedLocals)
      .bool (.unop .not (.name "se1")) =
      .ok (.unop .not rfl rfl (.simple (.local .here))) := by
  rw [check, checkVia, synth]
  rw [synth_smoke_se]
  all_goals first | rfl | simp

/-- The first conditional instruction after its condition has been hoisted. -/
def smokeGuardProgram : SProg Match.C :=
  letI : FreshNames := productionNames
  [.of (ECtx.toNCtx smokeCapturedLocals)
    (.ite (.unop .not rfl rfl (.simple (.local .here))) smokeSetFlagBlock.2 .nil)]

/-- The owned control interface composes the actual first conditional arm. -/
theorem smoke_guard_primitive (hk : Solidity.Goals.elabKernelTotal) (k : Nat) :
    @elabStmt1 Match.C productionNames
      (.ite (.unop .not (.name "se1")) [.assign (.name "brk0") (.bool true)] [])
      { funs := [], top := false } (smokeCapturedLocals, k) {} =
      .ok ((smokeGuardProgram, (smokeCapturedLocals, k)), {}) := by
  letI : FreshNames := productionNames
  apply CoverageControl.producer_ite_success Match.C hk _ _ _
    { funs := [], top := false } (smokeCapturedLocals, k) (smokeCapturedLocals, k)
    (smokeCapturedLocals, k) (smokeCapturedLocals, k) {} {} {} {}
    (.unop .not rfl rfl (.simple (.local .here))) smokeSetFlagBlock ⟨_, .nil⟩
  · unfold checkIn
    rw [check_not_se]
    rfl
  · exact smoke_set_flag_scope hk k
  · apply CoverageBranch.actual_scope (sc := { funs := [], top := false })
      (CoverageBranch.Children.nil _ _)
    rfl

/-- The first lowered conditional before expression preprocessing. -/
def smokeGuardRaw : RawStmt :=
  .ite (.unop .not (.assign (.name "i") (.name "a")))
    [.assign (.name "brk0") (.bool true)] []

/-- The first conditional after its effectful condition has been hoisted. -/
def smokeGuardHoisted : RawStmt :=
  .ite (.unop .not (.name "se1")) [.assign (.name "brk0") (.bool true)] []

/-- Statement hoisting preserves the conditional's branches and threads the
condition's actual capture and assignment into its emitted prefix. -/
theorem smoke_guard_hoist (hk : Solidity.Goals.elabKernelTotal) :
    @hoistStmt Match.C productionNames smokeGuardRaw { funs := [], top := false }
      ((("brk0", .val .bool) :: Match.locals), 1) {} =
      .ok ((((smokeCaptureProgram ++ smokeWriteProgram), smokeGuardHoisted),
        (smokeCapturedLocals, 2)), {}) := by
  letI : FreshNames := productionNames
  have hh : hoistStmt Match.C = hoistStmtWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.2.2.1
  have hc : (elabRec Match.C ()).hoist (.unop .not (.assign (.name "i") (.name "a")))
      { funs := [], top := false } ((("brk0", .val .bool) :: Match.locals), 1) {} =
      .ok ((((smokeCaptureProgram ++ smokeWriteProgram), .unop .not (.name "se1")),
        (smokeCapturedLocals, 2)), {}) := by
    rw [(hk.1 Match.C).2.1.1]
    exact smoke_condition_not_hoist hk
  rw [hh]
  unfold smokeGuardRaw hoistStmtWith
  simp only [RawStmt.mapExprsM]
  conv => lhs; whnf
  dsimp only [StateT.run, Bind.bind, StateT.bind, ReaderT.bind, Except.bind,
    liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
  rw [hc]
  rfl

private theorem guard_fn (Γ : ECtx) :
    @fnPure Match.C productionNames Γ (.unop .not (.assign (.name "i") (.name "a"))) =
      .ok (.unop .not (.assign (.name "i") (.name "a"))) := by
  simp only [fnPure_unop, fnPure_assign, fnPure_other]
  rfl

private theorem guard_bytes :
    @bytesPure Match.C productionNames (("brk0", .val .bool) :: Match.locals)
      (.unop .not (.assign (.name "i") (.name "a"))) =
      .ok (.unop .not (.assign (.name "i") (.name "a"))) := by
  simp only [bytesPure_unop, bytesPure_assign, bytesPure_other]
  rfl

private theorem guard_whole :
    @narrowWholeUse? Match.C productionNames (("brk0", .val .bool) :: Match.locals)
      (.unop .not (.assign (.name "i") (.name "a"))) = none := by
  rw [narrowWholeUse?_unop, narrowWholeUse?_assign]
  have hm : @storageMappingAlias? Match.C productionNames
      (("brk0", .val .bool) :: Match.locals) (.name "i") = false := by
    unfold storageMappingAlias?
    rw [synth]
    rfl
  simp only [hm, Bool.false_and, Bool.false_eq_true, if_false, narrowWholeUse?_name]
  rfl

private theorem guard_narrow :
    @narrowPure Match.C productionNames false (("brk0", .val .bool) :: Match.locals)
      (.unop .not (.assign (.name "i") (.name "a"))) =
      .ok (.unop .not (.assign (.name "i") (.name "a"))) := by
  simp only [narrowPure_unop, narrowPure_other]
  rfl

/-- Complete preprocessing and elaboration of the first lowered conditional,
including its actual effectful condition and the owned primitive receipt. -/
theorem smoke_guard (hk : Solidity.Goals.elabKernelTotal) :
    @elabStmtP Match.C productionNames smokeGuardRaw { funs := [], top := false }
      ((("brk0", .val .bool) :: Match.locals), 1) {} =
      .ok (((smokeCaptureProgram ++ smokeWriteProgram) ++ smokeGuardProgram,
        (smokeCapturedLocals, 2)), {}) := by
  letI : FreshNames := productionNames
  have hp : elabStmtP Match.C = elabStmtPWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.1
  have hh : (elabRec Match.C ()).hoistStmt smokeGuardRaw { funs := [], top := false }
      ((("brk0", .val .bool) :: Match.locals), 1) {} =
      .ok ((((smokeCaptureProgram ++ smokeWriteProgram), smokeGuardHoisted),
        (smokeCapturedLocals, 2)), {}) := smoke_guard_hoist hk
  have hg : (elabRec Match.C ()).elabStmt1 smokeGuardHoisted
      { funs := [], top := false } (smokeCapturedLocals, 2) {} =
      .ok ((smokeGuardProgram, (smokeCapturedLocals, 2)), {}) := smoke_guard_primitive hk 2
  dsimp only [smokeGuardRaw] at hh
  dsimp only [smokeGuardHoisted] at hg
  rw [hp]
  unfold smokeGuardRaw
  conv => lhs; whnf
  simp only [RawStmt.mapExprsM, guard_fn]
  conv => lhs; whnf
  simp only [bytesStmt, RawStmt.mapExprsM, guard_bytes]
  conv => lhs; whnf
  simp only [RawStmt.exprs, List.map_cons, List.map_nil, List.forIn_cons, List.forIn_nil,
    Bool.false_eq_true, if_false, guard_whole]
  conv => lhs; whnf
  simp only [RawStmt.mapExprsM, guard_narrow]
  conv => lhs; whnf
  dsimp only
  rw [hh]
  conv => lhs; whnf
  dsimp only [smokeGuardHoisted]
  rw [hg]
  rfl

/-- The break body is a block containing the already-proved flag assignment. -/
theorem smoke_break_block (hk : Solidity.Goals.elabKernelTotal) (k : Nat) :
    @elabStmtP Match.C productionNames (.block [.assign (.name "brk0") (.bool true)])
      { funs := [], top := false } (smokeCapturedLocals, k) {} =
      .ok ((smokeSetFlagProgram, (smokeCapturedLocals, k)), {}) := by
  letI : FreshNames := productionNames
  have hp : elabStmtP Match.C = elabStmtPWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.1
  have hb : (elabRec Match.C ()).elabStmt1 (.block [.assign (.name "brk0") (.bool true)])
      { funs := [], top := false } (smokeCapturedLocals, k) {} =
      .ok ((smokeSetFlagProgram, (smokeCapturedLocals, k)), {}) := by
    have h := CoverageBranch.actual_block (C := Match.C) hk
      (sc := { funs := [], top := false })
      (CoverageBranch.Children.cons (smoke_set_flag hk k)
        (CoverageBranch.Children.nil (smokeCapturedLocals, k) ({} : CallMemo)))
    simpa only [List.append_nil] using h
  rw [hp]
  conv => lhs; whnf
  dsimp only
  rw [hb]
  rfl

/-- The owned scope interface restores the entry context around the break block. -/
theorem smoke_break_scope (hk : Solidity.Goals.elabKernelTotal) (k : Nat) :
    @elabScope Match.C productionNames (@ECtx.toNCtx productionNames smokeCapturedLocals)
      [.block [.assign (.name "brk0") (.bool true)]] { funs := [], top := false }
      (smokeCapturedLocals, k) {} =
      .ok ((smokeSetFlagBlock, (smokeCapturedLocals, k)), {}) := by
  letI : FreshNames := productionNames
  apply CoverageBranch.actual_scope (sc := { funs := [], top := false })
    (CoverageBranch.Children.cons (smoke_break_block hk k)
      (CoverageBranch.Children.nil (smokeCapturedLocals, k) ({} : CallMemo)))
  rfl

/-- The second lowered guard executes the original break body if still active. -/
def smokeBreakRaw : RawStmt :=
  .ite (.unop .not (.name "brk0")) [.block [.assign (.name "brk0") (.bool true)]] []

/-- The second guard reads the generated flag in the post-capture context. -/
def smokeBreakProgram : SProg Match.C :=
  letI : FreshNames := productionNames
  [.of (ECtx.toNCtx smokeCapturedLocals)
    (.ite (.unop .not rfl rfl (.simple (.local (.there .here)))) smokeSetFlagBlock.2 .nil)]

private theorem check_not_flag :
    @check Match.C productionNames (@ECtx.toNCtx productionNames smokeCapturedLocals)
      .bool (.unop .not (.name "brk0")) =
      .ok (.unop .not rfl rfl (.simple (.local (.there .here)))) := by
  rw [check, checkVia, synth]
  rw [synth_flag]
  all_goals first | rfl | simp

/-- The owned conditional interface composes the actual break block's scope. -/
theorem smoke_break_primitive (hk : Solidity.Goals.elabKernelTotal) (k : Nat) :
    @elabStmt1 Match.C productionNames smokeBreakRaw
      { funs := [], top := false } (smokeCapturedLocals, k) {} =
      .ok ((smokeBreakProgram, (smokeCapturedLocals, k)), {}) := by
  letI : FreshNames := productionNames
  apply CoverageControl.producer_ite_success Match.C hk _ _ _
    { funs := [], top := false } (smokeCapturedLocals, k) (smokeCapturedLocals, k)
    (smokeCapturedLocals, k) (smokeCapturedLocals, k) {} {} {} {}
    (.unop .not rfl rfl (.simple (.local (.there .here)))) smokeSetFlagBlock ⟨_, .nil⟩
  · unfold checkIn
    rw [check_not_flag]
    rfl
  · exact smoke_break_scope hk k
  · apply CoverageBranch.actual_scope (sc := { funs := [], top := false })
      (CoverageBranch.Children.nil _ _)
    rfl

/-- Hoisting the second guard leaves both the instruction and state unchanged. -/
theorem smoke_break_hoist (hk : Solidity.Goals.elabKernelTotal) (k : Nat) :
    @hoistStmt Match.C productionNames smokeBreakRaw { funs := [], top := false }
      (smokeCapturedLocals, k) {} =
      .ok ((([], smokeBreakRaw), (smokeCapturedLocals, k)), {}) := by
  letI : FreshNames := productionNames
  have hh : hoistStmt Match.C = hoistStmtWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.2.2.1
  rw [hh]
  unfold smokeBreakRaw hoistStmtWith
  simp only [RawStmt.mapExprsM]
  conv => lhs; whnf
  dsimp only [StateT.run, Bind.bind, StateT.bind, ReaderT.bind, Except.bind,
    liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
  rfl

/-- Complete preprocessing and elaboration of the second lowered conditional. -/
theorem smoke_break (hk : Solidity.Goals.elabKernelTotal) (k : Nat) :
    @elabStmtP Match.C productionNames smokeBreakRaw { funs := [], top := false }
      (smokeCapturedLocals, k) {} =
      .ok ((smokeBreakProgram, (smokeCapturedLocals, k)), {}) := by
  letI : FreshNames := productionNames
  have hp : elabStmtP Match.C = elabStmtPWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.1
  have hg : (elabRec Match.C ()).elabStmt1 smokeBreakRaw
      { funs := [], top := false } (smokeCapturedLocals, k) {} =
      .ok ((smokeBreakProgram, (smokeCapturedLocals, k)), {}) := smoke_break_primitive hk k
  dsimp only [smokeBreakRaw] at hg
  rw [hp]
  unfold smokeBreakRaw
  conv => lhs; whnf
  simp only [RawStmt.mapExprsM, fnPure_unop, fnPure_other]
  conv => lhs; whnf
  simp only [bytesStmt, RawStmt.mapExprsM, bytesPure_unop, bytesPure_other]
  conv => lhs; whnf
  simp only [RawStmt.exprs, List.map_cons, List.map_nil, List.forIn_cons, List.forIn_nil,
    Bool.false_eq_true, if_false, narrowWholeUse?_unop, narrowWholeUse?_name]
  conv => lhs; whnf
  simp only [narrowPure_unop, narrowPure_other]
  conv => lhs; whnf
  dsimp only
  rw [hg]
  rfl

/-- Exact sequential output of both lowered guards, including condition effects. -/
def smokeBodyProgram : SProg Match.C :=
  ((smokeCaptureProgram ++ smokeWriteProgram) ++ smokeGuardProgram) ++ smokeBreakProgram

private theorem smoke_body_children (hk : Solidity.Goals.elabKernelTotal) :
    @CoverageBranch.Children Match.C (@elabStmtP Match.C productionNames)
      { funs := [], top := false } [smokeGuardRaw, smokeBreakRaw]
      ((("brk0", .val .bool) :: Match.locals), 1) {} smokeBodyProgram
      (smokeCapturedLocals, 2) {} := by
  simpa only [List.append_nil, smokeBodyProgram] using
    CoverageBranch.Children.cons (smoke_guard hk)
      (CoverageBranch.Children.cons (smoke_break hk 2)
        (CoverageBranch.Children.nil (smokeCapturedLocals, 2) ({} : CallMemo)))

/-- The whole lowered loop body, placed in its entry flag context. -/
def smokeBodyBlock : Blk Match.C [.val .bool, .val .bool, .val .bool] :=
  ⟨_, Prog.join smokeConditionBlock.2
    (.cons (.ite (.unop .not rfl rfl (.simple (.local .here))) smokeSetFlagBlock.2 .nil)
      (.cons (.ite (.unop .not rfl rfl (.simple (.local (.there .here))))
        smokeSetFlagBlock.2 .nil) .nil))⟩

/-- Actual placement of all condition effects and both lowered guards. -/
theorem smoke_body_placed :
    @SProg.chain Match.C productionNames
      (@ECtx.toNCtx productionNames (("brk0", .val .bool) :: Match.locals)).names
      [.val .bool, .val .bool, .val .bool] smokeBodyProgram = .ok smokeBodyBlock := rfl

/-- The owned scope composition restores the flag context but retains counter 2. -/
theorem smoke_body_scope (hk : Solidity.Goals.elabKernelTotal) :
    @elabScope Match.C productionNames
      (@ECtx.toNCtx productionNames (("brk0", .val .bool) :: Match.locals))
      [smokeGuardRaw, smokeBreakRaw] { funs := [], top := false }
      ((("brk0", .val .bool) :: Match.locals), 1) {} =
      .ok ((smokeBodyBlock, ((("brk0", .val .bool) :: Match.locals), 2)), {}) := by
  letI : FreshNames := productionNames
  exact CoverageBranch.actual_scope (sc := { funs := [], top := false })
    (smoke_body_children hk) smoke_body_placed

/-- The complete placed loop body passes the unchanged production checker. -/
theorem smoke_body_accepted :
    Solidity.Backend.AbiWorld.PublicCompilerTotal.ProgOk [] smokeBodyBlock.2 := by
  repeat constructor

/-- The canonical lowered loop tests the live flag and a literal true operand. -/
def smokeLoopCondition : RawExpr := .binop .and (.unop .not (.name "brk0")) (.bool true)

/-- The typed loop condition in the flag context, before body-local captures. -/
def smokeLoopValue : Val Match.C [.val .bool, .val .bool, .val .bool] .bool :=
  .binop .and rfl rfl (.unop .not rfl rfl (.simple (.local .here))) (.simple (.bool true))

private theorem loop_not_literal : (RawExpr.unop .not (.name "brk0")).isLit = false := by
  rw [RawExpr.isLit]
  all_goals first | rfl | simp

private theorem loop_not_constant : smokeLoopCondition.constRat? = none := by
  unfold smokeLoopCondition
  rw [RawExpr.constRat?, RawExpr.constRat?]
  all_goals first | rfl | simp

private theorem synth_loop_not_flag :
    @synth Match.C productionNames
      (@ECtx.toNCtx productionNames (("brk0", .val .bool) :: Match.locals))
      (.unop .not (.name "brk0")) =
      .ok (.val .bool (.unop .not rfl rfl (.simple (.local .here)))) := by
  rw [synth, synth]
  all_goals first | rfl | simp

private theorem check_loop_not_flag :
    @check Match.C productionNames
      (@ECtx.toNCtx productionNames (("brk0", .val .bool) :: Match.locals))
      .bool (.unop .not (.name "brk0")) =
      .ok (.unop .not rfl rfl (.simple (.local .here))) := by
  rw [check, checkVia, synth_loop_not_flag]
  all_goals first | rfl | simp

private theorem check_loop_condition :
    @check Match.C productionNames
      (@ECtx.toNCtx productionNames (("brk0", .val .bool) :: Match.locals))
      .bool smokeLoopCondition = .ok smokeLoopValue := by
  have hc := loop_not_constant
  dsimp only [smokeLoopCondition] at hc
  unfold smokeLoopCondition
  rw [check, hc]
  simp only [loop_not_literal, Bool.false_and, Bool.false_eq_true, if_false]
  rw [checkVia, synth, hc]
  simp only [loop_not_literal, Bool.false_eq_true, if_false]
  rw [synth_loop_not_flag]
  dsimp only
  conv => lhs; whnf
  simp only [synth_bool]
  conv => lhs; whnf
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, TExpr.toVal?, BinOp.accepts, BinOp.ret]
  rw [check_loop_not_flag, check_bool]
  rfl
  all_goals simp

private theorem loop_bool_any (f : RawExpr → Bool) :
    RawExpr.any f (.bool true) = f (.bool true) := by
  rw [RawExpr.any]
  all_goals first | rfl | simp

private theorem smoke_loop_hoist (hk : Solidity.Goals.elabKernelTotal) :
    @hoist Match.C productionNames smokeLoopCondition { funs := [], top := false }
      ((("brk0", .val .bool) :: Match.locals), 1) {} =
      .ok ((([], smokeLoopCondition), ((("brk0", .val .bool) :: Match.locals), 1)), {}) := by
  letI : FreshNames := productionNames
  have hh : hoist Match.C = hoistWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.2.2.2
  have hf : smokeLoopCondition.foldConst = pure smokeLoopCondition := by
    unfold RawExpr.foldConst
    rw [loop_not_constant]
  have hp : ((RawExpr.bool true).hasCall || (RawExpr.bool true).hasIncDec ||
      hasNarrow Match.C (("brk0", .val .bool) :: Match.locals) (.bool true) ||
      powerDataNeeded Match.C { funs := [], top := false }
        (("brk0", .val .bool) :: Match.locals) (.bool true)) = false := by
    simp only [RawExpr.hasCall, RawExpr.hasIncDec, hasNarrow, powerDataNeeded, loop_bool_any]
    rfl
  rw [hh]
  unfold hoistWith
  rw [hf]
  conv => lhs; whnf
  rw [hp]
  rfl

/-- The actual loop-expression producer emits no prelude and restores its input. -/
theorem smoke_loop_expression (hk : Solidity.Goals.elabKernelTotal) :
    @loopExpr Match.C productionNames
      (@ECtx.toNCtx productionNames (("brk0", .val .bool) :: Match.locals))
      .bool smokeLoopCondition "condition" { funs := [], top := false }
      ((("brk0", .val .bool) :: Match.locals), 1) {} =
      .ok ((smokeLoopValue, ((("brk0", .val .bool) :: Match.locals), 1)), {}) := by
  letI : FreshNames := productionNames
  unfold loopExpr loopExprWith
  conv => lhs; whnf
  rw [smoke_loop_hoist hk]
  conv => lhs; whnf
  rw [check_loop_condition]
  rfl

/-- The complete intrinsic lowered loop instruction. -/
def smokeLoopProgram : SProg Match.C :=
  letI : FreshNames := productionNames
  [.of (ECtx.toNCtx (("brk0", .val .bool) :: Match.locals))
    (.loop .auto smokeLoopValue smokeBodyBlock.2)]

/-- The owned loop interface composes actual condition and complete body scope. -/
theorem smoke_loop_primitive (hk : Solidity.Goals.elabKernelTotal) :
    @elabStmt1 Match.C productionNames (.loop {} smokeLoopCondition [smokeGuardRaw, smokeBreakRaw])
      { funs := [], top := false } ((("brk0", .val .bool) :: Match.locals), 1) {} =
      .ok ((smokeLoopProgram, ((("brk0", .val .bool) :: Match.locals), 2)), {}) := by
  letI : FreshNames := productionNames
  exact CoverageControl.producer_loop_default_success Match.C hk _ _
    { funs := [], top := false }
    ((("brk0", .val .bool) :: Match.locals), 1)
    ((("brk0", .val .bool) :: Match.locals), 1)
    ((("brk0", .val .bool) :: Match.locals), 2) {} {} {} smokeLoopValue smokeBodyBlock
    (smoke_loop_expression hk) (smoke_body_scope hk)

/-- Complete preprocessing and elaboration of the lowered loop statement. -/
theorem smoke_loop (hk : Solidity.Goals.elabKernelTotal) :
    @elabStmtP Match.C productionNames (.loop {} smokeLoopCondition [smokeGuardRaw, smokeBreakRaw])
      { funs := [], top := false } ((("brk0", .val .bool) :: Match.locals), 1) {} =
      .ok ((smokeLoopProgram, ((("brk0", .val .bool) :: Match.locals), 2)), {}) := by
  letI : FreshNames := productionNames
  have hp : elabStmtP Match.C = elabStmtPWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.1
  have hg : (elabRec Match.C ()).elabStmt1
      (.loop {} smokeLoopCondition [smokeGuardRaw, smokeBreakRaw])
      { funs := [], top := false } ((("brk0", .val .bool) :: Match.locals), 1) {} =
      .ok ((smokeLoopProgram, ((("brk0", .val .bool) :: Match.locals), 2)), {}) :=
    smoke_loop_primitive hk
  dsimp only [smokeLoopCondition] at hg
  rw [hp]
  unfold smokeLoopCondition
  conv => lhs; whnf
  simp only [RawStmt.mapExprsM, fnPure_binop, fnPure_unop, fnPure_other]
  conv => lhs; whnf
  simp only [bytesStmt, RawStmt.mapExprsM, bytesPure_binop, bytesPure_unop, bytesPure_other]
  conv => lhs; whnf
  simp only [RawStmt.exprs, RawLoopSpec.exprs, Option.toList, List.flatMap_nil, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil, List.forIn_cons, List.forIn_nil,
    Bool.false_eq_true, if_false, narrowWholeUse?_binop, narrowWholeUse?_unop,
    narrowWholeUse?_name, narrowWholeUse?_other]
  conv => lhs; whnf
  simp only [narrowPure_binop, narrowPure_unop, narrowPure_other]
  conv => lhs; whnf
  dsimp only
  simp only [List.reverse_nil]
  rw [hg]
  rfl

/-- The complete flag-plus-loop output in the exact caller context.
`smoke_production` below connects this program to the actual producer. -/
def smokeProgram : Blk Match.C [.val .bool, .val .bool] :=
  letI : FreshNames := productionNames
  ⟨[.val .bool, .val .bool, .val .bool],
    .cons (.declLocal .bool (Var.ofName "brk0") (some (.simple (.bool false))))
      (.cons (.loop .auto smokeLoopValue smokeBodyBlock.2) .nil)⟩

/-- Actual caller-name placement of the complete intrinsic output. -/
theorem smoke_program_placed :
    @SProg.chain Match.C productionNames (@ECtx.toNCtx productionNames Match.locals).names
      [.val .bool, .val .bool] (smokeFlagProgram ++ smokeLoopProgram) = .ok smokeProgram := rfl

/-- The complete program satisfies the unchanged production checker.
The separate `smoke_production` receipt proves actual producer provenance. -/
theorem smoke_program_accepted :
    Solidity.Backend.AbiWorld.PublicCompilerTotal.ProgOk [] smokeProgram.2 := by
  repeat constructor

/-- The exact raw block emitted by lowering the Match while/break input. -/
def smokeRaw : List RawStmt :=
  [.block [.decl (.named "bool") "brk0" (some (.bool false)),
    .loop {} smokeLoopCondition [smokeGuardRaw, smokeBreakRaw]]]

/-- The complete outer block restores caller locals while retaining fresh counter 2. -/
theorem smoke_outer_block (hk : Solidity.Goals.elabKernelTotal) :
    @elabStmtP Match.C productionNames (.block
      [.decl (.named "bool") "brk0" (some (.bool false)),
       .loop {} smokeLoopCondition [smokeGuardRaw, smokeBreakRaw]])
      { funs := [] } (Match.locals, 1) {} =
      .ok ((smokeFlagProgram ++ smokeLoopProgram, (Match.locals, 2)), {}) := by
  letI : FreshNames := productionNames
  have hp : elabStmtP Match.C = elabStmtPWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.1
  have hb : (elabRec Match.C ()).elabStmt1 (.block
      [.decl (.named "bool") "brk0" (some (.bool false)),
       .loop {} smokeLoopCondition [smokeGuardRaw, smokeBreakRaw]])
      { funs := [] } (Match.locals, 1) {} =
      .ok ((smokeFlagProgram ++ smokeLoopProgram, (Match.locals, 2)), {}) := by
    have h := CoverageBranch.actual_block (C := Match.C) hk (sc := { funs := [] })
      (CoverageBranch.Children.cons (smoke_flag hk)
        (CoverageBranch.Children.cons (smoke_loop hk)
          (CoverageBranch.Children.nil ((("brk0", .val .bool) :: Match.locals), 2)
            ({} : CallMemo))))
    simpa only [List.append_nil] using h
  rw [hp]
  conv => lhs; whnf
  dsimp only
  rw [hb]
  rfl

/-- The actual complete statement-list producer, with both mutable state layers. -/
theorem smoke_elaborated (hk : Solidity.Goals.elabKernelTotal) :
    @elabStmtsP Match.C productionNames smokeRaw { funs := [] } (Match.locals, 1) {} =
      .ok ((smokeFlagProgram ++ smokeLoopProgram, (Match.locals, 2)), {}) := by
  letI : FreshNames := productionNames
  simpa only [List.append_nil] using CoverageBranch.actual_list
    (CoverageBranch.Children.cons (smoke_outer_block hk)
      (CoverageBranch.Children.nil (Match.locals, 2) ({} : CallMemo)))

/-- Exact raw, scope, state, name and intrinsic-output proposals for the smoke. -/
def smokeOutput : Solidity.Correctness.Lowering.Checker.Output Match.C [.val .bool, .val .bool] where
  raw := smokeRaw
  afterLower := ⟨(Match.locals, 1), {}⟩
  elabScope := { funs := [] }
  beforeElab := ⟨(Match.locals, 1), {}⟩
  afterElab := ⟨(Match.locals, 2), {}⟩
  elaborated := smokeFlagProgram ++ smokeLoopProgram
  names := (@ECtx.toNCtx productionNames Match.locals).names
  program := smokeProgram

/-- Actual lowering and elaboration establish the approved v2 production receipt. -/
theorem smoke_production (hk : Solidity.Goals.elabKernelTotal) :
    @ProductionV2 productionNames Match.body (Match.emitted smokeOutput) := by
  letI : FreshNames := productionNames
  refine ⟨⟨rfl, ?_⟩, ⟨smoke_elaborated hk, smoke_program_placed⟩, ?_⟩
  · have h := Solidity.Correctness.Lowering.Total.Coverage.Template.whileBreak
      none (.assign (.name "i") (.name "a")) Match.body.input.before
      (Solidity.Correctness.Lowering.Total.Coverage.hasIncDec_assign _ _)
    exact lowerAt_of_lowersTo (h.lowers Match.body.input.scope)
  · exact ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩

/-- Nonvacuous application of restricted coverage to the actual accepted Match run. -/
theorem smoke_coverage (hk : Solidity.Goals.elabKernelTotal) :
    ∃ b' : Body, b'.SameInput Match.body ∧
      ∃ m, diagram.Assoc b' (Match.emitted smokeOutput) m :=
  diagram_total_boolean Match.body (Match.emitted smokeOutput)
    (smoke_in_domain smokeOutput) (smoke_production hk) smoke_program_accepted

/-- One Boolean caller local for the strict block-domain extension. -/
def blockLocals : ECtx := [("i", .val .bool)]

/-- The new input is a block, not a singleton while. -/
def blockRaw : List RawStmt := [.block [.assign (.name "i") (.bool true)]]

/-- The resolved block and its original production input. -/
def blockBody : Body where
  E := Match.unit.env
  returns := []
  modifier := false
  control := .body
  ctx := [.bool]
  input :=
    { raw := blockRaw,
      resolved := .block (.stmt (.expr (.assign (.local .here) (.bool true))) .nil),
      returnSlots := none, scope := { funs := [] },
      before := ⟨(blockLocals, 0), {}⟩ }
  site := .loop

/-- The exact symbolic instruction produced for the Boolean assignment. -/
def blockProgram : SProg Match.C :=
  letI : FreshNames := productionNames
  [.of (ECtx.toNCtx blockLocals) (.assignLocal .here (.simple (.bool true)))]

private theorem synth_block :
    @synth Match.C productionNames (@ECtx.toNCtx productionNames blockLocals) (.name "i") =
      .ok (.val .bool (.simple (.local .here))) := by
  rw [synth]
  rfl

private theorem narrow_block (sc : ElabScope) (k : Nat) (memo : CallMemo) :
    @narrowPost Match.C productionNames (.name "i") (.bool true) sc (blockLocals, k) memo =
      .ok (([], (blockLocals, k)), memo) := rfl

/-- Shared assignment receipt for the default top-level and child scopes. -/
private theorem assignment_write (hk : Solidity.Goals.elabKernelTotal) (top : Bool) (k : Nat) :
    (((@elabStmtP Match.C productionNames (.assign (.name "i") (.bool true))).run
      { funs := [], top := top }).run (blockLocals, k)).run {} =
      .ok ((blockProgram, (blockLocals, k)), {}) := by
  letI : FreshNames := productionNames
  have hp : elabStmtP Match.C = elabStmtPWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.1
  have ha : (elabRec Match.C ()).hoistAssign (.name "i") (.bool true) =
      pure ([], .assign (.name "i") (.bool true)) :=
    kernel_hoist_assign_bool hk Match.C "i" true
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
  rw [narrow_block]
  dsimp only
  unfold synthM
  dsimp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [nctx_run]
  dsimp only
  rw [synth_block]
  dsimp only [ElabM.lift, StateT.lift, Bind.bind, ReaderT.bind, StateT.bind,
    Pure.pure, ReaderT.pure, StateT.pure, Except.bind, Except.pure]
  simp only [checkIn, check_bool]
  rfl


/-- Actual elaboration under the block reader scope. -/
theorem block_write (hk : Solidity.Goals.elabKernelTotal) (k : Nat) :
    (((@elabStmtP Match.C productionNames (.assign (.name "i") (.bool true))).run
      { funs := [], top := false }).run (blockLocals, k)).run {} =
      .ok ((blockProgram, (blockLocals, k)), {}) :=
  assignment_write hk _ k

/-- The block restores the caller locals and changes neither counter nor memo. -/
theorem block_outer (hk : Solidity.Goals.elabKernelTotal) :
    @elabStmtP Match.C productionNames (.block [.assign (.name "i") (.bool true)])
      { funs := [] } (blockLocals, 0) {} =
      .ok ((blockProgram, (blockLocals, 0)), {}) := by
  letI : FreshNames := productionNames
  have hp : elabStmtP Match.C = elabStmtPWith Match.C (elabRec Match.C ()) :=
    (hk.1 Match.C).1.2.2.1
  have hb : (elabRec Match.C ()).elabStmt1 (.block [.assign (.name "i") (.bool true)])
      { funs := [] } (blockLocals, 0) {} =
      .ok ((blockProgram, (blockLocals, 0)), {}) := by
    have h := CoverageBranch.actual_block (C := Match.C) hk (sc := { funs := [] })
      (CoverageBranch.Children.cons (block_write hk 0)
        (CoverageBranch.Children.nil (blockLocals, 0) ({} : CallMemo)))
    simpa only [List.append_nil] using h
  rw [hp]
  conv => lhs; whnf
  dsimp only
  rw [hb]
  rfl

/-- Exact statement-list elaboration, obtained from the actual block receipt. -/
theorem block_elaborated (hk : Solidity.Goals.elabKernelTotal) :
    @elabStmtsP Match.C productionNames blockRaw { funs := [] } (blockLocals, 0) {} =
      .ok ((blockProgram, (blockLocals, 0)), {}) := by
  letI : FreshNames := productionNames
  simpa only [List.append_nil] using CoverageBranch.actual_list
    (CoverageBranch.Children.cons (block_outer hk)
      (CoverageBranch.Children.nil (blockLocals, 0) ({} : CallMemo)))

/-- Placing the instruction under the caller's actual names yields this program. -/
def blockIntrinsic : Blk Match.C [.val .bool] :=
  ⟨_, .cons (.assignLocal .here (.simple (.bool true))) .nil⟩

/-- Exact output proposal for the block production. -/
def blockOutput : Solidity.Correctness.Lowering.Checker.Output Match.C [.val .bool] where
  raw := blockRaw
  afterLower := ⟨(blockLocals, 0), {}⟩
  elabScope := { funs := [] }
  beforeElab := ⟨(blockLocals, 0), {}⟩
  afterElab := ⟨(blockLocals, 0), {}⟩
  elaborated := blockProgram
  names := (@ECtx.toNCtx productionNames blockLocals).names
  program := blockIntrinsic

/-- The emitted output has the caller's one-Boolean context. -/
def blockEmitted : Emitted := ⟨Match.C, [.val .bool], blockOutput⟩

/-- Membership is proved from syntax alone. -/
theorem block_in_domain : BooleanBlocksV3.Input blockBody blockEmitted := by
  apply Or.inr
  refine ⟨rfl, rfl, rfl, rfl, ["i"], _, rfl, rfl, ?_⟩
  exact .cons (.assign (by decide) (.bool true)) .nil

/-- The new accepted run is outside the delivered singleton-while domain. -/
theorem block_not_old : ¬ BooleanDomain.Input blockBody blockEmitted := by
  rintro ⟨_, _, _, _, names, c, ss, _, raw, _⟩
  cases raw

/-- Actual lowering, elaboration and placement for the strict extension witness. -/
theorem block_production (hk : Solidity.Goals.elabKernelTotal) :
    @ProductionV2 productionNames blockBody blockEmitted := by
  letI : FreshNames := productionNames
  refine ⟨⟨rfl, ?_⟩, ⟨block_elaborated hk, ?_⟩, ?_⟩
  · exact lowerAt_of_lowersTo (raw := blockRaw) (out := blockRaw)
      (before := blockBody.input.before) (after := blockOutput.afterLower) ⟨4, rfl⟩
  · rfl
  · exact ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩

/-- Unchanged production-checker acceptance of `{ i = true; }`. -/
theorem block_accepted : Accepted blockEmitted := by
  repeat constructor

/-- Nonvacuity of the new domain uses actual production and unchanged acceptance. -/
theorem block_coverage (hk : Solidity.Goals.elabKernelTotal) :
    ∃ b' : Body, b'.SameInput blockBody ∧ ∃ m, diagram.Assoc b' blockEmitted m :=
  diagram_total_boolean_blocks blockBody blockEmitted block_in_domain
    (block_production hk) block_accepted

/-- The original Match smoke remains covered by domain inclusion. -/
theorem smoke_blocks_coverage (hk : Solidity.Goals.elabKernelTotal) :
    ∃ b' : Body, b'.SameInput Match.body ∧
      ∃ m, diagram.Assoc b' (Match.emitted smokeOutput) m :=
  diagram_total_boolean_blocks Match.body (Match.emitted smokeOutput)
    (BooleanBlocksV3.of_boolean (smoke_in_domain smokeOutput))
    (smoke_production hk) smoke_program_accepted

/-- A standalone assignment outside both the while-only and block input boundaries. -/
def statementRaw : List RawStmt := [.assign (.name "i") (.bool true)]

def statementBody : Body :=
  { blockBody with input :=
      { blockBody.input with
        raw := statementRaw
        resolved := .expr (.assign (.local .here) (.bool true)) } }

/-- Actual assignment elaboration in the caller scope, using the kernel equations. -/
theorem statement_write (hk : Solidity.Goals.elabKernelTotal) (k : Nat) :
    (((@elabStmtP Match.C productionNames (.assign (.name "i") (.bool true))).run
      { funs := [] }).run (blockLocals, k)).run {} =
      .ok ((blockProgram, (blockLocals, k)), {}) :=
  assignment_write hk _ k

/-- Actual singleton-list elaboration, with no block wrapper. -/
theorem statement_elaborated (hk : Solidity.Goals.elabKernelTotal) :
    @elabStmtsP Match.C productionNames statementRaw { funs := [] } (blockLocals, 0) {} =
      .ok ((blockProgram, (blockLocals, 0)), {}) := by
  letI : FreshNames := productionNames
  simpa only [List.append_nil] using CoverageBranch.actual_list
    (CoverageBranch.Children.cons (statement_write hk 0)
      (CoverageBranch.Children.nil (blockLocals, 0) ({} : CallMemo)))

/-- The same symbolic assignment and placement, with the standalone raw input. -/
def statementOutput : Solidity.Correctness.Lowering.Checker.Output Match.C [.val .bool] :=
  { blockOutput with raw := statementRaw }

def statementEmitted : Emitted := ⟨Match.C, [.val .bool], statementOutput⟩

theorem statement_in_domain : BooleanStatements.Input statementBody statementEmitted := by
  exact ⟨rfl, rfl, rfl, rfl, ["i"], _, rfl, rfl, .assign (by decide) (.bool true)⟩

/-- Neither the while boundary nor the block boundary admits this run. -/
theorem statement_not_v3 : ¬ BooleanBlocksV3.Input statementBody statementEmitted := by
  intro h
  rcases h with old | block
  · obtain ⟨_, _, _, _, names, c, ss, _, raw, _⟩ := old
    cases raw
  · obtain ⟨_, _, _, _, names, ss, _, raw, _⟩ := block
    cases raw

/-- Actual lowering, elaboration and placement of the strict-extension witness. -/
theorem statement_production (hk : Solidity.Goals.elabKernelTotal) :
    @ProductionV2 productionNames statementBody statementEmitted := by
  letI : FreshNames := productionNames
  refine ⟨⟨rfl, ?_⟩, ⟨statement_elaborated hk, ?_⟩, ?_⟩
  · exact lowerAt_of_lowersTo (raw := statementRaw) (out := statementRaw)
      (before := statementBody.input.before) (after := statementOutput.afterLower) ⟨4, rfl⟩
  · rfl
  · exact ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩

/-- The new domain is nonvacuous under the authorized kernel-totality hypothesis. -/
theorem statement_coverage (hk : Solidity.Goals.elabKernelTotal) :
    ∃ b' : Body, b'.SameInput statementBody ∧ ∃ m, diagram.Assoc b' statementEmitted m :=
  diagram_total_boolean_statements statementBody statementEmitted statement_in_domain
    (statement_production hk) block_accepted

/-- The original Match smoke is still covered, through the two domain inclusions. -/
theorem smoke_statements_coverage (hk : Solidity.Goals.elabKernelTotal) :
    ∃ b' : Body, b'.SameInput Match.body ∧
      ∃ m, diagram.Assoc b' (Match.emitted smokeOutput) m :=
  diagram_total_boolean_statements Match.body (Match.emitted smokeOutput)
    (BooleanStatements.of_blocks
      (BooleanBlocksV3.of_boolean (smoke_in_domain smokeOutput)))
    (smoke_production hk) smoke_program_accepted

/-- The same assignment at the non-top-level checked caller scope. -/
def checkedBody : Body :=
  { statementBody with input := { statementBody.input with scope := { funs := [], top := false } } }
def checkedOutput : Solidity.Correctness.Lowering.Checker.Output Match.C [.val .bool] :=
  { statementOutput with elabScope := { funs := [], top := false } }
def checkedEmitted : Emitted := ⟨Match.C, [.val .bool], checkedOutput⟩

theorem checked_in_domain : BooleanStatements.CheckedInput checkedBody checkedEmitted := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, ["i"], _, rfl, rfl, .assign (by decide) (.bool true)⟩
theorem checked_not_default : ¬ BooleanStatements.Input checkedBody checkedEmitted := by
  intro h
  have top := congrArg ElabScope.top h.2.2.2.1
  cases top

/-- Actual lowering, elaboration and placement reuse the existing child-scope receipt. -/
theorem checked_production (hk : Solidity.Goals.elabKernelTotal) :
    @ProductionV2 productionNames checkedBody checkedEmitted := by
  letI : FreshNames := productionNames
  refine ⟨⟨rfl, ?_⟩, ⟨?_, rfl⟩, ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩⟩
  · exact lowerAt_of_lowersTo (raw := statementRaw) (out := statementRaw)
      (before := checkedBody.input.before) (after := checkedOutput.afterLower) ⟨4, rfl⟩
  · simpa only [List.append_nil] using CoverageBranch.actual_list
      (CoverageBranch.Children.cons (block_write hk 0)
        (CoverageBranch.Children.nil (blockLocals, 0) ({} : CallMemo)))

/-- Strict-extension nonvacuity with unchanged acceptance of the same intrinsic program. -/
theorem checked_coverage (hk : Solidity.Goals.elabKernelTotal) :
    ∃ b' : Body, b'.SameInput checkedBody ∧ ∃ m, diagram.Assoc b' checkedEmitted m :=
  diagram_total_checked_boolean_statements checkedBody checkedEmitted checked_in_domain
    (checked_production hk) block_accepted

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

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_condition_placed
#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_condition_accepted

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_flag_placed
#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_flag_accepted

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_write_list
#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_condition_hoist

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_condition_not_hoist
#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_set_flag_scope
#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_guard_primitive

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_guard_hoist

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_guard

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_break_block
#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_break_scope

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_break_primitive
#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_break_hoist

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_break

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_body_scope
#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_body_placed
#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_body_accepted

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_loop_expression
#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_loop_primitive

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_program_placed
#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_program_accepted

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_loop

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_production
#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_coverage

#print axioms Solidity.Examples.Lowering.Sim.Coverage.block_production
#print axioms Solidity.Examples.Lowering.Sim.Coverage.block_coverage

#print axioms Solidity.Examples.Lowering.Sim.Coverage.statement_production
#print axioms Solidity.Examples.Lowering.Sim.Coverage.statement_coverage

#print axioms Solidity.Examples.Lowering.Sim.Coverage.checked_production
#print axioms Solidity.Examples.Lowering.Sim.Coverage.checked_coverage
