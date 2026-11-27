import Solidity.Correctness.Lowering.Sim.Coverage.SpellingObstruction
import Solidity.Correctness.Lowering.Sim.Coverage.BooleanCoverage
import Solidity.Correctness.Lowering.Sim.Coverage.Alignment
import Solidity.Correctness.Lowering.Sim.Coverage.LoweringReceipt
import Solidity.Examples.Lowering.Sim.Match
import Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip.Leaves

/-!
# Coverage obstructions and independent smoke facts

The requested use of `diagram_total` cannot be supplied for the frozen v1
statement: the first example refutes it under the authorized kernel hypothesis.
The second checks that versioned production retains the v1 receipt; the third
shows that caller placement alone does not repair the frozen spelling relation.
The final checks establish decoding, alignment, acceptance of the existing
materialized program, and actual lowering of the smoke separately. The generated
flag declaration has an exact elaboration receipt below; the complete loop
production receipt is still outstanding.
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
