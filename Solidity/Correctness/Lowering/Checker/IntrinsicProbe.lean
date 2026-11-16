import Solidity.Correctness.Lowering.Checker.RawProbe
import Solidity.Syntax.Quote

/-! Reachability probe for the actual intrinsic output. This runs the actual
intrinsic elaborator on RawProbe.actual.raw; it does not replace that output
with G19.code. Kernel checks below establish context and retained loop shape,
not semantics. The missing generic target bridge remains explicit. -/
namespace Solidity.Correctness.Lowering.Checker.IntrinsicProbe

/-- No storage or calls are present in this concrete Boolean sample. -/
def C : Contract := { vars := [] }

/-- The named caller locals, before lowering and intrinsic elaboration. -/
def locals : ECtx := RawProbe.inputLocals

/-- Caller context; actual output is allowed to retain fresh locals. -/
def Γ : Ctx := [.val .bool, .val .bool]

/-- Exact intrinsic program and final fresh counter from the actual run. -/
structure Captured where
  program : Blk C Γ
  counter : Nat
  locals : ECtx
  memo : CallMemo

open Lean Elab Term in
elab "capture_actual_intrinsic%" : term => do
  let result := (((elabStmtsP C RawProbe.actual.raw).run RawProbe.scope).run
    (RawProbe.actual.locals, RawProbe.actual.counter)).run RawProbe.actual.memo
  let .ok ((ss, st), memo) := result | throwError "actual intrinsic elaboration refused probe"
  unless memo.starts.isEmpty && memo.bodies.isEmpty do
    throwError "unexpected call memo entries in no-call probe"
  match st.1 with
  | [("i", .val .bool), ("a", .val .bool)] => pure ()
  | _ => throwError "intrinsic stage did not restore the named caller context"
  let .ok p := SProg.chain (ECtx.toNCtx locals).names Γ ss |
    throwError "actual intrinsic placement refused probe"
  let (pe, ge, de) := Prog.quoteShared (mkConst ``C) p.2
  let family := mkLambda `Δ BinderInfo.default (mkConst ``Ctx)
    (mkAppN (mkConst ``Prog) #[mkConst ``C, ge, mkBVar 0])
  let block := mkAppN (mkConst ``Sigma.mk [0,0]) #[mkConst ``Ctx, family, de, pe]
  let memoTerm ← elabTerm (← `(show CallMemo from {})) none
  return mkAppN (mkConst ``Captured.mk) #[block, toExpr st.2, mkConst ``RawProbe.inputLocals, memoTerm]

/-- Materialized actual intrinsic elaboration and placement result. -/
def actual : Captured := capture_actual_intrinsic%

/-- Named context is restored; complete supported memo remains empty. -/
theorem actual_state : actual.locals = RawProbe.inputLocals ∧ actual.memo = ({} : CallMemo) := by
  exact ⟨rfl, rfl⟩

/-- Actual intrinsic elaboration allocates one additional condition capture. -/
theorem actual_counter : actual.counter = 3 := by
  rfl

/-- Total structural observation of the top-level program spine. No match
case evaluates a loop or assumes its semantic behavior. -/
def hasTopLoop {C : Contract} : {Γ Δ : Ctx} → Prog C Γ Δ → Bool
  | _, _, .nil => false
  | _, _, .cons (.loop ..) _ => true
  | _, _, .cons _ rest => hasTopLoop rest

/-- Actual elaboration retains the introduced flag as a hidden local. -/
theorem actual_context : actual.program.1 = [.val .bool, .val .bool, .val .bool] := by rfl

/-- Actual intrinsic output contains a loop, unlike the G19 scoped prefix. -/
theorem actual_has_loop : hasTopLoop actual.program.2 = true := by rfl

#print axioms actual_counter
#print axioms actual_state
#print axioms actual_context
#print axioms actual_has_loop

end Solidity.Correctness.Lowering.Checker.IntrinsicProbe
