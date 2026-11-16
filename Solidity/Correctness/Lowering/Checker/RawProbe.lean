import Solidity.Correctness.Lowering.Checker.Contract
import Lean.Elab.Term

/-! A raw-output feasibility probe, not semantic acceptance. The total matcher
recognizes one exact output shape without calling or copying `lowerList`.
The elaborator below runs the actual producer and quotes its returned value;
the acceptance theorem reduces only that closed quoted value. State capture
retains the exact supported Boolean caller context, counter and empty memo.
The reader is shared with intrinsic elaboration. This is not a checker for
general state carriers or a semantic endpoint by itself. -/
namespace Solidity.Correctness.Lowering.Checker.RawProbe

/-- Empty specifications are the entire specification boundary of this probe. -/
def emptySpec (s : RawLoopSpec) : Bool :=
  s.inv.isEmpty && s.qinv.isEmpty && s.dec.isNone && s.unwind.isNone && !s.brk

/-- Exact named context and reader shared by producer and intrinsic stages. -/
def inputLocals : ECtx := [("i", .val .bool), ("a", .val .bool)]
def scope : ElabScope := { funs := [] }

/-- The concrete raw input used by the actual-producer probe. -/
def input : List RawStmt :=
  [.whileLoop {} (.assign (.name "i") (.name "a")) [.brk]]

/-- Total finite structural case analysis for one while/break output family.
No semantic preservation or producer equality follows from this check. Every
other constructor/combination is refused by the final catch-all case. -/
def checkRaw [FreshNames] (source output : List RawStmt) (counter : Nat) : Bool :=
  match source, output with
  | [.whileLoop spec (.assign (.name i) (.name a)) [.brk]],
    [.block [.decl (.named "bool") flag (some (.bool false)),
      .loop outSpec (.binop .and (.unop .not (.name f1)) (.bool true))
        [.ite (.unop .not (.assign (.name i1) (.name a1)))
          [.assign (.name f2) (.bool true)] [],
         .ite (.unop .not (.name f3)) [.block [.assign (.name f4) (.bool true)]] []]]] =>
      emptySpec spec && emptySpec outSpec && i == i1 && a == a1 &&
        i != flag && a != flag &&
        flag == toString (Var.fresh "brk" counter) &&
        f1 == flag && f2 == flag && f3 == flag && f4 == flag
  | _, _ => false

open Lean (Expr mkConst mkApp mkAppN toExpr)

/-- Refusing quoter for the expression constructors present in this probe.
This reconstructs supplied data; it does not lower syntax. -/
def quoteExpr : RawExpr → Except String Expr
  | .name x => pure (mkApp (mkConst ``RawExpr.name) (toExpr x))
  | .bool b => pure (mkApp (mkConst ``RawExpr.bool) (toExpr b))
  | .unop .not e => do
      pure (mkAppN (mkConst ``RawExpr.unop) #[mkConst ``UnOp.not, ← quoteExpr e])
  | .binop .and a b => do
      pure (mkAppN (mkConst ``RawExpr.binop) #[mkConst ``BinOp.and, ← quoteExpr a, ← quoteExpr b])
  | .assign a b => do
      pure (mkAppN (mkConst ``RawExpr.assign) #[← quoteExpr a, ← quoteExpr b])
  | _ => .error "probe quoter: unsupported expression"

private def nilStmt : Expr := mkApp (mkConst ``List.nil [0]) (mkConst ``RawStmt)
private def consStmt (x xs : Expr) : Expr :=
  mkAppN (mkConst ``List.cons [0]) #[mkConst ``RawStmt, x, xs]

private def quoteSpec (s : RawLoopSpec) : Except String Expr :=
  if emptySpec s then
    pure (mkAppN (mkConst ``RawLoopSpec.mk)
      #[mkApp (mkConst ``List.nil [0]) (mkConst ``RawExpr),
        mkApp (mkConst ``Option.none [0]) (mkConst ``RawExpr),
        mkApp (mkConst ``Option.none [0]) (mkConst ``Nat), toExpr false,
        mkApp (mkConst ``List.nil [0]) (mkConst ``RawInv)])
  else .error "probe quoter: nonempty specification"

mutual
/-- Refusing structural data quoter; unsupported statements produce an error. -/
def quoteStmt : RawStmt → Except String Expr
  | .assign l r => do
      pure (mkAppN (mkConst ``RawStmt.assign) #[← quoteExpr l, ← quoteExpr r])
  | .decl (.named t) x (some e) => do
      pure (mkAppN (mkConst ``RawStmt.decl)
        #[mkApp (mkConst ``RawTy.named) (toExpr t), toExpr x,
          mkAppN (mkConst ``Option.some [0]) #[mkConst ``RawExpr, ← quoteExpr e]])
  | .block ss => do pure (mkApp (mkConst ``RawStmt.block) (← quoteStmts ss))
  | .ite c t e => do
      pure (mkAppN (mkConst ``RawStmt.ite) #[← quoteExpr c, ← quoteStmts t, ← quoteStmts e])
  | .loop spec c body => do
      pure (mkAppN (mkConst ``RawStmt.loop) #[← quoteSpec spec, ← quoteExpr c, ← quoteStmts body])
  | _ => .error "probe quoter: unsupported statement"
termination_by s => sizeOf s

/-- Lists are quoted without changing their ordering or elements. -/
def quoteStmts : List RawStmt → Except String Expr
  | [] => pure nilStmt
  | s :: ss => do pure (consStmt (← quoteStmt s) (← quoteStmts ss))
termination_by ss => sizeOf ss
end

/-- The producer's returned raw value and counter. Full state evidence is a
separate unresolved obligation, not implied by these two fields. -/
structure Captured where
  raw : List RawStmt
  counter : Nat
  locals : ECtx
  memo : CallMemo

open Lean Elab Term in
elab "capture_actual_while_break%" : term => do
  let result := (((lowerLoops none input).run scope).run (inputLocals, 1)).run {}
  let .ok ((raw, st), memo) := result | throwError "actual lowerLoops refused probe"
  unless memo.starts.isEmpty && memo.bodies.isEmpty do
    throwError "actual lowerLoops changed the expected empty memo"
  match st.1 with
  | [("i", .val .bool), ("a", .val .bool)] => pure ()
  | _ => throwError "actual lowerLoops changed the caller context"
  let .ok rawTerm := quoteStmts raw | throwError "actual output is outside probe quoter"
  let memoTerm ← elabTerm (← `(show CallMemo from {})) none
  return mkAppN (mkConst ``Captured.mk) #[rawTerm, toExpr st.2, mkConst ``inputLocals, memoTerm]

/-- Materialized result of running actual lowerLoops at elaboration time.
The kernel never unfolds its opaque partial recursion. -/
def actual : Captured := capture_actual_while_break%

/-- Kernel acceptance of the actual quoted producer output. Raw only. -/
theorem accepts_actual : checkRaw input actual.raw 1 = true := by
  decide

/-- The actual producer consumed exactly one fresh flag on this sample. -/
theorem actual_counter : actual.counter = 2 := by
  rfl

/-- The exact supported caller context and empty memo survive lowering. -/
theorem actual_state : actual.locals = inputLocals ∧ actual.memo = ({} : CallMemo) := by
  exact ⟨rfl, rfl⟩

/-- Corrupt only the flag declaration; preserve the returned guards/body. -/
def corruptFlag : List RawStmt → List RawStmt
  | [.block (.decl t _ value :: rest)] => [.block (.decl t "corrupt" value :: rest)]
  | ss => ss

/-- Negative control: incoherent declaration/uses are refused in the kernel. -/
theorem rejects_corrupt_flag : checkRaw input (corruptFlag actual.raw) 1 = false := by
  decide

/-- A mismatched incoming fresh counter is also refused. -/
theorem rejects_counter : checkRaw input actual.raw 2 = false := by
  decide

/-- A different raw RHS name cannot be associated with this output. -/
theorem rejects_wrong_source :
    checkRaw [.whileLoop {} (.assign (.name "i") (.name "b")) [.brk]] actual.raw 1 = false := by
  decide

/-- Continue remains visibly outside the accepted raw shape. -/
theorem rejects_continue :
    checkRaw [.whileLoop {} (.assign (.name "i") (.name "a")) [.cont]] actual.raw 1 = false := by
  decide

#print axioms actual_state
#print axioms rejects_wrong_source
#print axioms rejects_continue
#print axioms accepts_actual
#print axioms actual_counter
#print axioms rejects_corrupt_flag
#print axioms rejects_counter

end Solidity.Correctness.Lowering.Checker.RawProbe
