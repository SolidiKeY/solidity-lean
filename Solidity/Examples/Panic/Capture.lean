import Solidity.Correctness.Panic.Capture

/-!
# Capture linkage and guard order: checks

An enum conversion of a compound operand `a + 1`: the elaborator's own
output is the capture and the check of the captured local, and its run fails
with code 0x21 for the operand's value, not for a separately supplied one.
Then two-guard statements where the first failing guard decides the code.
-/

namespace Solidity.Examples.Panic.Capture

open Solidity Semantics Checked Panic.Source Solidity.Correctness.Panic

variable {C : Contract}

/-- The compound operand `a + 1`, `a` the innermost local. -/
private def next : Val C [.val .uint] .uint :=
  .binop .add rfl rfl (.simple (.local Idx.here)) (litU 1 (by decide))

private def two : PrimTy.uint.Denote := ⟨2, by decide⟩
private def three : PrimTy.uint.Denote := ⟨3, by decide⟩

private theorem next_reads_three (σ : State C []) :
    next.evalT (σ.push (t := .val .uint) two) = .ok three := by
  simp [next, litU, Val.evalT, BinOp.shortT, Simple.evalT, PrimTy.ofLit, BinOp.evalT,
    BinOp.evalNum, BinOp.arithInt, TRes.ofOpt, bind, Except.bind, State.push, TEnv.get, two]
  rfl

/-- `E(a + 1)` at a three-member enum with `a = 2`, in a data-retaining
frame: the run halts with `Panic(0x21)`, and the failure's origin is the
conversion of `3`, the value the operand `a + 1` read. -/
example (σ : State C []) (tail : Prog C [.val .uint, .val .uint] [.val .uint, .val .uint]) :
    (Prog.cons (.declLocal .uint (.fresh "se" 0) (some next))
      (.cons (panicStmt 0x21
        (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU 3 (by decide)))) tail)).runR
      (σ.push (t := .val .uint) two) = .error (THalt.ofData (encodePanic 0x21)) ∧
    OriginV2 (.original (.enumConversion 3 three)) .enumConversion :=
  enum_capture_panic_run _ _ next three 3 (by decide) tail (next_reads_three σ) (by decide)

/-- The same conversion outside such a frame is the bare assertion panic,
with the same origin at the operand's value. -/
example (σ : State C []) :
    (Prog.cons (.declLocal .uint (.fresh "se" 0) (some next))
      (.cons (.assert
        (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU 3 (by decide)))) .nil)).runR
      (σ.push (t := .val .uint) two) = .error .panic ∧
    OriginV2 (.original (.enumConversion 3 three)) .enumConversion :=
  enum_capture_assert_run _ _ next three 3 (by decide) .nil (next_reads_three σ) (by decide)

/-- The captured local, not a second read of the operand, is what the check
sees: after the capture it reads `3`. -/
example (σ : State C []) :
    ∃ out, (Stmt.declLocal .uint (.fresh "se" 0) (some next)).runR
        (σ.push (t := .val .uint) two) = .ok out ∧
      (Val.simple (.local Idx.here)).evalT out.st = .ok three :=
  capture_linkage _ .uint _ next three (next_reads_three σ)

/-- A narrowing capture of `a + 1` at `uint1`: `3` does not fit one bit, and
the failed check of the captured local is that value's narrow overflow. -/
example (σ : State C []) (tail : Prog C [.val .uint, .val .uint] [.val .uint, .val .uint]) :
    (Prog.cons (.declLocal .uint (.fresh "se" 0) (some next))
      (.cons (panicStmt 0x11
        (cmpU .le rfl rfl (.simple (.local Idx.here)) (litU 1 (by decide)))) tail)).runR
      (σ.push (t := .val .uint) two) = .error (THalt.ofData (encodePanic 0x11)) ∧
    OriginV2 (.narrowing (.unsigned 1 three)) .arithmetic :=
  ⟨capture_guard_panic_run _ .uint _ next three 0x11 _ tail (next_reads_three σ) rfl,
    uint_narrow_capture_origin ((σ.push (t := .val .uint) two)) three 1 (by decide) (by decide) rfl⟩

/-- A capture whose operand itself halts (`1 / 0`) halts there with the
operand's bare revert: the enum check behind it is never reached. -/
example (σ : State C []) :
    (Stmt.declLocal .uint (.fresh "se" 0)
      (some (.binop .div rfl rfl (litU 1 (by decide)) (litU 0 (by decide))))).runR σ =
      .error .revert :=
  capture_decl_halt σ .uint _ _ .revert rfl

/-- A signed narrowing capture holding `128` at `int8`: the failed range check
of the captured local is the narrow overflow of that value. -/
example (σ : State C []) :
    OriginV2 (.narrowing (.signed 8 ⟨128, by decide⟩)) .arithmetic :=
  int_narrow_capture_origin σ ⟨128, by decide⟩ 8 (by decide) (by decide) (by decide) rfl

section Elaborated

variable [FreshNames]

/-- The operand `a + 1`, checked where `a` is the only local. -/
private theorem next_checked :
    check C (ECtx.toNCtx [("a", .val .uint)]) .uint (.binop .add (.name "a") (.num 1)) =
      .ok next := by
  simp [check, checkVia, synth, RawExpr.constRat?, RawExpr.isLit, litAt, ECtx.toNCtx,
    LocalTy.toLTy, captured_name_synth, captured_name_check, TExpr.toVal?, bind, Except.bind,
    pure, Except.pure]
  rfl

/-- `enumCapture` on `E(a + 1)` emits exactly the two statements run above:
the capture of the checked operand, then the check of the innermost local. -/
example (free : checkFresh C [("a", .val .uint)] (toString (Var.fresh "se" 0)) = .ok ()) :
    (enumCapture C 3 (.binop .add (.name "a") (.num 1))).runFrom
      { funs := [], retainFailureData := true } ([("a", .val .uint)], 0) =
    .ok (([.of (ECtx.toNCtx [("a", .val .uint)])
            (.declLocal .uint (.fresh "se" 0) (some next)),
          .of (ECtx.toNCtx [(toString (Var.fresh "se" 0), .val .uint), ("a", .val .uint)])
            (panicStmt 0x21
              (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU 3 (by decide))))],
        .name (toString (Var.fresh "se" 0))),
      ([(toString (Var.fresh "se" 0), .val .uint), ("a", .val .uint)], 1)) :=
  enumCapture_linked 3 _ _ _ 0 next next_checked free (by decide)

/-- `narrowCapture` on a `uint8` operation `a + 1`, in a data-retaining frame
with no overflow mode: the capture, then `Panic(0x11)` unless the captured
local is at most `255`. -/
example (operation : checkedNarrow? C [("a", .val .uint)] (.binop .add (.name "a") (.num 1)) =
      some (.uint, 8))
    (free : checkFresh C [("a", .val .uint)] (toString (Var.fresh "se" 0)) = .ok ()) :
    (narrowCapture C (.binop .add (.name "a") (.num 1))).runFrom
      { funs := [], retainFailureData := true } ([("a", .val .uint)], 0) =
    .ok (([.of (ECtx.toNCtx [("a", .val .uint)])
            (.declLocal .uint (.fresh "se" 0) (some next)),
          .of (ECtx.toNCtx [(toString (Var.fresh "se" 0), .val .uint 8), ("a", .val .uint)])
            (panicStmt 0x11
              (cmpU .le rfl rfl (.simple (.local Idx.here)) (litU 255 (by decide))))],
        .name (toString (Var.fresh "se" 0))),
      ([(toString (Var.fresh "se" 0), .val .uint 8), ("a", .val .uint)], 1)) :=
  narrowCapture_uint_linked _ 8 _ _ 0 next operation (by decide) next_checked free (by decide)

/-- At `int8` the elaborated check of a captured local `se` is the lower
bound `-128 <= se`, then the upper bound `se <= 127`. -/
example (Γ : NCtx) :
    check C ((Var.ofName "se", .val .int) :: Γ) .bool (inTyCond .int 8 (.name "se")) =
      .ok (andB
        (cmpI .le rfl rfl (litI (-128) (by decide)) (.simple (.local Idx.here)))
        (cmpI .le rfl rfl (.simple (.local Idx.here)) (litI 127 (by decide)))) :=
  int_narrow_condition_check Γ "se" 8 (by decide) (by decide)

end Elaborated

end Solidity.Examples.Panic.Capture
