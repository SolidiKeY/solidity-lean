import Solidity.Correctness.Panic.Capture

/-!
# Capture linkage and guard order: checks

An enum conversion of a compound operand `a + 1`: the elaborator's own
output is the capture and the check of the captured local, and its run fails
with code 0x21 for the operand's value, not for a separately supplied one.
Then two-guard statements where the first failing guard decides the code,
and the emitted order of each producer with more than one guard.
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
    uint_narrow_capture_origin (σ.push (t := .val .uint) two) three 1 (by decide) (by decide)
      rfl⟩

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

/-! ## The first failing guard decides -/

section Order

variable {Γ : Ctx} {Γ' : Ctx}

/-- `values`, a storage array held by the innermost alias. -/
private def values : SPath C (.alias (.array (.prim .uint)) :: Γ) (.array (.prim .uint)) :=
  .alias Idx.here

/-- `values[i] / d == 0`. -/
private def quotient (i d : Int) (hi : PrimTy.uint.inRange i = true)
    (hd : PrimTy.uint.inRange d = true) :
    Val C (.alias (.array (.prim .uint)) :: Γ) .bool :=
  .binop .eqB rfl rfl
    (.binop .div rfl rfl (.read (.index (.arr .dyn) values (litU i hi))) (litU d hd))
    (litU 0 (by decide))

private theorem quotient_guards (i d : Int) (hi : PrimTy.uint.inRange i = true)
    (hd : PrimTy.uint.inRange d = true) :
    (Stmt.require (quotient (C := C) (Γ := Γ) i d hi hd)).panics =
      [(0x32, cmpU .lt rfl rfl (litU i hi) (.len values rfl)),
       (0x12, cmpU .neB rfl rfl (litU d hd) (litU 0 (by decide)))] := by
  simp [Stmt.panics, quotient, Val.panics, Loc.panics, SPath.panics, values, idxPG, divPG, pg,
    range, rangeU, litU, Val.mayHalt, BinOp.isArith]

private theorem lt_eval (σ : State C Γ) (a b : Val C Γ .uint) (x y : PrimTy.uint.Denote)
    (left : a.evalT σ = .ok x) (right : b.evalT σ = .ok y) :
    (cmpU .lt rfl rfl a b).evalT σ = .ok (decide (x.val < y.val)) := by
  simp [cmpU, Val.evalT, left, right, BinOp.shortT, BinOp.evalT, BinOp.evalNum, TRes.ofOpt,
    bind, Except.bind]

/-- `require(values[5] / 0 == 0);` on a two-element array, instrumented: the
index guard is emitted before the divisor guard and both would fail; the run
halts with the index code 0x32, not the divisor's 0x12. -/
example (σ : State C (.alias (.array (.prim .uint)) :: Γ))
    (tail : Prog C (.alias (.array (.prim .uint)) :: Γ) Γ')
    (length : (Val.len values rfl).evalT σ = .ok two) :
    (Prog.cons (.require (quotient 5 0 (by decide) (by decide))) tail).withPanics.runR σ =
      .error (THalt.ofData (encodePanic 0x32)) := by
  rw [withPanics_source_cons, quotient_guards]
  exact guards_first_failure _ _ σ 0 (by simp) (fun j before => absurd before (Nat.not_lt_zero j))
    (lt_eval σ _ _ ⟨5, by decide⟩ two rfl length)

/-- With the index in range, `require(values[1] / 0 == 0);` passes the first
guard and fails the second: now the divisor's code 0x12 is the data. -/
example (σ : State C (.alias (.array (.prim .uint)) :: Γ))
    (tail : Prog C (.alias (.array (.prim .uint)) :: Γ) Γ')
    (length : (Val.len values rfl).evalT σ = .ok two) :
    (Prog.cons (.require (quotient 1 0 (by decide) (by decide))) tail).withPanics.runR σ =
      .error (THalt.ofData (encodePanic 0x12)) := by
  rw [withPanics_source_cons, quotient_guards]
  refine guards_first_failure _ _ σ 1 (by simp) (fun j before => ?_)
    (uint_divisor_guard_eval σ _ ⟨0, by decide⟩ rfl)
  obtain rfl : j = 0 := by omega
  exact lt_eval σ _ _ ⟨1, by decide⟩ two rfl length

/-- The reverse order: `values[5] = 1 / 0;` emits its right-hand side's
divisor guard before its target's index guard, so the same two failures halt
with 0x12. -/
example (σ : State C (.alias (.array (.prim .uint)) :: Γ))
    (tail : Prog C (.alias (.array (.prim .uint)) :: Γ) Γ') :
    (Prog.cons (.assign (.index (.arr .dyn) values (litU 5 (by decide)))
      (.val (.binop .div rfl rfl (litU 1 (by decide)) (litU 0 (by decide))))) tail).withPanics.runR
      σ = .error (THalt.ofData (encodePanic 0x12)) := by
  have guards : (Stmt.assign (C := C) (.index (.arr .dyn) (values (Γ := Γ)) (litU 5 (by decide)))
      (.val (.binop .div rfl rfl (litU 1 (by decide)) (litU 0 (by decide))))).panics =
      [(0x12, cmpU .neB rfl rfl (litU 0 (by decide)) (litU 0 (by decide))),
       (0x32, cmpU .lt rfl rfl (litU 5 (by decide)) (.len values rfl))] := by
    simp [assign_panics_order, Src.panics, Val.panics, Loc.panics, SPath.panics, values, idxPG,
      divPG, pg, range, rangeU, litU, Val.mayHalt, BinOp.isArith]
  rw [withPanics_source_cons, guards]
  exact guards_first_failure _ _ σ 0 (by simp) (fun j before => absurd before (Nat.not_lt_zero j))
    (uint_divisor_guard_eval σ _ ⟨0, by decide⟩ rfl)

private theorem lt_halt (σ : State C Γ) (a b : Val C Γ .uint) (x : PrimTy.uint.Denote)
    (halt : THalt) (left : a.evalT σ = .ok x) (right : b.evalT σ = .error halt) :
    (cmpU .lt rfl rfl a b).evalT σ = .error halt := by
  simp [cmpU, Val.evalT, left, right, BinOp.shortT, bind, Except.bind]

/-- Where reading the array's length itself reverts (an unset alias), the
index guard halts with that bare revert: it is not relabelled 0x32, and the
failing divisor guard behind it is not reached. -/
example (σ : State C (.alias (.array (.prim .uint)) :: Γ))
    (tail : Prog C (.alias (.array (.prim .uint)) :: Γ) Γ')
    (unset : (Val.len values rfl).evalT σ = .error .revert) :
    (Prog.cons (.require (quotient 5 0 (by decide) (by decide))) tail).withPanics.runR σ =
      .error .revert := by
  rw [withPanics_source_cons, quotient_guards]
  exact guards_first_halt _ _ σ 0 (by simp) .revert
    (fun j before => absurd before (Nat.not_lt_zero j))
    (lt_halt σ _ _ ⟨5, by decide⟩ .revert rfl unset)

/-- `require(values[1] / 1 == 0);` passes both guards: the statement and the
tail run in the unchanged state. -/
example (σ : State C (.alias (.array (.prim .uint)) :: Γ))
    (tail : Prog C (.alias (.array (.prim .uint)) :: Γ) Γ')
    (length : (Val.len values rfl).evalT σ = .ok two) :
    (Prog.cons (.require (quotient 1 1 (by decide) (by decide))) tail).withPanics.runR σ =
      (Prog.cons (Stmt.require (quotient 1 1 (by decide) (by decide))).withPanics
        tail.withPanics).runR σ := by
  rw [withPanics_source_cons, quotient_guards]
  refine guards_all_pass _ _ σ fun j inside => ?_
  have cases : j = 0 ∨ j = 1 := by simp at inside; omega
  rcases cases with rfl | rfl
  · exact lt_eval σ _ _ ⟨1, by decide⟩ two rfl length
  · exact uint_divisor_guard_eval σ _ ⟨1, by decide⟩ rfl

/-! ### Emitted order, by producer

Each operand's guards are given as one guard; the equations place them. -/

variable {Δ : Ctx} (ga gb gc : Nat × Val C Δ .bool)

/-- `a / b`: the dividend's guard, then the zero-divisor check. -/
example (a b : Val C Δ .uint) (ha : a.panics = [ga]) (hb : b.panics = []) :
    (Val.binop .div rfl rfl a b).panics =
      [ga, (0x12, cmpU .neB rfl rfl b (litU 0 (by decide)))] := by
  rw [binop_panics_order _ _ _ _ _ ⟨by decide, by decide⟩, ha, hb]
  rfl

/-- `a && b`: `b`'s guard only where `a` holds, after `a`'s. -/
example (a b : Val C Δ .bool) (ha : a.panics = [ga]) (hb : b.panics = [gb]) :
    (Val.binop .and rfl rfl a b).panics = [ga, (gb.1, orB (notB a) gb.2)] := by
  rw [and_panics_order, ha, hb]
  rfl

/-- `a || b`: `b`'s guard only where `a` fails, after `a`'s. -/
example (a b : Val C Δ .bool) (ha : a.panics = [ga]) (hb : b.panics = [gb]) :
    (Val.binop .or rfl rfl a b).panics = [ga, (gb.1, orB (notB (notB a)) gb.2)] := by
  rw [or_panics_order, ha, hb]
  rfl

/-- `c ? a : b`: the condition's guard, then each branch's under its case. -/
example (c : Val C Δ .bool) (a b : Val C Δ .uint) (hc : c.panics = [gc])
    (ha : a.panics = [ga]) (hb : b.panics = [gb]) :
    (Val.ternary c a b).panics =
      [gc, (ga.1, orB (notB c) ga.2), (gb.1, orB (notB (notB c)) gb.2)] := by
  rw [ternary_panics_order, hc, ha, hb]
  rfl

/-- `addmod(a, b, k)`: the operands in order, the zero modulus last. -/
example (a b k : Val C Δ .uint) (ha : a.panics = [ga]) (hb : b.panics = [gb])
    (hk : k.panics = [gc]) :
    (Val.modular .addmod a b k).panics =
      [ga, gb, gc, (0x12, cmpU .neB rfl rfl k (litU 0 (by decide)))] := by
  rw [modular_panics_order, ha, hb, hk]
  rfl

/-- `base[i]` on a dynamic storage array: base, index, then the bound. -/
example (base : SPath C Δ (.array (.prim .uint))) (i : Val C Δ .uint)
    (hbase : base.panics = [ga]) (hi : i.panics = [gb]) :
    (SPath.loc (.index (.arr .dyn) base i)).panics =
      [ga, gb, (0x32, cmpU .lt rfl rfl i (.len base rfl))] := by
  rw [index_panics_order, hbase, hi]
  rfl

/-- The same on a dynamic memory array. -/
example (base : MPath C Δ (.array (.prim .uint))) (i : Val C Δ .uint)
    (hbase : base.panics = [ga]) (hi : i.panics = [gb]) :
    (MPath.loc (.index .dyn base i)).panics =
      [ga, gb, (0x32, cmpU .lt rfl rfl i (.mlen base rfl))] := by
  rw [mindex_panics_order, hbase, hi]
  rfl

/-- `x /= r` on a local: the right-hand side's guard before the divisor's. -/
example (x : Idx Δ (.val .uint)) (r : Val C Δ .uint) (hr : r.panics = [ga]) :
    (Stmt.opAssign .div rfl rfl (.local x) r).panics =
      [ga, (0x12, cmpU .neB rfl rfl r (litU 0 (by decide)))] := by
  rw [opAssign_panics_order, hr]
  rfl

/-- `base.pop()`: the base's guard before the emptiness check. -/
example (base : SPath C Δ (.array (.prim .uint))) (hbase : base.panics = [ga]) :
    (Stmt.pop base).panics =
      [ga, (0x31, cmpU .gt rfl rfl (.len base rfl) (litU 0 (by decide)))] := by
  rw [pop_panics_order, hbase]
  rfl

/-- `x++` on a local has only the range check of `x + 1`. -/
example (x : Idx Δ (.val .uint)) :
    (Stmt.incDec (C := C) .postInc rfl (.local x)).panics =
      pg 0x11 (bumpRange .postInc .uint (.simple (.local x))) := by
  rw [incDec_panics_order]
  rfl

/-- `base.push() /= r`: the right-hand side, the base, then the divisor. -/
example (base : SPath C Δ (.array (.prim .uint))) (r : Val C Δ .uint)
    (hr : r.panics = [ga]) (hbase : base.panics = [gb]) :
    (Stmt.pushOpAssign .div rfl rfl base r).panics =
      [ga, gb, (0x12, cmpU .neB rfl rfl r (litU 0 (by decide)))] := by
  rw [pushOpAssign_panics_order, hr, hbase]
  rfl

end Order

end Solidity.Examples.Panic.Capture
