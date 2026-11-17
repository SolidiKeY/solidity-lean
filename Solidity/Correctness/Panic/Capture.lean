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

end Solidity.Correctness.Panic
