import Solidity.Calculus.Sound.JoinSequence
import Solidity.Calculus.JoinSequenceSize
import Solidity.Calculus.Rules

/-! # Inhabited joined-assignment execution controls
These check the standalone builder and the actual joined-plan dispatcher. -/
namespace Solidity.Examples.Tactics.JoinSequence
private abbrev C := StandardExample
private abbrev Γ : Ctx := [.val .bool, .val .uint]
private def uint (n : Nat) (h : PrimTy.uint.inRange (Int.ofNat n) = true) : Val C Γ .uint :=
  .simple (.lit n h)
private def yes : LocalWrites C Γ :=
  [⟨.bool, .here, .simple (.bool false)⟩,
   ⟨.uint, .there .here, uint 1 rfl⟩,
   ⟨.uint, .there .here, .binop .add rfl rfl (.simple (.local (.there .here))) (uint 1 rfl)⟩]
private def no : LocalWrites C Γ :=
  [⟨.uint, .there .here, .binop .div rfl rfl (uint 1 rfl) (uint 0 rfl)⟩]
private def start (b : Bool) : State C Γ :=
  ((State.init C).push (t := .val .uint) (uintOfNat 0)).push (t := .val .bool) b
private def observed (b : Bool) : Option (Bool × PrimTy.uint.Denote) :=
  ((Prog.runSt (start b) (LocalWrites.joined (.fresh "se" 0) (.local .here) yes no)).map
    (fun σ => (σ.env.2.1, σ.env.2.2.1))).toOption

/-- The selected branch changes the original guard, then a later assignment
reads its predecessor. The untaken branch divides by zero. -/
theorem changedGuardDependent : observed true = some (false, uintOfNat 2) := by
  rfl

/-- Selecting the failing branch really fails; it is not erased as dead code. -/
theorem selectedFailure : observed false = none := by
  rfl

/-- A nested Solidity block is deliberately outside the straight-write decoder. -/
theorem refusesNested : (Prog.cons (.block yes.program) .nil).localWrites? = none := rfl

/-- A Solidity requirement is not silently treated as an assignment. -/
theorem refusesRequirement :
    (Prog.cons (.require (.simple (.bool true))) yes.program).localWrites? = none := rfl

/-- Every typed RHS occurs once in emitted syntax: both branches plus guards. -/
theorem emittedSize : (LocalWrites.joined (.fresh "se" 0) (.local .here) yes no).size = 33 := rfl

private def captured : Prog C Γ (.val .bool :: Γ) :=
  .cons (.declLocal .bool (.fresh "se" 0) (some (.simple (.local .here))))
    (.cons (.block (yes.guarded true (no.guarded false))) .nil)
private def capturedObserved (b : Bool) : Option (Bool × PrimTy.uint.Denote) :=
  (((Prog.runSt (start b) captured).map (State.drop (.push .refl))).map
    (fun σ => (σ.env.1, σ.env.2.1))).toOption

/-- The actual capture block keeps the selected dependent writes and skips
an untaken failing RHS even after the source condition changes. -/
theorem capturedChangedGuardDependent :
    capturedObserved true = some (false, uintOfNat 2) := by
  unfold capturedObserved captured
  rw [LocalWrites.captured_drop_runSt (start true) (.fresh "se" 0) (.local .here) yes no]
  rfl

/-- The selected failing branch remains observable through the block. -/
theorem capturedSelectedFailure : capturedObserved false = none := rfl

/-- Actual dispatcher syntax includes the extra block node. -/
theorem capturedEmittedSize : captured.size = 34 := rfl

private abbrev BΓ : Ctx := [.val .bool, .val .bool, .val .bool]
private abbrev i0 : Idx BΓ (.val .bool) := .here
private abbrev i1 : Idx BΓ (.val .bool) := .there .here
private abbrev i2 : Idx BΓ (.val .bool) := .there (.there .here)
private def nonSimpleBool : Val C BΓ .bool := .unop .not rfl rfl (.simple (.bool false))
private def andA (i j v : Idx BΓ (.val .bool)) (r : Val C BΓ .bool)
    (neutral : Bool) : LocalWrites C BΓ :=
  [⟨.bool, i, r⟩, ⟨.bool, j, .binop (p := .bool) (q := .bool) .and rfl rfl
    (.simple (.local v)) (.simple (.bool neutral))⟩]
private def andB (w : Idx BΓ (.val .bool)) : LocalWrites C BΓ :=
  [⟨.bool, w, .simple (.bool false)⟩]
private def orA (i : Idx BΓ (.val .bool)) : LocalWrites C BΓ :=
  [⟨.bool, i, .simple (.bool true)⟩]
private def orB (j v w : Idx BΓ (.val .bool)) (r : Val C BΓ .bool)
    (neutral : Bool) : LocalWrites C BΓ :=
  [⟨.bool, j, r⟩, ⟨.bool, v, .binop (p := .bool) (q := .bool) .or rfl rfl
    (.simple (.local w)) (.simple (.bool neutral))⟩]
private def eligible (a b : LocalWrites C BΓ) : Bool :=
  (Upd.ifJoin? (.pvV i2) a.program b.program).isSome

/-- Both canonical normalizations retain splitting. -/
theorem canonicalAndSplit : eligible (andA i0 i0 i0 nonSimpleBool true) (andB i0) = false := rfl
theorem canonicalOrSplit : eligible (orA i0) (orB i0 i0 i0 nonSimpleBool false) = false := rfl

/-- Every individual target/read mismatch stays eligible for a joined sequence. -/
example : eligible (andA i1 i0 i0 nonSimpleBool true) (andB i0) = true := rfl
example : eligible (andA i0 i1 i0 nonSimpleBool true) (andB i0) = true := rfl
example : eligible (andA i0 i0 i1 nonSimpleBool true) (andB i0) = true := rfl
example : eligible (andA i0 i0 i0 nonSimpleBool true) (andB i1) = true := rfl
example : eligible (orA i1) (orB i0 i0 i0 nonSimpleBool false) = true := rfl
example : eligible (orA i0) (orB i1 i0 i0 nonSimpleBool false) = true := rfl
example : eligible (orA i0) (orB i0 i1 i0 nonSimpleBool false) = true := rfl
example : eligible (orA i0) (orB i0 i0 i1 nonSimpleBool false) = true := rfl

/-- Neutral literals and the source RHS simplicity are part of the exact boundary. -/
example : eligible (andA i0 i0 i0 nonSimpleBool false) (andB i0) = true := rfl
example : eligible (orA i0) (orB i0 i0 i0 nonSimpleBool true) = true := rfl
example : eligible (andA i0 i0 i0 (.simple (.bool true)) true) (andB i0) = true := rfl
example : eligible (orA i0) (orB i0 i0 i0 (.simple (.bool true)) false) = true := rfl

/-- Additional writes are not rejected by a prefix-only pattern. -/
example : eligible (⟨.bool, i2, .simple (.bool false)⟩ :: andA i0 i0 i0 nonSimpleBool true) (andB i0) = true := rfl
example : eligible (andA i0 i0 i0 nonSimpleBool true ++ [⟨.bool, i2, .simple (.bool false)⟩]) (andB i0) = true := rfl

/-- A selected all-Boolean sequence reads the previous write. -/
private def boolThen : LocalWrites C BΓ := andA i0 i1 i0 nonSimpleBool true
private def boolElse : LocalWrites C BΓ := andB i0
private def boolStart (c : Bool) : State C BΓ :=
  (((State.init C).push (t := .val .bool) c).push (t := .val .bool) false).push (t := .val .bool) false
private def boolCaptured : Prog C BΓ (.val .bool :: BΓ) :=
  .cons (.declLocal .bool (.fresh "se" 0) (some (.simple (.local i2))))
    (.cons (.block (boolThen.guarded true (boolElse.guarded false))) .nil)
private def boolObserved (c : Bool) : Option (Bool × Bool) :=
  (((Prog.runSt (boolStart c) boolCaptured).map (State.drop (.push .refl))).map
    (fun σ => (σ.env.1, σ.env.2.1))).toOption

theorem actualBooleanPlan : Upd.ifJoin? (.pvV i2) boolThen.program boolElse.program =
    some (.inr (boolThen.guarded true (boolElse.guarded false))) := rfl

theorem boolDependentTrue : boolObserved true = some (true, true) := by
  unfold boolObserved boolCaptured
  rw [LocalWrites.captured_drop_runSt (boolStart true) (.fresh "se" 0) (.local i2) boolThen boolElse]
  rfl

theorem boolDependentFalse : boolObserved false = some (false, false) := by
  unfold boolObserved boolCaptured
  rw [LocalWrites.captured_drop_runSt (boolStart false) (.fresh "se" 0) (.local i2) boolThen boolElse]
  rfl

/-- The earlier mixed primitive/failure fixture is selected by the actual query. -/
theorem actualMixedPlan : Upd.ifJoin? (.pvV (.here : Idx Γ (.val .bool))) yes.program no.program =
    some (.inr (yes.guarded true (no.guarded false))) := rfl

/-- A different Boolean operator is not the canonical normalization. -/
example : eligible
    [⟨.bool, i0, nonSimpleBool⟩, ⟨.bool, i0, .binop (p := .bool) (q := .bool) .or rfl rfl
      (.simple (.local i0)) (.simple (.bool true))⟩] (andB i0) = true := rfl
example : eligible (orA i0)
    [⟨.bool, i0, nonSimpleBool⟩, ⟨.bool, i0, .binop (p := .bool) (q := .bool) .and rfl rfl
      (.simple (.local i0)) (.simple (.bool false))⟩] = true := rfl

private def addHead : Thin BΓ (.val .uint :: BΓ) := .drop .refl
private def addBelow : Thin BΓ [.val .bool, .val .uint, .val .bool, .val .bool] := .keep (.drop .refl)

/-- Recognition stays exact with a new head or a local inserted below it. -/
example : JoinBoundary.boundary
    (LocalWrites.wk addHead (andA i0 i0 i0 nonSimpleBool true))
    (LocalWrites.wk addHead (andB i0)) = true := rfl
example : JoinBoundary.boundary
    (LocalWrites.wk addBelow (orA i0))
    (LocalWrites.wk addBelow (orB i0 i0 i0 nonSimpleBool false)) = true := rfl
example : JoinBoundary.boundary
    (LocalWrites.wk addBelow (andA i0 i1 i0 nonSimpleBool true))
    (LocalWrites.wk addBelow (andB i0)) = false := rfl

/-- The opposite branch literal is also part of the exact canonical shape. -/
example : eligible (andA i0 i0 i0 nonSimpleBool true)
    [⟨.bool, i0, .simple (.bool true)⟩] = true := rfl
example : eligible [⟨.bool, i0, .simple (.bool false)⟩]
    (orB i0 i0 i0 nonSimpleBool false) = true := rfl

/-- Neither an OR prefix nor a suffix is rejected as a canonical pair. -/
example : eligible (orA i0)
    (⟨.bool, i2, .simple (.bool false)⟩ :: orB i0 i0 i0 nonSimpleBool false) = true := rfl
example : eligible (orA i0)
    (orB i0 i0 i0 nonSimpleBool false ++ [⟨.bool, i2, .simple (.bool false)⟩]) = true := rfl

private def falseStart : State C BΓ :=
  (((State.init C).push (t := .val .bool) false).push (t := .val .bool) true).push (t := .val .bool) true
private def elseObserved : Option (Bool × Bool) :=
  (((Prog.runSt falseStart boolCaptured).map (State.drop (.push .refl))).map
    (fun σ => (σ.env.1, σ.env.2.1))).toOption

/-- The selected else really changes its true destination and keeps the
other true local; skipping the branch cannot satisfy this observation. -/
theorem elseWritesFromTrue : elseObserved = some (false, true) := by
  unfold elseObserved boolCaptured
  rw [LocalWrites.captured_drop_runSt falseStart (.fresh "se" 0) (.local i2) boolThen boolElse]
  rfl

/-- The unchanged-state observation is refuted by the actual execution. -/
example : elseObserved ≠ some (true, true) := by
  rw [elseWritesFromTrue]
  decide

/-- Existing singleton branches still select their parallel update plan. -/
theorem singletonPlan : Upd.ifJoin? (.pvV i2) (andB i0).program (orA i1).program =
    some (.inl (Upd.ifJoin (.pvV i2)
      (some ⟨.bool, i0, .simple (.bool false)⟩)
      (some ⟨.bool, i1, .simple (.bool true)⟩))) := rfl

/-- The actual one-rule dispatcher selects the new captured sequence plan. -/
theorem stepSequence : Stmt.step 0 .box (.ite (.simple (.local i2)) boolThen.program boolElse.program) =
    Premise.capture .bool (fse 0) (.simple (.local i2))
      (.block (boolThen.guarded true (boolElse.guarded false))) := rfl

/-- The new row is a kernel-checked Lean-only rule instance. -/
theorem sequenceRow : LeanTaclet C 0 .box
    (.ite (.simple (.local i2)) boolThen.program boolElse.program)
    (Premise.capture .bool (fse 0) (.simple (.local i2))
      (.block (boolThen.guarded true (boolElse.guarded false)))) :=
  .ifElseJoinSequence rfl

/-- A canonical short-circuit shape still chooses the existing split step. -/
theorem stepCanonical : Stmt.step 0 .box
    (.ite (.simple (.local i2)) (andA i0 i0 i0 nonSimpleBool true).program (andB i0).program) =
    Premise.split .block (Fml.isBool (.pvV i2) true) (Fml.isBool (.pvV i2) false)
      (andA i0 i0 i0 nonSimpleBool true).program (andB i0).program := rfl

end Solidity.Examples.Tactics.JoinSequence
