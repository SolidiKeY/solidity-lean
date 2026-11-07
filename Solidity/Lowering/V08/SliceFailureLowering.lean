import Solidity.Source.Calldata
import Solidity.Lowering.V08.SourceEnvironment
import Solidity.Backend.Failure.Correct

/-! Exact Source calldata-slice evaluation and certified empty-terminal failure
transport. Bounds run in the existing evaluator; this does not emit a runtime
bounds-check branch or copy unknown calldata into target memory. -/
namespace Solidity.Lowering.V08.SliceFailureLowering
open Solidity Source Backend

def context (τ : STy) (Γ : RCtx) : RCtx := τ :: .int IntTy.u256 :: .int IntTy.u256 :: Γ

def expression {E : Env} {Γ : RCtx} (τ : STy) (allowed : τ.sliceable = true)
    (toEnd : Bool) : RExpr E (context τ Γ) τ :=
  .slice (.local .here) allowed (.local (.there .here)) rfl
    (.local (.there (.there .here))) rfl toEnd

def caller {E : Env} {Γ : RCtx} {τ : STy} (loc : τ.loc? = some .calldata)
    (offset length : Nat) (start stop : Roadmap.Word) (older : Locals E.layout Γ) :
    Locals E.layout (context τ Γ) :=
  .cons (.cdRef loc offset length) (.cons (SourceEnvironment.sourceWord start)
    (.cons (SourceEnvironment.sourceWord stop) older))

/-- A complete equation for the actual typed expression, for every current
caller, state, calldata and full-word unsigned bounds. No decoder-success premise. -/
theorem run {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (τ : STy) (allowed : τ.sliceable = true) (loc : τ.loc? = some .calldata)
    (offset length : Nat) (start stop : Roadmap.Word) (toEnd : Bool)
    (older : Locals E.layout Γ) (state : St E) :
    (evalE G F (n+2) (expression τ allowed toEnd)).run
      (caller loc offset length start stop older,state) =
      (match sliceR (.cdRef loc offset length) start.val stop.val toEnd with
       | .ok value => .ok (.val value)
       | .error halt => .error halt,
       (caller loc offset length start stop older,state)) := by
  simp only [expression, evalE, caller, EM.locals, EM.lift, getV, RVal.get,
    indexNat, RVal.amount, SourceEnvironment.sourceWord, Locals.get,
    bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.run,
    ExceptT.mk, StateT.bind, StateT.pure, StateT.get, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
    Functor.map, StateT.map, Except.pure, Int.toNat_natCast]
  cases h : sliceR (Val.cdRef loc offset length) start.val stop.val toEnd <;> rfl

/-- Accepted slicing changes only the existing reference coordinates. -/
theorem accepted {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (τ : STy) (allowed : τ.sliceable = true) (loc : τ.loc? = some .calldata)
    (offset length : Nat) (start stop : Roadmap.Word)
    (ordered : start.val ≤ stop.val) (bounded : stop.val ≤ length)
    (older : Locals E.layout Γ) (state : St E) :
    (evalE G F (n+2) (expression τ allowed false)).run
      (caller loc offset length start stop older,state) =
      (.ok (.val (.cdRef loc
        (offset + τ.cdStride * start.val)
        (stop.val-start.val))), (caller loc offset length start stop older,state)) := by
  rw [run]
  simp only [sliceR, Bool.false_eq_true, ↓reduceIte, if_neg (Nat.not_lt.mpr ordered), if_neg (Nat.not_lt.mpr bounded)]
  rfl

theorem reversed {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (τ : STy) (allowed : τ.sliceable = true) (loc : τ.loc? = some .calldata)
    (offset length : Nat) (start stop : Roadmap.Word) (wrong : stop.val < start.val)
    (older : Locals E.layout Γ) (state : St E) :
    (evalE G F (n+2) (expression τ allowed false)).run
      (caller loc offset length start stop older,state) =
      (.error (.revert []),(caller loc offset length start stop older,state)) := by
  rw [run]
  simp only [sliceR, Bool.false_eq_true, ↓reduceIte, if_pos wrong]

theorem beyond {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (τ : STy) (allowed : τ.sliceable = true) (loc : τ.loc? = some .calldata)
    (offset length : Nat) (start stop : Roadmap.Word) (ordered : start.val ≤ stop.val)
    (wrong : length < stop.val) (older : Locals E.layout Γ) (state : St E) :
    (evalE G F (n+2) (expression τ allowed false)).run
      (caller loc offset length start stop older,state) =
      (.error (.revert []),(caller loc offset length start stop older,state)) := by
  rw [run]
  simp only [sliceR, Bool.false_eq_true, ↓reduceIte, if_neg (Nat.not_lt.mpr ordered), if_pos wrong]

/-- Even an invalid range times out first if the actual child expression has
no horizon. This is not a completed revert or an emitted timeout model. -/
theorem exhausted {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr)
    (τ : STy) (allowed : τ.sliceable = true) (toEnd : Bool)
    (locals : Locals E.layout (context τ Γ)) (state : St E) :
    (evalE G F 1 (expression τ allowed toEnd)).run (locals,state) =
      (.error .timeout,(locals,state)) := by rfl

/-- The Source revert paired with the empty checked terminal. The target side does
not depend on the slice expression (it holds for an accepted range too), so this
is not a lowered bounds check; runtime target bounds checking is not supplied. -/
theorem lowered_reversed {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (τ : STy) (allowed : τ.sliceable = true) (loc : τ.loc? = some .calldata)
    (offset length : Nat) (start stop : Roadmap.Word) (wrong : stop.val < start.val)
    (older : Locals E.layout Γ) (state : St E)
    (outputOffset : Nat) (suffix : Backend.Program) (machine : Failure.Slice.Machine)
    (fits : Failure.Fits outputOffset []) (stack : machine.stack.length+2≤1024) :
    (evalE G F (n+2) (expression τ allowed false)).run
      (caller loc offset length start stop older,state) =
      (.error (.revert []),(caller loc offset length start stop older,state)) ∧
    Failure.Slice.checkedRun (Failure.emit outputOffset .empty ++ suffix) machine =
      some ({machine with memory := Failure.Slice.putBytes machine.memory outputOffset []},
        some (.revert [])) :=
  ⟨reversed G F n τ allowed loc offset length start stop wrong older state,
    Failure.checkedRun_emit_suffix outputOffset .empty suffix machine fits stack⟩

/-- The absent end uses the logical reference length; the end local is still
executed by evalE before sliceR chooses that length. -/
theorem accepted_toEnd {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (τ : STy) (allowed : τ.sliceable = true) (loc : τ.loc? = some .calldata)
    (offset length : Nat) (start stop : Roadmap.Word) (bounded : start.val ≤ length)
    (older : Locals E.layout Γ) (state : St E) :
    (evalE G F (n+2) (expression τ allowed true)).run
      (caller loc offset length start stop older,state) =
      (.ok (.val (.cdRef loc
        (offset + τ.cdStride * start.val)
        (length-start.val))), (caller loc offset length start stop older,state)) := by
  rw [run]
  simp only [sliceR, ↓reduceIte, if_neg (Nat.not_lt.mpr bounded),
    Nat.lt_irrefl]
  rfl

/-- Actual subsequent bytes observation, not a target byte-memory encoder.
Slice acceptance does not validate that the logical reference is in input. -/
theorem observed_bytes {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (offset length : Nat) (start stop : Roadmap.Word)
    (ordered : start.val ≤ stop.val) (bounded : stop.val ≤ length)
    (older : Locals E.layout Γ) (state : St E) :
    ((do let value ← evalE G F (n+2) (expression (.bytes .calldata) rfl false)
         bytesOfRV F n value) : EM E (context (.bytes .calldata) Γ) Roadmap.Bytes).run
      (caller rfl offset length start stop older,state) =
      (.ok ((F.cd.drop (offset+start.val)).take (stop.val-start.val)),
        (caller rfl offset length start stop older,state)) := by
  simp only [bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind]
  have step := accepted G F n (.bytes .calldata) rfl rfl offset length start stop ordered bounded older state
  simp only [ExceptT.run] at step
  rw [step]
  simp only [STy.cdStride, Nat.one_mul]
  rfl

/-- The two actual bound failures exhaust the explicit-end invalid range. -/
theorem invalid {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (τ : STy) (allowed : τ.sliceable = true) (loc : τ.loc? = some .calldata)
    (offset length : Nat) (start stop : Roadmap.Word)
    (wrong : stop.val < start.val ∨ length < stop.val)
    (older : Locals E.layout Γ) (state : St E) :
    (evalE G F (n+2) (expression τ allowed false)).run
      (caller loc offset length start stop older,state) =
      (.error (.revert []),(caller loc offset length start stop older,state)) := by
  by_cases ordered : start.val ≤ stop.val
  · exact beyond G F n τ allowed loc offset length start stop ordered (by omega) older state
  · exact reversed G F n τ allowed loc offset length start stop (Nat.lt_of_not_ge ordered) older state
end Solidity.Lowering.V08.SliceFailureLowering
