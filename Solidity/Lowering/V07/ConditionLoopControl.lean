import Solidity.Lowering.V07.P12Controls

/-! Negative P12 consumer/Backfill B control using the EXISTING TLoop API.
Capturing a condition only once is unsound when a body changes its RHS. This
module builds no G19 lowering, Source loop semantics, loop AST or evaluator.
All natural prefixes below belong to an intentionally wrong intrinsic loop. -/
namespace Solidity.Lowering.V07.ConditionLoopControl
open Source.SemanticsExamples
abbrev C := P12Controls.C
abbrev E := P12Controls.E
abbrev SrcCtx : Source.RCtx := .bool :: P12Controls.SrcCtx
abbrev TgtCtx : Ctx := .val .bool :: P12Controls.TgtCtx
abbrev CapturedCtx : Ctx := .val .bool :: TgtCtx

def source : Source.EMState E SrcCtx :=
  (.cons (.bool false) P12Controls.source.1,P12Controls.source.2)
def target : State C TgtCtx := P12Controls.target.push (t := .val .bool) false

def sourceFirst : Source.EMState E SrcCtx :=
  (source.1.set (.there .here) (.bool true),source.2)
def sourceBody : Source.EMState E SrcCtx :=
  (sourceFirst.1.set (.there (.there .here)) (.bool false),source.2)
def sourceStopped : Source.EMState E SrcCtx :=
  (sourceBody.1.set (.there .here) (.bool false),source.2)
def before : State C CapturedCtx :=
  (target.setLocal (.there .here) true).push (t := .val .bool) true
def after : State C CapturedCtx := before.setLocal (.there (.there (.there .here))) false

def bodyCode : Prog C CapturedCtx CapturedCtx :=
  .cons (.assignLocal (.there (.there (.there .here))) (.simple (.local (.there .here)))) .nil
/-- Adapters invoke the published typed program/value operations directly. -/
def body (state : State C CapturedCtx) : TRes (State C CapturedCtx) :=
  (bodyCode.run state).map (fun out => out.st)
def condition (state : State C CapturedCtx) : TRes Bool :=
  (.simple (.local .here) : Val C CapturedCtx .bool).evalT state

theorem actual_first_condition (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) F0 (fuel+2)
      (.assign (.local (.there .here)) (.local (.there (.there .here))))).run source =
        (.ok (.val (.bool true)),sourceFirst) ∧
    (assignLocalOperand (.there .here : Idx TgtCtx (.val .bool)) (.there (.there .here))).code.run target =
      .ok (⟨before,List.prefix_refl _⟩) :=
  ⟨source_assign_local_run (MixedAssignmentControls.globals p) F0 fuel source
    (.there .here) (.there (.there .here)) (.bool true) rfl,
    assigned_condition_prefix_run target (.there .here) (.there (.there .here))⟩

theorem actual_body_source (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) F0 (fuel+2)
      (.assign (.local (.there (.there .here))) (.local .here))).run sourceFirst =
        (.ok (.val (.bool false)),sourceBody) :=
  source_assign_local_run (MixedAssignmentControls.globals p) F0 fuel sourceFirst
    (.there (.there .here)) .here (.bool false) rfl

theorem actual_second_source_condition (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) F0 (fuel+2)
      (.assign (.local (.there .here)) (.local (.there (.there .here))))).run sourceBody =
        (.ok (.val (.bool false)),sourceStopped) :=
  source_assign_local_run (MixedAssignmentControls.globals p) F0 fuel sourceBody
    (.there .here) (.there (.there .here)) (.bool false) rfl

theorem body_first : body before = .ok after := rfl
theorem body_fixed : body after = .ok after := rfl
theorem captured_first : condition before = .ok true := rfl
theorem captured_stale : condition after = .ok true := rfl

theorem actual_refreshed_target_condition :
    (assignLocalOperand (.there (.there .here) : Idx CapturedCtx (.val .bool))
      (.there (.there (.there .here)))).code.run after =
        .ok (⟨(after.setLocal (.there (.there .here)) false).push (t := .val .bool) false,
          List.prefix_refl _⟩) :=
  assigned_condition_prefix_run after (.there (.there .here)) (.there (.there (.there .here)))

theorem wrong_once_captured_condition :
    condition after ≠
      (.simple (.local .here) : Val C (.val .bool :: CapturedCtx) .bool).evalT
        ((after.setLocal (.there (.there .here)) false).push (t := .val .bool) false) := by
  rw [captured_stale]
  change (Except.ok true : TRes Bool) ≠ .ok false
  intro same
  cases same

theorem step_first : TLoop.step body condition before = .inl after := by
  rw [TLoop.step,captured_first,body_first]
theorem step_fixed : TLoop.step body condition after = .inl after := by
  rw [TLoop.step,captured_stale,body_fixed]

/-- Genuine induction, with no admission or observation limit on n. -/
theorem every_stale_prefix (n : Nat) : TLoop.iterN body condition n after = .inl after := by
  induction n with
  | zero => rfl
  | succ n ih => rw [TLoop.iterN,step_fixed]; exact ih

theorem every_positive_stale_prefix (n : Nat) :
    TLoop.iterN body condition (n+1) before = .inl after := by
  rw [TLoop.iterN,step_first]
  exact every_stale_prefix n

theorem mixed_live_frames :
    after.glob = P12Controls.target.glob ∧ sourceStopped.2 = source.2 ∧
    after.heap.len P12Controls.memoryRef .dyn = 2 ∧
    TEnv.get (.there (.there (.there (.there (.there (.there .here)))))) after.env = some P12Controls.memoryRef ∧
    TEnv.get (.there (.there (.there (.there (.there (.there (.there .here))))))) after.env =
      some MixedAssignmentControls.storageRef :=
  ⟨rfl,rfl,P12Controls.live_memory_and_storage.2.1,rfl,rfl⟩

end Solidity.Lowering.V07.ConditionLoopControl
