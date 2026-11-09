import Solidity.Source.Eval
import Solidity.Lowering.V08.EnvironmentProjection

/-!
# Actual resolved environment reads

These laws execute published independent Source.evalE, not a source evaluator
constructed from the intrinsic result. They cover positive horizons and both
pipelines, retaining the complete source machine state. Frame/admission, body
lowering, ABI/layout and source-unit composition remain separate obligations.
-/
namespace Solidity.Lowering.V08.SourceEnvironment
open Solidity
open Source

/-- The existing request observations of an actual source frame. -/
def frameRequest {E : Source.Env} (global : Glob E) (frame : Fr)
    (input : Roadmap.Bytes) : Roadmap.Request :=
  { sender := frame.sender, target := frame.this, value := frame.value,
    timestamp := global.timestamp, input := input }

/-- A resolved sender read completes without altering locals, journal, memory,
events or logs, for every positive horizon and either pipeline. -/
theorem eval_sender {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalE global frame (horizon + 1)
      (.magic .msg "sender" rfl : RExpr E Γ (.address false))).run (locals, state) =
      (.ok (.val (.address frame.sender)), (locals, state)) := rfl

/-- Zero is an unfinished source horizon, not a target revert or divergence. -/
theorem sender_zero_horizon {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalE global frame 0
      (.magic .msg "sender" rfl : RExpr E Γ (.address false))).run (locals, state) =
      (.error .timeout, (locals, state)) := rfl

/-- Actual source execution and the intrinsic environment read agree on the
same sender through the existing total address adapter. No source execution or
preservation equality is assumed. The target state is explicitly projected;
this is not admission of an arbitrary target frame. -/
theorem sender_transport {E : Source.Env} {Γ : RCtx} {K : Type}
    {contracts : K → Contract} {C : Contract} {Δ : Ctx}
    (global : Glob E) (frame : Fr) (horizon : Nat)
    (locals : Source.Locals E.layout Γ) (source : Source.St E)
    (target : ContractWorld.World contracts) (state : State C Δ)
    (responses : List (Semantics.ExtKey × Semantics.ExtResult)) (input : Roadmap.Bytes) :
    (Source.evalE global frame (horizon + 1)
      (.magic .msg "sender" rfl : RExpr E Γ (.address false))).run (locals, source) =
      (.ok (.val (.address frame.sender)), (locals, source)) ∧
    (Solidity.Val.simple (.env .msgSender rfl) : Solidity.Val C Δ .uint).evalT
      (EnvironmentProjection.stateEnvironment source.ex.world target
        (frameRequest global frame input) responses state) =
      .ok (EnvironmentProjection.liftAddress frame.sender).1 :=
  ⟨eval_sender global frame horizon locals source, rfl⟩

/-- The resolved expression statement executes the same actual source read,
then discards its value while retaining its input locals and complete machine. -/
theorem exec_sender {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS global frame (horizon + 2) 0 none
      (.expr (.magic .msg "sender" rfl) : RStmt E [] false .body Γ Γ) locals).run
        (Source.L0 E, state) =
      (.ok (.normal locals), (Source.L0 E, state)) := rfl

/-- Source u256 range follows from the existing bounded request word. -/
private theorem word_range (word : Roadmap.Word) :
    IntTy.u256.lo ≤ (word.val : Int) ∧ (word.val : Int) ≤ IntTy.u256.hi := by
  change 0 ≤ (word.val : Int) ∧ (word.val : Int) ≤ ((2 ^ 256 - 1 : Nat) : Int)
  have bound : word.val ≤ 2 ^ 256 - 1 := by have h := word.isLt; omega
  exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr bound⟩

def sourceWord {D : Source.Layout} (word : Roadmap.Word) : Source.Val D (.int IntTy.u256) :=
  .int word.val (word_range word)

set_option backward.isDefEq.respectTransparency false in
theorem eval_value {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalE global frame (horizon + 1)
      (.magic .msg "value" rfl : RExpr E Γ (.int IntTy.u256))).run (locals, state) =
      (.ok (.val (sourceWord frame.value)), (locals, state)) := by
  simp only [Source.evalE, Source.mkInt, dite_eq_left (word_range frame.value), Source.EM.lift]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem eval_timestamp {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalE global frame (horizon + 1)
      (.magic .block "timestamp" rfl : RExpr E Γ (.int IntTy.u256))).run (locals, state) =
      (.ok (.val (sourceWord global.timestamp)), (locals, state)) := by
  simp only [Source.evalE, Source.mkInt, dite_eq_left (word_range global.timestamp), Source.EM.lift]
  rfl

/-- Exact actual source and intrinsic word observations, with the timestamp
and payment taken from their distinct published context fields. -/
theorem value_timestamp_transport {E : Source.Env} {Γ : RCtx} {K : Type}
    {contracts : K → Contract} {C : Contract} {Δ : Ctx}
    (global : Glob E) (frame : Fr) (horizon : Nat)
    (locals : Source.Locals E.layout Γ) (source : Source.St E)
    (target : ContractWorld.World contracts) (state : State C Δ)
    (responses : List (Semantics.ExtKey × Semantics.ExtResult)) (input : Roadmap.Bytes) :
    (Source.evalE global frame (horizon + 1)
      (.magic .msg "value" rfl : RExpr E Γ (.int IntTy.u256))).run (locals, source) =
      (.ok (.val (sourceWord frame.value)), (locals, source)) ∧
    (Source.evalE global frame (horizon + 1)
      (.magic .block "timestamp" rfl : RExpr E Γ (.int IntTy.u256))).run (locals, source) =
      (.ok (.val (sourceWord global.timestamp)), (locals, source)) ∧
    (Solidity.Val.simple (.env .msgValue rfl) : Solidity.Val C Δ .uint).evalT
      (EnvironmentProjection.stateEnvironment source.ex.world target
        (frameRequest global frame input) responses state) =
      .ok (EnvironmentProjection.liftWord frame.value) ∧
    (Solidity.Val.simple (.env .timestamp rfl) : Solidity.Val C Δ .uint).evalT
      (EnvironmentProjection.stateEnvironment source.ex.world target
        (frameRequest global frame input) responses state) =
      .ok (EnvironmentProjection.liftWord global.timestamp) :=
  ⟨eval_value global frame horizon locals source,
    eval_timestamp global frame horizon locals source, rfl, rfl⟩

#print axioms eval_value
#print axioms eval_timestamp
#print axioms value_timestamp_transport
#print axioms exec_sender
#print axioms eval_sender
#print axioms sender_zero_horizon
#print axioms sender_transport
end Solidity.Lowering.V08.SourceEnvironment
