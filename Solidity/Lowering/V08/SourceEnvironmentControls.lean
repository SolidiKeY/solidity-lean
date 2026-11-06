import Solidity.Lowering.V08.SourceEnvironment
import Solidity.Lowering.V08.Controls
import Solidity.Roadmap.Controls

/-! Populated independent source execution and actual paid intrinsic call.
The source/target stores are deliberately not identified: this checks the sender
observation and complete source-state retention, not general layout/body lowering.
-/
namespace Solidity.Lowering.V08.SourceEnvironmentControls
open Solidity
open Source
open SourceEnvironment

def savedDecl : Source.Decl :=
  { kind := .stateVar, name := "saved", scope := some "C", top := false,
    node := .stateVar (.elem .bool) none none none false "saved" .none }
def scratchDecl : Source.Decl :=
  { kind := .stateVar, name := "scratch", scope := some "C", top := false,
    node := .stateVar (.elem .bool) none none none true "scratch" .none }
def E : Source.Env := ⟨[savedDecl, scratchDecl]⟩
def sender : Roadmap.Address := ⟨1, by decide +kernel⟩
def self : Roadmap.Address := ⟨2, by decide +kernel⟩
def saved : Source.SPath := ⟨⟨some "C", "saved"⟩, []⟩
def scratch : Source.SPath := ⟨⟨some "C", "scratch"⟩, []⟩
def empty : Source.St E :=
  ⟨⟨⟨fun _ => Source.Account.empty _⟩, Source.Transient.empty, []⟩,
    Source.Heap.empty, [], [], ⟨[], .nil⟩, Source.FailureExecution.Cursor.empty⟩
def populated : Source.St E :=
  { empty with
    ex := empty.ex.run [
      .account sender (fun a => { a with balance := 93 }),
      .account self (fun a => { a with balance := 7, nonce := 1, code := some 0, storage := a.storage.write saved (.bool true) }),
      .transient self (fun t => t.write scratch (.bool true))]
    heap := (Source.Heap.empty.alloc ⟨.bytes .memory, .bytes [0, 0xff]⟩).1
    events := [.call self ⟨7, by decide +kernel⟩ [0, 0xff] false]
    logs := [(self, [0xab, 0, 0xff])]
    fnLocals := ⟨[.bool], .cons (.bool true) .nil⟩ }
def program : Source.Program E :=
  { body := fun _ => none, consts := fun _ => none, inits := fun _ => [],
    ctor := fun _ => none, ctorLocals := fun _ => [], baseArgs := fun _ => [],
    contracts := ["C"] }
def global (pipeline : Roadmap.Pipeline) : Source.Glob E :=
  { prog := program, pipeline := pipeline, fixed := Roadmap.Controls.toyFixed,
    balance0 := fun _ => ⟨100, by decide +kernel⟩, hasCode := fun _ _ => false,
    callee := fun _ => .answer (.success []), timestamp := ⟨12345, by decide +kernel⟩ }
def frame : Source.Fr :=
  { this := self, sender := sender, value := ⟨7, by decide +kernel⟩,
    static := false, contract := "C" }
def locals : Source.Locals E.layout [.bool] := .cons (.bool true) .nil

theorem populated_snapshot :
    (populated.ex.world.accounts sender).balance = 93 ∧
    (populated.ex.world.accounts self).balance = 7 ∧
    (populated.ex.world.accounts self).nonce = 1 ∧
    (populated.ex.world.accounts self).code = some 0 ∧
    (populated.ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (populated.ex.transient.cells self).read scratch = some (.bool true) ∧
    populated.ex.journal.length = 3 ∧ populated.heap.next = 1 ∧
    populated.heap.get 0 = some ⟨.bytes .memory, .bytes [0, 0xff]⟩ ∧
    populated.events = [.call self ⟨7, by decide +kernel⟩ [0, 0xff] false] ∧
    populated.logs = [(self, [0xab, 0, 0xff])] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem source_both_pipelines (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.evalE (global pipeline) frame (horizon + 1)
      (.magic .msg "sender" rfl : RExpr E [.bool] (.address false))).run (locals, populated) =
      (.ok (.val (.address sender)), (locals, populated)) :=
  eval_sender (global pipeline) frame horizon locals populated

theorem source_body (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.execS (global pipeline) frame (horizon + 2) 0 none
      (.expr (.magic .msg "sender" rfl) : RStmt E [] false .body [.bool] [.bool]) locals).run
        (Source.L0 E, populated) =
      (.ok (.normal locals), (Source.L0 E, populated)) :=
  exec_sender (global pipeline) frame horizon locals populated

theorem source_timeout (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 0
      (.magic .msg "sender" rfl : RExpr E [.bool] (.address false))).run (locals, populated) =
      (.error .timeout, (locals, populated)) :=
  sender_zero_horizon (global pipeline) frame locals populated

/-- A real paid typed body writes both regions before returning its sender. -/
def paidEntry : ContractWorld.Entry Controls.Cell Semantics.Word :=
  { locals := [], body := sol[Controls.Cell]{ saved = 3; scratch = 9; }, payable := true,
    result := fun state => (Solidity.Val.simple (.env .msgSender rfl) : Solidity.Val Controls.Cell [] .uint).evalT state }
def paidObservation : TRes (Option (Int × Int × Int × Int) × Semantics.Word) := do
  let world ← Controls.setup
  let (next, value) ← world.call (⟨Controls.self⟩ : ContractWorld.Handle ()) paidEntry Controls.paidCtx
  pure (Controls.observe next, value)

theorem paid_actual_sender : paidObservation.toOption =
    some (some (93, 7, 3, 9), (EnvironmentProjection.liftAddress sender).1) := by decide +kernel

theorem wrong_self : paidObservation.toOption ≠
    some (some (93, 7, 3, 9), (EnvironmentProjection.liftAddress self).1) := by
  rw [paid_actual_sender]
  decide +kernel

theorem no_skipped_payment : paidObservation.toOption ≠
    some (some (100, 0, 3, 9), (EnvironmentProjection.liftAddress sender).1) := by
  rw [paid_actual_sender]
  decide +kernel

/-- Same source/target sender observation, derived from both actual executions. -/
theorem execution_combination (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 1
      (.magic .msg "sender" rfl : RExpr E [.bool] (.address false))).run (locals, populated) =
      (.ok (.val (.address sender)), (locals, populated)) ∧
    paidObservation.toOption = some (some (93, 7, 3, 9),
      (EnvironmentProjection.liftAddress sender).1) :=
  ⟨source_both_pipelines pipeline 0, paid_actual_sender⟩

theorem source_value_time (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.evalE (global pipeline) frame (horizon + 1)
      (.magic .msg "value" rfl : RExpr E [.bool] (.int IntTy.u256))).run (locals, populated) =
      (.ok (.val (sourceWord frame.value)), (locals, populated)) ∧
    (Source.evalE (global pipeline) frame (horizon + 1)
      (.magic .block "timestamp" rfl : RExpr E [.bool] (.int IntTy.u256))).run (locals, populated) =
      (.ok (.val (sourceWord (global pipeline).timestamp)), (locals, populated)) :=
  ⟨eval_value (global pipeline) frame horizon locals populated,
    eval_timestamp (global pipeline) frame horizon locals populated⟩

def contextEntry : ContractWorld.Entry Controls.Cell (List Int) :=
  { paidEntry with result := fun state => do
      let s ← (Solidity.Val.simple (.env .msgSender rfl) : Solidity.Val Controls.Cell [] .uint).evalT state
      let v ← (Solidity.Val.simple (.env .msgValue rfl) : Solidity.Val Controls.Cell [] .uint).evalT state
      let t ← (Solidity.Val.simple (.env .timestamp rfl) : Solidity.Val Controls.Cell [] .uint).evalT state
      let a ← (Solidity.Val.simple (.env .selfAddress rfl) : Solidity.Val Controls.Cell [] .uint).evalT state
      let b ← (Solidity.Val.simple (.env .selfBalance rfl) : Solidity.Val Controls.Cell [] .uint).evalT state
      pure [s.1, v.1, t.1, a.1, b.1] }

def contextObservation : TRes (Option (Int × Int × Int × Int) × List Int) := do
  let world ← Controls.setup
  let (next, value) ← (world.atTime (EnvironmentProjection.liftWord ⟨12345, by decide +kernel⟩)).call
    (⟨Controls.self⟩ : ContractWorld.Handle ()) contextEntry Controls.paidCtx
  pure (Controls.observe next, value)

theorem actual_paid_context : contextObservation.toOption =
    some (some (93, 7, 3, 9), [1, 7, 12345, 2, 7]) := by decide +kernel

theorem wrong_context_order : contextObservation.toOption ≠
    some (some (93, 7, 3, 9), [1, 12345, 7, 2, 7]) := by
  rw [actual_paid_context]
  decide +kernel

def maximumSender : Roadmap.Address := ⟨2 ^ 160 - 1, by decide +kernel⟩
theorem maximum_sender (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) { frame with sender := maximumSender } 1
      (.magic .msg "sender" rfl : RExpr E [.bool] (.address false))).run (locals, populated) =
      (.ok (.val (.address maximumSender)), (locals, populated)) :=
  eval_sender (global pipeline) _ 0 locals populated

theorem timeout_not_revert (pipeline : Roadmap.Pipeline) :
    ((Source.evalE (global pipeline) frame 0
      (.magic .msg "sender" rfl : RExpr E [.bool] (.address false))).run
        (locals, populated)).1 ≠ .error (.revert [0, 0xff]) := by
  rw [source_timeout]
  intro impossible
  cases impossible

#print axioms source_value_time
#print axioms actual_paid_context
#print axioms wrong_context_order
#print axioms maximum_sender
#print axioms timeout_not_revert
#print axioms populated_snapshot
#print axioms source_both_pipelines
#print axioms source_body
#print axioms source_timeout
#print axioms paid_actual_sender
#print axioms wrong_self
#print axioms no_skipped_payment
#print axioms execution_combination
end Solidity.Lowering.V08.SourceEnvironmentControls
