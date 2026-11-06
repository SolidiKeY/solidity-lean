import Solidity.Lowering.V08.SourceTransactionControls
import Solidity.Lowering.V08.WorldImageAccess
import Solidity.Lowering.V08.AbiObservations

/-! Actual request-clock execution with storage/transient effects. This is an
explicit hand-written Source RBody/typed-world client, not syntax extraction or canonical compilation,
layout, admission or bytecode adequacy. Source timeout is not a target halt. -/
namespace Solidity.Lowering.V08.SourceClockTransactions
open Solidity Source Source.SemanticsExamples

theorem request_clock_override {E : Source.Env} (g : Source.Glob E)
    (timestamp : Roadmap.Word) (horizon : Nat) (q : Roadmap.Request) :
    Source.runTx {g with timestamp := timestamp} horizon q = Source.runTx g horizon q := by
  rfl

def clockBody : Source.RBody EB :=
  ⟨[],[uint],false,[uint],[uint],
    .stmt (setX (lit 5)) (.stmt (setT (lit 7))
      (.stmt (.retVal rfl (.magic .block "timestamp" rfl) rfl) .nil)),[]⟩
def program : Source.Program EB :=
  {PB with body := fun d => if d.name = "g" then some clockBody else PB.body d}
def global (p : Roadmap.Pipeline) : Source.Glob EB :=
  {SourceTransactionControls.global p with prog := program, timestamp := word 99}
def request : Roadmap.Request := SourceTransactionControls.request (selOf "g()")
def returned : Roadmap.Bytes := wordBytes (toWord 12345)
def success (bytes : Roadmap.Bytes) : Source.St EB :=
  {SourceTransactionControls.success bytes with events :=
    (SourceTransactionControls.initial bytes).events ++
      [.tx user thisC (word 0) (word 12345) (selOf "g()") (.success returned)]}

theorem source_actual (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.runTx (global p) (extra+20) request).run (Source.L0 EB,SourceTransactionControls.initial bytes) =
      (.ok (.success returned),(Source.L0 EB,success bytes)) := by
  cases p <;> rfl

theorem source_timeout (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.runTx (global p) 0 request).run (Source.L0 EB,SourceTransactionControls.initial bytes) =
      (.error .timeout,(Source.L0 EB,SourceTransactionControls.timed bytes)) := by
  cases p <;> rfl

def context : ContractWorld.Context := {sender := EnvironmentProjection.liftAddress user}
def targetEntry : ContractWorld.Entry Controls.Cell Semantics.Word :=
  {locals := [], body := sol[Controls.Cell]{ saved = 5; scratch = 7; },
    result := fun state => (Solidity.Val.simple (.env .timestamp rfl) : Solidity.Val Controls.Cell [] .uint).evalT state}
def initialEntry : ContractWorld.Entry Controls.Cell Unit :=
  ContractWorld.Entry.unit sol[Controls.Cell]{ saved = 3; scratch = 4; }
def targetInitial : ContractWorld.World Controls.catalog := ContractWorld.World.empty Controls.catalog
  (fun address => if address = EnvironmentProjection.liftAddress user then EnvironmentProjection.liftWord (word 93)
    else if address = EnvironmentProjection.liftAddress thisC then EnvironmentProjection.liftWord (word 7)
    else PrimTy.dflt .uint)
def targetObserve (world : ContractWorld.World Controls.catalog) : Option (Int × Int × Int × Int × Int × Bool × Bool) := do
  let store ← world.storage? (⟨EnvironmentProjection.liftAddress thisC⟩ : ContractWorld.Handle ())
  let .prim x ← store.find (SRef.ofRoot "saved" rfl)
  let .prim t ← store.find (SRef.ofRoot "scratch" rfl)
  pure ((world.balance (EnvironmentProjection.liftAddress user)).1,
    (world.balance (EnvironmentProjection.liftAddress thisC)).1,x.1,t.1,world.timestamp.1,
    world.isLibrary (), (world.accounts (EnvironmentProjection.liftAddress thisC)).isSome)
def targetSetup : TRes (ContractWorld.World Controls.catalog) := do
  let (installed,_) ← targetInitial.create () (EnvironmentProjection.liftAddress thisC) .nil context
  let (before,_) ← installed.call (⟨EnvironmentProjection.liftAddress thisC⟩ : ContractWorld.Handle ()) initialEntry context
  pure before
def targetRun (timestamp : Semantics.Word) : TRes ((Option (Int × Int × Int × Int × Int × Bool × Bool)) × Semantics.Word) := do
  let before ← targetSetup
  let (after,status) := (before.atTime timestamp).transact (fun w =>
    w.call (⟨EnvironmentProjection.liftAddress thisC⟩ : ContractWorld.Handle ()) targetEntry context)
  let value ← status
  pure (targetObserve after,value)

-- Named standard equality instances keep synthesis small without raising limits.
private instance tailEquality : DecidableEq (Int × Int × Bool × Bool) := inferInstance
private instance vectorEquality : DecidableEq (Int × Int × Int × Int × Int × Bool × Bool) := inferInstance

theorem target_projection : (targetRun (EnvironmentProjection.liftWord request.timestamp)).toOption =
    some (some (93,7,5,0,12345,false,true),EnvironmentProjection.liftWord request.timestamp) := by
  decide +kernel

theorem target_actual : targetRun (EnvironmentProjection.liftWord request.timestamp) =
    .ok (some (93,7,5,0,12345,false,true),EnvironmentProjection.liftWord request.timestamp) := by
  have projected := target_projection
  cases run : targetRun (EnvironmentProjection.liftWord request.timestamp) with
  | error halt => rw [run] at projected; cases projected
  | ok value =>
    rw [run] at projected
    have same := Option.some.inj projected
    cases same
    rfl

theorem setup_reached : targetSetup.toOption.map targetObserve =
    some (some (93,7,3,4,0,false,true)) := by
  decide +kernel

theorem source_vector (bytes : Roadmap.Bytes) :
    ((success bytes).ex.world.accounts user).balance.val = 93 ∧
    ((success bytes).ex.world.accounts thisC).balance.val = 7 ∧
    ((success bytes).ex.world.accounts user).nonce = 3 ∧
    ((success bytes).ex.world.accounts thisC).nonce = 1 ∧
    ((success bytes).ex.world.accounts thisC).code = some 0 ∧
    readX (success bytes) = some 5 ∧ readT (success bytes) = some 0 ∧
    ((success bytes).ex.transient.cells user).read dT.path =
      some (show Source.Val EB.layout uint from .int 0 (by decide +kernel)) ∧
    (success bytes).ex.journal = [] ∧ (success bytes).heap.next = 0 ∧
    (success bytes).heap.get 0 = none ∧
    (success bytes).logs = (SourceTransactionControls.initial bytes).logs ∧
    (success bytes).fnLocals = (SourceTransactionControls.initial bytes).fnLocals ∧
    (success bytes).events = (SourceTransactionControls.initial bytes).events ++
      [.tx user thisC (word 0) (word 12345) (selOf "g()") (.success returned)] := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem return_bytes_transport : returned =
    Semantics.wordBytes (EnvironmentProjection.liftWord request.timestamp).1.toNat :=
  natWordBytes_transport 12345

theorem paired (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.runTx (global p) (extra+20) request).run (Source.L0 EB,SourceTransactionControls.initial bytes) =
      (.ok (.success returned),(Source.L0 EB,success bytes)) ∧
    (targetRun (EnvironmentProjection.liftWord request.timestamp)).map
      (fun out => (out.1,Semantics.wordBytes out.2.1.toNat)) =
      .ok (some (93,7,5,0,12345,false,true),returned) := by
  refine ⟨source_actual p extra bytes,?_⟩
  rw [target_actual]
  change Except.ok (_,Semantics.wordBytes _) = _
  rw [←return_bytes_transport]

theorem stale_clock_actual : (targetRun (EnvironmentProjection.liftWord (word 99))).toOption =
    some (some (93,7,5,0,99,false,true),EnvironmentProjection.liftWord (word 99)) := by
  decide +kernel

theorem wrong_global_bytes : returned ≠ Semantics.wordBytes 99 := by
  decide +kernel

theorem wrong_target_clock :
    (targetRun (EnvironmentProjection.liftWord (word 99))).toOption.map
      (fun out => Semantics.wordBytes out.2.1.toNat) ≠ some returned := by
  rw [stale_clock_actual]
  change some (Semantics.wordBytes 99) ≠ some returned
  intro same
  exact wrong_global_bytes (Option.some.inj same).symm

theorem timeout_not_end (bytes : Roadmap.Bytes) :
    readT (SourceTransactionControls.timed bytes) = some 4 ∧
    (SourceTransactionControls.timed bytes).ex.journal ≠ [] ∧
    (SourceTransactionControls.timed bytes).events = (SourceTransactionControls.initial bytes).events ∧
    (SourceTransactionControls.timed bytes).logs = (SourceTransactionControls.initial bytes).logs ∧
    (SourceTransactionControls.timed bytes).fnLocals = (SourceTransactionControls.initial bytes).fnLocals :=
  ⟨rfl,SourceTransactionControls.wrong_timeout_end bytes,rfl,rfl,rfl⟩

/-- Observations are taken from the actual unfinished run, not a guessed
rollback state. Heap clearing occurs, but transient end/reset and tx event do not. -/
theorem timeout_observations (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    let reached := (Source.runTx (global p) 0 request).run
      (Source.L0 EB,SourceTransactionControls.initial bytes)
    reached.1 = .error .timeout ∧
    (readX reached.2.2 = some 3 ∧ readT reached.2.2 = some 4 ∧
      (reached.2.2.ex.transient.cells user).read dT.path = some SourceTransactionControls.v9 ∧
      reached.2.2.ex.journal.length = 4 ∧ reached.2.2.heap.next = 0 ∧
      reached.2.2.events = (SourceTransactionControls.initial bytes).events ∧
      reached.2.2.logs = (SourceTransactionControls.initial bytes).logs ∧
      reached.2.2.fnLocals = (SourceTransactionControls.initial bytes).fnLocals) := by
  rw [source_timeout]
  exact ⟨rfl,SourceTransactionControls.timeout_vector bytes⟩

theorem payload_clients (p : Roadmap.Pipeline) :
    (Source.runTx (global p) 20 request).run (Source.L0 EB,SourceTransactionControls.initial []) =
      (.ok (.success returned),(Source.L0 EB,success [])) ∧
    (Source.runTx (global p) 20 request).run (Source.L0 EB,SourceTransactionControls.initial [0,255,128]) =
      (.ok (.success returned),(Source.L0 EB,success [0,255,128])) ∧
    (Source.runTx (global p) 20 request).run
      (Source.L0 EB,SourceTransactionControls.initial (List.replicate 33 0x81)) =
      (.ok (.success returned),(Source.L0 EB,success (List.replicate 33 0x81))) :=
  ⟨source_actual p 0 [],source_actual p 0 [0,255,128],source_actual p 0 (List.replicate 33 0x81)⟩

/-- The operation list certifies the actual dispatch-generated journal; it is
not an interpreter or an assumed handler result. No end/reset has occurred. -/
def rawSuccess (bytes : Roadmap.Bytes) : Source.St EB :=
  let writes := [SourceTransactionControls.creditOp,SourceTransactionControls.xOp SourceTransactionControls.v5,
    SourceTransactionControls.tOp SourceTransactionControls.v7]
  {SourceTransactionControls.initial bytes with ex := (SourceTransactionControls.initial bytes).ex.run writes}

theorem source_raw (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.dispatch {global p with timestamp := request.timestamp}
      {this := thisC, sender := user, value := word 0, static := false, contract := "C", cd := request.input}
      (extra+20) request.input).run (Source.L0 EB,SourceTransactionControls.credited bytes) =
      (.ok returned,(Source.L0 EB,rawSuccess bytes)) := by
  cases p <;> rfl

theorem raw_vector (bytes : Roadmap.Bytes) :
    readX (rawSuccess bytes) = some 5 ∧ readT (rawSuccess bytes) = some 7 ∧
    ((rawSuccess bytes).ex.transient.cells user).read dT.path = some SourceTransactionControls.v9 ∧
    (rawSuccess bytes).ex.journal.length = 6 ∧ (rawSuccess bytes).heap.next = 1 ∧
    (rawSuccess bytes).heap.get 0 = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    (rawSuccess bytes).events = (SourceTransactionControls.initial bytes).events ∧
    (rawSuccess bytes).logs = (SourceTransactionControls.initial bytes).logs ∧
    (rawSuccess bytes).fnLocals = (SourceTransactionControls.initial bytes).fnLocals := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def targetRawRun : TRes ((Option (Int × Int × Int × Int × Int × Bool × Bool)) × Semantics.Word) := do
  let before ← targetSetup
  let (after,value) ← (before.resetTransient.atTime (EnvironmentProjection.liftWord request.timestamp)).call
    (⟨EnvironmentProjection.liftAddress thisC⟩ : ContractWorld.Handle ()) targetEntry context
  pure (targetObserve after,value)

theorem target_raw : targetRawRun.toOption =
    some (some (93,7,5,7,12345,false,true),EnvironmentProjection.liftWord request.timestamp) := by
  decide +kernel

theorem transient_effect_not_erased (bytes : Roadmap.Bytes) :
    readT (rawSuccess bytes) = some 7 ∧ readT (success bytes) = some 0 ∧
    readT (rawSuccess bytes) ≠ readT (success bytes) := by
  refine ⟨rfl,rfl,?_⟩
  change some (7 : Int) ≠ some 0
  decide +kernel

/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.request_clock_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms request_clock_override
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.source_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_actual
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.source_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_timeout
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.target_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_projection
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.target_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_actual
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.setup_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms setup_reached
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.source_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_vector
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.return_bytes_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms return_bytes_transport
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.paired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paired
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.stale_clock_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stale_clock_actual
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.wrong_global_bytes' does not depend on any axioms -/
#guard_msgs in
#print axioms wrong_global_bytes
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.wrong_target_clock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_target_clock
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.timeout_not_end' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms timeout_not_end
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.payload_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms payload_clients
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.timeout_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms timeout_observations
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.source_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_raw
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.raw_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_vector
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.target_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_raw
/-- info: 'Solidity.Lowering.V08.SourceClockTransactions.transient_effect_not_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transient_effect_not_erased
end Solidity.Lowering.V08.SourceClockTransactions
