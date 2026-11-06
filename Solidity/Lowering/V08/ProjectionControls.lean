import Solidity.Lowering.V08.EnvironmentProjection
import Solidity.Lowering.V08.Controls
import Solidity.Lowering.V08.AbiObservations
import Solidity.Roadmap.Controls

/-!
# Populated independent source journals and typed target frame controls

The two runs use Source.World's journal operations and ContractWorld's actual
paid calls respectively. They witness matching observations; they do not supply
missing RExpr/RStmt evaluation, a general storage layout relation or compiler
preservation. Source transfer success is checked rather than hidden by getD.
-/
namespace Solidity.Lowering.V08.ProjectionControls
open Solidity
open ContractWorld
open EnvironmentProjection

def senderS : Roadmap.Address := ⟨1, by decide +kernel⟩
def selfS : Roadmap.Address := ⟨2, by decide +kernel⟩
def layout : Source.Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
def slotTypes : Roadmap.Address → Source.SPath → Source.STy := fun _ _ => .int Source.IntTy.u256
abbrev SState := Source.ExecState layout slotTypes slotTypes

def saved : Source.SPath := ⟨⟨some "C", "saved"⟩, []⟩
def scratch : Source.SPath := ⟨⟨some "C", "scratch"⟩, []⟩
def initialS : SState :=
  { world := ⟨fun address =>
      { balance := if address = senderS then ⟨100, by decide +kernel⟩ else ⟨0, by decide +kernel⟩,
        nonce := 0, code := if address = selfS then some 0 else if address = senderS then some 1 else none, storage := Source.Storage.empty }⟩,
    transient := Source.Transient.empty, journal := [] }

def writes (persistent temporary : Int) (hp : 0 ≤ persistent ∧ persistent ≤ Source.IntTy.u256.hi)
    (ht : 0 ≤ temporary ∧ temporary ≤ Source.IntTy.u256.hi) : List (Source.Op layout slotTypes slotTypes) :=
  [.account selfS (fun account => { account with storage := account.storage.write saved (.int persistent hp) }),
   .transient selfS (fun store => store.write scratch (.int temporary ht))]

def paidS : SState := ((initialS.transfer senderS selfS ⟨7, by decide +kernel⟩).getD initialS).run
  (writes 3 9 (by decide +kernel) (by decide +kernel))
def dirtyS : SState := ((paidS.transfer senderS selfS ⟨2, by decide +kernel⟩).getD paidS).run
  (writes 5 17 (by decide +kernel) (by decide +kernel))
def caughtS : SState :=
  (paidS.enter selfS senderS ⟨2, by decide +kernel⟩ [0x22] false).rollback dirtyS
def rolledS : SState :=
  (initialS.enter selfS senderS ⟨7, by decide +kernel⟩ [0x11] false).rollback caughtS

def readInt (value : Option (Source.Val layout (.int Source.IntTy.u256))) : Option Int :=
  match value with | some (.int number _) => some number | _ => none

def observeS (state : SState) : Option (Int × Int × Int × Int) := do
  let persistent ← readInt ((state.world.accounts selfS).storage.read saved)
  let temporary ← readInt ((state.transient.cells selfS).read scratch)
  pure ((state.world.accounts senderS).balance.val, (state.world.accounts selfS).balance.val,
    persistent, temporary)

/-- Both real source transfers succeed; getD does not witness a failed payment. -/
theorem source_payments :
    (initialS.transfer senderS selfS ⟨7, by decide +kernel⟩).isSome = true ∧
    (paidS.transfer senderS selfS ⟨2, by decide +kernel⟩).isSome = true := by decide +kernel

/-- The inner dirty frame is genuinely populated in all four observations. -/
theorem source_dirty : observeS dirtyS = some (91, 9, 5, 17) := by decide +kernel

/-- Inner rollback retains the paid outer account, persistent and transient work. -/
theorem source_caught : observeS caughtS = some (93, 7, 3, 9) := by decide +kernel

/-- A later outer rollback restores its own entry, including both storage regions. -/
theorem source_rolled : observeS rolledS = some (100, 0, 0, 0) := by decide +kernel

/-- Source endTx retains persistent/payment observations and clears transient cells. -/
theorem source_reset : observeS caughtS.endTx = some (93, 7, 3, 0) := by decide +kernel

def innerEntry : Entry Controls.Cell Unit :=
  { locals := [], body := sol[Controls.Cell]{ saved = 5; scratch = 17; },
    result := fun _ => .ok (), payable := true }
def innerContext : Context := { sender := Controls.sender, mode := .ordinary ⟨2, by decide +kernel⟩ }
def innerHalt : THalt := .revertWith (Semantics.encodeError [0xee, 0x01])

def nestedFrame (world : World Controls.catalog) : TRes (World Controls.catalog × TRes Unit) := do
  let (paid, _) ← world.call (⟨Controls.self⟩ : Handle ()) Controls.entry Controls.paidCtx
  pure (atomic paid (do
    let _ ← paid.call (⟨Controls.self⟩ : Handle ()) innerEntry innerContext
    (.error innerHalt : TRes (World Controls.catalog × Unit))))

def nested : TRes (World Controls.catalog × TRes Unit) := Controls.setup >>= nestedFrame

def nestedView : TRes (Option (Int × Int × Int × Int) × Option (List UInt8)) := do
  let (world, status) ← nested
  pure (Controls.observe world, (match status with | .error (.revertWith bytes) => some bytes | _ => none))

def dirtyTargetView : TRes (Option (Int × Int × Int × Int)) := do
  let world ← Controls.setup
  let (paid, _) ← world.call (⟨Controls.self⟩ : Handle ()) Controls.entry Controls.paidCtx
  let (dirty, _) ← paid.call (⟨Controls.self⟩ : Handle ()) innerEntry innerContext
  pure (Controls.observe dirty)

/-- Both target paid calls succeed before the explicit descendant failure. -/
theorem target_dirty : dirtyTargetView.toOption = some (some (91, 9, 5, 17)) := by decide +kernel

/-- Actual paid target calls restore the same inner snapshot with exact reason bytes. -/
theorem target_caught : nestedView.toOption = some (some (93, 7, 3, 9), some (Semantics.encodeError [0xee, 0x01])) := by decide +kernel

/-- Independent source journal and actual target call observations agree here. -/
theorem inner_observations : nestedView.toOption.map Prod.fst = some (observeS caughtS) := by
  rw [target_caught, source_caught]
  rfl

/-- The dirty inner snapshot is wrong for both sides' caught outcome. -/
theorem wrong_inner_frame : nestedView.toOption ≠ some (some (91, 9, 5, 17), some (Semantics.encodeError [0xee, 0x01])) := by
  rw [target_caught]
  decide +kernel

def outer : TRes (Option (Int × Int × Int × Int) × Option (List UInt8)) := do
  let before ← Controls.setup
  let (world, status) := atomic before (do
    let _ ← nestedFrame before
    (.error (.revertWith [0xfa, 0x02]) : TRes (World Controls.catalog × Unit)))
  pure (Controls.observe world, (match status with | .error (.revertWith bytes) => some bytes | _ => none))

/-- A populated nested target run followed by outer failure restores the outer frame. -/
theorem target_rolled : outer.toOption = some (observeS rolledS, some [0xfa, 0x02]) := by decide +kernel

def resetTargetView : TRes (Option (Int × Int × Int × Int)) := do
  let (next, _) ← nested
  pure (Controls.observe next.resetTransient)

/-- Both published transaction boundaries retain outer work and clear transient cells. -/
theorem reset_observations : resetTargetView.toOption = some (observeS caughtS.endTx) := by decide +kernel

/-- Retaining the stale transient value is wrong on the actual target boundary too. -/
theorem target_stale_transient : resetTargetView.toOption ≠ some (some (93, 7, 3, 9)) := by
  rw [reset_observations, source_reset]
  decide +kernel

/-- Nonempty reason bytes survive both independent published byte encoders. -/
theorem exact_inner_reason : Source.errorData [0xee, 0x01] = Semantics.encodeError [0xee, 0x01] :=
  errorData_transport_total _

/-- Changing a reason byte cannot match the actual inner halt. -/
theorem wrong_reason : innerHalt ≠ .revertWith (Semantics.encodeError [0xee, 0x02]) := by decide +kernel

/-- After a true transaction boundary, the old transient value is distinguishable. -/
theorem stale_transient : observeS caughtS.endTx ≠ some (93, 7, 3, 9) := by
  rw [source_reset]
  decide +kernel

def request : Roadmap.Request :=
  { sender := senderS, target := selfS, value := ⟨7, by decide +kernel⟩,
    timestamp := ⟨12345, by decide +kernel⟩, input := [0x11] }
def projected : State Controls.Cell [] :=
  stateEnvironment paidS.world Controls.initial request [] (State.init Controls.Cell)
def environmentView : Int × Int × Int × Int × Int :=
  ((projected.envVal .msgSender).1, (projected.envVal .msgValue).1,
    (projected.envVal .timestamp).1, (projected.envVal .selfAddress).1,
    (projected.envVal .selfBalance).1)

/-- The request and independently populated source balance fix all five observations. -/
theorem environment_values : environmentView = (1, 7, 12345, 2, 7) := by decide +kernel

/-- A stale timestamp/value/receiver tuple does not describe the request projection. -/
theorem wrong_environment : environmentView ≠ (1, 0, 12344, 1, 0) := by
  rw [environment_values]
  decide +kernel

/-- Boundary values roundtrip without exclusion; no admission predicate is proved. -/
theorem boundary_roundtrips :
    lowerWord (liftWord ⟨2 ^ 256 - 1, by decide +kernel⟩) = ⟨2 ^ 256 - 1, by decide +kernel⟩ ∧
    lowerAddress (liftAddress ⟨2 ^ 160 - 1, by decide +kernel⟩) = ⟨2 ^ 160 - 1, by decide +kernel⟩ ∧
    lowerAddress (liftAddress ⟨0, by decide +kernel⟩) = ⟨0, by decide +kernel⟩ :=
  ⟨lower_lift_word _, lower_lift_address _, lower_lift_address _⟩

def externalS : Roadmap.Address := ⟨9, by decide +kernel⟩
/-- Existing G07 toyFixed is a fixture ledger, NOT the canonical G03 ledger. -/
def session : Roadmap.SessionEnv :=
  { deployer := senderS, deployNonce := ⟨0, by decide +kernel⟩, deployValue := ⟨0, by decide +kernel⟩,
    deployArgs := [], balance := fun _ => ⟨41, by decide +kernel⟩,
    hasCode := fun _ _ => false, requests := fun _ _ => none,
    callee := fun _ => .answer (.success []) }

/-- An installed instance chooses its source balance7 instead of fixture-ledger41. -/
theorem installed_balance_choice :
    (sessionFunds paidS.world Roadmap.Controls.toyFixed session [] (liftAddress selfS)).1 = 7 := by decide +kernel

/-- A code-less address chooses ledger41 instead of the source default account0. -/
theorem external_balance_choice :
    (sessionFunds paidS.world Roadmap.Controls.toyFixed session [] (liftAddress externalS)).1 = 41 := by decide +kernel

/-- Source instance-account fields cannot replace the external ledger projection. -/
theorem wrong_external_balance :
    (sessionFunds paidS.world Roadmap.Controls.toyFixed session [] (liftAddress externalS)).1 ≠
      (fundsOf paidS.world (liftAddress externalS)).1 := by decide +kernel

#print axioms installed_balance_choice
#print axioms external_balance_choice
#print axioms wrong_external_balance
#print axioms source_payments
#print axioms source_dirty
#print axioms source_caught
#print axioms source_rolled
#print axioms source_reset
#print axioms target_dirty
#print axioms target_caught
#print axioms inner_observations
#print axioms wrong_inner_frame
#print axioms target_rolled
#print axioms reset_observations
#print axioms target_stale_transient
#print axioms exact_inner_reason
#print axioms wrong_reason
#print axioms stale_transient
#print axioms environment_values
#print axioms wrong_environment
#print axioms boundary_roundtrips
end Solidity.Lowering.V08.ProjectionControls
