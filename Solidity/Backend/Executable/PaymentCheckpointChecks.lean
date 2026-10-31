import Solidity.Backend.Executable.PaymentCheckpoint

/-! Inhabited actual world creation/receive controls, independent of bytecode.
The supplied constructor is empty and the receive executes literal revert bytes.
No declaration lowering, stipend metering or nonce/address theorem is inferred. -/
namespace Solidity.Backend.Executable.PaymentCheckpointChecks
open ContractWorld

def emptyContract : Contract := {vars := []}
def contracts (_ : Unit) : Contract := emptyContract

def sender : Address := ⟨⟨10, by decide +kernel⟩, by decide +kernel⟩
def fresh : Address := ⟨⟨20, by decide +kernel⟩, by decide +kernel⟩
def other : Address := ⟨⟨30, by decide +kernel⟩, by decide +kernel⟩
def initial : World contracts := World.empty contracts (fun _ => PrimTy.dflt .uint)
def reference : Handle () := ⟨fresh⟩
def otherReference : Handle () := ⟨other⟩
def created : World contracts :=
  match initial.create () fresh .nil {sender} with
  | .ok (world, _) => world
  | .error _ => initial

theorem actual_create : initial.create () fresh .nil {sender} = .ok (created, reference) := by rfl

def secondWorld : World contracts :=
  match created.create () other .nil {sender} with
  | .ok (world, _) => world
  | .error _ => created

theorem second_create : created.create () other .nil {sender} = .ok (secondWorld, otherReference) := by rfl

def receive : Entry emptyContract Unit :=
  Entry.unit (.cons (.revertData [.bytes [0xde, 0xad]]) .nil) true

theorem actual_receive : created.receiveRun reference receive sender (PrimTy.dflt .uint) =
    .error (.revertWith [0xde, 0xad]) := by rfl

theorem actual_admission : (created.isLibrary () || (created.storage? reference).isNone) = false := by rfl

/-- Actual new-then-send: failed receive keeps the newly created account. -/
theorem caught_after_creation :
    atomic initial (initial.createSend () fresh .nil receive sender) = (created, .ok false) ∧
    ∃ st : Storage emptyContract, created.accounts reference.address = some ⟨(), st⟩ :=
  create_send_caught_prefix initial created () fresh sender .nil receive reference
    (.revertWith [0xde, 0xad]) actual_create actual_admission actual_receive rfl

/-- The pre-send prefix changed the installed-account observation. -/
example : initial.accounts fresh = none ∧ (created.accounts fresh).isSome = true := by
  exact ⟨rfl, rfl⟩

/-- Two actual creates give distinct references. -/
example : reference ≠ otherReference :=
  creation_handles_distinct actual_create second_create (by decide +kernel)

/-- The second actual creation also preserves the first installed instance. -/
example : (secondWorld.accounts fresh).isSome = true := by rfl

/-- An uncaught transfer failure rolls back the successful create prefix and
retains the exact recipient bytes rather than a caught send=false. -/
theorem transfer_rolls_back_prefix :
    atomic initial (initial.create () fresh .nil {sender} >>= fun pair =>
      pair.1.stipend .transfer pair.2 receive sender (PrimTy.dflt .uint)) =
      (initial, .error (.revertWith [0xde, 0xad])) :=
  prefix_atomic_failure initial created _ reference
    (fun world ref => world.stipend .transfer ref receive sender (PrimTy.dflt .uint))
    (.revertWith [0xde, 0xad]) actual_create
    (World.stipend_transfer_failure created reference receive sender _ _ actual_admission actual_receive)

/-- Mathematical divergence and model exhaustion cannot turn into send=false. -/
example : sendResult created (.error .diverge) = .error .diverge ∧
    sendResult created (.error .exhausted) = .error .exhausted := ⟨rfl, rfl⟩

/-- Exact nonempty revert bytes are separated from an empty failure. -/
example : THalt.data (.revertWith [0xde, 0xad]) ≠ THalt.data .revert := by decide +kernel

/-- A colliding create fails before attempting the recipient payment. -/
example : created.createSend () fresh .nil receive sender = .error .revert :=
  create_send_creation_failure created () fresh sender .nil receive .revert (by rfl)

end Solidity.Backend.Executable.PaymentCheckpointChecks
