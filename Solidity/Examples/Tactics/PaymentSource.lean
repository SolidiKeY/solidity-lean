import Solidity.Frontend.PaymentImport

/-! # Original payment source compositions, executed in the typed world
These are the original pinned source declarations. Runtime gas is independent
bytecode evidence. Every receive below is the imported declaration's body. -/
namespace Solidity.Examples.Tactics.PaymentSource
open Solidity.ContractWorld

solc_payment_source "../../../tests/payment-source/Send.ast.json" hash 0x7b794eeca2e6495e as Send
solc_payment_source "../../../tests/payment-source/Transfer.ast.json" hash 0x02b50c62d6e3412d as Transfer

private def alice : Address := ⟨⟨100, by decide +kernel⟩, by decide +kernel⟩
private def owner : Address := ⟨⟨200, by decide +kernel⟩, by decide +kernel⟩
private def child : Address := ⟨⟨300, by decide +kernel⟩, by decide +kernel⟩
private def other : Address := ⟨⟨400, by decide +kernel⟩, by decide +kernel⟩
private def funding (a : Address) : Word := if a = alice then (⟨1000, by decide +kernel⟩ : Word) else (⟨0, by decide +kernel⟩ : Word)

private structure SendSnapshot where
  sender : Int
  owner : Int
  child : Int
  installed : Bool
  result : Bool
  deriving DecidableEq

private def sendSnapshot : Option SendSnapshot := (do
  let (created, (self, _)) ← Send.deploy (World.empty Send.contracts funding) owner child
    {sender := alice, mode := .ordinary ((⟨20, by decide +kernel⟩ : Word))}
  let (next, result) ← Send.send created self {sender := alice} child
  pure (next, SendSnapshot.mk (next.balance alice).1 (next.balance owner).1
    (next.balance child).1 (next.accounts child).isSome result)).toOption.map Prod.snd

/-- Original constructor20wei; new Receiver; its actual receive; s()true. -/
theorem original_send : sendSnapshot = some ⟨980, 20, 0, true, true⟩ := by decide +kernel

private def initialized : TRes (World Transfer.contracts ×
    (Handle Transfer.Code.owner × Option (Handle Transfer.Code.recipient))) :=
  Transfer.deploy (World.empty Transfer.contracts funding) owner child {sender := alice}

private structure TransferSnapshot where
  beforeBalance : Int
  afterBalance : Int
  fundedBytes : List UInt8
  unfundedBytes : List UInt8
  installed : Bool
  deriving DecidableEq

private def initWorld : World Transfer.contracts :=
  match initialized with | .ok (w, _) => w | .error _ => World.empty Transfer.contracts funding
private def selfRef : Handle Transfer.Code.owner := ⟨owner⟩
private def childRef : Handle Transfer.Code.recipient := ⟨child⟩

/-- The actual deployment supplies exactly these references. -/
private theorem initialize_run : initialized = .ok (initWorld, (selfRef, some childRef)) := by rfl

private def fundingRun : TRes (World Transfer.contracts × Unit) :=
  initWorld.call selfRef Transfer.ownerReceiveEntry
  {sender := alice, mode := .ordinary ((⟨10, by decide +kernel⟩ : Word))}
private def fundedWorld : World Transfer.contracts :=
  match fundingRun with | .ok (w, _) => w | .error _ => initWorld
private theorem funding_empty : fundingRun = initWorld.call selfRef (Entry.unit .nil true)
    {sender := alice, mode := .ordinary ((⟨10, by decide +kernel⟩ : Word))} := by
  exact World.call_unit_noop initWorld selfRef Transfer.ownerReceiveBody true _ rfl Transfer.owner_receive_run
private theorem funding_success : fundingRun.toOption.isSome = true := by decide +kernel

private def transferSnapshot : Option TransferSnapshot := (do
  let (same, before) ← fundedWorld.call selfRef Transfer.getterEntry {sender := alice}
  let (afterF, f) := atomic same (Transfer.transfer same selfRef childRef {sender := alice} ((⟨1, by decide +kernel⟩ : Word)))
  let (afterH, h) := atomic afterF (Transfer.transfer afterF selfRef childRef {sender := alice} ((⟨100000000000000000000, by decide +kernel⟩ : Word)))
  let (final, after) ← afterH.call selfRef Transfer.getterEntry {sender := alice}
  let .error fe := f | .error .exhausted
  let .error he := h | .error .exhausted
  pure (final, TransferSnapshot.mk before.1 after.1 fe.data he.data
    ((final.accounts child).isSome && (final.accounts owner).isSome))).toOption.map Prod.snd

/-- The actual source getter reads the funded world. -/
private theorem getter_run : ((fundedWorld.call selfRef Transfer.getterEntry {sender := alice}).map
    (fun (_, value) => value.1)).toOption = some 10 := by decide +kernel

/-- Original receive10wei; g()10; actual nested Error(no_receive); h()empty
failure; both transactions leave g()10 and both code identities installed. -/
theorem original_transfer : transferSnapshot = some ⟨10, 10,
    Semantics.encodeError ("no_receive".toUTF8.data.toList), [], true⟩ := by decide +kernel

/-- Recipient reason bytes are not erased or replaced by an expected value. -/
theorem wrong_bytes : (transferSnapshot.map (·.fundedBytes)) ≠ some [] := by
  rw [original_transfer]
  decide +kernel

/-- The stored initializer address is checked against the actual handle. -/
theorem wrong_handle : (do
    let (w, (self, _)) ← initialized
    Transfer.transfer w self ⟨other⟩ {sender := alice} ((⟨1, by decide +kernel⟩ : Word))).toOption.isNone = true := by decide +kernel

/-- A forged recipient kind cannot dispatch the owner's receive as A's code. -/
theorem wrong_kind : (do
    let (w, _) ← initialized
    w.stipend .send (⟨owner⟩ : Handle Transfer.Code.recipient) Transfer.receiveEntry alice ((⟨0, by decide +kernel⟩ : Word))).toOption.isNone = true := by decide +kernel

#print axioms initialize_run
#print axioms funding_success
#print axioms getter_run
#print axioms wrong_bytes
#print axioms original_send
#print axioms original_transfer
#print axioms wrong_handle
#print axioms wrong_kind
end Solidity.Examples.Tactics.PaymentSource
