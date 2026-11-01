import Solidity.Backend.Executable.PaymentReceipt
import Solidity.Backend.Executable.StipendCall

/-! Physical send-result assignment into actual intrinsic bool/uint locals.
The frame is an explicit encoding of existing typed local values, not a general
runtime-frame producer. Numeric CALL is unsupported; this result suffix and
actual receipt/world Bool-or-refusal transport do not assume CALL simulation. -/
namespace Solidity.Backend.Executable.SendResult
open Semantics ContractWorld Scalar
variable {C : Contract}
abbrev Γ : Ctx := [.val .bool,.val .uint]

/-- Constructed encoding of the actual existing intrinsic local values. General
source/runtime frame production, references and arbitrary contexts stay OPEN. -/
def frame (σ : State C Γ) (spill : Stack) : Stack :=
  encodeValue .bool (TEnv.get .here σ.env) :: encodeValue .uint (TEnv.get (.there .here) σ.env) :: spill

def store : Program := [.op (.SWAP ⟨0,by decide⟩),.op .POP]

def code (recipient : Address) (amount : PrimTy.uint.Denote) : Program :=
  ValueCall.code (StipendCall.requested amount) recipient amount ++ store

theorem frame_length (σ : State C Γ) (spill : Stack) : (frame σ spill).length = spill.length+2 := by
  simp only [frame, List.length_cons]

/-- Real SWAP1 followed by POP replaces the old result cell, preserving the
uint local and every protected spill word; POP alone would discard the result. -/
theorem store_correct (σ : State C Γ) (spill : Stack) (b : Bool) :
    run store (encodeValue .bool b :: frame σ spill) =
      some (frame (σ.setLocal .here b) spill) := rfl

/-- Actual intrinsic send and its receipt update determine the value stored.
No machine success flag or post-state simulation is assumed. -/
theorem source_store (σ : State C Γ) (spill : Stack)
    (addr amount : PrimTy.uint.Denote) (r : ExtResult) :
    run store (encodeValue .bool ((PaymentReceipt.install σ addr amount r).canPay addr amount) :: frame σ spill) =
      some (frame (sendT (PaymentReceipt.install σ addr amount r) .here addr amount).st spill) := rfl

/-- The source statement is actual TRun.send, with its original literal
argument evaluations and typed result index. -/
theorem source_run (σ : State C Γ) (addr amount : PrimTy.uint.Denote) :
    TRun.send .here (.simple (.lit addr.1 addr.2)) (.simple (.lit amount.1 amount.2)) σ =
      .ok (sendT σ .here addr amount) := rfl

/-- Complete two-sided Bool/None transport through the actual physical store.
The numerical balance equality is an explicit checkpoint condition, not a
producer for pending-ledger/world or machine-CALL reconciliation. -/
theorem world_store {K : Type} [DecidableEq K] {contracts : K → Contract}
    (w : World contracts) {k : K} (recipient : Handle k) (entry : Entry (contracts k) Unit)
    (sender : Address) (amount : ContractWorld.Word) (σ : State C Γ) (spill : Stack)
    (aligned : σ.selfBalance.val = (w.funds sender).val) :
    (PaymentReceipt.prepare w recipient entry sender amount).bind (fun r =>
      run store (encodeValue .bool ((PaymentReceipt.install σ recipient.address.1 amount r).canPay recipient.address.1 amount) :: frame σ spill)) =
      ((w.stipend .send recipient entry sender amount).toOption.map Prod.snd).map
        (fun b => frame (σ.setLocal .here b) spill) := by
  have observed := PaymentReceipt.world_observation w recipient entry sender amount σ aligned
  have factor : (PaymentReceipt.prepare w recipient entry sender amount).bind (fun r =>
      run store (encodeValue .bool ((PaymentReceipt.install σ recipient.address.1 amount r).canPay recipient.address.1 amount) :: frame σ spill)) =
      ((PaymentReceipt.prepare w recipient entry sender amount).map (fun r =>
        (PaymentReceipt.install σ recipient.address.1 amount r).canPay recipient.address.1 amount)).map
          (fun b => frame (σ.setLocal .here b) spill) := by
    cases prepared : PaymentReceipt.prepare w recipient entry sender amount with
    | none => rfl
    | some r => exact store_correct σ spill _
  exact factor.trans (congrArg (fun obs : Option Bool => obs.map (fun b => frame (σ.setLocal .here b) spill)) observed)

/-- A genuinely unchanged checkpoint commits to the exact original world.
Storage identity, balance identity and the empty ledger are concrete state
fields; no desired source/machine simulation is among the premises. -/
theorem finish_unchanged {K : Type} {contracts : K → Contract} {k : K} {Δ : Ctx}
    (w : World contracts) (self : Address) (σ : State (contracts k) Δ)
    (stored : w.accounts self = some ⟨k,σ.storage⟩)
    (balance : σ.selfBalance = w.funds self) (empty : σ.net = []) :
    w.finish self σ = .ok w := by
  have accounts : (fun a => if a = self then some ⟨k,σ.storage⟩ else w.accounts a) = w.accounts := by
    funext a
    by_cases same : a = self
    · subst a; simp only [↓reduceIte, stored]
    · simp only [same, ↓reduceIte]
  have funds : (fun a => if a = self then w.funds self else w.funds a) = w.funds := by
    funext a
    by_cases same : a = self
    · subst a; simp only [↓reduceIte]
    · simp only [same, ↓reduceIte]
  unfold World.finish
  rw [empty]
  change Except.ok {w with accounts := (fun a => if a = self then some ⟨k,σ.storage⟩ else w.accounts a), funds := (fun a => if a = self then σ.selfBalance else w.funds a)} = _
  rw [balance, accounts, funds]

theorem store_capacity (σ : State C Γ) (spill : Stack) (b : Bool) :
    stackBound store ((encodeValue .bool b :: frame σ spill).length : Int) = true ↔ spill.length ≤ 1021 := by
  simp only [store, stackBound, heightTrace, stackDelta, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true, safeHeight, decide_eq_true_eq, List.length_cons, frame_length]
  omega

/-- Literal send preparation reuses the actual published CALL operand capacity;
it has a seven-word peak, because the literal requested gas is already known. -/
theorem operands_capacity (σ : State C Γ) (spill : Stack) (recipient : Address)
    (amount : PrimTy.uint.Denote) :
    stackBound (ValueCall.operandCode (StipendCall.requested amount) recipient amount)
      ((frame σ spill).length : Int) = true ↔ spill.length ≤ 1015 := by
  rw [ValueCall.capacity_iff, frame_length]
  constructor
  · intro h; omega
  · intro h; constructor <;> omega

theorem complete_bytes (recipient : Address) (amount : PrimTy.uint.Denote) :
    Backend.encode (code recipient amount) = ValueCall.bytes (StipendCall.requested amount) recipient amount ++ [0x90,0x50] := by
  rw [code, Backend.encode_append]
  rfl

theorem byte_length (recipient : Address) (amount : PrimTy.uint.Denote) :
    (Backend.encode (code recipient amount)).length = 107 := by
  rw [complete_bytes, List.length_append, ValueCall.byte_length]
  rfl

theorem decode_bytes (recipient : Address) (amount : PrimTy.uint.Denote) :
    Backend.decode (Backend.encode (code recipient amount)) = some (code recipient amount) :=
  Backend.decode_encode _

/-- info: 'Solidity.Backend.Executable.SendResult.store_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms store_correct

/-- info: 'Solidity.Backend.Executable.SendResult.source_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_store

/-- info: 'Solidity.Backend.Executable.SendResult.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_run

/-- info: 'Solidity.Backend.Executable.SendResult.world_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms world_store

/-- info: 'Solidity.Backend.Executable.SendResult.store_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms store_capacity

/-- info: 'Solidity.Backend.Executable.SendResult.operands_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms operands_capacity

/-- info: 'Solidity.Backend.Executable.SendResult.complete_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms complete_bytes

/-- info: 'Solidity.Backend.Executable.SendResult.byte_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms byte_length

/-- info: 'Solidity.Backend.Executable.SendResult.decode_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_bytes

/-- info: 'Solidity.Backend.Executable.SendResult.finish_unchanged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finish_unchanged

end Solidity.Backend.Executable.SendResult
