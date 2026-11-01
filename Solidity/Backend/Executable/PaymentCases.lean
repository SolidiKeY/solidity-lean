import Solidity.Backend.Executable.PaymentCheckpointChecks
import Solidity.Stipend.Rule

/-! Actual intrinsic send/transfer versus actual installed receiver frames.
Success settlement and failure observations are independent of pinned EVM gas. -/
namespace Solidity.Backend.Executable.PaymentCases
open ContractWorld Semantics
open PaymentCheckpointChecks (contracts sender fresh other reference)
abbrev C : Contract := contracts ()
abbrev Γ : Ctx := [.val .bool, .val .uint]
def one : ContractWorld.Word := ⟨1, by decide⟩
def four : ContractWorld.Word := ⟨4, by decide⟩
def w : World contracts where
  accounts := fun a => if a = sender ∨ a = fresh then some ⟨(),Storage.init C⟩ else none
  funds := fun a => if a = sender then ⟨3, by decide⟩ else ⟨0, by decide⟩
def ctx (reject : Bool) : Context := {sender, ext :=
  [(sendKey fresh.1 one, if reject then .other [0xde,0xad] else .ok [])]}
private def valueOr {α : Type} (r : TRes α) (fallback : α) : α :=
  match r with | .ok x => x | .error _ => fallback
private theorem recover {α : Type} (r : TRes α) (fallback : α)
    (h : r.toOption.isSome = true) : r = .ok (valueOr r fallback) := by
  cases r with | ok x => rfl | error e => cases h
private def halt {α : Type} : TRes α → Option THalt
  | .ok _ => none | .error e => some e
private theorem failed {α : Type} (r : TRes α) (e : THalt)
    (h : halt r = some e) : r = .error e := by
  cases r with | ok x => cases h | error e' => cases Option.some.inj h; rfl

def entered (reject : Bool) : State C [] :=
  valueOr (w.enter sender (ctx reject) (Storage.init C) true) (State.init C)
theorem actual_entry (reject : Bool) :
    w.enter sender (ctx reject) (Storage.init C) true = .ok (entered reject) := by
  apply recover
  cases reject <;> decide +kernel

def caller (reject : Bool) : State C Γ :=
  ((entered reject).push (t := .val .uint) ⟨99,by decide⟩).push (t := .val .bool) false
def recipientValue : Val C Γ .uint := .simple (.lit fresh.1.1 fresh.1.2)
def amountValue (amount : ContractWorld.Word) : Val C Γ .uint := .simple (.lit amount.1 amount.2)
def localSend (reject : Bool) (amount : ContractWorld.Word) : TRes (Out C (caller reject).H Γ) :=
  TRun.send .here recipientValue (amountValue amount) (caller reject)
def localTransfer (reject : Bool) (amount : ContractWorld.Word) : TRes (Out C (caller reject).H Γ) :=
  TRun.transfer recipientValue (amountValue amount) (caller reject)
def sent (reject : Bool) (amount : ContractWorld.Word) : Out C (caller reject).H Γ :=
  sendT (caller reject) .here fresh.1 amount
theorem actual_send (reject : Bool) (amount : ContractWorld.Word) :
    localSend reject amount = .ok (sent reject amount) := rfl

def receive (reject : Bool) : Entry C Unit :=
  Entry.unit (if reject then .cons (.revertData [.bytes [0xde,0xad]]) .nil else .nil) true
def worldPay (kind : StipendPayment) (reject : Bool) (amount : ContractWorld.Word) : TRes (World contracts × Bool) :=
  w.stipend kind reference (receive reject) sender amount

def paid : World contracts × Bool := valueOr (worldPay .send false one) (w,false)
theorem world_paid : worldPay .send false one = .ok paid :=
  recover _ _ (by decide +kernel)
def settled : World contracts := valueOr (w.finish sender (sent false one).st) w
theorem local_settles : w.finish sender (sent false one).st = .ok settled :=
  recover _ _ (by decide +kernel)

/-- Actual bool, protected caller word, debit, signed ledger and recipient
credit at a nonzero paid boundary. -/
theorem paid_observations :
    TEnv.get .here (sent false one).st.env = true ∧
    (TEnv.get (.there .here) (sent false one).st.env).val = 99 ∧
    (sent false one).st.selfBalance.val = 2 ∧
    (sent false one).st.net = [(fresh.1,-1)] ∧ paid.2 = true ∧
    ((paid.1.funds sender).val,(paid.1.funds fresh).val,(paid.1.funds other).val) = (2,1,0) := by decide +kernel

/-- Explicit rejected reply checked against real receiver execution. -/
theorem rejected_send :
    localSend true one = .ok (sent true one) ∧
    TEnv.get .here (sent true one).st.env = false ∧
    (sent true one).st.net = [] ∧ (sent true one).st.selfBalance.val = 3 ∧
    worldPay .send true one = .ok (w,false) := by
  refine ⟨actual_send _ _, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rfl

/-- Funding refusal precedes the receiver's nonempty error data. -/
theorem unfunded_receive : w.receiveRun reference (receive true) sender four = .error .revert :=
  failed _ _ (by decide +kernel)
theorem funded_receive : w.receiveRun reference (receive true) sender one =
    .error (.revertWith [0xde,0xad]) := failed _ _ (by decide +kernel)
theorem unfunded_send : TEnv.get .here (sent false four).st.env = false ∧
    (sent false four).st.net = [] ∧ worldPay .send true four = .ok (w,false) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  unfold worldPay World.stipend
  rw [show (w.isLibrary () || (w.storage? reference).isNone) = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte, unfunded_receive, sendResult, catchable]

theorem unfunded_transfer : localTransfer false four = .error .revert ∧
    worldPay .transfer true four = .error .revert := by
  refine ⟨failed _ _ (by decide +kernel), ?_⟩
  exact World.stipend_transfer_failure w reference (receive true) sender four .revert rfl unfunded_receive

/-- Exact failure-byte disagreement remains visible rather than assumed away. -/
theorem transfer_failure_boundary : localTransfer true one = .error .revert ∧
    worldPay .transfer true one = .error (.revertWith [0xde,0xad]) := by
  exact ⟨failed _ _ (by decide +kernel),
    World.stipend_transfer_failure w reference (receive true) sender one _ rfl funded_receive⟩

theorem cost_cases : Stipend.progCost (receive false).body = some 0 ∧
    Stipend.progCost (receive true).body = some 2 ∧
    (Stipend.rule C).fits ⟨(receive false).body⟩ ∧
    (Stipend.rule C).fits ⟨(receive true).body⟩ := by decide +kernel

def sourceWorld : World contracts := { w with
  accounts := fun a => if a = sender then some ⟨(),Storage.init C⟩ else w.accounts a,
  funds := fun a => if a = sender then ⟨2,by decide⟩ else if a = fresh then one else w.funds a }
def receiveWorld : World contracts := { w with
  accounts := fun a => if a = fresh then some ⟨(),Storage.init C⟩ else w.accounts a,
  funds := fun a => if a = fresh then one else if a = sender then ⟨2,by decide⟩ else w.funds a }

def sourceFunds (a : Address) : ContractWorld.Word := if a = fresh then one else w.funds a
def receiveFunds (a : Address) : ContractWorld.Word := if a = sender then ⟨2,by decide⟩ else w.funds a
private theorem source_address : Address.ofWord? fresh.1 = some fresh := by decide +kernel
private theorem source_credit : PrimTy.ofInt? .uint ((w.funds fresh).1 - (-1)) = some one := by decide +kernel
private theorem source_settle : settle w.funds sender [(fresh.1,-1)] = .ok sourceFunds := by
  simp only [settle, settle.go, List.not_mem_nil, false_or,
    show fresh.1 ≠ sender.1 from by decide +kernel, ↓reduceIte, source_address,
    TRes.ofOpt, bind, Except.bind, source_credit]
  rfl
private theorem receive_address : Address.ofWord? sender.1 = some sender := by decide +kernel
private theorem receive_debit : PrimTy.ofInt? .uint ((w.funds sender).1 - 1) = some (⟨2,by decide⟩ : ContractWorld.Word) := by decide +kernel
private theorem receive_settle : settle w.funds fresh [(sender.1,1)] = .ok receiveFunds := by
  simp only [settle, settle.go, List.not_mem_nil, false_or,
    show sender.1 ≠ fresh.1 from by decide +kernel, ↓reduceIte, receive_address,
    TRes.ofOpt, bind, Except.bind, receive_debit]
  rfl

private theorem finish_source_normal (σ : State C Γ)
    (net : σ.net = [(fresh.1,-1)]) (balance : σ.selfBalance = ⟨2,by decide⟩)
    (storage : σ.storage = Storage.init C) : w.finish sender σ = .ok sourceWorld := by
  unfold World.finish
  rw [net, source_settle, balance, storage]
  rfl

def receiverState : State C [] where
  storage := Storage.init C
  H := []
  heap := Heap.empty
  env := ()
  selfBalance := one
  net := [(sender.1,1)]
  tx := ({sender,mode := .ordinary one} : Context).tx w fresh
private theorem receive_enters :
    w.enter fresh {sender,mode := .ordinary one} (Storage.init C) true = .ok receiverState := rfl
private theorem receive_finishes : w.finish fresh receiverState = .ok receiveWorld := by
  unfold World.finish
  rw [show receiverState.net = [(sender.1,1)] from rfl, receive_settle]
  rfl

theorem receive_normal : w.receiveRun reference (receive false) sender one =
    .ok (receiveWorld,()) := by
  unfold World.receiveRun World.call World.callFrame
  rw [show w.isLibrary () = false from rfl]
  simp only [Context.isStatic, Bool.false_and, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  rw [show w.storage? reference = some (Storage.init C) from rfl]
  simp only [TRes.ofOpt, bind, Except.bind, PaymentCheckpointChecks.reference, receive, Entry.unit]
  rw [receive_enters]
  simp only [Bool.false_eq_true, ↓reduceIte, Prog.run, Prog.runR, TRun.nil]
  rw [receive_finishes]
  rfl

theorem paid_normal : paid = (receiveWorld,true) := by
  unfold paid worldPay World.stipend
  rw [show (w.isLibrary () || (w.storage? reference).isNone) = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte, receive_normal, sendResult, valueOr]

theorem settled_normal : settled = sourceWorld := by
  have balance : (sent false one).st.selfBalance = (⟨2,by decide⟩ : ContractWorld.Word) :=
    Subtype.ext paid_observations.2.2.1
  have finish := finish_source_normal (sent false one).st paid_observations.2.2.2.1 balance rfl
  unfold settled
  rw [finish]
  rfl

private theorem world_ext (a b : World contracts)
    (accounts : a.accounts = b.accounts) (funds : a.funds = b.funds)
    (time : a.timestamp = b.timestamp) (roles : a.roles = b.roles) : a = b := by
  cases a; cases b; cases accounts; cases funds; cases time; cases roles; rfl

/-- Full functional world equality after actual intrinsic ledger settlement
and actual receiver execution, including all untouched addresses and code. -/
theorem settlement_agrees : settled = paid.1 := by
  rw [settled_normal, paid_normal]
  apply world_ext
  · funext a
    change (if a = sender then some ⟨(),Storage.init C⟩ else w.accounts a) =
      (if a = fresh then some ⟨(),Storage.init C⟩ else w.accounts a)
    by_cases hs : a = sender <;> by_cases hf : a = fresh <;>
      simp only [w, hs, hf, or_self, or_true, true_or, ↓reduceIte, ite_self]
  · funext a
    change (if a = sender then (⟨2, by decide⟩ : ContractWorld.Word)
      else if a = fresh then ⟨1, by decide⟩ else w.funds a) =
      (if a = fresh then ⟨1, by decide⟩ else if a = sender then ⟨2, by decide⟩ else w.funds a)
    by_cases hs : a = sender
    · subst a
      simp only [show sender ≠ fresh from by decide +kernel, ↓reduceIte]
    · by_cases hf : a = fresh <;> simp only [hs, hf, show fresh ≠ sender from by decide +kernel, ↓reduceIte]
  · rfl
  · rfl

/-- A nontrivial inhabited two-sided client: true, the exact actual world,
are obtained from both independent executions. Source-only local protection
is recorded separately by paid_observations. -/
theorem payment_client : localSend false one = .ok (sent false one) ∧
    w.finish sender (sent false one).st = .ok paid.1 ∧
    worldPay .send false one = .ok paid ∧ paid.2 = true := by
  exact ⟨actual_send _ _, local_settles.trans (congrArg Except.ok settlement_agrees),
    world_paid, paid_observations.2.2.2.2.1⟩

theorem no_equal_transfer_halt : ¬ ∃ e,
    localTransfer true one = .error e ∧ worldPay .transfer true one = .error e := by
  rintro ⟨e, localEq, world⟩
  have le := transfer_failure_boundary.1.symm.trans localEq
  have we := transfer_failure_boundary.2.symm.trans world
  have same : THalt.revert = THalt.revertWith [0xde,0xad] :=
    (Except.error.inj le).trans (Except.error.inj we).symm
  cases same

/-- A real finite allocation is rejected by the published source cost rule,
but unmetered World.stipend executes it. This cannot be a gas theorem. -/
def allocating : Entry C Unit :=
  ⟨[.mem bytesR], .cons (.declMem bytesR (.user "scratch") none rfl rfl) .nil,
    fun _ => .ok (), true⟩
theorem allocation_policy_gap :
    ¬(Stipend.rule C).fits ⟨allocating.body⟩ ∧
    ((w.stipend .send reference allocating sender one).toOption.map Prod.snd) = some true := by
  constructor <;> decide +kernel

/-- The body can be admitted and empty while recipient entry overflows.
The source balance check alone is therefore not a receiver-success proof. -/
def maximum : ContractWorld.Word := ⟨(2 : Int)^256 - 1, by decide +kernel⟩
def overflowWorld : World contracts :=
  { w with funds := fun a => if a = fresh then maximum else w.funds a }
theorem overflow_entry_failure :
    overflowWorld.receiveRun reference (receive false) sender one = .error .revert :=
  failed _ _ (by decide +kernel)
theorem body_success_is_insufficient :
    (caller false).canPay fresh.1 one = true ∧
    (overflowWorld.funds sender).val = (w.funds sender).val ∧
    overflowWorld.stipend .send reference (receive false) sender one = .ok (overflowWorld,false) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  unfold World.stipend
  rw [show (overflowWorld.isLibrary () || (overflowWorld.storage? reference).isNone) = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte, overflow_entry_failure, sendResult, catchable]

def overflowCaller : State C Γ := { caller false with tx :=
  { (caller false).tx with ext := [(sendKey fresh.1 one, .other [])] } }
/-- A concrete failure receipt for the entry overflow matches the false result
for this finite entry failure without changing source semantics or assuming a future simulation. -/
theorem overflow_reply_rejects :
    TEnv.get .here (sendT overflowCaller .here fresh.1 one).st.env = false ∧
    (sendT overflowCaller .here fresh.1 one).st.net = [] ∧
    (sendT overflowCaller .here fresh.1 one).st.selfBalance.val = 3 := by decide +kernel

/-- The finite overflow receipt is installed in a caller actually entered
against the overflowing world, before its two protected locals are pushed. -/
def overflowContext : Context := {sender, ext := [(sendKey fresh.1 one, .other [])]}
def overflowBase : State C [] := {entered false with tx := overflowContext.tx overflowWorld sender}
theorem overflow_enters : overflowWorld.enter sender overflowContext (Storage.init C) true =
    .ok overflowBase := rfl
theorem overflow_frame :
    (overflowBase.push (t := .val .uint) ⟨99,by decide⟩).push (t := .val .bool) false =
      overflowCaller := rfl

/-- Actual failed-send settlement preserves the entire overflowing world;
the finite receipt is checked here, not supplied by a general compiler. -/
theorem overflow_settles :
    overflowWorld.finish sender (sendT overflowCaller .here fresh.1 one).st = .ok overflowWorld := by
  have net := overflow_reply_rejects.2.1
  unfold World.finish
  rw [net]
  change Except.ok _ = Except.ok overflowWorld
  apply congrArg Except.ok
  apply world_ext
  · funext a
    by_cases h : a = sender
    · subst a; rfl
    · simp only [h, ↓reduceIte]
  · funext a
    by_cases h : a = sender
    · subst a; rfl
    · simp only [h, ↓reduceIte]
  · rfl
  · rfl

def transferred : Out C (caller false).H Γ :=
  ⟨(caller false).pay fresh.1 one.1, List.prefix_refl _⟩
theorem successful_transfer : localTransfer false one = .ok transferred ∧
    w.finish sender transferred.st = .ok paid.1 ∧
    worldPay .transfer false one = .ok paid ∧
    TEnv.get .here transferred.st.env = false ∧
    (TEnv.get (.there .here) transferred.st.env).val = 99 := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · rfl
  · have h := finish_source_normal transferred.st (by decide +kernel) (by decide +kernel) rfl
    rw [h, paid_normal]
    exact congrArg Except.ok (settled_normal.symm.trans settlement_agrees |>.trans (congrArg Prod.fst paid_normal))
  · unfold worldPay World.stipend
    rw [show (w.isLibrary () || (w.storage? reference).isNone) = false from rfl]
    simp only [Bool.false_eq_true, ↓reduceIte, receive_normal, bind, Except.bind]
    rw [paid_normal]
    rfl

/-- info: 'Solidity.Backend.Executable.PaymentCases.payment_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payment_client
/-- info: 'Solidity.Backend.Executable.PaymentCases.settlement_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms settlement_agrees
/-- info: 'Solidity.Backend.Executable.PaymentCases.rejected_send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_send
/-- info: 'Solidity.Backend.Executable.PaymentCases.unfunded_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unfunded_transfer
/-- info: 'Solidity.Backend.Executable.PaymentCases.transfer_failure_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transfer_failure_boundary
/-- info: 'Solidity.Backend.Executable.PaymentCases.no_equal_transfer_halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_equal_transfer_halt
/-- info: 'Solidity.Backend.Executable.PaymentCases.cost_cases' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms cost_cases
/-- info: 'Solidity.Backend.Executable.PaymentCases.allocation_policy_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocation_policy_gap
/-- info: 'Solidity.Backend.Executable.PaymentCases.body_success_is_insufficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_success_is_insufficient
/-- info: 'Solidity.Backend.Executable.PaymentCases.overflow_reply_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms overflow_reply_rejects
/-- info: 'Solidity.Backend.Executable.PaymentCases.overflow_enters' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms overflow_enters
/-- info: 'Solidity.Backend.Executable.PaymentCases.overflow_frame' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms overflow_frame
/-- info: 'Solidity.Backend.Executable.PaymentCases.overflow_settles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms overflow_settles
/-- info: 'Solidity.Backend.Executable.PaymentCases.successful_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms successful_transfer
end Solidity.Backend.Executable.PaymentCases
