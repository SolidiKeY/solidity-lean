import Solidity.Semantics.ContractWorldCertificates

/-!
# Payment-specific composition of actual typed world frames

This deterministic, unmetered interface is above the legacy single-contract
run. The source bridge supplies the declaration-resolved receive entry. It
admits stipend send/transfer only; full-gas value calls need a separate source
shape and are not represented by this interface. Numerical stipend adequacy
is independent EVM evidence, not a theorem of this unmetered world.
-/
namespace Solidity.ContractWorld
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- The source payment kind. Full-gas calls cannot be passed as a stipend. -/
inductive StipendPayment where
  | send | transfer
  deriving DecidableEq

/-- Check code identity before executing a resolved receive. Admission errors
are not caught as send=false. Payment and body execution happen once, in call. -/
def World.receiveRun (w : World contracts) {k : K} (recipient : Handle k)
    (entry : Entry (contracts k) Unit) (sender : Address) (amount : Word) :
    TRes (World contracts × Unit) :=
  w.call recipient entry { sender, mode := .ordinary amount }

/-- Send catches only completed callee failures. Exhaustion/divergence retain
exactly their original halt. A failed recipient exposes no changed world. -/
def sendResult (w : World contracts) :
    TRes (World contracts × Unit) → TRes (World contracts × Bool)
  | .ok (next, ()) => .ok (next, true)
  | .error e => if catchable e then .ok (w, false) else .error e

/-- A checked stipend payment, with exact nested recipient bytes for transfer.
Only actual installed code of the resolved kind is admitted by this fragment. -/
def World.stipend (w : World contracts) {k : K} (kind : StipendPayment)
    (recipient : Handle k) (entry : Entry (contracts k) Unit)
    (sender : Address) (amount : Word) : TRes (World contracts × Bool) := do
  if w.isLibrary k || (w.storage? recipient).isNone then .error .exhausted else
    match kind with
    | .send => sendResult w (w.receiveRun recipient entry sender amount)
    | .transfer => do
      let (next, ()) ← w.receiveRun recipient entry sender amount
      pure (next, true)

/-- A source local receives the handle returned by actual creation; the next
statement sends to that very handle, including when the amount is zero. -/
def World.createSend (w : World contracts) (k : K) (fresh : Address)
    (ctor : Prog (contracts k) [] []) (receive : Entry (contracts k) Unit)
    (sender : Address) : TRes (World contracts × Bool) := do
  let (created, reference) ← w.create k fresh ctor {sender := sender}
  created.stipend .send reference receive sender (PrimTy.dflt .uint)

/-- A source wrapper's caller entry is paid once, then composed with its
world effects. Static/library contexts remain explicit refusals. -/
def World.paymentFrame {α : Type} (w : World contracts) {k : K} (self : Handle k)
    (ctx : Context) (payable : Bool)
    (body : World contracts → TRes (World contracts × α)) : TRes (World contracts × α) :=
  if w.isLibrary k || ctx.isStatic then .error .revert else
    w.paidRun self ctx payable body

omit [DecidableEq K] in
/-- Real successful receive execution, not a response table, justifies true. -/
theorem sendResult_success (w next : World contracts)
    (run : TRes (World contracts × Unit)) (h : run = .ok (next, ())) :
    sendResult w run = .ok (next, true) := by rw [h]; rfl

omit [DecidableEq K] in
/-- A completed failed receive returns false with the exact pre-receive world. -/
theorem sendResult_failure (w : World contracts) (e : THalt)
    (completed : catchable e = true) :
    sendResult w (.error e) = .ok (w, false) := by
  simp only [sendResult, completed, ↓reduceIte]

omit [DecidableEq K] in
/-- Resource stops cannot be certified as an ordinary send failure. -/
theorem sendResult_uncaught (w : World contracts) (e : THalt)
    (uncaught : catchable e = false) : sendResult w (.error e) = .error e := by
  simp only [sendResult, uncaught, Bool.false_eq_true, ↓reduceIte]

/-- Transfer transports the actual nested halt, retaining every byte. -/
theorem World.stipend_transfer_failure (w : World contracts) {k : K}
    (recipient : Handle k) (entry : Entry (contracts k) Unit)
    (sender : Address) (amount : Word) (e : THalt)
    (admitted : (w.isLibrary k || (w.storage? recipient).isNone) = false)
    (failed : w.receiveRun recipient entry sender amount = .error e) :
    w.stipend .transfer recipient entry sender amount = .error e := by
  simp only [World.stipend, admitted, Bool.false_eq_true, ↓reduceIte, failed,
    bind, Except.bind]

omit [DecidableEq K] in
/-- Send failure retains effects preceding the receive (e.g. new Receiver),
while an uncaught transfer failure restores the original transaction world. -/
theorem payment_atomic_failure {α : Type} (w : World contracts)
    (run : TRes (World contracts × α)) (e : THalt) (failed : run = .error e) :
    atomic w run = (w, .error e) := by rw [failed]; rfl

/-- Every successful receive exposes the actual body, funding and settlement. -/
theorem World.receiveRun_ok {w next : World contracts} {k : K}
    {recipient : Handle k} {entry : Entry (contracts k) Unit}
    {sender : Address} {amount : Word}
    (run : w.receiveRun recipient entry sender amount = .ok (next, ())) :
    ∃ (st : Storage (contracts k)) (σ : State (contracts k) [])
      (o : Out (contracts k) σ.H entry.locals),
      w.storage? recipient = some st ∧
      w.enter recipient.address {sender, mode := .ordinary amount} st entry.payable = .ok σ ∧
      entry.body.run σ = .ok o ∧ w.finish recipient.address o.st = .ok next := by
  unfold World.receiveRun World.call at run
  cases hf : w.callFrame recipient entry {sender, mode := .ordinary amount} with
  | error e => simp only [hf, bind, Except.bind] at run; cases run
  | ok pair =>
    obtain ⟨st, σ, o, stored, entered, ran, finish, eq⟩ := World.callFrame_ok hf
    cases hd : entry.result pair.2 with
    | error e => simp only [hf, hd, bind, Except.bind] at run; cases run
    | ok value =>
      simp only [hf, hd, bind, Except.bind, pure, Except.pure] at run
      have worlds : pair.1 = next := congrArg Prod.fst (Except.ok.inj run)
      exact ⟨st, σ, o, stored, entered, ran, worlds ▸ finish⟩

omit [DecidableEq K] in
/-- Send true is equivalent to actual successful recipient execution. -/
theorem sendResult_true_iff (w next : World contracts) (run : TRes (World contracts × Unit)) :
    sendResult w run = .ok (next, true) ↔ run = .ok (next, ()) := by
  cases run with
  | ok pair =>
    rcases pair with ⟨final, ⟨⟩⟩
    simp only [sendResult, Except.ok.injEq, Prod.mk.injEq, and_true]
  | error e =>
    cases h : catchable e with
    | false =>
      simp only [sendResult, h, Bool.false_eq_true, ↓reduceIte]
      constructor <;> intro impossible <;> cases impossible
    | true =>
      simp only [sendResult, h, ↓reduceIte]
      constructor
      · intro bad
        have impossible : false = true := congrArg Prod.snd (Except.ok.inj bad)
        cases impossible
      · intro impossible
        cases impossible

/-- The source creation/send composition exposes both real world operations. -/
theorem World.createSend_ok {w next : World contracts} {k : K} {fresh : Address}
    {ctor : Prog (contracts k) [] []} {receive : Entry (contracts k) Unit}
    {sender : Address} {result : Bool}
    (run : w.createSend k fresh ctor receive sender = .ok (next, result)) :
    ∃ created reference,
      w.create k fresh ctor {sender := sender} = .ok (created, reference) ∧
      created.stipend .send reference receive sender (PrimTy.dflt .uint) = .ok (next, result) := by
  unfold World.createSend at run
  cases hc : w.create k fresh ctor {sender := sender} with
  | error e => simp only [hc, bind, Except.bind] at run; cases run
  | ok pair =>
    simp only [hc, bind, Except.bind] at run
    exact ⟨pair.1, pair.2, rfl, run⟩

/-- True from a stipend send has an actual funded receive/body/settlement
witness through receiveRun_ok; no default oracle reply supplies this evidence. -/
theorem World.stipend_send_true {w next : World contracts} {k : K}
    {recipient : Handle k} {entry : Entry (contracts k) Unit} {sender : Address} {amount : Word}
    (run : w.stipend .send recipient entry sender amount = .ok (next, true)) :
    w.receiveRun recipient entry sender amount = .ok (next, ()) := by
  unfold World.stipend at run
  split at run
  · cases run
  · exact (sendResult_true_iff w next _).mp run

/-- A proved no-op receive uses the same existing paid empty world frame.
Static admissibility remains syntactic and is not inferred from final equality. -/
theorem World.call_unit_noop (w : World contracts) {k : K} (self : Handle k)
    (P : Prog (contracts k) [] []) (payable : Bool) (ctx : Context)
    (ordinary : ctx.isStatic = false)
    (body : ∀ σ : State (contracts k) [], P.run σ = .ok ⟨σ, List.prefix_refl _⟩) :
    w.call self (Entry.unit P payable) ctx = w.call self (Entry.unit .nil payable) ctx := by
  unfold World.call World.callFrame Entry.unit
  simp only [ordinary, Bool.false_and, Bool.or_false]
  split
  · rfl
  · cases hs : w.storage? self with
    | none => rfl
    | some st =>
      simp only [TRes.ofOpt, bind, Except.bind]
      cases he : w.enter self.address ctx st payable with
      | error e => rfl
      | ok σ =>
        simp only [body σ]
        rfl

/-- Funding refusal precedes execution of the actual receive body. -/
theorem World.receiveRun_unfunded (w : World contracts) {k : K}
    (recipient : Handle k) (entry : Entry (contracts k) Unit) (sender : Address)
    (amount : Word) (st : Storage (contracts k))
    (code : w.isLibrary k = false) (stored : w.storage? recipient = some st)
    (unfunded : (w.funds sender).1 < amount.1) :
    w.receiveRun recipient entry sender amount = .error .revert := by
  simp only [World.receiveRun, World.call, World.callFrame, code, Context.isStatic,
    Bool.false_and, Bool.or_self, Bool.false_eq_true, ↓reduceIte, stored,
    TRes.ofOpt, bind, Except.bind, World.enter, Context.value, unfunded]

#print axioms World.createSend_ok
#print axioms World.stipend_send_true
#print axioms sendResult_true_iff
#print axioms World.call_unit_noop
#print axioms World.receiveRun_unfunded
#print axioms World.receiveRun_ok
#print axioms World.stipend_transfer_failure
#print axioms sendResult_failure
#print axioms payment_atomic_failure
end Solidity.ContractWorld
