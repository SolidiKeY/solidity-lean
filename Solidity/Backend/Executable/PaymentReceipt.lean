import Solidity.Backend.Executable.PaymentCheckpoint
import Solidity.Semantics.RunFrame

/-! Data adapters from an actual world receive result to the existing intrinsic
send receipt table. These transport send observations only. No world journal,
source compiler, stipend gas or fetched EVM simulation is asserted. -/
namespace Solidity.Backend.Executable.PaymentReceipt
open ContractWorld Semantics
variable {K : Type} [DecidableEq K] {contracts : K → Contract}
variable {C : Contract} {Γ : Ctx}

/-- Explicitly refuse noncompleted results, rather than defaulting to a missing
oracle entry (which the intrinsic send semantics would accept). -/
def reply {α : Type} : TRes α → Option ExtResult
  | .ok _ => some (.ok [])
  | .error e => if catchable e then some (.other e.data) else none

/-- The actual key is installed first, shadowing an old receipt for that key.
Other keys and all typed caller storage, heap and locals remain unchanged. -/
def install (σ : State C Γ) (addr amount : PrimTy.uint.Denote) (r : ExtResult) : State C Γ :=
  {σ with tx := {σ.tx with ext := (sendKey addr amount,r) :: σ.tx.ext}}

def observe {α : Type} (σ : State C Γ) (addr amount : PrimTy.uint.Denote)
    (run : TRes α) : Option Bool :=
  (reply run).map fun r => (install σ addr amount r).canPay addr amount

theorem installed_lookup (σ : State C Γ) (addr amount : PrimTy.uint.Denote) (r : ExtResult) :
    lookupBy (sendKey addr amount) (install σ addr amount r).tx.ext = some r := by
  simp only [install, lookupBy, ↓reduceIte]

theorem other_lookup (σ : State C Γ) (addr amount : PrimTy.uint.Denote) (r : ExtResult)
    (key : ExtKey) (different : key ≠ sendKey addr amount) :
    lookupBy key (install σ addr amount r).tx.ext = lookupBy key σ.tx.ext := by
  simp only [install, lookupBy, different, ↓reduceIte]

private theorem accepts (σ : State C Γ) (addr amount : PrimTy.uint.Denote)
    (funded : amount.val ≤ σ.selfBalance.val) :
    (install σ addr amount (.ok [])).canPay addr amount = true := by
  unfold State.canPay
  rw [installed_lookup]
  simp only [install, decide_eq_true funded, Bool.true_and]

private theorem rejects (σ : State C Γ) (addr amount : PrimTy.uint.Denote) (bytes : List UInt8) :
    (install σ addr amount (.other bytes)).canPay addr amount = false := by
  unfold State.canPay
  rw [installed_lookup]
  exact Bool.and_false _

omit [DecidableEq K] in
/-- Funding is derived from actual World.enter success, before any body or
settlement; it is not assumed as part of a desired simulation. -/
private theorem enter_funded (w : World contracts) {k : K} (self : Address)
    (ctx : Context) (st : Storage (contracts k)) (payable : Bool) (σ : State (contracts k) [])
    (entered : w.enter self ctx st payable = .ok σ) : ctx.value.val ≤ (w.funds ctx.sender).val := by
  by_cases h : ctx.value.val ≤ (w.funds ctx.sender).val
  · exact h
  · have refused : ctx.value.val > (w.funds ctx.sender).val := by omega
    simp only [World.enter, refused, ↓reduceIte] at entered
    cases entered

theorem receive_funded {w next : World contracts} {k : K} {recipient : Handle k}
    {entry : Entry (contracts k) Unit} {sender : Address} {amount : ContractWorld.Word}
    (ran : w.receiveRun recipient entry sender amount = .ok (next, ())) :
    amount.val ≤ (w.funds sender).val := by
  obtain ⟨st, σ, out, _, entered, _, _⟩ := World.receiveRun_ok ran
  exact enter_funded w recipient.address {sender, mode := .ordinary amount} st entry.payable σ entered

/-- Derived receipts agree in both Bool directions with actual sendResult.
The explicit balance equality is a checkpoint condition, not general pending
caller/world reconciliation. Noncatchable original halts are refused, not false. -/
theorem actual_observation (w : World contracts) {k : K} (recipient : Handle k)
    (entry : Entry (contracts k) Unit) (sender : Address) (amount : ContractWorld.Word)
    (σ : State C Γ) (aligned : σ.selfBalance.val = (w.funds sender).val) :
    observe σ recipient.address.1 amount (w.receiveRun recipient entry sender amount) =
      (sendResult w (w.receiveRun recipient entry sender amount)).toOption.map Prod.snd := by
  cases run : w.receiveRun recipient entry sender amount with
  | ok pair =>
    rcases pair with ⟨next, ⟨⟩⟩
    have funded : amount.val ≤ σ.selfBalance.val := by
      rw [aligned]
      exact receive_funded run
    simp only [observe, reply, Option.map_some, sendResult, Except.toOption,
      accepts σ recipient.address.1 amount funded]
  | error e =>
    cases caught : catchable e with
    | false => simp only [observe, reply, caught, Bool.false_eq_true, ↓reduceIte,
        Option.map_none, sendResult, Except.toOption]
    | true => simp only [observe, reply, caught, ↓reduceIte, Option.map_some,
        rejects, sendResult, Except.toOption]

/-- Actual installed-code admission remains a separate producer condition. -/
theorem stipend_observation (w : World contracts) {k : K} (recipient : Handle k)
    (entry : Entry (contracts k) Unit) (sender : Address) (amount : ContractWorld.Word)
    (σ : State C Γ) (aligned : σ.selfBalance.val = (w.funds sender).val)
    (admitted : (w.isLibrary k || (w.storage? recipient).isNone) = false) :
    observe σ recipient.address.1 amount (w.receiveRun recipient entry sender amount) =
      (w.stipend .send recipient entry sender amount).toOption.map Prod.snd := by
  rw [actual_observation w recipient entry sender amount σ aligned]
  simp only [World.stipend, admitted, Bool.false_eq_true, ↓reduceIte]

/-- Fail closed at the actual stipend code-admission boundary before deriving
any intrinsic receipt from the existing receive execution. -/
def prepare (w : World contracts) {k : K} (recipient : Handle k)
    (entry : Entry (contracts k) Unit) (sender : Address) (amount : ContractWorld.Word) :
    Option ExtResult :=
  if w.isLibrary k || (w.storage? recipient).isNone then none
  else reply (w.receiveRun recipient entry sender amount)

/-- Entire admitted/refused source Bool observation, derived from actual world
execution and code admission. This is not a world/post-state simulation. -/
theorem world_observation (w : World contracts) {k : K} (recipient : Handle k)
    (entry : Entry (contracts k) Unit) (sender : Address) (amount : ContractWorld.Word)
    (σ : State C Γ) (aligned : σ.selfBalance.val = (w.funds sender).val) :
    ((prepare w recipient entry sender amount).map fun r =>
      (install σ recipient.address.1 amount r).canPay recipient.address.1 amount) =
      (w.stipend .send recipient entry sender amount).toOption.map Prod.snd := by
  cases admission : w.isLibrary k || (w.storage? recipient).isNone with
  | true => simp only [prepare, World.stipend, admission, ↓reduceIte, Except.toOption, Option.map_none]
  | false =>
    simp only [prepare, admission, Bool.false_eq_true, ↓reduceIte]
    exact stipend_observation w recipient entry sender amount σ aligned admission

/-- An explicitly rejecting table entry yields intrinsic transfer refusal.
This helper alone says nothing about which actual receive produced that entry. -/
theorem failed_transfer (σ : State C Γ) (addr amount : PrimTy.uint.Denote) (e : THalt) :
    TRun.transfer (.simple (.lit addr.1 addr.2)) (.simple (.lit amount.1 amount.2))
      (install σ addr amount (.other e.data)) = .error .revert := by
  change (if (install σ addr amount (.other e.data)).canPay addr amount then _ else _) = _
  rw [rejects]
  rfl

/-- Exact intrinsic result-local observation, using the actual sendT. -/
theorem source_result (σ : State C Γ) (pv : Idx Γ (.val .bool))
    (addr amount : PrimTy.uint.Denote) (r : ExtResult) :
    TEnv.get pv (sendT (install σ addr amount r) pv addr amount).st.env =
      (install σ addr amount r).canPay addr amount := by
  exact TEnv.get_set pv _ _

/-- Typed protected locals use the published environment frame fact. -/
theorem protected_local (σ : State C Γ) (pv : Idx Γ (.val .bool))
    (addr amount : PrimTy.uint.Denote) (r : ExtResult) {t : LTy} (i : Idx Γ t)
    (different : pv.toNat ≠ i.toNat) :
    TEnv.get i (sendT (install σ addr amount r) pv addr amount).st.env = TEnv.get i σ.env :=
  TEnv.get_set_ne pv i _ _ different

/-- Refusal originates exactly in a noncatchable halt. The Option receipt
does not retain its kind; the actual original run must be kept separately. -/
theorem refused_iff {α : Type} (run : TRes α) : reply run = none ↔
    ∃ e, run = .error e ∧ catchable e = false := by
  cases run with
  | ok value => simp only [reply, Option.some_ne_none]; constructor
                · intro h; cases h
                · rintro ⟨e,h,_⟩; cases h
  | error e =>
    cases h : catchable e with
    | false => simp only [reply, h, Bool.false_eq_true, ↓reduceIte];
               exact ⟨fun _ => ⟨e,rfl,h⟩, fun _ => trivial⟩
    | true => simp only [reply, h, ↓reduceIte, Option.some_ne_none]; constructor
              · intro h; cases h
              · rintro ⟨e',eq,bad⟩; cases eq; cases h.symm.trans bad

/-- Preparation is refused exactly when the real full stipend send halts.
The original run carries its halt; the Option refusal is not a halt encoding. -/
theorem prepare_refused_iff (w : World contracts) {k : K} (recipient : Handle k)
    (entry : Entry (contracts k) Unit) (sender : Address) (amount : ContractWorld.Word) :
    prepare w recipient entry sender amount = none ↔
      ∃ e, w.stipend .send recipient entry sender amount = .error e := by
  cases admission : w.isLibrary k || (w.storage? recipient).isNone with
  | true =>
    simp only [prepare, World.stipend, admission, ↓reduceIte]
    exact ⟨fun _ => ⟨.exhausted,rfl⟩, fun _ => trivial⟩
  | false =>
    simp only [prepare, World.stipend, admission, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro refused
      obtain ⟨e, ran, uncaught⟩ := (refused_iff _).mp refused
      exact ⟨e, (send_error_iff w _ e).mpr ⟨ran,uncaught⟩⟩
    · rintro ⟨e, halted⟩
      exact (refused_iff _).mpr ⟨e,(send_error_iff w _ e).mp halted⟩

/-- info: 'Solidity.Backend.Executable.PaymentReceipt.prepare_refused_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prepare_refused_iff
/-- info: 'Solidity.Backend.Executable.PaymentReceipt.receive_funded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms receive_funded
/-- info: 'Solidity.Backend.Executable.PaymentReceipt.actual_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_observation
/-- info: 'Solidity.Backend.Executable.PaymentReceipt.stipend_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stipend_observation
/-- info: 'Solidity.Backend.Executable.PaymentReceipt.world_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms world_observation
/-- info: 'Solidity.Backend.Executable.PaymentReceipt.failed_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms failed_transfer
/-- info: 'Solidity.Backend.Executable.PaymentReceipt.source_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_result
/-- info: 'Solidity.Backend.Executable.PaymentReceipt.protected_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms protected_local
/-- info: 'Solidity.Backend.Executable.PaymentReceipt.refused_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms refused_iff
end Solidity.Backend.Executable.PaymentReceipt
