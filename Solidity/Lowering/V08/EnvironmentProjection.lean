import Solidity.Source.World
import Solidity.Semantics.ContractWorld
import Solidity.Semantics.TransientWorld

/-!
# Source request and account observation projections

Total boundary adapters between the published bounded source/intrinsic words
and addresses, and projections of actual G01 requests/source account balances.
They preserve no bytecode or source execution by assumption. Storage layout,
code identity, source expression evaluation and frame admission remain separate
obligations. No environment opcode implementation or source interpreter is added.
-/
namespace Solidity.Lowering.V08.EnvironmentProjection
open Solidity

/-- A bounded source word at the existing intrinsic unsigned type. -/
def liftWord (word : Roadmap.Word) : Semantics.Word :=
  ⟨word.val, by
    simp only [PrimTy.inRange, decide_eq_true_eq]
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr word.isLt⟩⟩

/-- Explicit modular observation of exact Source money. Lossless equality
requires a separately established range invariant; this is not a ledger. -/
def liftBalance (balance : Source.Monetary.Balance) : Semantics.Word :=
  liftWord (Source.Monetary.wordView balance)

def lowerWord (word : Semantics.Word) : Roadmap.Word :=
  ⟨word.1.toNat, by
    have bound := word.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at bound
    omega⟩

/-- Both endpoints include zero and the maximum word: no input exclusion. -/
theorem lower_lift_word (word : Roadmap.Word) : lowerWord (liftWord word) = word := by
  apply Fin.ext
  exact Int.toNat_natCast _

theorem lower_lift_balance (balance : Source.Monetary.Balance) :
    lowerWord (liftBalance balance) = Source.Monetary.wordView balance :=
  lower_lift_word _

theorem lower_lift_balance_exact (balance : Source.Monetary.Balance)
    (fit : Source.Monetary.Fits balance) : (lowerWord (liftBalance balance)).val = balance := by
  simp only [lower_lift_balance, Source.Monetary.wordView_exact _ fit]

theorem lift_lower_word (word : Semantics.Word) : liftWord (lowerWord word) = word := by
  apply Subtype.ext
  have bound := word.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at bound
  exact Int.toNat_of_nonneg bound.1

/-- Account addresses retain the independent 160-bit account bound. -/
def liftAddress (address : Roadmap.Address) : ContractWorld.Address :=
  ⟨liftWord ⟨address.val, Nat.lt_trans address.isLt (by decide +kernel)⟩, by
    simpa only [Int.natCast_pow] using (Int.ofNat_lt.mpr address.isLt)⟩

def lowerAddress (address : ContractWorld.Address) : Roadmap.Address :=
  ⟨address.1.1.toNat, by
    have bound := address.2
    have nonnegative := address.1.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at nonnegative
    have boundCast : address.1.1 < ((2 ^ 160 : Nat) : Int) := by
      simpa only [Int.natCast_pow] using bound
    omega⟩

theorem lower_lift_address (address : Roadmap.Address) :
    lowerAddress (liftAddress address) = address := by
  apply Fin.ext
  exact Int.toNat_natCast _

theorem lift_lower_address (address : ContractWorld.Address) :
    liftAddress (lowerAddress address) = address := by
  apply Subtype.ext
  apply Subtype.ext
  have bound := address.1.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at bound
  exact Int.toNat_of_nonneg bound.1

/-- An ordinary request retains its actual payment and external response table. -/
def requestContext (request : Roadmap.Request)
    (responses : List (Semantics.ExtKey × Semantics.ExtResult)) : ContractWorld.Context :=
  { sender := liftAddress request.sender, mode := .ordinary (liftWord request.value), ext := responses }

/-- All fields of the actual typed transaction are fixed by the request/world.
The world is explicitly advanced to the supplied request timestamp; admission
of that timestamp and payment is not asserted by this field projection. -/
theorem request_tx {K : Type} {contracts : K → Contract} (world : ContractWorld.World contracts)
    (request : Roadmap.Request) (responses : List (Semantics.ExtKey × Semantics.ExtResult)) :
    let tx := (requestContext request responses).tx
      (world.atTime (liftWord request.timestamp)) (liftAddress request.target)
    tx.msgSender = (liftAddress request.sender).1 ∧
    tx.msgValue = liftWord request.value ∧ tx.timestamp = liftWord request.timestamp ∧
    tx.selfAddress = (liftAddress request.target).1 ∧ tx.ext = responses :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Structural projection of source instance-account fields only. Source.World
is not the external session ledger; this is NOT a universal balance semantics.
Use sessionFunds below to include the supplied G01 external ledger. -/
def fundsOf {D : Source.Layout} {L : Roadmap.Address → Source.SPath → Source.STy}
    (world : Source.World D L) : ContractWorld.Address → Semantics.Word :=
  fun address => liftBalance (world.accounts (lowerAddress address)).balance

theorem funds_at_source_address {D : Source.Layout} {L : Roadmap.Address → Source.SPath → Source.STy}
    (world : Source.World D L) (address : Roadmap.Address) :
    fundsOf world (liftAddress address) = liftBalance (world.accounts address).balance := by
  unfold fundsOf
  rw [lower_lift_address]

/-- Structural account-field replacement on an already typed intrinsic world;
not an external session-funding or account-admission certificate. -/
def withSourceFunds {D : Source.Layout} {L : Roadmap.Address → Source.SPath → Source.STy}
    {K : Type} {contracts : K → Contract} (source : Source.World D L)
    (target : ContractWorld.World contracts) : ContractWorld.World contracts :=
  { target with funds := fundsOf source }

theorem balance_projection {D : Source.Layout} {L : Roadmap.Address → Source.SPath → Source.STy}
    {K : Type} {contracts : K → Contract} (source : Source.World D L)
    (target : ContractWorld.World contracts) (address : Roadmap.Address) :
    (withSourceFunds source target).balance (liftAddress address) =
      liftBalance (source.accounts address).balance := funds_at_source_address source address

/-- Installed source accounts supply their own balance. Other addresses use
G01's supplied fixed external ledger and session opening balances/history.
Code installation/domain agreement (including constructor phases) and the
canonical G03 ledger application remain explicit integration obligations. -/
def sessionFunds {D : Source.Layout} {L : Roadmap.Address → Source.SPath → Source.STy}
    (source : Source.World D L) (fixed : Roadmap.Fixed) (environment : Roadmap.SessionEnv)
    (history : List Roadmap.Event) : ContractWorld.Address → Semantics.Word := fun address =>
  let sourceAddress := lowerAddress address
  if (source.accounts sourceAddress).code.isSome then
    liftBalance (source.accounts sourceAddress).balance
  else liftWord (fixed.ledger environment.balance history sourceAddress)

/-- Installed-account reads never substitute an external-ledger value. -/
theorem session_funds_installed {D : Source.Layout}
    {L : Roadmap.Address → Source.SPath → Source.STy} (source : Source.World D L)
    (fixed : Roadmap.Fixed) (environment : Roadmap.SessionEnv) (history : List Roadmap.Event)
    (address : Roadmap.Address) (installed : (source.accounts address).code.isSome = true) :
    sessionFunds source fixed environment history (liftAddress address) =
      liftBalance (source.accounts address).balance := by
  unfold sessionFunds
  dsimp only
  rw [lower_lift_address]
  simp only [installed, if_true]

/-- A code-less account read uses the exact supplied G01 ledger, never the
source instance-account field. This law does not certify a particular ledger. -/
theorem session_funds_external {D : Source.Layout}
    {L : Roadmap.Address → Source.SPath → Source.STy} (source : Source.World D L)
    (fixed : Roadmap.Fixed) (environment : Roadmap.SessionEnv) (history : List Roadmap.Event)
    (address : Roadmap.Address) (external : (source.accounts address).code = none) :
    sessionFunds source fixed environment history (liftAddress address) =
      liftWord (fixed.ledger environment.balance history address) := by
  unfold sessionFunds
  dsimp only
  rw [lower_lift_address]
  simp only [external, Option.isSome_none, Bool.false_eq_true, if_false]

/-- Source endTx changes neither installed balance fields nor the supplied
session ledger/history inputs. No history-rollback equation is assumed. -/
theorem session_funds_endTx {D : Source.Layout}
    {L T : Roadmap.Address → Source.SPath → Source.STy} (state : Source.ExecState D L T)
    (fixed : Roadmap.Fixed) (environment : Roadmap.SessionEnv) (history : List Roadmap.Event) :
    sessionFunds state.endTx.world fixed environment history =
      sessionFunds state.world fixed environment history := rfl

/-- Source endTx and intrinsic reset commute with this account observation.
This is not a storage/transient representation theorem. -/
theorem reset_funds_projection {D : Source.Layout}
    {L T : Roadmap.Address → Source.SPath → Source.STy} {K : Type} {contracts : K → Contract}
    (source : Source.ExecState D L T) (target : ContractWorld.World contracts) :
    withSourceFunds source.endTx.world target.resetTransient =
      (withSourceFunds source.world target).resetTransient := rfl

/-- Project the request fields and observed live balance into an existing typed
state. All storage/heap/locals/net data remain the supplied state's; this is an
observation adapter, not frame admission or a source-state representation. -/
def stateEnvironment {D : Source.Layout} {L : Roadmap.Address → Source.SPath → Source.STy}
    {K : Type} {contracts : K → Contract} {C : Contract} {Γ : Ctx}
    (source : Source.World D L) (target : ContractWorld.World contracts)
    (request : Roadmap.Request) (responses : List (Semantics.ExtKey × Semantics.ExtResult))
    (state : State C Γ) : State C Γ :=
  { state with
    tx := ((requestContext request responses).tx (target.atTime (liftWord request.timestamp)) (liftAddress request.target))
    selfBalance := liftBalance (source.accounts request.target).balance }

/-- The actual typed environment expressions expose exactly the five projected
observations; no source-expression evaluation equation is assumed. -/
theorem expression_observations {D : Source.Layout}
    {L : Roadmap.Address → Source.SPath → Source.STy} {K : Type} {contracts : K → Contract}
    {C : Contract} {Γ : Ctx} (source : Source.World D L) (target : ContractWorld.World contracts)
    (request : Roadmap.Request) (responses : List (Semantics.ExtKey × Semantics.ExtResult))
    (state : State C Γ) :
    let projected := stateEnvironment source target request responses state
    (Val.simple (.env .msgSender rfl) : Val C Γ .uint).evalT projected =
      .ok (liftAddress request.sender).1 ∧
    (Val.simple (.env .msgValue rfl) : Val C Γ .uint).evalT projected =
      .ok (liftWord request.value) ∧
    (Val.simple (.env .timestamp rfl) : Val C Γ .uint).evalT projected =
      .ok (liftWord request.timestamp) ∧
    (Val.simple (.env .selfAddress rfl) : Val C Γ .uint).evalT projected =
      .ok (liftAddress request.target).1 ∧
    (Val.simple (.env .selfBalance rfl) : Val C Γ .uint).evalT projected =
      .ok (liftBalance (source.accounts request.target).balance) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Source endTx and actual intrinsic transactionEntry commute with this
projection, including the intrinsic heap/transient reset and retained ledger. -/
theorem state_environment_reset {D : Source.Layout}
    {L T : Roadmap.Address → Source.SPath → Source.STy} {K : Type} {contracts : K → Contract}
    {C : Contract} (source : Source.ExecState D L T) (target : ContractWorld.World contracts)
    (request : Roadmap.Request) (responses : List (Semantics.ExtKey × Semantics.ExtResult))
    (state : State C []) :
    stateEnvironment source.endTx.world target request responses state.transactionEntry =
      (stateEnvironment source.world target request responses state).transactionEntry := rfl

/-- Arbitrary actual source journal rollback retains exactly the entry funds. -/
theorem source_rollback_funds {D : Source.Layout}
    {L T : Roadmap.Address → Source.SPath → Source.STy} (state : Source.ExecState D L T)
    (operations : List (Source.Op D L T)) (request : Roadmap.Request) (static : Bool) :
    fundsOf ((state.enter request.target request.sender request.value request.input static).rollback
      (state.run operations)).world = fundsOf state.world := by
  rw [Source.rollback_run]

/-- A committed source descendant followed by ancestor rollback has the same
entry balance observation, for populated account/transient operation lists. -/
theorem source_outer_rollback_funds {D : Source.Layout}
    {L T : Roadmap.Address → Source.SPath → Source.STy} (state : Source.ExecState D L T)
    (beforeOps inner tail : List (Source.Op D L T)) (request : Roadmap.Request) (static : Bool) :
    let frame := (state.run beforeOps).enter request.target request.sender request.value request.input static
    fundsOf ((state.enter request.target request.sender request.value request.input static).rollback
      ((frame.commit ((state.run beforeOps).run inner)).run tail)).world = fundsOf state.world := by
  dsimp only
  rw [Source.rollback_outer_after_commit]

#print axioms lower_lift_word
#print axioms lift_lower_word
#print axioms lower_lift_address
#print axioms lift_lower_address
#print axioms request_tx
#print axioms funds_at_source_address
#print axioms balance_projection
#print axioms session_funds_installed
#print axioms session_funds_external
#print axioms session_funds_endTx
#print axioms reset_funds_projection
#print axioms expression_observations
#print axioms state_environment_reset
#print axioms source_rollback_funds
#print axioms source_outer_rollback_funds
end Solidity.Lowering.V08.EnvironmentProjection
