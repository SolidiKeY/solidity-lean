import Solidity.Calculus.Lifetime
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close

/-!
# Safety and possible settlement throughout an escrow's lifetime

The two flags record settlement, not actual ether transfers. Its interface
contains only the declared calls below. Proofs use the deterministic run;
neither the entry calls nor the constructor calls another contract.
-/

namespace Solidity.Examples.Tactics.Lifetime

open Solidity.Lifetime
open scoped Scoped

def Escrow : Contract := contract!{
  bool paid;
  bool refunded;
  constructor() { paid = false; refunded = false; }
  function pay() public { require(!refunded); paid = true; }
  function refund() public { require(!paid); refunded = true; }
  function deposit() public payable { }
  function fail() public payable { paid = true; revert(); }
  -- A Lean modelling assumption, used to test resource exhaustion below.
  function exhaust() public { assume(false); }
}

inductive Action where
  | pay | refund | deposit | fail | exhaust

def model : System Escrow Unit Action where
  deploy := fun _ => sol[Escrow]{ constructor(); }
  call
    | .pay => sol[Escrow]{ pay(); }
    | .refund => sol[Escrow]{ refund(); }
    | .deposit => sol[Escrow]{ deposit(); }
    | .fail => sol[Escrow]{ fail(); }
    | .exhaust => sol[Escrow]{ exhaust(); }
  payable := fun a => match a with | .deposit | .fail => true | _ => false

private def safeFormula : Fml Escrow [] := dl[Escrow]{ ¬(paid == true ∧ refunded == true) }

/-- `paid` and `refunded` never both hold at an observation boundary. -/
def Safe (s : World Escrow) : Prop := holds s.observe safeFormula

/-- Settlement means one of the two flags is set. -/
def Settled (s : World Escrow) : Prop :=
  holds s.observe dl[Escrow]{ paid == true } ∨ holds s.observe dl[Escrow]{ refunded == true }

private theorem safe_read (σ : State Escrow []) :
    holds σ safeFormula ↔ Safe (World.ofState σ) := Iff.rfl

/-- Every interface call preserves mutual exclusion. -/
private theorem call_safe (a : Action) : Fml.Valid
    (.imp safeFormula (.modal .box (model.call a) .nil safeFormula)) := by
  cases a <;> sol_prove
  sol_leaf
  sol_close

private theorem constructor_safe : Fml.Valid
    (.modal .box (model.deploy ()) .nil safeFormula) := by sol_prove

/-- The constructor establishes mutual exclusion; each interface call keeps
it, and waiting or a rollback changes neither flag. -/
theorem safeInvariant : Solidity.Lifetime.Invariant model Safe := by
  apply Solidity.Lifetime.Invariant.ofRuns
  · intro d tx σ _ run
    cases d
    exact (safe_read σ).mp (post_of_deploy_box (constructor_safe _) run)
  · intro s a tx t accepted allowed hi run
    apply System.preserves_of_fml safeFormula safeFormula (call_safe a)
      (entry := ?_) (reflect := fun σ h => (safe_read σ).mp h) accepted allowed hi run
    intro s tx σ _ _ hi enter
    have hs : σ.storage = s.storage := World.enter_storage enter
    have hsafe : holds (World.ofState σ).observe safeFormula := by
      change holds { s.observe with storage := σ.storage } safeFormula
      rw [hs]
      exact hi
    exact (safe_read σ).mpr hsafe
  · intro s t _ hi
    exact hi

/-- No transaction sequence from the constructor reaches double settlement. -/
theorem neverBoth : AG model Safe := safeInvariant.always

private def tx : TTx := { selfAddress := ⟨9, rfl⟩, msgSender := ⟨1, rfl⟩ }

private def start : World Escrow :=
  ⟨.cons (.prim false) (.cons (.prim false) .nil), [(⟨1, rfl⟩, 0)],
    ⟨0, rfl⟩, ⟨9, rfl⟩, ⟨0, rfl⟩⟩

private def paid : World Escrow :=
  { start with storage := .cons (.prim true) (.cons (.prim false) .nil) }

private theorem deployed : model.Init start := by
  refine ⟨(), tx, ?_, trivial, ?_, ?_⟩
  · exact { start.observe with tx := tx }
  · rfl
  · rfl

/-- `pay();` is an actual successful transaction from deployment. -/
theorem paymentTrace : Trace model start [.call .pay tx] paid :=
  .cons (.commit ⟨rfl, Int.le_refl _, by decide⟩ trivial rfl) (.nil _)

/-- Some finite transaction sequence from the constructor settles payment. -/
theorem paymentPossible : EF model (fun s => holds s.observe dl[Escrow]{ paid == true }) :=
  ⟨start, deployed, [.call .pay tx], paid, paymentTrace, rfl⟩

private def refunded : World Escrow :=
  { start with storage := .cons (.prim false) (.cons (.prim true) .nil) }

/-- A different execution from the same deployment settles by refund. -/
theorem refundPossible : EF model (fun s => holds s.observe dl[Escrow]{ refunded == true }) :=
  ⟨start, deployed, [.call .refund tx], refunded,
    .cons (.commit ⟨rfl, Int.le_refl _, by decide⟩ trivial rfl) (.nil _), rfl⟩

private def userTx (s : World Escrow) : TTx :=
  { selfAddress := s.address, timestamp := s.timestamp,
    msgSender := if s.address = ⟨0, rfl⟩ then ⟨1, rfl⟩ else ⟨0, rfl⟩ }

private theorem userTx_accepted (s : World Escrow) : s.accepts (userTx s) := by
  refine ⟨rfl, Int.le_refl _, ?_⟩
  change (if s.address = ⟨0, rfl⟩ then (⟨1, rfl⟩ : PrimTy.uint.Denote) else ⟨0, rfl⟩) ≠ s.address
  split
  · next h => rw [h]; decide
  · next h => exact Ne.symm h

private def paidAfter (s : World Escrow) : World Escrow :=
  { s with storage := paid.storage }

private theorem payPending (s : World Escrow) (pending : s.storage = start.storage) :
    model.run s .pay (userTx s) = .ok (paidAfter s) := by
  change (do
    let σ ← s.enter (userTx s)
    let o ← (model.call .pay).run σ
    pure (World.ofState o.st)) = .ok (paidAfter s)
  rw [World.enter_zero s (userTx s) rfl]
  cases s with
  | mk storage net balance address timestamp =>
    change storage = start.storage at pending
    subst storage
    rfl

private theorem pendingOrSettled (s : World Escrow) : s.storage = start.storage ∨ Settled s :=
  match s with
  | ⟨.cons (.prim false) (.cons (.prim false) .nil), _, _, _, _⟩ => .inl rfl
  | ⟨.cons (.prim true) (.cons (.prim _) .nil), _, _, _, _⟩ => .inr (.inl rfl)
  | ⟨.cons (.prim false) (.cons (.prim true) .nil), _, _, _, _⟩ => .inr (.inr rfl)

/-- Settlement remains possible after every reached state, even if previous
transactions failed or the environment waited indefinitely. -/
theorem settlementRemainsPossible : AGEF model Settled := fun s _ =>
  match pendingOrSettled s with
  | .inr settled => .here settled
  | .inl pending =>
    .next (.commit (userTx_accepted s) trivial (payPending s pending)) (.here (.inl rfl))

/-- The invariant excludes every finite trace to double settlement. -/
theorem doubleSettlementImpossible : ¬ EF model (fun s => ¬ Safe s) :=
  (show AG model (fun s => ¬ ¬ Safe s) from fun s h hn => hn (neverBoth s h)).not_EF

/-- A payable call that writes then reverts rolls back its incoming payment,
ledger update, and storage write. Time still advances with the transaction. -/
theorem paymentRollback : Step model start
    (.call .fail { tx with msgValue := ⟨7, rfl⟩, timestamp := ⟨3, rfl⟩ })
    (start.atTime ⟨3, rfl⟩) :=
  .rollback ⟨rfl, by decide, by decide⟩ trivial rfl (.inl rfl)

/-- A successful payable transaction commits its payment to both balance and
net ledger. Unlike the reverting call, it retains the incoming funds. -/
theorem depositCommitted : Step model start
    (.call .deposit { tx with msgValue := ⟨7, rfl⟩ })
    { start with balance := ⟨7, rfl⟩, net := [(tx.msgSender, 7)] } :=
  .commit ⟨rfl, Int.le_refl _, by decide⟩ trivial rfl

/-- Transaction sequences compose: a deposit followed by payment keeps the
deposit's funds and reaches the paid flag. -/
theorem depositThenPay : Trace model start
    [.call .deposit { tx with msgValue := ⟨7, rfl⟩ }, .call .pay tx]
    { paid with balance := ⟨7, rfl⟩, net := [(tx.msgSender, 7)] } :=
  (Trace.cons depositCommitted (.nil _)).append
    (.cons (.commit ⟨rfl, Int.le_refl _, by decide⟩ trivial rfl) (.nil _))

/-- A payment to a nonpayable entry is refused before its body runs. -/
example : model.run start .pay { tx with msgValue := ⟨1, rfl⟩ } = .error .revert := rfl

/-- A completed payment cannot be followed by a successful refund. -/
example : model.run paid .refund tx = .error .revert := rfl

/-- Waiting can leave the state exactly as it was. -/
example : Step model start (.wait start.timestamp) start := .wait (Int.le_refl _)

/-- Backwards time and a changed contract address are inadmissible. -/
example : ¬ (start.atTime ⟨3, rfl⟩).accepts tx := by unfold World.accepts; decide +kernel
example : ¬ start.accepts { tx with selfAddress := ⟨8, rfl⟩ } := by
  unfold World.accepts
  decide +kernel

/-- Exhaustion satisfies the existing diamond, even with a false postcondition. -/
example : ⊨ᶠ dl[Escrow]{ ⟨ exhaust(); ⟩ false } := by sol_prove

/-- It nevertheless supplies no successful lifetime commit, from any state. -/
theorem exhaustedNotCommitted (s t : World Escrow) (tx : TTx) :
    model.run s .exhaust tx ≠ .ok t := by
  intro h
  obtain ⟨σ, o, _, ran, _⟩ := System.run_ok h
  cases ran

/-- A fresh transaction drops a previous call's memory. -/
example : (start.enter tx).toOption.map (·.H) = some [] := rfl

/-- Successful transaction entry credits both spendable funds and the ledger. -/
example : ((start.enter { tx with msgValue := ⟨7, rfl⟩ }).toOption.map fun σ =>
    (σ.selfBalance.1, (Semantics.lookupBy tx.msgSender σ.net).getD 0)) = some (7, 7) := rfl

def Refused : Contract := contract!{ constructor() { require(false); } }

private def refused : System Refused Unit Unit where
  deploy := fun _ => sol[Refused]{ constructor(); }
  call := fun _ => sol[Refused]{ }

/-- A failed constructor creates no deployed state, even though default storage
exists and the ordinary box accepts its revert. -/
theorem failedDeployment (s : World Refused) : ¬ refused.Init s := by
  intro ⟨d, tx, σ, _, run, _⟩
  unfold Contract.deployT at run
  split at run <;> cases run

/-- Neither waiting nor calls can create a lifetime without a deployment. -/
theorem refusedUnreachable (s : World Refused) : ¬ Solidity.Lifetime.Reachable refused s :=
  fun h => let ⟨s, _, hs, _⟩ := h.trace; failedDeployment s hs

-- The lifetime induction and concrete witnesses use no unchecked computation.
/-- info: 'Solidity.Examples.Tactics.Lifetime.neverBoth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms neverBoth
/-- info: 'Solidity.Examples.Tactics.Lifetime.paymentPossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms paymentPossible
/-- info: 'Solidity.Examples.Tactics.Lifetime.exhaustedNotCommitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exhaustedNotCommitted
/--
info: 'Solidity.Examples.Tactics.Lifetime.settlementRemainsPossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms settlementRemainsPossible
/-- info: 'Solidity.Examples.Tactics.Lifetime.depositThenPay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms depositThenPay

end Solidity.Examples.Tactics.Lifetime
