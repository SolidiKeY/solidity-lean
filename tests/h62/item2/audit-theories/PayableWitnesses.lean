import Solidity.Theory.Mutability.Payable
import tests.h62.item2.«audit-theories».CloserWitnesses

/-!
Six ordinary Payable input packets, plus a checked empty-input certificate for
World.enter_static (explicit Q-STATIC-VALUE option3 intentional H69 boundary).
World fixtures have installed code and funds, not merely dangling handles.
Positive controls separately require success of System.run, World.enter and
World.callFrame; no broader physical-EVM/payment-settlement guarantee is claimed.
-/
namespace H62.AuditTheories
open Solidity

/-- A real nonzero incoming value. -/
def payableTx : TTx := {msgSender := uintOfNat 1, selfAddress := uintOfNat 0, msgValue := uintOfNat 1}
/-- A concrete persistent world with room to accept the incoming unit. -/
def payableLifetime : Lifetime.World bridgeContract :=
  ⟨bridgeStorage, [], uintOfNat 3, uintOfNat 0, uintOfNat 0⟩
/-- An inhabited interface with a normally returning body. -/
def payableSystem : Lifetime.System bridgeContract Unit Unit :=
  {deploy := fun _ => .nil, call := fun _ => .nil, payable := fun _ => false}
/-- One installed contract identity. -/
def payableCatalog : Unit → Contract := fun _ => bridgeContract
/-- A bounded contract address. -/
def payableSelf : ContractWorld.Address := ⟨uintOfNat 0, by
    rw [uintOfNat_val (Nat.lt_trans (by decide : 0 < 1) (Nat.one_lt_two_pow' 255))]
    exact Int.pow_pos (by decide)⟩
/-- A distinct bounded sender address. -/
def payableSender : ContractWorld.Address := ⟨uintOfNat 1, by
    rw [uintOfNat_val (Nat.one_lt_two_pow' 255)]
    simpa only [Int.natCast_pow] using (Int.ofNat_lt.mpr (Nat.one_lt_two_pow' 159))⟩
/-- Installed matching code and sufficient funds are explicit data. -/
def payableWorld : ContractWorld.World payableCatalog :=
  {accounts := fun _ => some ⟨(), bridgeStorage⟩, funds := fun _ => uintOfNat 3}
/-- Ordinary positive-value context; static mode cannot represent this value. -/
def payableContext : ContractWorld.Context :=
  {sender := payableSender, mode := .ordinary (uintOfNat 1)}

/-- Both simple refusal hypotheses coexist. -/
theorem payable_refuses_joint_witness :
    ∃ (payable : Bool) (v : Int), payable = false ∧ v ≠ 0 :=
  ⟨false, 1, rfl, by decide⟩

/-- The complete system/action/world/transaction packet is jointly inhabited. -/
theorem payable_system_joint_witness :
    ∃ (C : Contract) (D A : Type) (M : Lifetime.System C D A)
      (s : Lifetime.World C) (a : A) (tx : TTx),
      M.payable a = false ∧ tx.msgValue.1 ≠ 0 ∧ M.run s a tx = .error .revert :=
  ⟨bridgeContract, Unit, Unit, payableSystem, payableLifetime, (), payableTx, rfl, by decide,
    Solidity.Theory.Mutability.System.run_nonpayable _ _ _ _ rfl (by decide)⟩

/-- The constructor flag and positive-value premise share a concrete program. -/
theorem payable_deploy_joint_witness :
    ∃ (C : Contract) (Γ' : Ctx) (P : Prog C [] Γ') (tx : TTx),
      (C.ctor.map (·.payable)).getD false = false ∧ tx.msgValue.1 ≠ 0 ∧
        C.deployT P tx = .error .revert :=
  ⟨bridgeContract, [], .nil, payableTx, rfl, by decide,
    Solidity.Theory.Mutability.deployT_nonpayable _ _ rfl (by decide)⟩

/-- Nonempty transient layout/read body and a positive transaction coexist. -/
theorem payable_transact_joint_witness :
    ∃ (C : Contract) (L : Solidity.Transient.Layout) (α : Type)
      (body : Solidity.Transient.Program C L α) (world : Lifetime.World C)
      (tx : TTx) (ctx : Solidity.Transient.Context), tx.msgValue.1 ≠ 0 ∧
        Solidity.Transient.Program.transact body world tx false ctx = .error .revert :=
  ⟨bridgeContract, [("flag", .bool)], Bool, .read .here, payableLifetime,
    payableTx, ⟨.view, false⟩, by decide,
    Solidity.Theory.Mutability.transact_nonpayable _ _ _ _ (by decide)⟩

/-- Nonpayable frame inputs have real matching installed code and positive value. -/
theorem payable_enter_joint_witness :
    ∃ (K : Type) (contracts : K → Contract) (w : ContractWorld.World contracts)
      (k : K) (self : ContractWorld.Address) (ctx : ContractWorld.Context)
      (st : Storage (contracts k)), ctx.value.1 ≠ 0 ∧ w.enter self ctx st false = .error .revert :=
  ⟨Unit, payableCatalog, payableWorld, (), payableSelf, payableContext, bridgeStorage, by decide,
    Solidity.Theory.Mutability.ContractWorld.World.enter_nonpayable _ _ _ _ (by decide)⟩

/-- Call-frame hypotheses include their global equality instance and real code. -/
theorem payable_call_joint_witness :
    ∃ (K : Type) (eqK : DecidableEq K) (contracts : K → Contract)
      (w : ContractWorld.World contracts) (k : K) (α : Type) (r : ContractWorld.Handle k)
      (entry : ContractWorld.Entry (contracts k) α) (ctx : ContractWorld.Context),
      letI : DecidableEq K := eqK
      entry.payable = false ∧ ctx.value.1 ≠ 0 ∧ w.storage? r = some (Storage.init (contracts k)) :=
  ⟨Unit, inferInstance, payableCatalog, payableWorld, (), Unit, ⟨payableSelf⟩,
    ContractWorld.Entry.unit .nil false, payableContext, rfl, by decide, rfl⟩

/-- All inputs of static entry have no simultaneous instance. Coordinator
    Q-STATIC-VALUE accepts this intentional H69 boundary, with no operational
    refusal coverage. This certificate is not a joint-satisfiability witness. -/
theorem payable_static_inputs_impossible :
    ¬ ∃ (K : Type) (contracts : K → Contract) (_w : ContractWorld.World contracts)
      (k : K) (_self : ContractWorld.Address) (ctx : ContractWorld.Context)
      (_st : Storage (contracts k)) (_payable : Bool),
      ctx.isStatic = true ∧ ctx.value.1 ≠ 0 := by
  rintro ⟨K, contracts, _w, k, _self, ctx, _st, _payable, hs, hv⟩
  rcases ctx with ⟨sender, mode, ext⟩
  cases mode with
  | ordinary value => cases hs
  | readOnly => exact hv rfl

/-- Changing only the entry flag to payable permits a genuine successful call. -/
theorem payable_system_positive_control :
    ∃ w', ({payableSystem with payable := fun _ => true}).run payableLifetime () payableTx = .ok w' :=
  ⟨_, rfl⟩

/-- Funded, installed, payable code can enter: this failure API is not reject-all. -/
theorem payable_enter_positive_control :
    ∃ σ, payableWorld.enter (k := ()) payableSelf payableContext bridgeStorage true = .ok σ :=
  ⟨_, rfl⟩

/-- Matching installed code also executes and settles a payable call frame. -/
theorem payable_call_positive_control :
    ∃ result, payableWorld.callFrame (k := ()) ⟨payableSelf⟩
      (ContractWorld.Entry.unit .nil true) payableContext = .ok result := by
  have bound : 8 ≤ 2 ^ 256 := Nat.pow_le_pow_right (n := 2) (by decide) (by decide : 3 ≤ 256)
  have h0 : 0 < 2 ^ 256 := by omega
  have h1 : 1 < 2 ^ 256 := by omega
  have h3 : 3 < 2 ^ 256 := by omega
  have distinct : payableSender ≠ payableSelf := by
    intro equal
    have word := congrArg (fun a : ContractWorld.Address => a.1.1) equal
    change (uintOfNat 1).1 = (uintOfNat 0).1 at word
    rw [uintOfNat_val h1, uintOfNat_val h0] at word
    cases word
  have notfunds : ¬ (uintOfNat 1).1 > (uintOfNat 3).1 := by
    rw [uintOfNat_val h1, uintOfNat_val h3]
    decide
  have nonzero : (uintOfNat 1).1 ≠ 0 := by rw [uintOfNat_val h1]; decide
  have balance : PrimTy.ofInt? .uint ((uintOfNat 3).1 + (uintOfNat 1).1) = some (uintOfNat 4) := rfl
  have address : ContractWorld.Address.ofWord? payableSender.1 = some payableSender := by
    unfold ContractWorld.Address.ofWord?
    rw [dif_pos payableSender.2]
  simp only [ContractWorld.World.callFrame, ContractWorld.World.isLibrary, payableWorld,
    ContractWorld.Context.isStatic, payableContext]
  simp only [Bool.false_and, Bool.false_or, Bool.false_eq_true, if_false]
  simp only [ContractWorld.World.storage?, Option.bind_some, dite_true,
    TRes.ofOpt, bind, Except.bind]
  simp only [ContractWorld.World.enter, ContractWorld.Context.value]
  simp only [ContractWorld.Entry.unit, ContractWorld.Context.isStatic,
    Bool.not_true, Bool.false_or, Bool.false_and, Bool.false_eq_true, if_false, notfunds]
  simp only [distinct, nonzero, or_false, if_false, balance, TRes.ofOpt, bind, Except.bind,
    pure, Except.pure]
  simp only [Prog.run_nil]
  simp only [ContractWorld.World.finish, ContractWorld.settle, ContractWorld.settle.go, address]
  exact ⟨_, rfl⟩

#print axioms payable_refuses_joint_witness
#print axioms payable_system_joint_witness
#print axioms payable_deploy_joint_witness
#print axioms payable_transact_joint_witness
#print axioms payable_enter_joint_witness
#print axioms payable_call_joint_witness
#print axioms payable_static_inputs_impossible
#print axioms payable_system_positive_control
#print axioms payable_enter_positive_control
#print axioms payable_call_positive_control
end H62.AuditTheories
