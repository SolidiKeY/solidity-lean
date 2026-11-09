import Solidity.Theory.Reachable.CleanTail
import tests.h62.item2.«audit-theories».AssignableWitnesses

/-! Simultaneous original clean-tail inputs, including the private helper.
The global interface is inhabited by Unit arguments, a successful deployment,
an admitted entry and a real flag write. These are source-model observations;
no compiler, target ABI/gas/fork or physical EVM adequacy is claimed. -/
namespace H62.AuditTheories
open Solidity Solidity.Lifetime Solidity.Reachable

/-- A nonempty admitted interface with an observable successful call body. -/
def tailAuditSystem : System bridgeContract Unit Unit where
  deploy := fun _ => .nil
  call := fun _ => assignableWrite

/-- The actual world returned by the successful nil constructor. -/
def tailAuditWorld : World bridgeContract :=
  World.ofState (State.deploy bridgeContract {})

/-- A distinct external sender, zero value, matching deployed address and time. -/
def tailAuditTx : TTx := { msgSender := uintOfNat 1 }

/-- The fresh state of this accepted transaction. -/
def tailAuditEntry : State bridgeContract [] :=
  { tailAuditWorld.observe with tx := tailAuditTx }

/-- Every constructor and call of the SAME interface exposes no storage alias. -/
theorem tail_audit_exposes : ExposesNone tailAuditSystem :=
  ⟨(fun _ => rfl), (fun _ => rfl)⟩

/-- Successful deployment is supplied, not inferred from a default storage. -/
theorem tail_audit_init : tailAuditSystem.Init tailAuditWorld :=
  ⟨(), {}, State.deploy bridgeContract {}, True.intro, rfl, rfl⟩

/-- The selected external transaction is admitted by the deployed world. -/
theorem tail_audit_accepts : tailAuditWorld.accepts tailAuditTx :=
  ⟨rfl, Int.le_refl _, by decide⟩

/-- All reachability, payment, allowance and successful-entry obligations coexist. -/
theorem tail_audit_entry : EntryState tailAuditSystem tailAuditEntry :=
  ⟨tailAuditWorld, tailAuditTx, (), .init tail_audit_init, tail_audit_accepts,
    rfl, True.intro, World.enter_zero tailAuditWorld tailAuditTx rfl⟩

/-- The admitted call actually changes a named flag from false to true. -/
theorem tail_audit_write_success :
    tailAuditWorld.storage.find bridgeFlag = some (.prim false) ∧
      ∃ after, tailAuditSystem.run tailAuditWorld () tailAuditTx = .ok after ∧
        after.storage.find bridgeFlag = some (.prim true) :=
  ⟨rfl, _, rfl, rfl⟩

/-- Both anonymous All premises and all data coexist on nonempty fields. -/
theorem tail_anon_inputs_joint :
    ∃ (P : Hered) (fs : List (Name × Ty)) (L : List Name) (x y : SFields fs),
      x.All P ∧ y.All P ∧ SFields.anon L x y = y :=
  ⟨cleanTailH, [("flag", .prim .bool)], ["flag"],
    .cons (.prim false) .nil, .cons (.prim true) .nil,
    (by simp only [SFields.All_cons, SVal.All_prim, SFields.All_nil, and_self]),
    (by simp only [SFields.All_cons, SVal.All_prim, SFields.All_nil, and_self]), rfl⟩

/-- A real transient root alongside a persistent array. -/
def tailTransientContract : Contract :=
  { vars := bridgeContract.vars, transientRoots := ["flag"] }

/-- One live persistent element and a true transient flag. -/
def tailTransientStorage : Storage tailTransientContract :=
  .cons (.array (.cons (.prim false) .nil) .nil (by decide))
    (.cons (.prim true) .nil)

/-- The transient root selected for the reset observation. -/
def tailTransientFlag : SRef tailTransientContract (.prim .bool) := ⟨"flag", rfl, .nil⟩

/-- The persistent live-array root in the same transient-reset fixture. -/
def tailTransientArray : SRef tailTransientContract (.ref (.array (.prim .bool))) :=
  ⟨"items", rfl, .nil⟩

/-- Reset preserves an actual successful read of a one-element persistent array. -/
theorem tail_transient_array_preserved :
    tailTransientStorage.find tailTransientArray =
      some (.array (.cons (.prim false) .nil) .nil (by decide)) ∧
      (Storage.resetTransient tailTransientStorage).find tailTransientArray =
        tailTransientStorage.find tailTransientArray := ⟨rfl, rfl⟩

/-- Both the live element and transient value have clean tails. -/
theorem tail_transient_clean : tailTransientStorage.CleanTail := by
  simp only [Storage.CleanTail, tailTransientStorage, SFields.All_cons,
    SVal.All_array, cleanTailH, SList.ordinaryDefault_nil, SVec.All_cons,
    SVec.All_nil, SList.All_nil, SVal.All_prim, SFields.All_nil, and_self]

/-- Clean storage, a true transient root and its actual reset coexist. -/
theorem tail_reset_inputs_joint :
    ∃ (C : Contract) (st : Storage C) (r : SRef C (.prim .bool)),
      st.CleanTail ∧ st.find r = some (.prim true) ∧
      (Storage.resetTransient st).find r = some (.prim false) :=
  ⟨tailTransientContract, tailTransientStorage, tailTransientFlag,
    tail_transient_clean, rfl, rfl⟩

/-- The private input has clean storage and an observable transaction reset. -/
theorem tail_ofState_inputs_joint :
    ∃ (C : Contract) (Γ : Ctx) (σ : State C Γ) (r : SRef C (.prim .bool)),
      σ.storage.CleanTail ∧ σ.storage.find r = some (.prim true) ∧
      (World.ofState σ).storage.find r = some (.prim false) :=
  ⟨tailTransientContract, [],
    { State.init tailTransientContract with storage := tailTransientStorage },
    tailTransientFlag, tail_transient_clean, rfl, rfl⟩

/-- The whole universal interface law is accompanied by real constructor/call inputs. -/
theorem tail_invariant_inputs_joint :
    ∃ (C : Contract) (D A : Type) (M : System C D A) (_d : D) (a : A)
      (world : World C) (tx : TTx) (r : SRef C (.prim .bool)),
      ExposesNone M ∧ M.Init world ∧ world.accepts tx ∧
      M.allowCall world a tx ∧ M.refuses a tx = false ∧
      world.storage.find r = some (.prim false) ∧
      ∃ after, M.run world a tx = .ok after ∧ after.storage.find r = some (.prim true) :=
  ⟨bridgeContract, Unit, Unit, tailAuditSystem, (), (), tailAuditWorld,
    tailAuditTx, bridgeFlag, tail_audit_exposes, tail_audit_init,
    tail_audit_accepts, True.intro, rfl, tail_audit_write_success.1,
    tail_audit_write_success.2⟩

/-- ExposesNone and a genuine admitted reachable entry state hold together. -/
theorem tail_entry_inputs_joint :
    ∃ (C : Contract) (D A : Type) (M : System C D A) (σ : State C []),
      ExposesNone M ∧ EntryState M σ :=
  ⟨bridgeContract, Unit, Unit, tailAuditSystem, tailAuditEntry,
    tail_audit_exposes, tail_audit_entry⟩

/-- The selected clean-mode validity law coexists with an actual reachable entry. -/
theorem tail_validStart_inputs_joint :
    ∃ (C : Contract) (D A : Type) (M : System C D A) (φ : Fml C [])
      (σ : State C []), ExposesNone M ∧ ValidTail .clean φ ∧ EntryState M σ :=
  ⟨bridgeContract, Unit, Unit, tailAuditSystem, Fml.cleanTail bridgeContract,
    tailAuditEntry, tail_audit_exposes, (fun _ h => h), tail_audit_entry⟩

/-- A reject-all SOURCE interface is incompatible with the concrete successful write. -/
theorem tail_reject_all_refuted :
    ¬ (∀ (s : World bridgeContract) (a : Unit) (tx : TTx),
      tailAuditSystem.run s a tx = .error .revert) := by
  intro rejects
  obtain ⟨after, success, _⟩ := tail_audit_write_success.2
  have failure := rejects tailAuditWorld () tailAuditTx
  rw [success] at failure
  cases failure

#print axioms tail_audit_exposes
#print axioms tail_audit_init
#print axioms tail_audit_accepts
#print axioms tail_audit_entry
#print axioms tail_audit_write_success
#print axioms tail_anon_inputs_joint
#print axioms tail_transient_array_preserved
#print axioms tail_transient_clean
#print axioms tail_reset_inputs_joint
#print axioms tail_ofState_inputs_joint
#print axioms tail_invariant_inputs_joint
#print axioms tail_entry_inputs_joint
#print axioms tail_validStart_inputs_joint
#print axioms tail_reject_all_refuted
end H62.AuditTheories
