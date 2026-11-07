import Solidity.Theory.Mutability.Assignable
import tests.h62.item2.«audit-theories».CloserWitnesses

/-!
Joint input packets for all eight original Assignable interfaces. Actual named
storage roots make frame predicates observable. The modifies-set/check packets
use a real successful write to flag, a nonempty modifies set, and a separately
observed unchanged array root. Read-only packets use a nonempty bool declaration.
-/
namespace H62.AuditTheories
open Solidity
open Solidity.Theory.Mutability

/-- Concrete populated starting storage, not an empty contract. -/
def assignableStart : State bridgeContract [] :=
  {(State.init bridgeContract) with storage := bridgeStorage}
/-- A real storage write: `flag = true;`. -/
def assignableWrite : Prog bridgeContract [] [] :=
  .cons (.assign (.root "flag" rfl) (.val (.simple (.bool true)))) .nil

/-- The written root changes from false to true, and another live root survives. -/
theorem assignable_write_success :
    assignableStart.storage.find bridgeFlag = some (.prim false) ∧
      ∃ o, Prog.run assignableStart assignableWrite = .ok o ∧
        o.st.storage.find bridgeFlag = some (.prim true) ∧
        o.st.storage.find bridgeArray = assignableStart.storage.find bridgeArray :=
  ⟨rfl, _, rfl, rfl, rfl⟩

/-- A write cannot pass the empty-clause check via a read-only shortcut. -/
theorem assignable_empty_clause_refuses :
    Prog.within .view assignableWrite = false ∧
      assignableCheck assignableWrite [] = false := ⟨rfl, rfl⟩

/-- A real root exists together with the full empty-clause frame premise. -/
theorem assignable_nothing_joint_witness :
    ∃ (C : Contract) (Γ Δ : Ctx) (σ : State C Γ) (τ : State C Δ)
      (U : Ty) (r : SRef C U), Frames [] σ τ ∧ τ.storage.find r = σ.storage.find r :=
  ⟨bridgeContract, [], [], assignableStart, assignableStart, .prim .bool, bridgeFlag,
    ⟨(fun _ _ => rfl), rfl, rfl⟩, rfl⟩

/-- Nonempty nested clauses coexist with their entire universal subset law. -/
theorem assignable_mono_joint_witness :
    ∃ (C : Contract) (Γ Δ : Ctx) (L M : List Name)
      (σ : State C Γ) (τ : State C Δ),
      (∀ r ∈ L, r ∈ M) ∧ Frames L σ τ :=
  ⟨bridgeContract, [], [], ["flag"], ["items", "flag"], assignableStart, assignableStart,
    (fun _ hr => List.mem_cons_of_mem "items" hr), ⟨(fun _ _ => rfl), rfl, rfl⟩⟩

/-- Compatible states, clause and unchanged globals share one populated state. -/
theorem assignable_globals_joint_witness :
    ∃ (C : Contract) (Γ Δ : Ctx) (L : List Name)
      (σ : State C Γ) (τ : State C Δ), globals τ = globals σ ∧ Frames L σ τ :=
  ⟨bridgeContract, [], [], ["flag"], assignableStart, assignableStart, rfl, ⟨(fun _ _ => rfl), rfl, rfl⟩⟩

/-- Mutability and success premises coexist for a real local declaration. -/
theorem assignable_readonly_joint_witness :
    ∃ (C : Contract) (μ : Mutability) (Γ Γ' : Ctx) (P : Prog C Γ Γ')
      (L : List Name) (σ : State C Γ) (o : Out C σ.H Γ'),
      Prog.within μ P = true ∧ μ ≠ .nonpayable ∧ Prog.run σ P = .ok o ∧ Frames L σ o.st := by
  obtain ⟨o, hr, _⟩ := CompilerAudit.bool_source_success bridgeContract true assignableStart
  exact ⟨bridgeContract, .view, [], [.val .bool], CompilerAudit.boolProgram bridgeContract true,
    [], assignableStart, o, rfl, by decide, hr,
    Solidity.Theory.Mutability.Prog.frames_readOnly (μ := .view) rfl (by decide) [] hr⟩

/-- The late root/type binders remain correlated with every read-only premise. -/
theorem assignable_storage_joint_witness :
    ∃ (C : Contract) (μ : Mutability) (Γ Γ' : Ctx) (P : Prog C Γ Γ')
      (σ : State C Γ) (o : Out C σ.H Γ') (U : Ty) (r : SRef C U),
      Prog.within μ P = true ∧ μ ≠ .nonpayable ∧ Prog.run σ P = .ok o ∧
        o.st.storage.find r = σ.storage.find r := by
  obtain ⟨o, hr, _⟩ := CompilerAudit.bool_source_success bridgeContract true assignableStart
  exact ⟨bridgeContract, .view, [], [.val .bool], CompilerAudit.boolProgram bridgeContract true,
    assignableStart, o, .prim .bool, bridgeFlag, rfl, by decide, hr,
    Solidity.Theory.Mutability.Prog.storage_readOnly (μ := .view) rfl (by decide) hr bridgeFlag⟩

/-- An actual writing run satisfies the nonempty modifies set and full inclusion. -/
theorem assignable_store_joint_witness :
    ∃ (C : Contract) (Γ Γ' : Ctx) (P : Prog C Γ Γ') (M L : List Name)
      (σ : State C Γ) (o : Out C σ.H Γ'),
      Prog.storeAt P = some M ∧ (∀ r ∈ M, r ∈ L) ∧ Prog.run σ P = .ok o := by
  obtain ⟨_, o, hr, _, _⟩ := assignable_write_success
  exact ⟨bridgeContract, [], [], assignableWrite, ["flag"], ["flag"], assignableStart,
    o, rfl, (fun _ hr => hr), hr⟩

/-- The check succeeds through its modifies branch alongside an actual write. -/
theorem assignable_check_joint_witness :
    ∃ (C : Contract) (Γ Γ' : Ctx) (P : Prog C Γ Γ') (locs : List SpecLoc)
      (σ : State C Γ) (o : Out C σ.H Γ'),
      assignableCheck P locs = true ∧ Prog.run σ P = .ok o := by
  obtain ⟨_, o, hr, _, _⟩ := assignable_write_success
  exact ⟨bridgeContract, [], [], assignableWrite, [.root "flag"], assignableStart, o, rfl, hr⟩

/-- Outcome framing is not audited only on a reverting run: this write succeeds. -/
theorem assignable_committed_joint_witness :
    ∃ (C : Contract) (Γ Γ' : Ctx) (P : Prog C Γ Γ') (locs : List SpecLoc)
      (σ : State C Γ), assignableCheck P locs = true ∧ ∃ o, Prog.run σ P = .ok o := by
  obtain ⟨_, o, hr, _, _⟩ := assignable_write_success
  exact ⟨bridgeContract, [], [], assignableWrite, [.root "flag"], assignableStart, rfl, o, hr⟩

#print axioms assignable_write_success
#print axioms assignable_empty_clause_refuses
#print axioms assignable_nothing_joint_witness
#print axioms assignable_mono_joint_witness
#print axioms assignable_globals_joint_witness
#print axioms assignable_readonly_joint_witness
#print axioms assignable_storage_joint_witness
#print axioms assignable_store_joint_witness
#print axioms assignable_check_joint_witness
#print axioms assignable_committed_joint_witness
end H62.AuditTheories
