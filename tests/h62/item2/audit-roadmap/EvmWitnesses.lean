import Solidity.Roadmap.Evm

/-! Joint witnesses importing the unchanged dependency-light G06 interface. -/
namespace Solidity.H62.AuditRoadmap.EvmWitnesses
open Solidity.Roadmap.Evm

/-- Both precompile inputs and the exact equality hypothesis are inhabited
at once. The original theorem is applied at that same input. -/
theorem address_injective_joint :
    ∃ p q : Precompile, p.address = q.address ∧ p = q :=
  ⟨.identity, .identity, rfl, Precompile.address_injective rfl⟩

/-- Closed frozen statement; there are no premises to witness. -/
theorem pinned_eq_audit : pinned = { osaka with
    runtimeCodeLimit := none, initcodeLimit := none, txGasCap := none, blockGasLimited := false } := pinned_eq

theorem mem_all_joint : ∃ p : Precompile, p ∈ Precompile.all :=
  ⟨.p256Verify, Precompile.mem_all _⟩

theorem address_inverse_joint : ∃ p : Precompile,
    Precompile.ofAddress? p.address = some p :=
  ⟨.p256Verify, Precompile.ofAddress?_address _⟩

theorem address_bound_joint : ∃ p : Precompile,
    0 < p.address ∧ p.address < 2 ^ 160 :=
  ⟨.p256Verify, Precompile.address_pos_lt _⟩

private theorem singleton_collision_free : withKeccak.NoCollision [[]] := by
  intro a ha b hb _
  have ha0 : a = [] := List.mem_singleton.mp ha
  have hb0 : b = [] := List.mem_singleton.mp hb
  exact ha0.trans hb0.symm

/-- Nonempty per-run preimage list; both the collision premise and inclusion
hold for the same Fixed object and lists. -/
theorem collision_mono_joint : ∃ (F : Fixed) (hs hs' : List Bytes),
    F.NoCollision hs' ∧ (∀ x ∈ hs, x ∈ hs') ∧ F.NoCollision hs :=
  ⟨withKeccak, [[]], [[]], singleton_collision_free,
    (fun _ h => h), singleton_collision_free.mono (fun _ h => h)⟩

private theorem singleton_no_overlap : withKeccak.NoOverlap 1 0 [[]] := by
  constructor
  · intro a ha b hb hne _ _ _ _
    have ha0 : a = [] := List.mem_singleton.mp ha
    have hb0 : b = [] := List.mem_singleton.mp hb
    exact False.elim (hne (ha0.trans hb0.symm))
  · intro _ _ _ _ k hk
    exact False.elim (Nat.not_lt_zero k hk)

/-- Positive region length with a nonempty hashed list. Root interaction is
outside this particular witness (roots=0), and remains a separate coverage case. -/
theorem overlap_joint : ∃ (F : Fixed) (L roots : Nat) (hs : List Bytes),
    F.NoOverlap L roots hs ∧ 0 < L ∧ F.NoCollision hs :=
  ⟨withKeccak, 1, 0, [[]], singleton_no_overlap, Nat.zero_lt_succ 0,
    singleton_no_overlap.noCollision (Nat.zero_lt_succ 0)⟩

theorem creation_bound_joint : ∃ (F : Fixed) (sender nonce : Nat),
    F.createAddress sender nonce < 2 ^ 160 :=
  ⟨withKeccak, 0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0, 0,
    Fixed.createAddress_lt _ _ _⟩

def zeroSchedule : Schedule := ⟨fun _ => 0⟩
def resource (fuel : Nat) : GasRes := ⟨zeroSchedule, fuel⟩

theorem resource_refl_joint : ∃ a : GasRes, a ≤ a :=
  ⟨resource 1, GasRes.le_refl _⟩

theorem resource_trans_joint : ∃ a b c : GasRes, a ≤ b ∧ b ≤ c ∧ a ≤ c := by
  have hab : resource 1 ≤ resource 2 := ⟨rfl, by decide⟩
  have hbc : resource 2 ≤ resource 3 := ⟨rfl, by decide⟩
  exact ⟨resource 1, resource 2, resource 3, hab, hbc, GasRes.le_trans hab hbc⟩

theorem admissible_of_le_joint : ∃ (p : Pin) (a b : GasRes),
    a ≤ b ∧ GasRes.Admissible p a ∧ GasRes.Admissible p b := by
  have hab : resource 1 ≤ resource 2 := ⟨rfl, by decide⟩
  have ha : GasRes.Admissible osaka (resource 1) := fun _ _ _ => Nat.zero_le _
  exact ⟨osaka, resource 1, resource 2, hab, ha, GasRes.Admissible.of_le hab ha⟩

theorem admissible_pinned_joint : ∃ r : GasRes, GasRes.Admissible pinned r :=
  ⟨resource 1, GasRes.admissible_pinned _⟩

theorem exceptional_observation_audit :
    Halt.exceptional.observe = (Halt.revert []).observe := Halt.observe_exceptional

theorem success_observation_joint : ∃ (h : Halt) (d : Bytes),
    h.observe = (true, d) ∧ h = .success d :=
  ⟨.success [1], [1], rfl, Halt.observe_success.mp rfl⟩

/-- An explicitly illustrative, nonconstant certificate carrier. This is
not a real EVM implementation; it witnesses the generic certificate inputs. -/
def model : Pinned Nat Nat where
  pin := pinned
  fixed := withKeccak
  Env := Nat
  Res := Nat
  resLE := inferInstance
  Allowed e := e ≤ 10
  Admissible r := r ≤ 10
  sem a e r := a + e + r
  consistent a e _ _ h := Nat.add_le_add_left h (a + e)

def selfCertificate : Certificate model model := Certificate.refl Nat.le_refl model

theorem certificate_back_joint : ∃ (c : Certificate model model) (a e r : Nat),
    c.Specified a ∧ model.Allowed e ∧ model.Admissible r ∧
    ∃ r', model.Admissible r' ∧ model.sem a e r ≤ model.sem a (c.envMap e) r' :=
  ⟨selfCertificate, 7, 3, 2, True.intro, (by change 3 ≤ 10; decide), (by change 2 ≤ 10; decide),
    Certificate.back_le selfCertificate True.intro
      (by change 3 ≤ 10; decide) (by change 2 ≤ 10; decide)⟩

/-- Exact Osaka gas-cap boundary versus the explicitly idealized pin. No
claim about transaction intrinsic gas or production compiler totality. -/
theorem gas_cap_boundary :
    GasRes.Admissible osaka ⟨⟨fun _ => 2 ^ 24⟩, 1⟩ ∧
    ¬ GasRes.Admissible osaka ⟨⟨fun _ => 2 ^ 24 + 1⟩, 1⟩ ∧
    GasRes.Admissible pinned ⟨⟨fun _ => 2 ^ 24 + 1⟩, 1⟩ := by
  refine ⟨?_, ?_, GasRes.admissible_pinned _⟩
  · intro c hc _
    have heq : 2 ^ 24 = c := Option.some.inj hc
    exact Nat.le_of_eq heq
  · intro h
    have bad : 2 ^ 24 + 1 ≤ 2 ^ 24 := h (2 ^ 24) rfl 0
    exact (by decide : ¬ (2 ^ 24 + 1 ≤ 2 ^ 24)) bad

/-- Observable success/revert data remain distinct; exceptional failure and
empty revert intentionally coincide at the public frame observation. -/
theorem failure_observation_boundary :
    (Halt.success [1]).observe ≠ (Halt.revert [1]).observe ∧
    (Halt.revert [1]).observe ≠ Halt.exceptional.observe ∧
    (Halt.revert []).observe = Halt.exceptional.observe := by
  exact ⟨by decide, by decide, rfl⟩

/-- P-256 is explicitly Osaka's 0x100 precompile; the idealized pin retains
that fork and the actual call-depth and stack limits. -/
theorem fork_and_depth_boundary :
    pinned.fork = .osaka ∧ Precompile.ofAddress? 0x100 = some .p256Verify ∧
    pinned.callFails 1023 = false ∧ pinned.callFails 1024 = true ∧
    pinned.stackLimit = 1024 := by
  exact ⟨rfl, by decide, by decide, by decide, rfl⟩

end Solidity.H62.AuditRoadmap.EvmWitnesses
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.address_injective_joint
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.pinned_eq_audit
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.mem_all_joint
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.address_inverse_joint
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.address_bound_joint
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.collision_mono_joint
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.overlap_joint
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.creation_bound_joint
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.resource_refl_joint
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.resource_trans_joint
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.admissible_of_le_joint
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.admissible_pinned_joint
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.exceptional_observation_audit
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.success_observation_joint
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.certificate_back_joint
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.gas_cap_boundary
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.failure_observation_boundary
#print axioms Solidity.H62.AuditRoadmap.EvmWitnesses.fork_and_depth_boundary
