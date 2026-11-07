import Solidity.Precompiles.PointEval

/-! Guards against counting the successful PointEval result law without a real
input satisfying its success premise. Infinity-point algebra avoids evaluating
a huge pairing exponent. No cryptographic equality axiom or compiler premise
is introduced. Success, gas price and malformed-length controls stay distinct. -/
namespace H62.AuditPrecompiles.Successor.PointEvalSuccess
open Solidity.Precompiles Solidity.Roadmap.Evm
open Solidity.Precompiles.Bls12381 (p r curve1 curve2 pairingCurve)

theorem one_mul_one : Fp12.mul 2 (p-2) (Fp12.one : Fp12 p) Fp12.one = Fp12.one := by
  decide +kernel

theorem pow_go_one (n e : Nat) :
    Fp12.pow.go 2 (p-2) n (Fp12.one : Fp12 p) e Fp12.one = Fp12.one := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
    simp only [Fp12.pow.go, one_mul_one]
    split
    · rfl
    · split <;> exact ih _

theorem pow_one (e : Nat) :
    Fp12.pow 2 (p-2) (Fp12.one : Fp12 p) e = Fp12.one :=
  pow_go_one _ _

theorem infinity_pairing (q t : Pt (Fp2 p)) :
    pairingCurve.check [(.inf,q),(.inf,t)] = true := by
  simp only [PairingCurve.check, List.foldl_cons, List.foldl_nil,
    PairingCurve.miller, PairingCurve.mul, pairingCurve, one_mul_one,
    PairingCurve.finalExp, pow_one, BEq.beq, decide_true]


theorem verifies_infinity (z : Nat) : PointEval.verifies ⟨z,0,.inf,.inf⟩ = true := by
  have hzero : curve1.mul ((r-0)%r) PointEval.g1Gen = .inf := by
    rw [Nat.sub_zero, Nat.mod_self]
    rfl
  unfold PointEval.verifies
  rw [hzero]
  change pairingCurve.check [(.inf, _),(.inf, _)] = true
  exact infinity_pairing _ _

def successInput : Bytes := ofHex "010657f37554c781402a22917dee2f75def7ab966d7b770905398eba3c44401400000000000000000000000000000000000000000000000000000000075bcd150000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"

deriving instance DecidableEq for PointEval.Inputs


theorem decoded_success : PointEval.decode successInput = some ⟨123456789,0,.inf,.inf⟩ := by
  unfold PointEval.decode
  decide +kernel


theorem pointEval_of_decode (d : Bytes) (i : PointEval.Inputs)
    (hd : PointEval.decode d = some i) (hv : PointEval.verifies i = true) :
    PointEval.pointEval d = some (word PointEval.fieldElementsPerBlob ++ word r) := by
  have hn : PointEval.pointEval d ≠ none := by
    intro h
    rcases (PointEval.pointEval_eq_none_iff d).mp h with hnone | ⟨j,hj,hbad⟩
    · rw [hd] at hnone
      cases hnone
    · have hij : i = j := Option.some.inj (hd.symm.trans hj)
      subst j
      rw [hv] at hbad
      cases hbad
  rcases Option.isSome_iff_exists.mp (Option.isSome_iff_ne_none.mpr hn) with ⟨o,ho⟩
  have out := PointEval.pointEval_result ho
  rw [out] at ho
  exact ho

theorem actual_success : PointEval.pointEval successInput =
    some (word PointEval.fieldElementsPerBlob ++ word r) :=
  pointEval_of_decode successInput ⟨123456789,0,.inf,.inf⟩ decoded_success
    (verifies_infinity 123456789)

theorem pointEval_result_joint : ∃ d o : Bytes,
    PointEval.pointEval d = some o ∧ o = word PointEval.fieldElementsPerBlob ++ word r :=
  ⟨successInput, word PointEval.fieldElementsPerBlob ++ word r, actual_success,
    @PointEval.pointEval_result successInput
      (word PointEval.fieldElementsPerBlob ++ word r) actual_success⟩

theorem success_price : PointEval.gas successInput = 50000 := rfl

theorem malformed_control : PointEval.pointEval [1] = none :=
  PointEval.pointEval_length (by decide)

/-- info: 'H62.AuditPrecompiles.Successor.PointEvalSuccess.one_mul_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms one_mul_one
/-- info: 'H62.AuditPrecompiles.Successor.PointEvalSuccess.pow_go_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pow_go_one
/-- info: 'H62.AuditPrecompiles.Successor.PointEvalSuccess.pow_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pow_one
/-- info: 'H62.AuditPrecompiles.Successor.PointEvalSuccess.infinity_pairing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms infinity_pairing
/-- info: 'H62.AuditPrecompiles.Successor.PointEvalSuccess.verifies_infinity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms verifies_infinity
/-- info: 'H62.AuditPrecompiles.Successor.PointEvalSuccess.decoded_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms decoded_success
/-- info: 'H62.AuditPrecompiles.Successor.PointEvalSuccess.pointEval_of_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pointEval_of_decode
/-- info: 'H62.AuditPrecompiles.Successor.PointEvalSuccess.actual_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms actual_success
/-- info: 'H62.AuditPrecompiles.Successor.PointEvalSuccess.pointEval_result_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pointEval_result_joint
/-- info: 'H62.AuditPrecompiles.Successor.PointEvalSuccess.success_price' does not depend on any axioms -/
#guard_msgs in
#print axioms success_price
/-- info: 'H62.AuditPrecompiles.Successor.PointEvalSuccess.malformed_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms malformed_control
#check pointEval_result_joint
end H62.AuditPrecompiles.Successor.PointEvalSuccess
