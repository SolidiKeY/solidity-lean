import SolidityBridge.RoadmapV15.P10.WrappingArithmeticWords
import SolidityBridge.RoadmapV15.P10.DecoderAgreement
import SolidityBridge.ExternalEvm.WordOps
import Solidity.Backend.Scalar.Comparisons

/-! G46.01 fetched EQ consumer of actual Scalar and pinned native definitions.
No source/compiler origin, gas adequacy for a whole run, or Osaka approval. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem equality_word (a b : Scalar.Word) :
    UInt256.eq ⟨a.toFin⟩ ⟨b.toFin⟩ = ⟨(Scalar.flag (a == b)).toFin⟩ := by
  have represented : (UInt256.mk a.toFin = UInt256.mk b.toFin) ↔ a = b := by
    constructor
    · intro same
      exact BitVec.eq_of_toFin_eq (congrArg UInt256.val same)
    · intro same
      exact congrArg (fun w : Scalar.Word => UInt256.mk w.toFin) same
  have test : decide (UInt256.mk a.toFin = UInt256.mk b.toFin) = (a == b) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,beq_iff_eq]
    exact represented
  rw [UInt256.eq,test]
  cases a == b <;> rfl

private theorem equality_gate (valid : Array UInt256) (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (enough : 2 ≤ s.stack.length)
    (room : s.stack.length-2+1 ≤ 1024) :
    Assembly.driverGate valid s .EQ = .ok (s,3) := by
  have expansion : EVM.memoryExpansionCost s .EQ = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  change (if s.gasAvailable.toNat < 3 then _ else _) = _
  rw [if_neg (Nat.not_lt_of_ge gas)]
  simp only [EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_of_ge enough),
    if_neg (Nat.not_lt_of_ge room)]
  cases s.executionEnv.perm <;> rfl

/-- Actual fetched EQ, preserving the complete charged State and continuation. -/
theorem equality_agreement (valid : Array UInt256) (site : Site .EQ)
    (a b : Scalar.Word) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (((Scalar.flag (a == b))::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .EQ) (a::b::tail) = some ((Scalar.flag (a == b))::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate valid input .EQ = .ok (input,3) := by
    apply equality_gate valid input gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.EQ,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        (((Scalar.flag (a == b))::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := equality_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.EQ,none) :=
    DecoderAgreement.decode_all (modularSite site (a::b::tail))
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel valid input input _ (.EQ,none) 3 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide)


/-- Consume the existing typed equality certificate without altering its types. -/
theorem selected_equality_agreement (valid : Array UInt256) (site : Site .EQ)
    (p : PrimTy) (a b : p.Denote) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let aw := Scalar.encodeValue p a
    let bw := Scalar.encodeValue p b
    let input := (modularSite site (aw::bw::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((Scalar.flag (aw == bw)::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.run (Scalar.scalarEq p).code (aw::bw::tail) =
      (BinOp.eqB.evalT (p := p) (by cases p <;> rfl) a b).map
        (fun result => Scalar.encodeValue .bool result::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  exact ⟨(Scalar.scalarEq p).correct a b tail,
    (equality_agreement valid site (Scalar.encodeValue p a) (Scalar.encodeValue p b)
      tail room gas fuel).2⟩

#print axioms equality_word
#print axioms equality_agreement
#print axioms selected_equality_agreement
end SolidityBridge.RoadmapV15.P10
