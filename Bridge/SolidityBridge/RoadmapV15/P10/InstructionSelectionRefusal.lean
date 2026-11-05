import SolidityBridge.RoadmapV15.P10.InstructionSelectionControls

/-! Failure consumers for the concrete published arithmetic certificates.
Reference gas precedes stack refusal; driver fuel precedes fetched execution.
An exceptional result carries no final State: no rollback/world conclusion is made. -/
namespace SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem short_scalar (words : Scalar.Stack) (short : words.length < 2) :
    Scalar.run InstructionSelectionAgreement.Cert.add.code words = none ∧
    Scalar.run InstructionSelectionAgreement.Cert.mul.code words = none := by
  first
  | solve | rfl
  | solve | decide
  | solve | omega
  | solve | simp only []
  | cases words with
    | nil => exact ⟨rfl,rfl⟩
    | cons a rest =>
      cases rest with
      | nil => exact ⟨rfl,rfl⟩
      | cons b tail => simp only [List.length_cons] at short; omega

private theorem short_gate (valid : Array UInt256) (s : EVM.State)
    (op : Operation .EVM) (cost : Nat) (allowed : op=.ADD ∨ op=.MUL)
    (chargeCost : EVM.C' s op=cost) (gas : cost≤s.gasAvailable.toNat)
    (short : s.stack.length<2) :
    Assembly.driverGate valid s op=.error .StackUnderflow := by
  first
  | solve | rfl
  | solve | decide
  | solve | omega
  | solve | simp only []
  | have expansion : EVM.memoryExpansionCost s op=0 := by
      rcases allowed with rfl|rfl <;>
        simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
    have delta : EVM.δ op=some 2 := by rcases allowed with rfl|rfl <;> rfl
    have charge : s.gasAvailable-UInt256.ofNat 0=s.gasAvailable := by
      change UInt256.mk (s.gasAvailable.val-0)=s.gasAvailable
      rw [sub_zero]
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [chargeCost,delta,Option.getD_some,if_neg (Nat.not_lt_zero _),
      if_neg (Nat.not_lt_of_ge gas),reduceCtorEq,if_false,if_pos short,bind,Except.bind,pure,Except.pure]

theorem add_refusal (valid : Array UInt256) (site : Site .ADD)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .add m=.fault ∧
    Scalar.run InstructionSelectionAgreement.Cert.add.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (short_scalar words short).1
  refine ⟨(InstructionSelectionAgreement.Cert.add.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := short_gate valid (modularSite site words).state .ADD 3 (Or.inl rfl) rfl gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem mul_refusal (valid : Array UInt256) (site : Site .MUL)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .mul m=.fault ∧
    Scalar.run InstructionSelectionAgreement.Cert.mul.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (short_scalar words short).2
  refine ⟨(InstructionSelectionAgreement.Cert.mul.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := short_gate valid (modularSite site words).state .MUL 5 (Or.inr rfl) rfl gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem add_native_refusal (valid : Array UInt256) (site : Site .ADD)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := short_gate valid (modularSite site words).state .ADD 3 (Or.inl rfl) rfl gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem mul_native_refusal (valid : Array UInt256) (site : Site .MUL)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := short_gate valid (modularSite site words).state .MUL 5 (Or.inr rfl) rfl gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

open WordPushFixtures (u spill)
theorem nonzero_client (perm : Bool) :
    let m := {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack [513]}
    Solidity.Evm.Instr.step .mul m=.fault ∧
    Scalar.run InstructionSelectionAgreement.Cert.mul.code [513]=none ∧
    Assembly.driverSteps 1 2 #[u 37,u 99]
      (modularSite (WrappingArithmeticFixtures.site .MUL 12 perm) [513]).state=.error .StackUnderflow := by
  exact mul_refusal _ _ _ _ rfl (by decide) (by change 5≤12;decide) 0

theorem priority_controls (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .ADD 2 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .MUL 12 perm [513])=.error .OutOfFuel ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .ADD 3 perm [])=.error .StackUnderflow := by
  first
  | solve | rfl
  | solve | decide
  | solve | omega
  | solve | simp only []
  | cases perm <;> exact ⟨rfl,rfl,rfl⟩

/-- Native X can reach its refusal gate at fuel one, unlike driverSteps. -/
theorem native_fuel_boundary (perm : Bool) :
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .MUL 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .MUL 12 perm) [513]).state=.error .OutOfFuel := by
  exact ⟨mul_native_refusal _ _ _ (by decide) (by change 5≤12;decide) 0,rfl⟩

#print axioms add_native_refusal
#print axioms mul_native_refusal
#print axioms native_fuel_boundary
#print axioms add_refusal
#print axioms mul_refusal
#print axioms nonzero_client
#print axioms priority_controls
end SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal
