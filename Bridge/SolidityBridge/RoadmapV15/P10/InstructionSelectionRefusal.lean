import SolidityBridge.RoadmapV15.P10.StackFamilyConsumer
import Solidity.Backend.Selection.StackSelection
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
private theorem signed_short_scalar (words : Scalar.Stack) (short : words.length < 2) :
    Scalar.run Selection.sdivCertificate.code words = none ∧
    Scalar.run Selection.smodCertificate.code words = none := by
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

private theorem signed_short_gate (valid : Array UInt256) (s : EVM.State)
    (op : Operation .EVM) (cost : Nat) (allowed : op=.SDIV ∨ op=.SMOD)
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

theorem sdiv_refusal (valid : Array UInt256) (site : Site .SDIV)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .sdiv m=.fault ∧
    Scalar.run Selection.sdivCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (signed_short_scalar words short).1
  refine ⟨(Selection.sdivCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := signed_short_gate valid (modularSite site words).state .SDIV 5 (Or.inl rfl) rfl gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem sdiv_native_refusal (valid : Array UInt256) (site : Site .SDIV)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := signed_short_gate valid (modularSite site words).state .SDIV 5 (Or.inl rfl) rfl gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem smod_refusal (valid : Array UInt256) (site : Site .SMOD)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .smod m=.fault ∧
    Scalar.run Selection.smodCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (signed_short_scalar words short).2
  refine ⟨(Selection.smodCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := signed_short_gate valid (modularSite site words).state .SMOD 5 (Or.inr rfl) rfl gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem smod_native_refusal (valid : Array UInt256) (site : Site .SMOD)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := signed_short_gate valid (modularSite site words).state .SMOD 5 (Or.inr rfl) rfl gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem signed_nonzero_clients (perm : Bool) :
    let m := {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack [513]}
    (Solidity.Evm.Instr.step .sdiv m=.fault ∧
      Scalar.run Selection.sdivCertificate.code [513]=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .SDIV 12 perm) [513]).state=.error .StackUnderflow) ∧
    (Solidity.Evm.Instr.step .smod m=.fault ∧
      Scalar.run Selection.smodCertificate.code [513]=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .SMOD 12 perm) [513]).state=.error .StackUnderflow) := by
  exact ⟨sdiv_refusal _ _ _ _ rfl (by decide) (by change 5≤12;decide) 0,
    smod_refusal _ _ _ _ rfl (by decide) (by change 5≤12;decide) 0⟩

theorem signed_priority_controls (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SDIV 4 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SMOD 4 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SDIV 4 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SMOD 4 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SDIV 5 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SMOD 5 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .SDIV 0 perm [])=.error .OutOfFuel ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .SMOD 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem signed_native_fuel_boundary (perm : Bool) :
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .SDIV 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .SDIV 12 perm) [513]).state=.error .OutOfFuel ∧
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .SMOD 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .SMOD 12 perm) [513]).state=.error .OutOfFuel := by
  exact ⟨sdiv_native_refusal _ _ _ (by decide) (by change 5≤12;decide) 0,rfl,
    smod_native_refusal _ _ _ (by decide) (by change 5≤12;decide) 0,rfl⟩

theorem signed_input_observation (perm : Bool) :
    let input := WrappingArithmeticFixtures.input .SDIV 12 perm [513]
    input.stack=[u 513] ∧ input.executionEnv.perm=perm ∧
    input.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x05,0] ∧
    input.pc=u 3 ∧ input.gasAvailable=u 12 ∧ input.execLength=41 ∧
    input.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    input.returnData.data.toList=[0xcc,0xdd] ∧ input.H_return.data.toList=[0xee,0xff] ∧
    input.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    input.accountMap=WordPushFixtures.accounts ∧ input.σ₀=WordPushFixtures.accounts := by
  first | rfl | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.sdiv_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sdiv_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.smod_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms smod_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.sdiv_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sdiv_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.smod_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms smod_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.signed_nonzero_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms signed_nonzero_clients
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.signed_priority_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms signed_priority_controls
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.signed_native_fuel_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms signed_native_fuel_boundary
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.signed_input_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms signed_input_observation
private theorem unsigned_short_scalar (words : Scalar.Stack) (short : words.length < 2) :
    Scalar.run Selection.divCertificate.code words = none ∧
    Scalar.run Selection.modCertificate.code words = none := by
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

private theorem unsigned_short_gate (valid : Array UInt256) (s : EVM.State)
    (op : Operation .EVM) (allowed : op=.DIV ∨ op=.MOD)
    (gas : 5≤s.gasAvailable.toNat) (short : s.stack.length<2) :
    Assembly.driverGate valid s op=.error .StackUnderflow := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | rcases allowed with rfl|rfl
    · exact signed_short_gate valid s .SDIV 5 (Or.inl rfl) rfl gas short
    · exact signed_short_gate valid s .SMOD 5 (Or.inr rfl) rfl gas short

theorem div_refusal (valid : Array UInt256) (site : Site .DIV)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .div m=.fault ∧
    Scalar.run Selection.divCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (unsigned_short_scalar words short).1
  refine ⟨(Selection.divCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := unsigned_short_gate valid (modularSite site words).state .DIV (Or.inl rfl) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem div_native_refusal (valid : Array UInt256) (site : Site .DIV)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := unsigned_short_gate valid (modularSite site words).state .DIV (Or.inl rfl) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem mod_refusal (valid : Array UInt256) (site : Site .MOD)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .mod m=.fault ∧
    Scalar.run Selection.modCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (unsigned_short_scalar words short).2
  refine ⟨(Selection.modCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := unsigned_short_gate valid (modularSite site words).state .MOD (Or.inr rfl) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem mod_native_refusal (valid : Array UInt256) (site : Site .MOD)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := unsigned_short_gate valid (modularSite site words).state .MOD (Or.inr rfl) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem unsigned_nonzero_clients (perm : Bool) :
    let m := {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack [513]}
    (Solidity.Evm.Instr.step .div m=.fault ∧
      Scalar.run Selection.divCertificate.code [513]=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .DIV 12 perm) [513]).state=.error .StackUnderflow) ∧
    (Solidity.Evm.Instr.step .mod m=.fault ∧
      Scalar.run Selection.modCertificate.code [513]=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .MOD 12 perm) [513]).state=.error .StackUnderflow) := by
  exact ⟨div_refusal _ _ _ _ rfl (by decide) (by change 5≤12;decide) 0,
    mod_refusal _ _ _ _ rfl (by decide) (by change 5≤12;decide) 0⟩

theorem unsigned_priority_controls (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .DIV 4 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .MOD 4 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .DIV 4 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .MOD 4 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .DIV 5 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .MOD 5 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .DIV 0 perm [])=.error .OutOfFuel ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .MOD 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem unsigned_native_fuel_boundary (perm : Bool) :
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .DIV 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .DIV 12 perm) [513]).state=.error .OutOfFuel ∧
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .MOD 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .MOD 12 perm) [513]).state=.error .OutOfFuel := by
  exact ⟨div_native_refusal _ _ _ (by decide) (by change 5≤12;decide) 0,rfl,
    mod_native_refusal _ _ _ (by decide) (by change 5≤12;decide) 0,rfl⟩

theorem unsigned_input_observation (perm : Bool) :
    let input := WrappingArithmeticFixtures.input .DIV 12 perm [513]
    input.stack=[u 513] ∧ input.executionEnv.perm=perm ∧
    input.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x04,0] ∧
    input.pc=u 3 ∧ input.gasAvailable=u 12 ∧ input.execLength=41 ∧
    input.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    input.returnData.data.toList=[0xcc,0xdd] ∧ input.H_return.data.toList=[0xee,0xff] ∧
    input.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    input.accountMap=WordPushFixtures.accounts ∧ input.σ₀=WordPushFixtures.accounts := by
  first | rfl | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.div_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms div_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.mod_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mod_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.div_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms div_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.mod_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mod_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.unsigned_nonzero_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms unsigned_nonzero_clients
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.unsigned_priority_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms unsigned_priority_controls
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.unsigned_native_fuel_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms unsigned_native_fuel_boundary
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.unsigned_input_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms unsigned_input_observation
private theorem unary_short_scalar (words : Scalar.Stack) (short : words.length<1) :
    Scalar.run Selection.notCertificate.code words=none ∧
    Scalar.run Selection.iszeroCertificate.code words=none := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | cases words with
    | nil => exact ⟨rfl,rfl⟩
    | cons a tail => simp only [List.length_cons] at short;omega

private theorem unary_short_gate (valid : Array UInt256) (s : EVM.State)
    (op : Operation .EVM) (cost : Nat) (allowed : op=.NOT ∨ op=.ISZERO)
    (chargeCost : EVM.C' s op=cost) (gas : cost≤s.gasAvailable.toNat)
    (short : s.stack.length<1) :
    Assembly.driverGate valid s op=.error .StackUnderflow := by
  first
  | solve | rfl
  | solve | decide
  | solve | omega
  | solve | simp only []
  | have expansion : EVM.memoryExpansionCost s op=0 := by
      rcases allowed with rfl|rfl <;>
        simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
    have delta : EVM.δ op=some 1 := by rcases allowed with rfl|rfl <;> rfl
    have charge : s.gasAvailable-UInt256.ofNat 0=s.gasAvailable := by
      change UInt256.mk (s.gasAvailable.val-0)=s.gasAvailable
      rw [sub_zero]
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [chargeCost,delta,Option.getD_some,if_neg (Nat.not_lt_zero _),
      if_neg (Nat.not_lt_of_ge gas),reduceCtorEq,if_false,if_pos short,bind,Except.bind,pure,Except.pure]

theorem not_refusal (valid : Array UInt256) (site : Site .NOT)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<1)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .not m=.fault ∧
    Scalar.run Selection.notCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (unary_short_scalar words short).1
  refine ⟨(Selection.notCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := unary_short_gate valid (modularSite site words).state .NOT 3 (Or.inl rfl) rfl gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem not_native_refusal (valid : Array UInt256) (site : Site .NOT)
    (words : Scalar.Stack) (short : words.length<1)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := unary_short_gate valid (modularSite site words).state .NOT 3 (Or.inl rfl) rfl gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem iszero_refusal (valid : Array UInt256) (site : Site .ISZERO)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<1)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .iszero m=.fault ∧
    Scalar.run Selection.iszeroCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (unary_short_scalar words short).2
  refine ⟨(Selection.iszeroCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := unary_short_gate valid (modularSite site words).state .ISZERO 3 (Or.inr rfl) rfl gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem iszero_native_refusal (valid : Array UInt256) (site : Site .ISZERO)
    (words : Scalar.Stack) (short : words.length<1)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := unary_short_gate valid (modularSite site words).state .ISZERO 3 (Or.inr rfl) rfl gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem unary_empty_clients (perm : Bool) :
    let m := {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack []}
    (Solidity.Evm.Instr.step .not m=.fault ∧
      Scalar.run Selection.notCertificate.code []=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .NOT 12 perm) []).state=.error .StackUnderflow) ∧
    (Solidity.Evm.Instr.step .iszero m=.fault ∧
      Scalar.run Selection.iszeroCertificate.code []=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .ISZERO 12 perm) []).state=.error .StackUnderflow) := by
  exact ⟨not_refusal _ _ _ _ rfl (by decide) (by change 3≤12;decide) 0,
    iszero_refusal _ _ _ _ rfl (by decide) (by change 3≤12;decide) 0⟩

theorem unary_priority_controls (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .NOT 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .ISZERO 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .NOT 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .ISZERO 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .NOT 0 perm [])=.error .OutOfFuel ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .ISZERO 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem unary_native_fuel_boundary (perm : Bool) :
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .NOT 12 perm) []).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .NOT 12 perm) []).state=.error .OutOfFuel ∧
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .ISZERO 12 perm) []).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .ISZERO 12 perm) []).state=.error .OutOfFuel := by
  exact ⟨not_native_refusal _ _ _ (by decide) (by change 3≤12;decide) 0,rfl,
    iszero_native_refusal _ _ _ (by decide) (by change 3≤12;decide) 0,rfl⟩

theorem unary_input_observation (perm : Bool) :
    let input := WrappingArithmeticFixtures.input .NOT 12 perm []
    input.stack=[] ∧ input.executionEnv.perm=perm ∧
    input.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x19,0] ∧
    input.pc=u 3 ∧ input.gasAvailable=u 12 ∧ input.execLength=41 ∧
    input.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    input.returnData.data.toList=[0xcc,0xdd] ∧ input.H_return.data.toList=[0xee,0xff] ∧
    input.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    input.accountMap=WordPushFixtures.accounts ∧ input.σ₀=WordPushFixtures.accounts := by
  first | rfl | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.not_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms not_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.iszero_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms iszero_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.not_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms not_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.iszero_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms iszero_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.unary_empty_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms unary_empty_clients
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.unary_priority_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms unary_priority_controls
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.unary_native_fuel_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms unary_native_fuel_boundary
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.unary_input_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms unary_input_observation
private theorem shift_short_scalar (words : Scalar.Stack) (short : words.length < 2) :
    Scalar.run Selection.shlCertificate.code words = none ∧
    Scalar.run Selection.shrCertificate.code words = none := by
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

private theorem shift_short_gate (valid : Array UInt256) (s : EVM.State)
    (op : Operation .EVM) (allowed : op=.SHL ∨ op=.SHR)
    (gas : 3≤s.gasAvailable.toNat) (short : s.stack.length<2) :
    Assembly.driverGate valid s op=.error .StackUnderflow := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | rcases allowed with rfl|rfl
    · exact short_gate valid s .ADD 3 (Or.inl rfl) rfl gas short
    · exact short_gate valid s .ADD 3 (Or.inl rfl) rfl gas short

theorem shl_refusal (valid : Array UInt256) (site : Site .SHL)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .shl m=.fault ∧
    Scalar.run Selection.shlCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (shift_short_scalar words short).1
  refine ⟨(Selection.shlCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := shift_short_gate valid (modularSite site words).state .SHL (Or.inl rfl) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem shl_native_refusal (valid : Array UInt256) (site : Site .SHL)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := shift_short_gate valid (modularSite site words).state .SHL (Or.inl rfl) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem shr_refusal (valid : Array UInt256) (site : Site .SHR)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .shr m=.fault ∧
    Scalar.run Selection.shrCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (shift_short_scalar words short).2
  refine ⟨(Selection.shrCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := shift_short_gate valid (modularSite site words).state .SHR (Or.inr rfl) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem shr_native_refusal (valid : Array UInt256) (site : Site .SHR)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := shift_short_gate valid (modularSite site words).state .SHR (Or.inr rfl) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem shift_nonzero_clients (perm : Bool) :
    let m := {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack [513]}
    (Solidity.Evm.Instr.step .shl m=.fault ∧
      Scalar.run Selection.shlCertificate.code [513]=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .SHL 12 perm) [513]).state=.error .StackUnderflow) ∧
    (Solidity.Evm.Instr.step .shr m=.fault ∧
      Scalar.run Selection.shrCertificate.code [513]=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .SHR 12 perm) [513]).state=.error .StackUnderflow) := by
  exact ⟨shl_refusal _ _ _ _ rfl (by decide) (by change 3≤12;decide) 0,
    shr_refusal _ _ _ _ rfl (by decide) (by change 3≤12;decide) 0⟩

theorem shift_priority_controls (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SHL 2 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SHR 2 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SHL 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SHR 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SHL 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SHR 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .SHL 0 perm [])=.error .OutOfFuel ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .SHR 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem shift_native_fuel_boundary (perm : Bool) :
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .SHL 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .SHL 12 perm) [513]).state=.error .OutOfFuel ∧
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .SHR 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .SHR 12 perm) [513]).state=.error .OutOfFuel := by
  exact ⟨shl_native_refusal _ _ _ (by decide) (by change 3≤12;decide) 0,rfl,
    shr_native_refusal _ _ _ (by decide) (by change 3≤12;decide) 0,rfl⟩

theorem shift_input_observation (perm : Bool) :
    let input := WrappingArithmeticFixtures.input .SHL 12 perm [513]
    input.stack=[u 513] ∧ input.executionEnv.perm=perm ∧
    input.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x1b,0] ∧
    input.pc=u 3 ∧ input.gasAvailable=u 12 ∧ input.execLength=41 ∧
    input.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    input.returnData.data.toList=[0xcc,0xdd] ∧ input.H_return.data.toList=[0xee,0xff] ∧
    input.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    input.accountMap=WordPushFixtures.accounts ∧ input.σ₀=WordPushFixtures.accounts := by
  first | rfl | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.shl_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shl_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.shr_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shr_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.shl_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shl_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.shr_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shr_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.shift_nonzero_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shift_nonzero_clients
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.shift_priority_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shift_priority_controls
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.shift_native_fuel_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shift_native_fuel_boundary
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.shift_input_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shift_input_observation
private theorem bitwise_short_scalar (words : Scalar.Stack) (short : words.length<2) :
    Scalar.run Selection.andCertificate.code words=none ∧
    Scalar.run Selection.orCertificate.code words=none ∧
    Scalar.run Selection.xorCertificate.code words=none := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | cases words with
    | nil => exact ⟨rfl,rfl,rfl⟩
    | cons a rest =>
      cases rest with
      | nil => exact ⟨rfl,rfl,rfl⟩
      | cons b tail => simp only [List.length_cons] at short;omega

private theorem bitwise_short_gate (valid : Array UInt256) (s : EVM.State)
    (op : Operation .EVM) (allowed : op=.AND ∨ op=.OR ∨ op=.XOR)
    (gas : 3≤s.gasAvailable.toNat) (short : s.stack.length<2) :
    Assembly.driverGate valid s op=.error .StackUnderflow := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | rcases allowed with rfl|rfl|rfl
    · exact short_gate valid s .ADD 3 (Or.inl rfl) rfl gas short
    · exact short_gate valid s .ADD 3 (Or.inl rfl) rfl gas short
    · exact short_gate valid s .ADD 3 (Or.inl rfl) rfl gas short

theorem and_refusal (valid : Array UInt256) (site : Site .AND)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .and m=.fault ∧
    Scalar.run Selection.andCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (bitwise_short_scalar words short).1
  refine ⟨(Selection.andCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := bitwise_short_gate valid (modularSite site words).state .AND (Or.inl rfl) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem and_native_refusal (valid : Array UInt256) (site : Site .AND)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := bitwise_short_gate valid (modularSite site words).state .AND (Or.inl rfl) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem or_refusal (valid : Array UInt256) (site : Site .OR)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .or m=.fault ∧
    Scalar.run Selection.orCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (bitwise_short_scalar words short).2.1
  refine ⟨(Selection.orCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := bitwise_short_gate valid (modularSite site words).state .OR (Or.inr (Or.inl rfl)) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem or_native_refusal (valid : Array UInt256) (site : Site .OR)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := bitwise_short_gate valid (modularSite site words).state .OR (Or.inr (Or.inl rfl)) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem xor_refusal (valid : Array UInt256) (site : Site .XOR)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .xor m=.fault ∧
    Scalar.run Selection.xorCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (bitwise_short_scalar words short).2.2
  refine ⟨(Selection.xorCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := bitwise_short_gate valid (modularSite site words).state .XOR (Or.inr (Or.inr rfl)) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem xor_native_refusal (valid : Array UInt256) (site : Site .XOR)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := bitwise_short_gate valid (modularSite site words).state .XOR (Or.inr (Or.inr rfl)) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem bitwise_nonzero_clients (perm : Bool) :
    let m := {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack [513]}
    (Solidity.Evm.Instr.step .and m=.fault ∧
      Scalar.run Selection.andCertificate.code [513]=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .AND 12 perm) [513]).state=.error .StackUnderflow) ∧
    (Solidity.Evm.Instr.step .or m=.fault ∧
      Scalar.run Selection.orCertificate.code [513]=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .OR 12 perm) [513]).state=.error .StackUnderflow) ∧
    (Solidity.Evm.Instr.step .xor m=.fault ∧
      Scalar.run Selection.xorCertificate.code [513]=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .XOR 12 perm) [513]).state=.error .StackUnderflow) := by
  exact ⟨and_refusal _ _ _ _ rfl (by decide) (by change 3≤12;decide) 0,
    or_refusal _ _ _ _ rfl (by decide) (by change 3≤12;decide) 0,
    xor_refusal _ _ _ _ rfl (by decide) (by change 3≤12;decide) 0⟩

theorem bitwise_priority_controls (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .AND 2 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .OR 2 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .XOR 2 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .AND 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .OR 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .XOR 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .AND 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .OR 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .XOR 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .AND 0 perm [])=.error .OutOfFuel ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .OR 0 perm [])=.error .OutOfFuel ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .XOR 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem bitwise_native_fuel_boundary (perm : Bool) :
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .AND 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .AND 12 perm) [513]).state=.error .OutOfFuel ∧
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .OR 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .OR 12 perm) [513]).state=.error .OutOfFuel ∧
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .XOR 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .XOR 12 perm) [513]).state=.error .OutOfFuel := by
  exact ⟨and_native_refusal _ _ _ (by decide) (by change 3≤12;decide) 0,rfl,or_native_refusal _ _ _ (by decide) (by change 3≤12;decide) 0,rfl,xor_native_refusal _ _ _ (by decide) (by change 3≤12;decide) 0,rfl⟩

theorem bitwise_input_observation (perm : Bool) :
    let input := WrappingArithmeticFixtures.input .XOR 12 perm [513]
    input.stack=[u 513] ∧ input.executionEnv.perm=perm ∧
    input.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x18,0] ∧
    input.pc=u 3 ∧ input.gasAvailable=u 12 ∧ input.execLength=41 ∧
    input.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    input.returnData.data.toList=[0xcc,0xdd] ∧ input.H_return.data.toList=[0xee,0xff] ∧
    input.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    input.accountMap=WordPushFixtures.accounts ∧ input.σ₀=WordPushFixtures.accounts := by
  first | rfl | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.and_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms and_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.or_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms or_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.xor_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms xor_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.and_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms and_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.or_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms or_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.xor_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms xor_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.bitwise_nonzero_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bitwise_nonzero_clients
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.bitwise_priority_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bitwise_priority_controls
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.bitwise_native_fuel_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bitwise_native_fuel_boundary
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.bitwise_input_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bitwise_input_observation
private theorem comparison_short_scalar (words : Scalar.Stack) (short : words.length<2) :
    Scalar.run Selection.ltCertificate.code words=none ∧
    Scalar.run Selection.gtCertificate.code words=none ∧
    Scalar.run Selection.eqCertificate.code words=none ∧
    Scalar.run Selection.sltCertificate.code words=none ∧
    Scalar.run Selection.sgtCertificate.code words=none := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | cases words with
    | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
    | cons a rest =>
      cases rest with
      | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
      | cons b tail => simp only [List.length_cons] at short;omega

private theorem comparison_short_gate (valid : Array UInt256) (s : EVM.State)
    (op : Operation .EVM) (allowed : op=.LT ∨ op=.GT ∨ op=.EQ ∨ op=.SLT ∨ op=.SGT)
    (gas : 3≤s.gasAvailable.toNat) (short : s.stack.length<2) :
    Assembly.driverGate valid s op=.error .StackUnderflow := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | rcases allowed with rfl|rfl|rfl|rfl|rfl
    · exact short_gate valid s .ADD 3 (Or.inl rfl) rfl gas short
    · exact short_gate valid s .ADD 3 (Or.inl rfl) rfl gas short
    · exact short_gate valid s .ADD 3 (Or.inl rfl) rfl gas short
    · exact short_gate valid s .ADD 3 (Or.inl rfl) rfl gas short
    · exact short_gate valid s .ADD 3 (Or.inl rfl) rfl gas short

theorem lt_refusal (valid : Array UInt256) (site : Site .LT)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .lt m=.fault ∧
    Scalar.run Selection.ltCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (comparison_short_scalar words short).1
  refine ⟨(Selection.ltCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := comparison_short_gate valid (modularSite site words).state .LT (Or.inl rfl) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem lt_native_refusal (valid : Array UInt256) (site : Site .LT)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := comparison_short_gate valid (modularSite site words).state .LT (Or.inl rfl) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem gt_refusal (valid : Array UInt256) (site : Site .GT)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .gt m=.fault ∧
    Scalar.run Selection.gtCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (comparison_short_scalar words short).2.1
  refine ⟨(Selection.gtCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := comparison_short_gate valid (modularSite site words).state .GT (Or.inr (Or.inl rfl)) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem gt_native_refusal (valid : Array UInt256) (site : Site .GT)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := comparison_short_gate valid (modularSite site words).state .GT (Or.inr (Or.inl rfl)) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem eq_refusal (valid : Array UInt256) (site : Site .EQ)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .eq m=.fault ∧
    Scalar.run Selection.eqCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (comparison_short_scalar words short).2.2.1
  refine ⟨(Selection.eqCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := comparison_short_gate valid (modularSite site words).state .EQ (Or.inr (Or.inr (Or.inl rfl))) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem eq_native_refusal (valid : Array UInt256) (site : Site .EQ)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := comparison_short_gate valid (modularSite site words).state .EQ (Or.inr (Or.inr (Or.inl rfl))) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem slt_refusal (valid : Array UInt256) (site : Site .SLT)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .slt m=.fault ∧
    Scalar.run Selection.sltCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (comparison_short_scalar words short).2.2.2.1
  refine ⟨(Selection.sltCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := comparison_short_gate valid (modularSite site words).state .SLT (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem slt_native_refusal (valid : Array UInt256) (site : Site .SLT)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := comparison_short_gate valid (modularSite site words).state .SLT (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem sgt_refusal (valid : Array UInt256) (site : Site .SGT)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .sgt m=.fault ∧
    Scalar.run Selection.sgtCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := (comparison_short_scalar words short).2.2.2.2
  refine ⟨(Selection.sgtCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := comparison_short_gate valid (modularSite site words).state .SGT (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem sgt_native_refusal (valid : Array UInt256) (site : Site .SGT)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := comparison_short_gate valid (modularSite site words).state .SGT (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem comparison_nonzero_clients (perm : Bool) :
    let m := {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack [513]}
    (Solidity.Evm.Instr.step .lt m=.fault ∧
      Scalar.run Selection.ltCertificate.code [513]=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .LT 12 perm) [513]).state=.error .StackUnderflow) ∧
    (Solidity.Evm.Instr.step .gt m=.fault ∧
      Scalar.run Selection.gtCertificate.code [513]=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .GT 12 perm) [513]).state=.error .StackUnderflow) ∧
    (Solidity.Evm.Instr.step .eq m=.fault ∧
      Scalar.run Selection.eqCertificate.code [513]=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .EQ 12 perm) [513]).state=.error .StackUnderflow) ∧
    (Solidity.Evm.Instr.step .slt m=.fault ∧
      Scalar.run Selection.sltCertificate.code [513]=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .SLT 12 perm) [513]).state=.error .StackUnderflow) ∧
    (Solidity.Evm.Instr.step .sgt m=.fault ∧
      Scalar.run Selection.sgtCertificate.code [513]=none ∧
      Assembly.driverSteps 1 2 #[u 37,u 99]
        (modularSite (WrappingArithmeticFixtures.site .SGT 12 perm) [513]).state=.error .StackUnderflow) := by
  exact ⟨lt_refusal _ _ _ _ rfl (by decide) (by change 3≤12;decide) 0,
    gt_refusal _ _ _ _ rfl (by decide) (by change 3≤12;decide) 0,
    eq_refusal _ _ _ _ rfl (by decide) (by change 3≤12;decide) 0,
    slt_refusal _ _ _ _ rfl (by decide) (by change 3≤12;decide) 0,
    sgt_refusal _ _ _ _ rfl (by decide) (by change 3≤12;decide) 0⟩

theorem comparison_priority_controls (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .LT 2 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .GT 2 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .EQ 2 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SLT 2 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SGT 2 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .LT 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .GT 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .EQ 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SLT 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SGT 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .LT 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .GT 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .EQ 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SLT 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SGT 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .LT 0 perm [])=.error .OutOfFuel ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .GT 0 perm [])=.error .OutOfFuel ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .EQ 0 perm [])=.error .OutOfFuel ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .SLT 0 perm [])=.error .OutOfFuel ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .SGT 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem comparison_native_fuel_boundary (perm : Bool) :
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .LT 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .LT 12 perm) [513]).state=.error .OutOfFuel ∧
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .GT 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .GT 12 perm) [513]).state=.error .OutOfFuel ∧
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .EQ 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .EQ 12 perm) [513]).state=.error .OutOfFuel ∧
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .SLT 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .SLT 12 perm) [513]).state=.error .OutOfFuel ∧
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .SGT 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .SGT 12 perm) [513]).state=.error .OutOfFuel := by
  exact ⟨lt_native_refusal _ _ _ (by decide) (by change 3≤12;decide) 0,rfl,gt_native_refusal _ _ _ (by decide) (by change 3≤12;decide) 0,rfl,eq_native_refusal _ _ _ (by decide) (by change 3≤12;decide) 0,rfl,slt_native_refusal _ _ _ (by decide) (by change 3≤12;decide) 0,rfl,sgt_native_refusal _ _ _ (by decide) (by change 3≤12;decide) 0,rfl⟩

theorem comparison_input_observation (perm : Bool) :
    let input := WrappingArithmeticFixtures.input .SLT 12 perm [513]
    input.stack=[u 513] ∧ input.executionEnv.perm=perm ∧
    input.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x12,0] ∧
    input.pc=u 3 ∧ input.gasAvailable=u 12 ∧ input.execLength=41 ∧
    input.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    input.returnData.data.toList=[0xcc,0xdd] ∧ input.H_return.data.toList=[0xee,0xff] ∧
    input.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    input.accountMap=WordPushFixtures.accounts ∧ input.σ₀=WordPushFixtures.accounts := by
  first | rfl | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.lt_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lt_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.lt_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lt_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.gt_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms gt_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.gt_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms gt_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.eq_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eq_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.eq_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eq_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.slt_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms slt_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.slt_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms slt_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.sgt_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sgt_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.sgt_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sgt_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.comparison_nonzero_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms comparison_nonzero_clients
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.comparison_priority_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms comparison_priority_controls
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.comparison_native_fuel_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms comparison_native_fuel_boundary
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.comparison_input_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms comparison_input_observation
private theorem sub_short_scalar (words : Scalar.Stack) (short : words.length<2) :
    Scalar.run Selection.subCertificate.code words=none := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | cases words with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b tail => simp only [List.length_cons] at short;omega

private theorem sub_short_gate (valid : Array UInt256) (s : EVM.State)
    (gas : 3≤s.gasAvailable.toNat) (short : s.stack.length<2) :
    Assembly.driverGate valid s .SUB=.error .StackUnderflow := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | exact short_gate valid s .ADD 3 (Or.inl rfl) rfl gas short

theorem sub_refusal (valid : Array UInt256) (site : Site .SUB)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .sub m=.fault ∧
    Scalar.run Selection.subCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := sub_short_scalar words short
  refine ⟨(Selection.subCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := sub_short_gate valid (modularSite site words).state gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem sub_native_refusal (valid : Array UInt256) (site : Site .SUB)
    (words : Scalar.Stack) (short : words.length<2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := sub_short_gate valid (modularSite site words).state gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem sub_nonzero_client (perm : Bool) :
    let m := {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack [513]}
    Solidity.Evm.Instr.step .sub m=.fault ∧
    Scalar.run Selection.subCertificate.code [513]=none ∧
    Assembly.driverSteps 1 2 #[u 37,u 99]
      (modularSite (WrappingArithmeticFixtures.site .SUB 12 perm) [513]).state=.error .StackUnderflow := by
  exact sub_refusal _ _ _ _ rfl (by decide) (by change 3≤12;decide) 0

theorem sub_priority_controls (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SUB 2 perm [513])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SUB 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .SUB 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .SUB 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem sub_native_fuel_boundary (perm : Bool) :
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .SUB 12 perm) [513]).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .SUB 12 perm) [513]).state=.error .OutOfFuel := by
  exact ⟨sub_native_refusal _ _ _ (by decide) (by change 3≤12;decide) 0,rfl⟩

theorem sub_input_observation (perm : Bool) :
    let input := WrappingArithmeticFixtures.input .SUB 12 perm [513]
    input.stack=[u 513] ∧ input.executionEnv.perm=perm ∧
    input.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x03,0] ∧
    input.pc=u 3 ∧ input.gasAvailable=u 12 ∧ input.execLength=41 ∧
    input.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    input.returnData.data.toList=[0xcc,0xdd] ∧ input.H_return.data.toList=[0xee,0xff] ∧
    input.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    input.accountMap=WordPushFixtures.accounts ∧ input.σ₀=WordPushFixtures.accounts := by
  first | rfl | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.sub_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sub_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.sub_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sub_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.sub_nonzero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sub_nonzero_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.sub_priority_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sub_priority_controls
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.sub_native_fuel_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sub_native_fuel_boundary
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.sub_input_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sub_input_observation
private theorem pop_short_scalar (words : Scalar.Stack) (short : words.length<1) :
    Scalar.run Selection.popCertificate.code words=none := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | cases words with
    | nil => rfl
    | cons a tail => simp only [List.length_cons] at short;omega

private theorem pop_short_gate (valid : Array UInt256) (s : EVM.State)
    (gas : 2≤s.gasAvailable.toNat) (short : s.stack.length<1) :
    Assembly.driverGate valid s .POP=.error .StackUnderflow := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | have expansion : EVM.memoryExpansionCost s .POP=0 := by
      simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
    have cost : EVM.C' s .POP=2 := rfl
    have delta : EVM.δ .POP=some 1 := rfl
    have charge : s.gasAvailable-UInt256.ofNat 0=s.gasAvailable := by
      change UInt256.mk (s.gasAvailable.val-0)=s.gasAvailable
      rw [sub_zero]
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [cost,delta,Option.getD_some,if_neg (Nat.not_lt_zero _),
      if_neg (Nat.not_lt_of_ge gas),reduceCtorEq,if_false,if_pos short,bind,Except.bind,pure,Except.pure]

theorem pop_refusal (valid : Array UInt256) (site : Site .POP)
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<1)
    (gas : 2≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step .pop m=.fault ∧
    Scalar.run Selection.popCertificate.code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := pop_short_scalar words short
  refine ⟨(Selection.popCertificate.refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := pop_short_gate valid (modularSite site words).state gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem pop_native_refusal (valid : Array UInt256) (site : Site .POP)
    (words : Scalar.Stack) (short : words.length<1)
    (gas : 2≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := pop_short_gate valid (modularSite site words).state gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem pop_empty_client (perm : Bool) :
    let m := {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack []}
    Solidity.Evm.Instr.step .pop m=.fault ∧
    Scalar.run Selection.popCertificate.code []=none ∧
    Assembly.driverSteps 1 2 #[u 37,u 99]
      (modularSite (WrappingArithmeticFixtures.site .POP 12 perm) []).state=.error .StackUnderflow := by
  exact pop_refusal _ _ _ _ rfl (by decide) (by change 2≤12;decide) 0

theorem pop_priority_controls (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .POP 1 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input .POP 2 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input .POP 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl,rfl⟩

theorem pop_native_fuel_boundary (perm : Bool) :
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site .POP 12 perm) []).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site .POP 12 perm) []).state=.error .OutOfFuel := by
  exact ⟨pop_native_refusal _ _ _ (by decide) (by change 2≤12;decide) 0,rfl⟩

theorem pop_input_observation (perm : Bool) :
    let input := WrappingArithmeticFixtures.input .POP 12 perm []
    input.stack=[] ∧ input.executionEnv.perm=perm ∧
    input.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x50,0] ∧
    input.pc=u 3 ∧ input.gasAvailable=u 12 ∧ input.execLength=41 ∧
    input.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    input.returnData.data.toList=[0xcc,0xdd] ∧ input.H_return.data.toList=[0xee,0xff] ∧
    input.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    input.accountMap=WordPushFixtures.accounts ∧ input.σ₀=WordPushFixtures.accounts := by
  first | rfl | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.pop_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pop_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.pop_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pop_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.pop_empty_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pop_empty_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.pop_priority_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pop_priority_controls
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.pop_native_fuel_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pop_native_fuel_boundary
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.pop_input_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pop_input_observation
open private SolidityBridge.RoadmapV15.P10.dup_facts from SolidityBridge.RoadmapV15.P10.StackFamilyConsumer

private theorem dup_short_scalar (n : Fin 16) (words : Scalar.Stack)
    (short : words.length<n.val+1) :
    Scalar.run (Selection.dupCertificate n).code words=none := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | have missing : words[n.val]?=none := List.getElem?_eq_none (by omega)
    change (Scalar.duplicate n.val words).bind (fun out=>some out)=none
    simp only [Scalar.duplicate,missing,Option.map_none,Option.bind_none]

private theorem dup_short_gate (valid : Array UInt256) (n : Fin 16) (s : EVM.State)
    (gas : 3≤s.gasAvailable.toNat) (short : s.stack.length<n.val+1) :
    Assembly.driverGate valid s (dupCode n)=.error .StackUnderflow := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | have facts := SolidityBridge.RoadmapV15.P10.dup_facts n s
    have charge : s.gasAvailable-UInt256.ofNat 0=s.gasAvailable := by
      change UInt256.mk (s.gasAvailable.val-0)=s.gasAvailable
      rw [sub_zero]
    simp only [Assembly.driverGate]
    rw [facts.1,charge]
    simp only [facts.2.1,facts.2.2.1,Option.getD_some,if_neg (Nat.not_lt_zero _),
      if_neg (Nat.not_lt_of_ge gas),reduceCtorEq,if_false,if_pos short,bind,Except.bind,pure,Except.pure]

theorem dup_refusal (valid : Array UInt256) (n : Fin 16) (site : Site (.DUP n))
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<n.val+1)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step (.dup (n.val+1)) m=.fault ∧
    Scalar.run (Selection.dupCertificate n).code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := dup_short_scalar n words short
  refine ⟨((Selection.dupCertificate n).refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := dup_short_gate valid n (modularSite site words).state gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem dup_native_refusal (valid : Array UInt256) (n : Fin 16) (site : Site (.DUP n))
    (words : Scalar.Stack) (short : words.length<n.val+1)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := dup_short_gate valid n (modularSite site words).state gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem dup_empty_client (n : Fin 16) (perm : Bool) :
    let m := {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack []}
    Solidity.Evm.Instr.step (.dup (n.val+1)) m=.fault ∧
    Scalar.run (Selection.dupCertificate n).code []=none ∧
    Assembly.driverSteps 1 2 #[u 37,u 99]
      (modularSite (WrappingArithmeticFixtures.site (.DUP n) 12 perm) []).state=.error .StackUnderflow := by
  exact dup_refusal _ n _ _ _ rfl (by change 0<n.val+1;omega) (by change 3≤12;decide) 0

theorem dup16_nonzero_client (perm : Bool) :
    let m := {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack (List.replicate 15 7)}
    Solidity.Evm.Instr.step (.dup 16) m=.fault ∧
    Scalar.run (Selection.dupCertificate ⟨15,by decide⟩).code (List.replicate 15 7)=none ∧
    Assembly.driverSteps 1 2 #[u 37,u 99]
      (modularSite (WrappingArithmeticFixtures.site (.DUP ⟨15,by decide⟩) 12 perm) (List.replicate 15 7)).state=.error .StackUnderflow := by
  exact dup_refusal _ ⟨15,by decide⟩ _ _ _ rfl (by decide) (by change 3≤12;decide) 0

theorem dup_depth_boundary (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input (.DUP ⟨15,by decide⟩) 12 perm (List.replicate 15 7))=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input (.DUP ⟨14,by decide⟩) 12 perm (List.replicate 15 7))=
      .ok {WrappingArithmeticFixtures.input (.DUP ⟨14,by decide⟩) 12 perm (List.replicate 15 7) with
        stack:=List.replicate 16 (u 7),pc:=u 4,gasAvailable:=u 9,execLength:=42} := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl⟩

theorem dup_priority_controls (n : Fin 16) (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input (.DUP n) 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input (.DUP n) 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input (.DUP n) 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | let input := WrappingArithmeticFixtures.input (.DUP n) 2 perm []
    have facts := SolidityBridge.RoadmapV15.P10.dup_facts n input
    have charge : input.gasAvailable-UInt256.ofNat 0=input.gasAvailable := by
      change UInt256.mk (input.gasAvailable.val-0)=input.gasAvailable
      rw [sub_zero]
    have gate : Assembly.driverGate #[] input (dupCode n)=.error .OutOfGass := by
      simp only [Assembly.driverGate]
      rw [facts.1,charge,facts.2.1]
      rfl
    have decoded := DecoderAgreement.decode_all
      (modularSite (WrappingArithmeticFixtures.site (.DUP n) 2 perm) [])
    change EVM.decode input.executionEnv.code input.pc=some (dupCode n,none) at decoded
    have low : Assembly.driverSteps 1 2 #[] input=.error .OutOfGass := by
      simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,
        DecoderAgreement.referenceOp,gate]
    have shortage := (dup_refusal #[] n (WrappingArithmeticFixtures.site (.DUP n) 3 perm) []
      {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack []} rfl
      (by change 0<n.val+1;omega) (by change 3≤3;decide) 0).2.2
    exact ⟨low,shortage,rfl⟩

theorem dup_native_fuel_boundary (n : Fin 16) (perm : Bool) :
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site (.DUP n) 12 perm) []).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site (.DUP n) 12 perm) []).state=.error .OutOfFuel := by
  exact ⟨dup_native_refusal _ n _ _ (by change 0<n.val+1;omega) (by change 3≤12;decide) 0,rfl⟩

theorem dup_input_observation (perm : Bool) :
    let input := WrappingArithmeticFixtures.input (.DUP ⟨15,by decide⟩) 12 perm (List.replicate 15 7)
    input.stack=List.replicate 15 (u 7) ∧ input.executionEnv.perm=perm ∧
    input.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x8f,0] ∧
    input.pc=u 3 ∧ input.gasAvailable=u 12 ∧ input.execLength=41 ∧
    input.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    input.returnData.data.toList=[0xcc,0xdd] ∧ input.H_return.data.toList=[0xee,0xff] ∧
    input.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    input.accountMap=WordPushFixtures.accounts ∧ input.σ₀=WordPushFixtures.accounts := by
  first | rfl | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.dup_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dup_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.dup_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dup_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.dup_empty_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dup_empty_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.dup16_nonzero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dup16_nonzero_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.dup_depth_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dup_depth_boundary
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.dup_priority_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dup_priority_controls
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.dup_native_fuel_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dup_native_fuel_boundary
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.dup_input_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dup_input_observation
open private SolidityBridge.RoadmapV15.P10.swap_facts from SolidityBridge.RoadmapV15.P10.StackFamilyConsumer

private theorem swap_short_scalar (n : Fin 16) (words : Scalar.Stack)
    (short : words.length<n.val+2) :
    Scalar.run (Selection.swapCertificate n).code words=none := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | cases words with
    | nil => rfl
    | cons a tail =>
      have missing : tail[n.val]?=none := List.getElem?_eq_none (by
        simp only [List.length_cons] at short;omega)
      change ((Scalar.exchange a n.val tail).map (fun pair=>pair.1::pair.2)).bind (fun out=>some out)=none
      simp only [Selection.exchange_get_set,missing,Option.map_none,Option.bind_none]

private theorem swap_short_gate (valid : Array UInt256) (n : Fin 16) (s : EVM.State)
    (gas : 3≤s.gasAvailable.toNat) (short : s.stack.length<n.val+2) :
    Assembly.driverGate valid s (swapCode n)=.error .StackUnderflow := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | have facts := SolidityBridge.RoadmapV15.P10.swap_facts n s
    have charge : s.gasAvailable-UInt256.ofNat 0=s.gasAvailable := by
      change UInt256.mk (s.gasAvailable.val-0)=s.gasAvailable
      rw [sub_zero]
    simp only [Assembly.driverGate]
    rw [facts.1,charge]
    simp only [facts.2.1,facts.2.2.1,Option.getD_some,if_neg (Nat.not_lt_zero _),
      if_neg (Nat.not_lt_of_ge gas),reduceCtorEq,if_false,if_pos short,bind,Except.bind,pure,Except.pure]

theorem swap_refusal (valid : Array UInt256) (n : Fin 16) (site : Site (.SWAP n))
    (words : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack words) (short : words.length<n.val+2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    Solidity.Evm.Instr.step (.swap (n.val+1)) m=.fault ∧
    Scalar.run (Selection.swapCertificate n).code words=none ∧
    Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow := by
  have scalar := swap_short_scalar n words short
  refine ⟨((Selection.swapCertificate n).refusal words m represented).mpr scalar,scalar,?_⟩
  have gate := swap_short_gate valid n (modularSite site words).state gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,DecoderAgreement.referenceOp,gate]

theorem swap_native_refusal (valid : Array UInt256) (n : Fin 16) (site : Site (.SWAP n))
    (words : Scalar.Stack) (short : words.length<n.val+2)
    (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow := by
  have gate := swap_short_gate valid n (modularSite site words).state gas
    (by simpa only [modularSite,Site.state,List.length_map] using short)
  have decoded := DecoderAgreement.decode_all (modularSite site words)
  simp only [Assembly.X_unfold,decoded,Option.getD_some,DecoderAgreement.referenceOp,gate]

theorem swap_empty_client (n : Fin 16) (perm : Bool) :
    let m := {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack []}
    Solidity.Evm.Instr.step (.swap (n.val+1)) m=.fault ∧
    Scalar.run (Selection.swapCertificate n).code []=none ∧
    Assembly.driverSteps 1 2 #[u 37,u 99]
      (modularSite (WrappingArithmeticFixtures.site (.SWAP n) 12 perm) []).state=.error .StackUnderflow := by
  exact swap_refusal _ n _ _ _ rfl (by change 0<n.val+2;omega) (by change 3≤12;decide) 0

theorem swap16_nonzero_client (perm : Bool) :
    let m := {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack (List.replicate 16 7)}
    Solidity.Evm.Instr.step (.swap 16) m=.fault ∧
    Scalar.run (Selection.swapCertificate ⟨15,by decide⟩).code (List.replicate 16 7)=none ∧
    Assembly.driverSteps 1 2 #[u 37,u 99]
      (modularSite (WrappingArithmeticFixtures.site (.SWAP ⟨15,by decide⟩) 12 perm) (List.replicate 16 7)).state=.error .StackUnderflow := by
  exact swap_refusal _ ⟨15,by decide⟩ _ _ _ rfl (by decide) (by change 3≤12;decide) 0

theorem swap_depth_boundary (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input (.SWAP ⟨15,by decide⟩) 12 perm (7::List.replicate 15 11))=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input (.SWAP ⟨14,by decide⟩) 12 perm (7::List.replicate 15 11))=
      .ok {WrappingArithmeticFixtures.input (.SWAP ⟨14,by decide⟩) 12 perm (7::List.replicate 15 11) with
        stack:=List.replicate 15 (u 11)++[u 7],pc:=u 4,gasAvailable:=u 9,execLength:=42} := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl⟩

theorem swap_priority_controls (n : Fin 16) (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input (.SWAP n) 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (WrappingArithmeticFixtures.input (.SWAP n) 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (WrappingArithmeticFixtures.input (.SWAP n) 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | simp only []
  | solve | decide
  | let input := WrappingArithmeticFixtures.input (.SWAP n) 2 perm []
    have facts := SolidityBridge.RoadmapV15.P10.swap_facts n input
    have charge : input.gasAvailable-UInt256.ofNat 0=input.gasAvailable := by
      change UInt256.mk (input.gasAvailable.val-0)=input.gasAvailable
      rw [sub_zero]
    have gate : Assembly.driverGate #[] input (swapCode n)=.error .OutOfGass := by
      simp only [Assembly.driverGate]
      rw [facts.1,charge,facts.2.1]
      rfl
    have decoded := DecoderAgreement.decode_all
      (modularSite (WrappingArithmeticFixtures.site (.SWAP n) 2 perm) [])
    change EVM.decode input.executionEnv.code input.pc=some (swapCode n,none) at decoded
    have low : Assembly.driverSteps 1 2 #[] input=.error .OutOfGass := by
      simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,
        DecoderAgreement.referenceOp,gate]
    have shortage := (swap_refusal #[] n (WrappingArithmeticFixtures.site (.SWAP n) 3 perm) []
      {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack []} rfl
      (by change 0<n.val+2;omega) (by change 3≤3;decide) 0).2.2
    exact ⟨low,shortage,rfl⟩

theorem swap_native_fuel_boundary (n : Fin 16) (perm : Bool) :
    EVM.X 1 #[] (modularSite (WrappingArithmeticFixtures.site (.SWAP n) 12 perm) []).state=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (modularSite (WrappingArithmeticFixtures.site (.SWAP n) 12 perm) []).state=.error .OutOfFuel := by
  exact ⟨swap_native_refusal _ n _ _ (by change 0<n.val+2;omega) (by change 3≤12;decide) 0,rfl⟩

theorem swap_input_observation (perm : Bool) :
    let input := WrappingArithmeticFixtures.input (.SWAP ⟨15,by decide⟩) 12 perm (7::List.replicate 15 11)
    input.stack=u 7::List.replicate 15 (u 11) ∧ input.executionEnv.perm=perm ∧
    input.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x9f,0] ∧
    input.pc=u 3 ∧ input.gasAvailable=u 12 ∧ input.execLength=41 ∧
    input.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    input.returnData.data.toList=[0xcc,0xdd] ∧ input.H_return.data.toList=[0xee,0xff] ∧
    input.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    input.accountMap=WordPushFixtures.accounts ∧ input.σ₀=WordPushFixtures.accounts := by
  first | rfl | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.swap_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms swap_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.swap_native_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms swap_native_refusal
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.swap_empty_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms swap_empty_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.swap16_nonzero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms swap16_nonzero_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.swap_depth_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms swap_depth_boundary
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.swap_priority_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms swap_priority_controls
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.swap_native_fuel_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms swap_native_fuel_boundary
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal.swap_input_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms swap_input_observation
end SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal
