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
end SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal
