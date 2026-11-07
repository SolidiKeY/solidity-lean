import SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement
import SolidityBridge.RoadmapV15.P10.WrappingArithmeticFixtures

/-! Inhabited concrete IR/Scalar/native arithmetic clients. Complete frames are
observed separately; no account-world or physical-loading relation is assumed. -/
namespace SolidityBridge.RoadmapV15.P10.InstructionSelectionControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (spill u accounts)
namespace F
export WrappingArithmeticFixtures (input observed site supplied)
end F

def ir (a b : Scalar.Word) : Solidity.Evm.Machine :=
  {Solidity.Evm.Machine.init with
    mem:=fun address=>if address=0 then .val (Solidity.Evm.wmod 128) else if address=63 then .val (Solidity.Evm.wmod 99) else .val (Solidity.Evm.wmod 0),
    stack:=Selection.irStack (a::b::spill),self:=Solidity.Evm.wmod 7,
    caller:=Solidity.Evm.wmod 19,callvalue:=Solidity.Evm.wmod 23,timestamp:=Solidity.Evm.wmod 29,
    bal:=fun a=>if a.val=7 then 41 else 13,bal₀:=fun a=>if a.val=7 then 53 else 17}
def irExpected (a b result : Scalar.Word) : Solidity.Evm.Machine :=
  {ir a b with stack:=Selection.irStack (result::spill)}
def nativeExpected (op : Backend.Op) (cost : Nat) (a b result : Scalar.Word) (perm : Bool) : EVM.State :=
  F.observed op 12 perm cost a b spill result

private theorem shape (op : Backend.Op) (cost : Nat) (a b result : Scalar.Word) (perm : Bool)
    (allowed : (op=.ADD ∧ cost=3) ∨ (op=.MUL ∧ cost=5)) :
    (Assembly.chargedPrepare (F.input op 12 perm (a::b::spill)) cost).replaceStackAndIncrPC
      ((result::spill).map (fun w=>UInt256.mk w.toFin))=nativeExpected op cost a b result perm := by
  rcases allowed with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
    simp only [F.input,nativeExpected,F.observed,WrappingArithmeticFixtures.input,WrappingArithmeticFixtures.observed,
      WrappingArithmeticFixtures.site,modularSite,Site.state,Assembly.chargedPrepare,
      EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,WordPushFixtures.seed,WordPushFixtures.u,WordPushFixtures.before] <;> rfl

theorem add_client (a b : Scalar.Word) (perm : Bool) :
    Solidity.Evm.Instr.step .add (ir a b)=.ok (irExpected a b (a+b)) 0 ∧
    Assembly.driverSteps 1 2 F.supplied (F.input .ADD 12 perm (a::b::spill))=.ok (nativeExpected .ADD 3 a b (a+b) perm) ∧
    EVM.X 2 F.supplied (F.input .ADD 12 perm (a::b::spill))=EVM.X 1 F.supplied (nativeExpected .ADD 3 a b (a+b) perm) := by
  have h := InstructionSelectionAgreement.add F.supplied (F.site .ADD 12 perm) a b spill (ir a b) rfl (by decide) (by change 3≤12;decide) 0
  dsimp only at h
  have eq := shape .ADD 3 a b (a+b) perm (Or.inl ⟨rfl,rfl⟩)
  simp only [WrappingArithmeticFixtures.input] at eq
  rw [eq] at h
  exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩

theorem mul_client (a b : Scalar.Word) (perm : Bool) :
    Solidity.Evm.Instr.step .mul (ir a b)=.ok (irExpected a b (a*b)) 0 ∧
    Assembly.driverSteps 1 2 F.supplied (F.input .MUL 12 perm (a::b::spill))=.ok (nativeExpected .MUL 5 a b (a*b) perm) ∧
    EVM.X 2 F.supplied (F.input .MUL 12 perm (a::b::spill))=EVM.X 1 F.supplied (nativeExpected .MUL 5 a b (a*b) perm) := by
  have h := InstructionSelectionAgreement.mul F.supplied (F.site .MUL 12 perm) a b spill (ir a b) rfl (by decide) (by change 5≤12;decide) 0
  dsimp only at h
  have eq := shape .MUL 5 a b (a*b) perm (Or.inr ⟨rfl,rfl⟩)
  simp only [WrappingArithmeticFixtures.input] at eq
  rw [eq] at h
  exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩

theorem boundaries (perm : Bool) :
    Assembly.driverSteps 1 2 F.supplied (F.input .ADD 12 perm (BitVec.ofNat 256 ((2^256:Nat)-1)::1::spill))=
      .ok (nativeExpected .ADD 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm) ∧
    Assembly.driverSteps 1 2 F.supplied (F.input .MUL 12 perm (BitVec.ofNat 256 (2^255)::2::spill))=
      .ok (nativeExpected .MUL 5 (BitVec.ofNat 256 (2^255)) 2 0 perm) := by
  have a := (add_client (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 perm).2.1
  have m := (mul_client (BitVec.ofNat 256 (2^255)) 2 perm).2.1
  have za : BitVec.ofNat 256 ((2^256:Nat)-1)+1=0 := by decide
  have zm : BitVec.ofNat 256 (2^255)*2=0 := by decide
  rw [za] at a;rw [zm] at m
  exact ⟨a,m⟩

theorem complete_observation (perm : Bool) :
    let next := nativeExpected .MUL 5 7 3 21 perm
    next.stack=[u 21,u 258,u 513] ∧ next.stack≠[u 10,u 258,u 513] ∧ next.stack≠[u 21,u 513,u 258] ∧
    next.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x02,0] ∧
    next.pc=u 4 ∧ next.gasAvailable=u 7 ∧ next.execLength=42 ∧
    next.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    next.returnData.data.toList=[0xcc,0xdd] ∧ next.H_return.data.toList=[0xee,0xff] ∧
    next.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧ next.accountMap=accounts ∧ next.σ₀=accounts := by
  refine ⟨rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 21,u 258,u 513]≠[u 10,u 258,u 513];decide
  · change [u 21,u 258,u 513]≠[u 21,u 513,u 258];decide

theorem ir_frame :
    (irExpected 7 3 21).mem=(ir 7 3).mem ∧ (irExpected 7 3 21).store=(ir 7 3).store ∧
    (irExpected 7 3 21).bal=(ir 7 3).bal ∧ (irExpected 7 3 21).bal₀=(ir 7 3).bal₀ ∧
    (irExpected 7 3 21).caller=Solidity.Evm.wmod 19 ∧ (irExpected 7 3 21).callvalue=Solidity.Evm.wmod 23 ∧
    (irExpected 7 3 21).timestamp=Solidity.Evm.wmod 29 ∧ (irExpected 7 3 21).mem 0=Solidity.Evm.Word.val (Solidity.Evm.wmod 128) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem resource_separation (perm : Bool) :
    Solidity.Evm.Instr.step .add (ir 7 3)=.ok (irExpected 7 3 10) 0 ∧
    Assembly.driverSteps 1 2 F.supplied (F.input .ADD 2 perm (7::3::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 1 F.supplied (F.input .ADD 0 perm [])=.error .OutOfFuel := by
  have h := (add_client 7 3 perm).1
  cases perm <;> exact ⟨h,rfl,rfl⟩

theorem stack_failure (perm : Bool) :
    Solidity.Evm.Instr.step .add {ir 7 3 with stack:=[]} = .fault ∧
    Assembly.driverSteps 1 2 F.supplied (F.input .ADD 3 perm [])=.error .StackUnderflow := by
  cases perm <;> exact ⟨rfl,rfl⟩

theorem frame_separation (perm : Bool) :
    (irExpected 7 3 21).callvalue.val=23 ∧
    (nativeExpected .MUL 5 7 3 21 perm).executionEnv.weiValue=u 0 ∧
    (irExpected 7 3 21).callvalue.val≠(nativeExpected .MUL 5 7 3 21 perm).executionEnv.weiValue.toNat := by
  refine ⟨rfl,rfl,?_⟩
  change (23 : Nat)≠0
  decide


/-- A populated client of the actual selected subtraction certificate. -/
theorem sub_client (a b : Scalar.Word) (perm : Bool) :
    Solidity.Evm.Instr.step .sub (ir a b)=.ok (irExpected a b (a-b)) 0 ∧
    Assembly.driverSteps 1 2 F.supplied (F.input .SUB 12 perm (a::b::spill))=
      .ok (nativeExpected .SUB 3 a b (a-b) perm) ∧
    EVM.X 2 F.supplied (F.input .SUB 12 perm (a::b::spill))=
      EVM.X 1 F.supplied (nativeExpected .SUB 3 a b (a-b) perm) := by
  first
  | solve | rfl
  | solve | simp only
  | solve | decide
  | solve | omega
  | have h := InstructionSelectionAgreement.sub F.supplied (F.site .SUB 12 perm)
      a b spill (ir a b) rfl (by decide) (by change 3≤12;decide) 0
    dsimp only at h
    have eq : (Assembly.chargedPrepare (F.input .SUB 12 perm (a::b::spill)) 3).replaceStackAndIncrPC
        (((a-b)::spill).map (fun w=>UInt256.mk w.toFin))=nativeExpected .SUB 3 a b (a-b) perm := by
      first
      | rfl
      | simp only [F.input,nativeExpected,F.observed,WrappingArithmeticFixtures.input,
          WrappingArithmeticFixtures.observed,WrappingArithmeticFixtures.site,modularSite,
          Site.state,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,
          EVM.State.incrPC,WordPushFixtures.seed,WordPushFixtures.u,WordPushFixtures.before]
        rfl
    simp only [WrappingArithmeticFixtures.input] at eq
    rw [eq] at h
    exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩

theorem sub_wrap_client (perm : Bool) :
    Assembly.driverSteps 1 2 F.supplied (F.input .SUB 12 perm (3::5::spill))=
      .ok (nativeExpected .SUB 3 3 5 (BitVec.ofNat 256 ((2^256:Nat)-2)) perm) := by
  have h := (sub_client 3 5 perm).2.1
  have value : (3 : Scalar.Word)-5=BitVec.ofNat 256 ((2^256:Nat)-2) := by decide
  rw [value] at h
  exact h

theorem sub_complete_observation (perm : Bool) :
    let next := nativeExpected .SUB 3 7 3 4 perm
    next.stack=[u 4,u 258,u 513] ∧ next.stack≠[u 4,u 513,u 258] ∧
    next.stack≠[u (2^256-4),u 258,u 513] ∧
    next.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x03,0] ∧
    next.pc=u 4 ∧ next.gasAvailable=u 9 ∧ next.execLength=42 ∧
    next.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    next.returnData.data.toList=[0xcc,0xdd] ∧ next.H_return.data.toList=[0xee,0xff] ∧
    next.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧ next.accountMap=accounts ∧ next.σ₀=accounts := by
  first
  | solve | decide
  | refine ⟨rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    · change [u 4,u 258,u 513]≠[u 4,u 513,u 258];decide
    · change [u 4,u 258,u 513]≠[u (2^256-4),u 258,u 513];decide

theorem sub_resource_order (perm : Bool) :
    Solidity.Evm.Instr.step .sub (ir 7 3)=.ok (irExpected 7 3 4) 0 ∧
    Assembly.driverSteps 1 2 F.supplied (F.input .SUB 2 perm (7::3::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 F.supplied (F.input .SUB 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 F.supplied (F.input .SUB 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 F.supplied (F.input .SUB 12 perm (7::3::spill))=.error .OutOfFuel := by
  have h := (sub_client 7 3 perm).1
  cases perm <;> exact ⟨h,rfl,rfl,rfl,rfl⟩


private theorem exp_three_cost (budget : Nat) (perm : Bool) :
    EVM.C' (F.input .EXP budget perm (7::3::spill)) .EXP=60 := by
  change EVM.C' (modularSite (F.site .EXP budget perm) (7::3::spill)).state .EXP=60
  rw [power_cost]
  change 10+50*(1+Nat.log 256 3)=60
  rw [Nat.log_of_lt (by decide : 3<256)]

theorem exp_nonzero_client (perm : Bool) :
    Solidity.Evm.Instr.step .exp (ir 7 3)=.ok (irExpected 7 3 343) 0 ∧
    Assembly.driverSteps 1 2 #[] (F.input .EXP 60 perm (7::3::spill))=
      .ok (F.observed .EXP 60 perm 60 7 3 spill 343) ∧
    EVM.X 2 #[] (F.input .EXP 60 perm (7::3::spill))=
      EVM.X 1 #[] (F.observed .EXP 60 perm 60 7 3 spill 343) := by
  have h := InstructionSelectionAgreement.exp (F.site .EXP 60 perm) 7 3 spill (ir 7 3)
    rfl (by decide) (by
      change EVM.C' (F.input .EXP 60 perm (7::3::spill)) .EXP≤60
      rw [exp_three_cost]) 0
  dsimp only at h
  have shape : (Assembly.chargedPrepare (F.input .EXP 60 perm (7::3::spill)) 60).replaceStackAndIncrPC
      ((343::spill).map (fun w=>UInt256.mk w.toFin))=F.observed .EXP 60 perm 60 7 3 spill 343 := by
    first | rfl | (simp only [F.input,F.observed,WrappingArithmeticFixtures.input,
      WrappingArithmeticFixtures.observed,WrappingArithmeticFixtures.site,modularSite,
      Site.state,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,
      EVM.State.incrPC,WordPushFixtures.seed,WordPushFixtures.u,WordPushFixtures.before];rfl)
  have cost : EVM.C' (modularSite (F.site .EXP 60 perm) (7::3::spill)).state .EXP=60 := exp_three_cost 60 perm
  have value : BitVec.ofNat 256 ((7:Scalar.Word).toNat^(3:Scalar.Word).toNat)=(343:Scalar.Word) := by rfl
  rw [cost,value] at h
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩

theorem exp_zero_client (perm : Bool) :
    Solidity.Evm.Instr.step .exp (ir 0 0)=.ok (irExpected 0 0 1) 0 ∧
    Assembly.driverSteps 1 2 #[] (F.input .EXP 10 perm (0::0::spill))=
      .ok (F.observed .EXP 10 perm 10 0 0 spill 1) := by
  have h := InstructionSelectionAgreement.exp (F.site .EXP 10 perm) 0 0 spill (ir 0 0)
    rfl (by decide) (by change 10≤10;decide) 0
  dsimp only at h
  have shape : (Assembly.chargedPrepare (F.input .EXP 10 perm (0::0::spill)) 10).replaceStackAndIncrPC
      ((1::spill).map (fun w=>UInt256.mk w.toFin))=F.observed .EXP 10 perm 10 0 0 spill 1 := by
    first | rfl | (simp only [F.input,F.observed,WrappingArithmeticFixtures.input,
      WrappingArithmeticFixtures.observed,WrappingArithmeticFixtures.site,modularSite,
      Site.state,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,
      EVM.State.incrPC,WordPushFixtures.seed,WordPushFixtures.u,WordPushFixtures.before];rfl)
  have value : BitVec.ofNat 256 ((0:Scalar.Word).toNat^(0:Scalar.Word).toNat)=(1:Scalar.Word) := by rfl
  rw [show EVM.C' (modularSite (F.site .EXP 10 perm) (0::0::spill)).state .EXP=10 from rfl,value] at h
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.2.1⟩

theorem exp_resource_boundary (perm : Bool) :
    EVM.C' (F.input .EXP 60 perm (7::255::spill)) .EXP=60 ∧
    EVM.C' (F.input .EXP 110 perm (7::256::spill)) .EXP=110 ∧
    Assembly.driverSteps 1 2 #[] (F.input .EXP 59 perm (7::3::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 1 #[] (F.input .EXP 60 perm (7::3::spill))=.error .OutOfFuel := by
  refine ⟨?_,?_,?_,rfl⟩
  · change EVM.C' (modularSite (F.site .EXP 60 perm) (7::255::spill)).state .EXP=60
    rw [power_cost]
    change 10+50*(1+Nat.log 256 255)=60
    rw [Nat.log_of_lt (by decide : 255<256)]
  · change EVM.C' (modularSite (F.site .EXP 110 perm) (7::256::spill)).state .EXP=110
    rw [power_cost]
    change 10+50*(1+Nat.log 256 256)=110
    rw [show Nat.log 256 256=1 by
      simpa only [Nat.pow_one] using Nat.log_pow (by decide : 1<256) 1]
  · let image := modularSite (F.site .EXP 59 perm) (7::3::spill)
    have expansion : EVM.memoryExpansionCost image.state .EXP=0 := by
      simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
    have charge : image.state.gasAvailable-UInt256.ofNat 0=image.state.gasAvailable := by
      change UInt256.mk (image.state.gasAvailable.val-0)=_
      rw [sub_zero]
    have cost : EVM.C' image.state .EXP=60 := exp_three_cost 59 perm
    have gate : Assembly.driverGate #[] image.state .EXP=.error .OutOfGass := by
      simp only [Assembly.driverGate]
      rw [expansion,charge,cost]
      rfl
    change Assembly.driverSteps 1 2 #[] image.state=_
    simp only [Assembly.driverSteps]
    rw [decode_exp image]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]

theorem exp_complete_observation (perm : Bool) :
    let next := F.observed .EXP 60 perm 60 7 3 spill 343
    next.stack=[u 343,u 258,u 513] ∧ next.stack≠[u 2187,u 258,u 513] ∧
    next.stack≠[u 343,u 513,u 258] ∧
    next.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x0a,0] ∧
    next.pc=u 4 ∧ next.gasAvailable=u 0 ∧ next.execLength=42 ∧
    next.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    next.returnData.data.toList=[0xcc,0xdd] ∧ next.H_return.data.toList=[0xee,0xff] ∧
    next.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧ next.accountMap=accounts ∧ next.σ₀=accounts := by
  refine ⟨rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 343,u 258,u 513]≠[u 2187,u 258,u 513];decide
  · change [u 343,u 258,u 513]≠[u 343,u 513,u 258];decide

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.exp_nonzero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exp_nonzero_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.exp_zero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exp_zero_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.exp_resource_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exp_resource_boundary
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.exp_complete_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exp_complete_observation

#print axioms sub_client
#print axioms sub_wrap_client
#print axioms sub_complete_observation
#print axioms sub_resource_order

#print axioms add_client
#print axioms mul_client
#print axioms boundaries
#print axioms complete_observation
#print axioms ir_frame
#print axioms resource_separation
#print axioms stack_failure
#print axioms frame_separation

private theorem five_shape (op : Backend.Op) (a b result : Scalar.Word) (perm : Bool) :
    (Assembly.chargedPrepare (F.input op 12 perm (a::b::spill)) 5).replaceStackAndIncrPC
      ((result::spill).map (fun w=>UInt256.mk w.toFin))=nativeExpected op 5 a b result perm := by
  first | rfl | (simp only [F.input,nativeExpected,F.observed,WrappingArithmeticFixtures.input,
    WrappingArithmeticFixtures.observed,WrappingArithmeticFixtures.site,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
    WordPushFixtures.seed,WordPushFixtures.u,WordPushFixtures.before];rfl)

theorem div_client (a b : Scalar.Word) (perm : Bool) :
    let result := (if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat / b.toNat))
    Solidity.Evm.Instr.step .div (ir a b)=.ok (irExpected a b result) 0 ∧
    Scalar.run Selection.divCertificate.code (a::b::spill)=some (result::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .DIV 12 perm (a::b::spill))=
      .ok (nativeExpected .DIV 5 a b result perm) ∧
    EVM.X 2 #[] (F.input .DIV 12 perm (a::b::spill))=
      EVM.X 1 #[] (nativeExpected .DIV 5 a b result perm) := by
  dsimp only
  have h := InstructionSelectionAgreement.div (F.site .DIV 12 perm) a b spill (ir a b)
    rfl (by decide) (by change 5≤12;decide) 0
  dsimp only at h
  have shape := five_shape .DIV a b (if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat / b.toNat)) perm
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem mod_client (a b : Scalar.Word) (perm : Bool) :
    let result := (if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat % b.toNat))
    Solidity.Evm.Instr.step .mod (ir a b)=.ok (irExpected a b result) 0 ∧
    Scalar.run Selection.modCertificate.code (a::b::spill)=some (result::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .MOD 12 perm (a::b::spill))=
      .ok (nativeExpected .MOD 5 a b result perm) ∧
    EVM.X 2 #[] (F.input .MOD 12 perm (a::b::spill))=
      EVM.X 1 #[] (nativeExpected .MOD 5 a b result perm) := by
  dsimp only
  have h := InstructionSelectionAgreement.mod (F.site .MOD 12 perm) a b spill (ir a b)
    rfl (by decide) (by change 5≤12;decide) 0
  dsimp only at h
  have shape := five_shape .MOD a b (if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat % b.toNat)) perm
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

/-- Raw target zero-divisor behavior, not a checked-source guard. -/
theorem div_mod_zero (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .DIV 12 perm (17::0::spill))=
      .ok (nativeExpected .DIV 5 17 0 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .MOD 12 perm (17::0::spill))=
      .ok (nativeExpected .MOD 5 17 0 0 perm) := by
  exact ⟨(div_client 17 0 perm).2.2.1,(mod_client 17 0 perm).2.2.1⟩

theorem div_high_bit (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .DIV 12 perm (BitVec.ofNat 256 (2^255)::2::spill))=
      .ok (nativeExpected .DIV 5 (BitVec.ofNat 256 (2^255)) 2 (BitVec.ofNat 256 (2^254)) perm) := by
  have h := (div_client (BitVec.ofNat 256 (2^255)) 2 perm).2.2.1
  have value : (if (2 : Scalar.Word) == 0 then (0 : Scalar.Word) else
      BitVec.ofNat 256 ((BitVec.ofNat 256 (2^255)).toNat / (2 : Scalar.Word).toNat))=
        BitVec.ofNat 256 (2^254) := by decide
  rw [value] at h
  exact h

theorem div_mod_complete_observation (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .DIV 12 perm (17::5::spill))=
      .ok (nativeExpected .DIV 5 17 5 3 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .MOD 12 perm (17::5::spill))=
      .ok (nativeExpected .MOD 5 17 5 2 perm) ∧
    (nativeExpected .DIV 5 17 5 3 perm).stack=[u 3,u 258,u 513] ∧
    (nativeExpected .MOD 5 17 5 2 perm).stack=[u 2,u 258,u 513] ∧
    (nativeExpected .DIV 5 17 5 3 perm).stack≠[u 0,u 258,u 513] ∧
    (nativeExpected .MOD 5 17 5 2 perm).stack≠[u 2,u 513,u 258] ∧
    (nativeExpected .DIV 5 17 5 3 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x04,0] ∧
    (nativeExpected .MOD 5 17 5 2 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x06,0] ∧
    (nativeExpected .DIV 5 17 5 3 perm).pc=u 4 ∧
    (nativeExpected .DIV 5 17 5 3 perm).gasAvailable=u 7 ∧
    (nativeExpected .DIV 5 17 5 3 perm).execLength=42 ∧
    (nativeExpected .DIV 5 17 5 3 perm).memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    (nativeExpected .DIV 5 17 5 3 perm).returnData.data.toList=[0xcc,0xdd] ∧
    (nativeExpected .DIV 5 17 5 3 perm).H_return.data.toList=[0xee,0xff] ∧
    (nativeExpected .DIV 5 17 5 3 perm).executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    (nativeExpected .DIV 5 17 5 3 perm).accountMap=accounts ∧
    (nativeExpected .DIV 5 17 5 3 perm).σ₀=accounts := by
  refine ⟨(div_client 17 5 perm).2.2.1,(mod_client 17 5 perm).2.2.1,rfl,rfl,?_,?_,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 3,u 258,u 513]≠[u 0,u 258,u 513];decide
  · change [u 2,u 258,u 513]≠[u 2,u 513,u 258];decide

theorem div_mod_resource_order (perm : Bool) :
    Solidity.Evm.Instr.step .div (ir 17 0)=.ok (irExpected 17 0 0) 0 ∧
    Assembly.driverSteps 1 2 #[] (F.input .DIV 4 perm (17::5::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .MOD 4 perm (17::0::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .DIV 4 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .MOD 4 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .DIV 5 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (F.input .MOD 5 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (F.input .DIV 12 perm (17::5::spill))=.error .OutOfFuel := by
  cases perm <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.div_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms div_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.mod_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mod_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.div_mod_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms div_mod_zero
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.div_high_bit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms div_high_bit
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.div_mod_complete_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms div_mod_complete_observation
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.div_mod_resource_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms div_mod_resource_order

private theorem three_shape (op : Backend.Op) (count value result : Scalar.Word) (perm : Bool) :
    (Assembly.chargedPrepare (F.input op 12 perm (count::value::spill)) 3).replaceStackAndIncrPC
      ((result::spill).map (fun w=>UInt256.mk w.toFin))=nativeExpected op 3 count value result perm := by
  first | rfl | (simp only [F.input,nativeExpected,F.observed,WrappingArithmeticFixtures.input,
    WrappingArithmeticFixtures.observed,WrappingArithmeticFixtures.site,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
    WordPushFixtures.seed,WordPushFixtures.u,WordPushFixtures.before];rfl)

theorem shl_client (count value : Scalar.Word) (perm : Bool) :
    let result := (if count.toNat < 256 then value <<< count.toNat else (0 : Scalar.Word))
    Solidity.Evm.Instr.step .shl (ir count value)=.ok (irExpected count value result) 0 ∧
    Scalar.run Selection.shlCertificate.code (count::value::spill)=some (result::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SHL 12 perm (count::value::spill))=
      .ok (nativeExpected .SHL 3 count value result perm) ∧
    EVM.X 2 #[] (F.input .SHL 12 perm (count::value::spill))=
      EVM.X 1 #[] (nativeExpected .SHL 3 count value result perm) := by
  dsimp only
  have h := InstructionSelectionAgreement.shl (F.site .SHL 12 perm) count value spill (ir count value)
    rfl (by decide) (by change 3≤12;decide) 0
  dsimp only at h
  have shape := three_shape .SHL count value (if count.toNat < 256 then value <<< count.toNat else (0 : Scalar.Word)) perm
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem shr_client (count value : Scalar.Word) (perm : Bool) :
    let result := (if count.toNat < 256 then value >>> count.toNat else (0 : Scalar.Word))
    Solidity.Evm.Instr.step .shr (ir count value)=.ok (irExpected count value result) 0 ∧
    Scalar.run Selection.shrCertificate.code (count::value::spill)=some (result::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SHR 12 perm (count::value::spill))=
      .ok (nativeExpected .SHR 3 count value result perm) ∧
    EVM.X 2 #[] (F.input .SHR 12 perm (count::value::spill))=
      EVM.X 1 #[] (nativeExpected .SHR 3 count value result perm) := by
  dsimp only
  have h := InstructionSelectionAgreement.shr (F.site .SHR 12 perm) count value spill (ir count value)
    rfl (by decide) (by change 3≤12;decide) 0
  dsimp only at h
  have shape := three_shape .SHR count value (if count.toNat < 256 then value >>> count.toNat else (0 : Scalar.Word)) perm
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem shifts_boundary (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SHL 12 perm (255::1::spill))=
      .ok (nativeExpected .SHL 3 255 1 (BitVec.ofNat 256 (2^255)) perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SHR 12 perm (255::BitVec.ofNat 256 (2^255)::spill))=
      .ok (nativeExpected .SHR 3 255 (BitVec.ofNat 256 (2^255)) 1 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SHL 12 perm (256::1::spill))=
      .ok (nativeExpected .SHL 3 256 1 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SHR 12 perm (256::511::spill))=
      .ok (nativeExpected .SHR 3 256 511 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SHR 12 perm (BitVec.ofNat 256 (2^256-1)::511::spill))=
      .ok (nativeExpected .SHR 3 (BitVec.ofNat 256 (2^256-1)) 511 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SHL 12 perm (0::511::spill))=
      .ok (nativeExpected .SHL 3 0 511 511 perm) := by
  exact ⟨(shl_client 255 1 perm).2.2.1,(shr_client 255 (BitVec.ofNat 256 (2^255)) perm).2.2.1,
    (shl_client 256 1 perm).2.2.1,
    (shr_client 256 511 perm).2.2.1,(shr_client (BitVec.ofNat 256 (2^256-1)) 511 perm).2.2.1,
    (shl_client 0 511 perm).2.2.1⟩

theorem shifts_complete_observation (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SHL 12 perm (2::3::spill))=
      .ok (nativeExpected .SHL 3 2 3 12 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SHR 12 perm (2::12::spill))=
      .ok (nativeExpected .SHR 3 2 12 3 perm) ∧
    (nativeExpected .SHL 3 2 3 12 perm).stack=[u 12,u 258,u 513] ∧
    (nativeExpected .SHL 3 2 3 12 perm).stack≠[u 16,u 258,u 513] ∧
    (nativeExpected .SHR 3 2 12 3 perm).stack=[u 3,u 258,u 513] ∧
    (nativeExpected .SHR 3 2 12 3 perm).stack≠[u 3,u 513,u 258] ∧
    (nativeExpected .SHL 3 256 1 0 perm).stack≠[u 1,u 258,u 513] ∧
    (nativeExpected .SHL 3 2 3 12 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x1b,0] ∧
    (nativeExpected .SHR 3 2 12 3 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x1c,0] ∧
    (nativeExpected .SHL 3 2 3 12 perm).pc=u 4 ∧
    (nativeExpected .SHL 3 2 3 12 perm).gasAvailable=u 9 ∧
    (nativeExpected .SHL 3 2 3 12 perm).execLength=42 ∧
    (nativeExpected .SHL 3 2 3 12 perm).memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    (nativeExpected .SHL 3 2 3 12 perm).returnData.data.toList=[0xcc,0xdd] ∧
    (nativeExpected .SHL 3 2 3 12 perm).H_return.data.toList=[0xee,0xff] ∧
    (nativeExpected .SHL 3 2 3 12 perm).executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    (nativeExpected .SHL 3 2 3 12 perm).accountMap=accounts ∧
    (nativeExpected .SHL 3 2 3 12 perm).σ₀=accounts := by
  refine ⟨(shl_client 2 3 perm).2.2.1,(shr_client 2 12 perm).2.2.1,rfl,?_,rfl,?_,?_,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 12,u 258,u 513]≠[u 16,u 258,u 513];decide
  · change [u 3,u 258,u 513]≠[u 3,u 513,u 258];decide
  · change [u 0,u 258,u 513]≠[u 1,u 258,u 513];decide

theorem shifts_resource_order (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SHL 2 perm (2::3::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .SHR 2 perm (2::12::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .SHL 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .SHR 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .SHL 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (F.input .SHR 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (F.input .SHL 12 perm (2::3::spill))=.error .OutOfFuel := by
  cases perm <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.shl_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shl_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.shr_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shr_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.shifts_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifts_boundary
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.shifts_complete_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifts_complete_observation
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.shifts_resource_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifts_resource_order

def unaryExpected (a result : Scalar.Word) (perm : Bool) : EVM.State :=
  {F.input .ISZERO 12 perm (a::spill) with
    pc:=u 4,gasAvailable:=u 9,execLength:=42,
    stack:=(result::spill).map (fun w=>UInt256.mk w.toFin)}

theorem eq_client (a b : Scalar.Word) (perm : Bool) :
    Solidity.Evm.Instr.step .eq (ir a b)=.ok (irExpected a b (Scalar.flag (a == b))) 0 ∧
    Scalar.run Selection.eqCertificate.code (a::b::spill)=some (Scalar.flag (a == b)::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .EQ 12 perm (a::b::spill))=
      .ok (nativeExpected .EQ 3 a b (Scalar.flag (a == b)) perm) ∧
    EVM.X 2 #[] (F.input .EQ 12 perm (a::b::spill))=
      EVM.X 1 #[] (nativeExpected .EQ 3 a b (Scalar.flag (a == b)) perm) := by
  have h := InstructionSelectionAgreement.eq #[] (F.site .EQ 12 perm) a b spill (ir a b)
    rfl (by decide) (by change 3≤12;decide) 0
  dsimp only at h
  have shape := three_shape .EQ a b (Scalar.flag (a == b)) perm
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem iszero_client (a : Scalar.Word) (perm : Bool) :
    Solidity.Evm.Instr.step .iszero {ir a 0 with stack:=Selection.irStack (a::spill)}=
      .ok {ir a 0 with stack:=Selection.irStack (Scalar.flag (a == 0)::spill)} 0 ∧
    Scalar.run Selection.iszeroCertificate.code (a::spill)=some (Scalar.flag (a == 0)::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .ISZERO 12 perm (a::spill))=
      .ok (unaryExpected a (Scalar.flag (a == 0)) perm) ∧
    EVM.X 2 #[] (F.input .ISZERO 12 perm (a::spill))=
      EVM.X 1 #[] (unaryExpected a (Scalar.flag (a == 0)) perm) := by
  have h := InstructionSelectionAgreement.iszero #[] (F.site .ISZERO 12 perm) a spill
    {ir a 0 with stack:=Selection.irStack (a::spill)} rfl (by decide) (by change 3≤12;decide) 0
  dsimp only at h
  have shape : (Assembly.chargedPrepare (F.input .ISZERO 12 perm (a::spill)) 3).replaceStackAndIncrPC
      ((Scalar.flag (a == 0)::spill).map (fun w=>UInt256.mk w.toFin))=
        unaryExpected a (Scalar.flag (a == 0)) perm := by
    first | rfl | (simp only [F.input,WrappingArithmeticFixtures.input,WrappingArithmeticFixtures.site,
      unaryExpected,modularSite,Site.state,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,
      EVM.State.incrPC,WordPushFixtures.seed,WordPushFixtures.u,WordPushFixtures.before];rfl)
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem flags_full_word_cases (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .EQ 12 perm (1::257::spill))=
      .ok (nativeExpected .EQ 3 1 257 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .EQ 12 perm (257::257::spill))=
      .ok (nativeExpected .EQ 3 257 257 1 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .ISZERO 12 perm (0::spill))=
      .ok (unaryExpected 0 1 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .ISZERO 12 perm (256::spill))=
      .ok (unaryExpected 256 0 perm) := by
  exact ⟨(eq_client 1 257 perm).2.2.1,(eq_client 257 257 perm).2.2.1,
    (iszero_client 0 perm).2.2.1,(iszero_client 256 perm).2.2.1⟩

theorem flags_complete_observation (perm : Bool) :
    (nativeExpected .EQ 3 1 257 0 perm).stack=[u 0,u 258,u 513] ∧
    (unaryExpected 256 0 perm).stack=[u 0,u 258,u 513] ∧
    (unaryExpected 0 1 perm).stack=[u 1,u 258,u 513] ∧
    (nativeExpected .EQ 3 1 257 0 perm).stack≠[u 1,u 258,u 513] ∧
    (unaryExpected 256 0 perm).stack≠[u 1,u 258,u 513] ∧
    (unaryExpected 0 1 perm).stack≠[u 1,u 513,u 258] ∧
    (nativeExpected .EQ 3 1 257 0 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x14,0] ∧
    (unaryExpected 256 0 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x15,0] ∧
    (unaryExpected 256 0 perm).pc=u 4 ∧ (unaryExpected 256 0 perm).gasAvailable=u 9 ∧
    (unaryExpected 256 0 perm).execLength=42 ∧
    (unaryExpected 256 0 perm).memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    (unaryExpected 256 0 perm).returnData.data.toList=[0xcc,0xdd] ∧
    (unaryExpected 256 0 perm).H_return.data.toList=[0xee,0xff] ∧
    (unaryExpected 256 0 perm).executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    (unaryExpected 256 0 perm).accountMap=accounts ∧ (unaryExpected 256 0 perm).σ₀=accounts := by
  refine ⟨rfl,rfl,rfl,?_,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 0,u 258,u 513]≠[u 1,u 258,u 513];decide
  · change [u 0,u 258,u 513]≠[u 1,u 258,u 513];decide
  · change [u 1,u 258,u 513]≠[u 1,u 513,u 258];decide

theorem flags_resource_order (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .EQ 2 perm (1::257::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .ISZERO 2 perm (256::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .EQ 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .ISZERO 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .EQ 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (F.input .ISZERO 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (F.input .EQ 0 perm [])=.error .OutOfFuel := by
  cases perm <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.eq_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eq_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.iszero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms iszero_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.flags_full_word_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms flags_full_word_cases
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.flags_complete_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms flags_complete_observation
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.flags_resource_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms flags_resource_order

theorem lt_client (a b : Scalar.Word) (perm : Bool) :
    Solidity.Evm.Instr.step .lt (ir a b)=.ok (irExpected a b (Scalar.flag (decide (a.toNat < b.toNat)))) 0 ∧
    Scalar.run Selection.ltCertificate.code (a::b::spill)=some (Scalar.flag (decide (a.toNat < b.toNat))::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .LT 12 perm (a::b::spill))=
      .ok (nativeExpected .LT 3 a b (Scalar.flag (decide (a.toNat < b.toNat))) perm) ∧
    EVM.X 2 #[] (F.input .LT 12 perm (a::b::spill))=
      EVM.X 1 #[] (nativeExpected .LT 3 a b (Scalar.flag (decide (a.toNat < b.toNat))) perm) := by
  have h := InstructionSelectionAgreement.lt #[] (F.site .LT 12 perm) a b spill (ir a b)
    rfl (by decide) (by change 3≤12;decide) 0
  dsimp only at h
  have shape := three_shape .LT a b (Scalar.flag (decide (a.toNat < b.toNat))) perm
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem gt_client (a b : Scalar.Word) (perm : Bool) :
    Solidity.Evm.Instr.step .gt (ir a b)=.ok (irExpected a b (Scalar.flag (decide (a.toNat > b.toNat)))) 0 ∧
    Scalar.run Selection.gtCertificate.code (a::b::spill)=some (Scalar.flag (decide (a.toNat > b.toNat))::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .GT 12 perm (a::b::spill))=
      .ok (nativeExpected .GT 3 a b (Scalar.flag (decide (a.toNat > b.toNat))) perm) ∧
    EVM.X 2 #[] (F.input .GT 12 perm (a::b::spill))=
      EVM.X 1 #[] (nativeExpected .GT 3 a b (Scalar.flag (decide (a.toNat > b.toNat))) perm) := by
  have h := InstructionSelectionAgreement.gt #[] (F.site .GT 12 perm) a b spill (ir a b)
    rfl (by decide) (by change 3≤12;decide) 0
  dsimp only at h
  have shape := three_shape .GT a b (Scalar.flag (decide (a.toNat > b.toNat))) perm
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem order_full_word_cases (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .LT 12 perm (1::257::spill))=
      .ok (nativeExpected .LT 3 1 257 1 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .GT 12 perm (1::257::spill))=
      .ok (nativeExpected .GT 3 1 257 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .LT 12 perm (17::17::spill))=
      .ok (nativeExpected .LT 3 17 17 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .GT 12 perm (17::17::spill))=
      .ok (nativeExpected .GT 3 17 17 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .GT 12 perm (BitVec.ofNat 256 (2^255)::1::spill))=
      .ok (nativeExpected .GT 3 (BitVec.ofNat 256 (2^255)) 1 1 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .LT 12 perm (BitVec.ofNat 256 (2^255)::1::spill))=
      .ok (nativeExpected .LT 3 (BitVec.ofNat 256 (2^255)) 1 0 perm) := by
  exact ⟨(lt_client 1 257 perm).2.2.1,(gt_client 1 257 perm).2.2.1,
    (lt_client 17 17 perm).2.2.1,(gt_client 17 17 perm).2.2.1,
    (gt_client (BitVec.ofNat 256 (2^255)) 1 perm).2.2.1,
    (lt_client (BitVec.ofNat 256 (2^255)) 1 perm).2.2.1⟩

theorem order_complete_observation (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .GT 12 perm (257::1::spill))=
      .ok (nativeExpected .GT 3 257 1 1 perm) ∧
    (nativeExpected .LT 3 1 257 1 perm).stack=[u 1,u 258,u 513] ∧
    (nativeExpected .GT 3 257 1 1 perm).stack=[u 1,u 258,u 513] ∧
    (nativeExpected .LT 3 1 257 1 perm).stack≠[u 0,u 258,u 513] ∧
    (nativeExpected .GT 3 257 1 1 perm).stack≠[u 1,u 513,u 258] ∧
    (nativeExpected .LT 3 1 257 1 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x10,0] ∧
    (nativeExpected .GT 3 257 1 1 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x11,0] ∧
    (nativeExpected .LT 3 1 257 1 perm).pc=u 4 ∧
    (nativeExpected .LT 3 1 257 1 perm).gasAvailable=u 9 ∧
    (nativeExpected .LT 3 1 257 1 perm).execLength=42 ∧
    (nativeExpected .LT 3 1 257 1 perm).memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    (nativeExpected .LT 3 1 257 1 perm).returnData.data.toList=[0xcc,0xdd] ∧
    (nativeExpected .LT 3 1 257 1 perm).H_return.data.toList=[0xee,0xff] ∧
    (nativeExpected .LT 3 1 257 1 perm).executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    (nativeExpected .LT 3 1 257 1 perm).accountMap=accounts ∧
    (nativeExpected .LT 3 1 257 1 perm).σ₀=accounts := by
  refine ⟨(gt_client 257 1 perm).2.2.1,rfl,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 1,u 258,u 513]≠[u 0,u 258,u 513];decide
  · change [u 1,u 258,u 513]≠[u 1,u 513,u 258];decide

theorem order_resource_priority (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .LT 2 perm (1::257::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .GT 2 perm (257::1::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .LT 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .GT 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .LT 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (F.input .GT 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (F.input .LT 0 perm [])=.error .OutOfFuel := by
  cases perm <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.lt_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lt_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.gt_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms gt_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.order_full_word_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms order_full_word_cases
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.order_complete_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms order_complete_observation
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.order_resource_priority' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms order_resource_priority
theorem bitAnd_client (a b : Scalar.Word) (perm : Bool) :
    Solidity.Evm.Instr.step .and (ir a b)=.ok (irExpected a b ((a &&& b))) 0 ∧
    Scalar.run Selection.andCertificate.code (a::b::spill)=some ((a &&& b)::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .AND 12 perm (a::b::spill))=
      .ok (nativeExpected .AND 3 a b ((a &&& b)) perm) ∧
    EVM.X 2 #[] (F.input .AND 12 perm (a::b::spill))=
      EVM.X 1 #[] (nativeExpected .AND 3 a b ((a &&& b)) perm) := by
  have h := InstructionSelectionAgreement.bitAnd (F.site .AND 12 perm) a b spill (ir a b)
    rfl (by decide) (by change 3≤12;decide) 0
  dsimp only at h
  have shape := three_shape .AND a b ((a &&& b)) perm
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem bitOr_client (a b : Scalar.Word) (perm : Bool) :
    Solidity.Evm.Instr.step .or (ir a b)=.ok (irExpected a b ((a ||| b))) 0 ∧
    Scalar.run Selection.orCertificate.code (a::b::spill)=some ((a ||| b)::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .OR 12 perm (a::b::spill))=
      .ok (nativeExpected .OR 3 a b ((a ||| b)) perm) ∧
    EVM.X 2 #[] (F.input .OR 12 perm (a::b::spill))=
      EVM.X 1 #[] (nativeExpected .OR 3 a b ((a ||| b)) perm) := by
  have h := InstructionSelectionAgreement.bitOr (F.site .OR 12 perm) a b spill (ir a b)
    rfl (by decide) (by change 3≤12;decide) 0
  dsimp only at h
  have shape := three_shape .OR a b ((a ||| b)) perm
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem and_or_full_word_cases (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .AND 12 perm (240::60::spill))=
      .ok (nativeExpected .AND 3 240 60 48 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .OR 12 perm (240::60::spill))=
      .ok (nativeExpected .OR 3 240 60 252 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .AND 12 perm (1::257::spill))=
      .ok (nativeExpected .AND 3 1 257 1 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .OR 12 perm (1::257::spill))=
      .ok (nativeExpected .OR 3 1 257 257 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .AND 12 perm (BitVec.ofNat 256 (2^255)::0::spill))=
      .ok (nativeExpected .AND 3 (BitVec.ofNat 256 (2^255)) 0 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .OR 12 perm (BitVec.ofNat 256 (2^255)::0::spill))=
      .ok (nativeExpected .OR 3 (BitVec.ofNat 256 (2^255)) 0 (BitVec.ofNat 256 (2^255)) perm) := by
  exact ⟨(bitAnd_client 240 60 perm).2.2.1,(bitOr_client 240 60 perm).2.2.1,
    (bitAnd_client 1 257 perm).2.2.1,(bitOr_client 1 257 perm).2.2.1,
    (bitAnd_client (BitVec.ofNat 256 (2^255)) 0 perm).2.2.1,
    (bitOr_client (BitVec.ofNat 256 (2^255)) 0 perm).2.2.1⟩

theorem and_or_complete_observation (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .OR 12 perm (240::60::spill))=
      .ok (nativeExpected .OR 3 240 60 252 perm) ∧
    (nativeExpected .AND 3 240 60 48 perm).stack=[u 48,u 258,u 513] ∧
    (nativeExpected .OR 3 240 60 252 perm).stack=[u 252,u 258,u 513] ∧
    (nativeExpected .AND 3 240 60 48 perm).stack≠[u 0,u 258,u 513] ∧
    (nativeExpected .OR 3 240 60 252 perm).stack≠[u 252,u 513,u 258] ∧
    (nativeExpected .AND 3 240 60 48 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x16,0] ∧
    (nativeExpected .OR 3 240 60 252 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x17,0] ∧
    (nativeExpected .AND 3 240 60 48 perm).pc=u 4 ∧
    (nativeExpected .AND 3 240 60 48 perm).gasAvailable=u 9 ∧
    (nativeExpected .AND 3 240 60 48 perm).execLength=42 ∧
    (nativeExpected .AND 3 240 60 48 perm).memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    (nativeExpected .AND 3 240 60 48 perm).returnData.data.toList=[0xcc,0xdd] ∧
    (nativeExpected .AND 3 240 60 48 perm).H_return.data.toList=[0xee,0xff] ∧
    (nativeExpected .AND 3 240 60 48 perm).executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    (nativeExpected .AND 3 240 60 48 perm).accountMap=accounts ∧
    (nativeExpected .AND 3 240 60 48 perm).σ₀=accounts := by
  refine ⟨(bitOr_client 240 60 perm).2.2.1,rfl,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 48,u 258,u 513]≠[u 0,u 258,u 513];decide
  · change [u 252,u 258,u 513]≠[u 252,u 513,u 258];decide

theorem and_or_resource_priority (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .AND 2 perm (1::257::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .OR 2 perm (257::1::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .AND 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .OR 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .AND 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (F.input .OR 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (F.input .AND 0 perm [])=.error .OutOfFuel := by
  cases perm <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.bitAnd_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bitAnd_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.bitOr_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bitOr_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.and_or_full_word_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms and_or_full_word_cases
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.and_or_complete_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms and_or_complete_observation
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.and_or_resource_priority' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms and_or_resource_priority
theorem bitXor_client (a b : Scalar.Word) (perm : Bool) :
    Solidity.Evm.Instr.step .xor (ir a b)=.ok (irExpected a b ((a ^^^ b))) 0 ∧
    Scalar.run Selection.xorCertificate.code (a::b::spill)=some ((a ^^^ b)::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .XOR 12 perm (a::b::spill))=
      .ok (nativeExpected .XOR 3 a b ((a ^^^ b)) perm) ∧
    EVM.X 2 #[] (F.input .XOR 12 perm (a::b::spill))=
      EVM.X 1 #[] (nativeExpected .XOR 3 a b ((a ^^^ b)) perm) := by
  have h := InstructionSelectionAgreement.bitXor (F.site .XOR 12 perm) a b spill (ir a b)
    rfl (by decide) (by change 3≤12;decide) 0
  dsimp only at h
  have shape := three_shape .XOR a b ((a ^^^ b)) perm
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem xor_full_word_cases (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .XOR 12 perm (240::60::spill))=
      .ok (nativeExpected .XOR 3 240 60 204 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .XOR 12 perm (1::257::spill))=
      .ok (nativeExpected .XOR 3 1 257 256 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .XOR 12 perm (257::257::spill))=
      .ok (nativeExpected .XOR 3 257 257 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .XOR 12 perm (BitVec.ofNat 256 (2^255)::0::spill))=
      .ok (nativeExpected .XOR 3 (BitVec.ofNat 256 (2^255)) 0 (BitVec.ofNat 256 (2^255)) perm) := by
  exact ⟨(bitXor_client 240 60 perm).2.2.1,(bitXor_client 1 257 perm).2.2.1,
    (bitXor_client 257 257 perm).2.2.1,(bitXor_client (BitVec.ofNat 256 (2^255)) 0 perm).2.2.1⟩

theorem xor_complete_observation (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .XOR 12 perm (1::257::spill))=
      .ok (nativeExpected .XOR 3 1 257 256 perm) ∧
    (nativeExpected .XOR 3 1 257 256 perm).stack=[u 256,u 258,u 513] ∧
    (nativeExpected .XOR 3 1 257 256 perm).stack≠[u 0,u 258,u 513] ∧
    (nativeExpected .XOR 3 1 257 256 perm).stack≠[u 256,u 513,u 258] ∧
    (nativeExpected .XOR 3 1 257 256 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x18,0] ∧
    (nativeExpected .XOR 3 1 257 256 perm).pc=u 4 ∧
    (nativeExpected .XOR 3 1 257 256 perm).gasAvailable=u 9 ∧
    (nativeExpected .XOR 3 1 257 256 perm).execLength=42 ∧
    (nativeExpected .XOR 3 1 257 256 perm).memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    (nativeExpected .XOR 3 1 257 256 perm).returnData.data.toList=[0xcc,0xdd] ∧
    (nativeExpected .XOR 3 1 257 256 perm).H_return.data.toList=[0xee,0xff] ∧
    (nativeExpected .XOR 3 1 257 256 perm).executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    (nativeExpected .XOR 3 1 257 256 perm).accountMap=accounts ∧
    (nativeExpected .XOR 3 1 257 256 perm).σ₀=accounts := by
  refine ⟨(bitXor_client 1 257 perm).2.2.1,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 256,u 258,u 513]≠[u 0,u 258,u 513];decide
  · change [u 256,u 258,u 513]≠[u 256,u 513,u 258];decide

theorem xor_resource_priority (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .XOR 2 perm (1::257::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .XOR 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .XOR 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (F.input .XOR 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.bitXor_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bitXor_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.xor_full_word_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms xor_full_word_cases
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.xor_complete_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms xor_complete_observation
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.xor_resource_priority' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms xor_resource_priority
def notExpected (a result : Scalar.Word) (perm : Bool) : EVM.State :=
  {F.input .NOT 12 perm (a::spill) with
    pc:=u 4,gasAvailable:=u 9,execLength:=42,
    stack:=(result::spill).map (fun w=>UInt256.mk w.toFin)}

theorem bitNot_client (a : Scalar.Word) (perm : Bool) :
    Solidity.Evm.Instr.step .not {ir a 0 with stack:=Selection.irStack (a::spill)}=
      .ok {ir a 0 with stack:=Selection.irStack ((~~~a)::spill)} 0 ∧
    Scalar.run Selection.notCertificate.code (a::spill)=some ((~~~a)::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .NOT 12 perm (a::spill))=
      .ok (notExpected a ((~~~a)) perm) ∧
    EVM.X 2 #[] (F.input .NOT 12 perm (a::spill))=
      EVM.X 1 #[] (notExpected a ((~~~a)) perm) := by
  have h := InstructionSelectionAgreement.bitNot #[] (F.site .NOT 12 perm) a spill
    {ir a 0 with stack:=Selection.irStack (a::spill)} rfl (by decide) (by change 3≤12;decide) 0
  dsimp only at h
  have shape : (Assembly.chargedPrepare (F.input .NOT 12 perm (a::spill)) 3).replaceStackAndIncrPC
      (((~~~a)::spill).map (fun w=>UInt256.mk w.toFin))=
        notExpected a ((~~~a)) perm := by
    first | rfl | (simp only [F.input,WrappingArithmeticFixtures.input,WrappingArithmeticFixtures.site,
      notExpected,modularSite,Site.state,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,
      EVM.State.incrPC,WordPushFixtures.seed,WordPushFixtures.u,WordPushFixtures.before];rfl)
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem not_full_word_cases (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .NOT 12 perm (0::spill))=
      .ok (notExpected 0 (BitVec.ofNat 256 ((2^256:Nat)-1)) perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .NOT 12 perm ((BitVec.ofNat 256 ((2^256:Nat)-1))::spill))=
      .ok (notExpected (BitVec.ofNat 256 ((2^256:Nat)-1)) 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .NOT 12 perm (256::spill))=
      .ok (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm) := by
  exact ⟨(bitNot_client 0 perm).2.2.1,
    (bitNot_client (BitVec.ofNat 256 ((2^256:Nat)-1)) perm).2.2.1,
    (bitNot_client 256 perm).2.2.1⟩

theorem not_complete_observation (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .NOT 12 perm (256::spill))=
      .ok (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm) ∧
    (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm).stack=[u ((2^256:Nat)-257),u 258,u 513] ∧
    (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm).stack≠[u 0,u 258,u 513] ∧
    (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm).stack≠[u ((2^256:Nat)-257),u 513,u 258] ∧
    (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x19,0] ∧
    (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm).pc=u 4 ∧
    (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm).gasAvailable=u 9 ∧
    (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm).execLength=42 ∧
    (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm).memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm).returnData.data.toList=[0xcc,0xdd] ∧
    (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm).H_return.data.toList=[0xee,0xff] ∧
    (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm).executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm).accountMap=accounts ∧
    (notExpected 256 (BitVec.ofNat 256 ((2^256:Nat)-257)) perm).σ₀=accounts := by
  refine ⟨(bitNot_client 256 perm).2.2.1,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u ((2^256:Nat)-257),u 258,u 513]≠[u 0,u 258,u 513];decide
  · change [u ((2^256:Nat)-257),u 258,u 513]≠[u ((2^256:Nat)-257),u 513,u 258];decide

theorem not_resource_priority (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .NOT 2 perm (256::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .NOT 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .NOT 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (F.input .NOT 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.bitNot_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bitNot_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.not_full_word_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms not_full_word_cases
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.not_complete_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms not_complete_observation
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.not_resource_priority' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms not_resource_priority
theorem slt_client (a b : Scalar.Word) (perm : Bool) :
    Solidity.Evm.Instr.step .slt (ir a b)=.ok (irExpected a b (Scalar.flag (decide (a.toInt < b.toInt)))) 0 ∧
    Scalar.run Selection.sltCertificate.code (a::b::spill)=some (Scalar.flag (decide (a.toInt < b.toInt))::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SLT 12 perm (a::b::spill))=
      .ok (nativeExpected .SLT 3 a b (Scalar.flag (decide (a.toInt < b.toInt))) perm) ∧
    EVM.X 2 #[] (F.input .SLT 12 perm (a::b::spill))=
      EVM.X 1 #[] (nativeExpected .SLT 3 a b (Scalar.flag (decide (a.toInt < b.toInt))) perm) := by
  have h := InstructionSelectionAgreement.slt #[] (F.site .SLT 12 perm) a b spill (ir a b)
    rfl (by decide) (by change 3≤12;decide) 0
  dsimp only at h
  have shape := three_shape .SLT a b (Scalar.flag (decide (a.toInt < b.toInt))) perm
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem slt_signed_cases (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SLT 12 perm ((BitVec.ofNat 256 ((2^256:Nat)-1))::1::spill))=
      .ok (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SLT 12 perm (1::(BitVec.ofNat 256 ((2^256:Nat)-1))::spill))=
      .ok (nativeExpected .SLT 3 1 (BitVec.ofNat 256 ((2^256:Nat)-1)) 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SLT 12 perm ((BitVec.ofNat 256 (2^255))::0::spill))=
      .ok (nativeExpected .SLT 3 (BitVec.ofNat 256 (2^255)) 0 1 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SLT 12 perm ((BitVec.ofNat 256 ((2^256:Nat)-1))::(BitVec.ofNat 256 ((2^256:Nat)-1))::spill))=
      .ok (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) (BitVec.ofNat 256 ((2^256:Nat)-1)) 0 perm) := by
  exact ⟨(slt_client (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 perm).2.2.1,
    (slt_client 1 (BitVec.ofNat 256 ((2^256:Nat)-1)) perm).2.2.1,
    (slt_client (BitVec.ofNat 256 (2^255)) 0 perm).2.2.1,
    (slt_client (BitVec.ofNat 256 ((2^256:Nat)-1)) (BitVec.ofNat 256 ((2^256:Nat)-1)) perm).2.2.1⟩

theorem slt_complete_observation (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SLT 12 perm ((BitVec.ofNat 256 ((2^256:Nat)-1))::1::spill))=
      .ok (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm) ∧
    (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm).stack=[u 1,u 258,u 513] ∧
    (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm).stack≠[u 0,u 258,u 513] ∧
    (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm).stack≠[u 1,u 513,u 258] ∧
    (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x12,0] ∧
    (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm).pc=u 4 ∧
    (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm).gasAvailable=u 9 ∧
    (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm).execLength=42 ∧
    (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm).memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm).returnData.data.toList=[0xcc,0xdd] ∧
    (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm).H_return.data.toList=[0xee,0xff] ∧
    (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm).executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm).accountMap=accounts ∧
    (nativeExpected .SLT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 1 perm).σ₀=accounts := by
  refine ⟨(slt_client (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 perm).2.2.1,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 1,u 258,u 513]≠[u 0,u 258,u 513];decide
  · change [u 1,u 258,u 513]≠[u 1,u 513,u 258];decide

theorem slt_resource_priority (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SLT 2 perm ((BitVec.ofNat 256 ((2^256:Nat)-1))::1::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .SLT 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .SLT 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (F.input .SLT 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.slt_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms slt_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.slt_signed_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms slt_signed_cases
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.slt_complete_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms slt_complete_observation
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.slt_resource_priority' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms slt_resource_priority
theorem sgt_client (a b : Scalar.Word) (perm : Bool) :
    Solidity.Evm.Instr.step .sgt (ir a b)=.ok (irExpected a b (Scalar.flag (decide (b.toInt < a.toInt)))) 0 ∧
    Scalar.run Selection.sgtCertificate.code (a::b::spill)=some (Scalar.flag (decide (b.toInt < a.toInt))::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SGT 12 perm (a::b::spill))=
      .ok (nativeExpected .SGT 3 a b (Scalar.flag (decide (b.toInt < a.toInt))) perm) ∧
    EVM.X 2 #[] (F.input .SGT 12 perm (a::b::spill))=
      EVM.X 1 #[] (nativeExpected .SGT 3 a b (Scalar.flag (decide (b.toInt < a.toInt))) perm) := by
  have h := InstructionSelectionAgreement.sgt (F.site .SGT 12 perm) a b spill (ir a b)
    rfl (by decide) (by change 3≤12;decide) 0
  dsimp only at h
  have shape := three_shape .SGT a b (Scalar.flag (decide (b.toInt < a.toInt))) perm
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem sgt_signed_cases (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SGT 12 perm ((BitVec.ofNat 256 ((2^256:Nat)-1))::1::spill))=
      .ok (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SGT 12 perm (1::(BitVec.ofNat 256 ((2^256:Nat)-1))::spill))=
      .ok (nativeExpected .SGT 3 1 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SGT 12 perm ((BitVec.ofNat 256 (2^255))::0::spill))=
      .ok (nativeExpected .SGT 3 (BitVec.ofNat 256 (2^255)) 0 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SGT 12 perm ((BitVec.ofNat 256 ((2^256:Nat)-1))::(BitVec.ofNat 256 ((2^256:Nat)-1))::spill))=
      .ok (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) (BitVec.ofNat 256 ((2^256:Nat)-1)) 0 perm) := by
  exact ⟨(sgt_client (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 perm).2.2.1,
    (sgt_client 1 (BitVec.ofNat 256 ((2^256:Nat)-1)) perm).2.2.1,
    (sgt_client (BitVec.ofNat 256 (2^255)) 0 perm).2.2.1,
    (sgt_client (BitVec.ofNat 256 ((2^256:Nat)-1)) (BitVec.ofNat 256 ((2^256:Nat)-1)) perm).2.2.1⟩
theorem sgt_complete_observation (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SGT 12 perm ((BitVec.ofNat 256 ((2^256:Nat)-1))::1::spill))=
      .ok (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm) ∧
    (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm).stack=[u 0,u 258,u 513] ∧
    (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm).stack≠[u 1,u 258,u 513] ∧
    (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm).stack≠[u 0,u 513,u 258] ∧
    (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x13,0] ∧
    (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm).pc=u 4 ∧
    (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm).gasAvailable=u 9 ∧
    (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm).execLength=42 ∧
    (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm).memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm).returnData.data.toList=[0xcc,0xdd] ∧
    (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm).H_return.data.toList=[0xee,0xff] ∧
    (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm).executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm).accountMap=accounts ∧
    (nativeExpected .SGT 3 (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 0 perm).σ₀=accounts := by
  refine ⟨(sgt_client (BitVec.ofNat 256 ((2^256:Nat)-1)) 1 perm).2.2.1,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 0,u 258,u 513]≠[u 1,u 258,u 513];decide
  · change [u 0,u 258,u 513]≠[u 0,u 513,u 258];decide
theorem sgt_resource_priority (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SGT 2 perm ((BitVec.ofNat 256 ((2^256:Nat)-1))::1::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .SGT 2 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .SGT 3 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (F.input .SGT 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.sgt_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sgt_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.sgt_signed_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sgt_signed_cases
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.sgt_complete_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sgt_complete_observation
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.sgt_resource_priority' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sgt_resource_priority
theorem sdiv_client (a b : Scalar.Word) (perm : Bool) :
    let result := (if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tdiv b.toInt))
    Solidity.Evm.Instr.step .sdiv (ir a b)=.ok (irExpected a b result) 0 ∧
    Scalar.run Selection.sdivCertificate.code (a::b::spill)=some (result::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SDIV 12 perm (a::b::spill))=
      .ok (nativeExpected .SDIV 5 a b result perm) ∧
    EVM.X 2 #[] (F.input .SDIV 12 perm (a::b::spill))=
      EVM.X 1 #[] (nativeExpected .SDIV 5 a b result perm) := by
  dsimp only
  have h := InstructionSelectionAgreement.sdiv (F.site .SDIV 12 perm) a b spill (ir a b)
    rfl (by decide) (by change 5≤12;decide) 0
  dsimp only at h
  have shape := five_shape .SDIV a b (if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tdiv b.toInt)) perm
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem sdiv_signed_cases (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SDIV 12 perm ((BitVec.ofInt 256 (-17))::5::spill))=
      .ok (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SDIV 12 perm (17::(BitVec.ofInt 256 (-5))::spill))=
      .ok (nativeExpected .SDIV 5 17 (BitVec.ofInt 256 (-5)) (BitVec.ofInt 256 (-3)) perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SDIV 12 perm ((BitVec.ofInt 256 (-17))::(BitVec.ofInt 256 (-5))::spill))=
      .ok (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) (BitVec.ofInt 256 (-5)) 3 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SDIV 12 perm (17::0::spill))=
      .ok (nativeExpected .SDIV 5 17 0 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SDIV 12 perm ((BitVec.ofNat 256 (2^255))::(BitVec.ofInt 256 (-1))::spill))=
      .ok (nativeExpected .SDIV 5 (BitVec.ofNat 256 (2^255)) (BitVec.ofInt 256 (-1)) (BitVec.ofNat 256 (2^255)) perm) := by
  exact ⟨(sdiv_client (BitVec.ofInt 256 (-17)) 5 perm).2.2.1,
    (sdiv_client 17 (BitVec.ofInt 256 (-5)) perm).2.2.1,
    (sdiv_client (BitVec.ofInt 256 (-17)) (BitVec.ofInt 256 (-5)) perm).2.2.1,
    (sdiv_client 17 0 perm).2.2.1,
    (sdiv_client (BitVec.ofNat 256 (2^255)) (BitVec.ofInt 256 (-1)) perm).2.2.1⟩

theorem sdiv_complete_observation (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SDIV 12 perm ((BitVec.ofInt 256 (-17))::5::spill))=
      .ok (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm) ∧
    (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm).stack=[u ((2^256:Nat)-3),u 258,u 513] ∧
    (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm).stack≠[u ((2^256:Nat)-4),u 258,u 513] ∧
    (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm).stack≠[u ((2^256:Nat)-3),u 513,u 258] ∧
    (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x05,0] ∧
    (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm).pc=u 4 ∧
    (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm).gasAvailable=u 7 ∧
    (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm).execLength=42 ∧
    (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm).memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm).returnData.data.toList=[0xcc,0xdd] ∧
    (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm).H_return.data.toList=[0xee,0xff] ∧
    (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm).executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm).accountMap=accounts ∧
    (nativeExpected .SDIV 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-3)) perm).σ₀=accounts := by
  refine ⟨(sdiv_client (BitVec.ofInt 256 (-17)) 5 perm).2.2.1,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u ((2^256:Nat)-3),u 258,u 513]≠[u ((2^256:Nat)-4),u 258,u 513];decide
  · change [u ((2^256:Nat)-3),u 258,u 513]≠[u ((2^256:Nat)-3),u 513,u 258];decide

theorem sdiv_resource_priority (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SDIV 4 perm ((BitVec.ofInt 256 (-17))::5::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .SDIV 4 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .SDIV 5 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (F.input .SDIV 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.sdiv_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sdiv_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.sdiv_signed_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sdiv_signed_cases
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.sdiv_complete_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sdiv_complete_observation
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.sdiv_resource_priority' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sdiv_resource_priority
theorem smod_client (a b : Scalar.Word) (perm : Bool) :
    let result := (if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tmod b.toInt))
    Solidity.Evm.Instr.step .smod (ir a b)=.ok (irExpected a b result) 0 ∧
    Scalar.run Selection.smodCertificate.code (a::b::spill)=some (result::spill) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SMOD 12 perm (a::b::spill))=
      .ok (nativeExpected .SMOD 5 a b result perm) ∧
    EVM.X 2 #[] (F.input .SMOD 12 perm (a::b::spill))=
      EVM.X 1 #[] (nativeExpected .SMOD 5 a b result perm) := by
  dsimp only
  have h := InstructionSelectionAgreement.smod (F.site .SMOD 12 perm) a b spill (ir a b)
    rfl (by decide) (by change 5≤12;decide) 0
  dsimp only at h
  have shape := five_shape .SMOD a b (if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tmod b.toInt)) perm
  simp only [WrappingArithmeticFixtures.input] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem smod_signed_cases (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SMOD 12 perm ((BitVec.ofInt 256 (-17))::5::spill))=
      .ok (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SMOD 12 perm (17::(BitVec.ofInt 256 (-5))::spill))=
      .ok (nativeExpected .SMOD 5 17 (BitVec.ofInt 256 (-5)) 2 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SMOD 12 perm ((BitVec.ofInt 256 (-17))::(BitVec.ofInt 256 (-5))::spill))=
      .ok (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) (BitVec.ofInt 256 (-5)) (BitVec.ofInt 256 (-2)) perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SMOD 12 perm (17::0::spill))=
      .ok (nativeExpected .SMOD 5 17 0 0 perm) ∧
    Assembly.driverSteps 1 2 #[] (F.input .SMOD 12 perm ((BitVec.ofNat 256 (2^255))::(BitVec.ofInt 256 (-1))::spill))=
      .ok (nativeExpected .SMOD 5 (BitVec.ofNat 256 (2^255)) (BitVec.ofInt 256 (-1)) 0 perm) := by
  exact ⟨(smod_client (BitVec.ofInt 256 (-17)) 5 perm).2.2.1,
    (smod_client 17 (BitVec.ofInt 256 (-5)) perm).2.2.1,
    (smod_client (BitVec.ofInt 256 (-17)) (BitVec.ofInt 256 (-5)) perm).2.2.1,
    (smod_client 17 0 perm).2.2.1,
    (smod_client (BitVec.ofNat 256 (2^255)) (BitVec.ofInt 256 (-1)) perm).2.2.1⟩
theorem smod_complete_observation (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SMOD 12 perm ((BitVec.ofInt 256 (-17))::5::spill))=
      .ok (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm) ∧
    (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm).stack=[u ((2^256:Nat)-2),u 258,u 513] ∧
    (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm).stack≠[u 3,u 258,u 513] ∧
    (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm).stack≠[u ((2^256:Nat)-2),u 513,u 258] ∧
    (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x07,0] ∧
    (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm).pc=u 4 ∧
    (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm).gasAvailable=u 7 ∧
    (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm).execLength=42 ∧
    (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm).memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm).returnData.data.toList=[0xcc,0xdd] ∧
    (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm).H_return.data.toList=[0xee,0xff] ∧
    (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm).executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm).accountMap=accounts ∧
    (nativeExpected .SMOD 5 (BitVec.ofInt 256 (-17)) 5 (BitVec.ofInt 256 (-2)) perm).σ₀=accounts := by
  refine ⟨(smod_client (BitVec.ofInt 256 (-17)) 5 perm).2.2.1,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u ((2^256:Nat)-2),u 258,u 513]≠[u 3,u 258,u 513];decide
  · change [u ((2^256:Nat)-2),u 258,u 513]≠[u ((2^256:Nat)-2),u 513,u 258];decide
theorem smod_resource_priority (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (F.input .SMOD 4 perm ((BitVec.ofInt 256 (-17))::5::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .SMOD 4 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (F.input .SMOD 5 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] (F.input .SMOD 0 perm [])=.error .OutOfFuel := by
  first
  | solve | rfl
  | solve | decide
  | cases perm <;> exact ⟨rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.smod_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms smod_client
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.smod_signed_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms smod_signed_cases
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.smod_complete_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms smod_complete_observation
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionControls.smod_resource_priority' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms smod_resource_priority
end SolidityBridge.RoadmapV15.P10.InstructionSelectionControls
