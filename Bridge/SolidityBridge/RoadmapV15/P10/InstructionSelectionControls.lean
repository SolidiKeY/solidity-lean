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
end SolidityBridge.RoadmapV15.P10.InstructionSelectionControls
