import SolidityBridge.RoadmapV15.P10.InstructionSelectionControls

/-! Concrete ADD/MUL certificate sequence over the real fetched reference.
Numeric operands are already represented. This does not establish their Source,
physical or account-world origin, nor complete Osaka/resource adequacy. -/
namespace SolidityBridge.RoadmapV15.P10.InstructionSelectionSequence
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed before after u spill)

def first (perm : Bool) : Site .ADD :=
  ⟨seed 12 perm,before,.op .MUL::after,by decide⟩
def input (a b c : Scalar.Word) (tail : Scalar.Stack) (perm : Bool) : EVM.State :=
  (modularSite (first perm) (a::b::c::tail)).state
def middle (a b c : Scalar.Word) (tail : Scalar.Stack) (perm : Bool) : EVM.State :=
  (Assembly.chargedPrepare (input a b c tail perm) 3).replaceStackAndIncrPC
    (((a+b)::c::tail).map (fun w=>UInt256.mk w.toFin))
def second (a b c : Scalar.Word) (tail : Scalar.Stack) (perm : Bool) : Site .MUL :=
  ⟨middle a b c tail perm,before++[.op .ADD],after,by decide⟩
def expected (a b c : Scalar.Word) (tail : Scalar.Stack) (perm : Bool) : EVM.State :=
  {input a b c tail perm with
    stack:=(((a+b)*c)::tail).map (fun w=>UInt256.mk w.toFin)
    pc:=u 5,gasAvailable:=u 4,execLength:=43}

private theorem middle_site (a b c : Scalar.Word) (tail : Scalar.Stack) (perm : Bool) :
    (modularSite (second a b c tail perm) ((a+b)::c::tail)).state=middle a b c tail perm := by
  rfl

private theorem final_state (a b c : Scalar.Word) (tail : Scalar.Stack) (perm : Bool) :
    (Assembly.chargedPrepare (modularSite (second a b c tail perm) ((a+b)::c::tail)).state 5).replaceStackAndIncrPC
      ((((a+b)*c)::tail).map (fun w=>UInt256.mk w.toFin))=expected a b c tail perm := by
  first
  | solve | rfl
  | solve | decide
  | solve | omega
  | solve | simp only []
  | simp only [second,middle,input,first,expected,modularSite,Site.state,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,seed,u]
    rfl

private theorem driver_pair (valid : Array UInt256) (s mid final : EVM.State)
    (one : Assembly.driverSteps 1 4 valid s=.ok mid)
    (two : Assembly.driverSteps 1 3 valid mid=.ok final) :
    Assembly.driverSteps 2 4 valid s=.ok final := by
  first
  | solve | rfl
  | solve | simp only [Assembly.driverSteps]
  | cases decoded : EVM.decode s.executionEnv.code s.pc with
    | none => simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind] at one; cases one
    | some packet =>
      cases gate : Assembly.driverGate valid s packet.1 with
      | error e => simp only [Assembly.driverSteps,decoded,Option.option,gate,bind,Except.bind] at one; cases one
      | ok pair =>
        rcases pair with ⟨charged,cost⟩
        cases stepped : EVM.step 3 cost (some packet) charged with
        | error e => simp only [Assembly.driverSteps,decoded,Option.option,gate,stepped,bind,Except.bind] at one; cases one
        | ok next =>
          simp only [Assembly.driverSteps,decoded,Option.option,gate,stepped,bind,Except.bind] at one ⊢
          cases Except.ok.inj one
          exact two

/-- Concrete certificates, actual two native steps and native continuation.
The full independently populated expected state fixes the charged gas and PC. -/
theorem sequence (valid : Array UInt256) (a b c : Scalar.Word) (tail : Scalar.Stack)
    (perm : Bool) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack (a::b::c::tail))
    (room : tail.length+3≤1024) :
    let irMid := {m with stack:=Selection.irStack ((a+b)::c::tail)}
    let irFinal := {m with stack:=Selection.irStack (((a+b)*c)::tail)}
    Solidity.Evm.Instr.step .add m=.ok irMid 0 ∧
    Solidity.Evm.Instr.step .mul irMid=.ok irFinal 0 ∧
    Scalar.run (InstructionSelectionAgreement.Cert.add.code++InstructionSelectionAgreement.Cert.mul.code)
      (a::b::c::tail)=some (((a+b)*c)::tail) ∧
    Assembly.driverSteps 1 4 valid (input a b c tail perm)=.ok (middle a b c tail perm) ∧
    Assembly.driverSteps 1 3 valid (middle a b c tail perm)=.ok (expected a b c tail perm) ∧
    EVM.X 4 valid (input a b c tail perm)=EVM.X 2 valid (expected a b c tail perm) ∧
    Assembly.driverSteps 2 4 valid (input a b c tail perm)=.ok (expected a b c tail perm) := by
  dsimp only
  have add := InstructionSelectionAgreement.add valid (first perm) a b (c::tail) m represented
    (by simpa only [List.length_cons] using room) (by change 3≤12;decide) 2
  have mul := InstructionSelectionAgreement.mul valid (second a b c tail perm) (a+b) c tail
    {m with stack:=Selection.irStack ((a+b)::c::tail)} rfl (by omega)
    (by change 5≤9;decide) 1
  dsimp only at add mul
  change _ ∧ _ ∧ _ ∧
    Assembly.driverSteps 1 4 valid (input a b c tail perm)=.ok (middle a b c tail perm) ∧ _ ∧ _
  have nativeAdd : Assembly.driverSteps 1 4 valid (input a b c tail perm)=.ok (middle a b c tail perm) := add.2.2.1
  have xAdd : EVM.X 4 valid (input a b c tail perm)=EVM.X 3 valid (middle a b c tail perm) := add.2.2.2.1
  have finished := final_state a b c tail perm
  rw [middle_site] at finished
  rw [middle_site,finished] at mul
  exact ⟨add.1,mul.1,rfl,nativeAdd,mul.2.2.1,xAdd.trans mul.2.2.2.1,
    driver_pair valid _ _ _ nativeAdd mul.2.2.1⟩

theorem nonzero_client (perm : Bool) :
    Assembly.driverSteps 2 4 #[u 37,u 99] (input 7 3 5 spill perm)=.ok (expected 7 3 5 spill perm) := by
  let m := {InstructionSelectionControls.ir 7 3 with stack:=Selection.irStack (7::3::5::spill)}
  exact (sequence _ 7 3 5 spill perm m rfl (by decide)).2.2.2.2.2.2

theorem ordered_observation (perm : Bool) :
    let out := expected 7 3 5 spill perm
    out.stack=[u 50,u 258,u 513] ∧ out.stack≠[u 22,u 258,u 513] ∧
    out.stack≠[u 50,u 513,u 258] ∧
    out.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x01,0x02,0] ∧
    out.pc=u 5 ∧ out.gasAvailable=u 4 ∧ out.execLength=43 ∧
    out.toState=(input 7 3 5 spill perm).toState ∧
    out.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    out.returnData.data.toList=[0xcc,0xdd] ∧ out.H_return.data.toList=[0xee,0xff] ∧
    out.activeWords=u 1 := by
  refine ⟨rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 50,u 258,u 513]≠[u 22,u 258,u 513];decide
  · change [u 50,u 258,u 513]≠[u 50,u 513,u 258];decide

theorem wrap_boundary :
    Scalar.run (InstructionSelectionAgreement.Cert.add.code++InstructionSelectionAgreement.Cert.mul.code)
      [BitVec.ofNat 256 ((2^256:Nat)-1),1,7]=some [0] := by decide

theorem resource_controls (perm : Bool) :
    Assembly.driverSteps 2 1 #[] (input 7 3 5 spill perm)=.error .OutOfFuel ∧
    Assembly.driverSteps 1 2 #[] {(middle 7 3 5 spill perm) with gasAvailable:=u 4}=.error .OutOfGass := by
  first
  | solve | rfl
  | solve | decide
  | solve | simp only []
  | cases perm <;> exact ⟨rfl,rfl⟩

#print axioms nonzero_client
#print axioms ordered_observation
#print axioms wrap_boundary
#print axioms resource_controls
#print axioms sequence
end SolidityBridge.RoadmapV15.P10.InstructionSelectionSequence
