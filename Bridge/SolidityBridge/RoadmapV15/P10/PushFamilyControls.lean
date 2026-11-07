import SolidityBridge.RoadmapV15.P10.PushFamily
import SolidityBridge.RoadmapV15.P10.MetadataPushControls

/-! Raw intrinsic payloads, including leading zeroes, consume the new Scalar-tail
transport against independently populated metadata expected states. No physical
memory padding, source/compiler/world origin or Osaka adequacy is claimed. -/
namespace SolidityBridge.RoadmapV15.P10.PushFamilyControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open PushFamily
open WordPushFixtures (seed before after spill u accounts)

def expected (perm : Bool) (n : Fin 33) (payload : Vector UInt8 n.val) (tail : Scalar.Stack) : EVM.State :=
  MetadataPushControls.expected perm n (value n payload) (tail.map typedWord)

theorem client (perm : Bool) (n : Fin 33) (payload : Vector UInt8 n.val) (tail : Scalar.Stack)
    (room : tail.length+1≤1024) :
    Scalar.step (.push n payload) tail=some (Scalar.immediate payload.toList::tail) ∧
    Assembly.driverSteps 1 2 #[] (input (seed 10 perm) before after n payload tail)=.ok (expected perm n payload tail) ∧
    EVM.X 2 #[] (input (seed 10 perm) before after n payload tail)=EVM.X 1 #[] (expected perm n payload tail) := by
  have h := agreement (seed 10 perm) before after n payload tail (by decide)
    (by change metadataPushCost n≤10;unfold metadataPushCost;split <;> decide) room 0
  dsimp only at h
  have old := MetadataPushControls.populated #[] perm n (value n payload) (tail.map typedWord)
    (by simpa only [List.length_map] using room)
  rw [metadata_input] at old
  have same := Except.ok.inj (h.2.1.symm.trans old)
  exact ⟨h.1,old,h.2.2.trans (congrArg (EVM.X 1 #[]) same)⟩

def empty : Vector UInt8 0 := #v[]
def one : Vector UInt8 1 := #v[0xa5]
def leading : Vector UInt8 3 := #v[0,1,2]
def full31 : Vector UInt8 31 := Vector.replicate 31 0xff
def full32 : Vector UInt8 32 := Vector.replicate 32 0xff

theorem widths (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (input (seed 10 perm) before after 0 empty spill)=.ok (expected perm 0 empty spill) ∧
    Assembly.driverSteps 1 2 #[] (input (seed 10 perm) before after 1 one spill)=.ok (expected perm 1 one spill) ∧
    Assembly.driverSteps 1 2 #[] (input (seed 10 perm) before after 3 leading spill)=.ok (expected perm 3 leading spill) ∧
    Assembly.driverSteps 1 2 #[] (input (seed 10 perm) before after 31 full31 spill)=.ok (expected perm 31 full31 spill) ∧
    Assembly.driverSteps 1 2 #[] (input (seed 10 perm) before after 32 full32 spill)=.ok (expected perm 32 full32 spill) := by
  exact ⟨(client perm 0 empty spill (by decide)).2.1,(client perm 1 one spill (by decide)).2.1,
    (client perm 3 leading spill (by decide)).2.1,(client perm 31 full31 spill (by decide)).2.1,
    (client perm 32 full32 spill (by decide)).2.1⟩

theorem length_endian :
    leading.toList=[0,1,2] ∧ Scalar.immediate leading.toList=Scalar.immediate [1,2] ∧
    leading.toList≠([1,2] : List UInt8) ∧ leading.toList≠leading.toList.reverse ∧
    (expected false 3 leading spill).pc≠(expected false 2 #v[1,2] spill).pc ∧
    (expected false 0 empty spill).gasAvailable=u 8 ∧ (expected false 3 leading spill).gasAvailable=u 7 := by decide

theorem complete_observation (perm : Bool) :
    let next := expected perm 3 leading spill
    next.stack=[u 258,u 258,u 513] ∧ next.stack≠[u 513,u 258,u 513] ∧ next.stack≠[u 258,u 513,u 258] ∧
    next.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x62,0,1,2,0] ∧
    next.pc=u 7 ∧ next.gasAvailable=u 7 ∧ next.execLength=42 ∧
    next.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    next.returnData.data.toList=[0xcc,0xdd] ∧ next.H_return.data.toList=[0xee,0xff] ∧
    next.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧ next.accountMap=accounts ∧ next.σ₀=accounts := by
  refine ⟨rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 258,u 258,u 513]≠[u 513,u 258,u 513];decide
  · change [u 258,u 258,u 513]≠[u 258,u 513,u 258];decide

theorem resource_order (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (input (seed 1 perm) before after 0 empty spill)=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (input (seed 2 perm) before after 3 leading spill)=.error .OutOfGass ∧
    Assembly.driverSteps 1 1 #[] (input (seed 0 perm) before after 0 empty spill)=.error .OutOfFuel := by
  cases perm <;> exact ⟨rfl,rfl,rfl⟩

#print axioms client
#print axioms widths
#print axioms length_endian
#print axioms complete_observation
#print axioms resource_order
end SolidityBridge.RoadmapV15.P10.PushFamilyControls
