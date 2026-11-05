import SolidityBridge.RoadmapV15.P10.StackSelectionAgreement
import SolidityBridge.RoadmapV15.P10.WordPushFixtures
import SolidityBridge.RoadmapV15.P10.PopControls

/-! All16 actual selected depths, independent populated whole-State outputs,
nonuniform operands/spill, index-origin and resource-separation negatives;
selected POP preserves caller tails and forgets only the discarded head. -/
namespace SolidityBridge.RoadmapV15.P10.StackSelectionControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (u spill accounts)

def leading (n : Fin 16) : Scalar.Stack :=
  (List.range n.val).map (fun i=>BitVec.ofNat 256 (i+1))
def ir (words : Scalar.Stack) : Solidity.Evm.Machine :=
  {Solidity.Evm.Machine.init with
    stack:=Selection.irStack words,
    mem:=fun a=>if a=63 then .val (Solidity.Evm.wmod 99) else .val (Solidity.Evm.wmod 0),
    self:=Solidity.Evm.wmod 7,caller:=Solidity.Evm.wmod 19,
    callvalue:=Solidity.Evm.wmod 23,timestamp:=Solidity.Evm.wmod 29}
def site (op : Backend.Op) (gas : Nat) (perm : Bool) : Site op :=
  ⟨WordPushFixtures.seed gas perm,WordPushFixtures.before,WordPushFixtures.after,by decide⟩
def input (op : Backend.Op) (gas : Nat) (perm : Bool) (words : Scalar.Stack) : EVM.State :=
  (modularSite (site op gas perm) words).state
def observed (op : Backend.Op) (perm : Bool) (words output : Scalar.Stack) : EVM.State :=
  {input op 12 perm words with
    pc:=u 4,gasAvailable:=u 9,execLength:=42,
    stack:=output.map (fun w=>UInt256.mk w.toFin)}

private theorem shape (op : Backend.Op) (perm : Bool) (words output : Scalar.Stack) :
    (Assembly.chargedPrepare (input op 12 perm words) 3).replaceStackAndIncrPC
      (output.map (fun w=>UInt256.mk w.toFin)) = observed op perm words output := by
  first | rfl | (simp only [input,observed,site,modularSite,Site.state,
    WordPushFixtures.seed,WordPushFixtures.u,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC]; rfl)

theorem dup_client (n : Fin 16) (perm : Bool) :
    let words := leading n ++ 511::spill
    let output := 511::words
    Selection.selectStack (.dup (n.val+1))=some (Selection.dupCertificate n) ∧
    Solidity.Evm.Instr.step (.dup (n.val+1)) (ir words)=
      .ok {ir words with stack:=Selection.irStack output} 0 ∧
    Scalar.run (Selection.dupCertificate n).code words=some output ∧
    Assembly.driverSteps 1 2 #[] (input (.DUP n) 12 perm words)=
      .ok (observed (.DUP n) perm words output) ∧
    EVM.X 2 #[] (input (.DUP n) 12 perm words)=
      EVM.X 1 #[] (observed (.DUP n) perm words output) := by
  dsimp only
  have depth : (leading n).length=n.val := by simp only [leading,List.length_map,List.length_range]
  have room : (leading n).length+spill.length+2≤1024 := by rw [depth];change n.val+2+2≤1024;omega
  have h := StackSelectionAgreement.dup n (site (.DUP n) 12 perm) (leading n) spill 511 depth
    (ir (leading n ++ 511::spill)) rfl room (by change 3≤12;decide) 0
  dsimp only at h
  have eq := shape (.DUP n) perm (leading n ++ 511::spill) (511::(leading n ++ 511::spill))
  simp only [input] at eq
  rw [eq] at h
  exact ⟨StackSelectionAgreement.selected_dup n,h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem swap_client (n : Fin 16) (perm : Bool) :
    let words := 1025::(leading n ++ 511::spill)
    let output := 511::(leading n ++ 1025::spill)
    Selection.selectStack (.swap (n.val+1))=some (Selection.swapCertificate n) ∧
    Solidity.Evm.Instr.step (.swap (n.val+1)) (ir words)=
      .ok {ir words with stack:=Selection.irStack output} 0 ∧
    Scalar.run (Selection.swapCertificate n).code words=some output ∧
    Assembly.driverSteps 1 2 #[] (input (.SWAP n) 12 perm words)=
      .ok (observed (.SWAP n) perm words output) ∧
    EVM.X 2 #[] (input (.SWAP n) 12 perm words)=
      EVM.X 1 #[] (observed (.SWAP n) perm words output) := by
  dsimp only
  have depth : (leading n).length=n.val := by simp only [leading,List.length_map,List.length_range]
  have room : (leading n).length+spill.length+2≤1024 := by rw [depth];change n.val+2+2≤1024;omega
  have h := StackSelectionAgreement.swap n (site (.SWAP n) 12 perm) (leading n) spill 1025 511 depth
    (ir (1025::(leading n ++ 511::spill))) rfl room (by change 3≤12;decide) 0
  dsimp only at h
  have eq := shape (.SWAP n) perm (1025::(leading n ++ 511::spill)) (511::(leading n ++ 1025::spill))
  simp only [input] at eq
  rw [eq] at h
  exact ⟨StackSelectionAgreement.selected_swap n,h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem complete_observation (perm : Bool) :
    let next := observed (.SWAP 15) perm (1025::(leading 15 ++ 511::spill))
      (511::(leading 15 ++ 1025::spill))
    next.stack = ([511,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,1025,258,513] : List Nat).map u ∧
    next.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x9f,0] ∧
    next.pc=u 4 ∧ next.gasAvailable=u 9 ∧ next.execLength=42 ∧
    next.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    next.returnData.data.toList=[0xcc,0xdd] ∧ next.H_return.data.toList=[0xee,0xff] ∧
    next.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    next.accountMap=accounts ∧ next.σ₀=accounts := by
  first | rfl | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Zero-based physical index1 is the wrong partner for one-based IR DUP1. -/
theorem wrong_index_partner :
    (Selection.dupCertificate 0).code≠[.op (.DUP 1)] ∧
    (observed (.DUP 0) false [511,258,513] [511,511,258,513]).stack ≠
      (observed (.DUP 1) false [511,258,513] [258,511,258,513]).stack := by
  decide +kernel

theorem resource_separation (perm : Bool) :
    Solidity.Evm.Instr.step (.dup 1) (ir (511::spill))=
      .ok {ir (511::spill) with stack:=Selection.irStack (511::511::spill)} 0 ∧
    Assembly.driverSteps 1 2 #[] (input (.DUP 0) 2 perm (511::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 1 #[] (input (.DUP 0) 12 perm (511::spill))=.error .OutOfFuel := by
  refine ⟨(dup_client 0 perm).2.1,?_,rfl⟩
  cases perm <;> rfl

/-- The same public selection path reaches charged POP, at an independent
populated fixture with an arbitrary legal caller tail and discarded word. -/
theorem pop_client (a : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+1≤1024) (perm : Bool) :
    Selection.selectStack .pop=some Selection.popCertificate ∧
    Solidity.Evm.Instr.step .pop (ir (a::tail))=
      .ok {ir (a::tail) with stack:=Selection.irStack tail} 0 ∧
    Scalar.run Selection.popCertificate.code (a::tail)=some tail ∧
    Assembly.driverSteps 1 2 PopControls.supplied (PopControls.input 11 perm (a::tail))=
      .ok (PopControls.observed 11 perm a tail) ∧
    EVM.X 2 PopControls.supplied (PopControls.input 11 perm (a::tail))=
      EVM.X 1 PopControls.supplied (PopControls.observed 11 perm a tail) := by
  have h := StackSelectionAgreement.pop PopControls.supplied (PopControls.site 11 perm)
    a tail (ir (a::tail)) rfl room (by change 2≤11;decide) 0
  dsimp only at h
  have shape : (Assembly.chargedPrepare (PopControls.input 11 perm (a::tail)) 2).replaceStackAndIncrPC
      (tail.map (fun w=>UInt256.mk w.toFin))=PopControls.observed 11 perm a tail := by
    first | rfl | (simp only [PopControls.input,PopControls.observed,PopControls.site,
      modularSite,Site.state,WordPushFixtures.seed,WordPushFixtures.u,
      EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,Assembly.chargedPrepare];rfl)
  simp only [PopControls.input] at shape
  rw [shape] at h
  exact ⟨StackSelectionAgreement.selected_pop,h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

/-- Actual fetched output is independent of the discarded head, including its
entire native frame, rather than merely agreeing on a top-word projection. -/
theorem pop_discards_head (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+1≤1024) (perm : Bool) :
    Assembly.driverSteps 1 2 PopControls.supplied (PopControls.input 11 perm (a::tail))=
      Assembly.driverSteps 1 2 PopControls.supplied (PopControls.input 11 perm (b::tail)) := by
  simp only [(pop_client a tail room perm).2.2.2.1,
    (pop_client b tail room perm).2.2.2.1]
  rfl

theorem pop_resource_separation (perm : Bool) :
    Solidity.Evm.Instr.step .pop (ir (511::spill))=
      .ok {ir (511::spill) with stack:=Selection.irStack spill} 0 ∧
    Assembly.driverSteps 1 2 PopControls.supplied (PopControls.input 1 perm (511::spill))=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 PopControls.supplied (PopControls.input 1 perm [])=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 PopControls.supplied (PopControls.input 2 perm [])=.error .StackUnderflow ∧
    Assembly.driverSteps 1 1 PopControls.supplied (PopControls.input 11 perm (511::spill))=.error .OutOfFuel ∧
    Assembly.driverSteps 1 1 PopControls.supplied (PopControls.input 11 perm [])=.error .OutOfFuel := by
  refine ⟨(pop_client 511 spill (by decide) perm).2.1,?_,?_,?_,rfl,rfl⟩
  all_goals cases perm <;> rfl

#print axioms pop_client
#print axioms pop_discards_head
#print axioms pop_resource_separation
#print axioms dup_client
#print axioms swap_client
#print axioms complete_observation
#print axioms wrong_index_partner
#print axioms resource_separation
end SolidityBridge.RoadmapV15.P10.StackSelectionControls
