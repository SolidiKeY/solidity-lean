import Solidity.Yul.Views.CalldataHashBinding
import Solidity.Source.Semantics

/-! Source calldata hashing allocates exactly once, clips oversized references,
and keeps timeout states unchanged. Physical payload copying preserves bytes
beyond the effective slice; it does not model the allocator header/FMP itself. -/
namespace Solidity.Yul.Views.CalldataHashControls
private def E : Source.Env := ⟨[]⟩
private def F : Source.Fr := {this:=1,sender:=2,value:=0,static:=false,contract:="CalldataHash",cd:=[17,255,0,128]}
private def state (off len : Nat) : Source.EMState E [.bytes .calldata,.bytes .calldata] :=
  (.cons (.cdRef rfl off len) (.cons (.cdRef rfl off len) .nil),Source.St.init E)
private def after (off len : Nat) := objectAllocatedState (state off len)
  (Source.Data.bytes (l:=.memory) ((F.cd.drop off).take len))
private def residual : ByteView := fun k=>if k=131 then 99 else if k=132 then 77 else if k=511 then 170 else 42

theorem actual_alias_hash (G : Source.Glob E) (n off len : Nat) (first : Bool) :
    let index : Source.Idx [.bytes .calldata,.bytes .calldata] (.bytes .calldata):=if first then .here else .there .here
    let bs:=(F.cd.drop off).take len
    let memory:=calldatacopy residual F.cd 128 off bs.length
    let value:=Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bs))
    (Source.evalE G F (n+4) (sourceCalldataHashExpr index)).run (state off len)=(.ok (.val value),after off len) ∧
      value.word=some (keccak256 G.fixed.evm memory 128 bs.length) := by
  have localValue : (state off len).1.get (if first then .here else .there .here)=Source.Val.cdRef rfl off len := by cases first <;> rfl
  have result := sourceCalldataHash_physical G F n (state off len) (if first then .here else .there .here)
    off len 128 residual localValue
  exact ⟨result.1,result.2.1⟩

theorem clipped_allocation : (after 1 5).2.heap.next=1 ∧
    (after 1 5).2.heap.get 0=some ⟨.bytes .memory,Source.Data.bytes [255,0,128]⟩ ∧
    (after 1 5).1=(state 1 5).1 := ⟨rfl,rfl,rfl⟩

theorem calldata_initial_MemOK (off len : Nat) : Source.MemOK E (state off len).2.heap.ty (state off len) := by
  have empty : Source.MemOK E (Source.St.init E).heap.ty ((.nil,Source.St.init E) : Source.EMState E []) :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  exact ⟨⟨empty.1.1,⟨trivial,⟨trivial,trivial⟩⟩⟩,empty.2⟩

theorem calldata_allocation_MemOK (off len : Nat) : Source.MemOK E (state off len).2.heap.ty (after off len) :=
  (objectAllocRef_MemOK _ (state off len) (Source.Data.bytes (l:=.memory) ((F.cd.drop off).take len))
    rfl trivial trivial (.bytes _) (calldata_initial_MemOK off len)).1

theorem low_horizon (G : Source.Glob E) (n off len : Nat) (low : n<4) :
    (Source.evalE G F n (sourceCalldataHashExpr Source.Idx.here)).run (state off len)=
      (.error .timeout,state off len) := by
  have casesN : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
  rcases casesN with rfl | rfl | rfl | rfl <;> rfl

/-- info: ([255, 0, 128], [255, 0, 128, 0, 0], 99, 77, 170) -/
#guard_msgs in #eval
  (readBytes (calldatacopy residual F.cd 128 1 3) 128 3,
   readBytes (calldatacopy residual F.cd 128 1 5) 128 5,
   (calldatacopy residual F.cd 128 1 3 131).toNat,
   (calldatacopy residual F.cd 128 1 3 132).toNat,
   (calldatacopy residual F.cd 128 1 3 511).toNat)
/-- info: ([255, 0], [], []) -/
#guard_msgs in #eval ((F.cd.drop 1).take 2,(F.cd.drop 1).take 0,(F.cd.drop 8).take 2)
/-- info: (0, 1) -/
#guard_msgs in #eval ((state 1 5).2.heap.next,(after 1 5).2.heap.next)
end Solidity.Yul.Views.CalldataHashControls
