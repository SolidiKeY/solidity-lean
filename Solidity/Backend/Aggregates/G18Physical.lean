import Solidity.Backend.MemoryOps.PhysicalUintWrite
import Solidity.Backend.MemoryOps.PhysicalByteJournal

/-! G18 consumers of the actual P6 array certificate. Ordered finite observers
are projections of existing heaps/memories, not a new execution relation.
REVERT below is a live byte-slice endpoint, not a Source rollback theorem. -/
namespace Solidity.Backend.Aggregates.G18Physical
open MemoryOps MemoryOps.Physical

/-- Existing intrinsic elements selected in the requested order, including repeats.
Validity is required by the theorems; the default is never used there. -/
def values {H : HTy} (hp : Heap H) (r : HRef H (.array (.prim .uint)))
    (indices : List (Fin Evm.W)) : List PrimTy.uint.Denote :=
  indices.map (fun i => ((MObj.elems .dyn (hp.get r))[i.val]?).getD (Evm.Memory.indexValue (Evm.wmod 0)))

/-- The complete requested ordered vector and each actual source/word read
follow from the initial relation. No payload or desired run is assumed. -/
theorem observations {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (h : UintArrayAt y address hp r base m bytes) (F : Source.Fr)
    (indices : List (Fin Evm.W)) (valid : ∀ i ∈ indices, i.val < hp.len r .dyn) :
    indices.map (fun i => Environment.readMemory bytes (32*(base.val+1+i.val)) 32) =
      (values hp r indices).map (fun v => Semantics.wordBytes v.val.toNat) ∧
    (∀ (i : Fin Evm.W) (member : i ∈ indices), ∃ v : PrimTy.uint.Denote,
      (Source.readLoc (E := E) (Γ := Γ) F (τ := .int .u256) (.mem address i.val)).run y =
        (.ok (sourceUint v),y) ∧
      Evm.ValOutT .uint (TRes.ofOpt (hp.index r .dyn (Evm.Memory.indexValue i)))
        (Evm.run (Evm.Memory.readArrayCode base) (m.push (.val i))) m ∧
      ∀ tail suffix, Failure.Slice.run (.op .REVERT :: suffix)
        ⟨⟨32*(base.val+1+i.val),by
          have fit := h.physical.fits (base.val+1+i.val) ⟨by omega,by have hi := valid i member;omega⟩
          omega⟩ :: ⟨32,by decide⟩ :: tail, bytes⟩ =
          some (⟨tail,bytes⟩,some (.revert (Semantics.wordBytes v.val.toNat)))) := by
  constructor
  · simp only [values,List.map_map]
    apply List.map_congr_left
    intro i hi
    obtain ⟨v,hv,_,hb,_⟩ := h.read F i (valid i hi)
    simpa only [Function.comp_def,hv,Option.getD_some] using hb
  · intro i hi
    obtain ⟨v,_,hs,hb,hw⟩ := h.read F i (valid i hi)
    refine ⟨v,hs,hw,?_⟩
    intro tail suffix
    rw [revert_live,hb]

/-- Actual source/typed/word/physical writes establish a reached certificate;
every ordered observer/specification can then be instantiated on that state.
All source non-heap fields, other objects and exterior bytes remain framed. -/
theorem write_observations {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (h : UintArrayAt y address hp r base m bytes) (F : Source.Fr) (fuel : Nat)
    (i w : Fin Evm.W) (hi : i.val < hp.len r .dyn) :
    let cell := base.val+1+i.val
    let next := Evm.Memory.writeMachine m cell (.val w)
    let byteNext := Environment.writeBytes bytes (32*cell) (Semantics.wordBytes w.val)
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) (Evm.Memory.indexValue w)=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem address i.val)
        (sourceUint (Evm.Memory.indexValue w))).run y=(.ok (),z) ∧
      Evm.run (Evm.Memory.writeArrayCode base) ((m.push (.val w)).push (.val i))=.ok next 0 ∧
      (∃ offset : Fin Evm.W, offset.val=32*cell ∧ ∀ tail : List Environment.Word,
        Environment.cryptoStep (.op .MSTORE)
          ⟨lenU offset.val offset.isLt::lenU w.val w.isLt::tail,bytes⟩=some ⟨tail,byteNext⟩) ∧
      UintArrayAt z address out r base next byteNext ∧
      z.1=y.1 ∧ z.2={y.2 with heap := z.2.heap} ∧
      (∀ b,b≠address → z.2.heap.get b=y.2.heap.get b) ∧
      (∀ k,k<32*cell ∨ 32*cell+32≤k → byteNext k=bytes k) ∧
      (∀ indices : List (Fin Evm.W), (∀ j ∈ indices,j.val<out.len r .dyn) →
        indices.map (fun j => Environment.readMemory byteNext (32*(base.val+1+j.val)) 32)=
          (values out r indices).map (fun v => Semantics.wordBytes v.val.toNat)) := by
  obtain ⟨out,z,ht,hs,hw,hb,hr,hl,hstate,hother,_,hbytes⟩ := h.write_cell F fuel i w hi
  exact ⟨out,z,ht,hs,hw,hb,hr,hl,hstate,hother,hbytes,
    fun indices valid => (observations hr F indices valid).1⟩

/-- Arbitrary predicates on the exact finite observation vector transport by
proved equality, never by an assumed final simulation or physical execution. -/
theorem observation_spec {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (h : UintArrayAt y address hp r base m bytes) (F : Source.Fr)
    (indices : List (Fin Evm.W)) (valid : ∀ i ∈ indices,i.val<hp.len r .dyn)
    (Q : List (List UInt8) → Prop) :
    Q (indices.map (fun i => Environment.readMemory bytes (32*(base.val+1+i.val)) 32)) ↔
      Q ((values hp r indices).map (fun v => Semantics.wordBytes v.val.toNat)) := by
  rw [(observations h F indices valid).1]
end Solidity.Backend.Aggregates.G18Physical
