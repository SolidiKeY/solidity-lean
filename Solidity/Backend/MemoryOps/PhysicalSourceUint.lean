import Solidity.Backend.MemoryOps.PhysicalWordFrame
import Solidity.Backend.MemoryOps.SourceUintMemory

/-! Independent Source/intrinsic/word/physical-byte observations for an already
represented DYNAMIC uint array. No allocation, pointer relocation or general
Source/compiler theorem is assumed. The byte footprint has its own stronger
no-wrap bounds; the old word-space bound is insufficient for physical bytes. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- The source object, typed array and published word layout are independently
related initially; the physical bytes then represent exactly its live cells. -/
structure UintArrayAt {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (address : Nat) (hp : Heap H)
    (r : HRef H (.array (.prim .uint))) (base : Fin Evm.W)
    (m : Evm.Machine) (bytes : Environment.Memory) : Prop where
  source : SourceUintMemoryAt y address hp r .dyn
  words : Evm.Memory.ArrayRepr hp r base m
  physical : WordFrame m bytes (fun c => base.val≤c ∧ c<base.val+1+hp.len r .dyn)

/-- A real source read, typed element, abstract target load and exact 32 physical
bytes are derived from the INITIAL relation, not supplied conversion/output. -/
theorem UintArrayAt.read {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (h : UintArrayAt y address hp r base m bytes) (F : Source.Fr)
    (i : Fin Evm.W) (hi : i.val<hp.len r .dyn) :
    ∃ value : PrimTy.uint.Denote,
      (MObj.elems .dyn (hp.get r))[i.val]?=some value ∧
      (Source.readLoc (E := E) (Γ := Γ) F (τ := .int .u256) (.mem address i.val)).run y=
        (.ok (sourceUint value),y) ∧
      Environment.readMemory bytes (32*(base.val+1+i.val)) 32=
        Semantics.wordBytes value.val.toNat ∧
      Evm.ValOutT .uint (TRes.ofOpt (hp.index r .dyn (Evm.Memory.indexValue i)))
        (Evm.run (Evm.Memory.readArrayCode base) (m.push (.val i))) m := by
  let value : PrimTy.uint.Denote := (MObj.elems .dyn (hp.get r))[i.val]'hi
  have hv : (MObj.elems .dyn (hp.get r))[i.val]?=some value := List.getElem?_eq_getElem hi
  have hs : (Source.readLoc (E := E) (Γ := Γ) F (τ := .int .u256) (.mem address i.val)).run y=
      (.ok (sourceUint value),y) := (h.source.read_nat_iff F i.val value).mpr hv
  have hw : Evm.ReprV .uint value (m.mem (base.val+1+i.val)) := h.words.elements _ _ hv
  obtain ⟨n,hn,he,hmem⟩ := Evm.ReprV.uint_inv hw
  obtain ⟨w,hcell,hbytes⟩ := h.physical.cells (base.val+1+i.val) ⟨by omega,by omega⟩
  have heq : w.val=n := congrArg Fin.val (Evm.Word.val.inj (hcell.symm.trans hmem))
  have hnat : value.val.toNat=n := by rw [he];rfl
  refine ⟨value,hv,hs,?_,Evm.Memory.readArray_correct h.words i⟩
  rw [hbytes,heq,hnat]

/-- info: 'Solidity.Backend.MemoryOps.Physical.UintArrayAt.read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UintArrayAt.read
end Solidity.Backend.MemoryOps.Physical
