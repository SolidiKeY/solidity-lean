import Solidity.Backend.MemoryOps.PhysicalUintDelete

/-! Producer for G34 whole local-pointer composition: two actual word arrays
for the SAME typed heap/object/base agree on exactly its header and elements.
No equality of whole machines, stacks, other cells, or a desired physical
postrelation is assumed. Source and byte observer glue is delegated separately. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- Actual header and typed scalar uniqueness derive agreement on every live
array cell. This is observational determinism, not global memory injectivity. -/
theorem uint_array_cells_eq {H : HTy} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W}
    {left right : Evm.Machine}
    (hl : Evm.Memory.ArrayRepr hp r base left)
    (hr : Evm.Memory.ArrayRepr hp r base right)
    (c : Nat) (hc : base.val≤c ∧ c<base.val+1+hp.len r .dyn) :
    left.mem c=right.mem c := by
  by_cases header : c=base.val
  · subst c
    simp only [hl.length,hr.length]
  · let i := c-(base.val+1)
    have hi : i<(MObj.elems .dyn (hp.get r)).length := by
      change i<hp.len r .dyn
      dsimp only [i]
      omega
    let v := (MObj.elems .dyn (hp.get r))[i]'hi
    have hv : (MObj.elems .dyn (hp.get r))[i]?=some v := List.getElem?_eq_getElem hi
    have offset : base.val+1+i=c := by dsimp only [i];omega
    have lv := hl.elements i v hv
    have rv := hr.elements i v hv
    rw [offset] at lv rv
    obtain ⟨a,ha,va,la⟩ := Evm.ReprV.uint_inv lv
    obtain ⟨b,hb,vb,rb⟩ := Evm.ReprV.uint_inv rv
    have equal : a=b := by omega
    have words : (⟨a,ha⟩ : Fin Evm.W)=⟨b,hb⟩ := Fin.ext equal
    simp only [la,rb,words]

/-- info: 'Solidity.Backend.MemoryOps.Physical.uint_array_cells_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uint_array_cells_eq
end Solidity.Backend.MemoryOps.Physical
