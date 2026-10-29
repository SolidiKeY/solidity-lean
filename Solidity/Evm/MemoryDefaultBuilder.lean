import Solidity.Evm.MemoryObjectFlatFixed

/-! Typed construction certificates for actual source reference defaults.
A builder returns its source root at the old cursor, retains all old identities
and every lower positive memory cell, and preserves any earlier parent gap. -/
namespace Solidity.Evm.Memory.Objects
open Semantics

def DefaultBuildResult {H : HTy} (hp : Heap H) (R : RefTy)
    (hm : (Ty.ref R).mapFree = true) (code : List Instr) (count : Nat)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (m : Machine)
    (hs : cursor.val + count < W) : Prop :=
  let g := hp.allocDefault R hm
  ∃ base' m', run code m = .ok (m'.push (.val cursor)) 0 ∧
    AllocatorRepr g.heap base' frame ⟨cursor.val + count, hs⟩ m' ∧
    base' g.val.id = cursor ∧ BaseExtends H base base' ∧
    m' = {m with mem := m'.mem} ∧
    (∀ addr, 0 < addr → addr < cursor.val → m'.mem addr = m.mem addr) ∧
    (∀ lo hi, Gap hp base lo hi → hi ≤ cursor.val → Gap g.heap base' lo hi)

/-- The certificate is indexed by its exact intrinsic reference type and cost. -/
structure DefaultBuilder (R : RefTy) (hm : (Ty.ref R).mapFree = true) (count : Nat) where
  code : List Instr
  positive : 0 < count
  correct : ∀ {H : HTy} (hp : Heap H) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (m : Machine) (_ha : AllocatorRepr hp base frame cursor m)
    (hs : cursor.val + count < W), DefaultBuildResult hp R hm code count base frame cursor m hs

/-- A dynamic default is an actual fresh empty object at any permitted element type. -/
def DefaultBuilder.empty (E : Ty) (hm : (Ty.ref (.array E)).mapFree = true) :
    DefaultBuilder (.array E) hm 1 where
  code := [.push (.val (wmod 0))] ++ allocateArrayCode
  positive := by decide
  correct := by
    intro H hp base frame cursor m ha hs
    rw [DefaultBuildResult, emptyArray_copy hp E hm]
    refine ⟨upd base H.length cursor, allocateMachine m cursor (wmod 0), ?_,
      ha.allocateEmpty E hs, upd_same _ _ _, (fun r => allocationBase_old base cursor r),
      rfl, ?_, ?_⟩
    · rw [run_append_ok (m' := m.push (.val (wmod 0))) rfl]
      exact allocateArray_run m cursor (wmod 0) ha.free.cell
    · intro addr hz hl
      exact allocateMachine_other m cursor (wmod 0) addr (by omega) (by omega)
    · intro lo hi hg hh
      exact hg.adoptSingle (emptyArray E) cursor hh

/-- Primitive-member structs use the existing source default object and allocator code. -/
def DefaultBuilder.primitiveStruct {s : Name}
    (hpfields : primitiveMembers (structDef s) = true) (hm : (Ty.ref (.struct s)).mapFree = true) :
    DefaultBuilder (.struct s) hm (structAllocationSize s) where
  code := allocateStructCode (structAllocationSize s)
  positive := by unfold structAllocationSize; omega
  correct := by
    intro H hp base frame cursor m ha hs
    rw [DefaultBuildResult, defaultStruct_alloc hp hpfields hm]
    refine ⟨upd base H.length cursor, allocateStructMachine m cursor (structAllocationSize s),
      allocateStruct_run m cursor _ ha.free.cell, ha.allocatePrimitiveStruct hpfields hm hs,
      upd_same _ _ _, (fun r => allocationBase_old base cursor r), rfl, ?_, ?_⟩
    · intro addr hz hl
      exact allocateStructMachine_other m cursor _ addr (by omega)
    · intro lo hi hg hh
      exact hg.adoptSingle (R := .struct s) (defaultFields (structDef s) hpfields) cursor hh

/-- A fixed primitive default is headerless and retains its exact source length. -/
def DefaultBuilder.fixedPrimitive (p : PrimTy) (n : Nat) :
    DefaultBuilder (.fixed (.prim p) n) rfl (max 1 n) where
  code := allocateStructCode (max 1 n)
  positive := by omega
  correct := by
    intro H hp base frame cursor m ha hs
    rw [DefaultBuildResult, defaultFixed_copy hp p n]
    refine ⟨upd base H.length cursor, allocateStructMachine m cursor (max 1 n),
      allocateStruct_run m cursor _ ha.free.cell, ha.allocateFixedPrimitive p n hs,
      upd_same _ _ _, (fun r => allocationBase_old base cursor r), rfl, ?_, ?_⟩
    · intro addr hz hl
      exact allocateStructMachine_other m cursor _ addr (by omega)
    · intro lo hi hg hh
      exact hg.adoptSingle (R := .fixed (.prim p) n) (defaultFixed p n) cursor hh

end Solidity.Evm.Memory.Objects
