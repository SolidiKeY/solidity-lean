import Solidity.Syntax.Scoped

/-! Typed storage-source observations used by the push argument rules.
A primitive path is read as a value; a reference path is bound as an alias.
The replacement's declaration tells the schema reader which one it needs.
Memory snapshots are classified separately for the upstream variable-copy
case and the explicit Lean-only complex-source capture. -/

namespace Solidity

/-- A memory snapshot is the source of `rows.push(mv)` or a storage write. -/
def Src.isMemory {C : Contract} {Γ : Ctx} {T : Ty} : Src C Γ T → Bool
  | .copyMem _ => true
  | _ => false

/-- A native typed view of a fixed-array snapshot at another outer shape. -/
def Src.isFixedCopy {C : Contract} {Γ : Ctx} {T : Ty} : Src C Γ T → Bool
  | .fixedCopy .. => true
  | _ => false

/-- Upstream captures primitive/storage expressions; a memory source is
directly covered when it is a memory variable. -/
def Src.keyPushSource {C : Contract} {Γ : Ctx} {T : Ty} : Src C Γ T → Bool
  | .copyMem p => p.isSimple
  | .fixedCopy .. => false
  | _ => true

/-- A typed shape-copy source requires its explicit adapter rule. -/
theorem Src.keyPushSource_ofFixedCopy {C : Contract} {Γ : Ctx} {T : Ty}
    {r : Src C Γ T} (h : r.isFixedCopy = true) : r.keyPushSource = false := by
  cases r <;> first | rfl | cases h

theorem Src.isMemory_wk {C : Contract} {Γ Δ : Ctx} {T : Ty}
    (h : Thin Γ Δ) (r : Src C Γ T) : (r.wk h).isMemory = r.isMemory := by
  cases r <;> rfl

theorem Src.keyPushSource_wk {C : Contract} {Γ Δ : Ctx} {T : Ty}
    (h : Thin Γ Δ) (r : Src C Γ T) : (r.wk h).keyPushSource = r.keyPushSource := by
  cases r with
  | val v => rfl
  | copy p hm => rfl
  | fixedCopy p shape hm => rfl
  | copyMem p => exact MPath.isSimple_wk h p

/-- A primitive storage path, such as `rows[i].value`, read as a value. -/
def SPath.primitiveRead {C : Contract} {Γ : Ctx} {p : PrimTy} :
    SPath C Γ (.prim p) → Val C Γ p
  | .loc l => .read l

/-- Whether the value `rows[i].value` needs the storage-path capture rule. -/
def Val.complexStorageRead {C : Contract} {Γ : Ctx} {p : PrimTy} : Val C Γ p → Bool
  | .read l => !(SPath.loc l).isSimple
  | _ => false

/-- Reading `rows[i].value` retains the source path's complexity. -/
theorem SPath.primitiveRead_complex {C : Contract} {Γ : Ctx} {p : PrimTy}
    (b : SPath C Γ (.prim p)) : b.primitiveRead.complexStorageRead = !b.isSimple := by
  cases b with
  | loc l => rfl

end Solidity
