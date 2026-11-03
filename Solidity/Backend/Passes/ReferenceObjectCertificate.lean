import Solidity.Backend.Passes.AllocatorPreservation

/-! Certificate inclusion over the EXISTING code and source syntax. An object
certificate has a stronger original Input; this never upgrades a weaker
reference-array state relation. No instruction selection is repeated. -/
namespace Solidity.Backend.Passes
open Evm Evm.Memory
variable {C : Contract} {b : Nat} {Γ Δ : Ctx} {F : Frag Γ}

theorem reference_ptr_objects {R : RefTy} {path : MPath C Γ (.ref R)} {code : List Evm.Instr}
    (h : RefPtrFrag b F path code) : Objects.PtrFrag b F path code := by
  induction h with
  | «local» src hm => exact .local src hm
  | field src hf code h ih => exact .field src hf code ih
  | index src pointer h i hi ih =>
    exact Objects.PtrFrag.index .dyn src pointer ih i hi

theorem reference_stmt_objects {G : Frag Δ} {s : Stmt C Γ Δ} {code : List Evm.Instr}
    (h : ReferenceArrays.StmtFrag b F G s code) : Objects.StmtFrag b F G s code := by
  cases h with
  | rebind F dst src code hs => exact .rebind F dst src code (reference_ptr_objects hs)
  | reference F dst src pointer value hd hs i hi =>
    exact Objects.StmtFrag.write F .dyn dst (.ref src) pointer value
      (reference_ptr_objects hd) (.ref src value (reference_ptr_objects hs)) i hi
  | primitive F dst pointer hd v hv i hi =>
    exact Objects.StmtFrag.write F .dyn dst (.val v) pointer (Evm.compileVal b v)
      (reference_ptr_objects hd) (.val v _ (.core v hv)) i hi

theorem reference_prog_objects {G : Frag Δ} {P : Prog C Γ Δ} {code : List Evm.Instr}
    (h : ReferenceArrays.ProgFrag b F G P code) : Objects.ProgFrag b F G P code := by
  induction h with
  | nil F => exact .nil F
  | cons hs hp ih => exact .cons (reference_stmt_objects hs) ih

/-- Same program, context, fragment and emitted code; the receiving branch's
FULL original Objects.Input is still required for its correctness theorem. -/
def referenceObjects {P : Prog C Γ Δ} (result : ReferenceArrays.CompiledProg b F P) :
    Objects.CompiledProg b F P := ⟨result.frag,result.code,reference_prog_objects result.cert⟩

theorem referenceObjects_code {P : Prog C Γ Δ} (result : ReferenceArrays.CompiledProg b F P) :
    (referenceObjects result).code = result.code := rfl

end Solidity.Backend.Passes
