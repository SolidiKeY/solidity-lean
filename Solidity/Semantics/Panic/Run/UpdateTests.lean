import Solidity.Semantics.Panic.Run.UpdateProofs

namespace Solidity.Semantics.Panic.Tests

/- Public update API availability; behavior contracts live in UpdateProofs. -/
#check compound
#check numericOne
#check bump
#check compound_erase
#check bump_erase
#check arhs
#check mrhs
#check opStore
#check opMem
#check opLocStore
#check bumpStore
#check bumpMem
#check opLocBump
#check memoryWrite
#check Run.assign
#check Run.rebind
#check Run.assignLocal
#check Run.declLocal
#check Run.declStorage
#check Run.opAssign
#check Run.incDec
#check Run.assignIncDec
#check Run.push
#check Run.assignLocalPush
#check Run.pushOpAssign
#check Run.pushIncDec
#check Run.pop
#check Run.transfer
#check Run.send
#check Run.declMem
#check Run.rebindMem
#check Run.assignFromMem
#check Run.assignMem
#check Run.delete
#check Run.clear
#check Run.deleteMem
#check Run.assignNew
#check Run.assign_rhs_error
#check Run.opAssign_rhs_error
#check Run.assignMem_rhs_error
#check Run.pushOpAssign_exhausted
#check Run.pop_origin
#check Run.opMem_read_error
#check Run.bumpMem_read_error
#check Run.memoryWrite_index_origin
#check Run.assignMem_target_error
#check Run.clear_prim_error
#check Run.clear_ref_error
#check Run.assignNew_mem_error

/- Division by zero retains code 0x12 at the compound-operation boundary. -/
#guard (match compound .div .uint rfl ⟨1, by decide⟩ ⟨0, by decide⟩ with
  | .error (.intrinsic c _) => c.code == 0x12
  | _ => false)

/- Unsigned subtraction underflow retains arithmetic code 0x11. -/
#guard (match compound .sub .uint rfl ⟨0, by decide⟩ ⟨1, by decide⟩ with
  | .error (.intrinsic c _) => c.code == 0x11
  | _ => false)

end Solidity.Semantics.Panic.Tests
