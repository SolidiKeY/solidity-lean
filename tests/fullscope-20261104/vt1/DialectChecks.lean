import Solidity.SolcValidation.Dialect
open Solidity.SolcValidation

example : (Op.evm Solidity.Yul.Builtin.mstore).name = "mstore" := rfl
example : (ObjectOp.memoryguard ⟨128, by decide⟩).name = "memoryguard" := rfl
example : (ObjectOp.setimmutable "constructor_immutable").name = "setimmutable" := rfl
example : (ObjectOp.loadimmutable "constructor_immutable").name = "loadimmutable" := rfl
example : (ObjectOp.linkersymbol "Library.sol:L").name = "linkersymbol" := rfl
example : (IrArtifact.mk .unoptimized [] "Contract" () []).root =
    Object.object "Contract" () [] := rfl
#print axioms Solidity.SolcValidation.evm_name
#print axioms Solidity.SolcValidation.mode_distinct
