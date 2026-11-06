import Solidity.SolcValidation.DataResolution
set_option pp.universes true
set_option pp.fullNames true
#check Solidity.SolcValidation.DataByte
#check Solidity.SolcValidation.DataWord
#check Solidity.SolcValidation.DataRef
#check Solidity.SolcValidation.DataRef.bytes
#check Solidity.SolcValidation.DataRef.bytes_length
#print axioms Solidity.SolcValidation.DataRef.bytes_length
#check Solidity.SolcValidation.DataRef.datasize
#check Solidity.SolcValidation.DataRef.dataoffset
#check Solidity.SolcValidation.DataRef.datasize_exact
#print axioms Solidity.SolcValidation.DataRef.datasize_exact
#check Solidity.SolcValidation.DataRef.dataoffset_exact
#print axioms Solidity.SolcValidation.DataRef.dataoffset_exact
#check Solidity.SolcValidation.DataRef.byte_exact
#print axioms Solidity.SolcValidation.DataRef.byte_exact
#check Solidity.SolcValidation.DataTable
#check Solidity.SolcValidation.DataSelection
#check Solidity.SolcValidation.selectData
#check Solidity.SolcValidation.selectData_complete
#print axioms Solidity.SolcValidation.selectData_complete
#check Solidity.SolcValidation.DataTable.select
#check Solidity.SolcValidation.DataSelection.sound
#print axioms Solidity.SolcValidation.DataSelection.sound
#check Solidity.SolcValidation.DataTable.selection_unique
#print axioms Solidity.SolcValidation.DataTable.selection_unique
#check Solidity.SolcValidation.DataSelection.ext
#print axioms Solidity.SolcValidation.DataSelection.ext
#check Solidity.SolcValidation.DataTable.select_complete
#print axioms Solidity.SolcValidation.DataTable.select_complete
#check Solidity.SolcValidation.DataTable.select_iff
#print axioms Solidity.SolcValidation.DataTable.select_iff
#check Solidity.SolcValidation.ObjectOp
#check Solidity.SolcValidation.Op
#check Solidity.SolcValidation.ObjectOp.name
#check Solidity.SolcValidation.Op.name
#check Solidity.SolcValidation.IrMode
#check Solidity.SolcValidation.compilerVersion
#check Solidity.SolcValidation.compilerSha256
#check Solidity.SolcValidation.Object
#check Solidity.SolcValidation.IrArtifact
#check Solidity.SolcValidation.IrArtifact.root
#check Solidity.SolcValidation.evm_name
#print axioms Solidity.SolcValidation.evm_name
#check Solidity.SolcValidation.mode_distinct
#print axioms Solidity.SolcValidation.mode_distinct
