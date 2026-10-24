import Solidity.Frontend.Import

/-! The pinned solc source for computed reasons and canonical raw rethrows. -/

solc_import "../../tests/solc/ComputedRevert.ast.json" hash 0x10dff782b68e1bca as Solc.ComputedRevert testing

solc_import "../../tests/solc/RevertAssemblyRejected.ast.json" hash 0xf9506f785c685172 as Solc.RevertAssemblyRejected

