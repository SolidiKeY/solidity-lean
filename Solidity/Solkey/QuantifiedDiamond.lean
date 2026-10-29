import Solidity.Frontend.Import
import Solidity.Frontend.Problems

/-!
# Scalar quantified loop fixtures from both solc pipelines

The headers retain compiler and source hashes and the distinct pipeline
settings. These are compiler AST-analysis artifacts, not native EVM replays.
-/
solc_import "../../tests/solc/QuantifiedDiamond.ast.json" hash 0x8a38a9595a87fdac as Solc.QuantifiedDiamond entrypoints
solc_import "../../tests/solc/QuantifiedDiamond.viaIR.ast.json" hash 0xedf9cdbe32c38ef7 as SolcIR.QuantifiedDiamond entrypoints
/-- info: 8 obligations declared scoped -/
#guard_msgs in solc_scoped_problems Solc.QuantifiedDiamond
/-- info: 8 obligations declared scoped -/
#guard_msgs in solc_scoped_problems SolcIR.QuantifiedDiamond
