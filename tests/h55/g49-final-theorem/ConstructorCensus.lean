import Solidity.Roadmap.G49Final.FoldedPublic
import tests.h62.item5.«statement-graph».Exporter

/-! Test-only constructor census. Reuses the existing elaborated-type exporter;
no witness is registered, no premise is discharged and no core import changes.
The two exports must agree byte-for-byte in the bounded external runner. -/
#h62_export "constructor-contracts.json" [Solidity.Roadmap.Lowering,
  Solidity.Roadmap.Compilation, Solidity.Roadmap.Execution,
  Solidity.Roadmap.Pass, Solidity.Roadmap.Cert,
  Solidity.Roadmap.G49Final.PublicObligations,
  Solidity.Roadmap.G49Final.g49_g50_of_fold]
#h62_export "constructor-contracts-repeat.json" [Solidity.Roadmap.Lowering,
  Solidity.Roadmap.Compilation, Solidity.Roadmap.Execution,
  Solidity.Roadmap.Pass, Solidity.Roadmap.Cert,
  Solidity.Roadmap.G49Final.PublicObligations,
  Solidity.Roadmap.G49Final.g49_g50_of_fold]
