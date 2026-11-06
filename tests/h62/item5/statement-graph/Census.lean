import Solidity.Roadmap.Contracts
import tests.h62.item5.«statement-graph».Exporter

/-! Read-only backfill census. This selects actual declarations from the Lean
namespace, not prose. It assigns no proof ownership and claims no G49/G50 proof. -/
#h62_census "roadmap-census.json" Solidity.Roadmap
#h62_census "roadmap-census-repeat.json" Solidity.Roadmap
