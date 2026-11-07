# Proposed audit-only registration fragment

For coordinator review only; no generated roots, central module maps or axiom pins were edited. Keep this outside the core library because census/fidelity modules import Lean tooling. The current per-file acceptance runner already checks these modules. Register an audit-only target only after owner approval.

```lean
import tests.h62.item2.«audit-typing».ClosureCensus
import tests.h62.item2.«audit-typing».ClosureFidelity
import tests.h62.item2.«audit-typing».ClosureWitnesses
import tests.h62.item2.«audit-typing».DeclarationCensus
import tests.h62.item2.«audit-typing».ProvisionedCensus
import tests.h62.item2.«audit-typing».UnitsSuccess
import tests.h62.item2.«audit-typing».UnitsSuccessFidelity
import tests.h62.item2.«audit-typing».ValuesDefaultsFidelity
import tests.h62.item2.«audit-typing».ValuesDefaultsWitnesses
import tests.h62.item2.«audit-typing».ValuesListsFidelity
import tests.h62.item2.«audit-typing».ValuesListsWitnesses
import tests.h62.item2.«audit-typing».ValuesHeredWitnesses
import tests.h62.item2.«audit-typing».ValuesHeredFidelity
import tests.h62.item2.«audit-typing».ValuesOpsWitnesses
import tests.h62.item2.«audit-typing».ValuesOpsFidelity
```

All helper/proof modules remain under the authorized additive tests directory. ProvisionedCensus.lean is generated deterministically by provisioned_census.py from the frozen assigned maps and validated build plans. Bulk signatures, uncovered lists, timings and hashes remain off Git.
