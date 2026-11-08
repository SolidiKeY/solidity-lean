import tests.h62.item2.«audit-language».FixedPointLawWitness
import tests.h62.item2.«audit-language».FixedPointAbiWitness
import tests.h62.item2.«audit-language».FixedPointStorageWitness
import tests.h62.item2.«audit-language».FixedPointLiteralWitness

/-!
Guarded regression: separately checked feasibility families must coexist without
namespace or imported-signature conflicts. This import suite checks composition;
family_coverage.py separately rejects duplicate target/witness credit. The suite
adds no theorem and makes no whole-audit or compiler-success claim.
-/
