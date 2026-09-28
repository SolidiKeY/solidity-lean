import Solidity.Semantics

/-!
# Decidable equality for the semantic carriers

`MObj`/`State`/`Except` derive on top of `SVal`'s instance, which is
written out by hand in `Semantics.lean` (a nested inductive, which the
deriving handler does not support on this toolchain): `Binding` holds a
storage and derives its own. Shared by every module
that closes a concrete interpreter run by `native_decide`
(`Counterexamples/`, `Reachability`).
-/

namespace Solidity
namespace Semantics

deriving instance DecidableEq for MObj
deriving instance DecidableEq for State
deriving instance DecidableEq for Except

end Semantics
end Solidity
