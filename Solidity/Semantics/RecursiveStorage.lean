import Solidity.Semantics.RecursiveStorage.Admission
import Solidity.Semantics.RecursiveStorage.Legacy
import Solidity.Semantics.RecursiveStorage.Observations

/-!
Intrinsically typed graph storage, copy admission and compatibility with
ordinary SVal subtrees over guarded declaration graphs.
This is a foundation for recursive structs, not a replacement for the
current Contract, State, heap, run, terms or calculus. See
`docs/feature-work/recursive-types.md` for the integration boundary.
-/
