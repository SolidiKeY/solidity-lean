import Solidity.Syntax

/-!
# The string-keyed mapping of `Examples/Tactics/Hashing.lean`

`Names`, `mapping(string => uint) ids`, is §3's contract there.  It lives in
this light module, under the same namespace, so that the decision examples
(`Examples/DecisionHashes.lean`) reach it without building the hashing
examples (`docs/parallelism.md`, P5).
-/

namespace Solidity.Examples.Tactics.Hashing

/-- `mapping(string => uint)`: a `mapping(uint => uint)` keyed by the hash
(`hashKeyRows`). -/
def Names : Contract := contract!{
  mapping(string => uint) ids;
}

end Solidity.Examples.Tactics.Hashing
