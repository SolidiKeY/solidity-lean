import Solidity.Semantics

/-!
# Ports of `keyext.solidity.examples/taclets`: payments (`net` ledger)

`a.transfer(v)` books `net(a) := net(a) - v` with no callback
(`transferNoCallback`, `netHeader.key`). In postconditions `net(a)`
reads the ledger, mirroring `selectSt<[int]>(net, at(a))`.

`net-manual-update.key` (a raw update formula, no program) and
`net-msg-value.key` (`msg.value` is not in the fragment) are not
ported.
-/

namespace Solidity
namespace TacletExamples

/-- `net-transfer-simple.key` -/
example :
    (sol!{ < uint to = 9; to.transfer(5) > (net(to) == -5) }).Holds := by
  native_decide

/-- `net-transfer-capture-receiver.key` (`owner = 7` premise inlined) -/
example :
    (sol!{ < owner = 7; owner.transfer(5) > (net(7) == -5) }).Holds := by
  native_decide

/-- `net-transfer-capture-argument.key` -/
example :
    (sol!{ < uint to = 9; uint x = 3; to.transfer(x + 2) >
           (net(to) == -5) }).Holds := by
  native_decide

/-- Two transfers accumulate on the ledger. -/
example :
    (sol!{ < uint to = 9; to.transfer(5); to.transfer(2) >
           (net(to) == -7) }).Holds := by
  native_decide

/-- Untouched addresses stay at zero. -/
example :
    (sol!{ < uint to = 9; to.transfer(5) > (net(2) == 0) }).Holds := by
  native_decide

/-! ### The balance check (solc/EVM alignment)

`a.transfer(v)` reverts when the contract's own funds (`selfBalance`)
do not cover `v` — the EVM's value-transfer check that solc's
`transfer` inherits. The example stores fund the contract generously,
so the ported tests above run unchanged; these pin the failure mode. -/

/-- With only 3 wei of contract funds, a transfer of 5 reverts: the
diamond judgment fails... -/
example :
    ¬ (sol!{ < uint to = 9; to.transfer(5) > (net(to) == -5) }).Holds
      { Semantics.State.exampleStore with selfBalance := 3 } := by
  native_decide

/-- ... while the box judgment holds vacuously on the revert. -/
example :
    (sol!{ [ uint to = 9; to.transfer(5) ] (net(to) == -5) }).Holds
      { Semantics.State.exampleStore with selfBalance := 3 } := by
  native_decide

/-- An exactly-covered transfer succeeds and drains the balance: the
debit books on the ledger, and a second transfer of the same amount
reverts. -/
example :
    (sol!{ < uint to = 9; to.transfer(5) > (net(to) == -5) }).Holds
      { Semantics.State.exampleStore with selfBalance := 5 } := by
  native_decide

example :
    ¬ (sol!{ < uint to = 9; to.transfer(3); to.transfer(3) >
             (net(to) == -6) }).Holds
      { Semantics.State.exampleStore with selfBalance := 5 } := by
  native_decide

end TacletExamples
end Solidity
