import Solidity.Wp.Verifier

/-!
# solkey `keyext.solidity.examples/net/*.key`, ported

The 21 `net` proof obligations, hand-written rather than generated: they
are `.key` problems, not annotated Solidity, so there is nothing for
`scripts/solkey-port.mjs` to read.

Five are raw ledger machinery over `PiggyBankNet.payTo`/`payToPlus`/
`payOwner` and port directly — `a.transfer(v)` books
`net(a) := net(a) - v` (`transferNoCallback`), and `net(a)` in a
postcondition reads the ledger, mirroring `selectSt<[int]>(net, at(a))`.
The `.key` premise `net = mtSt` is the empty ledger of
`State.exampleStore`, and `!(to = other)` becomes two distinct literals.
These re-prove by `sol_wp` what `Examples/Taclets/NetOps.lean` proves by
`native_decide`.

The other sixteen are the ISoLA-2020 eq.-4 invariant obligations over
`PiggyBankNet`, `EscrowNet`, `AuctionNet`, `AuctionWithdrawNet` and
`CasinoNet`. They are recorded `unsupported` in
`tests/solkey/expected.tsv`, for two reasons that are facts about this
fragment rather than about the calculus:

* they book an incoming payment with `{net := storeSt(net, at(msgSender),
  … + msgValue)}` before the call, and neither `msg.value` nor
  `msg.sender` is in the `sol_expr` grammar; and
* their precondition is an *uninterpreted* `CInv(storage, net)` supplied
  by a per-file `\rules { insertCInv … }`, i.e. a hypothesis over a
  symbolic store — whereas `sol_wp` evaluates from one concrete store, so
  there is no "assume `CInv`" to make.

`net-transfer-withcallback-simple.key` and the two `*-withcallback` POs
need `transferWithCallback`, which `Semantics/Callback.lean` gives a
relational meaning but which the surface `sol_stmt` grammar cannot spell.
-/

namespace Solidity
namespace Solkey
namespace Net

open Semantics Wp

set_option maxHeartbeats 8000000

/-- solkey `net-transfer-simple.key`: `payTo(to)` transfers 5 to its
parameter, booking `net(to) = -5` on the empty ledger while an untouched
address keeps `net(other) = 0`. -/
theorem solkey_Net_net_transfer_simple :
    (sol!{ < uint recipient = 9;
             recipient.transfer(5) >
           ((net(recipient) == -5) && (net(2) == 0)) }).Holds := by
  sol_wp

/-- solkey `net-transfer-capture-argument.key`: `payToPlus(a, x)`
transfers `x + 2`, so the argument is evaluated before the ledger is
booked. -/
theorem solkey_Net_net_transfer_capture_argument :
    (sol!{ < uint recipient = 9; uint x = 3;
             recipient.transfer(x + 2) > (net(recipient) == -5) }).Holds := by
  sol_wp

/-- solkey `net-transfer-capture-receiver.key`: `payOwner()` transfers to
the *value* of the `owner` state variable, captured before the transfer. -/
theorem solkey_Net_net_transfer_capture_receiver :
    (sol!{ < owner = 7;
             owner.transfer(5) > (net(7) == -5) }).Holds := by
  sol_wp

/-- Two transfers accumulate on the ledger (the `net` half of
`net-transfer-simple.key`, iterated). -/
theorem solkey_Net_net_transfer_accumulates :
    (sol!{ < uint recipient = 9;
             recipient.transfer(5); recipient.transfer(2) > (net(recipient) == -7) }).Holds := by
  sol_wp

end Net
end Solkey
end Solidity
