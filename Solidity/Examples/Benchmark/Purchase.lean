import Solidity.Calculus.Close

/-!
# Benchmark: `Purchase`

Source: <https://raw.githubusercontent.com/ethereum/solidity/v0.8.30/docs/examples/safe-remote.rst>
(solkey's `keyext.solidity.examples/benchmark/Purchase.sol`, which drops the
events and the errors; here they stay, and elaborate away).

Changes, each a light hack for what another part of the model has yet to
read:
* `msg.sender`, `msg.value` and `address(this).balance` are the state
  variables `msgSender`, `msgValue` and `thisBalance` (no `msg` or `this`
  here yet);
* the constructor is the function `init` (no constructors here; solkey
  skips it, `@custom:key skip`);
* the spelling of `contract!{ … }`: a branch is a block (`if (c) { revert
  OnlyBuyer(); }`), and a block statement ends with `;`.

The rest is the published text: the enum, the four modifiers applied in the
function headers (inlined, the first listed outermost), the errors and
`revert OnlyBuyer();`, the events and `emit Aborted();`, `payable(…)`.

solkey's clauses about `state` and `buyer` are the theorems below.  Its
clauses about `net(seller)` and `net(buyer)` have no counterpart: no formula
term reads the `net` ledger (`Examples/Net.lean`).  A `requires msg.sender ==
seller` is a premise on `msgSender`.

```solidity
contract Purchase {
    uint public value;
    address payable public seller;
    address payable public buyer;

    enum State { Created, Locked, Release, Inactive }
    // The state variable has a default value of the first member, `State.created`
    State public state;

    modifier condition(bool condition_) {
        require(condition_);
        _;
    }

    /// Only the buyer can call this function.
    error OnlyBuyer();
    /// Only the seller can call this function.
    error OnlySeller();
    /// The function cannot be called at the current state.
    error InvalidState();
    /// The provided value has to be even.
    error ValueNotEven();

    modifier onlyBuyer() {
        if (msg.sender != buyer)
            revert OnlyBuyer();
        _;
    }

    modifier onlySeller() {
        if (msg.sender != seller)
            revert OnlySeller();
        _;
    }

    modifier inState(State state_) {
        if (state != state_)
            revert InvalidState();
        _;
    }

    event Aborted();
    event PurchaseConfirmed();
    event ItemReceived();
    event SellerRefunded();

    // Ensure that `msg.value` is an even number.
    // Division will truncate if it is an odd number.
    // Check via multiplication that it wasn't an odd number.
    constructor() payable {
        seller = payable(msg.sender);
        value = msg.value / 2;
        if ((2 * value) != msg.value)
            revert ValueNotEven();
    }

    /// Abort the purchase and reclaim the ether.
    /// Can only be called by the seller before
    /// the contract is locked.
    function abort()
        external
        onlySeller
        inState(State.Created)
    {
        emit Aborted();
        state = State.Inactive;
        // We use transfer here directly. It is
        // reentrancy-safe, because it is the
        // last call in this function and we
        // already changed the state.
        seller.transfer(address(this).balance);
    }

    /// Confirm the purchase as buyer.
    /// Transaction has to include `2 * value` ether.
    /// The ether will be locked until confirmReceived
    /// is called.
    function confirmPurchase()
        external
        inState(State.Created)
        condition(msg.value == (2 * value))
        payable
    {
        emit PurchaseConfirmed();
        buyer = payable(msg.sender);
        state = State.Locked;
    }

    /// Confirm that you (the buyer) received the item.
    /// This will release the locked ether.
    function confirmReceived()
        external
        onlyBuyer
        inState(State.Locked)
    {
        emit ItemReceived();
        // It is important to change the state first because
        // otherwise, the contracts called using `send` below
        // can call in again here.
        state = State.Release;

        buyer.transfer(value);
    }

    /// This function refunds the seller, i.e.
    /// pays back the locked funds of the seller.
    function refundSeller()
        external
        onlySeller
        inState(State.Release)
    {
        emit SellerRefunded();
        // It is important to change the state first because
        // otherwise, the contracts called using `send` below
        // can call in again here.
        state = State.Inactive;

        seller.transfer(3 * value);
    }
}
```
-/

namespace Solidity.Examples.Benchmark.Purchase

open Proves

/-- `Purchase`, with `msg.sender`, `msg.value`, `address(this).balance` as
state variables and the constructor as `init`. -/
def Purchase : Contract := contract!{
  uint public value;
  address payable public seller;
  address payable public buyer;
  address msgSender;
  uint msgValue;
  uint thisBalance;

  enum State { Created, Locked, Release, Inactive }
  State public state;

  modifier condition(bool condition_) {
    require(condition_);
    _;
  }

  error OnlyBuyer();
  error OnlySeller();
  error InvalidState();
  error ValueNotEven();

  modifier onlyBuyer() {
    if (msgSender != buyer) {
      revert OnlyBuyer();
    };
    _;
  }

  modifier onlySeller() {
    if (msgSender != seller) {
      revert OnlySeller();
    };
    _;
  }

  modifier inState(State state_) {
    if (state != state_) {
      revert InvalidState();
    };
    _;
  }

  event Aborted();
  event PurchaseConfirmed();
  event ItemReceived();
  event SellerRefunded();

  function init() payable {
    seller = payable(msgSender);
    value = msgValue / 2;
    if ((2 * value) != msgValue) {
      revert ValueNotEven();
    };
  }

  function abort()
    external
    onlySeller
    inState(State.Created)
  {
    emit Aborted();
    state = State.Inactive;
    seller.transfer(thisBalance);
  }

  function confirmPurchase()
    external
    inState(State.Created)
    condition(msgValue == (2 * value))
    payable
  {
    emit PurchaseConfirmed();
    buyer = payable(msgSender);
    state = State.Locked;
  }

  function confirmReceived()
    external
    onlyBuyer
    inState(State.Locked)
  {
    emit ItemReceived();
    state = State.Release;
    buyer.transfer(value);
  }

  function refundSeller()
    external
    onlySeller
    inState(State.Release)
  {
    emit SellerRefunded();
    state = State.Inactive;
    seller.transfer(3 * value);
  }
}

local instance : InContract := ⟨Purchase⟩

/-! ## The modifiers, inlined

`abort()` runs `onlySeller`'s check, then `inState(State.Created)`'s with its
parameter bound fresh, then the body; the event is gone. -/

/--
info: if (msgSender != seller) { revert(); } else {  } uint se1 = 0; if (state != se1) { revert(); } else {  } state = 3; seller.transfer(thisBalance);
-/
#guard_msgs in #eval IO.println (Prog.toStr (Prog.inlined (sol{ abort(); })))

/-! ## The clauses -/

/-- `abort()`: `requires msg.sender == seller && state == State.Created`,
`ensures state == State.Inactive`. -/
theorem abort_spec :
    ⊨ dl!{ msgSender == seller ∧ state == State.Created → [ abort(); ] state == State.Inactive } := by
  sol_symex
  sol_close

/-- `abort()` by anyone but the seller reverts (`revert OnlySeller();`): no
run of it ends. -/
theorem abort_onlySeller : ⊨ dl!{ msgSender != seller → [ abort(); ] false } := by
  sol_symex
  sol_close

set_option maxHeartbeats 800000 in
/-- `confirmPurchase()`: `requires state == State.Created && msg.value ==
2 * value` (`value + value`: a formula term has no `*`), `ensures state ==
State.Locked && buyer == msg.sender`. -/
theorem confirmPurchase_spec :
    ⊨ dl!{ state == State.Created ∧ msgValue == value + value →
           [ confirmPurchase(); ] (state == State.Locked ∧ buyer == msgSender) } := by
  sol_symex
  sol_close

/-- `confirmReceived()`: `requires msg.sender == buyer && state ==
State.Locked`, `ensures state == State.Release`. -/
theorem confirmReceived_spec :
    ⊨ dl!{ msgSender == buyer ∧ state == State.Locked →
           [ confirmReceived(); ] state == State.Release } := by
  sol_symex
  sol_close

/-- `refundSeller()`: `requires msg.sender == seller && state ==
State.Release`, `ensures state == State.Inactive`. -/
theorem refundSeller_spec :
    ⊨ dl!{ msgSender == seller ∧ state == State.Release →
           [ refundSeller(); ] state == State.Inactive } := by
  sol_symex
  sol_close

end Solidity.Examples.Benchmark.Purchase
