import Solidity.Calculus.Spec

/-!
# Specifications: solkey's benchmark clauses, as obligations

Each contract is solkey's benchmark contract (`keyext.solidity.examples/benchmark/`)
with its `@custom:key` clauses written where the NatSpec lines stand
(`requires e;`, `ensures e;` above the function).  `spec!{f}` is the
obligation solkey's `SolidityProblemSynthesizer` builds for `f`
(`Calculus/Spec.lean`), and `sol_spec` proves it.

Not here: `Coin.send`, whose debit-and-credit clause `sol_close` does not
close (as in `Examples/Benchmark/Coin.lean`); `ERC20.transfer`, the same; and
the clauses over `net(a)`, which no term reads (EtherWallet, Purchase,
SimpleAuction).
-/
namespace Solidity.Examples.Specs

def Counter : Contract := contract!{
  uint256 public count;
  function get() public view returns (uint256) {
    return count;
  }
  ensures count == \old(count) + 1;
  function inc() public {
    count += 1;
  }
  requires count >= 1;
  ensures count == \old(count) - 1;
  function dec() public {
    count -= 1;
  }
}

section
local instance : InContract := ⟨Counter⟩
/-! `dec()`'s obligation, as solkey's synthesizer states it: the layout,
the `requires`, the snapshot `old := storage`, the call, the `ensures` read
against both storages. -/

/--
info: dl{
  ((0 <= select(storage, count) ∧
            select(storage, count) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧
        select(storage, count) >= 1) →
    { old := storage } [ dec(); ] select(storage, count) = select(old, count) - 1 } : Fml Counter
-/
#guard_msgs in #check spec!{ dec }

/-- `inc()`: `ensures count == \old(count) + 1`. -/
theorem inc_spec : ⊨ spec!{ inc } := by sol_spec
/-- `dec()`: `requires count >= 1`, `ensures count == \old(count) - 1`. -/
theorem dec_spec : ⊨ spec!{ dec } := by sol_spec
end

def Mapping : Contract := contract!{
  mapping(address => uint256) public myMap;
  function get(address _addr) public view returns (uint256) {
    return myMap[_addr];
  }
  requires _i >= 0;
  ensures myMap[_addr] == _i;
  ensures \forall address a; a != _addr -> myMap[a] == \old(myMap[a]);
  function set(address _addr, uint256 _i) public {
    myMap[_addr] = _i;
  }
  ensures myMap[_addr] == 0;
  ensures \forall address a; a != _addr -> myMap[a] == \old(myMap[a]);
  function remove(address _addr) public {
    delete myMap[_addr];
  }
}

section
local instance : InContract := ⟨Mapping⟩
/-- `set(_addr, _i)`: the entry written, every other key kept. -/
theorem set_spec : ⊨ spec!{ set } := by
  sol_spec
/-- `remove(_addr)`: the entry reset to `0`, every other key kept. -/
theorem remove_spec : ⊨ spec!{ remove } := by
  sol_spec
/-- `get(_addr)` has no clause: the obligation is the invariant-free `true`. -/
theorem get_spec : ⊨ spec!{ get } := by
  sol_spec
end

def Coin : Contract := contract!{
  address minter;
  mapping(address => uint) balances;
  requires amount >= 0;
  ensures \old(minter) == msg.sender && minter == \old(minter);
  ensures balances[receiver] == \old(balances[receiver]) + amount;
  ensures \forall address a; a != receiver -> balances[a] == \old(balances[a]);
  function mint(address receiver, uint amount) {
    require(msg.sender == minter);
    balances[receiver] += amount;
  }
  requires amount >= 0;
  ensures \old(balances[msg.sender]) >= amount;
  ensures msg.sender != receiver -> balances[msg.sender] == \old(balances[msg.sender]) - amount && balances[receiver] == \old(balances[receiver]) + amount;
  ensures msg.sender == receiver -> balances[msg.sender] == \old(balances[msg.sender]);
  ensures \forall address a; a != msg.sender && a != receiver -> balances[a] == \old(balances[a]);
  function send(address receiver, uint amount) {
    require(amount <= balances[msg.sender]);
    balances[msg.sender] -= amount;
    balances[receiver] += amount;
  }
}

section
local instance : InContract := ⟨Coin⟩
set_option maxHeartbeats 500000 in
/-- `mint(receiver, amount)`: only the minter mints, the receiver credited,
every other balance kept. -/
theorem mint_spec : ⊨ spec!{ mint } := by
  sol_spec

end


def SimpleStorage : Contract := contract!{
  uint storedData;
  requires x >= 0;
  ensures storedData == x;
  function set(uint x) public {
    storedData = x;
  }
  ensures \result == storedData;
  function get() public view returns (uint) {
    return storedData;
  }
}

section
local instance : InContract := ⟨SimpleStorage⟩
/-- `set(x)`: `ensures storedData == x`. -/
theorem ss_set : ⊨ spec!{ set } := by sol_spec
/-- `get()`: `ensures \result == storedData`. -/
theorem ss_get : ⊨ spec!{ get } := by sol_spec
end

def NestedMapping : Contract := contract!{
  mapping(address => mapping(uint256 => bool)) public nested;
  function get(address _addr1, uint256 _i) public view returns (bool) {
    return nested[_addr1][_i];
  }
  ensures nested[_addr1][_i] == _boo;
  function set(address _addr1, uint256 _i, bool _boo) public {
    nested[_addr1][_i] = _boo;
  }
  ensures !nested[_addr1][_i];
  function remove(address _addr1, uint256 _i) public {
    delete nested[_addr1][_i];
  }
}

section
local instance : InContract := ⟨NestedMapping⟩
set_option maxHeartbeats 500000 in
/-- `set(_addr1, _i, _boo)`: `ensures nested[_addr1][_i] == _boo`, an `<->`. -/
theorem nm_set : ⊨ spec!{ set } := by sol_spec
/-- `remove(_addr1, _i)`: `ensures !nested[_addr1][_i]`. -/
theorem nm_remove : ⊨ spec!{ remove } := by sol_spec
end

def ERC20 : Contract := contract!{
  uint totalSupply;
  mapping(address => uint) balanceOf;
  mapping(address => mapping(address => uint)) allowance;
  requires amount >= 0 && balanceOf[msg.sender] >= amount;
  ensures \result && totalSupply == \old(totalSupply);
  ensures msg.sender != recipient -> balanceOf[msg.sender] == \old(balanceOf[msg.sender]) - amount && balanceOf[recipient] == \old(balanceOf[recipient]) + amount;
  ensures msg.sender == recipient -> balanceOf[msg.sender] == \old(balanceOf[msg.sender]);
  ensures \forall address a; a != msg.sender && a != recipient -> balanceOf[a] == \old(balanceOf[a]);
  function transfer(address recipient, uint amount) returns (bool) {
    balanceOf[msg.sender] -= amount;
    balanceOf[recipient] += amount;
    return true;
  }
  requires amount >= 0;
  ensures \result && allowance[msg.sender][spender] == amount;
  function approve(address spender, uint amount) returns (bool) {
    allowance[msg.sender][spender] = amount;
    return true;
  }
  requires amount >= 0;
  ensures balanceOf[to] == \old(balanceOf[to]) + amount && totalSupply == \old(totalSupply) + amount;
  function _mint(address to, uint amount) {
    balanceOf[to] += amount;
    totalSupply += amount;
  }
}

section
local instance : InContract := ⟨ERC20⟩
/-- `approve(spender, amount)`: `ensures \result && allowance[msg.sender][spender] == amount`. -/
theorem erc_approve : ⊨ spec!{ approve } := by sol_spec
set_option maxHeartbeats 1000000 in
/-- `_mint(to, amount)`: the balance and the supply both up by `amount`. -/
theorem erc_mint : ⊨ spec!{ _mint } := by sol_spec
end

end Solidity.Examples.Specs
