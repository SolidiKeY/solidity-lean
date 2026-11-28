import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: solkey `WETH9`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/real-world/WETH9.sol>,
solkey's 0.8 port of the canonical WETH9
(Etherscan `0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2`).  Distinct from
`Examples/Benchmark/Defi/WrappedEther.lean` (Solmate's WETH, with a supply).

Changes: none but the spelling of `contract!{ … }` and solkey's
`@custom:key` clauses; `requires wad >= 0` holds for every typed `uint`.
`payable(msg.sender).transfer(wad)` is `msg.sender.transfer(wad)`
(`payable(·)` is the identity here).  `receive()` only calls
`deposit()` and is dropped; `transfer` is `@custom:key skip` in solkey and
kept without a clause.
-/

namespace Solidity.Examples.Benchmark.SolkeyMisc.WETH9

/-- solkey's `WETH9.sol`, with its clauses. -/
def WETH9 : Contract := contract!{
  uint8 public decimals = 18;
  mapping(address => uint) public balanceOf;
  mapping(address => mapping(address => uint)) public allowance;
  ensures balanceOf[msg.sender] == \old(balanceOf[msg.sender]) + msg.value;
  ensures net(msg.sender) == \old(net(msg.sender)) + msg.value;
  function deposit() public payable {
    balanceOf[msg.sender] += msg.value;
  }
  ensures balanceOf[msg.sender] == \old(balanceOf[msg.sender]) - wad;
  ensures net(msg.sender) == \old(net(msg.sender)) - wad;
  function withdraw(uint wad) public {
    require(balanceOf[msg.sender] >= wad);
    balanceOf[msg.sender] -= wad;
    msg.sender.transfer(wad);
  }
  ensures \result && allowance[msg.sender][guy] == wad;
  function approve(address guy, uint wad) public returns (bool ok) {
    allowance[msg.sender][guy] = wad;
    return true;
  }
  ensures \result;
  ensures src != dst -> balanceOf[src] == \old(balanceOf[src]) - wad && balanceOf[dst] == \old(balanceOf[dst]) + wad;
  ensures src == dst -> balanceOf[src] == \old(balanceOf[src]);
  ensures src != msg.sender && \old(allowance[src][msg.sender]) != 115792089237316195423570985008687907853269984665640564039457584007913129639935 -> allowance[src][msg.sender] == \old(allowance[src][msg.sender]) - wad;
  function transferFrom(address src, address dst, uint wad) public returns (bool ok) {
    require(balanceOf[src] >= wad);
    if (src != msg.sender && allowance[src][msg.sender] != 115792089237316195423570985008687907853269984665640564039457584007913129639935) {
      require(allowance[src][msg.sender] >= wad);
      allowance[src][msg.sender] -= wad;
    }
    balanceOf[src] -= wad;
    balanceOf[dst] += wad;
    return true;
  }
  function transfer(address dst, uint wad) public returns (bool) {
    return transferFrom(msg.sender, dst, wad);
  }
}

local instance : InContract := ⟨WETH9⟩

open scoped Scoped

/-- `deposit()`: both clauses. -/
theorem spec_deposit : ⊢ spec!{ deposit } := by
  sol_prove
  all_goals (sol_leaf; sol_close)

/- `withdraw(wad)`: unknown.  `spec!{ withdraw }` does not elaborate: inside
this contract `msg.sender.transfer(wad)` is refused ("only push, pop and
transfer are calls on a receiver"), the contract's own `transfer(dst, wad)`
shadowing the built-in.  Missing: receiver-call resolution that prefers the
built-in `address.transfer`. -/

/-- `approve(guy, wad)`. -/
theorem spec_approve : ⊢ spec!{ approve } := by
  sol_prove

/-- `transferFrom(src, dst, wad)`'s four clauses, as solkey states them. -/
def transferFrom_obligation : Fml WETH9 [] := spec!{ transferFrom }
/- Unknown: `sol_prove` leaves two leaves (allowance unlimited; `src == msg.sender`),
each a chain of two `balanceOf` saves under the nested-mapping layout, to be
read back at `src`, `dst` against `old` and the untouched `allowance`;
`sol_leaf; sol_close` exhausts the heartbeat budget there.  Missing: a closer
that splits on `src == dst` and resolves `find` over consecutive mapping
saves with a frame for the sibling root `allowance`. -/

end Solidity.Examples.Benchmark.SolkeyMisc.WETH9
