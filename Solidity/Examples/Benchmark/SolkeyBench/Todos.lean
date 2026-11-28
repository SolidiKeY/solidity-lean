import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `Todos`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/benchmark/Todos.sol>.

Changes: none beyond `contract!{ … }` spelling; the `@custom:key` clauses are written above their functions, invariants first. `payable(x)` is the identity on an address and is dropped (as in `Benchmark/EtherWallet.lean`); `if (c) s;` gets braces. (solkey's file already drops `create()`).

Verdicts are on the declarations below: a `theorem` is proved, a `def …_obligation` is unknown (its stuck goal and the missing closer or rule in its docstring).
-/

namespace Solidity.Examples.Benchmark.SolkeyBench.Todos

def Todos : Contract := contract!{
  struct Todo {
    string text;
    bool completed;
  }
  Todo[] public todos;
  function get(uint256 _index) public view returns (string memory text, bool completed) {
    Todo storage todo = todos[_index];
    return (todo.text, todo.completed);
  }
  function updateText(uint256 _index, string calldata _text) public {
    Todo storage todo = todos[_index];
    todo.text = _text;
  }
  requires _index < todos.length;
  ensures todos[_index].completed == !\old(todos[_index].completed);
  ensures todos.length == \old(todos.length);
  function toggleCompleted(uint256 _index) public {
    Todo storage todo = todos[_index];
    todo.completed = !todo.completed;
  }
}

local instance : InContract := ⟨Todos⟩

open scoped Scoped

theorem spec_toggleCompleted : ⊢ spec!{ toggleCompleted } := by sol_prove

end Solidity.Examples.Benchmark.SolkeyBench.Todos
