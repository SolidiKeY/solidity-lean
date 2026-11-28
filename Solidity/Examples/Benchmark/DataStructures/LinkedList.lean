import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers


/-!
# Benchmark: mapping-linked list

Source (solidity-linked-list v6.5.0):
<https://raw.githubusercontent.com/vittominacori/solidity-linked-list/426dd7fba8c733ba59419758f7d92e7d163cf4c7/contracts/StructuredLinkedList.sol>.
The `List` struct's fields become state variables; `insertAfter` (`_insert`
with `NEXT`) and `remove` become public functions, with the constants
`HEAD`/`NULL` = `0`, `PREV` = `false`, `NEXT` = `true` substituted,
`nodeExists` inlined as the equivalent disjunction, and `_createLink`
inlined at its two (resp. one) call sites in the published order.
The other functions are omitted.

Natural specification: `insertAfter` succeeds exactly when the new node is
absent and the anchor exists; then it links the new node between the
anchor and its old successor (both directions) and grows the size, and
otherwise it changes nothing.  Removing an existing node joins its
neighbours to each other and clears its links.  Both require local link
consistency at the node (`list[list[n][NEXT]][PREV] == n`, and the `PREV`
analogue for `remove`); `remove` also requires that the node is not its own
neighbour, which holds in every list built from the empty one (without it
the clause is false: a self-linked node `n` ends with `list[n][NEXT] == 0`).

Verdicts: `insertAfter`, `remove`: unknown (`remove` clearing proved).
The obligations stop on nested mapping writes whose outer keys may alias
(`list[_new]`, `list[_node]`, `list[c]`): the distinctness the premises
imply (`_new != _node` from existence; `c != _new` from link consistency)
needs a case split on the existence disjunctions that no closer makes.
-/
namespace Solidity.Examples.Benchmark.DataStructures.LinkedList

def LinkedList : Contract := contract!{
  mapping(uint256 => mapping(bool => uint256)) list;
  uint256 size;
  requires list[list[_node][true]][false] == _node;
  ensures \result == (!(\old(list[_new][false]) != 0 || \old(list[_new][true]) != 0 || \old(list[0][true]) == _new) && (\old(list[_node][false]) != 0 || \old(list[_node][true]) != 0 || \old(list[0][true]) == _node));
  ensures \result -> list[_node][true] == _new && list[_new][false] == _node;
  ensures \result -> list[_new][true] == \old(list[_node][true]) && list[\old(list[_node][true])][false] == _new;
  ensures \result -> size == \old(size) + 1;
  ensures !\result -> size == \old(size);
  ensures !\result -> \forall uint256 a; list[a][false] == \old(list[a][false]) && list[a][true] == \old(list[a][true]);
  function insertAfter(uint256 _node, uint256 _new) public returns (bool) {
    bool newExists = list[_new][false] != 0 || list[_new][true] != 0 || list[0][true] == _new;
    bool nodeExists = list[_node][false] != 0 || list[_node][true] != 0 || list[0][true] == _node;
    if (!newExists && nodeExists) {
      uint256 c = list[_node][true];
      list[_new][false] = _node;
      list[_node][true] = _new;
      list[c][false] = _new;
      list[_new][true] = c;
      size += 1;
      return true;
    }
    return false;
  }
  requires _node != 0 && (list[_node][false] != 0 || list[_node][true] != 0 || list[0][true] == _node);
  requires list[list[_node][false]][true] == _node && list[list[_node][true]][false] == _node;
  requires list[_node][false] != _node && list[_node][true] != _node;
  ensures \result == _node;
  ensures list[\old(list[_node][false])][true] == \old(list[_node][true]);
  ensures list[\old(list[_node][true])][false] == \old(list[_node][false]);
  ensures list[_node][false] == 0 && list[_node][true] == 0;
  function remove(uint256 _node) public returns (uint256) {
    bool nodeExists = list[_node][false] != 0 || list[_node][true] != 0 || list[0][true] == _node;
    if (_node == 0 || !nodeExists) {
      return 0;
    }
    uint256 p = list[_node][false];
    uint256 n = list[_node][true];
    list[n][false] = p;
    list[p][true] = n;
    delete list[_node][false];
    delete list[_node][true];
    size -= 1;
    return _node;
  }
}
local instance : InContract := ⟨LinkedList⟩
open scoped Scoped

/-- Unknown: outer-key aliasing (module docstring). -/
def insertAfterTarget := spec!{ insertAfter }
/-- Component of `remove`: a nonzero node ends with both links cleared. -/
theorem remove_clears : ⊢ dl!{ n != 0 → [ uint r = remove(n); ] (list[n][false] == 0 ∧ list[n][true] == 0) } := by
  sol_prove
/-- Unknown: outer-key aliasing (module docstring). -/
def removeTarget := spec!{ remove }

end Solidity.Examples.Benchmark.DataStructures.LinkedList
