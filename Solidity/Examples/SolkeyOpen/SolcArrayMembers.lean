import Solidity.Calculus.Closers
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface

/-!
# solkey open problems: `SolcArrayMembers`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/semantics/open/SolcArrayMembers.sol>.
Changes: none (comments dropped).  A function solkey tags `@custom:key box` or specifies has the obligation `spec!{f}`; an untagged
one solkey's diamond, `msg.value == 0 → wt(storage) → ⟨ f(); ⟩ true`.
-/

namespace Solidity.Examples.SolkeyOpen.SolcArrayMembers

def SolcArrayMembers : Contract := contract!{
  uint[3][90][] copyLarge;
  uint[3][3][] copySmall;
  function copyIncludingArray() public {
    require(copyLarge.length == 0 && copySmall.length == 0);
    for (uint i = 0; i < 7; i++) { copyLarge.push(); copySmall.push(); }
    copyLarge[3][2][0] = 2;
    copyLarge[1] = copyLarge[3];
    copySmall[3][2][0] = 2;
    copySmall[1] = copySmall[2];
    uint r = ((copySmall[3][2][0] * 0x100 | copySmall[1][2][0]) * 0x100 | copyLarge[3][2][0]) * 0x100 |
      copyLarge[1][2][0];
    delete copySmall;
    delete copyLarge;
    assert(r == 0x02000202);
  }
}

local instance : InContract := ⟨SolcArrayMembers⟩
open scoped Scoped

/-- Unknown: `sol_prove` unrolls the seven pushes and both copies and leaves one leaf,
`…, { se24 := se25 | se29 }, …, { se2 := se21 | se35 }, { se38 := se2 == 33554946 } ⟹ se38 = true`;
`sol_leaf; sol_close` times out and `sol_refute` finds no witness.  Missing closer: `|` (`BinOp.bor`)
at a leaf, solkey's own gap ("no rule executes bitwise |"). -/
def copyIncludingArray_obligation : Fml SolcArrayMembers [] := spec!{ copyIncludingArray }

end Solidity.Examples.SolkeyOpen.SolcArrayMembers
