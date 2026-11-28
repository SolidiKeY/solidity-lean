import Solidity.Calculus.Closers
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface

/-!
# solkey open problems: `SolcStructsMappings`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/semantics/open/SolcStructsMappings.sol>.
Changes: none (comments dropped).  A function solkey tags `@custom:key box` or specifies has the obligation `spec!{f}`; an untagged
one solkey's diamond, `msg.value == 0 → wt(storage) → ⟨ f(); ⟩ true`.
solkey generates no obligation for a struct `calldata` parameter; the front end refuses both
bodies.
-/

namespace Solidity.Examples.SolkeyOpen.SolcStructsMappings

def SolcStructsMappings : Contract := contract!{
  struct S8 { uint8 x; }
  S8 s8;
  mapping(uint8 => S8[2]) m1s;
  mapping(uint8 => S8[]) m2s;
  function structFromCalldataToStaticArrayInMapping(S8 calldata sCalldata) public {
    require(m1s[0][0].x == 0);
    require(sCalldata.x == 8);
    s8.x = 7;
    m1s[0][1] = sCalldata;
    S8[2] memory r = m1s[0];
    assert(r[0].x == 0);
    assert(r[1].x == 8);
  }
  function structFromCalldataToDynamicArrayInMapping(S8 calldata sCalldata) public {
    require(m2s[0].length == 0);
    require(sCalldata.x == 8);
    s8.x = 7;
    m2s[0].push();
    m2s[0][0] = sCalldata;
    S8[] memory r = m2s[0];
    assert(r.length == 1);
    assert(r[0].x == 8);
  }
}

local instance : InContract := ⟨SolcStructsMappings⟩
open scoped Scoped

-- Unknown: no obligation.  Missing: a copy of a `calldata` struct into storage.
/-- error: Solidity elaboration failed: m1s[0][1]: a write through calldata or a memory binding of it: solc refuses the first and copies calldata to memory for the second, where the model would share the object -/
#guard_msgs in #check spec!{ structFromCalldataToStaticArrayInMapping }
-- Unknown: no obligation; the refusal is at `m2s[0].push()`, before the copy.
/-- error: Solidity elaboration failed: m2s[0].push: a write through calldata or a memory binding of it: solc refuses the first and copies calldata to memory for the second, where the model would share the object -/
#guard_msgs in #check spec!{ structFromCalldataToDynamicArrayInMapping }

end Solidity.Examples.SolkeyOpen.SolcStructsMappings
