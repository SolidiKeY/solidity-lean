import Solidity.Calculus.Closers
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface

/-!
# solkey open problems: `SolcHigherLevel`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/semantics/open/SolcHigherLevel.sol>.
Changes: `contract!` has one contract and no inheritance, so only the most derived
`SolcHigherLevel`'s functions with an obligation and `bg` are here, with `x` of
`SolcHigherLevelBaseBase` and `creationData` of `SolcHigherLevelCreationContext`; `override`,
`m_derived`, `nf`, `vg`, `ivg` and the modifiers `ctorMod`, `creationMod1` dropped.  The constructor (base
initializers, base constructors called in its header, overridden modifiers) has no reading:
unknown, missing inheritance in the front end (solkey: the same).  A function solkey tags `@custom:key box` or specifies has the obligation `spec!{f}`; an untagged
one solkey's diamond, `msg.value == 0 → wt(storage) → ⟨ f(); ⟩ true`.
-/

namespace Solidity.Examples.SolkeyOpen.SolcHigherLevel

def SolcHigherLevel : Contract := contract!{
  uint x;
  uint256 creationData;
  function creationF3() public { creationData |= 0x300; }
  function creationF4() public { creationData |= 0x4000; }
  function bg() internal pure returns (uint256 r) { return 3; }
  function explicitBaseClass() public pure {
    uint256 g = bg();
    uint256 f = SolcHigherLevelBaseBase.bg();
    assert(g == 3);
    assert(f == 1);
  }
  function inheritedFunction() public pure { uint256 r = SolcHigherLevelBase.bg(); assert(r == 2); }
  function inheritedNamedBaseOrdered() public pure {
    uint256 r = SolcHigherLevelBaseBase.nf({a: 1, b: 2, c: 3});
    assert(r == 14);
  }
  function overriddenFunctionStaticCallParent(uint c, uint d) public {
    require(c == 1 && d == 0);
    SolcHigherLevelBaseBase.init(c, d);
    uint r = x;
    assert(r == c);
  }
}

local instance : InContract := ⟨SolcHigherLevel⟩
open scoped Scoped

/-- Unknown: `sol_prove` leaves `{ se2 := find(storage, creationData) }, { se1 := se2 | 768 },
{ storage := save(storage, creationData, se1) } ⟹ true`, a valid leaf; `sol_leaf; sol_close` stops
(`sol_close_nonlin`).  Missing closer: a leaf that reads `|` (`BinOp.bor`, printed as an escape). -/
def creationF3_obligation : Fml SolcHigherLevel [] := dl!{ msg.value == 0 → wt(storage) → ⟨ creationF3(); ⟩ true }
/-- Unknown: as `creationF3`, with `| 16384`. -/
def creationF4_obligation : Fml SolcHigherLevel [] := dl!{ msg.value == 0 → wt(storage) → ⟨ creationF4(); ⟩ true }
-- Unknown: a base-qualified call `Base.f(…)` is refused by the front end (solkey: "has no rule").
/-- error: Solidity elaboration failed: SolcHigherLevelBaseBase.bg(…): the callee is not a function value -/
#guard_msgs in #check dl!{ ⟨ explicitBaseClass(); ⟩ true }
-- Unknown: as above.
/-- error: Solidity elaboration failed: SolcHigherLevelBase.bg(…): the callee is not a function value -/
#guard_msgs in #check dl!{ ⟨ inheritedFunction(); ⟩ true }
-- Unknown: as above (named arguments).
/-- error: Solidity elaboration failed: SolcHigherLevelBaseBase.nf({…}): SolcHigherLevelBaseBase.nf is not a struct or a function declared before this one -/
#guard_msgs in #check dl!{ ⟨ inheritedNamedBaseOrdered(); ⟩ true }
-- Unknown: as above.
/-- error: Solidity elaboration failed: unknown name SolcHigherLevelBaseBase -/
#guard_msgs in #check spec!{ overriddenFunctionStaticCallParent }

end Solidity.Examples.SolkeyOpen.SolcHigherLevel
