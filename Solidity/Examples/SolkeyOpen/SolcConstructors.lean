import Solidity.Calculus.Closers
import Solidity.Tools.Counterexample

/-!
# solkey open problems: `SolcConstructors`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/semantics/open/SolcConstructors.sol>.
Changes: `--` is spelt `−−` (`--` opens a Lean comment); `multipleInitializationsAssignExpr` is
left out: `iy = ix += 2;` does not parse (unknown; missing: a compound assignment as an
expression, solkey's own "no rule").  A function solkey tags `@custom:key box` or specifies has the obligation `spec!{f}`; an untagged
one solkey's diamond, `msg.value == 0 → wt(storage) → ⟨ f(); ⟩ true`.
The constructor's diamond is a deployment, from the empty storage.
-/

namespace Solidity.Examples.SolkeyOpen.SolcConstructors

def SolcConstructors : Contract := contract!{
  enum Choice { GoLeft, GoRight, GoStraight, Sit }
  struct D { uint p; bool q; }
  uint constant X = 56;
  Choice constant CHOICES = Choice.GoLeft;
  uint immutable atDecl = 2;
  int immutable immX = 1;
  int immutable immY = 3;
  uint immutable delA;
  uint immutable delB = 0x42;
  uint delC;
  uint ci = 1;
  uint ck = 2;
  uint dw;
  int ds;
  bool dflag;
  address dad;
  uint[] darr;
  mapping(uint => uint) dm;
  Choice dchoice;
  D dst;
  uint immutable u;
  bool immutable b;
  address immutable a;
  uint ix;
  uint iy;
  mapping(uint => uint) m1;
  mapping(uint => uint) m2;
  uint public pi;
  uint public pk;
  constructor(uint newI, uint newK) {
    pi = newI;
    pk = newK;
    { uint rpi = pi; uint rpk = pk; assert(rpi == newI); assert(rpk == newK); }
    ci = ci + ci;
    ck = ck - ci;
    immX−−; −−immX; immY++; ++immY; −−immY;
    delete delA;
    delete delB;
    delC = delB * 2 + delA;
    uint ri = ci; uint rk = ck;
    assert(ri == 2); assert(rk == 0);
    uint ra = atDecl;
    assert(ra == 2);
    int rx = immX; int ry = immY; int expected = -1;
    assert(rx == expected); assert(ry == 4);
    uint da = delA; uint db = delB; uint dc = delC;
    assert(da == 0); assert(db == 0); assert(dc == 0);
    uint cx = X; Choice cc = CHOICES;
    assert(cx == 56); assert(cc == Choice.GoLeft);
    uint rw = dw; int rs = ds; bool rf = dflag; address rad = dad; uint rl = darr.length;
    uint rm = dm[5]; Choice rch = dchoice; uint rp = dst.p; bool rq = dst.q;
    assert(rw == 0); assert(rs == 0); assert(rf == false); assert(rad == address(0));
    assert(rl == 0); assert(rm == 0); assert(rch == Choice.GoLeft); assert(rp == 0); assert(rq == false);
  }
  function value() internal view returns (uint) { return msg.value; }
  function immutableUninitialized() public view {
    uint ru = u; bool rb = b; address ra = a;
    assert(ru == 0); assert(rb == false); assert(ra == address(0));
  }
  function msgValueZero() public view { uint v = value(); assert(v == 0); }
  function mappingLocalCompoundAssignment() public {
    require(m1[2] == 0 && m2[1] == 0);
    mapping(uint => uint) storage m = m1;
    m[1] = 42;
    (m = m2)[2] = 21;
    uint ra = m1[1]; uint rb = m1[2]; uint rc = m2[1]; uint rd = m2[2];
    assert(ra == 42); assert(rb == 0); assert(rc == 0); assert(rd == 21);
  }
}

local instance : InContract := ⟨SolcConstructors⟩
open scoped Scoped

/-- The deployment runs the initializers and the constructor, and every assertion holds.  Proved. -/
theorem total_constructor : ⊢ dl!{ { storage := mtSt ‖ net := store(mtSt, at(msg.sender), msg.value) ‖
    selfBalance := msg.value } ⟨ constructor(newI, newK); ⟩ true } := by sol_prove
/-- Refuted in the model, as solkey notes: an immutable is plain storage, so over every typed storage
a never-assigned one is unconstrained (the obligation does not start from a deployment). -/
example : ¬ (⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ immutableUninitialized(); ⟩ true }) := by sol_refute
/-- A function that is not `payable` reads `msg.value == 0`.  Proved. -/
theorem total_msgValueZero : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ msgValueZero(); ⟩ true } := by sol_prove
/-- `(m = m2)[2] = 21` rebinds the alias, then writes through it.  Proved. -/
theorem spec_mappingLocalCompoundAssignment : ⊢ spec!{ mappingLocalCompoundAssignment } := by sol_prove

end Solidity.Examples.SolkeyOpen.SolcConstructors
