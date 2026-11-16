import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Recursion
import Solidity.Calculus.RecursionCallback
import Solidity.Calculus.MemContract


namespace Solidity.Examples.Tactics.Recursion

open scoped Scoped

/-- A recursive memory return that calls back: a value call in every frame,
then the array allocated. -/
def BuildPay : Contract := contract!{
  uint a;
  ensures r.length == n;
  function buildPay(uint n, uint to) returns (uint[] memory r) {
    (bool ok, ) = to.call{value: 0}("");
    if (n == 0) { r = new uint[](0); return r; }
    uint[] memory s = buildPay(n - 1, to);
    assert(s.length == n - 1);
    r = new uint[](n);
    return r;
  }
}

section BuildPay

local instance instBuildPayExample : InContract := ⟨BuildPay⟩

/-- **A memory return by its contract, with callbacks**
(`ProvesC.recContractM`, `holdsC_callMemM`): the contract over the callback
runs and a grown heap (`RecContractCM`, `ExecP.frameM`), by induction over
the frames; the frame's `assert` reads the frame below's array off it. -/
theorem buildPayLen :
    ValidT .noCallback dl!{ [ uint[] memory q = buildPay(3, to); ] q.length == 3 } := by
  rec_auto_c

end BuildPay

/-- A recursive memory return whose frame writes into the object it
allocated: a body that writes only its own objects (`Stmt.withinW`). -/
def MakeAge : Contract := contract!{
  uint a;
  ensures p.age == 7;
  function mk(uint n) returns (Person memory p) {
    if (n == 0) { p.age = 7; return p; }
    return mk(n - 1);
  }
}

section MakeAge

local instance instMakeAgeExample : InContract := ⟨MakeAge⟩

/-- **A memory return whose frame writes its own object** (`RecContractM`
with `Prog.withinW`, `Stmt.run_frameW`): the write `p.age = 7` lands in the
frame's own allocation, so the caller's objects are kept and the returned
object read off the contract. -/
theorem mkAge : ⊨ᶠ dl!{ [ Person memory q = mk(2); uint z = q.age; ] z == 7 } := by
  rec_auto

end MakeAge

/-- `payDown` with its condition not captured by hand: `if (a > 0)` is
captured by `ifElseUnfold` under callbacks (`ProvesC.capture`), though the
branch calls back. -/
def PayDownDirect : Contract := contract!{
  uint a;
  function payDown(uint to) {
    if (a > 0) { a = a - 1; (bool ok, ) = to.call{value: 0}(""); payDown(to); }
  }
}

section PayDownDirect

local instance instPayDownDirectExample : InContract := ⟨PayDownDirect⟩

/-- **`payDown` on `if (a > 0)`, with callbacks.** -/
theorem payDownDirect : ValidT .noCallback dl!{ [ payDown(to); ] true } := by rec_auto_c

/-- Under the diamond. -/
theorem payDownDirectEnds : ValidT .noCallback dl!{ ⟨ payDown(to); ⟩ true } := by rec_auto_c

end PayDownDirect

/-! ## A nonlinear contract

The triangular sum's step is `(n - 1) * n / 2 + n == n * (n + 1) / 2`,
and its range checks bound `n * (n + 1)` by `n <= 1000`: `sol_close`'s last
alternative adds solkey's `multiply_2_inEq0` of the bounds of the
products' atoms (`Calculus/CloseNonlin.lean`). -/

def Triangular : Contract := contract!{
  uint a;
  requires n <= 1000;
  ensures r == n * (n + 1) / 2;
  function tri(uint n) returns (uint r) {
    if (n == 0) { return 0; }
    return n + tri(n - 1);
  }
}

section Triangular

local instance instTriangularExample : InContract := ⟨Triangular⟩

/-- `tri`'s contract, by induction over the frames. -/
theorem triSpec : ⊨ᶠ spec!{tri} := by rec_auto

/-- Its caller: `tri(3)` is `6`. -/
theorem triThree : ⊨ᶠ dl!{ [ uint z = tri(3); ] z == 6 } := by rec_auto

end Triangular

end Solidity.Examples.Tactics.Recursion
