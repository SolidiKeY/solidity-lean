import Solidity.Frontend.Checked.ExprExamples
import Solidity.Frontend.Checked.Certificate

/-!
# Statement and unit corpora (G11)

The G11 corpora and their in-profile acceptance (`unitCorpus_in_profile`),
split from `Solidity/Frontend/Checked/UnitExamples.lean` to keep each
module under the 8 GiB pre-gate bound; the coverage theorems are in `UnitExamples.lean`.
-/

namespace Solidity.Frontend.Checked

open Solidity.Source
open Solidity.Roadmap.Frontend (Input SourceUnit Settings)


/-- The statement and unit programs of the G11 corpus (all in the profile). -/
def unitCorpus : List String := [
  "pragma solidity ^0.8.0; pragma abicoder v2; import \"a.sol\"; import \"b.sol\" as B;",
  "import {x as y, z} from \"c.sol\"; import * as M from \"d.sol\";",
  "abstract contract A is B.I, C(1) { constructor(uint a) payable internal m1(a) {} }",
  "contract A { modifier m1(uint a) virtual { _; } modifier m2; }",
  "contract A { function f(uint a) public virtual override(B.I) returns (uint r, bool) {
     uint x = a; (uint p, , bool q) = g(); (x, r) = (r, x); } }",
  "contract A { function f() public {
     for (uint i = 0; i < 10; i++) { if (i == 3) continue; if (i == 7) break; }
     for (;;) { break; } } }",
  "contract A { function f() public { while (x > 0) x--; do { x++; } while (x < 5); } }",
  "contract A { function f() public { unchecked { x += 1; { x -= 1; } } } }",
  "contract A { function f() public {
     try this.f(1) returns (uint v, bool) { x = v; } catch Error(string memory e) { revert(e); }
     catch (bytes memory d) { assembly { revert(add(d, 32), mload(d)) } } catch { } } }",
  "contract A { function f() public { emit E(1); revert Err({code: 2});
     if (x == 0) return (1, true); else { return (x, false); } } }",
  "contract A { fallback(bytes calldata i) external payable returns (bytes memory) { return i; }
     receive() external payable {} event E(uint); error Err(uint code); }",
  "interface I is J { function h() external; } library L { function k() internal pure {} }",
  "contract D layout at 42 { fallback() external {} }"]

/-- An assembly program covering the Yul constructors (outside the profile). -/
def yulCorpus : List String := [
  "contract C { function f() public { assembly \"evmasm\" (\"memory-safe\") {
     let a, b := g()
     a := 1
     a.b, c := h()
     if a { leave }
     for { let i := 0 } lt(i, 2) { i := add(i, 1) } { break continue }
     switch a case 0 { } case \"x\" { } default { }
     function g() -> x, y { x := 0x10 y := true }
     { }
   } } }"]

/-- Every constructor any corpus program of the lane produces, computed
once. -/
def corpusCtors : List Ctor :=
  ((declCorpus ++ unitCorpus).flatMap ctorsOf ++ exprCorpus.flatMap exprCtorsOf).eraseDups

def yulCorpusCtors : List Ctor := (yulCorpus.flatMap ctorsOf).eraseDups

/-- The constructors of a unit admitted by `parseInProfile` (empty if
refused). -/
def profileCtorsOf (s : String) : List Ctor :=
  match parseInProfile (ascii s) with
  | .ok u => u.nodes.map Node.ctor
  | .error _ => []

/-- Every constructor of an in-profile program of the corpora. -/
def profileCorpusCtors : List Ctor :=
  ((declCorpus ++ unitCorpus ++ exprCorpus.map (s!"contract C \{ function f() public \{ {·}; } }")).flatMap
    profileCtorsOf).eraseDups

-- Kernel certificates are checked separately so a single reduction does not
-- retain parser reductions for the whole corpus at once.
private def unitAccepted (s : String) : Bool :=
  match parseInProfile (ascii s) with
  | .ok _ => true
  | .error _ => false

private theorem unitAccepted0 : unitAccepted (unitCorpus[0]!) = true := by decide +kernel
private theorem unitAccepted1 : unitAccepted (unitCorpus[1]!) = true := by decide +kernel
private theorem unitAccepted2 : unitAccepted (unitCorpus[2]!) = true := by decide +kernel
private theorem unitAccepted3 : unitAccepted (unitCorpus[3]!) = true := by decide +kernel
private theorem unitAccepted4 : unitAccepted (unitCorpus[4]!) = true := by decide +kernel
private theorem unitAccepted5 : unitAccepted (unitCorpus[5]!) = true := by decide +kernel
private theorem unitAccepted6 : unitAccepted (unitCorpus[6]!) = true := by decide +kernel
private theorem unitAccepted7 : unitAccepted (unitCorpus[7]!) = true := by decide +kernel
private theorem unitAccepted8 : unitAccepted (unitCorpus[8]!) = true := by decide +kernel
private theorem unitAccepted9 : unitAccepted (unitCorpus[9]!) = true := by decide +kernel
private theorem unitAccepted10 : unitAccepted (unitCorpus[10]!) = true := by decide +kernel
private theorem unitAccepted11 : unitAccepted (unitCorpus[11]!) = true := by decide +kernel
private theorem unitAccepted12 : unitAccepted (unitCorpus[12]!) = true := by decide +kernel

theorem unitCorpus_in_profile :
    unitCorpus.all (fun s => match parseInProfile (ascii s) with
      | .ok _ => true | .error _ => false) = true := by
  change unitCorpus.all unitAccepted = true
  simp only [unitCorpus, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨unitAccepted0, unitAccepted1, unitAccepted2, unitAccepted3, unitAccepted4, unitAccepted5, unitAccepted6, unitAccepted7, unitAccepted8, unitAccepted9, unitAccepted10, unitAccepted11, unitAccepted12⟩

end Solidity.Frontend.Checked
