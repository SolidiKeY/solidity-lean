import Solidity.Frontend.Checked.ExprExamples
import Solidity.Frontend.Checked.Certificate

/-!
# Statement, definition and whole-unit controls (G11)

Kernel-checked witnesses for statements (blocks, `unchecked`, loops,
`break`/`continue` contexts, `try`/`catch`, `emit`, `revert`, assembly),
functions, modifiers, constructors, `fallback`/`receive`, contracts,
interfaces, libraries with inheritance, pragmas and imports; the coverage of
**every** S00 constructor by accepted programs (`allCtors_covered`) and of
every in-profile one by in-profile programs (`profileCtors_covered`); the
G05 parse checker accepting what the producer returns; negative controls.
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

theorem unitCorpus_in_profile :
    unitCorpus.all (fun s => match parseInProfile (ascii s) with
      | .ok _ => true | .error _ => false) = true := by decide +kernel

/-- The constructors of a checked unit. -/
def unitCtors (s : String) : List Ctor := ctorsOf s

/-- **Every S00 constructor** is produced by an accepted program of the
lane's corpora (G09, G10 expressions as statements, G11, Yul). -/
theorem allCtors_covered :
    Ctor.all.all (fun c => corpusCtors.contains c || yulCorpusCtors.contains c) = true := by
  decide +kernel

/-- The constructors used only by assembly bodies other than the canonical
rethrow: outside the profile (`inlineAssembly`). -/
def yulOnly : List Ctor :=
  [.yulBlock, .yulLet, .yulAssign, .yulIf, .yulFor, .yulSwitch, .yulCase, .yulLeave,
    .yulBreak, .yulContinue, .yulFun]

/-- **Every in-profile constructor** is produced by a program admitted by
`parseInProfile` (the expressions as statements of a function). -/
theorem profileCtors_covered :
    (Ctor.all.filter (!yulOnly.contains ·)).all (fun c => profileCorpusCtors.contains c) = true := by
  decide +kernel

/-- The Yul program is rejected precisely (assembly outside the rethrow). -/
theorem yul_rejected :
    (yulCorpus.map fun s => match parse (ascii s) with
      | .ok u => u.rejections.map Excl.id | .error _ => []) = [["inlineAssembly"]] := by
  decide +kernel

/-! ## Statement trees -/

def sx (s : String) : Syn (.stmt .body) := .simpleStmt (.exprStmt (.ident s))

/-- The dangling `else` belongs to the nearest `if`. -/
theorem dangling_else :
    parsesTo (fun n => stmt n .body) "if (a) if (b) x; else y;"
      (.ifStmt va (.ifStmt vb (sx "x") (.some (sx "y"))) .none) = true := by decide +kernel

/-- A declaration is read before an expression: `a.b c;` declares, `a.b;`
evaluates; `revert E();` is a revert statement, `revert("x");` a call. -/
theorem decl_or_expr :
    parsesTo (fun n => stmt n .body) "a.b c;"
      (.simpleStmt (.declVar (.varDecl (.userType ⟨"a", ["b"]⟩) none "c") .none)) &&
    parsesTo (fun n => stmt n .body) "a.b;" (.simpleStmt (.exprStmt (.member va "b"))) &&
    parsesTo (fun n => stmt n .body) "revert E();" (.revert (.ident "E") (.positional .nil)) &&
    parsesTo (fun n => stmt n .body) "revert(\"x\");"
      (.simpleStmt (.exprStmt (.call (.ident "revert") (.positional (.cons (.lit (.str (ascii "x"))) .nil)))))
      = true := by decide +kernel

/-! ## Refused -/

theorem unit_refused :
    unitErr "contract C { function f() public { break; } }" = some (35, "break outside a loop") ∧
    unitErr "contract C { function f() public { while (x) { function g() {} } } }" =
      some (47, "expected an expression") ∧
    unitErr "contract C { function f() public { unchecked { unchecked { } } } }" =
      some (47, "nested unchecked block") ∧
    unitErr "contract C { function f() public { if (x) unchecked { } } }" =
      some (42, "expected an expression") ∧
    unitErr "contract C { function f() public { try g() { } } }" = some (47, "expected a catch clause") ∧
    unitErr "contract C { constructor() virtual {} }" = some (35, "invalid constructor attribute") ∧
    unitErr "contract C { fallback() external returns (uint) {} }" =
      some (48, "fallback without parameters has no returns") ∧
    unitErr "contract C { receive() external external {} }" = some (41, "repeated receive attribute") ∧
    unitErr "contract C is { }" = some (14, "expected an identifier") ∧
    unitErr "pragma solidity ^0.8.0" = some (0, "unterminated pragma") ∧
    unitErr "contract C { function f() public { assembly { let x := } } }" =
      some (55, "expected a Yul expression") ∧
    unitErr "contract C { function f() public { () = g(); } }" = some (43, "expected a primary expression") ∧
    unitErr "contract C { function f() public { (,) = g(); } }" = some (44, "expected a primary expression") := by
  decide +kernel

/-- Outside the profile, refused with the feature: assembly that is not the
rethrow, `layout at` with a non-literal base, `years`. -/
theorem unit_out_of_profile :
    (["contract C { function f() public { assembly { } } }",
      "contract C layout at f() { }",
      "contract C { uint x = 1 years; }"].map fun s => match parseInProfile (ascii s) with
        | .error e => e.msg | .ok _ => "") =
      ["outside the profile: inlineAssembly", "outside the profile: storageLayout",
        "outside the profile: removedUnits"] := by
  decide +kernel

/-! ## The G05 parse stage -/

def demoInput : Input where
  units := [⟨"a.sol", ascii "contract A { uint x; }"⟩, ⟨"b.sol", ascii "import \"a.sol\"; contract B is A { }"⟩]
  main := "b.sol"
  settings := Settings.ofPipeline .legacy

/-- **The producer and checker agree on a two-unit input**, so the input
`Parses` (by `parseChecker.sound`). -/
theorem demo_parses :
    (match produce demoInput with
      | .ok (s, c) => parseChecker.check demoInput s c
      | .error _ => false) = true := by decide +kernel

/-- A wrong syntax is refused: the trees swapped between the units, each
kept under the right name, fail the yield comparison. -/
theorem demo_wrong :
    (match produce demoInput with
      | .ok (s, c) => parseChecker.check demoInput
          ((s.map Prod.fst).zip (s.reverse.map Prod.snd)) c
      | .error _ => true) = false := by decide +kernel

/-- A hand-made tree the parser never returns is refused by the checker's
node conditions: named arguments for a base. -/
theorem demo_named_base :
    parseChecker.check ⟨[⟨"a.sol", ascii "contract C is B({x: 1}) {}"⟩], "a.sol", Settings.ofPipeline .legacy⟩
      [("a.sol", .unit (.cons (.contract false "C" .none
        (.cons (.inherit ⟨"B", []⟩ (.some (.named (.cons (.namedArg "x" (.lit (.num (.dec 1 0 0)))) .nil))))
          .nil) .nil) .nil))] [[]] = false := by decide +kernel

end Solidity.Frontend.Checked

/-- info: 'Solidity.Frontend.Checked.allCtors_covered' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.Checked.allCtors_covered
/-- info: 'Solidity.Frontend.Checked.profileCtors_covered' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.Checked.profileCtors_covered
