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

-- Each equality checks the original parser result for one complete program.
-- The coverage proofs rewrite these certificates before their small finite
-- checks, so they do not reduce the parser again for every constructor.
-- The literal lists are kernel-checked outputs, preserving order and duplicates.

private theorem parsedCtors_decl0 :
    ctorsOf "struct S { uint a; S[] kids; mapping(uint => S) next; }\n   enum E { A, B, C }\n   type T is address payable;\n   uint constant K = 1;\n   error Bad(uint code, string);\n   event Ev(uint indexed a, bytes b) anonymous;\n   using L for T global;\n   using {add as +, L.sub} for T;\n   using L for *;" =
    [.unit, .cons, .topPart, .struct, .structMember, .elem, .cons, .structMember,
     .array, .userType, .none, .cons, .structMember, .mapping, .userType, .nil, .cons,
     .topPart, .enum, .cons, .topPart, .udvt, .cons, .topPart, .constant, .elem, .lit,
     .cons, .topPart, .error, .cons, .errorParam, .elem, .cons, .errorParam, .elem,
     .nil, .cons, .topPart, .event, .cons, .eventParam, .elem, .cons, .eventParam,
     .elem, .nil, .cons, .topPart, .usingPart, .usingPath, .some, .userType, .cons,
     .topPart, .usingPart, .usingAliases, .usingAlias, .cons, .usingAlias, .nil, .some,
     .userType, .cons, .topPart, .usingPart, .usingPath, .none, .nil] := by
  decide +kernel

private theorem parsedCtors_decl1 :
    ctorsOf "contract C {\n     uint public constant x = 1;\n     bytes32 immutable private h;\n     mapping(address => uint) internal transient t;\n     uint transient;\n     function (uint) external returns (bool) public f;\n     uint[] override(A, B) public xs;\n     struct P { string s; }\n     event Q();\n     error R();\n     function(bytes memory) external public c3;\n     function () internal internal transient fiit;\n     mapping(a.K key => S) byKey;\n     function f(uint[] memory a, S storage s, bytes calldata c) internal {}\n   }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .stateVar, .elem, .some, .lit, .cons,
     .stateVar, .elem, .none, .cons, .stateVar, .mapping, .elem, .none, .cons,
     .stateVar, .elem, .none, .cons, .stateVar, .fnType, .cons, .param, .elem, .nil,
     .cons, .param, .elem, .nil, .none, .cons, .stateVar, .array, .elem, .none, .none,
     .cons, .struct, .structMember, .elem, .nil, .cons, .event, .nil, .cons, .error,
     .nil, .cons, .stateVar, .fnType, .cons, .param, .elem, .nil, .nil, .none, .cons,
     .stateVar, .fnType, .nil, .nil, .none, .cons, .stateVar, .mapping, .userType,
     .none, .cons, .function, .cons, .param, .array, .elem, .none, .cons, .param,
     .userType, .cons, .param, .elem, .nil, .nil, .nil, .some, .block, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_unit0 :
    ctorsOf "pragma solidity ^0.8.0; pragma abicoder v2; import \"a.sol\"; import \"b.sol\" as B;" =
    [.unit, .cons, .pragma, .cons, .pragma, .cons, .importPath, .cons, .importPath, .nil] := by
  decide +kernel

private theorem parsedCtors_unit1 :
    ctorsOf "import {x as y, z} from \"c.sol\"; import * as M from \"d.sol\";" =
    [.unit, .cons, .importSymbols, .importAlias, .cons, .importAlias, .nil, .cons,
     .importStar, .nil] := by
  decide +kernel

private theorem parsedCtors_unit2 :
    ctorsOf "abstract contract A is B.I, C(1) { constructor(uint a) payable internal m1(a) {} }" =
    [.unit, .cons, .contract, .none, .cons, .inherit, .none, .cons, .inherit, .some,
     .positional, .cons, .lit, .nil, .nil, .cons, .constructor, .cons, .param, .elem,
     .nil, .cons, .modInv, .some, .positional, .cons, .ident, .nil, .nil, .block, .nil,
     .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_unit3 :
    ctorsOf "contract A { modifier m1(uint a) virtual { _; } modifier m2; }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .modifier, .some, .cons, .param,
     .elem, .nil, .some, .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .ident, .nil,
     .cons, .modifier, .none, .none, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_unit4 :
    ctorsOf "contract A { function f(uint a) public virtual override(B.I) returns (uint r, bool) {\n     uint x = a; (uint p, , bool q) = g(); (x, r) = (r, x); } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .cons, .param, .elem, .nil,
     .nil, .cons, .param, .elem, .cons, .param, .elem, .nil, .some, .block, .cons,
     .stmtItem, .simpleStmt, .declVar, .varDecl, .elem, .some, .ident, .cons, .stmtItem,
     .simpleStmt, .declTuple, .varDecl, .elem, .cons, .none, .cons, .some, .varDecl,
     .elem, .nil, .call, .ident, .positional, .nil, .cons, .stmtItem, .simpleStmt,
     .exprStmt, .assign, .tuple, .some, .ident, .cons, .some, .ident, .nil, .tuple,
     .some, .ident, .cons, .some, .ident, .nil, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_unit5 :
    ctorsOf "contract A { function f() public {\n     for (uint i = 0; i < 10; i++) { if (i == 3) continue; if (i == 7) break; }\n     for (;;) { break; } } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .forStmt, .some, .declVar, .varDecl, .elem, .some, .lit,
     .some, .order, .ident, .lit, .some, .unarySuffix, .ident, .blockStmt, .block,
     .cons, .stmtItem, .ifStmt, .equality, .ident, .lit, .continueStmt, .none, .cons,
     .stmtItem, .ifStmt, .equality, .ident, .lit, .breakStmt, .none, .nil, .cons,
     .stmtItem, .forStmt, .none, .none, .none, .blockStmt, .block, .cons, .stmtItem,
     .breakStmt, .nil, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_unit6 :
    ctorsOf "contract A { function f() public { while (x > 0) x--; do { x++; } while (x < 5); } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .whileStmt, .order, .ident, .lit, .simpleStmt, .exprStmt,
     .unarySuffix, .ident, .cons, .stmtItem, .doWhile, .blockStmt, .block, .cons,
     .stmtItem, .simpleStmt, .exprStmt, .unarySuffix, .ident, .nil, .order, .ident,
     .lit, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_unit7 :
    ctorsOf "contract A { function f() public { unchecked { x += 1; { x -= 1; } } } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .uncheckedItem, .block, .cons, .stmtItem, .simpleStmt, .exprStmt,
     .assign, .ident, .lit, .cons, .stmtItem, .blockStmt, .block, .cons, .stmtItem,
     .simpleStmt, .exprStmt, .assign, .ident, .lit, .nil, .nil, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_unit8 :
    ctorsOf "contract A { function f() public {\n     try this.f(1) returns (uint v, bool) { x = v; } catch Error(string memory e) { revert(e); }\n     catch (bytes memory d) { assembly { revert(add(d, 32), mload(d)) } } catch { } } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .tryStmt, .call, .member, .ident, .positional, .cons,
     .lit, .nil, .cons, .param, .elem, .cons, .param, .elem, .nil, .block, .cons,
     .stmtItem, .simpleStmt, .exprStmt, .assign, .ident, .ident, .nil, .catchSig,
     .param, .elem, .nil, .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .call,
     .ident, .positional, .cons, .ident, .nil, .nil, .cons, .catchSig, .param, .elem,
     .nil, .block, .cons, .stmtItem, .assembly, .cons, .yulExprStmt, .yulCall, .cons,
     .yulCall, .cons, .yulPath, .cons, .yulLit, .nil, .cons, .yulCall, .cons, .yulPath,
     .nil, .nil, .nil, .nil, .cons, .catchPlain, .block, .nil, .nil, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_unit9 :
    ctorsOf "contract A { function f() public { emit E(1); revert Err({code: 2});\n     if (x == 0) return (1, true); else { return (x, false); } } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .emit, .ident, .positional, .cons, .lit, .nil, .cons,
     .stmtItem, .revert, .ident, .named, .cons, .namedArg, .lit, .nil, .cons, .stmtItem,
     .ifStmt, .equality, .ident, .lit, .returnStmt, .some, .tuple, .some, .lit, .cons,
     .some, .lit, .nil, .some, .blockStmt, .block, .cons, .stmtItem, .returnStmt, .some,
     .tuple, .some, .ident, .cons, .some, .lit, .nil, .nil, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_unit10 :
    ctorsOf "contract A { fallback(bytes calldata i) external payable returns (bytes memory) { return i; }\n     receive() external payable {} event E(uint); error Err(uint code); }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .fallback, .fbParams, .param, .elem,
     .nil, .cons, .param, .elem, .nil, .nil, .some, .block, .cons, .stmtItem,
     .returnStmt, .some, .ident, .nil, .cons, .receive, .nil, .some, .block, .nil,
     .cons, .event, .cons, .eventParam, .elem, .nil, .cons, .error, .cons, .errorParam,
     .elem, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_unit11 :
    ctorsOf "interface I is J { function h() external; } library L { function k() internal pure {} }" =
    [.unit, .cons, .interface, .cons, .inherit, .none, .nil, .cons, .function, .nil,
     .nil, .nil, .none, .nil, .cons, .library, .cons, .function, .nil, .nil, .nil,
     .some, .block, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_unit12 :
    ctorsOf "contract D layout at 42 { fallback() external {} }" =
    [.unit, .cons, .contract, .some, .lit, .nil, .cons, .fallback, .fbNoParams, .nil,
     .some, .block, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_expr0 :
    exprCtorsOf "a[1] + b[1:2]" =
    [.addSub, .index, .ident, .some, .lit, .slice, .ident, .some, .lit, .some, .lit] := by
  decide +kernel

private theorem parsedCtors_expr1 :
    exprCtorsOf "c.d ** e{x: 1}(f)" =
    [.exp, .member, .ident, .call, .callOptions, .ident, .namedArg, .lit, .nil,
     .positional, .cons, .ident, .nil] := by
  decide +kernel

private theorem parsedCtors_expr2 :
    exprCtorsOf "g({y: 2}) << h & i" =
    [.bitAnd, .shift, .call, .ident, .named, .cons, .namedArg, .lit, .nil, .ident,
     .ident] := by
  decide +kernel

private theorem parsedCtors_expr3 :
    exprCtorsOf "h ^ i | j < k == l" =
    [.equality, .order, .bitOr, .bitXor, .ident, .ident, .ident, .ident, .ident] := by
  decide +kernel

private theorem parsedCtors_expr4 :
    exprCtorsOf "m && n || o" =
    [.or, .and, .ident, .ident, .ident] := by
  decide +kernel

private theorem parsedCtors_expr5 :
    exprCtorsOf "z = p ? payable(q) : type(T).max" =
    [.assign, .ident, .cond, .ident, .payableConv, .positional, .cons, .ident, .nil,
     .member, .metaType, .userType] := by
  decide +kernel

private theorem parsedCtors_expr6 :
    exprCtorsOf "new uint[](1)" =
    [.call, .new, .array, .elem, .none, .positional, .cons, .lit, .nil] := by
  decide +kernel

private theorem parsedCtors_expr7 :
    exprCtorsOf "[1, 2][0]" =
    [.index, .inlineArray, .lit, .cons, .lit, .nil, .some, .lit] := by
  decide +kernel

private theorem parsedCtors_expr8 :
    exprCtorsOf "(3, 4)" =
    [.tuple, .some, .lit, .cons, .some, .lit, .nil] := by
  decide +kernel

private theorem parsedCtors_expr9 :
    exprCtorsOf "5 gwei" =
    [.litUnit] := by
  decide +kernel

private theorem parsedCtors_expr10 :
    exprCtorsOf "uint8(-x)" =
    [.call, .elemType, .positional, .cons, .unaryPrefix, .ident, .nil] := by
  decide +kernel

private theorem parsedCtors_expr11 :
    exprCtorsOf "x--" =
    [.unarySuffix, .ident] := by
  decide +kernel

private theorem parsedCtors_expr12 :
    exprCtorsOf "a * b % c" =
    [.mulDivMod, .mulDivMod, .ident, .ident, .ident] := by
  decide +kernel

private theorem parsedCtors_expr13 :
    exprCtorsOf "\"s\"" =
    [.lit] := by
  decide +kernel

private theorem parsedCtors_profileDecl0 :
    profileCtorsOf "struct S { uint a; S[] kids; mapping(uint => S) next; }\n   enum E { A, B, C }\n   type T is address payable;\n   uint constant K = 1;\n   error Bad(uint code, string);\n   event Ev(uint indexed a, bytes b) anonymous;\n   using L for T global;\n   using {add as +, L.sub} for T;\n   using L for *;" =
    [.unit, .cons, .topPart, .struct, .structMember, .elem, .cons, .structMember,
     .array, .userType, .none, .cons, .structMember, .mapping, .userType, .nil, .cons,
     .topPart, .enum, .cons, .topPart, .udvt, .cons, .topPart, .constant, .elem, .lit,
     .cons, .topPart, .error, .cons, .errorParam, .elem, .cons, .errorParam, .elem,
     .nil, .cons, .topPart, .event, .cons, .eventParam, .elem, .cons, .eventParam,
     .elem, .nil, .cons, .topPart, .usingPart, .usingPath, .some, .userType, .cons,
     .topPart, .usingPart, .usingAliases, .usingAlias, .cons, .usingAlias, .nil, .some,
     .userType, .cons, .topPart, .usingPart, .usingPath, .none, .nil] := by
  decide +kernel

private theorem parsedCtors_profileDecl1 :
    profileCtorsOf "contract C {\n     uint public constant x = 1;\n     bytes32 immutable private h;\n     mapping(address => uint) internal transient t;\n     uint transient;\n     function (uint) external returns (bool) public f;\n     uint[] override(A, B) public xs;\n     struct P { string s; }\n     event Q();\n     error R();\n     function(bytes memory) external public c3;\n     function () internal internal transient fiit;\n     mapping(a.K key => S) byKey;\n     function f(uint[] memory a, S storage s, bytes calldata c) internal {}\n   }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .stateVar, .elem, .some, .lit, .cons,
     .stateVar, .elem, .none, .cons, .stateVar, .mapping, .elem, .none, .cons,
     .stateVar, .elem, .none, .cons, .stateVar, .fnType, .cons, .param, .elem, .nil,
     .cons, .param, .elem, .nil, .none, .cons, .stateVar, .array, .elem, .none, .none,
     .cons, .struct, .structMember, .elem, .nil, .cons, .event, .nil, .cons, .error,
     .nil, .cons, .stateVar, .fnType, .cons, .param, .elem, .nil, .nil, .none, .cons,
     .stateVar, .fnType, .nil, .nil, .none, .cons, .stateVar, .mapping, .userType,
     .none, .cons, .function, .cons, .param, .array, .elem, .none, .cons, .param,
     .userType, .cons, .param, .elem, .nil, .nil, .nil, .some, .block, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileUnit0 :
    profileCtorsOf "pragma solidity ^0.8.0; pragma abicoder v2; import \"a.sol\"; import \"b.sol\" as B;" =
    [.unit, .cons, .pragma, .cons, .pragma, .cons, .importPath, .cons, .importPath, .nil] := by
  decide +kernel

private theorem parsedCtors_profileUnit1 :
    profileCtorsOf "import {x as y, z} from \"c.sol\"; import * as M from \"d.sol\";" =
    [.unit, .cons, .importSymbols, .importAlias, .cons, .importAlias, .nil, .cons,
     .importStar, .nil] := by
  decide +kernel

private theorem parsedCtors_profileUnit2 :
    profileCtorsOf "abstract contract A is B.I, C(1) { constructor(uint a) payable internal m1(a) {} }" =
    [.unit, .cons, .contract, .none, .cons, .inherit, .none, .cons, .inherit, .some,
     .positional, .cons, .lit, .nil, .nil, .cons, .constructor, .cons, .param, .elem,
     .nil, .cons, .modInv, .some, .positional, .cons, .ident, .nil, .nil, .block, .nil,
     .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileUnit3 :
    profileCtorsOf "contract A { modifier m1(uint a) virtual { _; } modifier m2; }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .modifier, .some, .cons, .param,
     .elem, .nil, .some, .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .ident, .nil,
     .cons, .modifier, .none, .none, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileUnit4 :
    profileCtorsOf "contract A { function f(uint a) public virtual override(B.I) returns (uint r, bool) {\n     uint x = a; (uint p, , bool q) = g(); (x, r) = (r, x); } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .cons, .param, .elem, .nil,
     .nil, .cons, .param, .elem, .cons, .param, .elem, .nil, .some, .block, .cons,
     .stmtItem, .simpleStmt, .declVar, .varDecl, .elem, .some, .ident, .cons, .stmtItem,
     .simpleStmt, .declTuple, .varDecl, .elem, .cons, .none, .cons, .some, .varDecl,
     .elem, .nil, .call, .ident, .positional, .nil, .cons, .stmtItem, .simpleStmt,
     .exprStmt, .assign, .tuple, .some, .ident, .cons, .some, .ident, .nil, .tuple,
     .some, .ident, .cons, .some, .ident, .nil, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileUnit5 :
    profileCtorsOf "contract A { function f() public {\n     for (uint i = 0; i < 10; i++) { if (i == 3) continue; if (i == 7) break; }\n     for (;;) { break; } } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .forStmt, .some, .declVar, .varDecl, .elem, .some, .lit,
     .some, .order, .ident, .lit, .some, .unarySuffix, .ident, .blockStmt, .block,
     .cons, .stmtItem, .ifStmt, .equality, .ident, .lit, .continueStmt, .none, .cons,
     .stmtItem, .ifStmt, .equality, .ident, .lit, .breakStmt, .none, .nil, .cons,
     .stmtItem, .forStmt, .none, .none, .none, .blockStmt, .block, .cons, .stmtItem,
     .breakStmt, .nil, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileUnit6 :
    profileCtorsOf "contract A { function f() public { while (x > 0) x--; do { x++; } while (x < 5); } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .whileStmt, .order, .ident, .lit, .simpleStmt, .exprStmt,
     .unarySuffix, .ident, .cons, .stmtItem, .doWhile, .blockStmt, .block, .cons,
     .stmtItem, .simpleStmt, .exprStmt, .unarySuffix, .ident, .nil, .order, .ident,
     .lit, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileUnit7 :
    profileCtorsOf "contract A { function f() public { unchecked { x += 1; { x -= 1; } } } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .uncheckedItem, .block, .cons, .stmtItem, .simpleStmt, .exprStmt,
     .assign, .ident, .lit, .cons, .stmtItem, .blockStmt, .block, .cons, .stmtItem,
     .simpleStmt, .exprStmt, .assign, .ident, .lit, .nil, .nil, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileUnit8 :
    profileCtorsOf "contract A { function f() public {\n     try this.f(1) returns (uint v, bool) { x = v; } catch Error(string memory e) { revert(e); }\n     catch (bytes memory d) { assembly { revert(add(d, 32), mload(d)) } } catch { } } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .tryStmt, .call, .member, .ident, .positional, .cons,
     .lit, .nil, .cons, .param, .elem, .cons, .param, .elem, .nil, .block, .cons,
     .stmtItem, .simpleStmt, .exprStmt, .assign, .ident, .ident, .nil, .catchSig,
     .param, .elem, .nil, .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .call,
     .ident, .positional, .cons, .ident, .nil, .nil, .cons, .catchSig, .param, .elem,
     .nil, .block, .cons, .stmtItem, .assembly, .cons, .yulExprStmt, .yulCall, .cons,
     .yulCall, .cons, .yulPath, .cons, .yulLit, .nil, .cons, .yulCall, .cons, .yulPath,
     .nil, .nil, .nil, .nil, .cons, .catchPlain, .block, .nil, .nil, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileUnit9 :
    profileCtorsOf "contract A { function f() public { emit E(1); revert Err({code: 2});\n     if (x == 0) return (1, true); else { return (x, false); } } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .emit, .ident, .positional, .cons, .lit, .nil, .cons,
     .stmtItem, .revert, .ident, .named, .cons, .namedArg, .lit, .nil, .cons, .stmtItem,
     .ifStmt, .equality, .ident, .lit, .returnStmt, .some, .tuple, .some, .lit, .cons,
     .some, .lit, .nil, .some, .blockStmt, .block, .cons, .stmtItem, .returnStmt, .some,
     .tuple, .some, .ident, .cons, .some, .lit, .nil, .nil, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileUnit10 :
    profileCtorsOf "contract A { fallback(bytes calldata i) external payable returns (bytes memory) { return i; }\n     receive() external payable {} event E(uint); error Err(uint code); }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .fallback, .fbParams, .param, .elem,
     .nil, .cons, .param, .elem, .nil, .nil, .some, .block, .cons, .stmtItem,
     .returnStmt, .some, .ident, .nil, .cons, .receive, .nil, .some, .block, .nil,
     .cons, .event, .cons, .eventParam, .elem, .nil, .cons, .error, .cons, .errorParam,
     .elem, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileUnit11 :
    profileCtorsOf "interface I is J { function h() external; } library L { function k() internal pure {} }" =
    [.unit, .cons, .interface, .cons, .inherit, .none, .nil, .cons, .function, .nil,
     .nil, .nil, .none, .nil, .cons, .library, .cons, .function, .nil, .nil, .nil,
     .some, .block, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileUnit12 :
    profileCtorsOf "contract D layout at 42 { fallback() external {} }" =
    [.unit, .cons, .contract, .some, .lit, .nil, .cons, .fallback, .fbNoParams, .nil,
     .some, .block, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileExpr0 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "a[1] + b[1:2]") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .addSub, .index, .ident, .some,
     .lit, .slice, .ident, .some, .lit, .some, .lit, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileExpr1 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "c.d ** e{x: 1}(f)") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .exp, .member, .ident, .call,
     .callOptions, .ident, .namedArg, .lit, .nil, .positional, .cons, .ident, .nil,
     .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileExpr2 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "g({y: 2}) << h & i") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .bitAnd, .shift, .call, .ident,
     .named, .cons, .namedArg, .lit, .nil, .ident, .ident, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileExpr3 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "h ^ i | j < k == l") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .equality, .order, .bitOr,
     .bitXor, .ident, .ident, .ident, .ident, .ident, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileExpr4 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "m && n || o") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .or, .and, .ident, .ident,
     .ident, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileExpr5 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "z = p ? payable(q) : type(T).max") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .assign, .ident, .cond, .ident,
     .payableConv, .positional, .cons, .ident, .nil, .member, .metaType, .userType,
     .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileExpr6 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "new uint[](1)") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .call, .new, .array, .elem,
     .none, .positional, .cons, .lit, .nil, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileExpr7 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "[1, 2][0]") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .index, .inlineArray, .lit,
     .cons, .lit, .nil, .some, .lit, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileExpr8 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "(3, 4)") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .tuple, .some, .lit, .cons,
     .some, .lit, .nil, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileExpr9 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "5 gwei") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .litUnit, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileExpr10 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "uint8(-x)") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .call, .elemType, .positional,
     .cons, .unaryPrefix, .ident, .nil, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileExpr11 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "x--") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .unarySuffix, .ident, .nil, .nil,
     .nil] := by
  decide +kernel

private theorem parsedCtors_profileExpr12 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "a * b % c") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .mulDivMod, .mulDivMod, .ident,
     .ident, .ident, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_profileExpr13 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "\"s\"") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .lit, .nil, .nil, .nil] := by
  decide +kernel

private theorem parsedCtors_yul0 :
    ctorsOf "contract C { function f() public { assembly \"evmasm\" (\"memory-safe\") {\n     let a, b := g()\n     a := 1\n     a.b, c := h()\n     if a { leave }\n     for { let i := 0 } lt(i, 2) { i := add(i, 1) } { break continue }\n     switch a case 0 { } case \"x\" { } default { }\n     function g() -> x, y { x := 0x10 y := true }\n     { }\n   } } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .assembly, .cons, .yulLet, .some, .yulCall, .nil, .cons,
     .yulAssign, .yulLit, .cons, .yulAssign, .yulCall, .nil, .cons, .yulIf, .yulPath,
     .cons, .yulLeave, .nil, .cons, .yulFor, .cons, .yulLet, .some, .yulLit, .nil,
     .yulCall, .cons, .yulPath, .cons, .yulLit, .nil, .cons, .yulAssign, .yulCall,
     .cons, .yulPath, .cons, .yulLit, .nil, .nil, .cons, .yulBreak, .cons, .yulContinue,
     .nil, .cons, .yulSwitch, .yulPath, .cons, .yulCase, .nil, .cons, .yulCase, .nil,
     .nil, .some, .nil, .cons, .yulFun, .cons, .yulAssign, .yulLit, .cons, .yulAssign,
     .yulLit, .nil, .cons, .yulBlock, .nil, .nil, .nil, .nil, .nil] := by
  decide +kernel


-- Aggregate the checked data before rewriting underneath coverage lambdas.
-- This avoids introducing function extensionality into the existing axiom pins.
private def checkedCorpusCtors : List Ctor :=
  [.unit, .cons, .topPart, .struct, .structMember, .elem, .array, .userType, .none,
   .mapping, .nil, .enum, .udvt, .constant, .lit, .error, .errorParam, .event,
   .eventParam, .usingPart, .usingPath, .some, .usingAliases, .usingAlias, .contract,
   .stateVar, .fnType, .param, .function, .block, .pragma, .importPath, .importSymbols,
   .importAlias, .importStar, .inherit, .positional, .constructor, .modInv, .ident,
   .modifier, .stmtItem, .simpleStmt, .exprStmt, .declVar, .varDecl, .declTuple, .call,
   .assign, .tuple, .forStmt, .order, .unarySuffix, .blockStmt, .ifStmt, .equality,
   .continueStmt, .breakStmt, .whileStmt, .doWhile, .uncheckedItem, .tryStmt, .member,
   .catchSig, .assembly, .yulExprStmt, .yulCall, .yulPath, .yulLit, .catchPlain, .emit,
   .revert, .named, .namedArg, .returnStmt, .fallback, .fbParams, .receive, .interface,
   .library, .fbNoParams, .addSub, .index, .slice, .exp, .callOptions, .bitAnd, .shift,
   .bitOr, .bitXor, .or, .and, .cond, .payableConv, .metaType, .new, .inlineArray,
   .litUnit, .elemType, .unaryPrefix, .mulDivMod]

private def checkedYulCtors : List Ctor :=
  [.unit, .cons, .contract, .none, .nil, .function, .some, .block, .stmtItem, .assembly,
   .yulLet, .yulCall, .yulAssign, .yulLit, .yulIf, .yulPath, .yulLeave, .yulFor,
   .yulBreak, .yulContinue, .yulSwitch, .yulCase, .yulFun, .yulBlock]

private theorem corpusCtors_exact : corpusCtors = checkedCorpusCtors := by
  simp only [corpusCtors, declCorpus, unitCorpus, exprCorpus, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    parsedCtors_decl0, parsedCtors_decl1, parsedCtors_unit0, parsedCtors_unit1,
    parsedCtors_unit2, parsedCtors_unit3, parsedCtors_unit4, parsedCtors_unit5,
    parsedCtors_unit6, parsedCtors_unit7, parsedCtors_unit8, parsedCtors_unit9,
    parsedCtors_unit10, parsedCtors_unit11, parsedCtors_unit12, parsedCtors_expr0,
    parsedCtors_expr1, parsedCtors_expr2, parsedCtors_expr3, parsedCtors_expr4,
    parsedCtors_expr5, parsedCtors_expr6, parsedCtors_expr7, parsedCtors_expr8,
    parsedCtors_expr9, parsedCtors_expr10, parsedCtors_expr11, parsedCtors_expr12,
    parsedCtors_expr13]
  decide +kernel

private theorem yulCorpusCtors_exact : yulCorpusCtors = checkedYulCtors := by
  simp only [yulCorpusCtors, yulCorpus, List.flatMap_cons, List.flatMap_nil,
    parsedCtors_yul0]
  decide +kernel

private theorem profileCorpusCtors_exact : profileCorpusCtors = checkedCorpusCtors := by
  simp only [profileCorpusCtors, declCorpus, unitCorpus, exprCorpus, List.map_cons, List.map_nil, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    parsedCtors_profileDecl0, parsedCtors_profileDecl1, parsedCtors_profileUnit0, parsedCtors_profileUnit1,
    parsedCtors_profileUnit2, parsedCtors_profileUnit3, parsedCtors_profileUnit4, parsedCtors_profileUnit5,
    parsedCtors_profileUnit6, parsedCtors_profileUnit7, parsedCtors_profileUnit8, parsedCtors_profileUnit9,
    parsedCtors_profileUnit10, parsedCtors_profileUnit11, parsedCtors_profileUnit12, parsedCtors_profileExpr0,
    parsedCtors_profileExpr1, parsedCtors_profileExpr2, parsedCtors_profileExpr3, parsedCtors_profileExpr4,
    parsedCtors_profileExpr5, parsedCtors_profileExpr6, parsedCtors_profileExpr7, parsedCtors_profileExpr8,
    parsedCtors_profileExpr9, parsedCtors_profileExpr10, parsedCtors_profileExpr11, parsedCtors_profileExpr12,
    parsedCtors_profileExpr13]
  decide +kernel

/-- The constructors of a checked unit. -/
def unitCtors (s : String) : List Ctor := ctorsOf s

/-- **Every S00 constructor** is produced by an accepted program of the
lane's corpora (G09, G10 expressions as statements, G11, Yul). -/
theorem allCtors_covered :
    Ctor.all.all (fun c => corpusCtors.contains c || yulCorpusCtors.contains c) = true := by
  rw [corpusCtors_exact, yulCorpusCtors_exact]
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
  rw [profileCorpusCtors_exact]
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
