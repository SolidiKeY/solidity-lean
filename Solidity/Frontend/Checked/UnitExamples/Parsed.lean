import Solidity.Frontend.Checked.ExprExamples
import Solidity.Frontend.Checked.Certificate

/-!
# Parser certificates of the corpora (G11)

The constructor list of every complete program of the declaration, unit and
expression corpora, each a separate kernel check; split from `Solidity/Frontend/Checked/UnitExamples.lean` to keep each
module under the 8 GiB pre-gate bound.
-/

namespace Solidity.Frontend.Checked

open Solidity.Source
open Solidity.Roadmap.Frontend (Input SourceUnit Settings)


-- Each equality checks the original parser result for one complete program.
-- The coverage proofs rewrite these certificates before their small finite
-- checks, so they do not reduce the parser again for every constructor.
-- The literal lists are kernel-checked outputs, preserving order and duplicates.

theorem parsedCtors_decl0 :
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

theorem parsedCtors_decl1 :
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

theorem parsedCtors_unit0 :
    ctorsOf "pragma solidity ^0.8.0; pragma abicoder v2; import \"a.sol\"; import \"b.sol\" as B;" =
    [.unit, .cons, .pragma, .cons, .pragma, .cons, .importPath, .cons, .importPath, .nil] := by
  decide +kernel

theorem parsedCtors_unit1 :
    ctorsOf "import {x as y, z} from \"c.sol\"; import * as M from \"d.sol\";" =
    [.unit, .cons, .importSymbols, .importAlias, .cons, .importAlias, .nil, .cons,
     .importStar, .nil] := by
  decide +kernel

theorem parsedCtors_unit2 :
    ctorsOf "abstract contract A is B.I, C(1) { constructor(uint a) payable internal m1(a) {} }" =
    [.unit, .cons, .contract, .none, .cons, .inherit, .none, .cons, .inherit, .some,
     .positional, .cons, .lit, .nil, .nil, .cons, .constructor, .cons, .param, .elem,
     .nil, .cons, .modInv, .some, .positional, .cons, .ident, .nil, .nil, .block, .nil,
     .nil, .nil] := by
  decide +kernel

theorem parsedCtors_unit3 :
    ctorsOf "contract A { modifier m1(uint a) virtual { _; } modifier m2; }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .modifier, .some, .cons, .param,
     .elem, .nil, .some, .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .ident, .nil,
     .cons, .modifier, .none, .none, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_unit4 :
    ctorsOf "contract A { function f(uint a) public virtual override(B.I) returns (uint r, bool) {\n     uint x = a; (uint p, , bool q) = g(); (x, r) = (r, x); } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .cons, .param, .elem, .nil,
     .nil, .cons, .param, .elem, .cons, .param, .elem, .nil, .some, .block, .cons,
     .stmtItem, .simpleStmt, .declVar, .varDecl, .elem, .some, .ident, .cons, .stmtItem,
     .simpleStmt, .declTuple, .varDecl, .elem, .cons, .none, .cons, .some, .varDecl,
     .elem, .nil, .call, .ident, .positional, .nil, .cons, .stmtItem, .simpleStmt,
     .exprStmt, .assign, .tuple, .some, .ident, .cons, .some, .ident, .nil, .tuple,
     .some, .ident, .cons, .some, .ident, .nil, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_unit5 :
    ctorsOf "contract A { function f() public {\n     for (uint i = 0; i < 10; i++) { if (i == 3) continue; if (i == 7) break; }\n     for (;;) { break; } } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .forStmt, .some, .declVar, .varDecl, .elem, .some, .lit,
     .some, .order, .ident, .lit, .some, .unarySuffix, .ident, .blockStmt, .block,
     .cons, .stmtItem, .ifStmt, .equality, .ident, .lit, .continueStmt, .none, .cons,
     .stmtItem, .ifStmt, .equality, .ident, .lit, .breakStmt, .none, .nil, .cons,
     .stmtItem, .forStmt, .none, .none, .none, .blockStmt, .block, .cons, .stmtItem,
     .breakStmt, .nil, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_unit6 :
    ctorsOf "contract A { function f() public { while (x > 0) x--; do { x++; } while (x < 5); } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .whileStmt, .order, .ident, .lit, .simpleStmt, .exprStmt,
     .unarySuffix, .ident, .cons, .stmtItem, .doWhile, .blockStmt, .block, .cons,
     .stmtItem, .simpleStmt, .exprStmt, .unarySuffix, .ident, .nil, .order, .ident,
     .lit, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_unit7 :
    ctorsOf "contract A { function f() public { unchecked { x += 1; { x -= 1; } } } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .uncheckedItem, .block, .cons, .stmtItem, .simpleStmt, .exprStmt,
     .assign, .ident, .lit, .cons, .stmtItem, .blockStmt, .block, .cons, .stmtItem,
     .simpleStmt, .exprStmt, .assign, .ident, .lit, .nil, .nil, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_unit8 :
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

theorem parsedCtors_unit9 :
    ctorsOf "contract A { function f() public { emit E(1); revert Err({code: 2});\n     if (x == 0) return (1, true); else { return (x, false); } } }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .emit, .ident, .positional, .cons, .lit, .nil, .cons,
     .stmtItem, .revert, .ident, .named, .cons, .namedArg, .lit, .nil, .cons, .stmtItem,
     .ifStmt, .equality, .ident, .lit, .returnStmt, .some, .tuple, .some, .lit, .cons,
     .some, .lit, .nil, .some, .blockStmt, .block, .cons, .stmtItem, .returnStmt, .some,
     .tuple, .some, .ident, .cons, .some, .lit, .nil, .nil, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_unit10 :
    ctorsOf "contract A { fallback(bytes calldata i) external payable returns (bytes memory) { return i; }\n     receive() external payable {} event E(uint); error Err(uint code); }" =
    [.unit, .cons, .contract, .none, .nil, .cons, .fallback, .fbParams, .param, .elem,
     .nil, .cons, .param, .elem, .nil, .nil, .some, .block, .cons, .stmtItem,
     .returnStmt, .some, .ident, .nil, .cons, .receive, .nil, .some, .block, .nil,
     .cons, .event, .cons, .eventParam, .elem, .nil, .cons, .error, .cons, .errorParam,
     .elem, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_unit11 :
    ctorsOf "interface I is J { function h() external; } library L { function k() internal pure {} }" =
    [.unit, .cons, .interface, .cons, .inherit, .none, .nil, .cons, .function, .nil,
     .nil, .nil, .none, .nil, .cons, .library, .cons, .function, .nil, .nil, .nil,
     .some, .block, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_unit12 :
    ctorsOf "contract D layout at 42 { fallback() external {} }" =
    [.unit, .cons, .contract, .some, .lit, .nil, .cons, .fallback, .fbNoParams, .nil,
     .some, .block, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_expr0 :
    exprCtorsOf "a[1] + b[1:2]" =
    [.addSub, .index, .ident, .some, .lit, .slice, .ident, .some, .lit, .some, .lit] := by
  decide +kernel

theorem parsedCtors_expr1 :
    exprCtorsOf "c.d ** e{x: 1}(f)" =
    [.exp, .member, .ident, .call, .callOptions, .ident, .namedArg, .lit, .nil,
     .positional, .cons, .ident, .nil] := by
  decide +kernel

theorem parsedCtors_expr2 :
    exprCtorsOf "g({y: 2}) << h & i" =
    [.bitAnd, .shift, .call, .ident, .named, .cons, .namedArg, .lit, .nil, .ident,
     .ident] := by
  decide +kernel

theorem parsedCtors_expr3 :
    exprCtorsOf "h ^ i | j < k == l" =
    [.equality, .order, .bitOr, .bitXor, .ident, .ident, .ident, .ident, .ident] := by
  decide +kernel

theorem parsedCtors_expr4 :
    exprCtorsOf "m && n || o" =
    [.or, .and, .ident, .ident, .ident] := by
  decide +kernel

theorem parsedCtors_expr5 :
    exprCtorsOf "z = p ? payable(q) : type(T).max" =
    [.assign, .ident, .cond, .ident, .payableConv, .positional, .cons, .ident, .nil,
     .member, .metaType, .userType] := by
  decide +kernel

theorem parsedCtors_expr6 :
    exprCtorsOf "new uint[](1)" =
    [.call, .new, .array, .elem, .none, .positional, .cons, .lit, .nil] := by
  decide +kernel

theorem parsedCtors_expr7 :
    exprCtorsOf "[1, 2][0]" =
    [.index, .inlineArray, .lit, .cons, .lit, .nil, .some, .lit] := by
  decide +kernel

theorem parsedCtors_expr8 :
    exprCtorsOf "(3, 4)" =
    [.tuple, .some, .lit, .cons, .some, .lit, .nil] := by
  decide +kernel

theorem parsedCtors_expr9 :
    exprCtorsOf "5 gwei" =
    [.litUnit] := by
  decide +kernel

theorem parsedCtors_expr10 :
    exprCtorsOf "uint8(-x)" =
    [.call, .elemType, .positional, .cons, .unaryPrefix, .ident, .nil] := by
  decide +kernel

theorem parsedCtors_expr11 :
    exprCtorsOf "x--" =
    [.unarySuffix, .ident] := by
  decide +kernel

theorem parsedCtors_expr12 :
    exprCtorsOf "a * b % c" =
    [.mulDivMod, .mulDivMod, .ident, .ident, .ident] := by
  decide +kernel

theorem parsedCtors_expr13 :
    exprCtorsOf "\"s\"" =
    [.lit] := by
  decide +kernel

end Solidity.Frontend.Checked
