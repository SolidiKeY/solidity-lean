import Solidity.Frontend.Checked.UnitExamples.Corpus

/-!
# Profile parser certificates of the expression and Yul programs (G11)

The constructor list `parseInProfile` produces for every expression program
(as a statement of a function), and `ctorsOf` of the Yul program; split from `Solidity/Frontend/Checked/UnitExamples.lean` to keep each
module under the 8 GiB pre-gate bound.
-/

namespace Solidity.Frontend.Checked

open Solidity.Source
open Solidity.Roadmap.Frontend (Input SourceUnit Settings)

theorem parsedCtors_profileExpr0 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "a[1] + b[1:2]") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .addSub, .index, .ident, .some,
     .lit, .slice, .ident, .some, .lit, .some, .lit, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_profileExpr1 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "c.d ** e{x: 1}(f)") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .exp, .member, .ident, .call,
     .callOptions, .ident, .namedArg, .lit, .nil, .positional, .cons, .ident, .nil,
     .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_profileExpr2 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "g({y: 2}) << h & i") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .bitAnd, .shift, .call, .ident,
     .named, .cons, .namedArg, .lit, .nil, .ident, .ident, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_profileExpr3 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "h ^ i | j < k == l") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .equality, .order, .bitOr,
     .bitXor, .ident, .ident, .ident, .ident, .ident, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_profileExpr4 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "m && n || o") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .or, .and, .ident, .ident,
     .ident, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_profileExpr5 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "z = p ? payable(q) : type(T).max") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .assign, .ident, .cond, .ident,
     .payableConv, .positional, .cons, .ident, .nil, .member, .metaType, .userType,
     .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_profileExpr6 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "new uint[](1)") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .call, .new, .array, .elem,
     .none, .positional, .cons, .lit, .nil, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_profileExpr7 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "[1, 2][0]") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .index, .inlineArray, .lit,
     .cons, .lit, .nil, .some, .lit, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_profileExpr8 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "(3, 4)") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .tuple, .some, .lit, .cons,
     .some, .lit, .nil, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_profileExpr9 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "5 gwei") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .litUnit, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_profileExpr10 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "uint8(-x)") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .call, .elemType, .positional,
     .cons, .unaryPrefix, .ident, .nil, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_profileExpr11 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "x--") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .unarySuffix, .ident, .nil, .nil,
     .nil] := by
  decide +kernel

theorem parsedCtors_profileExpr12 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "a * b % c") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .mulDivMod, .mulDivMod, .ident,
     .ident, .ident, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_profileExpr13 :
    profileCtorsOf ((s!"contract C \{ function f() public \{ {·}; } }") "\"s\"") =
    [.unit, .cons, .contract, .none, .nil, .cons, .function, .nil, .nil, .nil, .some,
     .block, .cons, .stmtItem, .simpleStmt, .exprStmt, .lit, .nil, .nil, .nil] := by
  decide +kernel

theorem parsedCtors_yul0 :
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

end Solidity.Frontend.Checked
