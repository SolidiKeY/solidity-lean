import Solidity.Frontend.Checked.UnitExamples.Corpus
import Solidity.Frontend.Checked.UnitExamples.Parsed
import Solidity.Frontend.Checked.UnitExamples.ProfileParsed
import Solidity.Frontend.Checked.UnitExamples.ProfileExprParsed

/-!
# Statement, definition and whole-unit controls (G11)

Kernel-checked witnesses for statements (blocks, `unchecked`, loops,
`break`/`continue` contexts, `try`/`catch`, `emit`, `revert`, assembly),
functions, modifiers, constructors, `fallback`/`receive`, contracts,
interfaces, libraries with inheritance, pragmas and imports; the coverage of
**every** S00 constructor by accepted programs (`allCtors_covered`) and of
every in-profile one by in-profile programs (`profileCtors_covered`); the
G05 parse checker accepting what the producer returns; negative controls.

The corpora and the per-program parser certificates are in
`UnitExamples/Corpus.lean`, `UnitExamples/Parsed.lean`,
`UnitExamples/ProfileParsed.lean` and `UnitExamples/ProfileExprParsed.lean`
(8 GiB and 300 s pre-gate bounds).
-/

namespace Solidity.Frontend.Checked

open Solidity.Source
open Solidity.Roadmap.Frontend (Input SourceUnit Settings)

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
