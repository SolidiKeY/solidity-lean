import Solidity.Frontend.Checked.Check
import Solidity.Frontend.StatementGrammarH28.G0List
import Solidity.Frontend.StatementGrammarH28.G0Nodes
import Solidity.Frontend.StatementGrammarH28.G0Rejections

/-! Finite kernel controls for every assigned statement/block constructor.
Acceptance and constructor observations are checked, not AST equality or
universal completeness. Sources and expected outcomes match the fixture manifest. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

structure StatementFixture where
  source : String
  accepts : Bool
  profile : Bool
  required : List Ctor

/-- Bounded typed list observation. Only Nat and the parameter-only typed
cell view are matched; the Syn eliminator generalises its category in G0List. -/
def fixtureListCtors {c : Cat} (f : Syn c → List Ctor)
    (fuel : Nat) (xs : Syn (.list c)) : List Ctor :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match g0ListCell xs with
    | none => []
    | some (x, rest) => f x ++ fixtureListCtors f n rest

private def optionalBodyCtorsAt {category : Cat} (tree : Syn category) : List Ctor := by
  apply Syn.casesOn (motive := fun _ _ => List Ctor) tree
  case some => intro category body; exact g0NodeCtors body
  all_goals intros; exact []

private def functionBodyCtorsAt {category : Cat} (tree : Syn category) : List Ctor := by
  apply Syn.casesOn (motive := fun _ _ => List Ctor) tree
  case function =>
    intro topLevel name params vis mutability modifiers virtual overrides returns body
    exact match name with
      | .ident name => if name == "f" then optionalBodyCtorsAt body else []
      | _ => []
  all_goals intros; exact []

def functionBodyCtors (part : Syn (.part false)) : List Ctor :=
  functionBodyCtorsAt part

private def topBodyCtorsAt {category : Cat} (tree : Syn category) : List Ctor := by
  apply Syn.casesOn (motive := fun _ _ => List Ctor) tree
  case contract =>
    intro abstract name layout bases parts
    exact fixtureListCtors functionBodyCtors 64 parts
  all_goals intros; exact []

def topBodyCtors (top : Syn .top) : List Ctor := topBodyCtorsAt top

private def fixtureBodyCtorsAt {category : Cat} (tree : Syn category) : List Ctor := by
  apply Syn.casesOn (motive := fun _ _ => List Ctor) tree
  case unit => intro tops; exact fixtureListCtors topBodyCtors 64 tops
  all_goals intros; exact []

def fixtureBodyCtors (u : Syn .unit) : List Ctor := fixtureBodyCtorsAt u

/-- The profile observation is `Syn.rejections`, read through its Gate G0 twin. -/
theorem statementFixtureCheck_profile (u : Syn .unit) : (g0Rejections u).isEmpty = u.rejections.isEmpty := by
  rw [g0Rejections_eq]

theorem fixtureListCtors_zero {c : Cat} (f : Syn c → List Ctor) (xs : Syn (.list c)) :
    fixtureListCtors f 0 xs = [] := rfl

theorem fixtureListCtors_succ_nil {c : Cat} (f : Syn c → List Ctor) (n : Nat) :
    fixtureListCtors f (n + 1) .nil = [] := rfl

theorem fixtureListCtors_succ_cons {c : Cat} (f : Syn c → List Ctor)
    (n : Nat) (x : Syn c) (xs : Syn (.list c)) :
    fixtureListCtors f (n + 1) (.cons x xs) = f x ++ fixtureListCtors f n xs := rfl

theorem fixtureBodyCtors_unit (tops : Syn (.list .top)) :
    fixtureBodyCtors (.unit tops) = fixtureListCtors topBodyCtors 64 tops := rfl

theorem topBodyCtors_contract (abstract : Bool) (name : String) (layout : Syn (.opt .expr))
    (bases : Syn (.list .inherit)) (parts : Syn (.list (.part false))) :
    topBodyCtors (.contract abstract name layout bases parts) =
      fixtureListCtors functionBodyCtors 64 parts := rfl

def statementFixtureCheck (c : StatementFixture) : Bool :=
  match parse (ascii c.source) with
  | .error _ => !c.accepts
  | .ok u => c.accepts && ((g0Rejections u).isEmpty == c.profile) &&
      c.required.all (fun ctor => (fixtureBodyCtors u).contains ctor)

def statementFixture0 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{{return;}}}\n", true, true, [.blockStmt, .block, .stmtItem, .nil, .cons, .returnStmt]⟩


def statementFixture1 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{uint x;}}\n", true, true, [.simpleStmt, .declVar, .varDecl, .elem]⟩


def statementFixture2 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{uint x=1;}}\n", true, true, [.simpleStmt, .declVar, .some, .lit]⟩


def statementFixture3 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{(,uint x,,uint y,)=(1,2,3,4,5);}}\n", true, true, [.declTuple, .none, .some, .varDecl]⟩


def statementFixture4 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{uint x=0;x=1;}}\n", true, true, [.exprStmt, .assign, .simpleStmt]⟩


def statementFixture5 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{if(true){return;}}}\n", true, true, [.ifStmt, .none]⟩


def statementFixture6 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{if(true){return;}else{return;}}}\n", true, true, [.ifStmt, .some]⟩


def statementFixture7 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{if(true)if(false)return;else return;}}\n", true, true, [.ifStmt, .returnStmt]⟩


def statementFixture8 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{for(;;){break;}}}\n", true, true, [.forStmt, .breakStmt]⟩


def statementFixture9 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{for(uint i=0;i<2;i++){continue;}}}\n", true, true, [.forStmt, .declVar, .order, .unarySuffix, .continueStmt]⟩


def statementFixture10 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{while(false){break;}}}\n", true, true, [.whileStmt, .breakStmt]⟩


def statementFixture11 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{do{continue;}while(false);}}\n", true, true, [.doWhile, .continueStmt]⟩


def statementFixture12 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{return;}}\n", true, true, [.returnStmt, .none]⟩


def statementFixture13 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public returns(uint){return 1;}}\n", true, true, [.returnStmt, .some, .lit]⟩


def statementFixture14 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{unchecked{uint x=0;x++;{x+=1;}}}}\n", true, true, [.uncheckedItem, .blockStmt]⟩


def statementFixture15 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{event E(uint code);function f() public{emit E(1);}}\n", true, true, [.emit, .positional]⟩


def statementFixture16 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{event E(uint code);function f() public{emit E({code:1});}}\n", true, true, [.emit, .named, .namedArg]⟩


def statementFixture17 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{error Err(uint code);function f() public{revert Err(1);}}\n", true, true, [.revert, .positional]⟩


def statementFixture18 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{error Err(uint code);function f() public{revert Err({code:1});}}\n", true, true, [.revert, .named, .namedArg]⟩


def statementFixture19 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function g() external pure returns(uint){return 1;}function f() public{try this.g(){}catch{}}}\n", true, true, [.tryStmt, .catchPlain]⟩


def statementFixture20 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function g() external pure returns(uint){return 1;}function f() public{try this.g()returns(uint v){v;}catch Error(string memory reason){reason;}catch Panic(uint code){code;}catch(bytes memory raw){raw;}}}\n", true, true, [.tryStmt, .catchSig, .param]⟩


def statementFixture21 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function g() external pure returns(uint){return 1;}function f() public{try this.g()returns(uint v){v;}catch{}}}\n", true, true, [.tryStmt, .catchPlain, .param]⟩


def statementFixture22 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{assembly{}}}\n", true, false, [.assembly]⟩


def statementFixture23 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{assembly \"evmasm\" (\"memory-safe\"){let x:=1 pop(x)}}}\n", true, false, [.assembly, .yulLet, .yulExprStmt, .yulCall, .yulPath, .yulLit]⟩


def statementFixture24 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function g() external pure returns(uint){return 1;}function f() public{try this.g(){}catch(bytes memory raw){assembly(\"memory-safe\"){revert(add(raw,32),mload(raw))}}}}\n", true, true, [.tryStmt, .catchSig, .assembly, .yulCall]⟩


def statementFixture25 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{for(;;){unchecked{continue;}}}}\n", true, true, [.forStmt, .uncheckedItem, .continueStmt]⟩


def statementFixture26 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public returns(uint,bool){return(1,true);}}\n", true, true, [.returnStmt, .tuple]⟩


def statementFixture27 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{assembly{let a,b:=pair() let c a,b:=pair() a:=1 if a{pop(b)} for{let i:=0}lt(i,2){i:=add(i,1)}{if eq(i,1){continue}break} switch a case 0{} default{} switch b default{} function pair()->x,y{x:=0x10 y:=true leave} function identity(x)->y{y:=x} {}}}}\n", true, false, [.assembly, .yulBlock, .yulLet, .yulAssign, .yulExprStmt, .yulIf, .yulFor, .yulSwitch, .yulCase, .yulLeave, .yulBreak, .yulContinue, .yulFun, .yulPath, .yulCall, .yulLit]⟩


def statementFixture28 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{break;}}\n", false, true, []⟩


def statementFixture29 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{continue;}}\n", false, true, []⟩


def statementFixture30 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{unchecked{unchecked{}}}}\n", false, true, []⟩


def statementFixture31 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{if(true)unchecked{}}}\n", false, true, []⟩


def statementFixture32 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{else{}}}\n", false, true, []⟩


def statementFixture33 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{if(true){}else{}else{}}}\n", false, true, []⟩


def statementFixture34 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{return}}\n", false, true, []⟩


def statementFixture35 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function g() external pure returns(uint){return 1;}function f() public{try this.g(){}}}\n", false, true, []⟩


def statementFixture36 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function g() external pure returns(uint){return 1;}function f() public{try this.g(){}catch(){}}}\n", false, true, []⟩


def statementFixture37 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function g() external pure returns(uint){return 1;}function f() public{try this.g()return;catch{}}}\n", false, true, []⟩


def statementFixture38 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{for(;;)unchecked{break;}}}\n", false, true, []⟩


def statementFixture39 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{assembly{switch 0}}}\n", false, true, []⟩


def statementFixture40 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{return(;}}\n", false, true, []⟩


def statementFixture41 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{assembly \"other\"{}}}\n", false, true, []⟩


def statementFixture42 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public{return 1;}}\n", true, true, [.returnStmt]⟩


def statementFixture43 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function f() public returns(uint){return;}}\n", true, true, [.returnStmt]⟩


def statementFixture44 : StatementFixture :=
  ⟨"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.38;\ncontract C{function g() external pure returns(uint){return 1;}function f() public{try this.g(){}catch Other(uint code){}}}\n", true, true, [.tryStmt, .catchSig]⟩


def statementFixtures : List StatementFixture := [statementFixture0, statementFixture1, statementFixture2, statementFixture3, statementFixture4, statementFixture5, statementFixture6, statementFixture7, statementFixture8, statementFixture9, statementFixture10, statementFixture11, statementFixture12, statementFixture13, statementFixture14, statementFixture15, statementFixture16, statementFixture17, statementFixture18, statementFixture19, statementFixture20, statementFixture21, statementFixture22, statementFixture23, statementFixture24, statementFixture25, statementFixture26, statementFixture27, statementFixture28, statementFixture29, statementFixture30, statementFixture31, statementFixture32, statementFixture33, statementFixture34, statementFixture35, statementFixture36, statementFixture37, statementFixture38, statementFixture39, statementFixture40, statementFixture41, statementFixture42, statementFixture43, statementFixture44]

def requiredStatementCtors : List Ctor := [.blockStmt, .simpleStmt, .ifStmt, .forStmt, .whileStmt, .doWhile, .continueStmt, .breakStmt, .tryStmt, .returnStmt, .emit, .revert, .assembly, .block, .stmtItem, .uncheckedItem, .declVar, .declTuple, .exprStmt, .catchPlain, .catchSig, .nil, .cons, .none, .some, .yulBlock, .yulLet, .yulAssign, .yulExprStmt, .yulIf, .yulFor, .yulSwitch, .yulCase, .yulLeave, .yulBreak, .yulContinue, .yulFun, .yulPath, .yulCall, .yulLit]

theorem statement_fixture_constructor_inventory :
    requiredStatementCtors.all (fun ctor => statementFixtures.any (fun c => c.accepts && c.required.contains ctor)) = true := by decide +kernel

#print axioms statement_fixture_constructor_inventory
end Solidity.Frontend.StatementGrammarH28
