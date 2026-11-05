import Solidity.Yul.Checks.OpenRun
import Solidity.Yul.Checks.DirectControl
namespace Solidity.Yul.Checks.OpenControls
open Closed
namespace Fixture
export Solidity.Yul.Checks.WordAdapter (types x flag ptr initial snapshot prepare scope outside localNames)
end Fixture
open Solidity.Yul.Checks.BlockTyping

def sig : Sig := ⟨0,0⟩
def spinBody : Stmt [sig] (globals Fixture.types) ⟨true,false⟩ 0 :=
  .discard (.call .here Fin.elim0)
def spinBodies : Bodies [sig] (globals Fixture.types) [sig] := .cons spinBody .nil
def switchCode (selector : Word) : Stmt [] Fixture.types ⟨false,false⟩ 0 :=
  .functions [sig] spinBodies
    (.switch (.literal selector) (.cons (word 1) (.discard (.call .here Fin.elim0)) .nil)
      (.assign (Fin.cases (.external Fixture.x.writeRef) Fin.elim0) (.literal (word 99))))
def switchPolicy (selector : Word) : Policy.StmtP .A (switchCode selector) := (Policy.stmt_iff .A _).mp rfl
def initial : WordState Fixture.types 0 := ⟨Fin.elim0,Fixture.initial⟩
def snap {c} (result : WordAdapter.Outcome Fixture.types c 0) : List Nat × String :=
  (Fixture.snapshot result.state.cells,Solidity.Yul.Checks.DirectControl.flowTag result.flow)
def observe {c} (code : Stmt [] Fixture.types c 0) (policy : Policy.StmtP .A code) (fuel : Nat) :=
  (Solidity.Yul.OpenRun.statement fuel .nil code policy initial).map snap
example : observe (switchCode (word 1)) (switchPolicy _) 12 = none := by decide
example : observe (switchCode (word 2)) (switchPolicy _) 12 = some ([99,2,0,0],"normal") := by decide

def bin {F n} (op : Pure 2) (a b : Expr F Fixture.types n 1) : Expr F Fixture.types n 1 :=
  .builtin (.pure op) (Fin.cases a (Fin.cases b Fin.elim0))
def set {F c n} (cell : WordCell Fixture.types) (value : Expr F Fixture.types n 1) : Stmt F Fixture.types c n :=
  .assign (Fin.cases (.external cell.writeRef) Fin.elim0) value
def increment : Stmt [] Fixture.types ⟨false,false⟩ 0 :=
  set Fixture.x (bin .add (.external Fixture.x.readRef) (.literal (word 1)))
def condition : Expr [] Fixture.types 0 1 :=
  bin .lt (.external Fixture.x.readRef) (.literal (word 2))
def continuing : Stmt [] Fixture.types ⟨false,false⟩ 0 :=
  .for_ (set Fixture.x (.literal (word 0))) condition increment
    (.seq (set Fixture.flag (.literal (word 7))) .continue_)
def breaking : Stmt [] Fixture.types ⟨false,false⟩ 0 :=
  .for_ (set Fixture.x (.literal (word 0))) condition increment
    (.seq (set Fixture.flag (.literal (word 7))) .break_)
def continuePolicy : Policy.StmtP .A continuing := (Policy.stmt_iff .A _).mp rfl
def breakPolicy : Policy.StmtP .A breaking := (Policy.stmt_iff .A _).mp rfl
example : observe continuing continuePolicy 32 = some ([2,7,0,0],"normal") := by decide
example : observe breaking breakPolicy 12 = some ([0,7,0,0],"normal") := by decide

def resultSig : Sig := ⟨0,1⟩
def leaveBody : Stmt [resultSig] (globals Fixture.types) ⟨true,false⟩ 1 :=
  .for_ .skip (.literal (word 1))
    (.assign (Fin.cases (.local 0) Fin.elim0) (.literal (word 99)))
    (.seq (.assign (Fin.cases (.local 0) Fin.elim0) (.literal (word 42))) .leave)
def leaveBodies : Bodies [resultSig] (globals Fixture.types) [resultSig] := .cons leaveBody .nil
def leaving : Stmt [] Fixture.types ⟨false,false⟩ 0 :=
  .functions [resultSig] leaveBodies
    (set Fixture.x (.call .here Fin.elim0))
def leavePolicy : Policy.StmtP .A leaving := (Policy.stmt_iff .A _).mp rfl
example : observe leaving leavePolicy 12 = some ([42,2,0,0],"normal") := by decide

def untouchedBody : Stmt [resultSig] (globals Fixture.types) ⟨true,false⟩ 1 := .leave
def untouched : Stmt [] Fixture.types ⟨false,false⟩ 0 :=
  .functions [resultSig] (.cons untouchedBody .nil) (set Fixture.x (.call .here Fin.elim0))
def untouchedPolicy : Policy.StmtP .A untouched := (Policy.stmt_iff .A _).mp rfl
example : observe untouched untouchedPolicy 8 = some ([0,2,0,0],"normal") := by decide

def mutualSource : List (Solidity.Source.Syn .yulStmt) :=
  [assign "x" (call "even" [lit 3]),
   fn "even" ["n"] ["r"]
     [.yulIf (varExpr "n") (list [assign "r" (call "odd" [call "sub" [varExpr "n",lit 1]]),.yulLeave]),
       assign "r" (varExpr "k")],
   fn "odd" ["n"] ["r"]
     [.yulIf (varExpr "n") (list [assign "r" (call "even" [call "sub" [varExpr "n",lit 1]]),.yulLeave]),
       assign "r" (call "add" [varExpr "k",lit 1])]]
def mutualPrepared := (Fixture.prepare mutualSource).toOption.get (by decide)
example : mutualPrepared.openRun 0 Fixture.initial = none := rfl
def mutualWitness : Nonempty (ScopedSyntax.Prepared Fixture.scope .A Fixture.outside Fixture.localNames (list mutualSource)) :=
  ⟨mutualPrepared⟩

/-- info: OPEN_DISCRIMINATORS_PASS:6 exact runtime discriminators;8 actual checked mutual-recursion comparisons; not EVM -/
#guard_msgs in
#eval do
  unless observe (switchCode (word 1)) (switchPolicy _) 12 == none &&
      observe (switchCode (word 2)) (switchPolicy _) 12 == some ([99,2,0,0],"normal") do
    throw (IO.userError "selected switch timeout incorrectly used fallback")
  unless observe continuing continuePolicy 32 == some ([2,7,0,0],"normal") &&
      observe breaking breakPolicy 12 == some ([0,7,0,0],"normal") do
    throw (IO.userError "continue/post versus break discriminator failed")
  unless observe leaving leavePolicy 12 == some ([42,2,0,0],"normal") &&
      observe untouched untouchedPolicy 8 == some ([0,2,0,0],"normal") do
    throw (IO.userError "leave propagation or zero return initialization failed")
  let mut comparisons := 0
  for fuel in [0,1,2,3,4,8,16,32] do
    let direct := (mutualPrepared.openRun fuel Fixture.initial).map snap
    let reference := (mutualPrepared.rawRun fuel Fixture.initial).map snap
    unless direct == reference do throw (IO.userError "mutual recursion source/member-index comparison failed")
    comparisons := comparisons+1
  unless (mutualPrepared.openRun 32 Fixture.initial).map snap == some ([8,2,0,0],"normal") do
    throw (IO.userError "mutual recursion same-arity body selection witness failed")
  unless comparisons == 8 do throw (IO.userError "mutual recursion matrix incomplete")
  IO.println "OPEN_DISCRIMINATORS_PASS:6 exact runtime discriminators;8 actual checked mutual-recursion comparisons; not EVM"
end Solidity.Yul.Checks.OpenControls
