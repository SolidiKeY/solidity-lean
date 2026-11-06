import Solidity.Yul.ScopedWordSyntax
import Solidity.Yul.Checks.BlockTyping
namespace Solidity.Yul.Checks.WordAdapter
open Solidity.Source (Syn)
open Solidity.Yul.Checks.BlockTyping

def types : List ExternalType :=
  [.value (.unsigned 0),.value .boolean,.externalFunction,.constant (word 7),.memory]
def declarations : ExternalNames types := [
  ("x",⟨_,.here⟩),("flag",⟨_,.there .here⟩),("ptr",⟨_,.there (.there .here)⟩),
  ("k",⟨_,.there (.there (.there .here))⟩),
  ("mem",⟨_,.there (.there (.there (.there .here)))⟩)]
def names : ScopedNames.Checked declarations := ⟨by decide⟩
def scope : BlockScope.Scope types := .external names .root
def outside := ["x","flag","ptr","k","mem"]
def localNames := ["x","flag","ptr","mem"]
def x : WordCell types := .scalar ⟨.unsigned 0,.here⟩
def flag : WordCell types := .scalar ⟨.boolean,.there .here⟩
def ptr : Member types .externalFunction := .there (.there .here)
def initial : WordCells types := fun cell =>
  if cell.key = x.key then word 257 else if cell.key = flag.key then word 2 else word 0
def snapshot (cells : WordCells types) : List Nat :=
  [cells x |>.val,cells flag |>.val,cells (.address ptr) |>.val,cells (.selector ptr) |>.val]
def prepare (body : List (Syn .yulStmt)) :=
  Solidity.Yul.ScopedSyntax.prepare scope .A outside localNames (list body)
def prepared (body : List (Syn .yulStmt)) : Bool := (prepare body).isOk
def observe (body : List (Syn .yulStmt)) (fuel : Nat) : Option (List Nat) :=
  match prepare body with
  | .error _ => none
  | .ok p => (p.rawRun fuel initial).map (fun result => snapshot result.state.cells)

def project (body : List (Syn .yulStmt)) (fuel : Nat) (cell : WordCell types) : Option Word :=
  match prepare body with
  | .error _ => none
  | .ok p => (p.rawRun fuel initial).map (fun result => result.state.cells cell)

theorem observe_agrees (body : List (Syn .yulStmt)) (fuel : Nat) (a b c d : Word)
    (one : project body fuel x = some a) (two : project body fuel flag = some b)
    (three : project body fuel (.address ptr) = some c)
    (four : project body fuel (.selector ptr) = some d) :
    observe body fuel = some [a.val,b.val,c.val,d.val] := by
  unfold project at one two three four
  unfold observe
  cases prepared : prepare body with
  | error reason => rw [prepared] at one; cases one
  | ok p =>
    rw [prepared] at one two three four
    dsimp only at one two three four ⊢
    cases finished : p.rawRun fuel initial with
    | none => rw [finished] at one; cases one
    | some result =>
      rw [finished] at one two three four
      have ha := Option.some.inj one
      have hb := Option.some.inj two
      have hc := Option.some.inj three
      have hd := Option.some.inj four
      dsimp only at ha hb hc hd
      change some (snapshot result.state.cells) = _
      change some [_,_,_,_] = _
      rw [ha,hb,hc,hd]

def field (attr : String) : Syn .yulExpr := .yulPath "ptr" [attr]
def writeField (attr : String) (rhs : Syn .yulExpr) : Syn .yulStmt :=
  .yulAssign ["ptr",attr] [] rhs

def dirty := [assign "x" (lit 257),assign "flag" (lit 2),
  writeField "address" (call "not" [lit 0]),writeField "selector" (call "not" [lit 0])]
def bound := [decl "saved" (varExpr "x"),zero "temporary",
  block [decl "inside" (lit 1),assign "x" (call "add" [varExpr "saved",varExpr "inside"])]]
def mulDiv := [
  assign "x" (call "mulDiv" [varExpr "x",varExpr "k",lit 3]),
  fn "mulDiv" ["a","b","denominator"] ["r"] [
    decl "product" (call "mul" [varExpr "a",varExpr "b"]),
    assign "r" (call "div" [varExpr "product",varExpr "denominator"])]]
def recursive := [
  assign "x" (call "sum" [lit 3]),
  fn "sum" ["n"] ["r"] [
    .yulIf (varExpr "n") (list [
      assign "r" (call "add" [varExpr "n",call "sum" [call "sub" [varExpr "n",lit 1]]]),
      .yulLeave]),
    assign "r" (varExpr "k")]]
def looping := [loop [decl "i" (lit 0)] (call "lt" [varExpr "i",lit 4])
  [assign "i" (call "add" [varExpr "i",lit 1]),
   writeField "selector" (call "add" [field "selector",lit 1])]
  [.yulIf (call "eq" [varExpr "i",lit 1]) (list [.yulContinue]),
   .yulIf (call "eq" [varExpr "i",lit 3]) (list [.yulBreak]),
   assign "x" (call "add" [varExpr "x",varExpr "i"])]]
def pair := [Syn.yulAssign ["x"] [["flag"]] (call "pair" [varExpr "flag",varExpr "x"]),
  fn "pair" ["a","b"] ["r","s"] [assign "r" (varExpr "a"),assign "s" (varExpr "b")]]
def switched : List (Syn .yulStmt) := [.yulSwitch (varExpr "x")
  (list [.yulCase (.dec 257) (list [assign "flag" (lit 2)])])
  (.some (list [assign "flag" (lit 1)]))]
def division := [assign "x" (call "div" [varExpr "x",lit 0]),
  assign "flag" (call "mod" [lit 257,lit 0])]
def crossed := [writeField "address" (lit 257),
  writeField "selector" (call "not" [lit 0])]
def never := [loop [] (lit 1) [] []]


end Solidity.Yul.Checks.WordAdapter
