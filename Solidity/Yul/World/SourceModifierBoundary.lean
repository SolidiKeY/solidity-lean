import Solidity.Source.Eval
import Solidity.Source.Hoare

/-! Actual typed modifier/placeholder execution input. This is not a frontend
elaboration/deployment certificate or universal callee preservation theorem. -/
namespace Solidity.Yul.World.SourceModifierBoundary
open Solidity.Source
open Solidity.Roadmap (Bytes)

def uint : STy := .int IntTy.u256
def value : Nat := 0x12 * 2^248 + 0x99

def functionDecl : Decl := ⟨.function,"go",some "Guarded",false,
  .function (.ident "go") .nil (some .external) (some .payable)
    (.cons (.modInv ⟨"around",[]⟩ (.some (.positional .nil))) .nil) false none .nil
    (.some (.block .nil))⟩
def errorDecl : Decl := ⟨.error,"ModDenied",some "Guarded",false,
  .error "ModDenied" (.cons (.errorParam (.elem (.int false 256 (by decide))) none) .nil)⟩
def failureSyntax : Syn (.stmt .body) :=
  .revert (.ident "ModDenied") (.positional (.cons (.lit (.num (.dec value 0 0))) .nil))
def modifierItems (failed : Bool) : Syn (.list (.item .body)) :=
  .cons (.stmtItem (.simpleStmt (.exprStmt (.ident "_"))))
    (if failed then .cons (.stmtItem failureSyntax) .nil else .nil)
def modifierDecl (failed : Bool) : Decl := ⟨.modifier,"around",some "Guarded",false,
  .modifier "around" (.some .nil) false none (.some (.block (modifierItems failed)))⟩
def env (failed : Bool) : Env := ⟨[functionDecl,errorDecl,modifierDecl failed]⟩
def modifierBody (failed : Bool) : RBody (env failed) :=
  ⟨[],[],true,[],[],.stmt (.placeholder rfl)
    (if failed then .stmt (.revertError errorDecl rfl
      (.cons (.const (Q.ofInt value)) (by cases failed <;> decide) .nil)) .nil else .nil),[]⟩
def body (failed : Bool) : RBody (env failed) :=
  ⟨[],[],false,[],[],.nil,[⟨modifierDecl failed,[],.nil⟩]⟩
def glob {failed} (G : Glob (env failed)) : Glob (env failed) :=
  {G with prog:={G.prog with contracts:=["Guarded"],body:=fun d=>if d.name="go" then some (body failed) else if d.name="around" then some (modifierBody failed) else none}}
def data {failed} (G : Glob (env failed)) : Bytes :=
  G.selector (sigOf (env failed).layout "ModDenied" [uint])++wordBytes (Source.intWord (value : Int))

/-- Actual placeholder completion and post-placeholder typed error, preserving
the entire caller Source state, including arbitrary function locals. -/
theorem actual {failed} (G : Glob (env failed)) (F : Fr) (s : EMState (env failed) [])
    (code : F.contract="Guarded") :
    (Source.runMods (glob G) F 7 (body failed) (body failed).mods .nil).run s=
      ((if failed then .error (.revert (data G)) else .ok .nil),s) := by
  cases F with
  | mk owner sender amount static contract checked depth cd =>
    change contract="Guarded" at code
    subst contract
    cases failed <;> cases G with
    | mk program pipeline fixed balance hasCode strategy timestamp => cases pipeline <;> rfl

/-- A genuine timeout during placeholder/body execution, after installing the
function-local frame. The outer modifier restores its saved caller state. -/
theorem entered_timeout {failed} (G : Glob (env failed)) (F : Fr) (s : EMState (env failed) [])
    (code : F.contract="Guarded") :
    (Source.runMods (glob G) F 4 (body failed) (body failed).mods .nil).run s=
      (.error .timeout,s) := by
  cases F with
  | mk owner sender amount static contract checked depth cd =>
    change contract="Guarded" at code
    subst contract
    cases failed <;> cases G with
    | mk program pipeline fixed balance hasCode strategy timestamp => cases pipeline <;> rfl

end Solidity.Yul.World.SourceModifierBoundary
