import Solidity.Yul.World.SourceModifierBoundary

/-! Actual scalar-local modifier argument transport. Supplied intrinsic runtime
inputs, not a frontend/deployment or universal-call certificate. -/
namespace Solidity.Yul.World.SourceModifierArgument
open Solidity.Source
open Solidity.Roadmap (Bytes)
open Solidity.Yul.World.SourceModifierBoundary (uint errorDecl)

def parameter (name : String) : Syn .param := .param (.elem (.int false 256 (by decide))) none (some name)
def functionDecl : Decl := ⟨.function,"go",some "Guarded",false,
  .function (.ident "go") (.cons (parameter "p") .nil) (some .external) (some .payable)
    (.cons (.modInv ⟨"around",[]⟩ (.some (.positional (.cons (.ident "p") .nil)))) .nil) false none .nil
    (.some (.block .nil))⟩
def failureSyntax : Syn (.stmt .body) := .revert (.ident "ModDenied") (.positional (.cons (.ident "v") .nil))
def modifierItems (failed : Bool) : Syn (.list (.item .body)) :=
  .cons (.stmtItem (.simpleStmt (.exprStmt (.ident "_"))))
    (if failed then .cons (.stmtItem failureSyntax) .nil else .nil)
def modifierDecl (failed : Bool) : Decl := ⟨.modifier,"around",some "Guarded",false,
  .modifier "around" (.some (.cons (parameter "v") .nil)) false none (.some (.block (modifierItems failed)))⟩
def env (failed : Bool) : Env := ⟨[functionDecl,errorDecl,modifierDecl failed]⟩
def args (failed : Bool) : RConvArgs (env failed) [uint] [uint] :=
  .cons (.local .here) (by cases failed <;> decide) .nil
def modifierBody (failed : Bool) : RBody (env failed) :=
  ⟨[uint],[],true,[uint],[uint],.stmt (.placeholder rfl)
    (if failed then .stmt (.revertError errorDecl rfl (args failed)) .nil else .nil),[]⟩
def body (failed : Bool) : RBody (env failed) :=
  ⟨[uint],[],false,[uint],[uint],.nil,[⟨modifierDecl failed,[uint],args failed⟩]⟩
def glob {failed} (G : Glob (env failed)) : Glob (env failed) :=
  {G with prog:={G.prog with contracts:=["Guarded"],body:=fun d=>if d.name="go" then some (body failed) else if d.name="around" then some (modifierBody failed) else none}}
def locals (failed : Bool) (x : Int) (range : IntTy.u256.lo ≤ x ∧ x ≤ IntTy.u256.hi) : Locals (env failed).layout [uint] :=
  .cons (.int x range) .nil
def data {failed} (G : Glob (env failed)) (x : Int) : Bytes :=
  G.selector (sigOf (env failed).layout "ModDenied" [uint])++wordBytes (Source.intWord x)

/-- The scalar argument is read from the actual function-local vector. -/
theorem argument_run {failed} (G : Glob (env failed)) (F : Fr) (s : St (env failed))
    (x : Int) (range : IntTy.u256.lo ≤ x ∧ x ≤ IntTy.u256.hi) :
    (Source.evalConvArgs (glob G) F 6 (args failed)).run (locals failed x range,s)=
      (.ok (.cons (.int x range) .nil),(locals failed x range,s)) := by
  cases failed <;> rfl

/-- Actual modifier invocation and placeholder execution, including full caller
function-local restoration. The error bytes encode the selected scalar. -/
theorem actual {failed} (G : Glob (env failed)) (F : Fr) (s : EMState (env failed) [])
    (x : Int) (range : IntTy.u256.lo ≤ x ∧ x ≤ IntTy.u256.hi)
    (code : F.contract="Guarded") :
    (Source.runMods (glob G) F 7 (body failed) (body failed).mods (locals failed x range)).run s=
      ((if failed then .error (.revert (data G x)) else .ok (locals failed x range)),s) := by
  cases F with
  | mk owner sender amount static contract checked depth cd =>
    change contract="Guarded" at code
    subst contract
    cases failed with
    | false =>
      cases G with
      | mk program pipeline fixed balance hasCode strategy timestamp => cases pipeline <;> rfl
    | true =>
      cases G with
      | mk program pipeline fixed balance hasCode strategy timestamp =>
        cases pipeline <;>
          change ((.error (.revert ((wordBytes (fixed.hash (asciiBytes (sigOf (env true).layout "ModDenied" [uint])))).take 4 ++
            ((wordBytes (Source.intWord x) ++ []) ++ []))) : Except Halt (Locals (env true).layout [uint])),s)=_
        all_goals simp only [List.append_nil]; rfl

/-- Horizon exhaustion occurs inside the entered placeholder/body path, rather
than being recoded as an EVM revert; the saved caller state is restored. -/
theorem entered_timeout {failed} (G : Glob (env failed)) (F : Fr) (s : EMState (env failed) [])
    (x : Int) (range : IntTy.u256.lo ≤ x ∧ x ≤ IntTy.u256.hi)
    (code : F.contract="Guarded") :
    (Source.runMods (glob G) F 4 (body failed) (body failed).mods (locals failed x range)).run s=
      (.error .timeout,s) := by
  cases F with
  | mk owner sender amount static contract checked depth cd =>
    change contract="Guarded" at code
    subst contract
    cases failed <;> cases G with
    | mk program pipeline fixed balance hasCode strategy timestamp => cases pipeline <;> rfl

/-- Actual ordinary invocation of the registered scalar-parameter function.
This derives the result through the already checked modifier execution. -/
theorem invoked {failed} (G : Glob (env failed)) (F : Fr) (s : EMState (env failed) [])
    (x : Int) (range : IntTy.u256.lo ≤ x ∧ x ≤ IntTy.u256.hi)
    (code : F.contract="Guarded") :
    (Source.callInternal (glob G) F 8 functionDecl (.cons (.int x range) .nil) []).run s=
      ((if failed then .error (.revert (data G x)) else .ok (Source.mkRet [] .nil)),s) := by
  cases F with
  | mk owner sender amount static contract checked depth cd =>
    change contract="Guarded" at code
    subst contract
    cases failed with
    | false =>
      cases G with
      | mk program pipeline fixed balance hasCode strategy timestamp => cases pipeline <;> rfl
    | true =>
      cases G with
      | mk program pipeline fixed balance hasCode strategy timestamp =>
        cases pipeline <;>
          change ((.error (.revert ((wordBytes (fixed.hash (asciiBytes (sigOf (env true).layout "ModDenied" [uint])))).take 4 ++
            ((wordBytes (Source.intWord x) ++ []) ++ []))) : Except Halt (RVal (env true).layout (STy.ret []))),s)=_
        all_goals simp only [List.append_nil]; rfl

end Solidity.Yul.World.SourceModifierArgument
