import Solidity.Syntax.Scoped

/-!
# A block with its calls inlined, printed

For display: each call of a scoped block written as the body it runs, KeY's
`expand_function_body` (`internalCallExpand`): the parameters declared with
the arguments, the return variables declared, the body (its own calls
inlined in turn), the result assigned.  `y = f(a);`, `f` being
`function f(uint x) returns (uint r) { r = x + 1; }`, is
`uint x' = a; uint r'; r' = x' + 1; y = r';`.  A memory return's variable is
declared where the return variables are; a `{ … }` block's statements are
written in place; a call in a branch or a loop's body is written as the call.
-/

namespace Solidity

section Print

variable {C : Contract} [FreshNames]

/-- `T x = e;` for each argument, in the order they are bound. -/
def Args.declStrs {Γ : Ctx} (ns : List Var) : {ps : Ctx} → Args C Γ ps → List String
  | _, .nil => []
  | _, .snoc as p x e => as.declStrs ns ++ [s!"{Ty.toStr (.prim p)} {x} = {e.toStr ns true};"]

/-- `T r;` for each return variable, at its default. -/
def CallRet.declStrs {Γ : Ctx} : {rs Γ' : Ctx} → CallRet Γ rs Γ' → List String
  | _, _, .none => []
  | _, _, .val p r _ => [s!"{Ty.toStr (.prim p)} {r};"]
  | _, _, .rets bs => bs.toList.map fun (p, r) => s!"{Ty.toStr (.prim p)} {r};"
  | _, _, .mem R r _ _ => [s!"{Ty.toStr (.ref R)} memory {r};"]

/-- `res = r;`: the returned value assigned where the call is. -/
def CallRet.resultStrs {Γ : Ctx} (ns : List Var) : {rs Γ' : Ctx} → CallRet Γ rs Γ' → List String
  | _, _, .val _ r (some res) => [s!"{res.name ns} = {r};"]
  | _, _, _ => []

mutual

/-- A statement, a call written as its inlined body. -/
def Stmt.inlinedStrs {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → List String
  | .call _ args ret body =>
    args.declStrs ns ++ ret.declStrs ++ Prog.inlinedStrs (ret.names ++ args.names) body ++
      ret.resultStrs ns
  | .block body => Prog.inlinedStrs ns body
  | s => [s.toStr ns]

/-- The statements of a block, each call written as its inlined body. -/
def Prog.inlinedStrs {Γ Γ' : Ctx} (ns : List Var) : Prog C Γ Γ' → List String
  | .nil => []
  | .cons s P => s.inlinedStrs ns ++ Prog.inlinedStrs (s.outNames ns) P

end

/-- A block, each call written as its inlined body. -/
def Prog.inlinedStr {Γ Γ' : Ctx} (ns : List Var) (P : Prog C Γ Γ') : String :=
  " ".intercalate (Prog.inlinedStrs ns P)

end Print

end Solidity
