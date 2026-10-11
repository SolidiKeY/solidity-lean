import Solidity.Syntax.Scoped

/-!
# A block with its calls inlined, printed

For display only: each call of a block written as KeY's
`expand_function_body` leaves it (`internalCallExpand`,
`functionBodyExpand`), the parameters declared with the arguments, the
return variables declared at their defaults, the body (its own calls
inlined in turn), the result assigned.  `y = f(a);`, `f` being
`function f(uint x) returns (uint r) { r = x + 1; }`, prints as
`uint x' = a; uint r'; r' = x' + 1; y = r';`.  A `{ … }` block's
statements are written in place, their calls inlined; a call inside a
branch or a loop stays a call, as `Prog.toStr` writes it.

The strings are `Syntax/Scoped.lean`'s printers' (`ns` the names beside the
context, innermost first); the body reads its frame's names, the return
variables on the parameters (`CallRet.names ++ Args.names`).
-/

namespace Solidity

section Inlined

variable {C : Contract} [FreshNames]

/-- `T x = e;` for each argument, the first first. -/
def Args.declStrs {Γ : Ctx} (ns : List Var) : {ps : Ctx} → Args C Γ ps → List String
  | _, .nil => []
  | _, .snoc as p x e => as.declStrs ns ++ [s!"{Ty.toStr (.prim p)} {x} = {e.toStr ns true};"]

/-- `T r;` for each return variable, at its default; a memory return as the
`T memory r;` its body begins with. -/
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

/-- A statement, a call inlined. -/
def Stmt.inlinedStrs {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → List String
  | .call _ args ret body =>
    args.declStrs ns ++ ret.declStrs ++ Prog.inlinedStrs (ret.names ++ args.names) body ++
      ret.resultStrs ns
  | .block body => Prog.inlinedStrs ns body
  | s => [s.toStr ns]

/-- The statements of a block, each call inlined. -/
def Prog.inlinedStrs {Γ Γ' : Ctx} (ns : List Var) : Prog C Γ Γ' → List String
  | .nil => []
  | .cons s P => s.inlinedStrs ns ++ Prog.inlinedStrs (s.outNames ns) P

end

/-- A block, its calls inlined, on one line. -/
def Prog.inlinedStr {Γ Γ' : Ctx} (ns : List Var) (P : Prog C Γ Γ') : String :=
  " ".intercalate (P.inlinedStrs ns)

/-- A block, its calls inlined, one statement per line. -/
def Prog.inlinedShow {Γ Γ' : Ctx} (ns : List Var) (P : Prog C Γ Γ') : String :=
  "\n".intercalate (P.inlinedStrs ns)

end Inlined

end Solidity
