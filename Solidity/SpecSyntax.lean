import Solidity.AST

/-!
# The specification language, as read

solkey's `SolSpec.g4`: Solidity expressions, plus `\old(e)`, `\result`,
`net(e)`, `->`, `<->` and `\forall T x; e`/`\exists T x; e`.  A clause is
kept as read (`SpecExpr`), as a function's body is: a `Contract` cannot hold
an `Fml C`, whose index it is.  `Calculus/Spec.lean` compiles a clause to a
formula against a storage term, as solkey's `SpecCompiler` does.

The clauses stand where solkey's NatSpec lines stand, above what they
specify, as members of `contract!{ … }` (`Syntax.lean`):

```
/// @custom:key requires count >= 1          requires count >= 1;
/// @custom:key ensures count == \old(count) - 1   ensures count == \old(count) - 1;
/// @custom:key invariant total >= 0         invariant total >= 0;
/// @custom:key skip                         skip;
```
-/

namespace Solidity

/-- A clause of the specification language, as read. -/
inductive SpecExpr where
  | num (n : Nat)
  | bool (b : Bool)
  | name (x : String)
  /-- `\result`: the function's return variable. -/
  | result
  /-- `\old(e)`: `e` read in the state the function started in. -/
  | old (e : SpecExpr)
  /-- `net(a)`: what the ledger holds for `a`. -/
  | net (e : SpecExpr)
  | field (e : SpecExpr) (f : String)
  | index (e k : SpecExpr)
  | unop (op : UnOp) (e : SpecExpr)
  /-- `* / % + - < <= > >= == != && ||` -/
  | binop (op : BinOp) (a b : SpecExpr)
  | imp (a b : SpecExpr)
  | iff (a b : SpecExpr)
  /-- `\forall T x; e`, at `T`'s primitive type (an `address` is a `uint`). -/
  | all (p : PrimTy) (x : String) (e : SpecExpr)
  | ex (p : PrimTy) (x : String) (e : SpecExpr)
  deriving Repr, Inhabited

/-- A function's clauses: solkey's `requires`, `ensures`, and `skip` (no
obligation). -/
structure FunSpec where
  requires : List SpecExpr := []
  ensures : List SpecExpr := []
  skip : Bool := false
  deriving Repr, Inhabited

declare_syntax_cat spec_expr (behavior := both)

syntax:max "(" spec_expr ")" : spec_expr
syntax:max num : spec_expr
syntax:max ident : spec_expr
syntax:max "\\" noWs &"result" : spec_expr
syntax:max "\\" noWs &"old" "(" spec_expr ")" : spec_expr
syntax:max &"net" "(" spec_expr ")" : spec_expr
/-- `address(e)`: `e`. -/
syntax:max &"address" "(" spec_expr ")" : spec_expr
syntax:max spec_expr:max "[" spec_expr "]" : spec_expr
syntax:max spec_expr:max noWs "." noWs ident : spec_expr
syntax:75 "!" spec_expr:75 : spec_expr
syntax:75 "-" spec_expr:75 : spec_expr
syntax:70 spec_expr:70 " * " spec_expr:71 : spec_expr
syntax:70 spec_expr:70 " / " spec_expr:71 : spec_expr
syntax:70 spec_expr:70 " % " spec_expr:71 : spec_expr
syntax:65 spec_expr:65 " + " spec_expr:66 : spec_expr
syntax:65 spec_expr:65 " - " spec_expr:66 : spec_expr
syntax:50 spec_expr:51 " < " spec_expr:51 : spec_expr
syntax:50 spec_expr:51 " <= " spec_expr:51 : spec_expr
syntax:50 spec_expr:51 " > " spec_expr:51 : spec_expr
syntax:50 spec_expr:51 " >= " spec_expr:51 : spec_expr
syntax:45 spec_expr:46 " == " spec_expr:46 : spec_expr
syntax:45 spec_expr:46 " != " spec_expr:46 : spec_expr
syntax:35 spec_expr:35 " && " spec_expr:36 : spec_expr
syntax:30 spec_expr:30 " || " spec_expr:31 : spec_expr
syntax:25 spec_expr:26 " -> " spec_expr:25 : spec_expr
syntax:20 spec_expr:20 " <-> " spec_expr:21 : spec_expr
syntax:10 "\\" noWs &"forall"  ident ident "; " spec_expr:10 : spec_expr
syntax:10 "\\" noWs &"exists"  ident ident "; " spec_expr:10 : spec_expr

section
open Lean

/-- A quantifier's sort: `uint`, `int`, `bool`, or `address` (a `uint`). -/
def specSort (T : Ident) : MacroM Term :=
  match T.getId.toString with
  | "uint" | "uint256" | "address" => `(PrimTy.uint)
  | "int" | "int256" => `(PrimTy.int)
  | "bool" => `(PrimTy.bool)
  | s => Macro.throwErrorAt T s!"a quantifier ranges over uint, int, bool or address, not {s}"

partial def expandSpec (e : TSyntax `spec_expr) : MacroM Term := do
  match e with
  | `(spec_expr| ( $a )) => expandSpec a
  | `(spec_expr| $n:num) => `(SpecExpr.num $n)
  | `(spec_expr| $x:ident) =>
    match x.getId.toString with
    | "true" => `(SpecExpr.bool true)
    | "false" => `(SpecExpr.bool false)
    | _ =>
      -- `msg.sender`, `State.Created` are read as one dotted identifier
      match x.getId.components.map (·.toString) with
      | [] => Macro.throwUnsupported
      | n :: fs => fs.foldlM (fun e f => `(SpecExpr.field $e $(quote f))) (← `(SpecExpr.name $(quote n)))
  | `(spec_expr| \result) => `(SpecExpr.result)
  | `(spec_expr| \old ( $a )) => do `(SpecExpr.old $(← expandSpec a))
  | `(spec_expr| net ( $a )) => do `(SpecExpr.net $(← expandSpec a))
  | `(spec_expr| address ( $a )) => expandSpec a
  | `(spec_expr| $a [ $k ]) => do `(SpecExpr.index $(← expandSpec a) $(← expandSpec k))
  | `(spec_expr| $a:spec_expr.$f:ident) => do `(SpecExpr.field $(← expandSpec a) $(quote f.getId.toString))
  | `(spec_expr| ! $a) => do `(SpecExpr.unop .not $(← expandSpec a))
  | `(spec_expr| - $a) => do `(SpecExpr.unop .neg $(← expandSpec a))
  | `(spec_expr| $a * $b) => bin ``BinOp.mul a b
  | `(spec_expr| $a / $b) => bin ``BinOp.div a b
  | `(spec_expr| $a % $b) => bin ``BinOp.mod a b
  | `(spec_expr| $a + $b) => bin ``BinOp.add a b
  | `(spec_expr| $a - $b) => bin ``BinOp.sub a b
  | `(spec_expr| $a < $b) => bin ``BinOp.lt a b
  | `(spec_expr| $a <= $b) => bin ``BinOp.le a b
  | `(spec_expr| $a > $b) => bin ``BinOp.gt a b
  | `(spec_expr| $a >= $b) => bin ``BinOp.ge a b
  | `(spec_expr| $a == $b) => bin ``BinOp.eqB a b
  | `(spec_expr| $a != $b) => bin ``BinOp.neB a b
  | `(spec_expr| $a && $b) => bin ``BinOp.and a b
  | `(spec_expr| $a || $b) => bin ``BinOp.or a b
  | `(spec_expr| $a -> $b) => do `(SpecExpr.imp $(← expandSpec a) $(← expandSpec b))
  | `(spec_expr| $a <-> $b) => do `(SpecExpr.iff $(← expandSpec a) $(← expandSpec b))
  | `(spec_expr| \forall $T:ident $x:ident; $a) => do
    `(SpecExpr.all $(← specSort T) $(quote x.getId.toString) $(← expandSpec a))
  | `(spec_expr| \exists $T:ident $x:ident; $a) => do
    `(SpecExpr.ex $(← specSort T) $(quote x.getId.toString) $(← expandSpec a))
  | _ => Macro.throwUnsupported
where
  bin (op : Lean.Name) (a b : TSyntax `spec_expr) : MacroM Term := do
    `(SpecExpr.binop $(mkIdent op) $(← expandSpec a) $(← expandSpec b))

end

/-- `spec!(count == \old(count) + 1)`: a clause as read. -/
syntax "spec!(" spec_expr ")" : term

macro_rules
  | `(spec!($e)) => expandSpec e

end Solidity
