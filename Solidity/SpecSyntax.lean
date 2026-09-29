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
/// @custom:key assignable count             assignable count;
```

An `assignable` clause lists locations (`SpecLoc`), not values: a state
variable, a member, an entry `m[e]`, every entry `m[*]`, or `\nothing`.
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

/-- A location an `assignable` clause names: a state variable, a member,
an entry `m[e]` (`e` read in the pre-state), or every entry `m[*]`.  A
location covers everything stored below it. -/
inductive SpecLoc where
  | root (r : String)
  | field (l : SpecLoc) (f : String)
  | index (l : SpecLoc) (e : SpecExpr)
  | all (l : SpecLoc)
  deriving Repr, Inhabited

/-- A function's clauses: solkey's `requires`, `ensures`, `assignable`
(`none` without the clause, which frames nothing; `some []` for
`\nothing`), and `skip` (no obligation). -/
structure FunSpec where
  requires : List SpecExpr := []
  ensures : List SpecExpr := []
  assignable : Option (List SpecLoc) := none
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

/-- A quantifier's sort: `uint`, `int`, `bool`, or `address` (a `uint`),
by `PrimTy.ofName?`. -/
def specSort (T : Ident) : MacroM Term :=
  let s := T.getId.toString
  match PrimTy.ofName? s with
  | some .uint => `(PrimTy.uint)
  | some .int => `(PrimTy.int)
  | some .bool => `(PrimTy.bool)
  | none => Macro.throwErrorAt T s!"a quantifier ranges over uint, int, bool or address, not {s}"

/-- `e.f.g`: `init` with the members `fs` read off it by the constructor `field`
(`SpecExpr.field`, `SpecLoc.field`, `RawExpr.field`). -/
def foldFields (field : Ident) (init : Term) (fs : List String) : MacroM Term :=
  fs.foldlM (fun e f => `($field $e $(quote f))) init

/-- The constructor `a` of the enumeration `ns`, to splice: `BinOp.add`. -/
def ctorIdent [Repr α] (ns : Lean.Name) (a : α) : Ident :=
  mkIdent (.str ns ((toString (repr a)).splitOn ".").getLast!)

partial def expandSpec (e : TSyntax `spec_expr) : MacroM Term := do
  -- the binary operators, by their table (`BinOp.ofSym?`): a node `[a, ⊕, b]`
  if e.raw.getNumArgs == 3 && e.raw[1].isAtom then
    if let some op := BinOp.ofSym? e.raw[1].getAtomVal then
      return ← `(SpecExpr.binop $(ctorIdent ``BinOp op) $(← expandSpec ⟨e.raw[0]⟩)
        $(← expandSpec ⟨e.raw[2]⟩))
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
      | n :: fs => do foldFields (mkIdent ``SpecExpr.field) (← `(SpecExpr.name $(quote n))) fs
  | `(spec_expr| \result) => `(SpecExpr.result)
  | `(spec_expr| \old ( $a )) => do `(SpecExpr.old $(← expandSpec a))
  | `(spec_expr| net ( $a )) => do `(SpecExpr.net $(← expandSpec a))
  | `(spec_expr| address ( $a )) => expandSpec a
  | `(spec_expr| $a [ $k ]) => do `(SpecExpr.index $(← expandSpec a) $(← expandSpec k))
  | `(spec_expr| $a:spec_expr.$f:ident) => do `(SpecExpr.field $(← expandSpec a) $(quote f.getId.toString))
  | `(spec_expr| ! $a) => do `(SpecExpr.unop .not $(← expandSpec a))
  | `(spec_expr| - $a) => do `(SpecExpr.unop .neg $(← expandSpec a))
  | `(spec_expr| $a -> $b) => do `(SpecExpr.imp $(← expandSpec a) $(← expandSpec b))
  | `(spec_expr| $a <-> $b) => do `(SpecExpr.iff $(← expandSpec a) $(← expandSpec b))
  | `(spec_expr| \forall $T:ident $x:ident; $a) => do
    `(SpecExpr.all $(← specSort T) $(quote x.getId.toString) $(← expandSpec a))
  | `(spec_expr| \exists $T:ident $x:ident; $a) => do
    `(SpecExpr.ex $(← specSort T) $(quote x.getId.toString) $(← expandSpec a))
  | _ => Macro.throwUnsupported

/-- A location of an `assignable` clause: `count`, `alice.age`,
`balances[msg.sender]`, `balances[*]`. -/
declare_syntax_cat spec_loc (behavior := both)
syntax:max ident : spec_loc
syntax:max spec_loc noWs "." noWs ident : spec_loc
syntax:max spec_loc "[" spec_expr "]" : spec_loc
syntax:max spec_loc "[" "*" "]" : spec_loc

/-- What an `assignable` clause lists: locations, or `\nothing`. -/
declare_syntax_cat spec_locs (behavior := both)
syntax "\\" noWs &"nothing" : spec_locs
syntax spec_loc,+ : spec_locs

partial def expandSpecLoc (l : TSyntax `spec_loc) : MacroM Term := do
  match l with
  | `(spec_loc| $x:ident) =>
    -- `alice.age` is read as one dotted identifier
    match x.getId.components.map (·.toString) with
    | [] => Macro.throwUnsupported
    | n :: fs => do foldFields (mkIdent ``SpecLoc.field) (← `(SpecLoc.root $(quote n))) fs
  | `(spec_loc| $a:spec_loc.$f:ident) => do `(SpecLoc.field $(← expandSpecLoc a) $(quote f.getId.toString))
  | `(spec_loc| $a:spec_loc [ * ]) => do `(SpecLoc.all $(← expandSpecLoc a))
  | `(spec_loc| $a:spec_loc [ $e:spec_expr ]) => do `(SpecLoc.index $(← expandSpecLoc a) $(← expandSpec e))
  | _ => Macro.throwUnsupported

/-- The locations of an `assignable` clause, `[]` for `\nothing`. -/
def expandSpecLocs (ls : TSyntax `spec_locs) : MacroM Term := do
  match ls with
  | `(spec_locs| \nothing) => `(([] : List SpecLoc))
  | `(spec_locs| $ls:spec_loc,*) => do `([$(← ls.getElems.mapM expandSpecLoc),*])
  | _ => Macro.throwUnsupported

end

/-- `spec!(count == \old(count) + 1)`: a clause as read. -/
syntax "spec!(" spec_expr ")" : term

macro_rules
  | `(spec!($e)) => expandSpec e

end Solidity
