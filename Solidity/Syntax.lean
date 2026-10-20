import Solidity.AST
import Solidity.SpecSyntax

/-!
# The grammar and the contract

What a program is written in, before it is typed: Solidity's grammar
(`sol_stmt`, `sol_expr`, `sol_ty`), the raw syntax it is read into
(`RawStmt`, `RawExpr`), the contract a program is written against
(`contract!{ … }`, `Contract`) and the types the typed syntax is indexed by
(`ArrTy`, `IndexTy`).  The typed syntax itself is `Syntax/Scoped.lean`'s:
every value indexed by its type and every local by its position in the
context it is read in, so a statement no rule can run cannot be written
(`alice.balance = 1;`, no such member; `alice = 1;`, a `uint` for a
`Person`; `wallet = wallet;`, a copy of a mapping).

`sol[C]{ … }` reads Solidity statements, elaborates them against the
contract `C` (`Syntax/Elab.lean`), each local typed at its position, and
splices the result into the file as a term (`Syntax/Splice.lean`);
`sol{ … }` is the same against the file's `InContract` instance.  The
elaborator is an ordinary function run at compile time; its result is
turned back into a term with every proof `Eq.refl`, so the kernel re-checks
each one: nothing the elaborator computed is trusted.

Two spellings differ from Solidity's.  A decrement is `x−−`, `−−x` (two
U+2212 MINUS SIGN): `--` opens a comment in Lean, so it cannot appear in a
`sol{ … }` block, and `x -= 1` is another statement.  And a value has no
effects: an `++`/`−−` inside an expression, or a conditional whose branches
are references, is captured by the elaborator into a fresh local before its
statement (`hoist`), in the order solc evaluates the operands.  A statement
ending in a block (`if (c) { … }`, `unchecked { … }`) may leave out its `;`
(`solSemi`), and `else if` nests an `if` in the `else` branch.

`while`, `for`, `do … while`, `break` and `continue` are lowered to one
loop, `Stmt.loop`, solkey's lowered `while`, by solkey's `LoopLowering`
(`lowerLoops`): a jump sets a flag, and a `return` inside a loop too.  The
`/// @custom:key` lines above a loop are its annotation (`LoopAnn`), which
chooses the rule that proves it.

A contract declares its internal functions (`contract!{ function f(uint x)
returns (uint r) { … } }`), each calling only the ones declared before it.
A call (`f(a);`, `y = f(a);`, `uint y = f(a);`) is elaborated by inlining:
`Stmt.call` carries the callee's parameters bound to the arguments, its
return variables and the body, every local of the callee renamed fresh for
this call (`elabCall`), as KeY's `FunctionBodyStatement` carries the function
it stands for.  A call is a statement or a whole right-hand side, as KeY
writes it (`res = f(a)@C;`); one inside an expression is captured before its
statement.  A push used as a target, `values.push() = e;`, is the push
`values.push(e);`, as the front end normalises it.  A body's
`return e;` ends it: an assignment to the return variable, the statements
after it moved into the branches that do not return (`lowerReturns`).

A function may return a memory reference (`returns (Person memory p)`), and
its call is then KeY's expansion written out: the callee's fresh return
variable is declared by the call's frame (`CallRet.mem`, a fresh default
object, as solc allocates one on entry), and the statement after the call
binds the caller's local to its identity (`Person memory mv1 =
mv2;`, `m = mv2;`, KeY's `resultVar = freshReturn`).  The printers write the
two statements as the call they are (`Person memory mv1 =
choosePersonMem();`), which reads back to them.  A member of a call's value
is a member of that capture (`choosePersonMem().account = a;`).

A single storage return (`returns (uint[] storage r)`) instead enters with
an unset alias and exports that alias without allocation (`CallRet.storage`).
Storage-local declarations and rebinding consume it; a direct call receiver
is retained as an unsupported case until its native capture taclet is added.
-/

namespace Solidity

open Semantics

/-! ## The surface syntax, as read

What `sol{ … }` reads before it is typed (`RawStmt`), declared first because
a contract keeps its functions' bodies in it (`FunDecl`). -/

inductive RawTy where
  | named (s : String)
  | mapping (k v : RawTy)
  | array (t : RawTy)
  | fixed (t : RawTy) (n : Nat)
  deriving Repr, Inhabited

/-- The environment a transaction runs in, read as values: `msg.sender`,
`msg.value`, `block.timestamp`, `address(this).balance`, and the contract's
own address `address(this)` (`this` where an address stands).  `this` is
the ledger's own account: a payment books `net` at both ends.  solkey's
`netHeader.key` declares the first two and the last as the program variables
`msgSender`, `msgValue`, `selfBalance`; `block.timestamp` it has not (its
benchmark reads a `timeNow` state variable instead), so its name here is the
one solc's Yul gives it. -/
inductive EnvKey where
  | msgSender
  | msgValue
  | timestamp
  | selfBalance
  | selfAddress
  deriving Repr, DecidableEq, Inhabited

/-- The Solidity spelling. -/
def EnvKey.toStr : EnvKey → String
  | .msgSender => "msg.sender"
  | .msgValue => "msg.value"
  | .timestamp => "block.timestamp"
  | .selfBalance => "address(this).balance"
  | .selfAddress => "address(this)"

/-- `msg.sender`, `msg.value`, `block.timestamp` by their two parts. -/
def EnvKey.ofParts : String → String → Option EnvKey
  | "msg", "sender" => some .msgSender
  | "msg", "value" => some .msgValue
  | "block", "timestamp" => some .timestamp
  | _, _ => none

inductive RawExpr where
  | num (n : Nat)
  | name (x : String)
  | bool (b : Bool)
  | field (e : RawExpr) (f : String)
  | index (e k : RawExpr)
  | binop (op : BinOp) (a b : RawExpr)
  | unop (op : UnOp) (a : RawExpr)
  | ternary (c a b : RawExpr)
  /-- `x++`, `−−x` inside an expression: captured before the statement. -/
  | incDec (op : IncDec) (e : RawExpr)
  /-- `new uint[](n)`: only a right-hand side. -/
  | newArr (T : RawTy) (n : RawExpr)
  /-- `f(a, b)`, a call of the contract's function `f`: the whole right-hand
  side of an assignment or a declaration, or of a `return`; captured before
  the statement anywhere else (`hoist`). -/
  | call (f : String) (args : List RawExpr)
  | modular (op : ModOp) (a b k : RawExpr)
  /-- `T({f: a, g: b})`, a struct constructor with named arguments: put in
  the members' order by `hoist`, then read as the positional `T(a, b)`; a
  function's call `f({q: b, p: a})`, put in its parameters' order
  (`RawExpr.orderNamed`). -/
  | named (f : String) (names : List String) (args : List RawExpr)
  /-- `msg.sender`, `address(this).balance`, …: a value of the environment. -/
  | env (k : EnvKey)
  /-- `(a, b)`, two components or more: only the right-hand side of a tuple
  assignment (`RawStmt.tupleAssign`) or a `return` of several values. -/
  | tuple (es : List RawExpr)
  /-- `(l = r)` inside an expression: the value assigned, the write made
  before the statement (`hoist`; solkey's `localCopyAssignmentValue`,
  `storageCopyAssignmentValue`). -/
  | assign (l r : RawExpr)
  /-- `(l ⊕= r)` inside an expression: `l`'s new value, the write made before
  the statement (`hoist`; solkey's `local…AssignmentValue`). -/
  | opAssign (op : BinOp) (l r : RawExpr)
  deriving Repr, Inhabited

/-- A quantified clause of a loop's invariant as read, solkey's
specification language above a loop (`LoopSpecCompiler`): `\forall T x; b`,
`b` an expression or `a -> c`. -/
inductive RawInv where
  | expr (e : RawExpr)
  | imp (a c : RawExpr)
  | all (p : PrimTy) (x : String) (body : RawInv)
  deriving Repr, Inhabited

/-- The expressions of a clause, as written. -/
def RawInv.exprs : RawInv → List RawExpr
  | .expr e => [e]
  | .imp a c => [a, c]
  | .all _ _ b => b.exprs

/-- A loop's specification as read, solkey's `///` lines above the loop:
`/// @custom:key invariant e` (several conjoined), `/// @custom:key
decreases e` (at most one) and, Lean only, `/// @custom:key unwind k`, the
bound on unwinding (`LoopAnn`). -/
structure RawLoopSpec where
  inv : List RawExpr := []
  dec : Option RawExpr := none
  unwind : Option Nat := none
  /-- The loop was lowered with a `break` flag, the first conjunct of its
  condition (`while (!brk && …)`, `lowerLoops`): solkey's `\getLoopBreak`. -/
  brk : Bool := false
  /-- The quantified `invariant` clauses (`\forall T x; …`). -/
  qinv : List RawInv := []
  deriving Repr, Inhabited

/-- The expressions of a loop's specification, as written. -/
def RawLoopSpec.exprs (a : RawLoopSpec) : List RawExpr :=
  a.inv ++ a.qinv.flatMap RawInv.exprs ++ a.dec.toList

/-- How a block reads an operation out of range: `checked { … }` fails the
proof (KeY Java's `checkingOF`), `ignoringOverflow { … }` assumes the run
away (`ignoringOF`, read soundly: an overflowing run proves anything, as
exhaustion does, rather than going on with unbounded values; `Prog.withOF`,
`docs/options.md` O2, O5). -/
inductive OFMode where
  | checking
  | ignoring
  deriving DecidableEq, Repr, Inhabited

inductive RawStmt where
  | assign (l r : RawExpr)
  | decl (T : RawTy) (x : String) (init : Option RawExpr)
  | declStorage (T : RawTy) (x : String) (init : Option RawExpr)
  | declMemory (T : RawTy) (x : String) (init : Option RawExpr)
  | delete (e : RawExpr)
  | opAssign (op : BinOp) (l r : RawExpr)
  | incDec (op : IncDec) (l : RawExpr)
  /-- `b.push() += r`: a primitive push result used as a compound target. -/
  | pushOpAssign (op : BinOp) (b r : RawExpr)
  /-- `++b.push()` / `b.push()++`: the result is discarded. -/
  | pushIncDec (op : IncDec) (b : RawExpr)
  /-- `b.push()`, `b.push(a)`, `b.pop()`, `a.transfer(v)`. -/
  | call (f : RawExpr) (args : List RawExpr)
  | assignIncDec (x : RawExpr) (op : IncDec) (l : RawExpr)
  /-- `lsv = b.push();`, `y = b.push();`, `T storage lsv = b.push();` -/
  | assignPush (l b : RawExpr)
  | declStoragePush (T : RawTy) (x : String) (b : RawExpr)
  /-- `uint y = values.push();` -/
  | declPush (T : RawTy) (x : String) (b : RawExpr)
  | ite (c : RawExpr) (thn els : List RawStmt)
  | require (c : RawExpr)
  | assert (c : RawExpr)
  | revert
  /-- `assume(false);`: a run assumed away (`Stmt.assumeFalse`). -/
  | assumeFalse
  /-- `return e;`, `return;`: in a function's body, lowered away when it is
  inlined (`lowerReturns`). -/
  | ret (e : Option RawExpr)
  /-- The arguments of `emit E(a, b);`, or of the error in
  `require(c, Err(a, b));`, evaluated left to right for their effects and
  their reverts and then dropped: the log and the error data are not
  modelled.  One that can neither revert nor have an effect (a literal, a
  name, a member of one) is not evaluated at all. -/
  | eval (args : List RawExpr)
  /-- `unchecked { … }`: a scope whose `+ - * **` wrap (`uncheckStmts`). -/
  | unchecked (body : List RawStmt)
  /-- `checked { … }`: a scope where a checked operation that leaves its
  range is an assertion failure (`Prog.checkOF`, `docs/options.md`);
  `ignoringOverflow { … }` (`o = .ignoring`), one where it is assumed away. -/
  | checked (o : OFMode) (body : List RawStmt)
  /-- `try e.f(a) returns (T v) { … } catch …`: the receiver, the function,
  the arguments, the return locals, and the clauses normalised as
  `Stmt.tryCall`'s, with the name of the `Panic` code. -/
  | tryCall (recv : RawExpr) (f : String) (args : List RawExpr) (rets : List (RawTy × String))
      (ok err : List RawStmt) (code : Option String) (panic other : List RawStmt)
  /-- `x = r.send(a);`, and with `T` given the declaration `T x = r.send(a);`
  (`x` a name).  A bare `r.send(a);` is not read: solkey has no rule for it.
  With `full`, the value call `(x, ) = r.call{value: a}("");` and
  `(T x, ) = r.call{value: a}("");`, which forwards all the gas. -/
  | send (T : Option RawTy) (x r a : RawExpr) (full : Bool)
  /-- `(uint a, , bool b) = e;`: a variable declared per component, a
  component left out discarded (`elabTuple`). -/
  | tupleDecl (vars : List (Option (RawTy × String))) (rhs : RawExpr)
  /-- `(a, , b) = e;`: a component assigned to each target, one left out
  discarded (`elabTuple`). -/
  | tupleAssign (targets : List (Option RawExpr)) (rhs : RawExpr)
  /-- `{ … }`: a block, whose declarations are scoped to it. -/
  | block (body : List RawStmt)
  /-- `while (c) { … }`, with its specification. -/
  | whileLoop (spec : RawLoopSpec) (c : RawExpr) (body : List RawStmt)
  /-- `for (init; c; upd) { … }`: `init` and `upd` are a statement or none,
  `c` none when left out (`true`). -/
  | forLoop (spec : RawLoopSpec) (init : List RawStmt) (c : Option RawExpr) (upd : List RawStmt)
      (body : List RawStmt)
  /-- `do { … } while (c);` -/
  | doWhile (spec : RawLoopSpec) (body : List RawStmt) (c : RawExpr)
  /-- `break;` -/
  | brk
  /-- `continue;` -/
  | cont
  /-- A loop as `lowerLoops` leaves it, solkey's lowered `while`: no
  `break`, `continue` or `return` in its body. -/
  | loop (spec : RawLoopSpec) (c : RawExpr) (body : List RawStmt)
  /-- `_;`: where a modifier's body runs the function's (`wrapMods`). -/
  | hole
  deriving Repr, Inhabited

/-- Evaluating `e` can neither revert nor have an effect: a literal, a name,
or a member of one (`msg.sender`, `State.Created`). -/
def RawExpr.isPure : RawExpr → Bool
  | .num _ | .bool _ | .name _ => true
  | .field e _ => e.isPure
  | .env _ => true
  | _ => false

/-- `require(c, Err(a, b));` and `require(c, "msg");`: solc evaluates the
condition, then the error's arguments, then reverts if the condition is
false.  With arguments that cannot revert nor have an effect that is
`require(c);`; with others, `if (c) { eval(a, b) } else { revert(); }`, the
same run: a false condition reverts whatever the arguments do, and a true one
evaluates them after the condition, as solc does. -/
def RawStmt.requireWith (c : RawExpr) (args : List RawExpr) : RawStmt :=
  if args.all RawExpr.isPure then .require c else .ite c [.eval args] [.revert]

/-- A modifier as a function applies it (`function f() onlyOwner
inState(State.Created) { … }`): its parameters, the arguments of this
application (read in the function's scope), and its body, where each `_;`
(`RawStmt.hole`, one at least, anywhere) runs the function's.  The
elaborator inlines it around the function's body (`wrapMods`). -/
structure ModApp where
  name : String
  params : List (Name × Ty)
  args : List RawExpr
  body : List RawStmt
  deriving Repr, Inhabited

/-- A reference parameter's declared data location. -/
inductive ParamLoc where
  | memory | storage | calldata
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- An internal function as the contract declares it: its parameters and
its return variables (`returns (uint r)`; unnamed, `returns (uint)`, it is
called `_ret`, and the `i`-th of several `_ret{i}`, solkey's `ret{i}`;
`returns (Account memory a)` or `returns (Account storage a)`, a reference
at its location), at their types, and its
body as read.  The elaborator types the body where the function is called
and inlines it there (`Stmt.call`). -/
structure FunDecl where
  params : List (Name × Ty)
  /-- Reference parameters retain their locations separately from their types. -/
  paramLocs : List (Name × ParamLoc) := []
  rets : List (Name × Ty) := []
  /-- The single reference return is declared `memory`. -/
  retMem : Bool := false
  /-- The single reference return is declared `storage`, exporting an alias. -/
  retStorage : Bool := false
  body : List RawStmt
  /-- The modifiers it applies, the first listed outermost. -/
  mods : List ModApp := []
  /-- Its `requires`/`ensures` clauses, as read (`Calculus/SurfaceSpec.lean`). -/
  spec : FunSpec := {}
  /-- Declared `payable`: its obligation assumes `msg.value >= 0` where
  another's assumes `msg.value == 0`, as solkey's does. -/
  payable : Bool := false
  /-- Its parameters and return variable of a narrow integer type (`uint8 x`),
  with their width: each is a `uint` or an `int` in `params`/`ret`. -/
  widths : List (Name × Nat) := []
  deriving Repr, Inhabited

/-- The return variable of a function of one return. -/
def FunDecl.ret (d : FunDecl) : Option (Name × Ty) :=
  match d.rets with
  | [r] => some r
  | _ => none

/-! ## The contract

Struct bodies are `Semantics.structDef`, the table the interpreter expands
structs through, so a contract cannot disagree with what runs: a contract
is its storage roots, in declaration order, and `fieldType` reads the
table.

A contract also declares its internal functions, in order.  A function may
call only the functions declared before it: the position is the rank that
makes the call graph acyclic (as `structRank` does the struct table's), so
inlining a call, which is what the elaborator does and KeY's
`internalCallExpand` and `functionBodyExpand` do, ends. -/

structure Contract where
  vars : List (Name × Ty)
  funs : List (Name × FunDecl) := []
  /-- Its enums, each with its members in order: `State.Locked` is the
  `uint` literal `1` (an enum is read as `uint`, as `address` is). -/
  enums : List (Name × List Name) := []
  /-- Its `invariant` clauses, as read: solkey's `CInv`. -/
  inv : List SpecExpr := []
  /-- Its state variables of a narrow integer type (`uint8 small;`), with their
  width: each is a `uint` or an `int` in `vars`. -/
  widths : List (Name × Nat) := []
  /-- `constructor(…) { … }`: what a deployment runs, called as
  `constructor(args);` (`elabCtor`).  `none` for a contract that declares
  none: solc's implicit one, which runs the initializers only. -/
  ctor : Option FunDecl := none
  /-- `uint x = 5;`: the state variables declared with an initializer, in
  declaration order, each with it as read.  The constructor runs them first
  (`elabCtor`), as solkey's `ExpandFunctionBody` prepends them. -/
  inits : List (Name × RawExpr) := []
  deriving Repr, Inhabited

namespace Contract

/-- The declared type of the storage root `r`. -/
def rootType (C : Contract) (r : Name) : Option Ty := lookupBy r C.vars

/-- The declared type of member `f` of struct `s`, from `structDef`.  The
parameter is there so terms read `C.fieldType`. -/
def fieldType (_C : Contract) (s f : Name) : Option Ty := lookupBy f (structDef s)

end Contract

/-- The contract `sol{ … }` and `dl{ … }` are about: a file of examples says
`local instance : InContract := ⟨StandardExample⟩`. -/
class InContract where
  contract : Contract

/-! ## Narrow integer types

`uint8` … `uint248` and `int8` … `int248` are not types of the syntax: a local,
a parameter, a return variable or a state variable declared at one is a `uint`
or an `int`, and the elaborator carries its width (`LocalTy.val`,
`Contract.widths`, `FunDecl.widths`).  What leaves the width is checked where it
happens, as solc checks it: an operation at a narrow type is followed by
`require(inTy)` on where its result lands (`narrowPost`, `narrowCapture`); an
implicit narrowing is refused (`fitCheck`); under `unchecked` the wrapping
operators are taken modulo `2^N` (`narrowWrapNode`); a cast is a capture at its
type (`castCapture`).  The range predicate `inTy(uintN, e)` is the
condition `inTyCond` writes. -/

/-- `uintN`/`intN` for `N` in `8, 16, …, 248`: the primitive type and the width.
`uint256` and `int256` are `PrimTy.ofName?`'s. -/
def narrowTy? (s : String) : Option (PrimTy × Nat) :=
  let (p, ds) :=
    if s.startsWith "uint" then (PrimTy.uint, s.drop 4)
    else if s.startsWith "int" then (PrimTy.int, s.drop 3)
    else (PrimTy.bool, "")
  match ds.toNat? with
  | some n =>
    if p != .bool && 8 ≤ n && n < 256 && n % 8 == 0 && toString n == ds then some (p, n)
    else none
  | none => none

/-- The type a cast `T(e)` converts to: a narrow type, or `uint`/`int` at `256`. -/
def castTy? (f : String) : Option (PrimTy × Nat) :=
  match narrowTy? f with
  | some t => some t
  | none =>
    match f with
    | "uint" | "uint256" => some (.uint, 256)
    | "int" | "int256" => some (.int, 256)
    | _ => none

/-- The Solidity spelling of `p` at `n` bits. -/
def tyName (p : PrimTy) (n : Nat) : String := if n < 256 then s!"{p.toStr}{n}" else p.toStr

/-- Why a narrow type is refused where it stands. -/
def narrowNestedMsg (s : String) : String :=
  s!"{s}: a narrow integer type is the type of a local, a parameter, a return value or a " ++
  "state variable only, not of an array's element, a mapping's key or value, or a struct's member"

declare_syntax_cat sol_ty (behavior := both)
syntax:max ident : sol_ty
syntax:max &"mapping" "(" sol_ty " => " sol_ty ")" : sol_ty
syntax:max sol_ty:max "[" "]" : sol_ty
/-- `uint[3]`: a fixed-size array; `uint[2][3]` is three `uint[2]`. -/
syntax:max sol_ty:max "[" num "]" : sol_ty
/-- `address payable`: an `address`, read as `uint`. -/
syntax:max &"address" &"payable" : sol_ty

/-- `ty!(mapping(uint => Person))`: a type written as Solidity does. -/
syntax "ty!(" sol_ty ")" : term

/-- `pty!(uint)`: a value type, as a mapping's key is. -/
syntax "pty!(" sol_ty ")" : term

macro_rules
  | `(pty!($x:ident)) =>
      match PrimTy.ofName? x.getId.toString with
      | some .uint => `(PrimTy.uint)
      | some .int => `(PrimTy.int)
      | some .bool => `(PrimTy.bool)
      | none => Lean.Macro.throwErrorAt x "a mapping's key is a value type"
  | `(pty!(address payable)) => `(PrimTy.uint)
  | `(pty!($t)) => Lean.Macro.throwErrorAt t "a mapping's key is a value type"

macro_rules
  | `(ty!($x:ident)) =>
      let s := x.getId.toString
      match PrimTy.ofName? s with
      | some .uint => `(Ty.uint)
      | some .int => `(Ty.int)
      | some .bool => `(Ty.bool)
      | none =>
        -- a struct of the table; an enum never reaches here (`expandMemberTy`),
        -- nor does a narrow type where one may stand (`expandMemberTyW`)
        if (narrowTy? s).isSome then Lean.Macro.throwErrorAt x (narrowNestedMsg s)
        else if (structDef s).isEmpty then Lean.Macro.throwErrorAt x (unknownStructMsg s)
        else `(Ty.struct $(Lean.quote s))
  | `(ty!(address payable)) => `(Ty.uint)
  | `(ty!(mapping($K => $V))) => `(Ty.mapping pty!($K) ty!($V))
  | `(ty!($T[])) => `(Ty.array ty!($T))
  | `(ty!($T[$n])) => `(Ty.fixed ty!($T) $n)

/-! ## The types an index carries

What the typed syntax (`Syntax/Scoped.lean`) indexes a path by: how an
array or a mapping is indexed. -/

/-- An array type and its element type: a dynamic array `E[]`, or a
fixed-size one `E[n]`.  Both are indexed by position and bounds-checked
alike; only a dynamic one has `push`/`pop` (`Stmt.push` takes `.array E`),
and only a fixed one's length is known statically (the elaborator writes
`fixedValues.length` as the literal `3`).  solkey's `Path[…,array]` is
either (`PathSVSort.typeCategoryOf`), so a rule over an array index is one
rule over `ArrTy`. -/
inductive ArrTy : RefTy → Ty → Type where
  | dyn {E : Ty} : ArrTy (.array E) E
  | fixed {E : Ty} {n : Nat} : ArrTy (.fixed E n) E

/-- How a reference type is indexed: a mapping by its key, an array (either
kind) by a `uint`.  One `Loc.index` serves both, so a rule that does not care
which is one constructor, and the ones that do fix it. -/
inductive IndexTy : RefTy → PrimTy → Ty → Type where
  | map {k : PrimTy} {V : Ty} : IndexTy (.mapping k V) k V
  | arr {R : RefTy} {E : Ty} (a : ArrTy R E) : IndexTy R .uint E

/-- `new R(n)` can be written: `R` is an array type whose elements a
memory object can hold (no mapping) and whose default is well-formed. -/
def RefTy.newArrOk : RefTy → Bool
  | .array E => E.mapFree && E.defaultOkS
  | _ => false

/-! ## Printing helpers -/

/-- `x++`, `−−x`: a decrement is spelled with two minus signs `−` (U+2212),
since `--` opens a comment in Lean (`Syntax.lean`, the grammar). -/
def IncDec.show (op : IncDec) (x : String) : String :=
  let t := if op.isIncrement then "++" else "−−"
  if op.isPre then t ++ x else x ++ t

/-- A block's statements in braces: `{ x = 1; }`, and `{ }` for none. -/
def braced (ss : List String) : String :=
  if ss.isEmpty then "{ }" else s!"\{ {" ".intercalate ss} }"

/-! ## The grammar -/

declare_syntax_cat sol_expr (behavior := both)
syntax:max num : sol_expr
syntax:max ident : sol_expr
syntax:max sol_expr:max "." ident : sol_expr
syntax:max sol_expr:max "[" sol_expr "]" : sol_expr
syntax:max "(" sol_expr ")" : sol_expr
/-- `(a, b)`: a tuple, the right-hand side of a tuple assignment or of a
`return` of several values (`RawExpr.tuple`). -/
syntax:max (name := solTupleExpr) "(" sol_expr ", " sol_expr,+ ")" : sol_expr
/-- An assignment inside an expression, parenthesized: `(x = e)`, `(x += e)`. -/
syntax:max "(" sol_expr " = " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " += " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " -= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " *= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " /= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " %= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " &= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " |= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " ^= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " <<= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " >>= " sol_expr ")" : sol_expr
syntax:80 "!" sol_expr:80 : sol_expr
syntax:80 "-" sol_expr:80 : sol_expr
/-- `a ** b`, right-associative and tighter than `*` (solc ≥ 0.8). -/
syntax:75 sol_expr:76 " ** " sol_expr:75 : sol_expr
syntax:70 sol_expr:70 " * " sol_expr:71 : sol_expr
syntax:70 sol_expr:70 " / " sol_expr:71 : sol_expr
syntax:70 sol_expr:70 " % " sol_expr:71 : sol_expr
syntax:65 sol_expr:65 " + " sol_expr:66 : sol_expr
syntax:65 sol_expr:65 " - " sol_expr:66 : sol_expr
/-- solc's precedence: `+ -` > `<< >>` > `&` > `^` > `|` > comparisons. -/
syntax:60 sol_expr:60 " << " sol_expr:61 : sol_expr
syntax:60 sol_expr:60 " >> " sol_expr:61 : sol_expr
syntax:58 sol_expr:58 " & " sol_expr:59 : sol_expr
syntax:56 sol_expr:56 " ^ " sol_expr:57 : sol_expr
syntax:54 sol_expr:54 " | " sol_expr:55 : sol_expr
/-- `~x`.  The category reads a leading atom as a non-reserved keyword, which
`~` (no Lean token) cannot be: `ppAllowUngrouped` makes it not the first. -/
syntax:80 ppAllowUngrouped "~" sol_expr:80 : sol_expr
/-- The wrapping arithmetic of an `unchecked { … }` block, spelt as Zig spells
it: `a +% b` is `a + b` modulo `2^256`.  Not Solidity: it is what the printers
write for an operator inside `unchecked`, and it reads back. -/
syntax:75 sol_expr:76 " **% " sol_expr:75 : sol_expr
syntax:70 sol_expr:70 " *% " sol_expr:71 : sol_expr
syntax:65 sol_expr:65 " +% " sol_expr:66 : sol_expr
syntax:65 sol_expr:65 " -% " sol_expr:66 : sol_expr
syntax:50 sol_expr:51 " < " sol_expr:51 : sol_expr
syntax:50 sol_expr:51 " > " sol_expr:51 : sol_expr
syntax:50 sol_expr:51 " <= " sol_expr:51 : sol_expr
syntax:50 sol_expr:51 " >= " sol_expr:51 : sol_expr
syntax:45 sol_expr:46 " == " sol_expr:46 : sol_expr
syntax:45 sol_expr:46 " != " sol_expr:46 : sol_expr
syntax:35 sol_expr:36 " && " sol_expr:35 : sol_expr
syntax:30 sol_expr:31 " || " sol_expr:30 : sol_expr
syntax:20 sol_expr:21 " ? " sol_expr:21 " : " sol_expr:20 : sol_expr
/-! `++` and `−−` inside an expression (`values[i++] = 1;`).  A decrement is
spelled with two minus signs `−` (U+2212): `--` opens a line comment in Lean,
so `x--` cannot be written in a `sol{ … }` block, and `x -= 1` is another
statement.  The postfix forms have precedence `arg`, below a member access,
so that a statement `x++;` (whose target is read at `max`) is not read as an
expression. -/
syntax:arg sol_expr:max "++" : sol_expr
syntax:arg sol_expr:max "−−" : sol_expr
syntax:max "++" sol_expr:max : sol_expr
syntax:max "−−" sol_expr:max : sol_expr
/-- `new uint[](n)`: a fresh memory array. -/
syntax:max &"new" sol_ty "(" sol_expr ")" : sol_expr
/-! `address(this).balance`, the contract's own funds: one form, since an
`address(…)` conversion is not otherwise an expression here.  `msg.sender`,
`msg.value` and `block.timestamp` arrive as identifiers (`expandIdent`). -/
syntax:max &"address" "(" &"this" ")" "." &"balance" : sol_expr

/-! What elaborates away (`sol{ … }` reads it, no statement or value holds
it): an ether or time unit on a number literal (`2 ether`, `3 days`), the
casts `payable(e)` and `address(e)` of a value (identities: an address is a
`uint`), a struct constructor with named arguments (`T({f: a, g: b})`), and
a call's (`f({q: b, p: a})`). -/

/-- `2 ether`, `3 days`: the literal times its unit (`wei gwei ether`,
`seconds minutes hours days weeks`). -/
syntax:max atomic(num ident) : sol_expr
/-- `payable(e)`: `e`. -/
syntax:max atomic(&"payable" "(") sol_expr ")" : sol_expr
/-- `address(e)`: `e` (not `address(this)`, which is no value here). -/
syntax:max atomic(&"address" "(") sol_expr ")" : sol_expr
/-- `T({f: a, g: b})`: a struct constructor with named arguments. -/
syntax:max atomic(ident "(" "{") (ident ": " sol_expr),* "}" ")" : sol_expr

/-- `f(a, b)` inside an expression (`x = f(a) + 1;`), captured before its
statement (`hoist`).  At precedence `arg`, as a postfix `++`: a statement
`f(a);` reads its callee at `max`, so it stays the call statement, and the
call statements below are preferred (`priority := high`) where both
readings take the same text (`y = f(a);`, `lsv = values.push();`). -/
syntax:arg (name := solCallExpr) sol_expr:max "(" sol_expr,* ")" : sol_expr
/-- `choosePersonMem().account`: a member of a call's value, a memory
reference (`hoist` captures the call).  At `max`, as a member is; `atomic`,
so that a call with no member after it is left to the readings above. -/
syntax:max (name := solCallMember) sol_expr:max atomic("(" sol_expr,* ")" ".") ident : sol_expr
/-- A call's storage reference indexed, `matrixRef()[i]`: the call before the index. -/
syntax:max (name := solCallIndex) sol_expr:max atomic("(" sol_expr,* ")" "[") sol_expr "]" : sol_expr

declare_syntax_cat sol_stmt (behavior := both)
declare_syntax_cat sol_block (behavior := both)

section Semi
open Lean Parser PrettyPrinter

/-- The last token of a node: an atom or an identifier. -/
partial def lastToken? : Syntax → Option Syntax
  | .node _ _ args => args.reverse.findSome? lastToken?
  | .missing => none
  | s => some s

/-- `;` after a statement, which a statement ending in a block (`if (c) { … }`,
`unchecked { … }`) may leave out: it is then read as if written, so the
statement's syntax is the same either way. -/
def solSemiFn : ParserFn := fun c s =>
  let s' := symbolFn ";" c s
  if s'.hasError && (lastToken? s.stxStack.back).any (·.isToken "}") then
    s.pushSyntax (mkAtom ";")
  else s'

def solSemi : Parser :=
  { fn := solSemiFn, info := { collectTokens := (";" :: ·) } }

@[combinator_formatter solSemi]
def solSemi.formatter : Formatter := Formatter.symbolNoAntiquot.formatter ";"

@[combinator_parenthesizer solSemi]
def solSemi.parenthesizer : Parenthesizer := Parenthesizer.symbolNoAntiquot.parenthesizer ";"

end Semi

syntax "{" (sol_stmt solSemi)* "}" : sol_block
syntax sol_expr " = " sol_expr : sol_stmt
syntax sol_ty ident : sol_stmt
syntax sol_ty ident " = " sol_expr : sol_stmt
syntax sol_ty &"storage" ident : sol_stmt
syntax sol_ty &"storage" ident " = " sol_expr : sol_stmt
syntax sol_ty &"memory" ident : sol_stmt
syntax sol_ty &"memory" ident " = " sol_expr : sol_stmt
syntax (name := solDelete) "delete" ppSpace sol_expr : sol_stmt
-- `.push(`, `.push()` and `.pop()` are tokens, so a push on a member or an
-- entry is spelt with them; one on a name is an identifier `values.push`
-- called.
syntax sol_expr ".push(" sol_expr ")" : sol_stmt
syntax sol_expr ".push()" : sol_stmt
syntax (name := solPushAddAssign) sol_expr ".push()" " += " sol_expr : sol_stmt
syntax (name := solPushSubAssign) sol_expr ".push()" " -= " sol_expr : sol_stmt
syntax (name := solPushMulAssign) sol_expr ".push()" " *= " sol_expr : sol_stmt
syntax (name := solPushDivAssign) sol_expr ".push()" " /= " sol_expr : sol_stmt
syntax (name := solPushModAssign) sol_expr ".push()" " %= " sol_expr : sol_stmt
syntax (name := solPushPreInc) "++" sol_expr ".push()" : sol_stmt
syntax (name := solPushPreDec) "−−" sol_expr ".push()" : sol_stmt
syntax (name := solPushPostInc) sol_expr ".push()" "++" : sol_stmt
syntax (name := solPushPostDec) sol_expr ".push()" "−−" : sol_stmt
syntax (name := solPushCallPreInc) "++" sol_expr:max "(" ")" : sol_stmt
syntax (name := solPushCallPreDec) "−−" sol_expr:max "(" ")" : sol_stmt
syntax (name := solPushCallPostInc) sol_expr:max "(" ")" "++" : sol_stmt
syntax (name := solPushCallPostDec) sol_expr:max "(" ")" "−−" : sol_stmt
syntax sol_expr ".pop()" : sol_stmt
syntax sol_expr " = " sol_expr ".push()" : sol_stmt
/-- `values .push() = e;`, `a[i].push() = e;`: a push used as a target spelt
with the `.push()` token; on a name or a member chain it is the push
`b.push(e);`, on another receiver refused (`expandStmt.pushTarget`). -/
syntax (name := solPushTarget) sol_expr ".push()" " = " sol_expr : sol_stmt
syntax sol_ty &"storage" ident " = " sol_expr ".push()" : sol_stmt
/-- `uint y = values.push();`: the slot appended, `y` its default. -/
syntax sol_ty ident " = " sol_expr ".push()" : sol_stmt
syntax sol_expr ".transfer(" sol_expr ")" : sol_stmt
syntax sol_expr " = " sol_expr ".send(" sol_expr ")" : sol_stmt
syntax sol_ty ident " = " sol_expr ".send(" sol_expr ")" : sol_stmt
/-- `(ok, ) = r.call{value: a}("");`: a send with all the gas (`RawStmt.send`). -/
syntax (name := solValueCall) "(" sol_expr ", " ")" " = " sol_expr:max "{" &"value" ": " sol_expr "}"
  "(" str ")" : sol_stmt
/-- `(bool ok, ) = r.call{value: a}("");`. -/
syntax (name := solValueCallDecl) "(" sol_ty ident ", " ")" " = " sol_expr:max "{" &"value" ": "
  sol_expr "}" "(" str ")" : sol_stmt
syntax sol_expr:max "(" ")" : sol_stmt
syntax sol_expr:max "(" sol_expr ")" : sol_stmt
syntax (priority := high) sol_expr " = " sol_expr:max "(" ")" : sol_stmt
/-- A call of the contract's function with two arguments or more. -/
syntax sol_expr:max "(" sol_expr ", " sol_expr,+ ")" : sol_stmt
/-- `y = f(a, b);`: a call assigned. -/
syntax (priority := high) sol_expr " = " sol_expr:max "(" sol_expr,+ ")" : sol_stmt
/-- `uint y = f(a);`: a call declared. -/
syntax (priority := high) sol_ty ident " = " sol_expr:max "(" sol_expr,* ")" : sol_stmt
/-- `return e;`, `return;`: anywhere in a function's body (`lowerReturns`). -/
syntax (name := solReturn) "return " sol_expr : sol_stmt
syntax (name := solReturnNone) "return" : sol_stmt
syntax (priority := high) sol_ty &"storage" ident " = " sol_expr:max "(" ")" : sol_stmt
syntax sol_expr:max "++" : sol_stmt
syntax "++" sol_expr : sol_stmt
syntax sol_expr " = " sol_expr:max "++" : sol_stmt
syntax sol_expr " = " "++" sol_expr : sol_stmt
syntax sol_expr:max "−−" : sol_stmt
syntax "−−" sol_expr : sol_stmt
syntax sol_expr " = " sol_expr:max "−−" : sol_stmt
syntax sol_expr " = " "−−" sol_expr : sol_stmt
syntax sol_expr " += " sol_expr : sol_stmt
syntax sol_expr " -= " sol_expr : sol_stmt
syntax sol_expr " *= " sol_expr : sol_stmt
syntax sol_expr " /= " sol_expr : sol_stmt
syntax sol_expr " %= " sol_expr : sol_stmt
syntax sol_expr " &= " sol_expr : sol_stmt
syntax sol_expr " |= " sol_expr : sol_stmt
syntax sol_expr " ^= " sol_expr : sol_stmt
syntax sol_expr " <<= " sol_expr : sol_stmt
syntax sol_expr " >>= " sol_expr : sol_stmt
/-- `unchecked { … }`: its `+ - * **` wrap at `2^256` instead of reverting. -/
syntax (name := solUnchecked) &"unchecked" ppSpace sol_block : sol_stmt
/-- `checked { … }`: an overflow in it fails as an `assert` does
(`Prog.checkOF`), not as a revert. -/
syntax (name := solChecked) &"checked" ppSpace sol_block : sol_stmt
/-- `ignoringOverflow { … }`: a run in which an operation leaves its range
proves anything (`Prog.ignoreOF`), under either modality. -/
syntax (name := solIgnoringOverflow) &"ignoringOverflow" ppSpace sol_block : sol_stmt
syntax "if " "(" sol_expr ") " sol_block (" else " sol_block)? : sol_stmt
/-- `if (c) { … } else if (d) { … } else { … }`: the `if`s nested. -/
syntax (name := solIfChain) "if " "(" sol_expr ") " sol_block
  (atomic(" else " "if ") "(" sol_expr ") " sol_block)+ (" else " sol_block)? : sol_stmt
syntax (name := solRequire) &"require" "(" sol_expr ")" : sol_stmt
syntax (name := solAssert) &"assert" "(" sol_expr ")" : sol_stmt
syntax (name := solRevert) &"revert" "(" ")" : sol_stmt
/-- `assume(false);`: not Solidity; the statement `ignoringOverflow { … }`
writes where an operation leaves its range (`Stmt.assumeFalse`). -/
syntax (name := solAssumeFalse) &"assume" "(" &"false" ")" : sol_stmt
/-- `emit E(a, b);`: the arguments evaluated (`RawStmt.eval`), the log dropped. -/
syntax (name := solEmit) &"emit" ident "(" sol_expr,* ")" : sol_stmt
/-- `require(c, "msg");`: `require(c);`. -/
syntax (name := solRequireMsg) &"require" "(" sol_expr ", " str ")" : sol_stmt
/-- `require(c, Err(a));`: `RawStmt.requireWith`. -/
syntax (name := solRequireErr) &"require" "(" sol_expr ", " ident "(" sol_expr,* ")" ")" : sol_stmt
/-- `revert Err(a);`: `revert();`, since a revert undoes whatever evaluating
`a` did. -/
syntax (name := solRevertErr) &"revert" ident "(" sol_expr,* ")" : sol_stmt
/-- `revert("msg");`: `revert();`. -/
syntax (name := solRevertMsg) &"revert" "(" str ")" : sol_stmt
/-- `_;`: where a modifier's body runs the function's (`contract!{ … }`). -/
syntax (name := solHole) "_" : sol_stmt
/-- `(a, , b) = e;`: a tuple assignment, a component left out discarded
(`RawStmt.tupleAssign`).  One comma at least, so that it is not `(a) = e;`. -/
syntax (name := solTupleAssign) "(" (sol_expr)? (", " (sol_expr)?)+ ")" " = " sol_expr : sol_stmt
/-- `(uint a, , bool b) = e;`: a tuple declaration (`RawStmt.tupleDecl`). -/
syntax (name := solTupleDecl) "(" (sol_ty ident)? (", " (sol_ty ident)?)+ ")" " = " sol_expr :
  sol_stmt
/-- `{ … }`: a block (`RawStmt.block`). -/
syntax (name := solBlockStmt) "{" (sol_stmt solSemi)* "}" : sol_stmt
/-- `while (c) { … }` -/
syntax (name := solWhile) "while " "(" sol_expr ") " sol_block : sol_stmt
/-- `for (init; c; upd) { … }`, each of the three parts optional. -/
syntax (name := solFor) "for " "(" (sol_stmt)? "; " (sol_expr)? "; " (sol_stmt)? ") " sol_block :
  sol_stmt
/-- `do { … } while (c);` -/
syntax (name := solDoWhile) "do " sol_block " while " "(" sol_expr ")" : sol_stmt
/-- `break;` -/
syntax (name := solBreak) "break" : sol_stmt
/-- `continue;` -/
syntax (name := solContinue) "continue" : sol_stmt
/-! `/// @custom:key invariant e`, `/// @custom:key decreases e` above a loop,
solkey's loop specification, and, Lean only, `/// @custom:key unwind k`
(`RawLoopSpec`).  A clause is a category of its own: a statement's leading
atom must already be a token (`sol_stmt` reads leading keywords as
identifiers too), and `///` is not one. -/
declare_syntax_cat sol_loop_clause
syntax "/// " "@" &"custom" ":" &"key" ident sol_expr : sol_loop_clause
/-- A quantified invariant's body: an expression, `a -> c`, or another
`\forall`. -/
declare_syntax_cat sol_loop_inv
syntax "\\" noWs &"forall " ident ident "; " sol_loop_inv : sol_loop_inv
syntax sol_expr " -> " sol_expr : sol_loop_inv
syntax sol_expr : sol_loop_inv
/-- `/// @custom:key invariant \forall uint q; a -> c`: a quantified clause. -/
syntax (name := solLoopForall) "/// " "@" &"custom" ":" &"key" &"invariant" "\\" noWs &"forall "
  ident ident "; " sol_loop_inv : sol_loop_clause
syntax (name := solLoopSpec) sol_loop_clause ppSpace sol_stmt : sol_stmt
/-! `try e.f(a) returns (uint v) { … } catch Error(string memory m) { … }
catch Panic(uint c) { … } catch (bytes memory d) { … } catch { … }`: an
external call.  A clause's parameter is `sol_tparam`: a type, `memory` for
`string`/`bytes`, an optional name. -/
declare_syntax_cat sol_tparam (behavior := both)
syntax sol_ty (ppSpace &"memory")? (ppSpace ident)? : sol_tparam
declare_syntax_cat sol_rparam (behavior := both)
syntax sol_ty (ppSpace (&"memory" <|> &"storage"))? (ppSpace ident)? : sol_rparam
declare_syntax_cat sol_catch (behavior := both)
syntax (name := solCatchError) "catch " &"Error" "(" sol_tparam ") " sol_block : sol_catch
syntax (name := solCatchPanic) "catch " &"Panic" "(" sol_tparam ") " sol_block : sol_catch
syntax (name := solCatchData) "catch " "(" sol_tparam ") " sol_block : sol_catch
syntax (name := solCatchAll) "catch " sol_block : sol_catch
syntax (name := solTry) "try " sol_expr (ppSpace &"returns" " (" sol_tparam,* ")")? ppSpace sol_block
  (ppSpace sol_catch)+ : sol_stmt
/-- `T memory t = T(a, b);`: a struct constructor declared. -/
syntax sol_ty &"memory" ident " = " sol_expr "(" sol_expr,* ")" : sol_stmt
/-- `todos.push(Todo(a, b));`: a struct constructor pushed. -/
syntax sol_expr "(" sol_expr "(" sol_expr,* ")" ")" : sol_stmt
syntax sol_expr ".push(" sol_expr "(" sol_expr,* ")" ")" : sol_stmt

/-! The schema forms of the taclets (`Calculus/RuleSyntax.lean`): an
escape `‹t›` to any Lean term, and the operator schema variables.  They live
with the grammar, whose tokens they extend. -/

/-- `‹t›`: any Lean term, in a program position. -/
syntax:max "‹" term "›" : sol_expr
syntax "‹" term "›" : sol_stmt
/-- A block that is a schema variable: `if (se) thn else els`. -/
syntax ident : sol_block
syntax "‹" term "›" : sol_block
/-- A binary operator schema variable `op`. -/
syntax:65 sol_expr:65 " ⊕ " sol_expr:66 : sol_expr
/-- A unary operator schema variable `op`. -/
syntax:80 "⊖" sol_expr:80 : sol_expr
/-- An increment or decrement schema variable `op`. -/
syntax sol_expr "⊕⊕" : sol_stmt
syntax sol_expr " = " sol_expr "⊕⊕" : sol_stmt
/-- A compound assignment with an operator schema variable `op`. -/
syntax sol_expr " ⊕= " sol_expr : sol_stmt

/-- `sol_raw!{ s₁; s₂; … }`: the raw statements, before elaboration. -/
syntax "sol_raw!{" (sol_stmt solSemi)* "}" : term

/-- The dot-separated parts of a name: `alice.account` is `["alice", "account"]`. -/
def nameParts : Lean.Name → List String
  | .anonymous => []
  | .str p s => nameParts p ++ [s]
  | .num p n => nameParts p ++ [toString n]

section Expand
open Lean

partial def expandTy : TSyntax `sol_ty → MacroM Term
  | `(sol_ty| $x:ident) => `(RawTy.named $(quote x.getId.toString))
  | `(sol_ty| address payable) => `(RawTy.named "address")
  | `(sol_ty| mapping ( $k => $v )) => do `(RawTy.mapping $(← expandTy k) $(← expandTy v))
  | `(sol_ty| $t[]) => do `(RawTy.array $(← expandTy t))
  | `(sol_ty| $t[$n]) => do `(RawTy.fixed $(← expandTy t) $n)
  | _ => Macro.throwUnsupported

/-- What a unit multiplies a literal by: `1 gwei` is `10^9`, `1 days` is
`86400`. -/
def unitFactor? : String → Option Nat
  | "wei" => some 1
  | "gwei" => some (10 ^ 9)
  | "ether" => some (10 ^ 18)
  | "seconds" => some 1
  | "minutes" => some 60
  | "hours" => some 3600
  | "days" => some 86400
  | "weeks" => some 604800
  | _ => none

/-- The constructor's name, to splice. -/
def EnvKey.ident : EnvKey → Ident
  | .msgSender => mkIdent ``EnvKey.msgSender
  | .msgValue => mkIdent ``EnvKey.msgValue
  | .timestamp => mkIdent ``EnvKey.timestamp
  | .selfBalance => mkIdent ``EnvKey.selfBalance
  | .selfAddress => mkIdent ``EnvKey.selfAddress

/-- A name, as a string literal. -/
def strLit (x : Ident) : Term := quote x.getId.toString

/-- `e.f.g`: the members `fs` of `e`. -/
def fieldChain (e : Term) (fs : List String) : MacroM Term :=
  foldFields (mkIdent ``RawExpr.field) e fs

/-- `alice.account.age` arrives as one identifier; split it into members;
`msg.sender` and `block.timestamp` are the environment's. -/
def expandIdent (x : Ident) : MacroM Term := do
  match nameParts x.getId with
  | [] => Macro.throwError "empty identifier"
  | ["true"] => `(RawExpr.bool true)
  | ["false"] => `(RawExpr.bool false)
  | ["this"] => `(RawExpr.env .selfAddress)
  | root :: f :: flds =>
    match EnvKey.ofParts root f with
    | some k => fieldChain (← `(RawExpr.env $(k.ident))) flds
    | none => fieldChain (← `(RawExpr.name $(quote root))) (f :: flds)
  | root :: flds => fieldChain (← `(RawExpr.name $(quote root))) flds

/-- `f`, a function's name: an identifier with no member access. -/
def funName? (f : TSyntax `sol_expr) : Option String :=
  match f with
  | `(sol_expr| $x:ident) =>
    match nameParts x.getId with
    | [g] => some g
    | _ => none
  | _ => none

/-- `a ⊕ b` for an operator of the table (`BinOp.ofSym?`): a node
`[a, ⊕, b]`, whatever its kind. -/
def binParts? (s : Syntax) : Option (BinOp × Syntax × Syntax) :=
  if s.getNumArgs == 3 && s[1].isAtom then
    (BinOp.ofSym? s[1].getAtomVal).map (·, s[0], s[2])
  else none

/-- `e++`, `−−e`: a node `[e, tok]` or `[tok, e]` (`IncDec.ofTok?`). -/
def incDecParts? (s : Syntax) : Option (IncDec × Syntax) :=
  if s.getNumArgs != 2 then none
  else if s[1].isAtom then (IncDec.ofTok? false s[1].getAtomVal).map (·, s[0])
  else if s[0].isAtom then (IncDec.ofTok? true s[0].getAtomVal).map (·, s[1])
  else none

/-- The receiver of a method named `push`, before its empty argument list. -/
def pushMethodBase? : TSyntax `sol_expr → MacroM (Option (TSyntax `sol_expr))
  | `(sol_expr| $x:ident) => do
    match (nameParts x.getId).reverse with
    | "push" :: r :: rs =>
      let n := (r :: rs).reverse.foldl (fun n s => Name.str n s) Name.anonymous
      return some (← `(sol_expr| $(mkIdentFrom x n):ident))
    | _ => return none
  | `(sol_expr| $b:sol_expr . $f:ident) =>
    pure (if f.getId.toString == "push" then some b else none)
  | _ => pure none

/-- `b.push()` as a compound or increment lvalue, optionally parenthesized. -/
partial def pushLvalueBase? : TSyntax `sol_expr → MacroM (Option (TSyntax `sol_expr))
  | `(sol_expr| $f:sol_expr ( )) => pushMethodBase? f
  | `(sol_expr| ($e:sol_expr)) => pushLvalueBase? e
  | _ => pure none

/-- Both the fused `.push()` token and an ordinary method-call expression
can spell `rows[i].push() += rhs`. -/
def pushCompoundParts? (s : Syntax) : MacroM (Option (BinOp × TSyntax `sol_expr × TSyntax `sol_expr)) := do
  let fixed := match s.getKind with
    | ``solPushAddAssign => some BinOp.add | ``solPushSubAssign => some BinOp.sub
    | ``solPushMulAssign => some BinOp.mul | ``solPushDivAssign => some BinOp.div
    | ``solPushModAssign => some BinOp.mod | _ => none
  if let some op := fixed then return some (op, ⟨s[0]⟩, ⟨s[3]⟩)
  if s.getNumArgs == 3 && s[1].isAtom && s[1].getAtomVal.endsWith "=" then
    if let some op := BinOp.ofSym? (s[1].getAtomVal.dropRight 1) then
      if let some b ← pushLvalueBase? ⟨s[0]⟩ then return some (op, b, ⟨s[2]⟩)
  return none

/-- A discarded push increment/decrement, including calls whose callee
lexes as the dotted identifier `values.push`. -/
def pushIncrementParts? (s : Syntax) : MacroM (Option (IncDec × TSyntax `sol_expr)) := do
  match s.getKind with
  | ``solPushPreInc => return some (.preInc, ⟨s[1]⟩)
  | ``solPushPreDec => return some (.preDec, ⟨s[1]⟩)
  | ``solPushPostInc => return some (.postInc, ⟨s[0]⟩)
  | ``solPushPostDec => return some (.postDec, ⟨s[0]⟩)
  | ``solPushCallPreInc | ``solPushCallPreDec =>
    let some b ← pushMethodBase? ⟨s[1]⟩ | return none
    return some ((if s.isOfKind ``solPushCallPreInc then .preInc else .preDec), b)
  | ``solPushCallPostInc | ``solPushCallPostDec =>
    let some b ← pushMethodBase? ⟨s[0]⟩ | return none
    return some ((if s.isOfKind ``solPushCallPostInc then .postInc else .postDec), b)
  | _ =>
    if let some (op, l) := incDecParts? s then
      if let some b ← pushLvalueBase? ⟨l⟩ then return some (op, b)
    return none

/-- Of an ambiguous parse, the readings `good` accepts first, then all of them;
of an unambiguous one, itself. -/
def readings (s : Syntax) (good : Syntax → Bool) : Array Syntax :=
  if s.isOfKind choiceKind then s.getArgs.filter good ++ s.getArgs else #[s]

/-- Of an ambiguous parse, the first reading `good` accepts (else the first). -/
def preferReading (s : Syntax) (good : Syntax → Bool) : Syntax :=
  (readings s good)[0]?.getD s

/-- What a call's callee must be. -/
def callMsg : String := "a call's callee is a function's name"

/-- What a push used as a target is written on. -/
def pushTargetMsg : String :=
  "`b.push() = e;` is written on a name or a member chain, `bucket.tokens`"

/-- The expressions and blocks of a node, its atoms and groupings dropped. -/
partial def payload (s : Syntax) : Array Syntax :=
  if s.isAtom then #[]
  else if s.getKind == nullKind || s.getKind == groupKind then s.getArgs.flatMap payload
  else #[s]

/-- `type(T).max`, `type(T).min`: an integer type's bound as a value of `T`
(`uint8(255)`, `int8(-128)`: solc types it `T`, so `type(uint8).max + 1`
overflows at `uint8`); an enum's, its first or last member, which the
elaborator reads (`enumLit?`, the member `type(max)`) -/
def typeBoundExpr (f : TSyntax `sol_expr) (as : Array (TSyntax `sol_expr)) (g : Ident) :
      MacroM (Option Term) := do
  unless funName? f == some "type" do return none
  let #[a] := as | return none
  let some T := funName? a | return none
  let m := g.getId.toString
  unless m == "max" || m == "min" do
    Macro.throwErrorAt g s!"type({T}).{m}: only `max` and `min` are modelled"
  match castTy? T with
  | some (p, n) =>
    let v : Int := if p == .int then
        (if m == "max" then 2 ^ (n - 1) - 1 else -(2 ^ (n - 1) : Int))
      else (if m == "max" then 2 ^ n - 1 else 0)
    let lit ← if v < 0 then `(RawExpr.unop .neg (.num $(quote v.natAbs)))
      else `(RawExpr.num $(quote v.toNat))
    return some (← `(RawExpr.call $(quote T) [$lit]))
  | none => return some (← `(RawExpr.field (.name $(quote T)) $(quote s!"type({m})")))

partial def expandExpr (e : TSyntax `sol_expr) : MacroM Term := do
  if e.raw.isOfKind ``solTupleExpr then
    let es := #[e.raw[1]] ++ e.raw[3].getSepArgs
    return ← `(RawExpr.tuple [$(← es.mapM (expandExpr ⟨·⟩)),*])
  -- `(l = r)`, `(l ⊕= r)`: by their tokens
  let r := e.raw
  if r.getNumArgs == 5 && r[0].isAtom && r[0].getAtomVal == "(" && r[2].isAtom &&
      r[2].getAtomVal.endsWith "=" && r[4].isAtom then
    let sym := r[2].getAtomVal
    if sym == "=" then
      return ← `(RawExpr.assign $(← expandExpr ⟨r[1]⟩) $(← expandExpr ⟨r[3]⟩))
    if let some op := BinOp.ofSym? (sym.dropRight 1) then
      return ← `(RawExpr.opAssign $(ctorIdent ``BinOp op) $(← expandExpr ⟨r[1]⟩)
        $(← expandExpr ⟨r[3]⟩))
  -- the operators, by their table: one arm for all of them
  if let some (op, a, b) := binParts? e then
    return ← `(RawExpr.binop $(ctorIdent ``BinOp op) $(← expandExpr ⟨a⟩) $(← expandExpr ⟨b⟩))
  if let some (op, a) := incDecParts? e then
    return ← `(RawExpr.incDec $(ctorIdent ``IncDec op) $(← expandExpr ⟨a⟩))
  expandExpr1 e
where
  expandExpr1 : TSyntax `sol_expr → MacroM Term
  | `(sol_expr| $n:num) => `(RawExpr.num $n)
  | `(sol_expr| $x:ident) => expandIdent x
  | `(sol_expr| $e:sol_expr . $f:ident) => do fieldChain (← expandExpr e) (nameParts f.getId)
  | `(sol_expr| $e:sol_expr [ $k:sol_expr ]) => do
      `(RawExpr.index $(← expandExpr e) $(← expandExpr k))
  | `(sol_expr| ( $e:sol_expr )) => expandExpr e
  | `(sol_expr| ! $a) => do `(RawExpr.unop .not $(← expandExpr a))
  | `(sol_expr| - $a) => do `(RawExpr.unop .neg $(← expandExpr a))
  | `(sol_expr| ~ $a) => do `(RawExpr.unop .bnot $(← expandExpr a))
  | `(sol_expr| $c ? $a : $b) => do
      `(RawExpr.ternary $(← expandExpr c) $(← expandExpr a) $(← expandExpr b))
  | `(sol_expr| new $T:sol_ty ( $n:sol_expr )) => do
      `(RawExpr.newArr $(← expandTy T) $(← expandExpr n))
  | `(sol_expr| address ( this ) . balance) => `(RawExpr.env .selfBalance)
  | `(sol_expr| $n:num $u:ident) => do
      let some k := unitFactor? u.getId.toString |
        Macro.throwErrorAt u "a unit is one of wei gwei ether seconds minutes hours days weeks"
      `(RawExpr.num $(quote (n.getNat * k)))
  | `(sol_expr| payable ( $e:sol_expr )) => expandExpr e
  | `(sol_expr| address ( $e:sol_expr )) => expandExpr e
  | `(sol_expr| $f:ident ( { $[$ns:ident : $as:sol_expr],* } )) => do
      `(RawExpr.named $(strLit f) [$(ns.map strLit),*] [$(← as.mapM expandExpr),*])
  | `(sol_expr| $f:sol_expr ( $as:sol_expr,* ) . $g:ident) => do
      if let some t ← typeBoundExpr f as.getElems g then return t
      fieldChain (← expandCall f as.getElems callMsg) (nameParts g.getId)
  | `(sol_expr| $f:sol_expr ( $as:sol_expr,* ) [ $k:sol_expr ]) => do
      `(RawExpr.index $(← expandCall f as.getElems callMsg) $(← expandExpr k))
  | `(sol_expr| $f:sol_expr ( $as:sol_expr,* )) => expandCall f as.getElems callMsg
  | _ => Macro.throwUnsupported
  -- `f(a, b)`, a call of the function `f` (or a struct's constructor, `msg`
  -- says which): `RawExpr.call`
  expandCall (f : TSyntax `sol_expr) (as : Array (TSyntax `sol_expr)) (msg : String) :
      MacroM Term := do
  let some g := funName? f | Macro.throwErrorAt f msg
  `(RawExpr.call $(quote g) [$(← as.mapM expandExpr),*])

partial def expandStmt (s : TSyntax `sol_stmt) : MacroM Term := do
  -- `delete x` also parses as a declaration `T x` of a type called
  -- `delete`, and `require(c)` as a call (the categories read keywords as
  -- identifiers too): of an ambiguous parse, take the reading that starts
  -- with a keyword.
  if s.raw.isOfKind choiceKind then
    for alt in readings s (·[0].isAtom) do
      try return ← expandStmt ⟨alt⟩ catch _ => pure ()
    Macro.throwUnsupported
  -- `x++;`, `−−x;` and `l ⊕= r;`: by their tokens.  (`y = x++;` is read as
  -- an assignment of the expression `x++`, which `hoistStmt` makes an
  -- `assignIncDec` when `y` is a local: its other parse is not expanded.)
  let r := s.raw
  if let some (op, b, rhs) ← pushCompoundParts? r then
    return ← `(RawStmt.pushOpAssign $(ctorIdent ``BinOp op) $(← expandExpr b) $(← expandExpr rhs))
  if let some (op, b) ← pushIncrementParts? r then
    return ← `(RawStmt.pushIncDec $(ctorIdent ``IncDec op) $(← expandExpr b))
  if let some (op, l) := incDecParts? r then
    return ← `(RawStmt.incDec $(ctorIdent ``IncDec op) $(← expandExpr ⟨l⟩))
  if r.getNumArgs == 3 && r[1].isAtom && r[1].getAtomVal.endsWith "=" then
    if let some op := BinOp.ofSym? (r[1].getAtomVal.dropRight 1) then
      return ← `(RawStmt.opAssign $(ctorIdent ``BinOp op) $(← expandExpr ⟨r[0]⟩)
        $(← expandExpr ⟨r[2]⟩))
  -- the four keyword statements, by their node kind: a quotation pattern
  -- for them would be as ambiguous as the parse
  match s.raw.getKind with
  | ``solDelete => `(RawStmt.delete $(← expandExpr ⟨s.raw[1]⟩))
  | ``solRequire => `(RawStmt.require $(← expandExpr ⟨s.raw[2]⟩))
  | ``solAssert => `(RawStmt.assert $(← expandExpr ⟨s.raw[2]⟩))
  | ``solRevert => `(RawStmt.revert)
  | ``solAssumeFalse => `(RawStmt.assumeFalse)
  | ``solReturn => `(RawStmt.ret (some $(← expandExpr ⟨s.raw[1]⟩)))
  | ``solReturnNone => `(RawStmt.ret none)
  | ``solTry => expandTry s
  | ``solEmit => `(RawStmt.eval [$(← exprs s.raw[3]),*])
  | ``solRequireMsg => `(RawStmt.require $(← expandExpr ⟨s.raw[2]⟩))
  | ``solRequireErr => `(RawStmt.requireWith $(← expandExpr ⟨s.raw[2]⟩) [$(← exprs s.raw[6]),*])
  | ``solRevertErr | ``solRevertMsg => `(RawStmt.revert)
  | ``solHole => `(RawStmt.hole)
  | ``solBreak => `(RawStmt.brk)
  | ``solContinue => `(RawStmt.cont)
  | ``solWhile | ``solFor | ``solDoWhile => expandStmt.loop s (← `({}))
  | ``solLoopSpec => do
    -- the clauses down to the loop, in the order written
    let mut cur := s.raw
    let mut inv : Array Term := #[]
    let mut dec : Option Term := none
    let mut unw : Option Term := none
    let mut qinv : Array Term := #[]
    while cur.getKind == ``solLoopSpec do
      let cl := cur[0]
      if cl.getKind == ``solLoopForall then
        qinv := qinv.push (← expandStmt.loopForall cl[8] cl[9] cl[11])
        cur := cur[1]
        continue
      let k := cl[5].getId.toString
      let e := cl[6]
      match k with
      | "invariant" => inv := inv.push (← expandExpr ⟨e⟩)
      | "decreases" =>
        if dec.isSome then Macro.throwErrorAt cur "a loop has one `decreases` clause"
        dec := some (← expandExpr ⟨e⟩)
      | "unwind" =>
        let some n := e.isNatLit? <|> e[0].isNatLit? |
          Macro.throwErrorAt e "`/// @custom:key unwind k` takes a number"
        if unw.isSome then Macro.throwErrorAt cur "a loop has one `unwind` clause"
        unw := some (quote n)
      | _ => Macro.throwErrorAt cl[5] "a loop's clause is `invariant`, `decreases` or `unwind`"
      cur := cur[1]
    unless cur.getKind == ``solWhile || cur.getKind == ``solFor || cur.getKind == ``solDoWhile do
      Macro.throwErrorAt cur "a `/// @custom:key` clause stands above a loop"
    let decT ← match dec with
      | some d => `(some $d)
      | none => `(none)
    let unwT ← match unw with
      | some n => `(some $n)
      | none => `(none)
    expandStmt.loop ⟨cur⟩
      (← `({ inv := [$inv,*], dec := $decT, unwind := $unwT, qinv := [$qinv,*] : RawLoopSpec }))
  | ``solPushTarget =>
    expandStmt.pushTarget s ⟨s.raw[0]⟩ (← expandExpr ⟨s.raw[0]⟩) (← expandExpr ⟨s.raw[3]⟩)
  | ``solUnchecked => `(RawStmt.unchecked $(← expandStmt.expandBlock ⟨s.raw[1]⟩))
  | ``solChecked => `(RawStmt.checked .checking $(← expandStmt.expandBlock ⟨s.raw[1]⟩))
  | ``solIgnoringOverflow =>
    `(RawStmt.checked .ignoring $(← expandStmt.expandBlock ⟨s.raw[1]⟩))
  | ``solBlockStmt => `(RawStmt.block [$(← (payload s.raw[1]).mapM (expandStmt ⟨·⟩)),*])
  | ``solTupleAssign =>
    let ts ← (#[s.raw[1]] ++ s.raw[2].getArgs).mapM fun o => do
      match payload o with
      | #[e] => `(some $(← expandExpr ⟨e⟩))
      | _ => `(none)
    `(RawStmt.tupleAssign [$ts,*] $(← expandExpr ⟨s.raw[5]⟩))
  | ``solTupleDecl =>
    let vs ← (#[s.raw[1]] ++ s.raw[2].getArgs).mapM fun o => do
      match payload o with
      | #[T, x] => `(some ($(← expandTy ⟨T⟩), $(strLit ⟨x⟩)))
      | _ => `(none)
    `(RawStmt.tupleDecl [$vs,*] $(← expandExpr ⟨s.raw[5]⟩))
  | ``solIfChain =>
    -- `if (c₀) b₀ else if (c₁) b₁ … else e`: nested, from the last branch out
    let arms := payload s.raw[5]
    let last : Term ← match payload s.raw[6] with
      | #[f] => expandStmt.expandBlock ⟨f⟩
      | _ => `([])
    let els ← (List.range (arms.size / 2)).foldrM (init := last) fun k els => do
      `([RawStmt.ite $(← expandExpr ⟨arms[2 * k]!⟩) $(← expandStmt.expandBlock ⟨arms[2 * k + 1]!⟩)
        $els])
    `(RawStmt.ite $(← expandExpr ⟨s.raw[2]⟩) $(← expandStmt.expandBlock ⟨s.raw[4]⟩) $els)
  | _ => expandStmt1 s
where
  /-- The expressions of a `sol_expr,*`. -/
  exprs (as : Syntax) : MacroM (Array Term) := as.getSepArgs.mapM (expandExpr ⟨·⟩)
  /-- `\forall T x; b`, a quantified invariant clause (`RawInv`); a sort as the
  specification language reads it, an `address` a `uint`. -/
  loopForall (T x body : Syntax) : MacroM Term := do
    let p ← match T.getId.toString with
      | "uint" | "address" => `(PrimTy.uint)
      | "int" => `(PrimTy.int)
      | "bool" => `(PrimTy.bool)
      | s => Macro.throwErrorAt T s!"a quantifier ranges over uint, int, bool or address, not {s}"
    let b ← match (⟨body⟩ : TSyntax `sol_loop_inv) with
      | `(sol_loop_inv| \forall $T':ident $x':ident; $b') => loopForall T' x' b'
      | `(sol_loop_inv| $a:sol_expr -> $c:sol_expr) => do
        `(RawInv.imp $(← expandExpr a) $(← expandExpr c))
      | `(sol_loop_inv| $e:sol_expr) => do `(RawInv.expr $(← expandExpr e))
      | _ => Macro.throwErrorAt body "a quantified invariant's body is `e` or `a -> c`"
    `(RawInv.all $p $(strLit ⟨x⟩) $b)
  expandStmt1 : TSyntax `sol_stmt → MacroM Term
  | `(sol_stmt| $l:sol_expr = $r:sol_expr) => do assignTo l (← expandExpr r)
  | `(sol_stmt| $l:sol_expr = $b:sol_expr .push()) => do
      `(RawStmt.assignPush $(← expandExpr l) $(← expandExpr b))
  | `(sol_stmt| $l:sol_expr = $f:sol_expr ( )) => do
      match funName? f with
      | some g => assignTo l (← `(RawExpr.call $(quote g) []))
      | none => `(RawStmt.assignPush $(← expandExpr l) $(← pushRecv f))
  | `(sol_stmt| $l:sol_expr = $f:sol_expr ( $as:sol_expr,* )) => do
      if let some s ← send? none (← expandExpr l) f as.getElems then return s
      assignTo l (← expandExpr.expandCall f as.getElems callMsg)
  | `(sol_stmt| $T:sol_ty $x:ident = $b:sol_expr .push()) => do
      `(RawStmt.declPush $(← expandTy T) $(strLit x) $(← expandExpr b))
  | `(sol_stmt| $T:sol_ty $x:ident = $f:sol_expr ( )) => do
      match funName? f with
      | some g => `(RawStmt.decl $(← expandTy T) $(strLit x) (some (RawExpr.call $(quote g) [])))
      | none => `(RawStmt.declPush $(← expandTy T) $(strLit x) $(← pushRecv f))
  | `(sol_stmt| $T:sol_ty $x:ident = $f:sol_expr ( $as:sol_expr,* )) => do
      if let some s ← send? (some (← expandTy T)) (← `(RawExpr.name $(strLit x))) f as.getElems then
        return s
      `(RawStmt.decl $(← expandTy T) $(strLit x) (some $(← expandExpr.expandCall f as.getElems callMsg)))
  | `(sol_stmt| $f:sol_expr ( $a:sol_expr, $as:sol_expr,* )) => do
      `(RawStmt.call $(← expandExpr f) [$(← expandExpr a), $(← as.getElems.mapM expandExpr),*])
  | `(sol_stmt| $T:sol_ty memory $x:ident = $f:sol_expr ( $as:sol_expr,* )) => do
      `(RawStmt.declMemory $(← expandTy T) $(strLit x)
        (some $(← expandExpr.expandCall f as.getElems ctorMsg)))
  | `(sol_stmt| $b:sol_expr ( $g:sol_expr ( $as:sol_expr,* ) )) => do
      `(RawStmt.call $(← expandExpr b) [$(← expandExpr.expandCall g as.getElems ctorMsg)])
  | `(sol_stmt| $b:sol_expr .push( $g:sol_expr ( $as:sol_expr,* ) )) => do
      `(RawStmt.call (.field $(← expandExpr b) "push") [$(← expandExpr.expandCall g as.getElems ctorMsg)])
  | `(sol_stmt| $T:sol_ty storage $x:ident = $b:sol_expr .push()) => do
      `(RawStmt.declStoragePush $(← expandTy T) $(strLit x) $(← expandExpr b))
  | `(sol_stmt| $T:sol_ty storage $x:ident = $f:sol_expr ( )) => do
      match funName? f with
      | some g => `(RawStmt.declStorage $(← expandTy T) $(strLit x)
          (some (RawExpr.call $(quote g) [])))
      | none => `(RawStmt.declStoragePush $(← expandTy T) $(strLit x) $(← pushRecv f))
  | `(sol_stmt| $T:sol_ty storage $x:ident = $e) => do
      `(RawStmt.declStorage $(← expandTy T) $(strLit x) (some $(← expandExpr e)))
  | `(sol_stmt| $T:sol_ty storage $x:ident) => do
      `(RawStmt.declStorage $(← expandTy T) $(strLit x) none)
  | `(sol_stmt| $T:sol_ty memory $x:ident = $e) => do
      `(RawStmt.declMemory $(← expandTy T) $(strLit x) (some $(← expandExpr e)))
  | `(sol_stmt| $T:sol_ty memory $x:ident) => do
      `(RawStmt.declMemory $(← expandTy T) $(strLit x) none)
  | `(sol_stmt| $T:sol_ty $x:ident = $e) => do
      `(RawStmt.decl $(← expandTy T) $(strLit x) (some $(← expandExpr e)))
  | `(sol_stmt| $T:sol_ty $x:ident) => do
      `(RawStmt.decl $(← expandTy T) $(strLit x) none)
  | `(sol_stmt| $b:sol_expr .push( $a:sol_expr )) => do
      `(RawStmt.call (.field $(← expandExpr b) "push") [$(← expandExpr a)])
  | `(sol_stmt| $b:sol_expr .push()) => do `(RawStmt.call (.field $(← expandExpr b) "push") [])
  | `(sol_stmt| $b:sol_expr .pop()) => do `(RawStmt.call (.field $(← expandExpr b) "pop") [])
  | `(sol_stmt| $r:sol_expr .transfer( $a:sol_expr )) => do
      `(RawStmt.call (.field $(← expandExpr r) "transfer") [$(← expandExpr a)])
  | `(sol_stmt| $l:sol_expr = $r:sol_expr .send( $a:sol_expr )) => do
      `(RawStmt.send none $(← expandExpr l) $(← expandExpr r) $(← expandExpr a) false)
  | `(sol_stmt| $T:sol_ty $x:ident = $r:sol_expr .send( $a:sol_expr )) => do
      `(RawStmt.send (some $(← expandTy T)) (.name $(strLit x)) $(← expandExpr r)
        $(← expandExpr a) false)
  | `(sol_stmt| ( $l:sol_expr , ) = $f:sol_expr { value : $a:sol_expr } ( $d:str )) => do
      unless d.getString.isEmpty do Macro.throwErrorAt d "a value call with no calldata only"
      let some r ← recvOf? "call" f | Macro.throwErrorAt f "`r.call{value: a}(\"\")`"
      `(RawStmt.send none $(← expandExpr l) $r $(← expandExpr a) true)
  | `(sol_stmt| ( $T:sol_ty $x:ident , ) = $f:sol_expr { value : $a:sol_expr } ( $d:str )) => do
      unless d.getString.isEmpty do Macro.throwErrorAt d "a value call with no calldata only"
      let some r ← recvOf? "call" f | Macro.throwErrorAt f "`r.call{value: a}(\"\")`"
      `(RawStmt.send (some $(← expandTy T)) (.name $(strLit x)) $r $(← expandExpr a) true)
  | `(sol_stmt| $f:sol_expr ( )) => do `(RawStmt.call $(← expandExpr f) [])
  | `(sol_stmt| $f:sol_expr ( $a:sol_expr )) => do
      `(RawStmt.call $(← expandExpr f) [$(← expandExpr a)])
  | `(sol_stmt| if ($c) $t $[else $f]?) => do
      let els ← match f with
        | some f => expandBlock f
        | none => `([])
      `(RawStmt.ite $(← expandExpr c) $(← expandBlock t) $els)
  | _ => Macro.throwUnsupported
  /-- A struct constructor's callee. -/
  ctorMsg : String := "a constructor's name is a struct's name"
  /-- `values.push`, `bucket.tokens.push` (one identifier) or `e.tokens.push`:
  the receiver `values`, `bucket.tokens`, `e.tokens`; none for another callee. -/
  pushRecv? (f : TSyntax `sol_expr) : MacroM (Option Term) := recvOf? "push" f
  /-- The receiver of the member `m` called: `to` of `to.send`, as
  `pushRecv?` reads `values.push`. -/
  recvOf? (m : String) (f : TSyntax `sol_expr) : MacroM (Option Term) := do
    match f with
    | `(sol_expr| $x:ident) =>
      match x.getId with
      | .str p m' => if p.isAnonymous || m' != m then pure none else some <$> expandIdent (mkIdent p)
      | _ => pure none
    | `(sol_expr| $e:sol_expr . $g:ident) =>
      match (nameParts g.getId).reverse with
      | m' :: fs => if m' == m then some <$> fieldChain (← expandExpr e) fs.reverse else pure none
      | _ => pure none
    | _ => pure none
  /-- `l = r.send(a);` and `T x = r.send(a);` where the receiver is a name or
  a member chain (`to.send` is one identifier): the send, else none. -/
  send? (T : Option Term) (l : Term) (f : TSyntax `sol_expr) (as : Array (TSyntax `sol_expr)) :
      MacroM (Option Term) := do
    let #[a] := as | pure none
    let some r ← recvOf? "send" f | pure none
    let T ← match T with
      | some T => `(some $T)
      | none => `(none)
    some <$> `(RawStmt.send $T $l $r $(← expandExpr a) false)
  /-- The receiver of `b.push` (`pushRecv?`). -/
  pushRecv (f : TSyntax `sol_expr) : MacroM Term := do
    match ← pushRecv? f with
    | some b => pure b
    | none => Macro.throwErrorAt f "only `b.push()` is a call on the right of `=`"
  /-- `l = r;`, `r` expanded: the assignment, or, when `l` is `b.push()`, the
  push `b.push(r);` (the front end normalises a push used as a target
  so).  solc evaluates `r` before the push's receiver; `b` is a name or a
  member chain, which no effect of `r` moves and which cannot revert, so
  evaluating it first, as `b.push(r)` does, is the same run, and the slot the
  push adds is written once either way. -/
  assignTo (l : TSyntax `sol_expr) (r : Term) : MacroM Term := do
    if l.raw.isOfKind ``solTupleExpr then
      let ts := #[l.raw[1]] ++ l.raw[3].getSepArgs
      return ← `(RawStmt.tupleAssign [$(← ts.mapM fun t => do `(some $(← expandExpr ⟨t⟩))),*] $r)
    if let `(sol_expr| $f:sol_expr ( $as:sol_expr,* )) := l then
      if as.getElems.isEmpty then
        if let some b ← pushRecv? f then return ← pushTarget l f b r
    `(RawStmt.assign $(← expandExpr l) $r)
  /-- `b.push() = r;`, `b` and `r` expanded: the push `b.push(r);` when the
  receiver, spelt `chain` (`b` or `b.push`), is a name or a member chain
  (`assignTo` says why the order is solc's); refused at `ref` otherwise. -/
  pushTarget (ref : Syntax) (chain : TSyntax `sol_expr) (b r : Term) : MacroM Term := do
    unless nameChain chain do Macro.throwErrorAt ref pushTargetMsg
    `(RawStmt.call (.field $b "push") [$r])
  /-- A name or a member chain of names: `values`, `bucket.tokens`,
  `bucket .tokens.push`. -/
  nameChain : TSyntax `sol_expr → Bool
    | `(sol_expr| $_:ident) => true
    | `(sol_expr| $e:sol_expr . $_:ident) => nameChain e
    | _ => false
  expandBlock : TSyntax `sol_block → MacroM Term
    | `(sol_block| { $[$ss:sol_stmt;]* }) => do `([$(← ss.mapM expandStmt),*])
    | _ => Macro.throwUnsupported
  /-- A loop, with its specification `spec`. -/
  loop (s : TSyntax `sol_stmt) (spec : Term) : MacroM Term := do
    let r := s.raw
    match r.getKind with
    | ``solWhile => `(RawStmt.whileLoop $spec $(← expandExpr ⟨r[2]⟩) $(← expandBlock ⟨r[4]⟩))
    | ``solDoWhile => `(RawStmt.doWhile $spec $(← expandBlock ⟨r[1]⟩) $(← expandExpr ⟨r[4]⟩))
    | _ =>
      let part (o : Syntax) : MacroM Term := do
        match payload o with
        | #[t] => `([$(← expandStmt ⟨t⟩)])
        | _ => `([])
      let c ← match payload r[4] with
        | #[e] => `(some $(← expandExpr ⟨e⟩))
        | _ => `(none)
      `(RawStmt.forLoop $spec $(← part r[2]) $c $(← part r[6]) $(← expandBlock ⟨r[8]⟩))
  /-- A clause's parameter: its type and its name, if it has one. -/
  tparam (p : Syntax) : MacroM (Term × Option String) := do
    let T ← expandTy ⟨p[0]⟩
    pure (T, if p[2].getNumArgs > 0 then some p[2][0].getId.toString else none)
  /-- The receiver of an external call: `I(a)` and `address(a)` are `a`. -/
  extRecv (r : TSyntax `sol_expr) : MacroM Term := do
    match r with
    | `(sol_expr| $_:ident ( $a:sol_expr )) => expandExpr a
    | _ => expandExpr r
  /-- `e.f(a₁, …)`: the receiver `e`, the name `f`, the arguments. -/
  extCall (e : TSyntax `sol_expr) : MacroM (Term × String × Array Term) := do
    let `(sol_expr| $f:sol_expr ( $as:sol_expr,* )) := e
      | Macro.throwErrorAt e "`try` takes an external call `e.f(…)`"
    let args ← as.getElems.mapM expandExpr
    match f with
    | `(sol_expr| $x:ident) =>
      match (nameParts x.getId).reverse with
      | g :: r :: rs => do
        let rs := (r :: rs).reverse
        pure (← fieldChain (← expandIdent (mkIdent (.mkSimple rs.head!))) rs.tail, g, args)
      | _ => Macro.throwErrorAt e "`try` takes an external call `e.f(…)`"
    | `(sol_expr| $r:sol_expr . $g:ident) =>
      match (nameParts g.getId).reverse with
      | h :: fs => do pure (← fieldChain (← extRecv r) fs.reverse, h, args)
      | [] => Macro.throwUnsupported
    | `(sol_expr| $c:sol_expr ( $bs:sol_expr,* ) . $g:ident) => do
      let r ← match bs.getElems with
        | #[b] => if (funName? c).isSome then expandExpr b else expandExpr.expandCall c bs.getElems callMsg
        | _ => expandExpr.expandCall c bs.getElems callMsg
      match (nameParts g.getId).reverse with
      | h :: fs => do pure (← fieldChain r fs.reverse, h, args)
      | [] => Macro.throwUnsupported
    | _ => Macro.throwErrorAt e "`try` takes an external call `e.f(…)`"
  /-- `try …`, its clauses normalised as solkey's `TryStatement.of` does. -/
  expandTry (s : TSyntax `sol_stmt) : MacroM Term := do
    let r := s.raw
    let (recv, f, args) ← extCall ⟨r[1]⟩
    let mut rets : Array Term := #[]
    if r[2].getNumArgs > 0 then
      for p in r[2][2].getSepArgs do
        let (T, x) ← tparam p
        let some x := x | Macro.throwErrorAt p "an external call's return value is named"
        rets := rets.push (← `(($T, $(quote x))))
    let ok ← expandBlock ⟨r[3]⟩
    let mut err : Option Term := none
    let mut pnc : Option Term := none
    let mut code : Option String := none
    let mut other : Option Term := none
    for c in r[4].getArgs do
      let c := if c.getKind == nullKind && c.getNumArgs == 1 then c[0] else c
      match c.getKind with
      | ``solCatchError => err := some (← expandBlock ⟨c[5]⟩)
      | ``solCatchPanic =>
        pnc := some (← expandBlock ⟨c[5]⟩)
        code := (← tparam c[3]).2
      | ``solCatchData => other := some (← expandBlock ⟨c[4]⟩)
      | ``solCatchAll => other := some (← expandBlock ⟨c[1]⟩)
      | _ => Macro.throwErrorAt c "a `catch` clause"
    let otherB ← match other with
      | some b => pure b
      | none => `([RawStmt.revert])
    `(RawStmt.tryCall $recv $(quote f) [$args,*] [$rets,*] $ok $(err.getD otherB)
        $(quote code) $(pnc.getD otherB) $otherB)

macro_rules
  | `(sol_raw!{ $[$ss:sol_stmt;]* }) => do `([$(← ss.mapM expandStmt),*])

end Expand

/-! ## `contract!{ … }`

A contract written as Solidity writes one, less what elaborates away: a
state variable's visibility, a function's visibility and mutability, events
and errors (declared, then dropped), and enums (read as `uint`, a member as
its position).  A modifier is inlined around the body of each function that
applies it (`wrapMods`), as a call is inlined where it is called. -/

declare_syntax_cat sol_member (behavior := both)

/-- A state variable's visibility, dropped. -/
declare_syntax_cat sol_vis (behavior := both)
syntax &"public" : sol_vis
syntax &"private" : sol_vis
syntax &"internal" : sol_vis
syntax &"immutable" : sol_vis
syntax &"constant" : sol_vis

/-- `uint public count;`: a state variable. -/
syntax sol_ty sol_vis* ident ";" : sol_member
/-- `uint x = 5;`: a state variable with an initializer, which the
constructor runs (`Contract.inits`).  A `constant` or an `immutable` is one
too, as solkey reads it: a storage root with an initializer. -/
syntax sol_ty sol_vis* ident " = " sol_expr ";" : sol_member

/-- A parameter, `uint x`. -/
declare_syntax_cat sol_param (behavior := both)
syntax sol_ty ident : sol_param
syntax sol_ty (&"memory" <|> &"storage" <|> &"calldata") ident : sol_param

/-- A function's attribute: its return variables, `returns (uint r)`,
`returns (Person memory p)`, `returns (uint lo, uint hi)`; a visibility or a
mutability (dropped); or a modifier applied, `onlyOwner`,
`inState(State.Created)`. -/
declare_syntax_cat sol_fattr (behavior := both)
syntax (name := solAttrReturns) &"returns" "(" sol_rparam,+ ")" : sol_fattr
syntax (name := solAttrKw) (&"public" <|> &"external" <|> &"internal" <|> &"private" <|> &"view" <|>
  &"pure" <|> &"payable" <|> &"virtual" <|> &"override") : sol_fattr
syntax (name := solAttrMod) ident ("(" sol_expr,* ")")? : sol_fattr

/-- `function f(uint x, uint y) returns (uint r) { r = x + y; }`: an internal
function, which may call the functions declared before it. -/
syntax &"function " ident "(" sol_param,* ")" sol_fattr* ppSpace sol_block : sol_member

/-- `constructor(uint v) payable { … }`: the contract's constructor
(`Contract.ctor`), which only a deployment calls, `constructor(args);`. -/
syntax (name := solConstructor) &"constructor" "(" sol_param,* ")" sol_fattr* ppSpace sol_block :
  sol_member

/-- `modifier inState(State s) { if (state != s) revert(); _; }`: the code
before and after its one `_;`. -/
syntax &"modifier " ident ("(" sol_param,* ")")? ppSpace sol_block : sol_member

/-- An event's or an error's parameter, `address indexed from`. -/
declare_syntax_cat sol_eparam (behavior := both)
syntax sol_ty (&"indexed")? (ppSpace ident)? : sol_eparam

/-- `event Sent(address from, uint amount);`, dropped. -/
syntax &"event " ident "(" sol_eparam,* ")" ";" : sol_member
/-- `error Unauthorized(uint code);`, dropped. -/
syntax &"error " ident "(" sol_eparam,* ")" ";" : sol_member
/-- `enum State { Created, Locked }`: `State.Locked` is `1`. -/
syntax &"enum " ident "{" ident,* "}" : sol_member

/-- A clause of the specification, where solkey's NatSpec line stands:
`requires e;` and `ensures e;` above the function they specify (`/// @custom:key
requires e`), `skip;` for a function with no obligation, `invariant e;`
anywhere, a clause of the contract. -/
syntax (name := solRequires) (priority := high) &"requires " spec_expr ";" : sol_member
syntax (name := solEnsures) (priority := high) &"ensures " spec_expr ";" : sol_member
syntax (name := solSkip) (priority := high) &"skip" ";" : sol_member
syntax (name := solInvariant) (priority := high) &"invariant " spec_expr ";" : sol_member
/-- `assignable count, balances[msg.sender];` or `assignable \nothing;`: what
the next function may change (solkey's `@custom:key assignable`). -/
syntax (name := solAssignable) (priority := high) &"assignable " spec_locs ";" : sol_member

/-- `contract!{ uint total; Person alice; mapping(uint => Person) folks; }`:
a contract written as Solidity declares its state, and its functions. -/
syntax "contract!{" sol_member* "}" : term

section
open Lean

/-- The words among a function's attributes that are not modifiers. -/
def attrKeywords : List String :=
  ["public", "external", "internal", "private", "view", "pure", "payable", "virtual", "override"]

/-- A declared type, an enum of the contract read as `uint`. -/
def expandMemberTy (enums : List String) (T : TSyntax `sol_ty) : MacroM Term :=
  match T with
  | `(sol_ty| $x:ident) => if enums.contains x.getId.toString then `(Ty.uint) else `(ty!($T))
  | _ => `(ty!($T))

def expandParams (enums : List String) (ps : Array (TSyntax `sol_param)) : MacroM (Array Term) :=
  ps.mapM fun
    | `(sol_param| $T:sol_ty $x:ident) => do `(($(strLit x), $(← expandMemberTy enums T)))
    | _ => Macro.throwUnsupported

/-- `expandMemberTy` where a narrow type may stand: a `uint8` is `Ty.uint` and
its width. -/
def expandMemberTyW (enums : List String) (T : TSyntax `sol_ty) : MacroM (Term × Option Nat) :=
  match T with
  | `(sol_ty| $x:ident) =>
    match narrowTy? x.getId.toString with
    | some (.int, n) => do pure (← `(Ty.int), some n)
    | some (_, n) => do pure (← `(Ty.uint), some n)
    | none => do pure (← expandMemberTy enums T, none)
  | _ => do pure (← expandMemberTy enums T, none)

/-- A function's parameters, and the rows of `FunDecl.widths` for the narrow ones. -/
def expandParamsW (enums : List String) (ps : Array (TSyntax `sol_param)) :
    MacroM (Array Term × Array Term × Array Term) := do
  let mut rows := #[]
  let mut ws := #[]
  let mut locs := #[]
  for p in ps do
    let (T, x, loc) ← match p with
      | `(sol_param| $T:sol_ty $x:ident) => pure (T, x, none)
      | `(sol_param| $T:sol_ty memory $x:ident) => pure (T, x, some ParamLoc.memory)
      | `(sol_param| $T:sol_ty storage $x:ident) => pure (T, x, some ParamLoc.storage)
      | `(sol_param| $T:sol_ty calldata $x:ident) => pure (T, x, some ParamLoc.calldata)
      | _ => Macro.throwUnsupported
    let (t, w) ← expandMemberTyW enums T
    rows := rows.push (← `(($(strLit x), $t)))
    if let some n := w then ws := ws.push (← `(($(strLit x), $(quote n))))
    if let some loc := loc then
      let l ← match loc with
        | .memory => `(ParamLoc.memory)
        | .storage => `(ParamLoc.storage)
        | .calldata => `(ParamLoc.calldata)
      locs := locs.push (← `(($(strLit x), $l)))
  pure (rows, ws, locs)

/-- A modifier: its name, its parameters, and its body, with a `_;` at least
(solc's "Modifier body does not contain '_'"), anywhere. -/
def expandModifier (enums : List String) (m : Ident) (ps : Array (TSyntax `sol_param))
    (b : TSyntax `sol_block) : MacroM (String × Array Term × Term) := do
  let `(sol_block| { $[$ss:sol_stmt;]* }) := b | Macro.throwErrorAt b "a modifier's body is a block"
  unless (b.raw.find? (·.isOfKind ``solHole)).isSome do
    Macro.throwErrorAt b "a modifier's body has a `_;`"
  pure (m.getId.toString, ← expandParams enums ps, ← `([$(← ss.mapM expandStmt),*]))

/-- A function's declaration, as a term: its return variable and its
modifiers read off its attributes. -/
def expandFun (enums : List String) (mods : List (String × Array Term × Term)) (f : Ident)
    (ps : Array (TSyntax `sol_param)) (attrs : Array (TSyntax `sol_fattr))
    (b : TSyntax `sol_block) (spec : Term) : MacroM Term := do
  let (ps, ws, locs) ← expandParamsW enums ps
  let mut ws := ws
  -- `payable` is an atom of the keyword reading and an identifier of the
  -- modifier reading
  let payable := attrs.any fun a => (a.raw.find? fun s =>
    s.isAtom && s.getAtomVal == "payable" || s.isIdent && s.getId == `payable).isSome
  let mut rets : Array Term := #[]
  let mut retMem := false
  let mut retStorage := false
  let mut apps : Array Term := #[]
  for a in attrs do
    -- `returns (uint)` also reads as a modifier `returns` applied to `uint`,
    -- and `view` as a modifier `view`: take the other reading
    let a := preferReading a.raw (!·.isOfKind ``solAttrMod)
    if a.isOfKind ``solAttrKw then continue
    if a.isOfKind ``solAttrReturns then
      -- Return locations are separate from external try/catch parameters.
      let ps := a[2].getSepArgs
      for i in [0:ps.size] do
        -- A location also reads as the return variable's name: take the location.
        let p := preferReading ps[i]! (!·[1].isNone)
        let n := (p[2].getOptional?.map (·.getId.toString)).getD
          (if ps.size == 1 then "_ret" else s!"_ret{i}")
        let (t, w) ← expandMemberTyW enums ⟨p[0]⟩
        if let some b := w then ws := ws.push (← `(($(quote n), $(quote b))))
        rets := rets.push (← `(($(quote n), $t)))
        retMem := retMem || (p[1].find? fun s => s.isAtom && s.getAtomVal == "memory").isSome
        retStorage := retStorage || (p[1].find? fun s => s.isAtom && s.getAtomVal == "storage").isSome
      continue
    match (⟨a⟩ : TSyntax `sol_fattr) with
    | `(sol_fattr| $m:ident $[( $as:sol_expr,* )]?) =>
      let name := m.getId.toString
      if attrKeywords.contains name then continue
      let some (_, params, mb) := mods.find? (·.1 == name) |
        Macro.throwErrorAt m s!"{name} is not a modifier of this contract"
      let args ← match as with
        | some as => as.getElems.mapM expandExpr
        | none => pure #[]
      apps := apps.push (← `(ModApp.mk $(quote name) [$params,*] [$args,*] $mb))
    | _ => Macro.throwUnsupported
  let body ← expandStmt.expandBlock b
  `(($(strLit f),
    ({ params := [$ps,*], paramLocs := [$locs,*], rets := [$rets,*], retMem := $(quote retMem),
       retStorage := $(quote retStorage), body := $body,
       mods := [$apps,*], spec := $spec, payable := $(quote payable),
       widths := [$ws,*] } : FunDecl)))

end

macro_rules
  | `(contract!{ $ms:sol_member* }) => do
      -- the enums and the modifiers first: a function may apply a modifier
      -- declared after it
      let mut enums : List String := []
      let mut enumRows : Array Lean.Term := #[]
      let mut mods := []
      for m in ms do
        match m with
        | `(sol_member| enum $e:ident { $xs:ident,* }) =>
          enums := enums ++ [e.getId.toString]
          enumRows := enumRows.push (← `(($(strLit e), [$(xs.getElems.map strLit),*])))
        | _ => pure ()
      for m in ms do
        match m with
        | `(sol_member| modifier $f:ident $[( $ps:sol_param,* )]? $b:sol_block) =>
          mods := mods ++ [← expandModifier enums f ((ps.map (·.getElems)).getD #[]) b]
        | _ => pure ()
      let mut rows := #[]
      let mut widthRows : Array Lean.Term := #[]
      let mut funs := #[]
      -- the clauses read since the last function: they specify the next one
      let mut reqs : Array Lean.Term := #[]
      let mut enss : Array Lean.Term := #[]
      let mut skip := false
      let mut asg : Option Lean.Term := none
      let mut invs : Array Lean.Term := #[]
      let mut ctor : Option Lean.Term := none
      let mut initRows : Array Lean.Term := #[]
      for m in ms do
        -- `requires x;` also reads as a state variable `x` of a type `requires`
        let m : Lean.TSyntax `sol_member := ⟨preferReading m.raw fun a =>
          [``solRequires, ``solEnsures, ``solSkip, ``solInvariant, ``solAssignable].any a.isOfKind⟩
        match m with
        | `(sol_member| requires $e:spec_expr ;) => reqs := reqs.push (← expandSpec e)
        | `(sol_member| ensures $e:spec_expr ;) => enss := enss.push (← expandSpec e)
        | `(sol_member| skip ;) => skip := true
        | `(sol_member| assignable $ls:spec_locs ;) =>
          if asg.isSome then Lean.Macro.throwErrorAt m "one `assignable` clause per function"
          asg := some (← expandSpecLocs ls)
        | `(sol_member| invariant $e:spec_expr ;) => invs := invs.push (← expandSpec e)
        | `(sol_member| $T:sol_ty $_:sol_vis* $x:ident ;) =>
          let (t, w) ← expandMemberTyW enums T
          rows := rows.push (← `(($(strLit x), $t)))
          if let some n := w then widthRows := widthRows.push (← `(($(strLit x), $(Lean.quote n))))
        | `(sol_member| $T:sol_ty $_:sol_vis* $x:ident = $e:sol_expr ;) =>
          let (t, w) ← expandMemberTyW enums T
          rows := rows.push (← `(($(strLit x), $t)))
          if let some n := w then widthRows := widthRows.push (← `(($(strLit x), $(Lean.quote n))))
          initRows := initRows.push (← `(($(strLit x), $(← expandExpr e))))
        | `(sol_member| constructor ( $ps:sol_param,* ) $as:sol_fattr* $b:sol_block) =>
          if ctor.isSome then Lean.Macro.throwErrorAt m "a second constructor: a contract declares one"
          for a in as do
            if (preferReading a.raw (!·.isOfKind ``solAttrMod)).isOfKind ``solAttrReturns then
              Lean.Macro.throwErrorAt a "a constructor returns nothing: no `returns`"
          let asgT ← match asg with
            | some ls => `(some $ls)
            | none => `(none)
          let spec ← `(({ requires := [$reqs,*], ensures := [$enss,*], assignable := $asgT,
                          skip := $(Lean.quote skip) } : FunSpec))
          let d ← expandFun enums mods (Lean.mkIdent `constructor) ps.getElems as b spec
          ctor := some (← `(some ($d).2))
          reqs := #[]; enss := #[]; skip := false; asg := none
        | `(sol_member| function $f:ident ( $ps:sol_param,* ) $as:sol_fattr* $b:sol_block) =>
          if f.getId.toString == "constructor" then
            Lean.Macro.throwErrorAt f "`constructor` names the constructor, not a function"
          let asgT ← match asg with
            | some ls => `(some $ls)
            | none => `(none)
          let spec ← `(({ requires := [$reqs,*], ensures := [$enss,*], assignable := $asgT,
                          skip := $(Lean.quote skip) } : FunSpec))
          funs := funs.push (← expandFun enums mods f ps.getElems as b spec)
          reqs := #[]; enss := #[]; skip := false; asg := none
        | `(sol_member| modifier $_:ident $[( $_:sol_param,* )]? $_:sol_block)
        | `(sol_member| event $_:ident ( $_:sol_eparam,* ) ;)
        | `(sol_member| error $_:ident ( $_:sol_eparam,* ) ;)
        | `(sol_member| enum $_:ident { $_:ident,* }) => pure ()
        | _ => Lean.Macro.throwUnsupported
      unless reqs.isEmpty && enss.isEmpty && !skip && asg.isNone do
        Lean.Macro.throwError
          "a `requires`, `ensures`, `assignable` or `skip` clause after the last function"
      let ctorT ← match ctor with
        | some t => pure t
        | none => `(none)
      `(({ vars := [$rows,*], funs := [$funs,*], enums := [$enumRows,*], inv := [$invs,*],
           widths := [$widthRows,*], ctor := $ctorT, inits := [$initRows,*] } : Contract))
/-! ### The contracts

One per store of `Semantics.lean`, under the store's renames, with
`address` read as `uint` as the interpreter does.  `initStorage_*` there
checks each against its store. -/

/-- `StandardExample.sol`, with the `people` array of the worked examples. -/
def StandardExample : Contract := contract!{
  uint total; uint age; uint owner; uint balance;
  uint[] values;
  mapping(uint => uint) balances;
  mapping(uint => bool) flags;
  mapping(uint => Person) folks;
  uint[][] matrix;
  Person[] persons;
  Person[] people;
  Person alice; Person bob;
  Wallet wallet;
}

/-- `TestSuite.sol`, as ported. -/
def TestSuite : Contract := contract!{
  uint total; uint age; uint owner; uint balance;
  uint[] values; uint[] aux;
  uint[][] matrix;
  mapping(uint => uint) balances;
  mapping(uint => Person) folks;
  mapping(uint => bool) flags;
  mapping(uint => uint) valuesMap;
  mapping(uint => Account) accountMap;
  Person[] persons;
  Person alice; Person bob;
  Ledger ledger;
  Token[] tokens;
  TokenBucket bucket;
  LedgerUse[] ledgerUses;
  bool flag; bool flag2;
  bool[] boolFlags;
  Toggle toggle;
  Token tok;
  TokenBucket[] buckets;
  Basket basketA; Basket basketB;
  int signedTotal;
  uint[3] fixedValues;
  uint[3][] rows;
  Token[2] fixedTokens;
  mapping(uint => uint)[2] fixedMaps;
  FixedTriple triple; FixedTriple triple2;
  mapping(uint => mapping(uint => uint)) grid;
  mapping(uint => Ledger) ledgerMap;
  mapping(uint => uint)[] mapArray;
}

/-- `solc/SolcExpressions.sol`. -/
def SolcExpressions : Contract := contract!{ uint counter; }

/-- `solc/SolcStructs.sol`, less the `Flagged`/`Depth*` family. -/
def SolcStructs : Contract := contract!{
  Simple data1; WithArray withArray; Triple triple;
  uint neighbourBefore; uint neighbourAfter;
  Pair source; Pair target;
  Pair[] pairs1; Pair[] pairs2;
  mapping(uint => Simple) campaigns;
}

/-- `solc/SolcArrays.sol`. -/
def SolcArrays : Contract := contract!{
  uint[] storageArray; uint[][] matrix; Pair[] structs;
}

/-- `solc/SolcMemory.sol`. -/
def SolcMemory : Contract := contract!{
  Outer outerX; Inner innerS; Inner[] inners; uint[] prims;
}

/-- `solc/SolcMappings.sol`. -/
def SolcMappings : Contract := contract!{
  S sBox; WithSub withSub;
  mapping(uint => S) sMap;
  mapping(uint => WithSub) withSubMap;
  mapping(uint => uint) balances;
  mapping(uint => uint[]) arrayMap;
  uint[][] rows;
  Ledger ledger;
}

/-- Internal functions (`Examples/Tactics/Calls.lean`): a function may call the ones
declared before it. -/
def CallsExample : Contract := contract!{
  uint total; uint count;
  mapping(uint => uint) balances;
  function addOne(uint x) returns (uint r) { r = x + 1; }
  function double(uint x) returns (uint) { return x + x; }
  function addTwo(uint x) returns (uint r) { r = addOne(x); r = addOne(r); }
  function credit(uint a, uint v) { balances[a] += v; total += v; }
  function larger(uint a, uint b) returns (uint) { if (a > b) { return a; } else { return b; }; }
  function bump() { count++; }
}

/-- `solc/SolcControlFlow.sol`. -/
def SolcControlFlow : Contract := contract!{
  Pair sx; Pair sy; Pair target; uint[] values;
}



/-! ## Quoting

The elaborated block is turned back into a term by hand, because
`deriving ToExpr` cannot handle an indexed family whose constructors carry
proofs.  The contract is the constant it names, and every proof is spelt
`Eq.refl`, so the kernel re-checks each one by computing `rootType`,
`fieldType` or the Boolean check. -/

deriving instance Lean.ToExpr for PrimTy
deriving instance Lean.ToExpr for RefTy, Ty
deriving instance Lean.ToExpr for BinOp
deriving instance Lean.ToExpr for UnOp
deriving instance Lean.ToExpr for IncDec
deriving instance Lean.ToExpr for EnvKey

section Quote
open Lean (mkAppN mkConst toExpr)

/-- `a = a`. -/
def quoteRefl (α a : Lean.Expr) : Lean.Expr := mkAppN (mkConst ``Eq.refl [1]) #[α, a]

/-- `p = p`, at `PrimTy`. -/
def rflPrim (p : PrimTy) : Lean.Expr := quoteRefl (mkConst ``PrimTy) (toExpr p)

/-- `true = true`: every Boolean side condition. -/
def rflTrue : Lean.Expr := quoteRefl (mkConst ``Bool) (mkConst ``Bool.true)

/-- `some T = some T`: every contract lookup. -/
def rflSome (T : Ty) : Lean.Expr :=
  quoteRefl (mkAppN (mkConst ``Option [0]) #[mkConst ``Ty])
    (mkAppN (mkConst ``Option.some [0]) #[mkConst ``Ty, toExpr T])

def optE (α : Lean.Expr) : Option Lean.Expr → Lean.Expr
  | none => mkAppN (mkConst ``Option.none [0]) #[α]
  | some a => mkAppN (mkConst ``Option.some [0]) #[α, a]

def ArrTy.quote : {R : RefTy} → {E : Ty} → ArrTy R E → Lean.Expr
  | _, _, @ArrTy.dyn E => mkAppN (mkConst ``ArrTy.dyn) #[toExpr E]
  | _, _, @ArrTy.fixed E n => mkAppN (mkConst ``ArrTy.fixed) #[toExpr E, toExpr n]

def IndexTy.quote : {R : RefTy} → {k : PrimTy} → {V : Ty} → IndexTy R k V → Lean.Expr
  | _, _, _, @IndexTy.map k V => mkAppN (mkConst ``IndexTy.map) #[toExpr k, toExpr V]
  | _, _, _, @IndexTy.arr R E a => mkAppN (mkConst ``IndexTy.arr) #[toExpr R, toExpr E, ArrTy.quote a]

end Quote

end Solidity
