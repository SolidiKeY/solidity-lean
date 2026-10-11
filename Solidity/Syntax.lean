import Solidity.AST
import Solidity.SpecSyntax

/-!
# The typed syntax and its elaboration

A program is written against a **contract**, the storage roots it declares,
and every expression is indexed by its type: `Val C p` is a value of
primitive type `p`, `SPath C T` a storage path of type `T`, `Surface.Stmt C`
a statement (mini-solkey's `Ch02_Elab`).  A statement here is the syntax as
written (decision 11 of `docs/intrinsic.md`): the erasure of the scoped
statement (`Syntax/Scoped.lean`) that the elaborator emits
(`Syntax/Elab.lean`), for the readers not yet scoped, with no run, no taclet
and no `wt`.  A member access carries the proof
that the member exists, an operator the proof that it takes its operand
type, a copy the proof that its type holds no mapping.  So a statement no
rule can run cannot be written: `alice.balance = 1;` (no such member),
`alice = 1;` (a `uint` for a `Person`) and `wallet = wallet;` (a copy of a
mapping) are elaboration errors.

`Surface.Stmt` keeps locals as names (`Var`s, `AST.lean`) with no scope: a
stack local carries its `PrimTy`, an alias (`Person storage p`) and a
memory local (`Person memory m`) their reference type, all by the
constructor they are written with.  It is the printers' input; `resolve`
turns each name into a position of the scoped statement's context.

`sol[C]{ … }` reads Solidity statements, elaborates them against the
contract `C` (`Syntax/Elab.lean`), each local typed at its position, and
splices the result into the file as a term (`Syntax/Splice.lean`);
`sol{ … }` is the same against the file's `InContract` instance.  The elaborator is an
ordinary function run at compile time; its result is turned back into a
term with every proof `Eq.refl`, so the kernel re-checks each one: nothing
the elaborator computed is trusted.

Two spellings differ from Solidity's.  A decrement is `x−−`, `−−x` (two
U+2212 MINUS SIGN): `--` opens a comment in Lean, so it cannot appear in a
`sol{ … }` block, and `x -= 1` is another statement.  And a value has no
effects: an `++`/`−−` inside an expression, or a conditional whose branches
are references, is captured by the elaborator into a fresh local before its
statement (`hoist`), in the order solc evaluates the operands.  A statement
ending in a block (`if (c) { … }`, `unchecked { … }`) may leave out its `;`
(`solSemi`), and `else if` nests an `if` in the `else` branch.

`while`, `for`, `do … while`, `break` and `continue` are lowered to one
loop, `Surface.Stmt.loop`, solkey's lowered `while`, by solkey's `LoopLowering`
(`lowerLoops`): a jump sets a flag, and a `return` inside a loop too.  The
`/// @custom:key` lines above a loop are its annotation (`LoopAnn`), which
chooses the rule that proves it.

A contract declares its internal functions (`contract!{ function f(uint x)
returns (uint r) { … } }`), each calling only the ones declared before it.
A call (`f(a);`, `y = f(a);`, `uint y = f(a);`) is elaborated by inlining:
`Surface.Stmt.call` carries the callee's parameters bound to the arguments, its
return variable and the body, every local of the callee renamed fresh for
this call (`elabCall`), as KeY's `FunctionBodyStatement` carries the function
it stands for.  A call is a statement or a whole right-hand side, as KeY
writes it (`res = f(a)@C;`); one inside an expression is captured before its
statement.  A push used as a target, `values.push() = e;`, is the push
`values.push(e);`, as the front end normalises it.  A body's
`return e;` ends it: an assignment to the return variable, the statements
after it moved into the branches that do not return (`lowerReturns`).

A function may return a memory reference (`returns (Person memory p)`), and
its call is then KeY's expansion written out, with no return of its own
(`CallRet.none`): the callee's fresh return variable is declared at the head
of the body (`Person memory mv2;`, a fresh default object, as solc
allocates one on entry), and the statement after the call binds the
caller's local to its identity (`Person memory mv1 = mv2;`, `m = mv2;`,
KeY's `resultVar = freshReturn`).  The printers write the two statements as
the call they are (`Person memory mv1 = choosePersonMem();`), which reads
back to them.  A member of a call's value is a member of that capture
(`choosePersonMem().account = a;`).
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
  deriving Repr, Inhabited

/-- A loop's specification as read, solkey's `///` lines above the loop:
`/// @custom:key invariant e` (several conjoined), `/// @custom:key
decreases e` (at most one) and, Lean only, `/// @custom:key unwind k`, the
bound on unwinding (`LoopAnn`). -/
structure RawLoopSpec where
  inv : List RawExpr := []
  dec : Option RawExpr := none
  unwind : Option Nat := none
  deriving Repr, Inhabited

/-- The expressions of a loop's specification, as written. -/
def RawLoopSpec.exprs (a : RawLoopSpec) : List RawExpr := a.inv ++ a.dec.toList

inductive RawStmt where
  | assign (l r : RawExpr)
  | decl (T : RawTy) (x : String) (init : Option RawExpr)
  | declStorage (T : RawTy) (x : String) (init : Option RawExpr)
  | declMemory (T : RawTy) (x : String) (init : Option RawExpr)
  | delete (e : RawExpr)
  | opAssign (op : BinOp) (l r : RawExpr)
  | incDec (op : IncDec) (l : RawExpr)
  /-- `b.push()`, `b.push(a)`, `b.pop()`, `a.transfer(v)`. -/
  | call (f : RawExpr) (args : List RawExpr)
  | assignIncDec (x : RawExpr) (op : IncDec) (l : RawExpr)
  /-- `lsv = b.push();`, `T storage lsv = b.push();` -/
  | assignPush (l b : RawExpr)
  | declStoragePush (T : RawTy) (x : String) (b : RawExpr)
  | ite (c : RawExpr) (thn els : List RawStmt)
  | require (c : RawExpr)
  | assert (c : RawExpr)
  | revert
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
  /-- `try e.f(a) returns (T v) { … } catch …`: the receiver, the function,
  the arguments, the return locals, and the clauses normalised as
  `Stmt.tryCall`'s, with the name of the `Panic` code. -/
  | tryCall (recv : RawExpr) (f : String) (args : List RawExpr) (rets : List (RawTy × String))
      (ok err : List RawStmt) (code : Option String) (panic other : List RawStmt)
  /-- `x = r.send(a);`, and with `T` given the declaration `T x = r.send(a);`
  (`x` a name).  A bare `r.send(a);` is not read: solkey has no rule for it. -/
  | send (T : Option RawTy) (x r a : RawExpr)
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

/-- An internal function as the contract declares it: its parameters and
its return variables (`returns (uint r)`; unnamed, `returns (uint)`, it is
called `_ret`, and the `i`-th of several `_ret{i}`, solkey's `ret{i}`;
`returns (Account memory a)`, a memory reference), at their types, and its
body as read.  The elaborator types the body where the function is called
and inlines it there (`Stmt.call`). -/
structure FunDecl where
  params : List (Name × Ty)
  rets : List (Name × Ty) := []
  /-- A return variable is declared `memory`, as a reference one must be
  (only a function of one return may return a reference). -/
  retMem : Bool := false
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
  | `(ty!(mapping($K => $V))) => `(Ty.mapping ty!($K) ty!($V))
  | `(ty!($T[])) => `(Ty.array ty!($T))
  | `(ty!($T[$n])) => `(Ty.fixed ty!($T) $n)

/-! ## Expressions

The sorts of the schema variables are types here:

| sort | name | is |
|---|---|---|
| `Simple C p` | `se` | a literal or a stack local |
| `SPath C T` | `sp`, `nsp` | a storage path: an alias or a location |
| `Loc C T` | `gsp`, `sp.fld`, `sp[e]` | a state variable, a member, an entry |
| `Val C p` | `e`, `nse` | a value: simple, a read, an operator, a conditional |
| `MPath C T`, `MLoc C T` | `mv`, `nmp` | the same in memory, which has no roots |

`isSimple` tells `sp` from `nsp` and `se` from `nse`: which one a statement
has decides which rule runs, not which statements can be written. -/

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
  | map {k : PrimTy} {V : Ty} : IndexTy (.mapping (.prim k) V) k V
  | arr {R : RefTy} {E : Ty} (a : ArrTy R E) : IndexTy R .uint E

/-- A simple value (`se`): a literal, a stack local, or a value of the
environment (`msg.sender`), which solkey's `netHeader.key` declares as program
variables, so a `SimpleExpression` like a local. -/
inductive Surface.Simple (C : Contract) : PrimTy → Type where
  /-- A number of its type's range (`PrimTy.inRange`): solc rejects a literal
  out of it, so no program has one. -/
  | lit {p : PrimTy} (n : Int) (h : p.inRange n = true) : Surface.Simple C p
  | bool (b : Bool) : Surface.Simple C .bool
  | local {p : PrimTy} (x : Var) : Surface.Simple C p
  /-- `msg.sender`, `msg.value`, `block.timestamp`, `address(this).balance`:
  a `uint` (an `address` is one). -/
  | env {p : PrimTy} (k : EnvKey) (hp : p = .uint) : Surface.Simple C p

mutual

/-- A storage path of type `T`: an alias (`lsv`), or a location. -/
inductive Surface.SPath (C : Contract) : Ty → Type where
  | alias {R : RefTy} (x : Var) : Surface.SPath C (.ref R)
  | loc {T : Ty} (l : Surface.Loc C T) : Surface.SPath C T

/-- A storage location: what `delete` and a write reach through. -/
inductive Surface.Loc (C : Contract) : Ty → Type where
  /-- A state variable (`gsp`), `alice`. -/
  | root {T : Ty} (r : Name) (h : C.rootType r = some T) : Surface.Loc C T
  /-- A member, `alice.age`. -/
  | field {s : Name} {T : Ty} (b : Surface.SPath C (.struct s)) (f : Name)
      (h : C.fieldType s f = some T) : Surface.Loc C T
  /-- A mapping entry `balances[i]`, or an array element `values[i]`. -/
  | index {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (b : Surface.SPath C (.ref R))
      (i : Surface.Val C k) : Surface.Loc C V

/-- A memory path (`mv`, `nmp`): a memory local, or a memory location. -/
inductive Surface.MPath (C : Contract) : Ty → Type where
  /-- A memory local, of a type that holds no mapping (memory has none). -/
  | var {R : RefTy} (x : Var) (hm : (Ty.ref R).mapFree = true) : Surface.MPath C (.ref R)
  | loc {T : Ty} (l : Surface.MLoc C T) : Surface.MPath C T

/-- A member or an element of a memory object (memory has no mappings). -/
inductive Surface.MLoc (C : Contract) : Ty → Type where
  | field {s : Name} {T : Ty} (b : Surface.MPath C (.struct s)) (f : Name)
      (h : C.fieldType s f = some T) : Surface.MLoc C T
  | index {R : RefTy} {E : Ty} (a : ArrTy R E) (b : Surface.MPath C (.ref R)) (i : Surface.Val C .uint) : Surface.MLoc C E

/-- A value of primitive type `p`. -/
inductive Surface.Val (C : Contract) : PrimTy → Type where
  | simple {p : PrimTy} (s : Surface.Simple C p) : Surface.Val C p
  /-- A storage read, `alice.age`. -/
  | read {p : PrimTy} (l : Surface.Loc C (.prim p)) : Surface.Val C p
  /-- `a ⊕ b`, at the type `q` that `⊕` returns at `p`. -/
  | binop {p q : PrimTy} (op : BinOp) (h : op.accepts p = true) (hq : op.ret p = q)
      (a b : Surface.Val C p) : Surface.Val C q
  | unop {p q : PrimTy} (op : UnOp) (h : op.accepts p = true) (hq : op.ret p = q)
      (a : Surface.Val C p) : Surface.Val C q
  /-- `c ? a : b`, which evaluates only the branch it takes. -/
  | ternary {p : PrimTy} (c : Surface.Val C .bool) (a b : Surface.Val C p) : Surface.Val C p
  /-- A memory read, `m.age`. -/
  | readMem {p : PrimTy} (l : Surface.MLoc C (.prim p)) : Surface.Val C p
  /-- The length of a storage array, `values.length` (KeY's field `length`,
  `find(storage, sp.size)`). -/
  | len {p : PrimTy} {E : Ty} (b : Surface.SPath C (.array E)) (hp : p = .uint) : Surface.Val C p
  /-- The length of a memory array, `xs.length` (`read(memory, mv.size)`). -/
  | mlen {p : PrimTy} {E : Ty} (b : Surface.MPath C (.array E)) (hp : p = .uint) : Surface.Val C p

end

/-- The source of a storage write: a value, or a storage path copied (of a
type that holds no mapping; solc rejects the copy otherwise). -/
inductive Surface.Src (C : Contract) : Ty → Type where
  | val {p : PrimTy} (v : Surface.Val C p) : Surface.Src C (.prim p)
  | copy {R : RefTy} (p : Surface.SPath C (.ref R)) (h : (Ty.ref R).mapFree = true) : Surface.Src C (.ref R)

/-- What a storage alias is bound to: a path, or the slot `b.push()`
appends (whose default must be well-formed). -/
inductive Surface.ARhs (C : Contract) (R : RefTy) where
  | path (p : Surface.SPath C (.ref R))
  | push (b : Surface.SPath C (.array (.ref R))) (hd : (Ty.ref R).defaultOkS = true)

/-- `new R(n)` can be written: `R` is an array type whose elements a
memory object can hold (no mapping) and whose default is well-formed. -/
def RefTy.newArrOk : RefTy → Bool
  | .array E => E.mapFree && E.defaultOkS
  | _ => false

/-- What a memory local is bound to: a memory object by identity
(`m = n;`), a fresh deep copy of a storage object (`m = alice;`), or a fresh
array of `n` default elements (`m = new uint[](n);`, the size simple: the
elaborator captures another first). -/
inductive Surface.MRhs (C : Contract) (R : RefTy) where
  | alias (p : Surface.MPath C (.ref R))
  | copy (p : Surface.SPath C (.ref R)) (hm : (Ty.ref R).mapFree = true)
  | newArr (n : Surface.Simple C .uint) (h : R.newArrOk = true)

mutual
/-- What a memory path names holds no mapping: its local's type does not, and
a member or an element of a type that holds none holds none. -/
theorem Surface.MPath.mapFree {C : Contract} : {T : Ty} → Surface.MPath C T → T.mapFree = true
  | _, .var _ hm => hm
  | _, .loc l => l.mapFree
theorem Surface.MLoc.mapFree {C : Contract} : {T : Ty} → Surface.MLoc C T → T.mapFree = true
  | _, .field b _ h => Ty.mapFree_field b.mapFree h
  | _, .index .dyn b _ => b.mapFree
  | _, .index .fixed b _ => b.mapFree
end

/-- What a memory local is bound to holds no mapping. -/
theorem Surface.MRhs.mapFree {C : Contract} {R : RefTy} : Surface.MRhs C R → (Ty.ref R).mapFree = true
  | .alias p => p.mapFree
  | .copy _ hm => hm
  | .newArr _ h => by
    cases R <;> simp only [RefTy.newArrOk, Bool.and_eq_true, Bool.false_eq_true] at h
    exact h.1

/-- Where a fresh array lands when it is not bound to a memory local
(KeY's `newArrayCapture`, `Path[complex] lhs`): a storage location
(`basket.items = new uint[](2);`) or a memory one (`xs[0] = new uint[](3);`). -/
inductive Surface.NewLhs (C : Contract) : RefTy → Type where
  | store {R : RefTy} (l : Surface.Loc C (.ref R)) : Surface.NewLhs C R
  | mem {R : RefTy} (l : Surface.MLoc C (.ref R)) : Surface.NewLhs C R

/-- What a memory location is written: a value, or a memory reference. -/
inductive Surface.MSrc (C : Contract) : Ty → Type where
  | val {p : PrimTy} (v : Surface.Val C p) : Surface.MSrc C (.prim p)
  | ref {R : RefTy} (p : Surface.MPath C (.ref R)) : Surface.MSrc C (.ref R)

/-- The target of `l ⊕= e` and `l++`: a local, a state variable, a member,
or an entry at a simple index. -/
inductive Surface.OpLoc (C : Contract) : PrimTy → Type where
  | local {p : PrimTy} (x : Var) : Surface.OpLoc C p
  | root {p : PrimTy} (r : Name) (h : C.rootType r = some (.prim p)) : Surface.OpLoc C p
  | field {s : Name} {p : PrimTy} (b : Surface.SPath C (.struct s)) (f : Name)
      (h : C.fieldType s f = some (.prim p)) : Surface.OpLoc C p
  | index {R : RefTy} {k p : PrimTy} (it : IndexTy R k (.prim p)) (b : Surface.SPath C (.ref R))
      (i : Surface.Simple C k) : Surface.OpLoc C p
  | mfield {s : Name} {p : PrimTy} (b : Surface.MPath C (.struct s)) (f : Name)
      (h : C.fieldType s f = some (.prim p)) : Surface.OpLoc C p
  | mindex {R : RefTy} {p : PrimTy} (a : ArrTy R (.prim p)) (b : Surface.MPath C (.ref R))
      (i : Surface.Simple C .uint) : Surface.OpLoc C p

/-! ### Which parts are simple -/

/-- `se`: a literal or a local. -/
def Surface.Val.isSimple {C : Contract} {p : PrimTy} : Surface.Val C p → Bool
  | .simple _ => true
  | _ => false

/-- `sp`: an alias or a state variable. -/
def Surface.SPath.isSimple {C : Contract} {T : Ty} : Surface.SPath C T → Bool
  | .alias _ => true
  | .loc (.root ..) => true
  | .loc _ => false

/-- `mv`: a memory local. -/
def Surface.MPath.isSimple {C : Contract} {T : Ty} : Surface.MPath C T → Bool
  | .var .. => true
  | .loc _ => false

mutual
/-- A memory path that indexes nothing: a local and its members, which a
read cannot revert on (memory has no null and no mapping). -/
def Surface.MPath.indexFree {C : Contract} : {T : Ty} → Surface.MPath C T → Bool
  | _, .var .. => true
  | _, .loc l => l.indexFree
def Surface.MLoc.indexFree {C : Contract} : {T : Ty} → Surface.MLoc C T → Bool
  | _, .field b _ _ => b.indexFree
  | _, .index .. => false
end

/-- A target whose receiver, if it has one, is simple: `x`, `total`,
`sp.fld`, `sp[ie]`, `mv.fld`, `mv[ie]`. -/
def Surface.OpLoc.recvSimple {C : Contract} {p : PrimTy} : Surface.OpLoc C p → Bool
  | .field b _ _ | .index _ b _ => b.isSimple
  | .mfield b _ _ | .mindex _ b _ => b.isSimple
  | _ => true

/-- `v`, if it is simple. -/
def Surface.Val.toSimple? {C : Contract} {p : PrimTy} : Surface.Val C p → Option (Surface.Simple C p)
  | .simple s => some s
  | _ => none

/-! ### The locals a part mentions -/

section Vars
variable {C : Contract}

def Surface.Simple.vars {p : PrimTy} : Surface.Simple C p → List Var
  | .local x => [x]
  | .lit .. | .bool _ | .env .. => []

mutual

def Surface.SPath.vars : {T : Ty} → Surface.SPath C T → List Var
  | _, .alias x => [x]
  | _, .loc l => l.vars

def Surface.Loc.vars : {T : Ty} → Surface.Loc C T → List Var
  | _, .root .. => []
  | _, .field b _ _ => b.vars
  | _, .index _ b i => b.vars ++ i.vars

def Surface.MPath.vars : {T : Ty} → Surface.MPath C T → List Var
  | _, .var x _ => [x]
  | _, .loc l => l.vars

def Surface.MLoc.vars : {T : Ty} → Surface.MLoc C T → List Var
  | _, .field b _ _ => b.vars
  | _, .index _ b i => b.vars ++ i.vars

def Surface.Val.vars : {p : PrimTy} → Surface.Val C p → List Var
  | _, .simple s => s.vars
  | _, .read l => l.vars
  | _, .binop _ _ _ a b => a.vars ++ b.vars
  | _, .unop _ _ _ a => a.vars
  | _, .ternary c a b => c.vars ++ a.vars ++ b.vars
  | _, .readMem l => l.vars
  | _, .len b _ => b.vars
  | _, .mlen b _ => b.vars

end

end Vars

/-! ## Calls

A call carries its callee inlined, as KeY's `FunctionBodyStatement` carries
the function it stands for: the parameters with the arguments bound to them,
the return variable and where its value lands, and the body.  Every local of
the callee is a name the elaborator made fresh for this call, so running the
body in the caller's locals is running it in a frame of its own. -/

/-- An argument: the value `e` passed for the parameter `x` of type `p`. -/
structure Arg (C : Contract) where
  p : PrimTy
  x : Var
  e : Surface.Val C p

/-- What a call returns: nothing, or the value of its return variable `r` of
type `p` (declared at the call, KeY's fresh named return), which lands in the
caller's local `res` when the call is assigned (`y = f(a);`).  A memory
reference is returned through the caller's locals, with `none`: the body
declares the return variable, and the statement after the call binds it
(the module docstring).  A function of several returns returns them all
with `rets`, KeyTaclets' `FunctionBodyStatement` with targets: each return
variable is declared at the call, at its type's default (solc's), and the
targets are ordinary statements after the call (`t = r;`), solkey's
`R r0; …; function-frame{…} t0 = r0;` without the frame.  `rets` is the
call of a tuple assignment (`(lo, hi) = f(a);`) and of a specification's
obligation (`result = f(x);`), the two KeY reads as a
`FunctionBodyStatement` (`functionBodyExpand`); every other call is KeY's
`InternalCall` (`internalCallExpand`), a callee of several returns called as
a statement declaring them in its body. -/
inductive Surface.CallRet where
  | none
  | val (p : PrimTy) (r : Var) (res : Option Var)
  | rets (rs : List (PrimTy × Var))
  deriving DecidableEq, Repr, Inhabited

/-- The arguments of a call are **separated**: no argument that is not
simple reads a parameter bound before it.  Inlined, the parameters are bound
one after another (KeY's `expand_function_body`), and an argument captured
before the call (`functionCallArgCapture`) is read before any of them; the
two agree on a separated call.  The elaborator's parameters are fresh, so its
calls are. -/
def Arg.separatedFrom {C : Contract} : List Var → List (Arg C) → Bool
  | _, [] => true
  | bound, a :: as =>
    (a.e.isSimple || a.e.vars.all fun y => !bound.contains y) && Arg.separatedFrom (a.x :: bound) as

/-- An argument of an external call, at its type. -/
abbrev Surface.ExtArg (C : Contract) := (p : PrimTy) × Surface.Simple C p

/-- `a.f(e₁, …, eₙ)`, a call of the function `f` of the contract at the
address `a`: solkey's `ExternalCall`, whose receiver and arguments cannot
revert or have an effect.  Here they are simple, `sol{ … }` capturing any
other first; a contract conversion `I(a)` elaborates away to `a`. -/
structure Surface.ExtCall (C : Contract) where
  addr : Surface.Simple C .uint
  fn : Name
  args : List (Surface.ExtArg C)

/-- What a loop is proved by (`docs/loops.md`, Decision 3), chosen by the
source, so that a loop has one rule: unwound at most `k` times (Lean only:
solkey's strategy unwinds without a bound), or by its invariant `I` and,
under the diamond, its variant `dec` (solkey's `/// @custom:key invariant`
and `decreases`).  The typed run does not read it. -/
inductive Surface.LoopAnn (C : Contract) where
  | unwind (k : Nat)
  | inv (I : Surface.Val C .bool) (dec : Option (Surface.Val C .uint))

/-! ## Statements -/

/-- A statement of contract `C`, as written. -/
inductive Surface.Stmt (C : Contract) where
  /-- A storage write, `alice.age = 10;`, `alice = bob;`, `sp.age = 1;`. -/
  | assign {T : Ty} (l : Loc C T) (r : Src C T)
  /-- `lsv = sp;`, `lsv = sp.push();`: the alias now points there. -/
  | rebind {R : RefTy} (x : Var) (r : ARhs C R)
  /-- `v = e;` -/
  | assignLocal {p : PrimTy} (x : Var) (r : Val C p)
  /-- `uint v = e;`, `uint v;` -/
  | declLocal (p : PrimTy) (x : Var) (init : Option (Val C p))
  /-- `Person storage lsv = sp;`, `Person storage lsv;` -/
  | declStorage (R : RefTy) (x : Var) (init : Option (ARhs C R))
  /-- `l += e;`: `+= -= *= /= %=` (solkey's five), at a numeric type. -/
  | opAssign {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
      (hp : p.isNumeric = true) (l : OpLoc C p) (r : Val C p)
  /-- `x++;`, `--alice.age;` -/
  | incDec {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C p)
  /-- `v = x++;`, from a target whose receiver is simple (`sol{ … }` captures
  another first; no taclet takes one). -/
  | assignIncDec {p : PrimTy} (x : Var) (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C p)
      (hs : l.recvSimple = true)
  /-- `values.push(x);`, `persons.push(alice);`, `values.push();` (the last
  needs the element type's default to be well-formed). -/
  | push {E : Ty} (b : SPath C (.array E)) (v : Option (Src C E))
      (hd : (v.isSome || E.defaultOkS) = true)
  /-- `values.pop();` -/
  | pop {E : Ty} (b : SPath C (.array E))
  /-- `a.transfer(v);` -/
  | transfer (r a : Val C .uint)
  /-- `pv = a.send(v);`: the payment, and whether it went through in the
  `bool` local `pv` (a refused send returns `false` and reverts nothing). -/
  | send (pv : Var) (r a : Val C .uint)
  /-- `Person memory m;` (a fresh default object), `Person memory m = n;` -/
  | declMem (R : RefTy) (x : Var) (init : Option (MRhs C R))
      (hd : (init.isSome || (Ty.ref R).defaultOkS) = true) (hm : (Ty.ref R).mapFree = true)
  /-- `m = n;`: the memory local now names `n`'s object. -/
  | rebindMem {R : RefTy} (x : Var) (r : MRhs C R)
  /-- `alice = m;`: a storage location written with a deep copy of a memory
  object. -/
  | assignFromMem {R : RefTy} (l : Loc C (.ref R)) (p : MPath C (.ref R))
  /-- `m.age = 3;`, `m.account = n.account;` -/
  | assignMem {T : Ty} (l : MLoc C T) (r : MSrc C T)
  /-- `delete alice.account;` -/
  | delete {T : Ty} (l : Loc C T)
  /-- `delete m;`, `delete m.age;`, `delete m.items[i];`: a memory local
  bound to a fresh default object, a member or an element reset (a
  reference one to a fresh default object, as solc and KeY allocate one). -/
  | deleteMem {T : Ty} (p : MPath C T) (hd : T.defaultOkS = true)
  /-- `basket.items = new uint[](n);`, `xs[0] = new uint[](n);`: a fresh
  array written to a location that is not a memory local. -/
  | assignNew {R : RefTy} (l : NewLhs C R) (n : Simple C .uint) (h : R.newArrOk = true)
  /-- `if (c) { … } else { … }` -/
  | ite (c : Val C .bool) (thn els : List (Surface.Stmt C))
  /-- `require(c);` -/
  | require (c : Val C .bool)
  /-- `assert(c);` -/
  | assert (c : Val C .bool)
  /-- `revert();` -/
  | revert
  /-- `f(e₁, …, eₙ);`, `y = f(e₁, …, eₙ);`: an internal call of `f`, its
  arguments bound to its parameters, its body inlined (see `Arg`). -/
  | call (f : Name) (args : List (Arg C)) (hsep : Arg.separatedFrom [] args = true) (ret : CallRet)
      (body : List (Surface.Stmt C))
  /-- `try a.f(e) returns (uint v) { ok } catch Error(string memory) { err }
  catch Panic(uint c) { panic } catch { other }`: an external call, and a
  block per way it may end.  As solkey's `TryStatement.of` normalises it,
  every clause is present: a missing `Error` or `Panic` clause is the
  catch-all's block, a missing catch-all `revert();`.  `rets` are the locals
  the call's return data binds in `ok`, `code` the `Panic` code's in `panic`;
  an `Error`'s message and a catch-all's data are not modelled. -/
  | tryCall (call : ExtCall C) (rets : List (PrimTy × Var)) (ok err : List (Surface.Stmt C))
      (code : Option Var) (panic other : List (Surface.Stmt C))
  /-- `while (c) { … }`, solkey's lowered `while`: `for`, `do … while`,
  `break`, `continue` and a `return` inside a loop are lowered to it by the
  elaborator (`lowerLoops`), so its body ends only normally or by halting. -/
  | loop (a : LoopAnn C) (c : Val C .bool) (body : List (Surface.Stmt C))

/-- A block. -/
abbrev Surface.Prog (C : Contract) := List (Surface.Stmt C)

/-- The locals the `Panic` code binds: `code`, a `uint`, if the clause names it. -/
def codeBinders (code : Option Var) : List (PrimTy × Var) :=
  code.toList.map fun x => (.uint, x)

/-- `T x = e;`: a parameter bound to its argument. -/
def Arg.decl {C : Contract} (a : Arg C) : Surface.Stmt C := .declLocal a.p a.x (some a.e)

/-- `T r;`: the return variable declared, at its default. -/
def Surface.CallRet.decl {C : Contract} : Surface.CallRet → Surface.Prog C
  | .none => []
  | .val p r _ => [.declLocal p r Option.none]
  | .rets rs => rs.map fun (p, r) => .declLocal p r Option.none

/-- `res = r;`: the returned value assigned where the call is. -/
def Surface.CallRet.result {C : Contract} : Surface.CallRet → Surface.Prog C
  | .val p r (some res) => [.assignLocal (p := p) res (.simple (.local r))]
  | _ => []

/-- A call inlined, KeY's `expand_function_body`: the parameters declared
with the arguments, the return variable declared, the body, the result
assigned.  `y = f(a);`, `f` being `function f(uint x) returns (uint r)
{ r = x + 1; }`, is `uint x' = a; uint r'; r' = x' + 1; y = r';`. -/
def Surface.Stmt.expandBody {C : Contract} (args : List (Arg C)) (ret : Surface.CallRet) (body : Surface.Prog C) : Surface.Prog C :=
  args.map Arg.decl ++ ret.decl ++ body ++ ret.result

/-! ## Printing

`Prog.toStr` writes a block back as the Solidity it came from, which
`sol{ … }` reads again.  An operator application is parenthesised unless it
is the whole expression. -/

section Print

variable {C : Contract} [FreshNames]

def Surface.Simple.toStr {p : PrimTy} : Surface.Simple C p → String
  | .lit n _ => toString n
  | .bool b => toString b
  | .local x => toString x
  | .env k _ => k.toStr

mutual

def Surface.SPath.toStr {T : Ty} : Surface.SPath C T → String
  | .alias x => toString x
  | .loc l => l.toStr

def Surface.Loc.toStr {T : Ty} : Surface.Loc C T → String
  | .root r _ => r
  | .field b f _ => s!"{b.toStr}.{f}"
  | .index _ b i => s!"{b.toStr}[{i.toStr true}]"

def Surface.MPath.toStr {T : Ty} : Surface.MPath C T → String
  | .var x _ => toString x
  | .loc l => l.toStr

def Surface.MLoc.toStr {T : Ty} : Surface.MLoc C T → String
  | .field b f _ => s!"{b.toStr}.{f}"
  | .index _ b i => s!"{b.toStr}[{i.toStr true}]"

/-- `top` is whether the value stands alone, so needs no parentheses. -/
def Surface.Val.toStr {p : PrimTy} : Surface.Val C p → (top : Bool := false) → String
  | .simple s, _ => s.toStr
  | .read l, _ => l.toStr
  | .binop op _ _ a b, top =>
    let s := s!"{a.toStr} {BinOp.sym op} {b.toStr}"
    if top then s else s!"({s})"
  | .unop op _ _ a, _ => s!"{UnOp.sym op}{a.toStr}"
  | .ternary c a b, top =>
    let s := s!"{c.toStr} ? {a.toStr} : {b.toStr}"
    if top then s else s!"({s})"
  | .readMem l, _ => l.toStr
  | .len b _, _ => s!"{b.toStr}.length"
  | .mlen b _, _ => s!"{b.toStr}.length"

end

def Surface.Src.toStr {T : Ty} : Surface.Src C T → String
  | .val v => v.toStr true
  | .copy p _ => p.toStr

def Surface.ARhs.toStr {R : RefTy} : Surface.ARhs C R → String
  | .path p => p.toStr
  | .push b _ => s!"{b.toStr}.push()"

def Surface.OpLoc.toStr {p : PrimTy} : Surface.OpLoc C p → String
  | .local x => toString x
  | .root r _ => r
  | .field b f _ => s!"{b.toStr}.{f}"
  | .index _ b i => s!"{b.toStr}[{i.toStr}]"
  | .mfield b f _ => s!"{b.toStr}.{f}"
  | .mindex _ b i => s!"{b.toStr}[{i.toStr}]"

def Surface.MRhs.toStr {R : RefTy} : Surface.MRhs C R → String
  | .alias p => p.toStr
  | .copy p _ => p.toStr
  | .newArr n _ => s!"new {Ty.toStr (.ref R)}({n.toStr})"

def Surface.NewLhs.toStr {R : RefTy} : Surface.NewLhs C R → String
  | .store l => l.toStr
  | .mem l => l.toStr

def Surface.MSrc.toStr {T : Ty} : Surface.MSrc C T → String
  | .val v => v.toStr true
  | .ref p => p.toStr

/-- `x++`, `−−x`: a decrement is spelled with two minus signs `−` (U+2212),
since `--` opens a comment in Lean (`Syntax.lean`, the grammar). -/
def IncDec.show (op : IncDec) (x : String) : String :=
  let t := if op.isIncrement then "++" else "−−"
  if op.isPre then t ++ x else x ++ t

/-- A call of a function returning a memory reference and the statement
after it that binds its fresh return variable, the one the body declares
first: `Person memory mv1 = choosePersonMem();`, `m = choosePersonMem();`,
the statement they are elaborated from. -/
def Surface.Stmt.memCallStr? : Surface.Stmt C → Surface.Stmt C → Option String
  | .call f args _ .none (.declMem _ r none _ _ :: _), .declMem R x (some (.alias (.var r' _))) _ _ =>
    if r' = r then
      some s!"{Ty.toStr (.ref R)} memory {x} = {f}({", ".intercalate (args.map fun a => a.e.toStr true)});"
    else none
  | .call f args _ .none (.declMem _ r none _ _ :: _), .rebindMem x (.alias (.var r' _)) =>
    if r' = r then some s!"{x} = {f}({", ".intercalate (args.map fun a => a.e.toStr true)});"
    else none
  | _, _ => none

/-- The target a statement after a call of several returns assigns one of
them to (`lo = se2;`): the return's position among `rs`, and the target. -/
def Surface.Stmt.retTarget? (rs : List (PrimTy × Var)) : Surface.Stmt C → Option (Nat × String)
  | .assignLocal x (.simple (.local r)) => (rs.findIdx? (·.2 == r)).map (·, toString x)
  | .assign l (.val (.simple (.local r))) => (rs.findIdx? (·.2 == r)).map (·, l.toStr)
  | .assignMem l (.val (.simple (.local r))) => (rs.findIdx? (·.2 == r)).map (·, l.toStr)
  | _ => none

/-- The statements after a call of several returns that assign them, in
their order, from the `start`-th return on. -/
def Surface.Stmt.retTargets (rs : List (PrimTy × Var)) (start : Nat) : List (Surface.Stmt C) → List (Nat × String)
  | [] => []
  | s :: P =>
    match s.retTarget? rs with
    | some (i, t) => if start ≤ i then (i, t) :: Surface.Stmt.retTargets rs (i + 1) P else []
    | none => []

/-- A call of several returns and the statements after it that assign them,
written as the tuple assignment they are elaborated from:
`(lo, , sum) = returnStats(3, 1, 2);`, with the number of statements after
the call it covers.  A call of one return with its target (a specification's
obligation, `Calculus/SurfaceSpec.lean`) is `result = f(x);`. -/
def Surface.Stmt.tupleCallStr? : Surface.Stmt C → List (Surface.Stmt C) → Option (String × Nat)
  | .call f args _ (.rets rs) _, P =>
    let ts := Surface.Stmt.retTargets rs 0 P
    let call := s!"{f}({", ".intercalate (args.map fun a => a.e.toStr true)});"
    if ts.isEmpty then
      -- every value discarded: `(, ) = f(x);`, a call with targets still
      if rs.length < 2 then none
      else some (s!"({String.mk (List.replicate (rs.length - 1) ',')}) = {call}", 0)
    else if rs.length == 1 then some (s!"{((ts.head?).map (·.2)).getD ""} = {call}", ts.length)
    else
      let slots := (List.range rs.length).map fun i => ((ts.find? (·.1 == i)).map (·.2)).getD ""
      some (s!"({", ".intercalate slots}) = {call}", ts.length)
  | _, _ => none

/-- A loop's annotation, as the `///` lines above it: none for `.unwind 0`. -/
def Surface.LoopAnn.toStr : Surface.LoopAnn C → String
  | .unwind 0 => ""
  | .unwind k => s!"/// @custom:key unwind {k} "
  | .inv I dec =>
    s!"/// @custom:key invariant {I.toStr true} " ++
      ((dec.map fun d => s!"/// @custom:key decreases {d.toStr true} ").getD "")

/-- A block's statements in braces: `{ x = 1; }`, and `{ }` for none. -/
def braced (ss : List String) : String :=
  if ss.isEmpty then "{ }" else s!"\{ {" ".intercalate ss} }"

mutual

def Surface.Stmt.toStr : Surface.Stmt C → String
  | .assign l r => s!"{l.toStr} = {r.toStr};"
  | .rebind x r => s!"{x} = {r.toStr};"
  | .assignLocal x r => s!"{x} = {r.toStr true};"
  | .declLocal p x init =>
    match init with
    | none => s!"{Ty.toStr (.prim p)} {x};"
    | some e => s!"{Ty.toStr (.prim p)} {x} = {e.toStr true};"
  | .declStorage R x init =>
    match init with
    | none => s!"{Ty.toStr (.ref R)} storage {x};"
    | some e => s!"{Ty.toStr (.ref R)} storage {x} = {e.toStr};"
  | .declMem R x init _ _ =>
    match init with
    | none => s!"{Ty.toStr (.ref R)} memory {x};"
    | some r => s!"{Ty.toStr (.ref R)} memory {x} = {r.toStr};"
  | .rebindMem x r => s!"{x} = {r.toStr};"
  | .assignMem l r => s!"{l.toStr} = {r.toStr};"
  | .assignFromMem l p => s!"{l.toStr} = {p.toStr};"
  | .opAssign op _ _ l r => s!"{l.toStr} {BinOp.sym op}= {r.toStr true};"
  | .incDec op _ l => s!"{IncDec.show op l.toStr};"
  | .push b v _ =>
    match v with
    | none => s!"{b.toStr}.push();"
    | some r => s!"{b.toStr}.push({r.toStr});"
  | .pop b => s!"{b.toStr}.pop();"
  | .transfer r a => s!"{r.toStr}.transfer({a.toStr true});"
  | .send pv r a => s!"{pv} = {r.toStr}.send({a.toStr true});"
  | .assignIncDec x op _ l _ => s!"{x} = {IncDec.show op l.toStr};"
  | .delete l => s!"delete {l.toStr};"
  | .deleteMem p _ => s!"delete {p.toStr};"
  | .assignNew (R := R) l n _ => s!"{l.toStr} = new {Ty.toStr (.ref R)}({n.toStr});"
  | .ite c thn els =>
    s!"if ({c.toStr true}) {braced (Surface.Prog.toStrs 0 thn)} else {braced (Surface.Prog.toStrs 0 els)}"
  | .require c => s!"require({c.toStr true});"
  | .assert c => s!"assert({c.toStr true});"
  | .revert => "revert();"
  | .call f args _ ret _ =>
    let call := s!"{f}({", ".intercalate (args.map fun a => a.e.toStr true)});"
    match ret with
    | .val _ _ (some y) => s!"{y} = {call}"
    | _ => call
  | .tryCall c rets ok err code pnc other =>
    let args := ", ".intercalate (c.args.map fun a => a.2.toStr)
    let rets := if rets.isEmpty then "" else
      s!" returns ({", ".intercalate (rets.map fun (p, x) => s!"{Ty.toStr (.prim p)} {x}")})"
    let code := match code with
      | some x => s!"uint {x}"
      | none => "uint"
    s!"try address({c.addr.toStr}).{c.fn}({args}){rets} {braced (Surface.Prog.toStrs 0 ok)} \
      catch Error(string memory) {braced (Surface.Prog.toStrs 0 err)} \
      catch Panic({code}) {braced (Surface.Prog.toStrs 0 pnc)} \
      catch {braced (Surface.Prog.toStrs 0 other)}"
  | .loop a c body => s!"{a.toStr}while ({c.toStr true}) {braced (Surface.Prog.toStrs 0 body)}"

/-- The statements of a block, one string each; a memory call and the
statement binding its result are one (`Stmt.memCallStr?`), and so are a call
of several returns and the statements assigning them (`Stmt.tupleCallStr?`),
the statements after the first skipped (`skip` of them). -/
def Surface.Prog.toStrs (skip : Nat) : List (Surface.Stmt C) → List String
  | [] => []
  | s :: P =>
    match skip with
    | k + 1 => Surface.Prog.toStrs k P
    | 0 =>
      match Surface.Stmt.tupleCallStr? s P with
      | some (c, k) => c :: Surface.Prog.toStrs k P
      | none =>
      match P with
      | t :: _ =>
        match Surface.Stmt.memCallStr? s t with
        | some c => c :: Surface.Prog.toStrs 1 P
        | none => s.toStr :: Surface.Prog.toStrs 0 P
      | [] => [s.toStr]

end

/-- A block, as the Solidity it came from. -/
def Surface.Prog.toStr (P : List (Surface.Stmt C)) : String := " ".intercalate (Surface.Prog.toStrs 0 P)

/-- One statement per line, for display. -/
def Surface.Prog.show (P : List (Surface.Stmt C)) : String :=
  "\n".intercalate (Surface.Prog.toStrs 0 P)

end Print

/-! ## Surface syntax -/

declare_syntax_cat sol_expr (behavior := both)
syntax:max num : sol_expr
syntax:max ident : sol_expr
syntax:max sol_expr:max "." ident : sol_expr
syntax:max sol_expr:max "[" sol_expr "]" : sol_expr
syntax:max "(" sol_expr ")" : sol_expr
/-- `(a, b)`: a tuple, the right-hand side of a tuple assignment or of a
`return` of several values (`RawExpr.tuple`). -/
syntax:max (name := solTupleExpr) "(" sol_expr ", " sol_expr,+ ")" : sol_expr
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
syntax sol_expr ".pop()" : sol_stmt
syntax sol_expr " = " sol_expr ".push()" : sol_stmt
/-- `values .push() = e;`, `a[i].push() = e;`: a push used as a target spelt
with the `.push()` token; on a name or a member chain it is the push
`b.push(e);`, on another receiver refused (`expandStmt.pushTarget`). -/
syntax (name := solPushTarget) sol_expr ".push()" " = " sol_expr : sol_stmt
syntax sol_ty &"storage" ident " = " sol_expr ".push()" : sol_stmt
syntax sol_expr ".transfer(" sol_expr ")" : sol_stmt
syntax sol_expr " = " sol_expr ".send(" sol_expr ")" : sol_stmt
syntax sol_ty ident " = " sol_expr ".send(" sol_expr ")" : sol_stmt
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
syntax "if " "(" sol_expr ") " sol_block (" else " sol_block)? : sol_stmt
/-- `if (c) { … } else if (d) { … } else { … }`: the `if`s nested. -/
syntax (name := solIfChain) "if " "(" sol_expr ") " sol_block
  (atomic(" else " "if ") "(" sol_expr ") " sol_block)+ (" else " sol_block)? : sol_stmt
syntax (name := solRequire) &"require" "(" sol_expr ")" : sol_stmt
syntax (name := solAssert) &"assert" "(" sol_expr ")" : sol_stmt
syntax (name := solRevert) &"revert" "(" ")" : sol_stmt
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
syntax (name := solLoopSpec) sol_loop_clause ppSpace sol_stmt : sol_stmt
/-! `try e.f(a) returns (uint v) { … } catch Error(string memory m) { … }
catch Panic(uint c) { … } catch (bytes memory d) { … } catch { … }`: an
external call.  A clause's parameter is `sol_tparam`: a type, `memory` for
`string`/`bytes`, an optional name. -/
declare_syntax_cat sol_tparam (behavior := both)
syntax sol_ty (ppSpace &"memory")? (ppSpace ident)? : sol_tparam
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

partial def expandExpr (e : TSyntax `sol_expr) : MacroM Term := do
  if e.raw.isOfKind ``solTupleExpr then
    let es := #[e.raw[1]] ++ e.raw[3].getSepArgs
    return ← `(RawExpr.tuple [$(← es.mapM (expandExpr ⟨·⟩)),*])
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
      fieldChain (← expandCall f as.getElems callMsg) (nameParts g.getId)
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
    while cur.getKind == ``solLoopSpec do
      let cl := cur[0]
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
    expandStmt.loop ⟨cur⟩ (← `({ inv := [$inv,*], dec := $decT, unwind := $unwT : RawLoopSpec }))
  | ``solPushTarget =>
    expandStmt.pushTarget s ⟨s.raw[0]⟩ (← expandExpr ⟨s.raw[0]⟩) (← expandExpr ⟨s.raw[3]⟩)
  | ``solUnchecked => `(RawStmt.unchecked $(← expandStmt.expandBlock ⟨s.raw[1]⟩))
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
      `(RawStmt.declStoragePush $(← expandTy T) $(strLit x) $(← pushRecv f))
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
      `(RawStmt.send none $(← expandExpr l) $(← expandExpr r) $(← expandExpr a))
  | `(sol_stmt| $T:sol_ty $x:ident = $r:sol_expr .send( $a:sol_expr )) => do
      `(RawStmt.send (some $(← expandTy T)) (.name $(strLit x)) $(← expandExpr r)
        $(← expandExpr a))
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
    some <$> `(RawStmt.send $T $l $r $(← expandExpr a))
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

/-- A function's attribute: its return variables, `returns (uint r)`,
`returns (Person memory p)`, `returns (uint lo, uint hi)`; a visibility or a
mutability (dropped); or a modifier applied, `onlyOwner`,
`inState(State.Created)`. -/
declare_syntax_cat sol_fattr (behavior := both)
syntax (name := solAttrReturns) &"returns" "(" sol_tparam,+ ")" : sol_fattr
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
    MacroM (Array Term × Array Term) := do
  let mut rows := #[]
  let mut ws := #[]
  for p in ps do
    let `(sol_param| $T:sol_ty $x:ident) := p | Macro.throwUnsupported
    let (t, w) ← expandMemberTyW enums T
    rows := rows.push (← `(($(strLit x), $t)))
    if let some n := w then ws := ws.push (← `(($(strLit x), $(quote n))))
  pure (rows, ws)

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
  let (ps, ws) ← expandParamsW enums ps
  let mut ws := ws
  -- `payable` is an atom of the keyword reading and an identifier of the
  -- modifier reading
  let payable := attrs.any fun a => (a.raw.find? fun s =>
    s.isAtom && s.getAtomVal == "payable" || s.isIdent && s.getId == `payable).isSome
  let mut rets : Array Term := #[]
  let mut retMem := false
  let mut apps : Array Term := #[]
  for a in attrs do
    -- `returns (uint)` also reads as a modifier `returns` applied to `uint`,
    -- and `view` as a modifier `view`: take the other reading
    let a := preferReading a.raw (!·.isOfKind ``solAttrMod)
    if a.isOfKind ``solAttrKw then continue
    if a.isOfKind ``solAttrReturns then
      -- `returns ( T memory? r?, … )`: unnamed, `_ret`, or `_ret0`, `_ret1`, …
      let ps := a[2].getSepArgs
      for i in [0:ps.size] do
        -- `T memory` also reads as `T` named `memory`: take the location
        let p := preferReading ps[i]! (!·[1].isNone)
        let n := (p[2].getOptional?.map (·.getId.toString)).getD
          (if ps.size == 1 then "_ret" else s!"_ret{i}")
        let (t, w) ← expandMemberTyW enums ⟨p[0]⟩
        if let some b := w then ws := ws.push (← `(($(quote n), $(quote b))))
        rets := rets.push (← `(($(quote n), $t)))
        retMem := retMem || !p[1].isNone
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
    ({ params := [$ps,*], rets := [$rets,*], retMem := $(quote retMem), body := $body,
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

variable {C : Contract} (c : Lean.Expr)

def Surface.Simple.quote : (p : PrimTy) → Surface.Simple C p → Lean.Expr
  | p, .lit n _ => mkAppN (mkConst ``Surface.Simple.lit) #[c, toExpr p, toExpr n, rflTrue]
  | _, .bool b => mkAppN (mkConst ``Surface.Simple.bool) #[c, toExpr b]
  | p, .local x => mkAppN (mkConst ``Surface.Simple.local) #[c, toExpr p, toExpr x]
  | p, .env k _ => mkAppN (mkConst ``Surface.Simple.env) #[c, toExpr p, toExpr k,
      rflPrim p]

mutual

def Surface.SPath.quote : (T : Ty) → Surface.SPath C T → Lean.Expr
  | .ref R, .alias x => mkAppN (mkConst ``Surface.SPath.alias) #[c, toExpr R, toExpr x]
  | T, .loc l => mkAppN (mkConst ``Surface.SPath.loc) #[c, toExpr T, Surface.Loc.quote T l]

def Surface.Loc.quote : (T : Ty) → Surface.Loc C T → Lean.Expr
  | T, .root r _ => mkAppN (mkConst ``Surface.Loc.root) #[c, toExpr T, toExpr r, rflSome T]
  | T, @Surface.Loc.field _ s _ b f _ =>
    mkAppN (mkConst ``Surface.Loc.field) #[c, toExpr s, toExpr T, Surface.SPath.quote _ b, toExpr f, rflSome T]
  | V, @Surface.Loc.index _ R k _ it b i =>
    mkAppN (mkConst ``Surface.Loc.index) #[c, toExpr R, toExpr k, toExpr V, IndexTy.quote it,
      Surface.SPath.quote _ b, Surface.Val.quote k i]

def Surface.MPath.quote : (T : Ty) → Surface.MPath C T → Lean.Expr
  | .ref R, .var x _ => mkAppN (mkConst ``Surface.MPath.var) #[c, toExpr R, toExpr x, rflTrue]
  | T, .loc l => mkAppN (mkConst ``Surface.MPath.loc) #[c, toExpr T, Surface.MLoc.quote T l]

def Surface.MLoc.quote : (T : Ty) → Surface.MLoc C T → Lean.Expr
  | T, @Surface.MLoc.field _ s _ b f _ =>
    mkAppN (mkConst ``Surface.MLoc.field) #[c, toExpr s, toExpr T, Surface.MPath.quote _ b, toExpr f, rflSome T]
  | E, @Surface.MLoc.index _ R _ a b i =>
    mkAppN (mkConst ``Surface.MLoc.index) #[c, toExpr R, toExpr E, ArrTy.quote a, Surface.MPath.quote _ b,
      Surface.Val.quote .uint i]

def Surface.Val.quote : (p : PrimTy) → Surface.Val C p → Lean.Expr
  | p, .simple s => mkAppN (mkConst ``Surface.Val.simple) #[c, toExpr p, Surface.Simple.quote c p s]
  | p, .read l => mkAppN (mkConst ``Surface.Val.read) #[c, toExpr p, Surface.Loc.quote _ l]
  | _, @Surface.Val.binop _ p q op _ _ a b =>
    mkAppN (mkConst ``Surface.Val.binop) #[c, toExpr p, toExpr q, toExpr op, rflTrue,
      rflPrim q, Surface.Val.quote p a, Surface.Val.quote p b]
  | _, @Surface.Val.unop _ p q op _ _ a =>
    mkAppN (mkConst ``Surface.Val.unop) #[c, toExpr p, toExpr q, toExpr op, rflTrue,
      rflPrim q, Surface.Val.quote p a]
  | p, .ternary cv a b =>
    mkAppN (mkConst ``Surface.Val.ternary) #[c, toExpr p, Surface.Val.quote .bool cv, Surface.Val.quote p a, Surface.Val.quote p b]
  | p, .readMem l => mkAppN (mkConst ``Surface.Val.readMem) #[c, toExpr p, Surface.MLoc.quote _ l]
  | p, @Surface.Val.len _ _ E b _ => mkAppN (mkConst ``Surface.Val.len) #[c, toExpr p, toExpr E, Surface.SPath.quote _ b,
      rflPrim p]
  | p, @Surface.Val.mlen _ _ E b _ => mkAppN (mkConst ``Surface.Val.mlen) #[c, toExpr p, toExpr E, Surface.MPath.quote _ b,
      rflPrim p]

end

def Surface.Src.quote : (T : Ty) → Surface.Src C T → Lean.Expr
  | _, @Surface.Src.val _ p v => mkAppN (mkConst ``Surface.Src.val) #[c, toExpr p, Surface.Val.quote c p v]
  | _, @Surface.Src.copy _ R p _ => mkAppN (mkConst ``Surface.Src.copy) #[c, toExpr R, Surface.SPath.quote c _ p, rflTrue]

def Surface.ARhs.quote (R : RefTy) : Surface.ARhs C R → Lean.Expr
  | .path p => mkAppN (mkConst ``Surface.ARhs.path) #[c, toExpr R, Surface.SPath.quote c _ p]
  | .push b _ => mkAppN (mkConst ``Surface.ARhs.push) #[c, toExpr R, Surface.SPath.quote c _ b, rflTrue]

def Surface.MRhs.quote (R : RefTy) : Surface.MRhs C R → Lean.Expr
  | .alias p => mkAppN (mkConst ``Surface.MRhs.alias) #[c, toExpr R, Surface.MPath.quote c _ p]
  | .copy p _ => mkAppN (mkConst ``Surface.MRhs.copy) #[c, toExpr R, Surface.SPath.quote c _ p, rflTrue]
  | .newArr n _ => mkAppN (mkConst ``Surface.MRhs.newArr) #[c, toExpr R, Surface.Simple.quote c .uint n, rflTrue]

def Surface.NewLhs.quote : (R : RefTy) → Surface.NewLhs C R → Lean.Expr
  | R, .store l => mkAppN (mkConst ``Surface.NewLhs.store) #[c, toExpr R, Surface.Loc.quote c _ l]
  | R, .mem l => mkAppN (mkConst ``Surface.NewLhs.mem) #[c, toExpr R, Surface.MLoc.quote c _ l]

def Surface.MSrc.quote : (T : Ty) → Surface.MSrc C T → Lean.Expr
  | _, @Surface.MSrc.val _ p v => mkAppN (mkConst ``Surface.MSrc.val) #[c, toExpr p, Surface.Val.quote c p v]
  | _, @Surface.MSrc.ref _ R p => mkAppN (mkConst ``Surface.MSrc.ref) #[c, toExpr R, Surface.MPath.quote c _ p]

def Surface.OpLoc.quote : (p : PrimTy) → Surface.OpLoc C p → Lean.Expr
  | p, .local x => mkAppN (mkConst ``Surface.OpLoc.local) #[c, toExpr p, toExpr x]
  | p, .root r _ => mkAppN (mkConst ``Surface.OpLoc.root) #[c, toExpr p, toExpr r, rflSome (.prim p)]
  | p, @Surface.OpLoc.field _ s _ b f _ =>
    mkAppN (mkConst ``Surface.OpLoc.field) #[c, toExpr s, toExpr p, Surface.SPath.quote c _ b, toExpr f,
      rflSome (.prim p)]
  | p, @Surface.OpLoc.index _ R k _ it b i =>
    mkAppN (mkConst ``Surface.OpLoc.index) #[c, toExpr R, toExpr k, toExpr p, IndexTy.quote it,
      Surface.SPath.quote c _ b, Surface.Simple.quote c k i]
  | p, @Surface.OpLoc.mfield _ s _ b f _ =>
    mkAppN (mkConst ``Surface.OpLoc.mfield) #[c, toExpr s, toExpr p, Surface.MPath.quote c _ b, toExpr f,
      rflSome (.prim p)]
  | p, @Surface.OpLoc.mindex _ R _ a b i =>
    mkAppN (mkConst ``Surface.OpLoc.mindex) #[c, toExpr R, toExpr p, ArrTy.quote a, Surface.MPath.quote c _ b,
      Surface.Simple.quote c .uint i]

def Arg.quoteList : List (Arg C) → Lean.Expr
  | [] => mkAppN (mkConst ``List.nil [0]) #[mkAppN (mkConst ``Arg) #[c]]
  | a :: as => mkAppN (mkConst ``List.cons [0]) #[mkAppN (mkConst ``Arg) #[c],
      mkAppN (mkConst ``Arg.mk) #[c, toExpr a.p, toExpr a.x, Surface.Val.quote c a.p a.e], Arg.quoteList as]

def Surface.CallRet.quote : Surface.CallRet → Lean.Expr
  | .none => mkConst ``Surface.CallRet.none
  | .val p r res => mkAppN (mkConst ``Surface.CallRet.val) #[toExpr p, toExpr r, toExpr res]
  | .rets rs => mkAppN (mkConst ``Surface.CallRet.rets) #[toExpr rs]

/-- An external call, each argument a `Sigma.mk` of its type and value. -/
def Surface.ExtCall.quote (call : Surface.ExtCall C) : Lean.Expr :=
  let argTy := mkAppN (mkConst ``Surface.ExtArg) #[c]
  let args := call.args.foldr (fun a acc => mkAppN (mkConst ``List.cons [0]) #[argTy,
      mkAppN (mkConst ``Sigma.mk [0, 0]) #[mkConst ``PrimTy, mkAppN (mkConst ``Surface.Simple) #[c], toExpr a.1,
        Surface.Simple.quote c a.1 a.2], acc])
    (mkAppN (mkConst ``List.nil [0]) #[argTy])
  mkAppN (mkConst ``Surface.ExtCall.mk) #[c, Surface.Simple.quote c .uint call.addr, toExpr call.fn, args]

def Surface.LoopAnn.quote : Surface.LoopAnn C → Lean.Expr
  | .unwind k => mkAppN (mkConst ``Surface.LoopAnn.unwind) #[c, toExpr k]
  | .inv I dec =>
    mkAppN (mkConst ``Surface.LoopAnn.inv) #[c, Surface.Val.quote c .bool I,
      optE (mkAppN (mkConst ``Surface.Val) #[c, toExpr PrimTy.uint]) (dec.map (Surface.Val.quote c .uint))]

mutual

def Surface.Stmt.quote : Surface.Stmt C → Lean.Expr
  | @Surface.Stmt.assign _ T l r => mkAppN (mkConst ``Surface.Stmt.assign) #[c, toExpr T, Surface.Loc.quote c T l, Surface.Src.quote c T r]
  | @Surface.Stmt.rebind _ R x r => mkAppN (mkConst ``Surface.Stmt.rebind) #[c, toExpr R, toExpr x, Surface.ARhs.quote c R r]
  | @Surface.Stmt.assignLocal _ p x r =>
    mkAppN (mkConst ``Surface.Stmt.assignLocal) #[c, toExpr p, toExpr x, Surface.Val.quote c p r]
  | .declLocal p x init =>
    mkAppN (mkConst ``Surface.Stmt.declLocal) #[c, toExpr p, toExpr x,
      optE (mkAppN (mkConst ``Surface.Val) #[c, toExpr p]) (init.map (Surface.Val.quote c p))]
  | .declStorage R x init =>
    mkAppN (mkConst ``Surface.Stmt.declStorage) #[c, toExpr R, toExpr x,
      optE (mkAppN (mkConst ``Surface.ARhs) #[c, toExpr R]) (init.map (Surface.ARhs.quote c R))]
  | @Surface.Stmt.opAssign _ p op _ _ l r =>
    mkAppN (mkConst ``Surface.Stmt.opAssign) #[c, toExpr p, toExpr op, rflTrue, rflTrue,
      Surface.OpLoc.quote c p l, Surface.Val.quote c p r]
  | @Surface.Stmt.incDec _ p op _ l =>
    mkAppN (mkConst ``Surface.Stmt.incDec) #[c, toExpr p, toExpr op, rflTrue, Surface.OpLoc.quote c p l]
  | @Surface.Stmt.assignIncDec _ p x op _ l _ =>
    mkAppN (mkConst ``Surface.Stmt.assignIncDec) #[c, toExpr p, toExpr x, toExpr op, rflTrue,
      Surface.OpLoc.quote c p l, rflTrue]
  | @Surface.Stmt.push _ E b v _ =>
    mkAppN (mkConst ``Surface.Stmt.push) #[c, toExpr E, Surface.SPath.quote c _ b,
      optE (mkAppN (mkConst ``Surface.Src) #[c, toExpr E]) (v.map (Surface.Src.quote c E)), rflTrue]
  | @Surface.Stmt.pop _ E b => mkAppN (mkConst ``Surface.Stmt.pop) #[c, toExpr E, Surface.SPath.quote c _ b]
  | .transfer r a => mkAppN (mkConst ``Surface.Stmt.transfer) #[c, Surface.Val.quote c .uint r, Surface.Val.quote c .uint a]
  | .send pv r a =>
    mkAppN (mkConst ``Surface.Stmt.send) #[c, toExpr pv, Surface.Val.quote c .uint r, Surface.Val.quote c .uint a]
  | .declMem R x init _ _ =>
    mkAppN (mkConst ``Surface.Stmt.declMem) #[c, toExpr R, toExpr x,
      optE (mkAppN (mkConst ``Surface.MRhs) #[c, toExpr R]) (init.map (Surface.MRhs.quote c R)), rflTrue, rflTrue]
  | @Surface.Stmt.rebindMem _ R x r => mkAppN (mkConst ``Surface.Stmt.rebindMem) #[c, toExpr R, toExpr x, Surface.MRhs.quote c R r]
  | @Surface.Stmt.assignFromMem _ R l p =>
    mkAppN (mkConst ``Surface.Stmt.assignFromMem) #[c, toExpr R, Surface.Loc.quote c _ l, Surface.MPath.quote c _ p]
  | @Surface.Stmt.assignMem _ T l r => mkAppN (mkConst ``Surface.Stmt.assignMem) #[c, toExpr T, Surface.MLoc.quote c T l, Surface.MSrc.quote c T r]
  | @Surface.Stmt.delete _ T l => mkAppN (mkConst ``Surface.Stmt.delete) #[c, toExpr T, Surface.Loc.quote c T l]
  | @Surface.Stmt.deleteMem _ T p _ =>
    mkAppN (mkConst ``Surface.Stmt.deleteMem) #[c, toExpr T, Surface.MPath.quote c T p, rflTrue]
  | @Surface.Stmt.assignNew _ R l n _ =>
    mkAppN (mkConst ``Surface.Stmt.assignNew) #[c, toExpr R, Surface.NewLhs.quote c R l, Surface.Simple.quote c .uint n,
      rflTrue]
  | .ite cond thn els =>
    mkAppN (mkConst ``Surface.Stmt.ite) #[c, Surface.Val.quote c .bool cond, Surface.Prog.quote thn, Surface.Prog.quote els]
  | .require cond => mkAppN (mkConst ``Surface.Stmt.require) #[c, Surface.Val.quote c .bool cond]
  | .assert cond => mkAppN (mkConst ``Surface.Stmt.assert) #[c, Surface.Val.quote c .bool cond]
  | .revert => mkAppN (mkConst ``Surface.Stmt.revert) #[c]
  | .call f args _ ret body =>
    mkAppN (mkConst ``Surface.Stmt.call)
      #[c, toExpr f, Arg.quoteList c args, rflTrue, Surface.CallRet.quote ret, Surface.Prog.quote body]
  | .tryCall call rets ok err code pnc other =>
    mkAppN (mkConst ``Surface.Stmt.tryCall)
      #[c, Surface.ExtCall.quote c call, toExpr rets, Surface.Prog.quote ok, Surface.Prog.quote err, toExpr code,
        Surface.Prog.quote pnc, Surface.Prog.quote other]
  | .loop a cond body =>
    mkAppN (mkConst ``Surface.Stmt.loop) #[c, Surface.LoopAnn.quote c a, Surface.Val.quote c .bool cond, Surface.Prog.quote body]

def Surface.Prog.quote : List (Surface.Stmt C) → Lean.Expr
  | [] => mkAppN (mkConst ``List.nil [0]) #[mkAppN (mkConst ``Surface.Stmt) #[c]]
  | s :: P => mkAppN (mkConst ``List.cons [0]) #[mkAppN (mkConst ``Surface.Stmt) #[c], Surface.Stmt.quote s, Surface.Prog.quote P]

end

end Quote

end Solidity
