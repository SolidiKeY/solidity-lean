import Solidity.AST
import Solidity.SpecSyntax

/-!
# The typed syntax and its elaboration

A program is written against a **contract**, the storage roots it declares,
and every expression is indexed by its type: `Val C p` is a value of
primitive type `p`, `SPath C T` a storage path of type `T`, `Stmt C` a
statement (mini-solkey's `Ch02_Elab`).  A member access carries the proof
that the member exists, an operator the proof that it takes its operand
type, a copy the proof that its type holds no mapping.  So a statement no
rule can run cannot be written: `alice.balance = 1;` (no such member),
`alice = 1;` (a `uint` for a `Person`) and `wallet = wallet;` (a copy of a
mapping) are elaboration errors, not stuck runs.

Locals are `Var`s (`AST.lean`), and the syntax does not track which are in
scope: a stack local carries its `PrimTy`, an alias (`Person storage p`) and
a memory local (`Person memory m`) their reference type, all by the
constructor they are written with.  That is what lets a rule declare fresh
variables (`se1`, `sp1`) without re-typing the rest of the program.

`sol[C]{ … }` reads Solidity statements, elaborates them against the
contract `C`, and splices the result into the file as a term; `sol{ … }` is
the same against the file's `InContract` instance.  The elaborator is an
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
loop, `Stmt.loop`, solkey's lowered `while`, by solkey's `LoopLowering`
(`lowerLoops`): a jump sets a flag, and a `return` inside a loop too.  The
`/// @custom:key` lines above a loop are its annotation (`LoopAnn`), which
chooses the rule that proves it.

A contract declares its internal functions (`contract!{ function f(uint x)
returns (uint r) { … } }`), each calling only the ones declared before it.
A call (`f(a);`, `y = f(a);`, `uint y = f(a);`) is elaborated by inlining:
`Stmt.call` carries the callee's parameters bound to the arguments, its
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
  the members' order by `hoist`, then read as the positional `T(a, b)`. -/
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
  /-- Its `requires`/`ensures` clauses, as read (`Calculus/Spec.lean`). -/
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
        else if (structDef s).isEmpty then Lean.Macro.throwErrorAt x (unknownTyMsg s)
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
inductive Simple (C : Contract) : PrimTy → Type where
  | lit {p : PrimTy} (n : Int) (h : p.isNumeric = true) : Simple C p
  | bool (b : Bool) : Simple C .bool
  | local {p : PrimTy} (x : Var) : Simple C p
  /-- `msg.sender`, `msg.value`, `block.timestamp`, `address(this).balance`:
  a `uint` (an `address` is one). -/
  | env {p : PrimTy} (k : EnvKey) (hp : p = .uint) : Simple C p

mutual

/-- A storage path of type `T`: an alias (`lsv`), or a location. -/
inductive SPath (C : Contract) : Ty → Type where
  | alias {R : RefTy} (x : Var) : SPath C (.ref R)
  | loc {T : Ty} (l : Loc C T) : SPath C T

/-- A storage location: what `delete` and a write reach through. -/
inductive Loc (C : Contract) : Ty → Type where
  /-- A state variable (`gsp`), `alice`. -/
  | root {T : Ty} (r : Name) (h : C.rootType r = some T) : Loc C T
  /-- A member, `alice.age`. -/
  | field {s : Name} {T : Ty} (b : SPath C (.struct s)) (f : Name)
      (h : C.fieldType s f = some T) : Loc C T
  /-- A mapping entry `balances[i]`, or an array element `values[i]`. -/
  | index {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (b : SPath C (.ref R))
      (i : Val C k) : Loc C V

/-- A memory path (`mv`, `nmp`): a memory local, or a memory location. -/
inductive MPath (C : Contract) : Ty → Type where
  | var {R : RefTy} (x : Var) : MPath C (.ref R)
  | loc {T : Ty} (l : MLoc C T) : MPath C T

/-- A member or an element of a memory object (memory has no mappings). -/
inductive MLoc (C : Contract) : Ty → Type where
  | field {s : Name} {T : Ty} (b : MPath C (.struct s)) (f : Name)
      (h : C.fieldType s f = some T) : MLoc C T
  | index {R : RefTy} {E : Ty} (a : ArrTy R E) (b : MPath C (.ref R)) (i : Val C .uint) : MLoc C E

/-- A value of primitive type `p`. -/
inductive Val (C : Contract) : PrimTy → Type where
  | simple {p : PrimTy} (s : Simple C p) : Val C p
  /-- A storage read, `alice.age`. -/
  | read {p : PrimTy} (l : Loc C (.prim p)) : Val C p
  /-- `a ⊕ b`, at the type `q` that `⊕` returns at `p`. -/
  | binop {p q : PrimTy} (op : BinOp) (h : op.accepts p = true) (hq : op.ret p = q)
      (a b : Val C p) : Val C q
  | unop {p q : PrimTy} (op : UnOp) (h : op.accepts p = true) (hq : op.ret p = q)
      (a : Val C p) : Val C q
  /-- `c ? a : b`, which evaluates only the branch it takes. -/
  | ternary {p : PrimTy} (c : Val C .bool) (a b : Val C p) : Val C p
  /-- A memory read, `m.age`. -/
  | readMem {p : PrimTy} (l : MLoc C (.prim p)) : Val C p
  /-- The length of a storage array, `values.length` (KeY's field `length`,
  `find(storage, sp.size)`). -/
  | len {p : PrimTy} {E : Ty} (b : SPath C (.array E)) (hp : p = .uint) : Val C p
  /-- The length of a memory array, `xs.length` (`read(memory, mv.size)`). -/
  | mlen {p : PrimTy} {E : Ty} (b : MPath C (.array E)) (hp : p = .uint) : Val C p

end

/-- The source of a storage write: a value, or a storage path copied (of a
type that holds no mapping; solc rejects the copy otherwise). -/
inductive Src (C : Contract) : Ty → Type where
  | val {p : PrimTy} (v : Val C p) : Src C (.prim p)
  | copy {R : RefTy} (p : SPath C (.ref R)) (h : (Ty.ref R).mapFree = true) : Src C (.ref R)

/-- What a storage alias is bound to: a path, or the slot `b.push()`
appends (whose default must be well-formed). -/
inductive ARhs (C : Contract) (R : RefTy) where
  | path (p : SPath C (.ref R))
  | push (b : SPath C (.array (.ref R))) (hd : (Ty.ref R).defaultOkS = true)

/-- `new R(n)` can be written: `R` is an array type whose elements a
memory object can hold (no mapping) and whose default is well-formed. -/
def RefTy.newArrOk : RefTy → Bool
  | .array E => E.mapFree && E.defaultOkS
  | _ => false

/-- What a memory local is bound to: a memory object by identity
(`m = n;`), a fresh deep copy of a storage object (`m = alice;`), or a fresh
array of `n` default elements (`m = new uint[](n);`, the size simple: the
elaborator captures another first). -/
inductive MRhs (C : Contract) (R : RefTy) where
  | alias (p : MPath C (.ref R))
  | copy (p : SPath C (.ref R)) (hm : (Ty.ref R).mapFree = true)
  | newArr (n : Simple C .uint) (h : R.newArrOk = true)

/-- Where a fresh array lands when it is not bound to a memory local
(KeY's `newArrayCapture`, `Path[complex] lhs`): a storage location
(`basket.items = new uint[](2);`) or a memory one (`xs[0] = new uint[](3);`). -/
inductive NewLhs (C : Contract) : RefTy → Type where
  | store {R : RefTy} (l : Loc C (.ref R)) : NewLhs C R
  | mem {R : RefTy} (l : MLoc C (.ref R)) : NewLhs C R

/-- What a memory location is written: a value, or a memory reference. -/
inductive MSrc (C : Contract) : Ty → Type where
  | val {p : PrimTy} (v : Val C p) : MSrc C (.prim p)
  | ref {R : RefTy} (p : MPath C (.ref R)) : MSrc C (.ref R)

/-- The target of `l ⊕= e` and `l++`: a local, a state variable, a member,
or an entry at a simple index. -/
inductive OpLoc (C : Contract) : PrimTy → Type where
  | local {p : PrimTy} (x : Var) : OpLoc C p
  | root {p : PrimTy} (r : Name) (h : C.rootType r = some (.prim p)) : OpLoc C p
  | field {s : Name} {p : PrimTy} (b : SPath C (.struct s)) (f : Name)
      (h : C.fieldType s f = some (.prim p)) : OpLoc C p
  | index {R : RefTy} {k p : PrimTy} (it : IndexTy R k (.prim p)) (b : SPath C (.ref R))
      (i : Simple C k) : OpLoc C p
  | mfield {s : Name} {p : PrimTy} (b : MPath C (.struct s)) (f : Name)
      (h : C.fieldType s f = some (.prim p)) : OpLoc C p
  | mindex {R : RefTy} {p : PrimTy} (a : ArrTy R (.prim p)) (b : MPath C (.ref R))
      (i : Simple C .uint) : OpLoc C p

/-! ### Which parts are simple -/

/-- `se`: a literal or a local. -/
def Val.isSimple {C : Contract} {p : PrimTy} : Val C p → Bool
  | .simple _ => true
  | _ => false

/-- `sp`: an alias or a state variable. -/
def SPath.isSimple {C : Contract} {T : Ty} : SPath C T → Bool
  | .alias _ => true
  | .loc (.root ..) => true
  | .loc _ => false

/-- `mv`: a memory local. -/
def MPath.isSimple {C : Contract} {T : Ty} : MPath C T → Bool
  | .var _ => true
  | .loc _ => false

/-- A target whose receiver, if it has one, is simple: `x`, `total`,
`sp.fld`, `sp[ie]`, `mv.fld`, `mv[ie]`. -/
def OpLoc.recvSimple {C : Contract} {p : PrimTy} : OpLoc C p → Bool
  | .field b _ _ | .index _ b _ => b.isSimple
  | .mfield b _ _ | .mindex _ b _ => b.isSimple
  | _ => true

/-- `v`, if it is simple. -/
def Val.toSimple? {C : Contract} {p : PrimTy} : Val C p → Option (Simple C p)
  | .simple s => some s
  | _ => none

/-! ### The locals a part mentions -/

section Vars
variable {C : Contract}

def Simple.vars {p : PrimTy} : Simple C p → List Var
  | .local x => [x]
  | .lit .. | .bool _ | .env .. => []

mutual

def SPath.vars : {T : Ty} → SPath C T → List Var
  | _, .alias x => [x]
  | _, .loc l => l.vars

def Loc.vars : {T : Ty} → Loc C T → List Var
  | _, .root .. => []
  | _, .field b _ _ => b.vars
  | _, .index _ b i => b.vars ++ i.vars

def MPath.vars : {T : Ty} → MPath C T → List Var
  | _, .var x => [x]
  | _, .loc l => l.vars

def MLoc.vars : {T : Ty} → MLoc C T → List Var
  | _, .field b _ _ => b.vars
  | _, .index _ b i => b.vars ++ i.vars

def Val.vars : {p : PrimTy} → Val C p → List Var
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
  e : Val C p

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
inductive CallRet where
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
abbrev ExtArg (C : Contract) := (p : PrimTy) × Simple C p

/-- `a.f(e₁, …, eₙ)`, a call of the function `f` of the contract at the
address `a`: solkey's `ExternalCall`, whose receiver and arguments cannot
revert or have an effect.  Here they are simple, `sol{ … }` capturing any
other first; a contract conversion `I(a)` elaborates away to `a`. -/
structure ExtCall (C : Contract) where
  addr : Simple C .uint
  fn : Name
  args : List (ExtArg C)

/-- What a loop is proved by (`docs/loops.md`, Decision 3), chosen by the
source, so that a loop has one rule: unwound at most `k` times (Lean only:
solkey's strategy unwinds without a bound), or by its invariant `I` and,
under the diamond, its variant `dec` (solkey's `/// @custom:key invariant`
and `decreases`).  `Stmt.run` does not read it. -/
inductive LoopAnn (C : Contract) where
  | unwind (k : Nat)
  | inv (I : Val C .bool) (dec : Option (Val C .uint))

/-! ## Statements -/

/-- A statement of contract `C`. -/
inductive Stmt (C : Contract) where
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
      (hd : (init.isSome || (Ty.ref R).defaultOkS) = true)
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
  | ite (c : Val C .bool) (thn els : List (Stmt C))
  /-- `require(c);` -/
  | require (c : Val C .bool)
  /-- `assert(c);` -/
  | assert (c : Val C .bool)
  /-- `revert();` -/
  | revert
  /-- `f(e₁, …, eₙ);`, `y = f(e₁, …, eₙ);`: an internal call of `f`, its
  arguments bound to its parameters, its body inlined (see `Arg`). -/
  | call (f : Name) (args : List (Arg C)) (hsep : Arg.separatedFrom [] args = true) (ret : CallRet)
      (body : List (Stmt C))
  /-- `try a.f(e) returns (uint v) { ok } catch Error(string memory) { err }
  catch Panic(uint c) { panic } catch { other }`: an external call, and a
  block per way it may end.  As solkey's `TryStatement.of` normalises it,
  every clause is present: a missing `Error` or `Panic` clause is the
  catch-all's block, a missing catch-all `revert();`.  `rets` are the locals
  the call's return data binds in `ok`, `code` the `Panic` code's in `panic`;
  an `Error`'s message and a catch-all's data are not modelled. -/
  | tryCall (call : ExtCall C) (rets : List (PrimTy × Var)) (ok err : List (Stmt C))
      (code : Option Var) (panic other : List (Stmt C))
  /-- `while (c) { … }`, solkey's lowered `while`: `for`, `do … while`,
  `break`, `continue` and a `return` inside a loop are lowered to it by the
  elaborator (`lowerLoops`), so its body ends only normally or by halting. -/
  | loop (a : LoopAnn C) (c : Val C .bool) (body : List (Stmt C))

/-- A block. -/
abbrev Prog (C : Contract) := List (Stmt C)

/-- The locals the `Panic` code binds: `code`, a `uint`, if the clause names it. -/
def codeBinders (code : Option Var) : List (PrimTy × Var) :=
  code.toList.map fun x => (.uint, x)

/-- `T x = e;`: a parameter bound to its argument. -/
def Arg.decl {C : Contract} (a : Arg C) : Stmt C := .declLocal a.p a.x (some a.e)

/-- `T r;`: the return variable declared, at its default. -/
def CallRet.decl {C : Contract} : CallRet → Prog C
  | .none => []
  | .val p r _ => [.declLocal p r Option.none]
  | .rets rs => rs.map fun (p, r) => .declLocal p r Option.none

/-- `res = r;`: the returned value assigned where the call is. -/
def CallRet.result {C : Contract} : CallRet → Prog C
  | .val p r (some res) => [.assignLocal (p := p) res (.simple (.local r))]
  | _ => []

/-- A call inlined, KeY's `expand_function_body`: the parameters declared
with the arguments, the return variable declared, the body, the result
assigned.  `y = f(a);`, `f` being `function f(uint x) returns (uint r)
{ r = x + 1; }`, is `uint x' = a; uint r'; r' = x' + 1; y = r';`. -/
def Stmt.expandBody {C : Contract} (args : List (Arg C)) (ret : CallRet) (body : Prog C) : Prog C :=
  args.map Arg.decl ++ ret.decl ++ body ++ ret.result

/-! ## Printing

`Prog.toStr` writes a block back as the Solidity it came from, which
`sol{ … }` reads again.  An operator application is parenthesised unless it
is the whole expression. -/

section Print

variable {C : Contract} [FreshNames]

def Simple.toStr {p : PrimTy} : Simple C p → String
  | .lit n _ => toString n
  | .bool b => toString b
  | .local x => toString x
  | .env k _ => k.toStr

mutual

def SPath.toStr {T : Ty} : SPath C T → String
  | .alias x => toString x
  | .loc l => l.toStr

def Loc.toStr {T : Ty} : Loc C T → String
  | .root r _ => r
  | .field b f _ => s!"{b.toStr}.{f}"
  | .index _ b i => s!"{b.toStr}[{i.toStr true}]"

def MPath.toStr {T : Ty} : MPath C T → String
  | .var x => toString x
  | .loc l => l.toStr

def MLoc.toStr {T : Ty} : MLoc C T → String
  | .field b f _ => s!"{b.toStr}.{f}"
  | .index _ b i => s!"{b.toStr}[{i.toStr true}]"

/-- `top` is whether the value stands alone, so needs no parentheses. -/
def Val.toStr {p : PrimTy} : Val C p → (top : Bool := false) → String
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

def Src.toStr {T : Ty} : Src C T → String
  | .val v => v.toStr true
  | .copy p _ => p.toStr

def ARhs.toStr {R : RefTy} : ARhs C R → String
  | .path p => p.toStr
  | .push b _ => s!"{b.toStr}.push()"

def OpLoc.toStr {p : PrimTy} : OpLoc C p → String
  | .local x => toString x
  | .root r _ => r
  | .field b f _ => s!"{b.toStr}.{f}"
  | .index _ b i => s!"{b.toStr}[{i.toStr}]"
  | .mfield b f _ => s!"{b.toStr}.{f}"
  | .mindex _ b i => s!"{b.toStr}[{i.toStr}]"

def MRhs.toStr {R : RefTy} : MRhs C R → String
  | .alias p => p.toStr
  | .copy p _ => p.toStr
  | .newArr n _ => s!"new {Ty.toStr (.ref R)}({n.toStr})"

def NewLhs.toStr {R : RefTy} : NewLhs C R → String
  | .store l => l.toStr
  | .mem l => l.toStr

def MSrc.toStr {T : Ty} : MSrc C T → String
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
def Stmt.memCallStr? : Stmt C → Stmt C → Option String
  | .call f args _ .none (.declMem _ r none _ :: _), .declMem R x (some (.alias (.var r'))) _ =>
    if r' = r then
      some s!"{Ty.toStr (.ref R)} memory {x} = {f}({", ".intercalate (args.map fun a => a.e.toStr true)});"
    else none
  | .call f args _ .none (.declMem _ r none _ :: _), .rebindMem x (.alias (.var r')) =>
    if r' = r then some s!"{x} = {f}({", ".intercalate (args.map fun a => a.e.toStr true)});"
    else none
  | _, _ => none

/-- The target a statement after a call of several returns assigns one of
them to (`lo = se2;`): the return's position among `rs`, and the target. -/
def Stmt.retTarget? (rs : List (PrimTy × Var)) : Stmt C → Option (Nat × String)
  | .assignLocal x (.simple (.local r)) => (rs.findIdx? (·.2 == r)).map (·, toString x)
  | .assign l (.val (.simple (.local r))) => (rs.findIdx? (·.2 == r)).map (·, l.toStr)
  | .assignMem l (.val (.simple (.local r))) => (rs.findIdx? (·.2 == r)).map (·, l.toStr)
  | _ => none

/-- The statements after a call of several returns that assign them, in
their order, from the `start`-th return on. -/
def Stmt.retTargets (rs : List (PrimTy × Var)) (start : Nat) : List (Stmt C) → List (Nat × String)
  | [] => []
  | s :: P =>
    match s.retTarget? rs with
    | some (i, t) => if start ≤ i then (i, t) :: Stmt.retTargets rs (i + 1) P else []
    | none => []

/-- A call of several returns and the statements after it that assign them,
written as the tuple assignment they are elaborated from:
`(lo, , sum) = returnStats(3, 1, 2);`, with the number of statements after
the call it covers.  A call of one return with its target (a specification's
obligation, `Calculus/Spec.lean`) is `result = f(x);`. -/
def Stmt.tupleCallStr? : Stmt C → List (Stmt C) → Option (String × Nat)
  | .call f args _ (.rets rs) _, P =>
    let ts := Stmt.retTargets rs 0 P
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
def LoopAnn.toStr : LoopAnn C → String
  | .unwind 0 => ""
  | .unwind k => s!"/// @custom:key unwind {k} "
  | .inv I dec =>
    s!"/// @custom:key invariant {I.toStr true} " ++
      ((dec.map fun d => s!"/// @custom:key decreases {d.toStr true} ").getD "")

mutual

def Stmt.toStr : Stmt C → String
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
  | .declMem R x init _ =>
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
    s!"if ({c.toStr true}) \{ {" ".intercalate (Prog.toStrs 0 thn)} } else \{ {" ".intercalate (Prog.toStrs 0 els)} }"
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
    s!"try address({c.addr.toStr}).{c.fn}({args}){rets} \{ {" ".intercalate (Prog.toStrs 0 ok)} } \
      catch Error(string memory) \{ {" ".intercalate (Prog.toStrs 0 err)} } \
      catch Panic({code}) \{ {" ".intercalate (Prog.toStrs 0 pnc)} } \
      catch \{ {" ".intercalate (Prog.toStrs 0 other)} }"
  | .loop a c body => s!"{a.toStr}while ({c.toStr true}) \{ {" ".intercalate (Prog.toStrs 0 body)} }"

/-- The statements of a block, one string each; a memory call and the
statement binding its result are one (`Stmt.memCallStr?`), and so are a call
of several returns and the statements assigning them (`Stmt.tupleCallStr?`),
the statements after the first skipped (`skip` of them). -/
def Prog.toStrs (skip : Nat) : List (Stmt C) → List String
  | [] => []
  | s :: P =>
    match skip with
    | k + 1 => Prog.toStrs k P
    | 0 =>
      match Stmt.tupleCallStr? s P with
      | some (c, k) => c :: Prog.toStrs k P
      | none =>
      match P with
      | t :: _ =>
        match Stmt.memCallStr? s t with
        | some c => c :: Prog.toStrs 1 P
        | none => s.toStr :: Prog.toStrs 0 P
      | [] => [s.toStr]

end

/-- A block, as the Solidity it came from. -/
def Prog.toStr (P : List (Stmt C)) : String := " ".intercalate (Prog.toStrs 0 P)

/-- One statement per line, for display. -/
def Prog.show (P : List (Stmt C)) : String :=
  "\n".intercalate (Prog.toStrs 0 P)

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
`uint`), a struct constructor with named arguments (`T({f: a, g: b})`). -/

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

/-- `constructor(uint v) payable { … }`: the function `init`, the name the
benchmark ports give their constructors (`Examples/Benchmark/Purchase.lean`). -/
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
      for m in ms do
        -- `requires x;` also reads as a state variable `x` of a type `requires`
        let m : Lean.TSyntax `sol_member := ⟨preferReading m.raw fun a =>
          [``solRequires, ``solEnsures, ``solSkip, ``solInvariant, ``solAssignable].any a.isOfKind⟩
        -- a constructor is the function `init`
        let m : Lean.TSyntax `sol_member ← match m with
          | `(sol_member| constructor ( $ps:sol_param,* ) $as:sol_fattr* $b:sol_block) =>
            `(sol_member| function $(Lean.mkIdent `init):ident ( $ps,* ) $as:sol_fattr* $b:sol_block)
          | _ => pure m
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
        | `(sol_member| function $f:ident ( $ps:sol_param,* ) $as:sol_fattr* $b:sol_block) =>
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
      `(({ vars := [$rows,*], funs := [$funs,*], enums := [$enumRows,*], inv := [$invs,*],
           widths := [$widthRows,*] } : Contract))
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


/-! ## The elaborator

Synthesis returns a path or a value with its type; checking takes the
expected primitive type, which is how a literal gets one.  Every proof a
constructor needs comes from a `match h : …` on the check that justifies
it.  A local shadows nothing: a declaration may not reuse the name of a
local in scope or of a state variable. -/

/-- What a local in scope holds. -/
inductive LocalTy where
  /-- A stack local of type `p`, `bits` wide (`uint8 x` is a `uint` 8 bits wide). -/
  | val (p : PrimTy) (bits : Nat := 256)
  | alias (R : RefTy)
  | mem (R : RefTy)
  /-- A storage variable, `old`: only a formula binds one (`old := storage`),
  and a program cannot read it. -/
  | store
  deriving DecidableEq, Repr

/-- The locals in scope, most recent first. -/
abbrev ECtx := List (Name × LocalTy)

/-- A type as read, against the contract: a primitive type (`PrimTy.ofName?`),
an enum of `C` (a `uint`, as a state variable of it is), a struct of
`structDef`.  Any other name is refused (`unknownTyMsg`). -/
def elabTy (C : Contract) : RawTy → Except String Ty
  | .named s =>
    match PrimTy.ofName? s with
    | some p => pure (.prim p)
    | none =>
      if (lookupBy s C.enums).isSome then pure .uint
      else if (narrowTy? s).isSome then throw (narrowNestedMsg s)
      else if (structDef s).isEmpty then throw (unknownTyMsg s)
      else pure (.struct s)
  | .mapping k v => do pure (.mapping (← elabTy C k) (← elabTy C v))
  | .array t => do pure (.array (← elabTy C t))
  | .fixed t n => do pure (.fixed (← elabTy C t) n)

/-- A declared variable's type: `elabTy`'s, or a narrow integer type
(`narrowTy?`) as its primitive type; and its width. -/
def elabDeclTy (C : Contract) : RawTy → Except String (Ty × Nat)
  | .named s =>
    match narrowTy? s with
    | some (p, n) => pure (.prim p, n)
    | none => do pure (← elabTy C (.named s), 256)
  | T => do pure (← elabTy C T, 256)

/-- `PrimTy.toStr`, under the name `Calculus/Spec.lean` uses. -/
abbrev primName (p : PrimTy) : String := p.toStr

/-- A synthesised expression: a storage path, a memory path, or a value. -/
inductive TExpr (C : Contract) where
  | path (T : Ty) (p : SPath C T)
  | mpath (T : Ty) (p : MPath C T)
  | val (p : PrimTy) (v : Val C p)

/-- Its type. -/
def TExpr.ty {C : Contract} : TExpr C → Ty
  | .path T _ | .mpath T _ => T
  | .val p _ => .prim p

/-- A path of primitive type is read as a value. -/
def TExpr.toVal? {C : Contract} : TExpr C → Option ((p : PrimTy) × Val C p)
  | .val p v => some ⟨p, v⟩
  | .path (.prim p) (.loc l) => some ⟨p, .read l⟩
  | .mpath (.prim p) (.loc l) => some ⟨p, .readMem l⟩
  | .path _ _ | .mpath _ _ => none

/-- A literal: a number, or a negated one (`-5`), which takes its type from
where it stands. -/
def RawExpr.isLit : RawExpr → Bool
  | .num _ | .unop .neg (.num _) => true
  | _ => false

/-! ### Traversals of the raw syntax

Every question about a raw expression is `RawExpr.any` of a question about
one node, and every rewrite `RawExpr.mapM` of a rewrite of one node; a
statement is its own expressions (`RawStmt.exprs`) and its blocks
(`RawStmt.blocks`). -/

/-- The Solidity spelling. -/
def RawTy.toStr : RawTy → String
  | .named s => s
  | .mapping k v => s!"mapping({k.toStr} => {v.toStr})"
  | .array t => t.toStr ++ "[]"
  | .fixed t n => s!"{t.toStr}[{n}]"

/-- The Solidity spelling, for messages: an operator application is
parenthesised unless it is the whole expression (`top`). -/
partial def RawExpr.toStr (e : RawExpr) (top : Bool := true) : String :=
  let paren (s : String) := if top then s else s!"({s})"
  match e with
  | .num n => toString n
  | .name x => x
  | .bool b => toString b
  | .field e f => s!"{e.toStr false}.{f}"
  | .index e k => s!"{e.toStr false}[{k.toStr}]"
  | .binop op a b => paren s!"{a.toStr false} {op.sym} {b.toStr false}"
  | .unop op a => s!"{op.sym}{a.toStr false}"
  | .ternary c a b => paren s!"{c.toStr false} ? {a.toStr false} : {b.toStr false}"
  | .incDec op e => IncDec.show op (e.toStr false)
  | .newArr T n => s!"new {T.toStr}({n.toStr})"
  | .call f as => s!"{f}({", ".intercalate (as.map (·.toStr))})"
  | .named f ns as =>
    s!"{f}(\{{", ".intercalate ((ns.zip as).map fun (n, a) => s!"{n}: {a.toStr}")}})"
  | .env k => k.toStr
  | .tuple es => s!"({", ".intercalate (es.map (·.toStr))})"

/-- Whether `p` holds of the expression or of an expression inside it. -/
def RawExpr.any (p : RawExpr → Bool) (e : RawExpr) : Bool :=
  p e || match e with
    | .field a _ | .unop _ a | .incDec _ a | .newArr _ a => a.any p
    | .index a b | .binop _ a b => a.any p || b.any p
    | .ternary c a b => c.any p || a.any p || b.any p
    | .call _ as | .named _ _ as | .tuple as => as.attach.any fun ⟨a, _⟩ => a.any p
    | .num _ | .name _ | .bool _ | .env _ => false

/-- The expression rewritten from the top down: `f` rewrites a node, then
the expressions inside what it returns are rewritten, left to right. -/
partial def RawExpr.mapM {m : Type → Type} [Monad m] [Inhabited (m RawExpr)]
    (f : RawExpr → m RawExpr) (e : RawExpr) : m RawExpr := do
  match ← f e with
  | .field a g => return .field (← a.mapM f) g
  | .index a b => return .index (← a.mapM f) (← b.mapM f)
  | .binop op a b => return .binop op (← a.mapM f) (← b.mapM f)
  | .unop op a => return .unop op (← a.mapM f)
  | .ternary c a b => return .ternary (← c.mapM f) (← a.mapM f) (← b.mapM f)
  | .incDec op a => return .incDec op (← a.mapM f)
  | .newArr T n => return .newArr T (← n.mapM f)
  | .call g as => return .call g (← as.mapM (·.mapM f))
  | .named g ns as => return .named g ns (← as.mapM (·.mapM f))
  | .tuple as => return .tuple (← as.mapM (·.mapM f))
  | e => pure e

/-- The names a raw expression reads, in order. -/
def RawExpr.names : RawExpr → List String
  | .name x => [x]
  | .field e _ | .unop _ e | .incDec _ e | .newArr _ e => e.names
  | .index a b | .binop _ a b => a.names ++ b.names
  | .ternary c a b => c.names ++ a.names ++ b.names
  | .call _ as => as.attach.flatMap fun ⟨a, _⟩ => a.names
  | .named _ _ as | .tuple as => as.attach.flatMap fun ⟨a, _⟩ => a.names
  | .num _ | .bool _ | .env _ => []

/-- Whether an index occurs in the expression: evaluating it may revert. -/
def RawExpr.hasIndex : RawExpr → Bool :=
  RawExpr.any (· matches .index ..)

/-- Whether a `.length` of an indexed base occurs in the expression
(`rows[i].length`): if the base is a fixed-size array, it is evaluated for its
bounds check although the length is a literal, so `hoist` captures it. -/
def RawExpr.hasIdxLen : RawExpr → Bool :=
  RawExpr.any fun | .field b "length" => b.hasIndex | _ => false

/-- Whether an effect occurs in the expression: an `++` or `−−`, or a call
(a cast `uint8(e)` is not one). -/
def RawExpr.hasIncDec : RawExpr → Bool :=
  RawExpr.any fun
    | .incDec .. | .named .. => true
    | .call f _ => (castTy? f).isNone
    | _ => false

/-- Whether a cast `uint8(e)` occurs in the expression: `hoist` captures it. -/
def RawExpr.hasCast : RawExpr → Bool :=
  RawExpr.any fun | .call f _ => (castTy? f).isSome | _ => false

/-- A literal's value: `5`, `-5`. -/
def RawExpr.litVal? : RawExpr → Option Int
  | .num n => some n
  | .unop .neg (.num n) => some (-(n : Int))
  | _ => none

/-- The range of `p` at `n` bits. -/
def intRange (p : PrimTy) (n : Nat) : Int × Int :=
  if p = .int then (-((2 ^ (n - 1) : Nat) : Int), ((2 ^ (n - 1) - 1 : Nat) : Int))
  else (0, ((2 ^ n - 1 : Nat) : Int))

/-- The range predicate `inTy(T, e)`, as a condition: `e` lies in `p`'s range at `n`
bits.  At `uint` only the upper bound is written: the operation's own
256-bit check has reverted below `0`. -/
def inTyCond (p : PrimTy) (n : Nat) (e : RawExpr) : RawExpr :=
  if p = .int then
    .binop .and (.binop .le (.unop .neg (.num (2 ^ (n - 1)))) e) (.binop .le e (.num (2 ^ (n - 1) - 1)))
  else .binop .le e (.num (2 ^ n - 1))

/-- Whether a call occurs in the expression. -/
def RawExpr.hasCall : RawExpr → Bool :=
  RawExpr.any (· matches .call ..)

/-- Whether the name `x` occurs in the expression. -/
def RawExpr.mentions (x : String) : RawExpr → Bool :=
  RawExpr.any fun | .name y => y == x | _ => false

/-- `e` with the names `ρ` maps renamed (a callee's locals, made fresh). -/
def RawExpr.rename (ρ : List (String × String)) (e : RawExpr) : RawExpr :=
  Id.run <| e.mapM fun
    | .name x => .name ((lookupBy x ρ).getD x)
    | e => e

/-- An expression inside `unchecked { … }`: `+ - * **` wrap (`+%` …).  An
`++`/`−−` inside it is an error: its capture (`hoist`) is checked. -/
def RawExpr.uncheck : RawExpr → Except String RawExpr :=
  RawExpr.mapM fun
    | .binop op a b =>
      let op' : BinOp := match op with
        | .add => .addW | .sub => .subW | .mul => .mulW | .pow => .powW | op => op
      pure (.binop op' a b)
    | .incDec .. => throw "`++` or `−−` inside an expression in `unchecked`"
    | e => pure e

/-- The largest index among the fresh variables an expression writes, as the
`FreshNames` in scope reads them (a file may spell `ie1` as `idx`). -/
def RawExpr.maxIdx [FreshNames] (e : RawExpr) : Nat :=
  e.names.foldl (fun n x => max n (Var.ofName x).idx) 0

def RawExpr.maxIdxs [FreshNames] (es : List RawExpr) : Nat :=
  es.foldl (fun n e => max n e.maxIdx) 0

/-- A statement's own expressions, in the order it is written (not those of
its blocks). -/
def RawStmt.exprs : RawStmt → List RawExpr
  | .assign l r | .assignPush l r | .opAssign _ l r | .assignIncDec l _ r => [l, r]
  | .decl _ _ i | .declStorage _ _ i | .declMemory _ _ i | .ret i => i.toList
  | .declStoragePush _ _ b | .delete b | .incDec _ b | .require b | .assert b | .ite b _ _ => [b]
  | .call f as => f :: as
  | .eval as => as
  | .tryCall r _ as .. => r :: as
  | .send none x r a => [x, r, a]
  | .send (some _) _ r a => [r, a]
  | .tupleDecl _ r => [r]
  | .tupleAssign ts r => ts.filterMap id ++ [r]
  | .revert | .unchecked _ | .block _ | .brk | .cont | .hole => []
  | .whileLoop a c _ | .doWhile a _ c | .loop a c _ => a.exprs ++ [c]
  | .forLoop a _ c _ _ => a.exprs ++ c.toList

/-- A statement's blocks: an `if`'s branches, an `unchecked` block's body, a
loop's body (a `for`'s initialisation, body and update). -/
def RawStmt.blocks : RawStmt → List (List RawStmt)
  | .ite _ t e => [t, e]
  | .unchecked b | .block b => [b]
  | .tryCall _ _ _ _ ok err _ pnc other => [ok, err, pnc, other]
  | .whileLoop _ _ b | .doWhile _ b _ | .loop _ _ b => [b]
  | .forLoop _ i _ u b => [i, b, u]
  | _ => []

/-- A loop's specification with its expressions rewritten by `f`. -/
def RawLoopSpec.mapM {m : Type → Type} [Monad m] (f : RawExpr → m RawExpr) (a : RawLoopSpec) :
    m RawLoopSpec :=
  return { a with inv := ← a.inv.mapM f, dec := ← a.dec.mapM f }

/-- A statement with its own expressions rewritten by `f`, left to right (its
blocks as they are). -/
def RawStmt.mapExprsM {m : Type → Type} [Monad m] (f : RawExpr → m RawExpr) :
    RawStmt → m RawStmt
  | .assign l r => return .assign (← f l) (← f r)
  | .assignPush l r => return .assignPush (← f l) (← f r)
  | .opAssign op l r => return .opAssign op (← f l) (← f r)
  | .assignIncDec l op r => return .assignIncDec (← f l) op (← f r)
  | .decl T x i => return .decl T x (← i.mapM f)
  | .declStorage T x i => return .declStorage T x (← i.mapM f)
  | .declMemory T x i => return .declMemory T x (← i.mapM f)
  | .ret i => return .ret (← i.mapM f)
  | .declStoragePush T x b => return .declStoragePush T x (← f b)
  | .delete b => return .delete (← f b)
  | .incDec op b => return .incDec op (← f b)
  | .require b => return .require (← f b)
  | .assert b => return .assert (← f b)
  | .ite c t e => return .ite (← f c) t e
  | .call g as => return .call (← f g) (← as.mapM f)
  | .eval as => return .eval (← as.mapM f)
  | .revert => pure .revert
  | .unchecked b => pure (.unchecked b)
  | .tryCall r g as rets ok err code pnc other =>
    return .tryCall (← f r) g (← as.mapM f) rets ok err code pnc other
  | .send T x r a => return .send T (← f x) (← f r) (← f a)
  | .tupleDecl vs r => return .tupleDecl vs (← f r)
  | .tupleAssign ts r => return .tupleAssign (← ts.mapM (·.mapM f)) (← f r)
  | .block b => pure (.block b)
  | .brk => pure .brk
  | .cont => pure .cont
  | .hole => pure .hole
  | .whileLoop a c b => return .whileLoop (← a.mapM f) (← f c) b
  | .doWhile a b c => return .doWhile (← a.mapM f) b (← f c)
  | .loop a c b => return .loop (← a.mapM f) (← f c) b
  | .forLoop a i c u b => return .forLoop (← a.mapM f) i (← c.mapM f) u b

/-- The name a statement declares in its own block. -/
def RawStmt.declared? : RawStmt → Option String
  | .decl _ x _ | .declStorage _ x _ | .declMemory _ x _ | .declStoragePush _ x _ => some x
  | .send (some _) (.name x) _ _ => some x
  | _ => none

/-- The names a statement binds in its blocks: a `try`'s return locals and
`Panic` code; and the variables a tuple declaration declares in its own. -/
def RawStmt.binds : RawStmt → List String
  | .tryCall _ _ _ rets _ _ code _ _ => rets.map (·.2) ++ code.toList
  | .tupleDecl vs _ => vs.filterMap (·.map (·.2))
  | _ => []

/-- Whether a `return` occurs in the statement. -/
partial def RawStmt.hasReturn (s : RawStmt) : Bool :=
  s matches .ret _ || s.blocks.any (·.any RawStmt.hasReturn)

/-- Whether the name `x` occurs in the statement, read, written or declared. -/
partial def RawStmt.mentions (x : String) (s : RawStmt) : Bool :=
  s.declared? == some x || s.binds.contains x || s.exprs.any (·.mentions x) ||
    s.blocks.any (·.any (·.mentions x))

mutual

/-- The names a raw statement reads (a function's name is not one). -/
partial def RawStmt.names (s : RawStmt) : List String :=
  let es := match s with
    | .call (.name _) as => as
    | s => s.exprs
  es.flatMap RawExpr.names ++ s.blocks.flatMap RawStmt.namesList

partial def RawStmt.namesList (ss : List RawStmt) : List String :=
  ss.flatMap RawStmt.names

end

mutual

/-- The names a raw statement declares, in either branch of an `if`. -/
partial def RawStmt.decls (s : RawStmt) : List String :=
  s.declared?.toList ++ s.binds ++ s.blocks.flatMap RawStmt.declsList

partial def RawStmt.declsList (ss : List RawStmt) : List String :=
  ss.flatMap RawStmt.decls

end

mutual

/-- The largest index among the fresh variables a raw statement writes. -/
partial def RawStmt.maxIdx [FreshNames] (s : RawStmt) : Nat :=
  max (((s.declared?.toList ++ s.binds).map fun x => (Var.ofName x).idx).foldl max 0)
    (max (RawExpr.maxIdxs s.exprs) ((s.blocks.map RawStmt.maxIdxs).foldl max 0))

partial def RawStmt.maxIdxs [FreshNames] (ss : List RawStmt) : Nat :=
  ss.foldl (fun n s => max n s.maxIdx) 0

end

section Elab

variable [FreshNames] (C : Contract)

/-- `E.m` for an enum `E` of the contract that no local or state variable
shadows: the position of `m`. -/
def enumLit? (Γ : ECtx) : RawExpr → String → Option Nat
  | .name x, m =>
    if (lookupBy x Γ).isNone && (C.rootType x).isNone then
      (lookupBy x C.enums).bind (·.findIdx? (· == m))
    else none
  | _, _ => none

mutual

def synth (Γ : ECtx) : RawExpr → Except String (TExpr C)
  | .num n => pure (.val .uint (.simple (.lit n rfl)))
  | .bool b => pure (.val .bool (.simple (.bool b)))
  | .name x =>
    match lookupBy x Γ with
    | some (.val p _) => pure (.val p (.simple (.local (Var.ofName x))))
    | some (.alias R) => pure (.path (.ref R) (.alias (Var.ofName x)))
    | some (.mem R) => pure (.mpath (.ref R) (.var (Var.ofName x)))
    | some .store => throw s!"{x} is a storage variable, not a program value"
    | none =>
      match hr : C.rootType x with
      | some T => pure (.path T (.loc (.root x hr)))
      | none => throw s!"unknown name {x}"
  | .field e f => do
    if let some i := enumLit? C Γ e f then return .val .uint (.simple (.lit i rfl))
    match ← synth Γ e with
    | .path (.ref (.array _)) b =>
      if f == "length" then pure (.val .uint (.len b rfl))
      else throw s!"member access .{f} on an array"
    | .mpath (.ref (.array _)) b =>
      if f == "length" then pure (.val .uint (.mlen b rfl))
      else throw s!"member access .{f} on an array"
    -- a fixed-size array's length is its type's: the literal, as solc folds
    -- it.  A base that indexes is evaluated first (it may revert), so
    -- `hoist` captured it; one left is where no capture may go.
    | .path (.ref (.fixed _ n)) _ | .mpath (.ref (.fixed _ n)) _ =>
      if f != "length" then throw s!"member access .{f} on an array"
      else if e.hasIndex then
        throw "the length of an indexed fixed-size array under a short-circuit operator or in a conditional's branch"
      else pure (.val .uint (.simple (.lit n rfl)))
    | .path (.ref (.struct s)) b =>
      match h : C.fieldType s f with
      | some T => pure (.path T (.loc (.field b f h)))
      | none => throw s!"struct {s} has no member {f}"
    | .mpath (.ref (.struct s)) b =>
      match h : C.fieldType s f with
      | some T => pure (.mpath T (.loc (.field b f h)))
      | none => throw s!"struct {s} has no member {f}"
    | _ => throw s!"member access .{f} on a non-struct"
  | .index e k => do
    match ← synth Γ e with
    | .path (.ref (.mapping (.prim kp) V)) b => pure (.path V (.loc (.index .map b (← check Γ kp k))))
    | .path (.ref (.array E)) b => pure (.path E (.loc (.index (.arr .dyn) b (← check Γ .uint k))))
    | .mpath (.ref (.array E)) b => pure (.mpath E (.loc (.index .dyn b (← check Γ .uint k))))
    -- a literal index past a fixed-size array's end is solc's compile error
    | .path (.ref (.fixed E n)) b =>
      if let .num i := k then if n ≤ i then throw s!"index {i} out of bounds of a length-{n} array"
      pure (.path E (.loc (.index (.arr .fixed) b (← check Γ .uint k))))
    | .mpath (.ref (.fixed E n)) b =>
      if let .num i := k then if n ≤ i then throw s!"index {i} out of bounds of a length-{n} array"
      pure (.mpath E (.loc (.index .fixed b (← check Γ .uint k))))
    | t => throw s!"{e.toStr} is indexed, but it is a {t.ty}, not a mapping or an array"
  | .binop op a b => do
    -- the operand type: the first operand that is not a literal gives it
    let t ← if a.isLit then synth Γ b else synth Γ a
    let some ⟨p, _⟩ := t.toVal? |
      throw s!"{(if a.isLit then b else a).toStr}: an operand of reference type {t.ty}"
    match h : op.accepts p with
    | true => pure (.val _ (.binop op h rfl (← check Γ p a) (← check Γ p b)))
    | false => throw s!"operator {BinOp.sym op} does not take {primName p}"
  | .ternary c a b => do
    let t ← if a.isLit then synth Γ b else synth Γ a
    let some ⟨p, _⟩ := t.toVal? | throw "a conditional of reference type"
    pure (.val p (.ternary (← check Γ .bool c) (← check Γ p a) (← check Γ p b)))
  | .unop op a => do
    let t ← synth Γ a
    let some ⟨p, v⟩ := t.toVal? | throw s!"{a.toStr}: an operand of reference type {t.ty}"
    match h : op.accepts p with
    | true => pure (.val _ (.unop op h rfl v))
    | false => throw s!"operator {UnOp.sym op} does not take {primName p}"
  | .incDec .. => throw "`++` or `−−` under a short-circuit operator or in a conditional's branch"
  | .newArr .. => throw "`new` stands only on the right of `=`"
  | .call f _ => throw s!"the call {f}(…) under a short-circuit operator or in a conditional's branch"
  | .named f .. => throw s!"the constructor {f}(\{…}) under a short-circuit operator or in a conditional's branch"
  | .env k => pure (.val .uint (.simple (.env k rfl)))
  | .tuple _ => throw "a tuple is the right-hand side of a tuple assignment or of a `return`"
termination_by e => (sizeOf e, 0)

/-- `e` checked at `p` through its synthesised type. -/
def checkVia (Γ : ECtx) (p : PrimTy) (e : RawExpr) : Except String (Val C p) := do
  let some ⟨q, v⟩ := (← synth Γ e).toVal? |
    throw s!"a storage reference where a {primName p} is expected"
  if h : q = p then pure (h ▸ v) else throw s!"a {primName q} where a {primName p} is expected"
termination_by (sizeOf e, 1)

def check (Γ : ECtx) (p : PrimTy) : RawExpr → Except String (Val C p)
  | .num n =>
    match h : p.isNumeric with
    | true => pure (.simple (.lit n h))
    | false => throw s!"a number where a {primName p} is expected"
  -- a negative literal takes the type it is checked at: `int e = -5;`
  | .unop .neg (.num n) =>
    if hp : p = .int then pure (by subst hp; exact .simple (.lit (-(n : Int)) rfl))
    else checkVia Γ p (.unop .neg (.num n))
  -- so does arithmetic on literals alone: `int e = -5 + 2;`
  | .binop op a b =>
    if a.isLit && b.isLit && op.isArith then
      match h : op.accepts p with
      | true =>
        if hq : op.ret p = p then do pure (.binop op h hq (← check Γ p a) (← check Γ p b))
        else checkVia Γ p (.binop op a b)
      | false => checkVia Γ p (.binop op a b)
    else checkVia Γ p (.binop op a b)
  | e => checkVia Γ p e
termination_by e => (sizeOf e, 2)

end

/-- `e` as a storage path of type `T`. -/
def checkPath (Γ : ECtx) (T : Ty) (e : RawExpr) : Except String (SPath C T) := do
  match ← synth C Γ e with
  | .path T' p =>
    if h : T' = T then pure (h ▸ p)
    else throw s!"{e.toStr}: a storage reference to a {T'} where a {T} is expected"
  | .mpath .. | .val .. => throw "a value where a storage reference is expected"

/-- `e` as a memory path of type `T`. -/
def checkMPath (Γ : ECtx) (T : Ty) (e : RawExpr) : Except String (MPath C T) := do
  match ← synth C Γ e with
  | .mpath T' p =>
    if h : T' = T then pure (h ▸ p)
    else throw s!"{e.toStr}: a memory reference to a {T'} where a {T} is expected"
  | .path .. | .val .. => throw "a memory reference is expected"

/-- What a memory local is bound to: a memory path by identity, or a storage
path deep-copied. -/
def elabMRhs (Γ : ECtx) (R : RefTy) (e : RawExpr) : Except String (MRhs C R) := do
  match ← synth C Γ e with
  | .mpath T p =>
    if h : T = .ref R then pure (.alias (h ▸ p))
    else throw s!"{e.toStr}: a memory reference to a {T} where a {Ty.ref R} is expected"
  | .path T p =>
    if h : T = .ref R then
      match hm : (Ty.ref R).mapFree with
      | true => pure (.copy (h ▸ p) hm)
      | false => throw "a copy into memory of a type that holds a mapping"
    else throw s!"{e.toStr}: a storage reference to a {T} where a {Ty.ref R} is expected"
  | .val .. => throw "a value where a memory reference is expected"

/-- The slot `b.push()` appends, as what an alias of `R` is bound to. -/
def elabPush (Γ : ECtx) (R : RefTy) (b : RawExpr) : Except String (ARhs C R) := do
  match hd : (Ty.ref R).defaultOkS with
  | true => pure (.push (← checkPath C Γ (.array (.ref R)) b) hd)
  | false => throw "push() of an element whose default is not well-formed"

/-- `x` may be declared: it is neither a local in scope nor a state variable. -/
def checkFresh (Γ : ECtx) (x : Name) : Except String Unit :=
  if (lookupBy x Γ).isSome || (C.rootType x).isSome then
    throw s!"{x} is already declared, or names a state variable"
  else pure ()

/-- Elaboration threads the locals in scope and the index of the next
variable a capture declares, and reads the functions a call may name: the
contract's, and in a function's body the ones declared before it. -/
abbrev ElabM := ReaderT (List (Name × FunDecl)) (StateT (ECtx × Nat) (Except String))

/-- A checking step, in the elaborator. -/
def ElabM.lift {α : Type} (x : Except String α) : ElabM α := fun _ => StateT.lift x

/-- A fresh variable for a capture, `ie1`, `sp2`: numbered past every
variable the program itself writes. -/
def freshCapture (base : String) : ElabM Var := do
  let (Γ, k) ← get
  set (Γ, k + 1)
  pure (.fresh base k)

/-- The locals in scope. -/
def ctx : ElabM ECtx := do pure (← get).1

/-- `synth`, in the locals in scope. -/
def synthM (e : RawExpr) : ElabM (TExpr C) := do ElabM.lift (synth C (← ctx) e)

/-- `check`, in the locals in scope. -/
def checkM (p : PrimTy) (e : RawExpr) : ElabM (Val C p) := do ElabM.lift (check C (← ctx) p e)

/-- A compound assignment's target, with a non-simple index captured into a
fresh `ie` first: `values[i + 1] += 1;` is `uint ie1 = i + 1; values[ie1] += 1;`. -/
def elabOpTarget (l : RawExpr) : ElabM (Prog C × (p : PrimTy) × OpLoc C p) := do
  match ← synthM C l with
  | .val p (.simple (.local x)) => pure ([], ⟨p, .local x⟩)
  | .path (.prim p) (.loc (.root r h)) => pure ([], ⟨p, .root r h⟩)
  | .path (.prim p) (.loc (.field b f h)) => pure ([], ⟨p, .field b f h⟩)
  | .path (.prim p) (.loc (@Loc.index _ _ k _ it b i)) =>
    match i.toSimple? with
    | some ie => pure ([], ⟨p, .index it b ie⟩)
    | none =>
      let x ← freshCapture "ie"
      pure ([.declLocal k x (some i)], ⟨p, .index it b (.local x)⟩)
  | .mpath (.prim p) (.loc (.field b f h)) => pure ([], ⟨p, .mfield b f h⟩)
  | .mpath (.prim p) (.loc (.index a b i)) =>
    match i.toSimple? with
    | some ie => pure ([], ⟨p, .mindex a b ie⟩)
    | none =>
      let x ← freshCapture "ie"
      pure ([.declLocal .uint x (some i)], ⟨p, .mindex a b (.local x)⟩)
  | _ => throw "a compound assignment needs a local or a place of value type"

/-- An inc/dec target for the assignment form, with a non-simple receiver
captured into a fresh `sp` or `mv` first: `y = folks[i].age++;` is
`Person storage sp1 = folks[i]; y = sp1.age++;`. -/
def elabIncTarget (l : RawExpr) :
    ElabM (Prog C × (p : PrimTy) × (t : OpLoc C p) ×' t.recvSimple = true) := do
  let (pre, ⟨p, t⟩) ← elabOpTarget C l
  match hs : t.recvSimple with
  | true => pure (pre, ⟨p, t, hs⟩)
  | false =>
    match t with
    | .field b f h =>
      let x ← freshCapture "sp"
      pure (pre ++ [.declStorage (.struct _) x (some (.path b))], ⟨p, .field (.alias x) f h, rfl⟩)
    | .index it b i =>
      let x ← freshCapture "sp"
      pure (pre ++ [.declStorage _ x (some (.path b))], ⟨p, .index it (.alias x) i, rfl⟩)
    | .mfield b f h =>
      let x ← freshCapture "mv"
      pure (pre ++ [.declMem (.struct _) x (some (.alias b)) rfl], ⟨p, .mfield (.var x) f h, rfl⟩)
    | .mindex a b i =>
      let x ← freshCapture "mv"
      pure (pre ++ [.declMem _ x (some (.alias b)) rfl], ⟨p, .mindex a (.var x) i, rfl⟩)
    | .local _ | .root .. => nomatch hs

/-- Declare `x` in scope. -/
def declare (x : Name) (t : LocalTy) : ElabM Unit := do
  let (Γ, k) ← get
  checkFresh C Γ x
  set (setBy x t Γ, k)

/-- A capture: a fresh `base` variable (`freshCapture`), declared at `t`. -/
def captureAs (base : String) (t : LocalTy) : ElabM Var := do
  let x ← freshCapture base
  declare C (toString x) t
  pure x

/-- The size of `new T[](n)` as a simple value: a size that is not one is
captured into a fresh `uint` first (KeY's `memoryArrayFreshAlloc` takes a
`SimpleExpression`). -/
def elabSize (n : RawExpr) : ElabM (Prog C × Simple C .uint) := do
  let v ← checkM C .uint n
  match v.toSimple? with
  | some se => pure ([], se)
  | none =>
    let x ← freshCapture "se"
    pure ([.declLocal .uint x (some v)], .local x)

/-- `e` as a simple value of type `p`, captured into a fresh local first
when it is not one. -/
def simpleOf (p : PrimTy) (e : RawExpr) : ElabM (Prog C × Simple C p) := do
  let v ← checkM C p e
  match v.toSimple? with
  | some se => pure ([], se)
  | none =>
    let x ← captureAs C "se" (.val p)
    pure ([.declLocal p x (some v)], .local x)

/-- The array type `new T(n)` allocates, if it may be allocated. -/
def elabNewTy (T : RawTy) : ElabM ((R : RefTy) ×' R.newArrOk = true) := do
  let .ref R ← ElabM.lift (elabTy C T) | throw "`new` of a value type"
  match h : R.newArrOk with
  | true => pure ⟨R, h⟩
  | false => throw "`new` of an array whose elements a memory array cannot hold"

/-! ### Narrow widths -/

/-- Two operands' type: a literal takes the other's, and the wider wins (solc
converts a `uint8` to a `uint16` implicitly). -/
def joinIT : Option (PrimTy × Nat) → Option (PrimTy × Nat) → Option (PrimTy × Nat)
  | none, t => t
  | t, none => t
  | some (p, n), some (_, m) => some (p, max n m)

/-- The integer type solc gives `e`: `some (p, n)` for `n` bits (a value not
built from a narrow variable or a cast is 256 bits wide), `none` for a literal,
which takes the type of what it meets.  `a ** b`, `a << b` and `a >> b` have
`a`'s type (a literal base is 256 bits wide, solc ≥ 0.7). -/
def intTyOf (Γ : ECtx) : RawExpr → Option (PrimTy × Nat)
  | .num _ => none
  | .name x =>
    match lookupBy x Γ with
    | some (.val p n) => some (p, n)
    | some _ => some (.uint, 256)
    | none =>
      match C.rootType x with
      | some (.prim p) => some (p, (lookupBy x C.widths).getD 256)
      | _ => some (.uint, 256)
  | .unop .not _ => some (.bool, 256)
  | .unop _ a => intTyOf Γ a
  | .binop op a b =>
    if !op.isArith then some (.bool, 256)
    else if op matches .pow | .powW | .shl | .shr then
      match a.litVal? with
      | some v => some (if v < 0 then .int else .uint, 256)
      | none => intTyOf Γ a
    else joinIT (intTyOf Γ a) (intTyOf Γ b)
  | .ternary _ a b => joinIT (intTyOf Γ a) (intTyOf Γ b)
  | .incDec _ e => intTyOf Γ e
  | .call f _ => some ((castTy? f).getD (.uint, 256))
  | .bool _ => some (.bool, 256)
  | _ => some (.uint, 256)

/-- `e`'s width in bits: `intTyOf`'s, `256` for a literal. -/
def widthIn (Γ : ECtx) (e : RawExpr) : Nat := ((intTyOf C Γ e).map (·.2)).getD 256

/-- `e`, an operation that can leave its narrow type — `+ - * **`, and `/` and
unary `-` at `int` (`-128 / -1` at `int8`) — with that type. -/
def checkedNarrow? (Γ : ECtx) (e : RawExpr) : Option (PrimTy × Nat) :=
  match e, intTyOf C Γ e with
  | .binop op _ _, some (p, n) =>
    if n < 256 && ((op matches .add | .sub | .mul | .pow) || (op == .div && p == .int))
    then some (p, n) else none
  | .unop .neg _, some (.int, n) => if n < 256 then some (.int, n) else none
  | _, _ => none

/-- Whether a narrow operation (`checkedNarrow?`) occurs in `e`. -/
def hasNarrow (Γ : ECtx) (e : RawExpr) : Bool :=
  e.any fun n => (checkedNarrow? C Γ n).isSome

/-- `r` may be written where a `p` of `n` bits is expected: a literal fits it,
and a value is not wider (solc converts only to a wider type implicitly). -/
def fitCheck (Γ : ECtx) (p : PrimTy) (n : Nat) (r : RawExpr) : Except String Unit := do
  if 256 ≤ n then return
  match r.litVal?, intTyOf C Γ r with
  | some v, _ =>
    let (lo, hi) := intRange p n
    unless lo ≤ v && v ≤ hi do throw s!"{v} does not fit {tyName p n}"
  | none, some (q, m) =>
    if q != .bool && n < m then
      throw s!"a {tyName q m} where a {tyName p n} is expected: write {tyName p n}(…)"
  | none, none => pure ()

/-- One node at a narrow `uintN`, read as solc reads it: the wrapping
`+% -% *% **%` of `unchecked` and `<<` are taken modulo `2^N` (solc truncates
them to the type), `~a` is `(2^N - 1) -% a`; and a literal operand must fit the
type. -/
def narrowWrapNode (Γ : ECtx) (e : RawExpr) : Except String RawExpr := do
  let some (p, n) := intTyOf C Γ e | return e
  if 256 ≤ n then return e
  match e with
  | .binop op a b =>
    -- `%` too: the modulus this rewrite writes may meet it again
    unless op matches .pow | .powW | .shl | .shr | .mod do
      for l in [a, b] do
        if let some v := l.litVal? then
          let (lo, hi) := intRange p n
          unless lo ≤ v && v ≤ hi do throw s!"{v} does not fit {tyName p n}"
    if op matches .addW | .subW | .mulW | .powW | .shl then
      return .binop .mod e (.num (2 ^ n))
    return e
  | .unop .bnot a => return .binop .subW (.num (2 ^ n - 1)) a
  | _ => return e

/-- `narrowWrapNode` at every node of `e`, bottom up. -/
partial def narrowPure (Γ : ECtx) : RawExpr → Except String RawExpr
  | .binop op a b => do narrowWrapNode C Γ (.binop op (← narrowPure Γ a) (← narrowPure Γ b))
  | .unop op a => do narrowWrapNode C Γ (.unop op (← narrowPure Γ a))
  | .field e f => do pure (.field (← narrowPure Γ e) f)
  | .index e k => do pure (.index (← narrowPure Γ e) (← narrowPure Γ k))
  | .ternary c a b => do pure (.ternary (← narrowPure Γ c) (← narrowPure Γ a) (← narrowPure Γ b))
  | .incDec op e => do pure (.incDec op (← narrowPure Γ e))
  | .newArr T e => do pure (.newArr T (← narrowPure Γ e))
  | .call f as => do pure (.call f (← as.mapM (narrowPure Γ)))
  | .named f ns as => do pure (.named f ns (← as.mapM (narrowPure Γ)))
  | e => pure e

/-- `require(inTy)` of `e` at `p`'s `n` bits, when `n` is narrow. -/
def narrowCheck (p : PrimTy) (n : Nat) (e : RawExpr) : ElabM (Prog C) := do
  if 256 ≤ n then return []
  pure [.require (← checkM C .bool (inTyCond p n e))]

/-- What follows a write of `r` to the variable `l`: the check of `r`'s narrow
operation, on `l` (`c = a + b;` at `uint8` is `c = a + b; require(c <= 255);`:
a revert discards the write, so checking after it is checking before it); and,
when `l` is narrow, `r` fitting it (`fitCheck`) and arithmetic on literals
alone checked at `l`'s type (solc folds it at compile time). -/
def narrowPost (l r : RawExpr) : ElabM (Prog C) := do
  let Γ ← ctx
  let tl := intTyOf C Γ l
  if let some (p, n) := tl then ElabM.lift (fitCheck C Γ p n r)
  match checkedNarrow? C Γ r, tl, intTyOf C Γ r, r.litVal? with
  | some (p, n), _, _, _ => narrowCheck C p n l
  | none, some (p, n), none, none => narrowCheck C p n l
  | _, _, _, _ => pure []

/-- A narrow operation inside an expression, its operands' captures made:
held in a fresh local and checked there, before the statement
(`x = a + b > c;` at `uint8` is `uint se1 = a + b; require(se1 <= 255);
x = se1 > c;`). -/
def narrowCapture (e : RawExpr) : ElabM (Prog C × RawExpr) := do
  let some (p, n) := checkedNarrow? C (← ctx) e | return ([], e)
  let v ← checkM C p e
  let x ← captureAs C "se" (.val p n)
  let e' : RawExpr := .name (toString x)
  pure (.declLocal p x (some v) :: (← narrowCheck C p n e'), e')

/-- A cast `T(e)`, `e`'s captures made: a fresh local of type `T` holding `e`.
Narrowing a `uint` keeps the low bits (`e % 2^N`, as solc truncates); a cast
between `uint` and `int`, and one narrowing an `int`, are refused. -/
def castCapture (f : String) (e : RawExpr) : ElabM (Prog C × RawExpr) := do
  let some (p, n) := castTy? f | throw s!"{f} is not a type"
  let Γ ← ctx
  let r ← match intTyOf C Γ e, e.litVal? with
    | _, some _ => do ElabM.lift (fitCheck C Γ p n e); pure e
    | some (q, m), none =>
      if q != p then throw s!"{f}({e.toStr}): a cast between uint and int is not modelled"
      else if m ≤ n then pure e
      else if p == .int then throw s!"{f}({e.toStr}): a cast narrowing an int is not modelled"
      else pure (.binop .mod e (.num (2 ^ n)))
    | none, none =>
      if 256 ≤ n then pure e
      else if p == .int then throw s!"{f}({e.toStr}): a cast narrowing an int is not modelled"
      else pure (.binop .mod e (.num (2 ^ n)))
  let v ← checkM C p r
  let x ← captureAs C "se" (.val p n)
  pure ([.declLocal p x (some v)], .name (toString x))

/-- `e`'s value, or the reference it names, held in a fresh local before a
later operand's effect: `x = i++ + i;` reads the right `i` first (solc
evaluates a binary operator's right operand first), so it is
`uint se1 = i; uint se2; se2 = i++; x = se2 + se1;`.  A literal needs no
capture, nor does a name bound to a reference (an effect cannot rebind it). -/
def captureExpr (e : RawExpr) : ElabM (Prog C × RawExpr) := do
  if e.isLit || e matches .bool _ then return ([], e)
  -- a capture already made holds its value
  if let .name x := e then
    if Var.ofName x matches .fresh .. then return ([], e)
  let t ← synthM C e
  match e, t with
  | .name _, .path (.ref _) _ | .name _, .mpath (.ref _) _ => return ([], e)
  | _, .path (.ref R) sp =>
    let x ← captureAs C "sp" (.alias R)
    return ([.declStorage R x (some (.path sp))], .name (toString x))
  | _, .mpath (.ref R) mp =>
    let x ← captureAs C "mv" (.mem R)
    return ([.declMem R x (some (.alias mp)) rfl], .name (toString x))
  | _, t =>
    let some ⟨p, v⟩ := t.toVal? | throw s!"{e.toStr}: a value or a reference is expected"
    let x ← captureAs C "se" (.val p (widthIn C (← ctx) e))
    return ([.declLocal p x (some v)], .name (toString x))

/-! ### Inlining a call -/

/-- A callee's body with its locals renamed fresh, each declaration's name
numbered as a capture of its kind is (`se`, `sp`, `mv`), and the names `ρ`
maps (its parameters and return variable) renamed: inlined, it binds no
name the caller uses. -/
partial def renameStmts (ρ : List (String × String)) : List RawStmt → ElabM (List RawStmt)
  | [] => pure []
  | s :: ss => do
    let r := RawExpr.rename ρ
    let ra (a : RawLoopSpec) : RawLoopSpec := Id.run (a.mapM (pure ∘ r))
    let fresh (base x : String) : ElabM (String × List (String × String)) := do
      let y := toString (← freshCapture base)
      pure (y, (x, y) :: ρ)
    match s with
    | .decl T x i =>
      let (y, ρ') ← fresh "se" x
      pure (.decl T y (i.map r) :: (← renameStmts ρ' ss))
    | .declStorage T x i =>
      let (y, ρ') ← fresh "sp" x
      pure (.declStorage T y (i.map r) :: (← renameStmts ρ' ss))
    | .declMemory T x i =>
      let (y, ρ') ← fresh "mv" x
      pure (.declMemory T y (i.map r) :: (← renameStmts ρ' ss))
    | .declStoragePush T x b =>
      let (y, ρ') ← fresh "sp" x
      pure (.declStoragePush T y (r b) :: (← renameStmts ρ' ss))
    | .send (some T) (.name x) e a =>
      let (y, ρ') ← fresh "se" x
      pure (.send (some T) (.name y) (r e) (r a) :: (← renameStmts ρ' ss))
    | .ite c t e =>
      pure (.ite (r c) (← renameStmts ρ t) (← renameStmts ρ e) :: (← renameStmts ρ ss))
    | .unchecked b => pure (.unchecked (← renameStmts ρ b) :: (← renameStmts ρ ss))
    | .block b => pure (.block (← renameStmts ρ b) :: (← renameStmts ρ ss))
    | .tupleDecl vs e =>
      let mut ρ' := ρ
      let mut vs' := []
      for v in vs do
        match v with
        | some (T, x) =>
          let y := toString (← freshCapture "se")
          ρ' := (x, y) :: ρ'
          vs' := vs' ++ [some (T, y)]
        | none => vs' := vs' ++ [none]
      pure (.tupleDecl vs' (r e) :: (← renameStmts ρ' ss))
    | .tryCall e g as rets ok err code pnc other =>
      let mut ρok := ρ
      let mut rets' := []
      for (T, x) in rets do
        let y := toString (← freshCapture "se")
        ρok := (x, y) :: ρok
        rets' := rets' ++ [(T, y)]
      let (code', ρp) ← match code with
        | some x => fresh "se" x >>= fun (y, ρ') => pure (some y, ρ')
        | none => pure (none, ρ)
      pure (.tryCall (r e) g (as.map r) rets' (← renameStmts ρok ok) (← renameStmts ρ err) code'
        (← renameStmts ρp pnc) (← renameStmts ρ other) :: (← renameStmts ρ ss))
    | .whileLoop a c b =>
      pure (.whileLoop (ra a) (r c) (← renameStmts ρ b) :: (← renameStmts ρ ss))
    | .doWhile a b c =>
      pure (.doWhile (ra a) (← renameStmts ρ b) (r c) :: (← renameStmts ρ ss))
    | .loop a c b =>
      pure (.loop (ra a) (r c) (← renameStmts ρ b) :: (← renameStmts ρ ss))
    | .forLoop a [] c u b =>
      pure (.forLoop (ra a) [] (c.map r) (← renameStmts ρ u) (← renameStmts ρ b) ::
        (← renameStmts ρ ss))
    | .forLoop a i c u b =>
      -- the initialisation's declarations scope over the rest of the loop
      let out ← renameStmts ρ (i ++ [.forLoop a [] c u b])
      match out.getLast? with
      | some (.forLoop a' [] c' u' b') =>
        pure (.forLoop a' out.dropLast c' u' b' :: (← renameStmts ρ ss))
      | _ => throw "a `for` loop's initialisation, renamed"
    | s => pure ((Id.run (s.mapExprsM (pure ∘ r))) :: (← renameStmts ρ ss))

/-- `return e;`, lowered to the return variables `rs`: `r = e;` for one;
for several, `r₀ = e₀; r₁ = e₁; …` from `return (e₀, e₁, …);`, or, when a
component reads a return variable, the tuple assignment `(r₀, r₁, …) = e;`,
which reads every component before it writes (`elabTuple`; solkey's
`ReturnLowering`, `returnSwapped`).  Lean only: `return g();` of several
values is `(r₀, r₁, …) = g();`, which solkey's `ReturnLowering` refuses. -/
def lowerReturn (rs : List String) (e : RawExpr) : Except String (List RawStmt) :=
  match rs, e with
  | [], _ => throw "`return` of a value from a function that returns none"
  | [_], .tuple es => throw s!"`return` of {es.length} values from a function that returns one"
  | [n], e => pure [.assign (.name n) e]
  | rs, .tuple es =>
    if es.length != rs.length then
      throw s!"`return` of {es.length} values from a function that returns {rs.length}"
    else if es.any fun e => rs.any e.mentions then
      pure [.tupleAssign (rs.map fun n => some (.name n)) (.tuple es)]
    else pure ((rs.zip es).map fun (n, e) => .assign (.name n) e)
  | rs, e@(.call ..) => pure [.tupleAssign (rs.map fun n => some (.name n)) e]
  | rs, _ => throw s!"`return` of one value from a function that returns {rs.length}"

/-- The names a statement declares in its own block: a declaration's, a tuple
declaration's. -/
def RawStmt.declaredAll (s : RawStmt) : List String :=
  match s with
  | .tupleDecl .. => s.binds
  | s => s.declared?.toList

/-- **A body's `return`s, lowered** to assignments to its return variables
`r` (`return x + 1;` is `r = x + 1;`, `lowerReturn`), so that `Stmt.run` has no abrupt
completion.  What follows a `return` in its block is dead and dropped; the
statements after an `if` one of whose branches returns move into both
branches, which is where they run: `if (c) { return a; } s;` is
`if (c) { r = a; } else { s; }`.  A branch's own declarations would then be
in scope over the moved statements, so a moved statement may not name one
(Solidity scopes it to the branch); in an inlined body every local is
already fresh (`renameStmts`), and that never happens.  A block with a
`return` inside is spliced into the statements after it (solkey's
`blockReturn`, by the same guard).  A `return` inside a loop is lowered
first, to a flag (`lowerLoops`), since this cannot give an early exit from a
loop: what is left of it is the `if (ret) return;` after the outermost loop.
A function on a body as read: it may run before or
after the body is renamed. -/
partial def lowerReturns (r : List String) : List RawStmt → Except String (List RawStmt)
  | [] => pure []
  | .ret none :: _ => pure []
  | .ret (some e) :: _ => lowerReturn r e
  | .block b :: ss => do
    if b.any RawStmt.hasReturn && !ss.isEmpty then
      for x in b.flatMap RawStmt.declaredAll do
        if ss.any (·.mentions x) then
          throw s!"`return` in a block declaring {x}, which the statements after it name"
      lowerReturns r (b ++ ss)
    else
      pure (.block (← lowerReturns r b) :: (← lowerReturns r ss))
  | .ite c t e :: ss => do
    if (t.any RawStmt.hasReturn || e.any RawStmt.hasReturn) && !ss.isEmpty then
      for x in (t ++ e).flatMap RawStmt.declaredAll do
        if ss.any (·.mentions x) then
          throw s!"`return` in a branch declaring {x}, which the statements after it name"
      pure [.ite c (← lowerReturns r (t ++ ss)) (← lowerReturns r (e ++ ss))]
    else
      pure (.ite c (← lowerReturns r t) (← lowerReturns r e) :: (← lowerReturns r ss))
  | .tryCall e g as rets ok err code pnc other :: ss => do
    let bs := [ok, err, pnc, other]
    if bs.any (·.any RawStmt.hasReturn) && !ss.isEmpty then
      for x in (bs.flatten.flatMap RawStmt.declaredAll ++ rets.map (·.2) ++ code.toList) do
        if ss.any (·.mentions x) then
          throw s!"`return` in a clause declaring {x}, which the statements after it name"
      pure [.tryCall e g as rets (← lowerReturns r (ok ++ ss)) (← lowerReturns r (err ++ ss)) code
        (← lowerReturns r (pnc ++ ss)) (← lowerReturns r (other ++ ss))]
    else
      pure (.tryCall e g as rets (← lowerReturns r ok) (← lowerReturns r err) code
        (← lowerReturns r pnc) (← lowerReturns r other) :: (← lowerReturns r ss))
  | .unchecked b :: ss => do
    -- the statements after it would move into the block, and be unchecked
    if b.any RawStmt.hasReturn && !ss.isEmpty then
      throw "`return` inside `unchecked { … }` with statements after the block"
    pure (.unchecked (← lowerReturns r b) :: (← lowerReturns r ss))
  | s :: ss => do pure (s :: (← lowerReturns r ss))

/-! ### Loops, lowered

solkey's `LoopLowering` (`docs/loops.md`, Decision 2), shape for shape: a
loop's `break`, `continue` and `return` become fresh `bool` flags `brk`,
`cnt`, `ret`, made only when used; the rest of a block after a statement
that may set one runs under `if (!brk && !cnt && !ret) { … }`, testing only
the flags it may set; the loop's condition gets `!brk && !ret`; `for` and
`do … while` become a `while` (`RawStmt.loop`).  In an inlined body it runs
before `lowerReturns`, which then lowers the `if (ret) return;` after the
outermost loop as any early `return`. -/

/-- How a statement in a loop may end abruptly: solkey's `Abrupt`. -/
inductive Abrupt where
  | brk | cnt | ret
  deriving DecidableEq, Repr

/-- The kinds of `a` or `b`, in solkey's order (`brk`, `cnt`, `ret`). -/
def Abrupt.union (a b : List Abrupt) : List Abrupt :=
  [.brk, .cnt, .ret].filter fun k => a.contains k || b.contains k

/-- The flags of the loop being lowered (its `brk` and `cnt`, and the `ret`
the loops of one nest share), each made when first used; `inLoop` is false
outside every loop. -/
structure LoopFlags where
  brk : Option String := none
  cnt : Option String := none
  ret : Option String := none
  inLoop : Bool := false

/-- Lowering loops: the elaborator, and the flags of the loop being lowered. -/
abbrev LowerM := StateT LoopFlags ElabM

/-- The flag of `k`, made fresh on its first use (`brk1`, `cnt2`, `ret3`). -/
def LoopFlags.flag (k : Abrupt) : LowerM String := do
  let fl ← get
  let cur := match k with
    | .brk => fl.brk
    | .cnt => fl.cnt
    | .ret => fl.ret
  if let some x := cur then return x
  let x := toString (← freshCapture (match k with | .brk => "brk" | .cnt => "cnt" | .ret => "ret"))
  match k with
  | .brk => set { fl with brk := some x }
  | .cnt => set { fl with cnt := some x }
  | .ret => set { fl with ret := some x }
  pure x

/-- `e₁ && e₂ && … && c`, nested to the right as it reads. -/
def RawExpr.andAll (es : List RawExpr) (c : RawExpr) : RawExpr :=
  es.foldr (fun e acc => .binop .and e acc) c

/-- `!brk && !cnt && !ret`, of the flags of `ks`, before `c`; solkey's
`notAny`. -/
def notAny (ks : List Abrupt) (c : Option RawExpr := none) : LowerM RawExpr := do
  let gs ← ks.mapM fun k => do pure (RawExpr.unop .not (.name (← LoopFlags.flag k)))
  match c, gs.reverse with
  | some c, _ => pure (RawExpr.andAll gs c)
  | none, g :: rest => pure (RawExpr.andAll rest.reverse g)
  | none, [] => pure (.bool true)

/-- `bool x = b;` -/
def RawStmt.declBool (x : String) (b : Bool) : RawStmt := .decl (.named "bool") x (some (.bool b))

/-- `x = b;` -/
def RawStmt.setBool (x : String) (b : Bool) : RawStmt := .assign (.name x) (.bool b)

/-- A `break`, `continue` or `return`. -/
def RawStmt.isJump : RawStmt → Bool
  | .brk | .cont | .ret _ => true
  | _ => false

/-- Whether a `break`, `continue` or `return` occurs in the statement, at any
depth (solkey's `containsJump`). -/
partial def RawStmt.hasJump (s : RawStmt) : Bool :=
  s.isJump || s.blocks.any (·.any RawStmt.hasJump)

/-- Lower outside every loop: a `try`'s clauses inside a loop, which have no
jump. -/
def LowerM.outside {α : Type} (x : LowerM α) : LowerM α := do
  let fl ← get
  set ({} : LoopFlags)
  let r ← x
  set fl
  pure r

mutual

/-- A block, lowered: its statements, and how it may end abruptly.  After a
statement that may set a flag, the rest runs under `if (!flag…)`; after a
jump it is dropped. -/
partial def lowerList (rs : Option (List String)) :
    List RawStmt → LowerM (List RawStmt × List Abrupt)
  | [] => pure ([], [])
  | s :: ss => do
    let (s', ab) ← lowerStmt rs s
    if ab.isEmpty then
      let (ss', ab') ← lowerList rs ss
      pure (s' :: ss', ab')
    else if s.isJump then pure ([s'], ab)
    else
      let (ss', ab') ← lowerList rs ss
      if ss'.isEmpty then pure ([s'], ab)
      else pure ([s', .ite (← notAny ab) ss' []], Abrupt.union ab ab')

/-- A statement, lowered.  `rs` are the return variables of the body it is
in, none outside a function. -/
partial def lowerStmt (rs : Option (List String)) (s : RawStmt) :
    LowerM (RawStmt × List Abrupt) := do
  if s matches .whileLoop .. | .forLoop .. | .doWhile .. | .loop .. then return ← lowerLoop rs s
  let lowerB (b : List RawStmt) : LowerM (List RawStmt) := do pure (← lowerList rs b).1
  unless (← get).inLoop do
    return ← match s with
      | .block b => do pure (.block (← lowerB b), [])
      | .unchecked b => do pure (.unchecked (← lowerB b), [])
      | .ite c t e => do pure (.ite c (← lowerB t) (← lowerB e), [])
      | .tryCall e g as rets ok err code pnc other => do
        pure (.tryCall e g as rets (← lowerB ok) (← lowerB err) code (← lowerB pnc) (← lowerB other),
          [])
      | .brk => throw "`break` outside a loop"
      | .cont => throw "`continue` outside a loop"
      | s => pure (s, [])
  match s with
  | .brk => pure (.setBool (← LoopFlags.flag .brk) true, [.brk])
  | .cont => pure (.setBool (← LoopFlags.flag .cnt) true, [.cnt])
  | .ret e =>
    let some rs := rs | throw "`return` outside a function's body"
    let pre ← match e with
      | none => pure []
      | some e => ElabM.lift (lowerReturn rs e)
    pure (.block (pre ++ [.setBool (← LoopFlags.flag .ret) true]), [.ret])
  | .block b => do
    let (b', ab) ← lowerList rs b
    pure (.block b', ab)
  | .unchecked b => do
    let (b', ab) ← lowerList rs b
    pure (.unchecked b', ab)
  | .ite c t e => do
    let (t', a) ← lowerList rs t
    let (e', b) ← lowerList rs e
    pure (.ite c t' e', Abrupt.union a b)
  | .tryCall e g as rets ok err code pnc other => do
    if s.hasJump then throw "`break`, `continue` or `return` inside `try` inside a loop"
    LowerM.outside do
      pure (.tryCall e g as rets (← lowerB ok) (← lowerB err) code (← lowerB pnc) (← lowerB other),
        [])
  | s => pure (s, [])

/-- A loop, lowered to `RawStmt.loop`: `{ before; while (!brk && !ret && c)
{ bool cnt = false; body } }`, with what `for` and `do … while` add, and
`if (ret) return;` after the outermost loop of a nest with a `return`. -/
partial def lowerLoop (rs : Option (List String)) (s : RawStmt) :
    LowerM (RawStmt × List Abrupt) := do
  let (spec, c, init, upd, body, isDo) := match s with
    | .forLoop a i c u b => (a, c.getD (.bool true), i, u, b, false)
    | .doWhile a b c => (a, c, [], [], b, true)
    | .whileLoop a c b | .loop a c b => (a, c, [], [], b, false)
    | _ => ({}, .bool true, [], [], [], false)
  let outer ← get
  let outermost := !outer.inLoop
  set ({ ret := if outermost then none else outer.ret, inLoop := true } : LoopFlags)
  let (body', ab) ← lowerList rs body
  let exits := ab.filter (· != .cnt)
  let mut before : List RawStmt := init
  let mut iter : List RawStmt := []
  let mut cond := c
  -- the flags the condition reads, which an invariant says are `bool`s
  let mut heads : List String := []
  if isDo then
    let first := toString (← freshCapture "first")
    before := before ++ [.declBool first true]
    iter := [.setBool first false]
    cond := .binop .or (.name first) cond
    heads := heads ++ [first]
  if let some x := (← get).cnt then iter := iter ++ [.declBool x false]
  iter := iter ++ body'
  unless upd.isEmpty do
    if exits.isEmpty then iter := iter ++ upd
    else iter := iter ++ [.ite (← notAny exits) upd []]
  unless exits.isEmpty do cond ← notAny exits (some cond)
  let fl ← get
  if exits.contains .brk then heads := heads ++ fl.brk.toList
  if exits.contains .ret then heads := heads ++ fl.ret.toList
  if let some x := fl.brk then before := before ++ [.declBool x false]
  let returns := exits.contains .ret
  let retX := fl.ret.getD ""
  if returns && outermost then before := before ++ [.declBool retX false]
  set { outer with ret := if outermost then outer.ret else fl.ret }
  -- Lean's locals are untyped: an invariant says the flags its condition
  -- reads hold a `bool` (`f || !f` is defined exactly then), which KeY's
  -- types say of `brk`, `ret` and `first`
  let spec := if spec.inv.isEmpty then spec else
    { spec with inv := spec.inv ++ heads.map fun f => .binop .or (.name f) (.unop .not (.name f)) }
  let w := RawStmt.loop spec cond iter
  let ab' := if returns then [Abrupt.ret] else []
  if before.isEmpty && !(returns && outermost) then return (w, ab')
  if returns && outermost then
    return (.block (before ++ [w, .ite (.name retX) [.ret none] []]), [])
  pure (.block (before ++ [w]), ab')

end

/-- **Loops, lowered** in a block (`lowerList`), outside every loop. -/
def lowerLoops (rs : Option (List String)) (ss : List RawStmt) : ElabM (List RawStmt) := do
  pure (← (lowerList rs ss).run' {}).1

/-- Whether a `_;` occurs in the statement, at any depth. -/
partial def RawStmt.hasHole (s : RawStmt) : Bool :=
  s matches .hole || s.blocks.any (·.any RawStmt.hasHole)

/-- A modifier's body with each `_;` the block `inner`, at any depth.  Not
inside `unchecked`, as solc refuses it there. -/
partial def RawStmt.fillHole (inner : List RawStmt) (s : RawStmt) : Except String RawStmt :=
  let go := fun (b : List RawStmt) => b.mapM (RawStmt.fillHole inner)
  match s with
  | .hole => pure (.block inner)
  | .ite c t e => return .ite c (← go t) (← go e)
  | .block b => return .block (← go b)
  | .unchecked b =>
    if b.any RawStmt.hasHole then throw "`_;` inside `unchecked { … }`" else pure (.unchecked b)
  | .tryCall e g as rets ok err code pnc other =>
    return .tryCall e g as rets (← go ok) (← go err) code (← go pnc) (← go other)
  | .whileLoop a c b => return .whileLoop a c (← go b)
  | .doWhile a b c => return .doWhile a (← go b) c
  | .loop a c b => return .loop a c (← go b)
  | .forLoop a i c u b => return .forLoop a i c u (← go b)
  | s => pure s

/-- **Modifiers, inlined** around a function's body (its locals already
fresh), the first listed outermost, as solc runs them: a modifier's
parameters are declared fresh with its arguments (read in the function's
scope, and evaluated when the modifier is entered: after the code before
the `_;` of the modifiers outside it), then its body with each `_;` the
next modifier (or the function's body), as a block.  A modifier's locals are
renamed fresh, so the body cannot see them.  A `return` in a modifier is
not read; one in the body is its last statement (`lowerReturns`), so the
code after `_;` runs after it, as it does in solc.  A body run by several
`_;` (or by one in a loop) is run again in the same locals, its parameters
and return variables not reset: solc's legacy pipeline (via-IR resets
them). -/
partial def wrapMods (body : List RawStmt) : List ModApp → ElabM (List RawStmt)
  | [] => pure body
  | m :: ms => do
    let inner ← wrapMods body ms
    unless m.params.length == m.args.length do
      throw s!"modifier {m.name} takes {m.params.length} arguments, not {m.args.length}"
    if m.body.any RawStmt.hasReturn then throw s!"modifier {m.name}: `return` in a modifier"
    let mut ρ : List (String × String) := []
    let mut decls : List RawStmt := []
    for ((n, T), a) in m.params.zip m.args do
      let .prim p := T | throw s!"modifier {m.name}: the parameter {n} has a reference type"
      let y := toString (← freshCapture "se")
      decls := decls ++ [.decl (.named (primName p)) y (some a)]
      ρ := (n, y) :: ρ
    let code ← renameStmts ρ m.body
    pure (decls ++ (← ElabM.lift (code.mapM (RawStmt.fillHole inner))))

/-- The statements of `unchecked { … }` with their arithmetic wrapping: `x += 1;`
and `x++;` are `x = x +% 1;`.  A call's callee stays checked, as in solc. -/
partial def uncheckStmts : List RawStmt → Except String (List RawStmt)
  | [] => pure []
  | s :: ss => do
    let s' ← match s with
      | .opAssign op l e => do
        let op' : BinOp := match op with | .add => .addW | .sub => .subW | .mul => .mulW | op => op
        pure (.opAssign op' (← l.uncheck) (← e.uncheck))
      | .incDec op l => do
        pure (.opAssign (if op.isIncrement then .addW else .subW) (← l.uncheck) (.num 1))
      | .assignIncDec .. => throw "`v = x++;` inside `unchecked`: write `v = x; x += 1;`"
      | .ite c t e => do pure (.ite (← c.uncheck) (← uncheckStmts t) (← uncheckStmts e))
      | .unchecked b => do pure (.unchecked (← uncheckStmts b))
      | .block b => do pure (.block (← uncheckStmts b))
      | .tryCall e g as rets ok err code pnc other => do
        pure (.tryCall (← e.uncheck) g (← as.mapM RawExpr.uncheck) rets (← uncheckStmts ok)
          (← uncheckStmts err) code (← uncheckStmts pnc) (← uncheckStmts other))
      -- a loop's specification is not a program's arithmetic: it stays as written
      | .whileLoop a c b => do pure (.whileLoop a (← c.uncheck) (← uncheckStmts b))
      | .doWhile a b c => do pure (.doWhile a (← uncheckStmts b) (← c.uncheck))
      | .loop a c b => do pure (.loop a (← c.uncheck) (← uncheckStmts b))
      | .forLoop a i c u b => do
        pure (.forLoop a (← uncheckStmts i) (← c.mapM RawExpr.uncheck) (← uncheckStmts u)
          (← uncheckStmts b))
      | s => s.mapExprsM RawExpr.uncheck
    pure (s' :: (← uncheckStmts ss))

/-- Why a call of `f`, returning a `T` that is a reference, is refused. -/
def refReturnMsg (f : String) (T : Ty) : String :=
  s!"{f} returns a reference ({T}): a call's value is a value type"

mutual

/-- **Captures before a statement**: an `++`/`−−` inside an expression, and a
conditional of references, are evaluated before the statement that holds
them, in solc's order (an assignment's right-hand side before its target, a
binary operator's right operand before its left, an index's base before the
index: an operand read before an effect is captured with `captureExpr`),
into fresh locals (KeY's captures): `values[i++] = 1;`
is `uint se1; se1 = i++; values[se1] = 1;`, and
`Person storage p = c ? alice : bob;` is
`if (c) { Person storage sp1 = alice; } else { Person storage sp1 = bob; }
Person storage p = sp1;`.  Under the right operand of `&&`/`||` or in a
branch of a conditional an effect would be evaluated where the program does
not evaluate it, so there it is an error. -/
partial def hoist : RawExpr → ElabM (Prog C × RawExpr)
  | .field e f => do
    let (P, e) ← hoist e
    -- `rows[i].length` of a fixed-size `rows[i]`: the base is evaluated (and
    -- may revert) although the length is the literal, so it is captured
    if f == "length" && e.hasIndex then
      match synth C (← ctx) e with
      | .ok (.path (.ref (.fixed ..)) _) | .ok (.mpath (.ref (.fixed ..)) _) =>
        let (Pc, e) ← captureExpr C e
        return (P ++ Pc, .field e f)
      | _ => pure ()
    pure (P, .field e f)
  | .index e k => do
    -- the base first, then the index: `matrix[k][k++]` indexes `matrix[0]`
    let (P, e) ← hoist e
    if k.hasIncDec then
      let (Pc, e) ← captureExpr C e
      let (Q, k) ← hoist k
      pure (P ++ Pc ++ Q, .index e k)
    else if k.hasIdxLen || k.hasCast || hasNarrow C (← ctx) k then
      let (Q, k) ← hoist k
      pure (P ++ Q, .index e k)
    else pure (P, .index e k)
  | .binop op a b => do
    if op.shortCircuits then
      let (P, a) ← hoist a
      if b.hasCall then throw "a call under a short-circuit operator"
      if b.hasIncDec then throw "`++` or `−−` under a short-circuit operator"
      if hasNarrow C (← ctx) b then
        throw "narrow arithmetic under a short-circuit operator: its check would run where the program does not evaluate it"
      pure (P, .binop op a b)
    else
      let (P, e) ← hoistBinop op a b
      let (Q, e) ← narrowCapture C e
      pure (P ++ Q, e)
  | .unop op a => do
    let (P, a) ← hoist a
    let (Q, e) ← narrowCapture C (.unop op a)
    pure (P ++ Q, e)
  | .ternary c a b => do
    let (P, c) ← hoist c
    if a.hasCall || b.hasCall then throw "a call in a conditional's branch"
    if a.hasIncDec || b.hasIncDec then throw "`++` or `−−` in a conditional's branch"
    if hasNarrow C (← ctx) a || hasNarrow C (← ctx) b then
      throw "narrow arithmetic in a conditional's branch: its check would run where the program does not evaluate it"
    let Γ ← ctx
    match synth C Γ a, synth C Γ b with
    | .ok (.path (.ref R) pa), .ok (.path (.ref R') pb) =>
      if hR : R' = R then
        let c ← ElabM.lift (check C Γ .bool c)
        let x ← captureAs C "sp" (.alias R)
        pure (P ++ [.ite c [.declStorage R x (some (.path pa))]
          [.declStorage R x (some (.path (hR ▸ pb)))]], .name (toString x))
      else throw "a conditional of two reference types"
    | .ok (.mpath (.ref R) pa), .ok (.mpath (.ref R') pb) =>
      if hR : R' = R then
        let c ← ElabM.lift (check C Γ .bool c)
        let x ← captureAs C "mv" (.mem R)
        pure (P ++ [.ite c [.declMem R x (some (.alias pa)) rfl]
          [.declMem R x (some (.alias (hR ▸ pb))) rfl]], .name (toString x))
      else throw "a conditional of two reference types"
    | .ok (.path (.ref _) _), .ok (.mpath ..) | .ok (.mpath ..), .ok (.path (.ref _) _) =>
      throw "a conditional of a storage and a memory reference"
    | _, _ => pure (P, .ternary c a b)
  | .incDec op e => do
    let (P, e) ← hoist e
    let (pre, ⟨p, t, hs⟩) ← elabIncTarget C e
    match hp : p.isNumeric with
    | true =>
      let n := widthIn C (← ctx) e
      let x ← captureAs C "se" (.val p n)
      pure (P ++ pre ++ [.declLocal p x none, .assignIncDec x op hp t hs] ++ (← narrowCheck C p n e),
        .name (toString x))
    | false => throw s!"++ or −− at {primName p}"
  | .named f ns args => do
    -- the members' order; an effect may not move
    let flds := (structDef f).map (·.1)
    if flds.isEmpty then throw s!"{f}(\{…}): named arguments of a struct's constructor only"
    unless ns.length == flds.length && flds.all ns.contains do
      throw s!"{f}(\{…}) names each member of {f} once: {flds}"
    if ns != flds && args.any (·.hasIncDec) then
      throw s!"{f}(\{…}): an argument with an effect, out of the members' order"
    hoist (.call f (flds.map fun g => (lookupBy g (ns.zip args)).getD (.num 0)))
  | .call f args => do
    if (castTy? f).isSome then
      let [a] := args | throw s!"a cast {f}(…) takes one argument"
      let (P, a) ← hoist a
      let (Q, e) ← castCapture C f a
      return (P ++ Q, e)
    -- a struct's constructor (no function of that name): a fresh memory
    -- object, its members written in order, after the arguments are evaluated
    -- left to right (`T memory mv1; mv1.a = x; mv1.b = y;`)
    let flds := structDef f
    if (← read).all (·.1 != f) && !flds.isEmpty then
      let (P, args) ← hoistArgs args
      unless flds.length == args.length do
        throw s!"{f} has {flds.length} members, not {args.length}"
      let x := toString (← freshCapture "mv")
      let Q ← elabStmts (.declMemory (.named f) x none ::
        (flds.zip args).map fun ((g, _), a) => .assign (.field (.name x) g) a)
      return (P ++ Q, .name x)
    -- a call inside an expression runs before the statement, into a fresh local
    let (P, args) ← hoistArgs args
    let some (_, d) := (← read).find? (·.1 == f) | throw s!"{f} is not a function declared before this one"
    match d.ret with
      | some (r, .prim p) =>
        let n := (lookupBy r d.widths).getD 256
        let x ← freshCapture "se"
        let Q ← elabCall f args (some (x, p)) n
        declare C (toString x) (.val p n)
        pure (P ++ [.declLocal p x none] ++ Q, .name (toString x))
      | some (_, .ref R) =>
        -- `Account memory mv1 = makeAccount();`
        let x ← freshCapture "mv"
        let Q ← elabMemCall f args R fun r => .declMem R x (some (.alias (.var r))) rfl
        declare C (toString x) (.mem R)
        pure (P ++ Q, .name (toString x))
      | none =>
        if d.rets.isEmpty then throw s!"{f} returns no value"
        else throw s!"{f} returns {d.rets.length} values, which a tuple assignment takes"
  | .tuple _ => throw "a tuple is the right-hand side of a tuple assignment or of a `return`"
  | e => pure ([], e)

/-- `a ⊕ b`'s captures: the right operand first (solc evaluates it first: `i++ +
i` is `1 + 1`), the left one's after it, and the right one held before an
effect of the left. -/
partial def hoistBinop (op : BinOp) (a b : RawExpr) : ElabM (Prog C × RawExpr) := do
  let (Q, b) ← hoist b
  if a.hasIncDec then
    let (Qc, b) ← captureExpr C b
    let (P, a) ← hoist a
    pure (Q ++ Qc ++ P, .binop op a b)
  else if a.hasIdxLen || a.hasCast || hasNarrow C (← ctx) a then
    -- captures that may only revert: the right operand need not be held
    let (P, a) ← hoist a
    pure (Q ++ P, .binop op a b)
  else pure (Q, .binop op a b)

/-- `hoist`, but an operation at the top is left to the statement, which
checks its narrow width after the write (`narrowPost`). -/
partial def hoistTop : RawExpr → ElabM (Prog C × RawExpr)
  | .binop op a b => if op.shortCircuits then hoist (.binop op a b) else hoistBinop op a b
  | .unop op a => do
    let (P, a) ← hoist a
    pure (P, .unop op a)
  | e => hoist e

/-- `l = r;`: the right-hand side's captures, then the target's; an operation at
the top of `r` stays there when `l` is a variable (`hoistTop`). -/
partial def hoistAssign (l r : RawExpr) : ElabM (Prog C × RawStmt) := do
  let (P, r) ← if l matches .name _ then hoistTop r else hoist r
  let (Pc, r) ← if l.hasIncDec then captureExpr C r else pure ([], r)
  let (Q, l) ← hoist l
  pure (P ++ Pc ++ Q, .assign l r)

/-- A call's arguments, left to right: one read before a later argument's
effect is captured first, as a binary operator's operand is. -/
partial def hoistArgs : List RawExpr → ElabM (Prog C × List RawExpr)
  | [] => pure ([], [])
  | a :: as => do
    let (P, a) ← hoist a
    let (Pc, a) ← if as.any (·.hasIncDec) then captureExpr C a else pure ([], a)
    let (Q, as) ← hoistArgs as
    pure (P ++ Pc ++ Q, a :: as)

/-- **A call, inlined** (KeY's `FunctionBodyStatement`, then its body): `f`
is found among the functions the scope may call, its arguments are checked
at its parameters' types in the caller's scope, and its body is elaborated in
a scope of its own — its parameters and its return variable, every local
renamed fresh (`renameStmts`), then its `return`s lowered (`lowerReturns`) — with
the functions declared before `f`, so no call recurses.  `res` is the local
the returned value lands in, with its type. -/
partial def elabCall (f : String) (args : List RawExpr) (res : Option (Var × PrimTy))
    (resW : Nat := 256) : ElabM (Prog C) := do
  pure (← elabCallRet f args res resW).1

/-- A call of `f`, which returns a memory reference of type `R`, and `bind r`,
the statement that binds the callee's return variable `r` where the call
is: `Account memory mv1 = mv2;`, `m = mv2;` (the module docstring). -/
partial def elabMemCall (f : String) (args : List RawExpr) (R : RefTy) (bind : Var → Stmt C) :
    ElabM (Prog C) := do
  let (P, r, _) ← elabCallRet f args none
  match r with
  | some ⟨R', r⟩ =>
    unless R' = R do throw s!"{f} returns a {Ty.ref R'}, not a {Ty.ref R}"
    pure (P ++ [bind r])
  | none => throw s!"{f} does not return a memory reference"

/-- `elabCall`, and the fresh return variable of a callee that returns a
memory reference, with its type: the body's first statement declares it (a
fresh default object) and the call returns nothing (`CallRet.none`), the
caller binding it after the call (`elabMemCall`).  With `targets`, the
call is a tuple assignment's right-hand side (`elabTuple`), KeyTaclets'
`FunctionBodyStatement` with targets: it returns every return value
(`CallRet.rets`, one or several), which the caller reads after the call —
their fresh variables, types and widths.  A callee of several returns called
as a statement (`f(a);`, KeY's `InternalCall`) declares them at the head of
its body and returns nothing. -/
partial def elabCallRet (f : String) (args : List RawExpr) (res : Option (Var × PrimTy))
    (resW : Nat := 256) (targets : Bool := false) :
    ElabM (Prog C × Option (RefTy × Var) × List (PrimTy × Var × Nat)) := do
  let funs ← read
  let some i := funs.findIdx? (·.1 == f) | throw s!"{f} is not a function declared before this one"
  let d := (funs[i]?.map (·.2)).getD default
  unless d.params.length == args.length do
    throw s!"{f} takes {d.params.length} arguments, not {args.length}"
  let Γ ← ctx
  let mut targs : List (Arg C) := []
  let mut ρ : List (String × String) := []
  let mut Γf : ECtx := []
  for ((n, T), a) in d.params.zip args do
    let .prim p := T | throw s!"{f}: the parameter {n} has a reference type"
    let w := (lookupBy n d.widths).getD 256
    ElabM.lift (fitCheck C Γ p w a)
    let e ← ElabM.lift (check C Γ p a)
    let x ← freshCapture "se"
    targs := targs ++ [⟨p, x, e⟩]
    ρ := (n, toString x) :: ρ
    Γf := setBy (toString x) (.val p w) Γf
  let mut mret : Option (RefTy × Var) := none
  let mut mrets : List (PrimTy × Var × Nat) := []
  let ret ← match d.rets, res with
    -- a void call with targets (a void function's obligation, `f(x̄)@C;`)
    -- is a `FunctionBodyStatement` all the same
    | [], none => pure (if targets then CallRet.rets [] else CallRet.none)
    | [], some _ => throw s!"{f} returns no value"
    | [(n, .ref R)], none => do
      if targets then throw s!"{f} returns a {Ty.ref R}, which a tuple assignment does not take"
      unless d.retMem do throw s!"{f}: its return of reference type {Ty.ref R} needs the location `memory`"
      let r ← freshCapture "mv"
      ρ := (n, toString r) :: ρ
      Γf := setBy (toString r) (.mem R) Γf
      mret := some ⟨R, r⟩
      pure CallRet.none
    | [(_, .ref R)], some (_, q) => throw s!"{f} returns a memory {Ty.ref R}, not a {primName q}"
    | [(n, .prim p)], res => do
      if d.retMem then throw s!"{f}: `memory` on its return of value type {primName p}"
      if let some (_, q) := res then
        unless q = p do throw s!"{f} returns a {primName p}, not a {primName q}"
      let w := (lookupBy n d.widths).getD 256
      if resW < w then throw s!"{f} returns a {tyName p w}, where a {tyName p resW} is expected"
      let r ← freshCapture "se"
      ρ := (n, toString r) :: ρ
      Γf := setBy (toString r) (.val p w) Γf
      if targets then
        mrets := [(p, r, w)]
        pure (CallRet.rets [(p, r)])
      else pure (CallRet.val p r (res.map (·.1)))
    | rs, some _ => throw s!"{f} returns {rs.length} values, which a tuple assignment takes"
    | rs, none => do
      if d.retMem then throw s!"{f}: `memory` on a return of a function of several returns"
      for (n, T) in rs do
        let .prim p := T | throw s!"{f}: its return {n} has a reference type"
        let w := (lookupBy n d.widths).getD 256
        let r ← freshCapture "se"
        ρ := (n, toString r) :: ρ
        Γf := setBy (toString r) (.val p w) Γf
        mrets := mrets ++ [(p, r, w)]
      if targets then pure (CallRet.rets (mrets.map fun (p, r, _) => (p, r))) else pure CallRet.none
  let body ← renameStmts ρ d.body
  let body ← lowerLoops (some (d.rets.map fun (n, _) => (lookupBy n ρ).getD n)) body
  let body ← ElabM.lift (lowerReturns (d.rets.map fun (n, _) => (lookupBy n ρ).getD n) body)
  let body ← wrapMods body (d.mods.map fun m => { m with args := m.args.map (·.rename ρ) })
  modify fun (_, k) => (Γf, k)
  let P ← withReader (fun _ => funs.take i) (elabStmts body)
  modify fun (_, k) => (Γ, k)
  -- a memory return variable: declared on entry, a fresh default object
  let P ← match mret with
    | none => pure P
    | some ⟨R, r⟩ =>
      match hd : (Ty.ref R).defaultOkS with
      | true => pure (Stmt.declMem R r none (by simp [hd]) :: P)
      | false => throw s!"{f} returns a {Ty.ref R}, whose default is not well-formed"
  -- several returns of a call that is a statement: declared on entry, at their defaults
  let P := if targets then P else mrets.map (fun (p, r, _) => Stmt.declLocal p r none) ++ P
  match hsep : Arg.separatedFrom [] targs with
  | true => pure ([.call f targs hsep ret P], mret, mrets)
  | false => throw s!"{f}: an argument reads a parameter"

/-- The captures a statement's own expressions need (`hoist`), and the
statement left: a right-hand side before the left-hand side, as the
interpreter evaluates them, a receiver before an argument.  A branch's statements are elaborated on their
own. -/
partial def hoistStmt : RawStmt → ElabM (Prog C × RawStmt)
  | .assign l r => do
    -- `m = f(a);` to a memory local: its arguments only (`elabStmt1`)
    if let .call f args := r then
      if (← read).any (·.1 == f) && synth C (← ctx) l matches .ok (.mpath (.ref _) (.var _)) then
        let (P, args) ← hoistArgs args
        return (P, .assign l (.call f args))
    match r, synth C (← ctx) l with
    | .incDec op e, .ok (.val _ (.simple (.local _))) =>
      let (P, e) ← hoist e
      pure (P, .assignIncDec l op e)
    | .newArr T n, _ =>
      let (Q, l) ← hoist l
      pure (Q, .assign l (.newArr T n))
    | .call f args, .ok (.val _ (.simple (.local _))) =>
      if (castTy? f).isSome then hoistAssign l r
      else
        let (P, args) ← hoistArgs args
        pure (P, .assign l (.call f args))
    | _, _ => hoistAssign l r
  | .decl T x (some (.call f args)) => do
    if (castTy? f).isSome then
      let (P, r) ← hoist (.call f args)
      return (P, .decl T x (some r))
    let (P, args) ← hoistArgs args
    pure (P, .decl T x (some (.call f args)))
  | .decl T x (some r) => do
    let (P, r) ← hoistTop r
    pure (P, .decl T x (some r))
  | .declMemory T x (some (.newArr T' n)) => pure ([], .declMemory T x (some (.newArr T' n)))
  -- a statement of one expression: its captures, then the statement
  | s@(.decl ..) | s@(.declStorage ..) | s@(.declMemory ..) | s@(.declStoragePush ..)
  | s@(.delete _) | s@(.incDec ..) | s@(.ite ..) | s@(.require _) | s@(.assert _)
  | s@(.tryCall ..) => do
    -- `T memory x = f(a);`: its arguments only (`elabStmt1`)
    if let .declMemory T x (some (.call f args)) := s then
      if (← read).any (·.1 == f) then
        let (P, args) ← hoistArgs args
        return (P, .declMemory T x (some (.call f args)))
    let (s, P) ← (s.mapExprsM fun e => do
      let (Q, e) ← hoist e
      modify (· ++ Q)
      pure e : StateT (Prog C) ElabM RawStmt).run []
    pure (P, s)
  | .opAssign op l r => do
    let (P, r) ← hoist r
    let (Pc, r) ← if l.hasIncDec then captureExpr C r else pure ([], r)
    let (Q, l) ← hoist l
    pure (P ++ Pc ++ Q, .opAssign op l r)
  | .assignIncDec x op l => do
    let (P, l) ← hoist l
    pure (P, .assignIncDec x op l)
  | .call (.field e m) args => do
    -- the receiver first, then the arguments
    let (P, e) ← hoist e
    let (Pc, e) ← if args.any (·.hasIncDec) && !(e matches .name _) then captureExpr C e
      else pure ([], e)
    let mut Q := P ++ Pc
    let mut args' := []
    for a in args do
      let (Q', a) ← hoist a
      Q := Q ++ Q'
      args' := args' ++ [a]
    pure (Q, .call (.field e m) args')
  | .call (.name f) args => do
    let (P, args) ← hoistArgs args
    pure (P, .call (.name f) args)
  | .assignPush l b => do
    let (P, b) ← hoist b
    let (Q, l) ← hoist l
    pure (P ++ Q, .assignPush l b)
  | .send T x r a => do
    -- the receiver first, then the amount, as `transfer`'s
    let (P, r) ← hoist r
    let (Pc, r) ← if a.hasIncDec && !(r matches .name _) then captureExpr C r
      else pure ([], r)
    let (Q, a) ← hoist a
    pure (P ++ Pc ++ Q, .send T x r a)
  | .eval args => do
    -- the effects captured, left to right; then what may still revert is
    -- evaluated into a fresh local, which nothing reads
    let (P, args) ← hoistArgs args
    let mut Q := P
    for a in args do
      unless a.isPure do Q := Q ++ (← captureExpr C a).1
    pure (Q, .eval [])
  | s => pure ([], s)

/-- A statement, as a block: its narrow rewrites (`narrowPure`), its captures
(`hoistStmt`), then the statement,
whose compound target may need a capture of its own. -/
partial def elabStmt (s : RawStmt) : ElabM (Prog C) := do
  -- a loop outside a function's body, lowered here (`lowerLoops`)
  if s matches .whileLoop .. | .forLoop .. | .doWhile .. then
    return ← elabStmts (← lowerLoops none [s])
  let s ← ElabM.lift (s.mapExprsM (narrowPure C (← ctx)))
  let (P, s) ← hoistStmt s
  pure (P ++ (← elabStmt1 s))

/-- A statement whose expressions have no effect left. -/
partial def elabStmt1 : RawStmt → ElabM (Prog C)
  | .assign l (.newArr T n) => do
    let ⟨R, hR⟩ ← elabNewTy C T
    let (P, se) ← elabSize C n
    match ← synthM C l with
    | .mpath (.ref R') (.var x) =>
      if R' = R then pure (P ++ [.rebindMem (R := R) x (.newArr se hR)])
      else throw "`new` of another type than the memory local's"
    | .mpath T' (.loc ml) =>
      if hT : T' = .ref R then pure (P ++ [.assignNew (.mem (hT ▸ ml)) se hR])
      else throw "`new` of another type than the member's"
    | .path T' (.loc sl) =>
      if hT : T' = .ref R then pure (P ++ [.assignNew (.store (hT ▸ sl)) se hR])
      else throw "`new` of another type than the location's"
    | .path _ (.alias _) => throw "a storage pointer bound to a memory array"
    | .val .. => throw "`new` assigned to a value"
  | .assign l (.call f args) => do
    match ← synthM C l with
    | .val p (.simple (.local x)) => elabCall f args (some (x, p)) (widthIn C (← ctx) l)
    | .mpath (.ref R) (.var x) => elabMemCall f args R fun r => .rebindMem (R := R) x (.alias (.var r))
    | _ => throw "a call's value is assigned to a stack local"
  | .assign l r => do
    let post ← narrowPost C l r
    let Γ ← ctx
    let P : Prog C ← match ← synthM C l with
      | .val p (.simple (.local x)) => do pure [.assignLocal x (← checkM C p r)]
      | .val p _ => throw s!"{l.toStr} is a {p.toStr} value, not a place to assign to"
      | .path (.prim p) (.loc l) => do pure [.assign l (.val (← checkM C p r))]
      | .path (.ref R) (.loc l) => do
        match ← synthM C r with
        | .mpath T mp =>
          if hT : T = .ref R then pure [.assignFromMem l (hT ▸ mp)]
          else throw s!"{r.toStr}: a memory reference to a {T} where a {Ty.ref R} is expected"
        | _ =>
          match h : (Ty.ref R).mapFree with
          | true => do pure [.assign l (.copy (← checkPath C Γ (.ref R) r) h)]
          | false => throw "a storage copy of a type that holds a mapping"
      | .path (.ref R) (.alias x) => do pure [.rebind x (.path (← checkPath C Γ (.ref R) r))]
      | .mpath (.ref R) (.var x) => do pure [.rebindMem x (← elabMRhs C Γ R r)]
      | .mpath (.prim p) (.loc l) => do pure [.assignMem l (.val (← checkM C p r))]
      | .mpath (.ref R) (.loc l) => do pure [.assignMem l (.ref (← checkMPath C Γ (.ref R) r))]
    pure (P ++ post)
  | .decl T x (some (.call f args)) => do
    let (.prim p, n) ← ElabM.lift (elabDeclTy C T) | throw s!"{x}: a reference type needs a data location"
    let P ← elabCall f args (some (Var.ofName x, p)) n
    declare C x (.val p n)
    pure (.declLocal p (Var.ofName x) none :: P)
  | .decl T x init => do
    let (.prim p, n) ← ElabM.lift (elabDeclTy C T) | throw s!"{x}: a reference type needs a data location"
    let v ← init.mapM (checkM C p)
    declare C x (.val p n)
    let post ← match init with
      | some r => narrowPost C (.name x) r
      | none => pure []
    pure (.declLocal p (Var.ofName x) v :: post)
  | .declStorage T x init => do
    let .ref R ← ElabM.lift (elabTy C T) | throw s!"{x}: `storage` on a value type"
    let Γ ← ctx
    let init ← ElabM.lift (init.mapM fun e => ARhs.path <$> checkPath C Γ (.ref R) e)
    declare C x (.alias R)
    pure [.declStorage R (Var.ofName x) init]
  | .declStoragePush T x b => do
    let .ref R ← ElabM.lift (elabTy C T) | throw s!"{x}: `storage` on a value type"
    let Γ ← ctx
    let r ← elabPush C Γ R b
    declare C x (.alias R)
    pure [.declStorage R (Var.ofName x) (some r)]
  | .assignPush l b => do
    let Γ ← ctx
    match ← synthM C l with
    | .path (.ref R) (.alias x) => pure [.rebind x (← elabPush C Γ R b)]
    | _ => throw "`= b.push()` binds a storage pointer"
  | .declMemory T x (some (.newArr T' n)) => do
    let .ref R ← ElabM.lift (elabTy C T) | throw s!"{x}: `memory` on a value type"
    let ⟨R', hR⟩ ← elabNewTy C T'
    unless R' = R do throw s!"{x}: `new` of another type"
    let (P, se) ← elabSize C n
    declare C x (.mem R')
    pure (P ++ [.declMem R' (Var.ofName x) (some (.newArr se hR)) rfl])
  | .declMemory T x (some (.call f args)) => do
    let .ref R ← ElabM.lift (elabTy C T) | throw s!"{x}: `memory` on a value type"
    let P ← elabMemCall f args R fun r => .declMem R (Var.ofName x) (some (.alias (.var r))) rfl
    declare C x (.mem R)
    pure P
  | .declMemory T x init => do
    let .ref R ← ElabM.lift (elabTy C T) | throw s!"{x}: `memory` on a value type"
    let Γ ← ctx
    let s ← match init with
      | some e => pure (Stmt.declMem R (Var.ofName x) (some (← elabMRhs C Γ R e)) rfl)
      | none =>
        match hd : (Ty.ref R).defaultOkS with
        | true => pure (Stmt.declMem R (Var.ofName x) none (by simp [hd]))
        | false => throw s!"{x}: a memory object whose default is not well-formed"
    declare C x (.mem R)
    pure [s]
  | .delete e => do
    match ← synthM C e with
    | .path T (.loc l) =>
      if T matches .ref (.mapping ..) then throw "a mapping cannot be deleted"
      else pure [.delete l]
    | .path _ (.alias _) => throw "`delete` on a storage pointer"
    | .mpath T p =>
      match hd : T.defaultOkS with
      | true => pure [.deleteMem p hd]
      | false => throw "`delete` of a memory object whose default is not well-formed"
    | .val .. => throw "`delete` needs a storage or a memory location"
  | .opAssign op l r => do
    -- `&= |= ^= <<= >>=` and a wrapping `+=`: `l = l ⊕ r`, the target's
    -- effects already captured (`hoistStmt`), so reading it twice is safe
    if op.isArith && !op.hasCompoundAssign && op != .pow then
      return ← elabStmt1 (.assign l (← ElabM.lift (narrowWrapNode C (← ctx) (.binop op l r))))
    let (pre, ⟨p, t⟩) ← elabOpTarget C l
    -- at a narrow target, what `l ⊕ r` may leave the type by is checked after
    let n := widthIn C (← ctx) l
    ElabM.lift (fitCheck C (← ctx) p n r)
    let post ← if (op matches .add | .sub | .mul) || (op == .div && p == .int) then
      narrowCheck C p n l else pure []
    match hop : op.hasCompoundAssign, hp : p.isNumeric with
    | true, true => pure (pre ++ [.opAssign op hop hp t (← checkM C p r)] ++ post)
    | false, _ => throw s!"no compound assignment for {BinOp.sym op}"
    | _, false => throw s!"a compound assignment at {primName p}"
  | .incDec op l => do
    let (pre, ⟨p, t⟩) ← elabOpTarget C l
    match hp : p.isNumeric with
    | true => pure (pre ++ [.incDec op hp t] ++ (← narrowCheck C p (widthIn C (← ctx) l) l))
    | false => throw s!"++ or −− at {primName p}"
  | .assignIncDec x op l => do
    let (pre, ⟨p, t, hs⟩) ← elabIncTarget C l
    match ← synthM C x with
    | .val q (.simple (.local y)) =>
      ElabM.lift (fitCheck C (← ctx) q (widthIn C (← ctx) x) l)
      match hp : p.isNumeric with
      | true => if q = p then
                  pure (pre ++ [.assignIncDec y op hp t hs] ++ (← narrowCheck C p (widthIn C (← ctx) l) l))
                else throw s!"a {primName p} assigned to a {primName q}"
      | false => throw s!"++ or −− at {primName p}"
    | _ => throw "the result of ++ or −− goes to a stack local"
  | .call (.field e "push") args => do
    let Γ ← ctx
    let .path (.ref (.array E)) b ← synthM C e | throw "push on something that is not an array"
    match args with
    | [] =>
      match hd : E.defaultOkS with
      | true => pure [.push b none (by simp [hd])]
      | false => throw "push() of an element whose default is not well-formed"
    | [a] =>
      match E with
      | .prim p => pure [.push b (some (.val (← checkM C p a))) rfl]
      | .ref R =>
        -- a memory object (a struct's constructor): a default slot pushed,
        -- then written with its copy
        if (← synthM C a) matches .mpath .. then
          return ← elabStmts [.call (.field e "push") [],
            .assign (.index e (.binop .sub (.field e "length") (.num 1))) a]
        match h : (Ty.ref R).mapFree with
        | true => pure [.push b (some (.copy (← checkPath C Γ (.ref R) a) h)) rfl]
        | false => throw "a push copying a type that holds a mapping"
    | _ => throw "push takes at most one argument"
  | .call (.field e "pop") [] => do
    let .path (.ref (.array _)) b ← synthM C e | throw "pop on something that is not an array"
    pure [.pop b]
  | .call (.field e "transfer") [a] => do
    pure [.transfer (← checkM C .uint e) (← checkM C .uint a)]
  | .send T x e a => do
    let r ← checkM C .uint e
    let v ← checkM C .uint a
    match T, x with
    | some T, .name n =>
      let (.prim .bool, w) ← ElabM.lift (elabDeclTy C T)
        | throw s!"{n}: `send` returns a bool"
      declare C n (.val .bool w)
      pure [.declLocal .bool (Var.ofName n) none, .send (Var.ofName n) r v]
    | some _, _ => throw "`T x = r.send(a);` declares a name"
    | none, x =>
      match ← synthM C x with
      | .val .bool (.simple (.local y)) => pure [.send y r v]
      | _ => throw s!"{x.toStr}: a send's result goes to a bool local"
  | .call (.name f) args => elabCall f args none
  | .call .. => throw "only push, pop and transfer are calls on a receiver"
  | .ret _ => throw "`return` outside a function's body"
  | .brk => throw "`break` outside a loop"
  | .cont => throw "`continue` outside a loop"
  | .hole => throw "`_;` outside a modifier's body"
  | s@(.whileLoop ..) | s@(.forLoop ..) | s@(.doWhile ..) => do elabStmts (← lowerLoops none [s])
  | .loop a c body => do
    -- evaluated again each iteration, so it is not captured before the loop
    let c ← loopExpr .bool c "condition"
    let a ← match a.inv, a.unwind with
      | [], u => do
        if a.dec.isSome then throw "a loop's `decreases` clause without an `invariant`"
        pure (LoopAnn.unwind (u.getD 0))
      | i :: is, none => do
        let I ← loopExpr .bool (RawExpr.andAll (i :: is).dropLast ((i :: is).getLast?.getD i))
          "invariant"
        pure (.inv I (← a.dec.mapM fun d => loopExpr .uint d "variant"))
      | _ :: _, some _ => throw "a loop has an `invariant` or an `unwind` clause, not both"
    pure [.loop a c (← elabBranch body)]
  | .block b => elabBranch b
  | .tupleAssign ts rhs => elabTuple ts rhs
  | .tupleDecl vs rhs => do
    -- `T x;` for each variable, then the tuple assigned to them
    for (_, x) in vs.filterMap id do
      if rhs.mentions x then throw s!"{rhs.toStr} reads {x}, which the tuple declares"
    let P ← elabStmts (vs.filterMap fun v => v.map fun (T, x) => .decl T x none)
    pure (P ++ (← elabTuple (vs.map fun v => v.map fun (_, x) => .name x) rhs (direct := true)))
  | .ite c thn els => do
    let c ← checkM C .bool c
    let thn ← elabBranch thn
    let els ← elabBranch els
    pure [.ite c thn els]
  | .require c => do
    pure [.require (← checkM C .bool c)]
  | .assert c => do
    pure [.assert (← checkM C .bool c)]
  | .revert => pure [.revert]
  | .eval _ => pure []
  | .unchecked ss => do elabBranch (← ElabM.lift (uncheckStmts ss))
  | .tryCall e g as rets ok err code pnc other => do
    -- `I(a)` is `a`
    let funs ← read
    let e := match e with
      | .call h [a] => if funs.any (·.1 == h) then e else a
      | e => e
    let (P, addr) ← simpleOf C .uint e
    let mut Q := P
    let mut args : List (ExtArg C) := []
    for a in as do
      let some ⟨p, _⟩ := (← synthM C a).toVal? | throw s!"{a.toStr}: an external call's argument is a value"
      let (Q', se) ← simpleOf C p a
      Q := Q ++ Q'
      args := args ++ [⟨p, se⟩]
    let mut rets' : List (PrimTy × Var) := []
    for (T, x) in rets do
      let (.prim p, n) ← ElabM.lift (elabDeclTy C T) | throw s!"{x}: an external call returns a value"
      unless n == 256 do throw s!"{x}: a narrow return value of an external call"
      rets' := rets' ++ [(p, Var.ofName x)]
    let (Γ, _) ← get
    for (p, x) in rets' do declare C (toString x) (.val p)
    let ok ← elabStmts ok
    let (_, k) ← get
    set (Γ, k)
    let err ← elabBranch err
    if let some c := code then declare C c (.val .uint)
    let pnc ← elabStmts pnc
    let (_, k) ← get
    set (Γ, k)
    let other ← elabBranch other
    pure (Q ++ [.tryCall ⟨addr, g, args⟩ rets' ok err (code.map Var.ofName) pnc other])

/-- A loop's condition, invariant or variant, of type `p` (its narrow
rewrites done, `elabStmt`): nothing may be captured before it, since it is
evaluated where the loop is, again.  So an effect, a call to a declared
function, a cast, a narrow operation that needs a capture or a struct
constructor in it is refused (`docs/loops.md`), where solkey evaluates it
per iteration. -/
partial def loopExpr (p : PrimTy) (e : RawExpr) (what : String) : ElabM (Val C p) := do
  let st ← get
  let (P, _) ← hoist e
  set st
  unless P.isEmpty do
    throw s!"{e.toStr}: a loop's {what} needs a statement before it (an effect, a call, \
      a cast, a narrow operation or a constructor), and is evaluated again each iteration"
  checkM C p e

/-- A block. -/
partial def elabStmts : List RawStmt → ElabM (Prog C)
  | [] => pure []
  | s :: ss => do
    let P ← elabStmt s
    let Q ← elabStmts ss
    pure (P ++ Q)

/-- A branch: its declarations stay inside it. -/
partial def elabBranch (ss : List RawStmt) : ElabM (Prog C) := do
  let (Γ, _) ← get
  let P ← elabStmts ss
  let (_, k) ← get
  set (Γ, k)
  pure P

/-- **A tuple assignment** `(t₀, , t₂) = e;`, written out as solkey's
`ParserUtils.tupleAssignment` writes it.  From a call of a function of several
returns: the call (`CallRet.rets`), then `tᵢ = rᵢ;` for each target, left to
right (a component left out is not read).  From a tuple `(e₀, e₁, e₂)`: each
component with a target into a fresh temporary, left to right, then each
target assigned its temporary, left to right; a component left out is
dropped if it can neither revert nor have an effect, and evaluated
otherwise (solc's; solkey keeps only a call).  Targets that may alias (the same name
twice, two that are not stack locals, one that reads another) are refused:
solc's order of their writes is not KeY's.  The variables of a tuple
declaration, which no component reads, are assigned directly (`direct`). -/
partial def elabTuple (ts : List (Option RawExpr)) (rhs : RawExpr) (direct : Bool := false) :
    ElabM (Prog C) := do
  let tgts := ts.filterMap id
  let mut nonLocal := 0
  for t in tgts do
    if t.hasIncDec then throw s!"{t.toStr}: a tuple's target with an effect"
    unless (← synthM C t) matches .val _ (.simple (.local _)) do nonLocal := nonLocal + 1
    for u in tgts do
      if let .name x := u then
        if t.toStr != u.toStr && t.mentions x then throw s!"{t.toStr}: a tuple's target that reads {x}, another"
  if nonLocal > 1 then throw "a tuple assignment to two targets that are not stack locals"
  unless (tgts.map (·.toStr)).eraseDups.length == tgts.length do
    throw "a tuple assignment to the same target twice"
  match rhs with
  | .call f args =>
    -- a function not declared before this one is `elabCallRet`'s error
    unless (castTy? f).isNone do
      throw s!"{f}(…): the right-hand side of a tuple assignment is a call of a function"
    let (P, args) ← hoistArgs args
    let (Q, _, rs) ← elabCallRet f args none (targets := true)
    unless rs.length == ts.length do throw s!"{f} returns {rs.length} values, not {ts.length}"
    for (p, r, w) in rs do declare C (toString r) (.val p w)
    let R ← elabStmts ((ts.zip rs).filterMap fun (t, (_, r, _)) =>
      t.map fun t => .assign t (.name (toString r)))
    pure (P ++ Q ++ R)
  | .tuple es =>
    unless es.length == ts.length do throw s!"a tuple of {es.length} values assigned to {ts.length}"
    let mut tmps : List RawStmt := []
    let mut asgs : List RawStmt := []
    for (t, e) in ts.zip es do
      match t with
      | some t =>
        if direct then
          tmps := tmps ++ [.assign t e]
          continue
        let p ← match ← synthM C t with
          | .val p _ | .path (.prim p) _ | .mpath (.prim p) _ => pure p
          | _ => throw s!"{t.toStr}: a tuple's component of a reference type"
        let x := toString (← freshCapture "se")
        tmps := tmps ++ [.decl (.named (tyName p (widthIn C (← ctx) t))) x (some e)]
        asgs := asgs ++ [.assign t (.name x)]
      | none => unless e.isPure do tmps := tmps ++ [.eval [e]]
    elabStmts (tmps ++ asgs)
  | _ => throw s!"{rhs.toStr}: the right-hand side of a tuple assignment is a tuple or a call"

end

/-- Elaborate a block against `C`, from no locals.  A capture is numbered
past every fresh variable the block writes. -/
def elabProg (ss : List RawStmt) : Except String (Prog C) :=
  ((elabStmts C ss).run C.funs).run' ([], RawStmt.maxIdxs ss + 1)

/-- `elabProg`, an error naming the statement of the block it arose in (its
position): the same block, statement by statement. -/
def elabProgAt (ss : List RawStmt) : Except (Nat × String) (Prog C) :=
  go 0 ss ([], RawStmt.maxIdxs ss + 1)
where
  go (i : Nat) : List RawStmt → ECtx × Nat → Except (Nat × String) (Prog C)
    | [], _ => pure []
    | s :: ss, st =>
      match ((elabStmt C s).run C.funs).run st with
      | .error e => .error (i, e)
      | .ok (P, st) => do pure (P ++ (← go (i + 1) ss st))

end Elab

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

def Simple.quote : (p : PrimTy) → Simple C p → Lean.Expr
  | p, .lit n _ => mkAppN (mkConst ``Simple.lit) #[c, toExpr p, toExpr n, rflTrue]
  | _, .bool b => mkAppN (mkConst ``Simple.bool) #[c, toExpr b]
  | p, .local x => mkAppN (mkConst ``Simple.local) #[c, toExpr p, toExpr x]
  | p, .env k _ => mkAppN (mkConst ``Simple.env) #[c, toExpr p, toExpr k,
      rflPrim p]

mutual

def SPath.quote : (T : Ty) → SPath C T → Lean.Expr
  | .ref R, .alias x => mkAppN (mkConst ``SPath.alias) #[c, toExpr R, toExpr x]
  | T, .loc l => mkAppN (mkConst ``SPath.loc) #[c, toExpr T, Loc.quote T l]

def Loc.quote : (T : Ty) → Loc C T → Lean.Expr
  | T, .root r _ => mkAppN (mkConst ``Loc.root) #[c, toExpr T, toExpr r, rflSome T]
  | T, @Loc.field _ s _ b f _ =>
    mkAppN (mkConst ``Loc.field) #[c, toExpr s, toExpr T, SPath.quote _ b, toExpr f, rflSome T]
  | V, @Loc.index _ R k _ it b i =>
    mkAppN (mkConst ``Loc.index) #[c, toExpr R, toExpr k, toExpr V, IndexTy.quote it,
      SPath.quote _ b, Val.quote k i]

def MPath.quote : (T : Ty) → MPath C T → Lean.Expr
  | .ref R, .var x => mkAppN (mkConst ``MPath.var) #[c, toExpr R, toExpr x]
  | T, .loc l => mkAppN (mkConst ``MPath.loc) #[c, toExpr T, MLoc.quote T l]

def MLoc.quote : (T : Ty) → MLoc C T → Lean.Expr
  | T, @MLoc.field _ s _ b f _ =>
    mkAppN (mkConst ``MLoc.field) #[c, toExpr s, toExpr T, MPath.quote _ b, toExpr f, rflSome T]
  | E, @MLoc.index _ R _ a b i =>
    mkAppN (mkConst ``MLoc.index) #[c, toExpr R, toExpr E, ArrTy.quote a, MPath.quote _ b,
      Val.quote .uint i]

def Val.quote : (p : PrimTy) → Val C p → Lean.Expr
  | p, .simple s => mkAppN (mkConst ``Val.simple) #[c, toExpr p, Simple.quote c p s]
  | p, .read l => mkAppN (mkConst ``Val.read) #[c, toExpr p, Loc.quote _ l]
  | _, @Val.binop _ p q op _ _ a b =>
    mkAppN (mkConst ``Val.binop) #[c, toExpr p, toExpr q, toExpr op, rflTrue,
      rflPrim q, Val.quote p a, Val.quote p b]
  | _, @Val.unop _ p q op _ _ a =>
    mkAppN (mkConst ``Val.unop) #[c, toExpr p, toExpr q, toExpr op, rflTrue,
      rflPrim q, Val.quote p a]
  | p, .ternary cv a b =>
    mkAppN (mkConst ``Val.ternary) #[c, toExpr p, Val.quote .bool cv, Val.quote p a, Val.quote p b]
  | p, .readMem l => mkAppN (mkConst ``Val.readMem) #[c, toExpr p, MLoc.quote _ l]
  | p, @Val.len _ _ E b _ => mkAppN (mkConst ``Val.len) #[c, toExpr p, toExpr E, SPath.quote _ b,
      rflPrim p]
  | p, @Val.mlen _ _ E b _ => mkAppN (mkConst ``Val.mlen) #[c, toExpr p, toExpr E, MPath.quote _ b,
      rflPrim p]

end

def Src.quote : (T : Ty) → Src C T → Lean.Expr
  | _, @Src.val _ p v => mkAppN (mkConst ``Src.val) #[c, toExpr p, Val.quote c p v]
  | _, @Src.copy _ R p _ => mkAppN (mkConst ``Src.copy) #[c, toExpr R, SPath.quote c _ p, rflTrue]

def ARhs.quote (R : RefTy) : ARhs C R → Lean.Expr
  | .path p => mkAppN (mkConst ``ARhs.path) #[c, toExpr R, SPath.quote c _ p]
  | .push b _ => mkAppN (mkConst ``ARhs.push) #[c, toExpr R, SPath.quote c _ b, rflTrue]

def MRhs.quote (R : RefTy) : MRhs C R → Lean.Expr
  | .alias p => mkAppN (mkConst ``MRhs.alias) #[c, toExpr R, MPath.quote c _ p]
  | .copy p _ => mkAppN (mkConst ``MRhs.copy) #[c, toExpr R, SPath.quote c _ p, rflTrue]
  | .newArr n _ => mkAppN (mkConst ``MRhs.newArr) #[c, toExpr R, Simple.quote c .uint n, rflTrue]

def NewLhs.quote : (R : RefTy) → NewLhs C R → Lean.Expr
  | R, .store l => mkAppN (mkConst ``NewLhs.store) #[c, toExpr R, Loc.quote c _ l]
  | R, .mem l => mkAppN (mkConst ``NewLhs.mem) #[c, toExpr R, MLoc.quote c _ l]

def MSrc.quote : (T : Ty) → MSrc C T → Lean.Expr
  | _, @MSrc.val _ p v => mkAppN (mkConst ``MSrc.val) #[c, toExpr p, Val.quote c p v]
  | _, @MSrc.ref _ R p => mkAppN (mkConst ``MSrc.ref) #[c, toExpr R, MPath.quote c _ p]

def OpLoc.quote : (p : PrimTy) → OpLoc C p → Lean.Expr
  | p, .local x => mkAppN (mkConst ``OpLoc.local) #[c, toExpr p, toExpr x]
  | p, .root r _ => mkAppN (mkConst ``OpLoc.root) #[c, toExpr p, toExpr r, rflSome (.prim p)]
  | p, @OpLoc.field _ s _ b f _ =>
    mkAppN (mkConst ``OpLoc.field) #[c, toExpr s, toExpr p, SPath.quote c _ b, toExpr f,
      rflSome (.prim p)]
  | p, @OpLoc.index _ R k _ it b i =>
    mkAppN (mkConst ``OpLoc.index) #[c, toExpr R, toExpr k, toExpr p, IndexTy.quote it,
      SPath.quote c _ b, Simple.quote c k i]
  | p, @OpLoc.mfield _ s _ b f _ =>
    mkAppN (mkConst ``OpLoc.mfield) #[c, toExpr s, toExpr p, MPath.quote c _ b, toExpr f,
      rflSome (.prim p)]
  | p, @OpLoc.mindex _ R _ a b i =>
    mkAppN (mkConst ``OpLoc.mindex) #[c, toExpr R, toExpr p, ArrTy.quote a, MPath.quote c _ b,
      Simple.quote c .uint i]

def Arg.quoteList : List (Arg C) → Lean.Expr
  | [] => mkAppN (mkConst ``List.nil [0]) #[mkAppN (mkConst ``Arg) #[c]]
  | a :: as => mkAppN (mkConst ``List.cons [0]) #[mkAppN (mkConst ``Arg) #[c],
      mkAppN (mkConst ``Arg.mk) #[c, toExpr a.p, toExpr a.x, Val.quote c a.p a.e], Arg.quoteList as]

def CallRet.quote : CallRet → Lean.Expr
  | .none => mkConst ``CallRet.none
  | .val p r res => mkAppN (mkConst ``CallRet.val) #[toExpr p, toExpr r, toExpr res]
  | .rets rs => mkAppN (mkConst ``CallRet.rets) #[toExpr rs]

/-- An external call, each argument a `Sigma.mk` of its type and value. -/
def ExtCall.quote (call : ExtCall C) : Lean.Expr :=
  let argTy := mkAppN (mkConst ``ExtArg) #[c]
  let args := call.args.foldr (fun a acc => mkAppN (mkConst ``List.cons [0]) #[argTy,
      mkAppN (mkConst ``Sigma.mk [0, 0]) #[mkConst ``PrimTy, mkAppN (mkConst ``Simple) #[c], toExpr a.1,
        Simple.quote c a.1 a.2], acc])
    (mkAppN (mkConst ``List.nil [0]) #[argTy])
  mkAppN (mkConst ``ExtCall.mk) #[c, Simple.quote c .uint call.addr, toExpr call.fn, args]

def LoopAnn.quote : LoopAnn C → Lean.Expr
  | .unwind k => mkAppN (mkConst ``LoopAnn.unwind) #[c, toExpr k]
  | .inv I dec =>
    mkAppN (mkConst ``LoopAnn.inv) #[c, Val.quote c .bool I,
      optE (mkAppN (mkConst ``Val) #[c, toExpr PrimTy.uint]) (dec.map (Val.quote c .uint))]

mutual

def Stmt.quote : Stmt C → Lean.Expr
  | @Stmt.assign _ T l r => mkAppN (mkConst ``Stmt.assign) #[c, toExpr T, Loc.quote c T l, Src.quote c T r]
  | @Stmt.rebind _ R x r => mkAppN (mkConst ``Stmt.rebind) #[c, toExpr R, toExpr x, ARhs.quote c R r]
  | @Stmt.assignLocal _ p x r =>
    mkAppN (mkConst ``Stmt.assignLocal) #[c, toExpr p, toExpr x, Val.quote c p r]
  | .declLocal p x init =>
    mkAppN (mkConst ``Stmt.declLocal) #[c, toExpr p, toExpr x,
      optE (mkAppN (mkConst ``Val) #[c, toExpr p]) (init.map (Val.quote c p))]
  | .declStorage R x init =>
    mkAppN (mkConst ``Stmt.declStorage) #[c, toExpr R, toExpr x,
      optE (mkAppN (mkConst ``ARhs) #[c, toExpr R]) (init.map (ARhs.quote c R))]
  | @Stmt.opAssign _ p op _ _ l r =>
    mkAppN (mkConst ``Stmt.opAssign) #[c, toExpr p, toExpr op, rflTrue, rflTrue,
      OpLoc.quote c p l, Val.quote c p r]
  | @Stmt.incDec _ p op _ l =>
    mkAppN (mkConst ``Stmt.incDec) #[c, toExpr p, toExpr op, rflTrue, OpLoc.quote c p l]
  | @Stmt.assignIncDec _ p x op _ l _ =>
    mkAppN (mkConst ``Stmt.assignIncDec) #[c, toExpr p, toExpr x, toExpr op, rflTrue,
      OpLoc.quote c p l, rflTrue]
  | @Stmt.push _ E b v _ =>
    mkAppN (mkConst ``Stmt.push) #[c, toExpr E, SPath.quote c _ b,
      optE (mkAppN (mkConst ``Src) #[c, toExpr E]) (v.map (Src.quote c E)), rflTrue]
  | @Stmt.pop _ E b => mkAppN (mkConst ``Stmt.pop) #[c, toExpr E, SPath.quote c _ b]
  | .transfer r a => mkAppN (mkConst ``Stmt.transfer) #[c, Val.quote c .uint r, Val.quote c .uint a]
  | .send pv r a =>
    mkAppN (mkConst ``Stmt.send) #[c, toExpr pv, Val.quote c .uint r, Val.quote c .uint a]
  | .declMem R x init _ =>
    mkAppN (mkConst ``Stmt.declMem) #[c, toExpr R, toExpr x,
      optE (mkAppN (mkConst ``MRhs) #[c, toExpr R]) (init.map (MRhs.quote c R)), rflTrue]
  | @Stmt.rebindMem _ R x r => mkAppN (mkConst ``Stmt.rebindMem) #[c, toExpr R, toExpr x, MRhs.quote c R r]
  | @Stmt.assignFromMem _ R l p =>
    mkAppN (mkConst ``Stmt.assignFromMem) #[c, toExpr R, Loc.quote c _ l, MPath.quote c _ p]
  | @Stmt.assignMem _ T l r => mkAppN (mkConst ``Stmt.assignMem) #[c, toExpr T, MLoc.quote c T l, MSrc.quote c T r]
  | @Stmt.delete _ T l => mkAppN (mkConst ``Stmt.delete) #[c, toExpr T, Loc.quote c T l]
  | @Stmt.deleteMem _ T p _ =>
    mkAppN (mkConst ``Stmt.deleteMem) #[c, toExpr T, MPath.quote c T p, rflTrue]
  | @Stmt.assignNew _ R l n _ =>
    mkAppN (mkConst ``Stmt.assignNew) #[c, toExpr R, NewLhs.quote c R l, Simple.quote c .uint n,
      rflTrue]
  | .ite cond thn els =>
    mkAppN (mkConst ``Stmt.ite) #[c, Val.quote c .bool cond, Prog.quote thn, Prog.quote els]
  | .require cond => mkAppN (mkConst ``Stmt.require) #[c, Val.quote c .bool cond]
  | .assert cond => mkAppN (mkConst ``Stmt.assert) #[c, Val.quote c .bool cond]
  | .revert => mkAppN (mkConst ``Stmt.revert) #[c]
  | .call f args _ ret body =>
    mkAppN (mkConst ``Stmt.call)
      #[c, toExpr f, Arg.quoteList c args, rflTrue, CallRet.quote ret, Prog.quote body]
  | .tryCall call rets ok err code pnc other =>
    mkAppN (mkConst ``Stmt.tryCall)
      #[c, ExtCall.quote c call, toExpr rets, Prog.quote ok, Prog.quote err, toExpr code,
        Prog.quote pnc, Prog.quote other]
  | .loop a cond body =>
    mkAppN (mkConst ``Stmt.loop) #[c, LoopAnn.quote c a, Val.quote c .bool cond, Prog.quote body]

def Prog.quote : List (Stmt C) → Lean.Expr
  | [] => mkAppN (mkConst ``List.nil [0]) #[mkAppN (mkConst ``Stmt) #[c]]
  | s :: P => mkAppN (mkConst ``List.cons [0]) #[mkAppN (mkConst ``Stmt) #[c], Stmt.quote s, Prog.quote P]

end

end Quote

/-! ## `sol[C]{ … }` -/

/-- `sol[C]{ s₁; s₂; … }`: the statements, elaborated against the named
contract `C`. -/
syntax "sol[" term "]{" (sol_stmt solSemi)* "}" : term

/-- `sol{ … }`: `sol[C]{ … }` for the file's `InContract` contract. -/
syntax "sol{" (sol_stmt solSemi)* "}" : term

open Lean Elab Term Meta in
/-- Run `f C` at compile time for the contract the term `c` names, and splice
the term it computes, of type `Except ε Lean.Expr` (`ε` the Lean type `errTy`);
an error is reported by `onErr`.  `c` is unfolded through instances only, so
it may be `InContract.contract` but must end at a named contract. -/
def elabAgainstWith {ε : Type} (errTy : Lean.Expr) (onErr : ε → TermElabM Lean.Expr)
    (c : Lean.Term) (f : Lean.Term → TermElabM Lean.Term) : TermElabM Lean.Expr := do
  let C ← withTransparency .instances <| whnf (← elabTermAndSynthesize c (mkConst ``Contract))
  let some n := C.constName? | throwError "not a named contract: {C}"
  let t ← f (← `(Lean.mkConst $(quote n)))
  let ty := mkApp2 (mkConst ``Except [0, 0]) errTy (mkConst ``Lean.Expr)
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  match ← unsafe evalExpr (Except ε Lean.Expr) ty e with
  | .ok r => pure r
  | .error err => onErr err

open Lean Elab Term Meta in
/-- `elabAgainstWith`, an error reported at the source. -/
def elabAgainst (c : Lean.Term) (f : Lean.Term → TermElabM Lean.Term) : TermElabM Lean.Expr :=
  elabAgainstWith (ε := String) (mkConst ``String)
    (fun msg => throwError "Solidity elaboration failed: {msg}") c f

open Lean Elab Term Meta in
elab_rules : term
  | `(sol[ $c ]{ $[$ss:sol_stmt;]* }) => do
    let raw ← `(sol_raw!{ $[$ss;]* })
    -- an error is reported at the statement it arose in
    let errTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``String)
    let ref ← getRef
    let stmts : Array Syntax := ss.map TSyntax.raw
    elabAgainstWith (ε := Nat × String) errTy (fun ((i, msg) : Nat × String) =>
        throwErrorAt (stmts[i]?.getD ref) "Solidity elaboration failed: {msg}") c
      fun q => `((elabProgAt $c $raw).map (Prog.quote $q))

macro_rules
  | `(sol{ $[$ss;]* }) => `(sol[InContract.contract]{ $[$ss;]* })

/-! ## Examples -/

section Examples

local instance : InContract := ⟨StandardExample⟩

/-- A block over `StandardExample`: a local, an alias, writes through both,
a mapping entry, a branch on a comparison, a delete, a struct copy into a
mapping, a guard. -/
def tour : Prog StandardExample := sol{
  uint x = alice.age + 1;
  Person storage p = alice;
  p.age = x;
  balances[x] = 10;
  if (x > 3) { alice.age = 0; } else { revert(); };
  delete bob.account;
  folks[1] = bob;
  require(flags[x] || x == 2);
}

/--
info: uint x = alice.age + 1;
Person storage p = alice;
p.age = x;
balances[x] = 10;
if (x > 3) { alice.age = 0; } else { revert(); }
delete bob.account;
folks[1] = bob;
require(flags[x] || (x == 2));
-/
#guard_msgs in #eval IO.println (Prog.show tour)

/-- A compound target at a non-simple index captures the index first. -/
example : Prog.toStr (sol{ values[total + 1] += 2; }) =
    "uint ie1 = total + 1; values[ie1] += 2;" := rfl

/-- The captures are numbered past the fresh variables the block writes. -/
example : Prog.toStr (sol{ uint ie4 = 1; values[total + 1] += 2; }) =
    "uint ie4 = 1; uint ie5 = total + 1; values[ie5] += 2;" := rfl

/-- `lsv = sp.push()` and `T storage lsv = sp.push()`. -/
example : Prog.toStr (sol{ Person storage p = people.push(); p = persons.push(); }) =
    "Person storage p = people.push(); p = persons.push();" := rfl

/-- error: Solidity elaboration failed: age is already declared, or names a state variable -/
#guard_msgs in #check sol{ uint age = 1; }

/-- error: Solidity elaboration failed: a storage reference where a uint is expected -/
#guard_msgs in #check sol{ uint y = alice; }

/-- error: Solidity elaboration failed: `delete` on a storage pointer -/
#guard_msgs in #check sol{ Person storage q = alice; delete q; }

/-- error: Solidity elaboration failed: struct Person has no member balance -/
#guard_msgs in #check sol{ alice.balance = 1; }

/-- error: Solidity elaboration failed: a storage copy of a type that holds a mapping -/
#guard_msgs in #check sol{ wallet = wallet; }

/-- `.length` is a value: of a storage array and of a memory one. -/
example : Prog.toStr (sol{ uint n = values.length; uint[] memory xs = new uint[](n);
    n = xs.length; }) =
    "uint n = values.length; uint[] memory xs = new uint[](n); n = xs.length;" := rfl

/-- A decrement is spelled `−−` (two U+2212): `--` opens a Lean comment. -/
example : Prog.toStr (sol{ total−−; −−total; uint y = 0; y = total−−; }) =
    "total−−; −−total; uint y = 0; y = total−−;" := rfl

/-- `++` inside an expression is captured before its statement, into a fresh
local. -/
example : Prog.toStr (sol{ uint i = 0; values[i++] = 1; }) =
    "uint i = 0; uint se1; se1 = i++; values[se1] = 1;" := rfl

/-- A conditional of references is bound in a branch to a fresh alias. -/
example : Prog.toStr (sol{ bool c = true; Person storage p = c ? alice : bob; }) =
    "bool c = true; if (c) { Person storage sp1 = alice; } else { Person storage sp1 = bob; } \
    Person storage p = sp1;" := rfl

-- An increment under `&&` is evaluated only when the left operand does not
-- decide, so it cannot be captured before the statement.
/-- error: Solidity elaboration failed: `++` or `−−` under a short-circuit operator -/
#guard_msgs in #check sol{ bool c = true; uint i = 0; c = c && i++ > 0; }

/-- A negative literal takes the type it stands at. -/
example : (sol{ int e = -5; } : Prog StandardExample) =
    [.declLocal .int (.user "e") (some (.simple (.lit (-5) rfl)))] := rfl

/-- info: int e = -5; -/
#guard_msgs in #eval IO.println (Prog.show (sol{ int e = -5; } : Prog StandardExample))

/-- `delete` in memory, and a fresh array written to a location. -/
example : Prog.toStr (sol[TestSuite]{ Person memory m; delete m.age; delete m;
    basketA.items = new uint[](2); }) =
    "Person memory m; delete m.age; delete m; basketA.items = new uint[](2);" := rfl

/-- A call is its body inlined, every local of the callee fresh. -/
example : Prog.toStr (C := CallsExample) (sol[CallsExample]{ uint y = addTwo(3); credit(y, 2); bump(); }) =
    "uint y; y = addTwo(3); credit(y, 2); bump();" := rfl

/-- Each call of a block replaced by its inlined body, for display. -/
partial def Prog.inlined {C : Contract} : Prog C → Prog C
  | [] => []
  | .call _ args _ ret body :: P => Stmt.expandBody args ret (Prog.inlined body) ++ Prog.inlined P
  | s :: P => s :: Prog.inlined P

/-! What the calls run: `addTwo` calls `addOne` twice, `larger` returns from
both branches of its last `if`. -/

/--
info: uint y; uint se1 = 3; uint se2; uint se3 = se1; uint se4; se4 = se3 + 1; se2 = se4; uint se5 = se2; uint se6; se6 = se5 + 1; se2 = se6; y = se2; uint z; uint se7 = y; uint se8 = 7; uint se9; if (se7 > se8) { se9 = se7; } else { se9 = se8; } z = se9;
-/
#guard_msgs in
#eval IO.println (Prog.toStr (Prog.inlined (sol[CallsExample]{ uint y = addTwo(3); uint z = larger(y, 7); })))

/-- error: Solidity elaboration failed: addOne is not a function declared before this one -/
#guard_msgs in #check sol[StandardExample]{ uint y = addOne(1); }

/-- error: Solidity elaboration failed: addOne takes 1 arguments, not 2 -/
#guard_msgs in #check sol[CallsExample]{ uint y = addOne(1, 2); }

/-! ### Friendlier spellings -/

/-- `else if`: the `if`s nested. -/
example : Prog.toStr (sol{ if (total > 2) { total = 1; } else if (total > 1) { total = 2; }
    else if (total > 0) { total = 3; } else { total = 4; } }) =
    "if (total > 2) { total = 1; } else { if (total > 1) { total = 2; } else { \
    if (total > 0) { total = 3; } else { total = 4; } } }" := rfl

/-- A statement ending in a block needs no `;`; one with it reads the same. -/
example : (sol{ if (total > 0) { total = 0; } unchecked { total += 1; } total = 1; } :
    Prog StandardExample) = sol{ if (total > 0) { total = 0; }; unchecked { total += 1; }; total = 1; } :=
  rfl

/-- `address payable` is an `address`, a `uint`. -/
example : Prog.toStr (sol{ address payable a = owner; }) = "uint a = owner;" := rfl

/-- error: Solidity elaboration failed: unknown type Foo -/
#guard_msgs in #check sol{ Foo x; }

/-- A `uint8` is a `uint` whose arithmetic is checked at 8 bits (`narrowPost`);
`Examples/Tactics/Checked.lean` has the rest. -/
example : Prog.toStr (sol{ uint8 x = 250; x += 10; }) =
    "uint x = 250; x += 10; require(x <= 255);" := rfl

/-- error: Solidity elaboration failed: unknown type uint7: the integer types are `uint8` … `uint256` and `int8` … `int256`, in steps of 8 -/
#guard_msgs in #check sol{ uint7 x = 1; }

/-- error: Solidity elaboration failed: total is indexed, but it is a uint, not a mapping or an array -/
#guard_msgs in #check sol{ total[1] = 2; }

/-- error: Solidity elaboration failed: alice: an operand of reference type Person -/
#guard_msgs in #check sol{ total = alice + 1; }

/-- error: Solidity elaboration failed: alice: a storage reference to a Person where a Person[] is expected -/
#guard_msgs in #check sol{ Person[] storage ps = alice; }



end Examples

end Solidity
