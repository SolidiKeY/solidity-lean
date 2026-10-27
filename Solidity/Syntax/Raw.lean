import Solidity.AST
import Solidity.SpecSyntax

/-!
# The surface syntax, as read

The raw syntax `sol{ … }` reads (`RawStmt`), the contract, narrow integer,
byte and function types, the types an index carries, printing helpers.

A piece of `Syntax.lean`, whose docstring describes the whole.
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
  /-- `(a, b)`, two components or more: the right-hand side of a tuple
  assignment (`RawStmt.tupleAssign`), a `return` of several values, or a
  loop's ordered `uint` lexicographic variant. -/
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
decreases e` (at most one; a scalar or a tuple of at least two `uint`
expressions) and, Lean only, `/// @custom:key unwind k`, the
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
  /-- `revert("m");`: a revert with `Error(m)`'s data where a `try` reads it
  (the callee of a self-call `try`, `Stmt.revertData`), `revert();`
  elsewhere (`docs/semantic-gaps.md`, "Revert data"). -/
  | revertMsg (msg : String)
  /-- `require(c, "m");`: `require(c);`, but where a `try` reads the data
  (as `revertMsg`) `if (c) { } else { revert("m"); }`. -/
  | requireMsg (c : RawExpr) (msg : String)
  /-- `revert(s)` with a computed string reason. -/
  | revertReason (msg : RawExpr)
  /-- `require(c, s)`: both operands evaluated before the condition is tested. -/
  | requireReason (c msg : RawExpr)
  /-- The canonical memory-byte rethrow assembly block. -/
  | revertRaw (data : RawExpr)
  /-- `revert E(a, b);`: a revert with the custom error `E`'s data (its
  selector, then `abi.encode(a, b)`) where a `try` reads it, `revert();`
  elsewhere, as `revertMsg`. -/
  | revertErr (e : String) (args : List RawExpr)
  /-- `require(c, E(a, b));`: `RawStmt.requireWith c [a, b]`, but where a
  `try` reads the data `if (c) { eval(a, b) } else { revert E(a, b); }`. -/
  | requireErr (c : RawExpr) (e : String) (args : List RawExpr)
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

/-- A syntactically simple operand. This is not a totality test: a member
read through an unset reference can fail. Discarding an operand also needs
the elaborator's typed `canDiscardArg` check. -/
def RawExpr.isPure : RawExpr → Bool
  | .num _ | .bool _ | .name _ => true
  | .field e _ => e.isPure
  | .env _ => true
  | _ => false

/-- `require(c, Err(a, b));`: evaluate the condition first, then the
arguments on either branch. An argument's panic takes priority over the
require's revert, even when `c` is false. The elaborator may omit arguments
only after checking their typed reads cannot fail. -/
def RawStmt.requireWith (c : RawExpr) (args : List RawExpr) : RawStmt :=
  if args.isEmpty then .require c
  else .ite c [.eval args] [.eval args, .revert]

/-- A reference parameter's declared data location. -/
inductive ParamLoc where
  | memory | storage | calldata
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

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
  /-- The widths of its parameters' narrow positions, keyed by the parameter
  and their path below it, as `FunDecl.widths` keys a function's (`xs[]`). -/
  widths : List (Name × Nat) := []
  /-- Its reference parameters' data locations. -/
  locs : List (Name × ParamLoc) := []
  deriving Repr, Inhabited

/-- Source visibility of a function which has no ABI entry. -/
inductive SourceLocalVisibility where
  | privateFn | internalFn | freeFn
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- Public functions also have internal values; external functions do not. -/
inductive SourceAbiVisibility where
  | publicFn | externalFn
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- A retained base body is callable internally, but is not the selected ABI entry. -/
inductive SourceSelection where
  | selected | retained
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

inductive SourceMutability where
  | nonpayable | pureFn | viewFn | payable
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- Compiler declaration roles. Only ABI declarations and getters carry
selectors, bounded to four bytes. Special entries have no ordinary selector. -/
inductive SourceCallable where
  | local (visibility : SourceLocalVisibility)
  | abi (visibility : SourceAbiVisibility) (selection : SourceSelection)
      (selector : Option (Fin (2 ^ 32)))
  | getter (selector : Fin (2 ^ 32))
  | constructor
  | receive (selection : SourceSelection)
  | fallback (selection : SourceSelection)
  | implementation
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- Source ABI identity survives model-name disambiguation. The signature is
computed before enum, contract and value-type erasure; an absent signature
never licenses hashing a generated model name. Native declarations use `none`. -/
structure SourceFunction where
  declaration : Option Int := none
  name : String := ""
  signature : Option String := none
  mutability : SourceMutability := .nonpayable
  callable : SourceCallable := .implementation
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

def SourceFunction.internalValue (d : SourceFunction) : Bool :=
  match d.callable with
  | .local _ | .abi .publicFn _ _ => true
  | _ => false

def SourceFunction.externalValue (d : SourceFunction) : Bool :=
  match d.callable with
  | .abi .. | .getter _ => true
  | _ => false

def SourceFunction.externalEntry (d : SourceFunction) : Bool :=
  match d.callable with
  | .abi _ .selected _ | .getter _ => true
  | _ => false

/-- An internal function as the contract declares it: its parameters and
its return variables (`returns (uint r)`; unnamed, `returns (uint)`, it is
called `_ret`, and the `i`-th of several `_ret{i}`, solkey's `ret{i}`;
`returns (Account memory a)` or `returns (Account storage a)`, a reference
at its location), at their types, and its
body as read.  The elaborator types the body where the function is called
and inlines it there (`Stmt.call`). -/
structure FunDecl where
  /-- Imported source identity, independent of this function's model alias. -/
  sourceDecl : Option SourceFunction := none
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
  with their width: each is a `uint` or an `int` in `params`/`ret`; and the
  narrow positions inside a reference one, keyed by their path as
  `Contract.widths` keys them (`uint8[] memory xs` is `xs[]`). -/
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

/-- Operand scheduling during elaboration. Calls, indices, short-circuit
operators and assignment targets keep their existing sequencing. -/
structure EvalOrder where
  binaryLeftToRight : Bool := false
  modularLeftToRight : Bool := false
  /-- Modifier placeholders have separate function parameter/return slots. -/
  modifierFrames : Bool := false
  deriving Repr, Inhabited

/-- Solidity's IR code generator evaluates ordinary expressions in source order. -/
def EvalOrder.viaIR : EvalOrder := ⟨true, true, true⟩

/-- A contract carries the validity of its storage declaration. The proof
fields are erased when programs run; literals discharge them by computation. -/
structure Contract where
  vars : List (Name × Ty)
  funs : List (Name × FunDecl) := []
  /-- Its enums, each with its members in order: `State.Locked` is the
  `uint` literal `1` (an enum is read as `uint`, as `address` is). -/
  enums : List (Name × List Name) := []
  /-- Its `invariant` clauses, as read: solkey's `CInv`. -/
  inv : List SpecExpr := []
  /-- Its state variables of a narrow integer type (`uint8 small;`), with their
  width: each is a `uint` or an `int` in `vars`; and the narrow positions
  inside one, keyed by their path (`uint8[] xs;` is `xs[]`, a mapping's key
  `m{}`, its value `m[]`: `expandStateTyW`). -/
  widths : List (Name × Nat) := []
  /-- `constructor(…) { … }`: what a deployment runs, called as
  `constructor(args);` (`elabCtor`).  `none` for a contract that declares
  none: solc's implicit one, which runs the initializers only. -/
  ctor : Option FunDecl := none
  /-- `uint x = 5;`: the state variables declared with an initializer, in
  declaration order, each with it as read.  The constructor runs them first
  (`elabCtor`), as solkey's `ExpandFunctionBody` prepends them. -/
  inits : List (Name × RawExpr) := []
  /-- `struct S { … }`: its own structs, each by the name it is written by
  and its type's name in the table, which spells its members
  (`Semantics.StructEnc`; the plain name when the table's struct of that
  name has those members). -/
  structs : List (Name × Name) := []
  /-- `error E(uint8 a, address b);`: its custom errors, each a declaration
  of its parameters only (their types and width rows, as a function's), from
  which a `revert E(…)` computes its selector (`errorSignature?`). -/
  errors : List (Name × FunDecl) := []
  /-- The elaborator's operand schedule, retained by every use of this contract. -/
  evalOrder : EvalOrder := {}
  /-- Every storage type has well-formed defaults all the way down. -/
  vars_ok : vars.all (fun nt => nt.2.okDeep) = true := by decide
  /-- A storage name identifies exactly one declared root. -/
  vars_nodup : nodupKeysB vars = true := by decide
  deriving Repr

instance : Inhabited Contract := ⟨{ vars := [] }⟩

namespace Contract

/-- The struct a type name names in `C`: its own first, else the table's. -/
def structName? (C : Contract) (s : Name) : Option Name :=
  match lookupBy s C.structs with
  | some e => some e
  | none => if (structDef s).isEmpty then none else some s

/-- The members of the struct a type name names in `C`; none for another name. -/
def structFields (C : Contract) (s : Name) : List (Name × Ty) :=
  match C.structName? s with
  | some e => structDef e
  | none => []

/-- The declared type of the storage root `r`. -/
def rootType (C : Contract) (r : Name) : Option Ty := lookupBy r C.vars

/-- A declared root inherits its type's validity from the contract. -/
theorem root_okDeep (C : Contract) {r : Name} {T : Ty}
    (h : C.rootType r = some T) : T.okDeep = true :=
  all_mem C.vars_ok (r, T) (lookupBy_eq_some_mem h)

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

/-! ## Byte types

`bytes1` … `bytes32`, `bytes` and `string` are not types of the syntax
either (`docs/semantic-gaps.md`, "Bytes and strings"): a `bytesN` is a `uint`
of `8N` bits holding its bytes read big-endian (the `uintN(b)` solc's
conversion gives), and `bytes`/`string` a `bytes1[]`, a `uint[]` 8 bits wide.
Beside a width the tables carry a marker row `k#bytes ↦ N` (`valueRows?`),
which is how the elaborator tells a `bytesN` from a `uint8N` where solc's
operations differ (`bytesPure`, `Syntax/Elab.lean`). -/

/-- `bytes1` … `bytes32`: the number of bytes. -/
def bytesTy? (s : String) : Option Nat :=
  if s.startsWith "bytes" then
    match (s.drop 5).toNat? with
    | some n => if 1 ≤ n && n ≤ 32 && toString n == s.drop 5 then some n else none
    | none => none
  else none

/-- `bytes` and `string`, both a `bytes1[]`. -/
def dynBytesTy (s : String) : Bool := s == "bytes" || s == "string"

/-- The marker of an `address` (`valueRows?`): its width in bytes. -/
def addressRows : List (String × Nat) := [("#address", 20)]

/-- The marker of an enum (`expandStateTyW`, `elabTyW`): a `uint` of one
byte in the ABI, `uint8` in a signature. -/
def enumRows : List (String × Nat) := [("#enum", 1)]

/-- The width rows a value type adds at its own position (`""`): a narrow
integer's width, a `bytesN`'s width below 256 bits and its marker, a function
type's marker ("Function types" below); with the primitive type it is read
as. -/
def valueRows? (s : String) : Option (PrimTy × List (String × Nat)) :=
  if s.startsWith "function(" then some (.uint, [("#" ++ s, 0)]) else
  -- an `address`: a `uint` and its marker, which the ABI reads (20 bytes
  -- packed, `address` in a signature)
  if s == "address" then some (.uint, addressRows) else
  match narrowTy? s, bytesTy? s with
  | some (p, n), _ => some (p, [("", n)])
  | none, some n => some (.uint, (if n < 32 then [("", 8 * n)] else []) ++ [("#bytes", n)])
  | none, none => none

/-- The marker rows of a mapping keyed by `string` or `bytes`: the key is the
`keccak256` of the bytes, a `bytes32` (`docs/semantic-gaps.md`, "Hashing and
the ABI"); `m[s]` is `m[keccak256(bytes(s))]` (`bytesPure`). -/
def hashKeyRows : List (String × Nat) := [("{}#hash", 1)]

/-- The rows of `bytes` and `string`: elements 8 bits wide, each a `bytes1`. -/
def dynBytesRows : List (String × Nat) := [("[]", 8), ("[]#bytes", 1)]

/-- The rows of `bytes` or `string` (`dynBytesTy`): a `string` marked so
too, retained by signatures and computed revert reasons. -/
def dynBytesRowsOf (s : String) : List (String × Nat) :=
  if s == "string" then dynBytesRows ++ [("#string", 1)] else dynBytesRows

/-- The name of a literal of bytes (`"ab"`, `hex"6162"`) as an expression:
a call no function can be the callee of, read at the type it meets
(`bytesPure`, `Syntax/Elab.lean`). -/
def bytesLitName : String := "#bytes"

/-- The name of a call through a value that is not a name, `s.f(x)`,
`fs[i](x)`, `choose(b)(x)`: `#callValue(callee, args…)`, the callee captured
into a fresh local of its function type before the call (`hoist`,
`Syntax/Elab.lean`). -/
def callValueName : String := "#callValue"

/-- `keccak256(b)` (`sha256(b)`, …) once `hoist` has made `b` a memory path:
the member `b.#keccak256`, which no source can write (`Val.hash`). -/
def hashMember (k : HashKind) : String := "#" ++ k.toStr

/-- A hashing builtin's name (`HashKind.ofName?`). -/
def isHashName (f : String) : Bool := (HashKind.ofName? f).isSome

/-- The hash a member names, if it is one (`hashMember`). -/
def hashMember? (f : String) : Option HashKind :=
  if f.startsWith "#" then HashKind.ofName? (f.drop 1) else none

/-- The literal of the bytes `bs`. -/
def RawExpr.bytesLit (bs : List Nat) : RawExpr := .call bytesLitName (bs.map .num)

/-- The bytes of a literal of bytes. -/
def RawExpr.bytesLit? : RawExpr → Option (List Nat)
  | .call f as => if f == bytesLitName then as.mapM fun | .num n => some n | _ => none else none
  | _ => none

/-- The bytes `hex"…"` spells: pairs of hex digits, `_` between them. -/
def hexBytes? (s : String) : Option (List Nat) :=
  let ds := (s.toList.filter (· != '_')).map fun c =>
    if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
    else none
  match ds.mapM id with
  | some ds =>
    let rec pairs : List Nat → Option (List Nat)
      | [] => some []
      | a :: b :: r => (pairs r).map ((16 * a + b) :: ·)
      | [_] => none
    pairs ds
  | none => none

/-! ## Function types

An internal function type (`function (uint) pure returns (uint)`) is not a
type of the syntax either (`docs/semantic-gaps.md`, "Function types"): a
value of one is a `uint`, the tag of a function of the contract (its
position in `Contract.funs`, from `1`; `0` is unassigned), and a call through
it is a dispatch over the contract's functions of its signature
(`fnDispatch`, `Syntax/Elab.lean`).  Its spelling, `function(uint)returns(uint)`
(`fnTyStr`), is the marker row beside the `uint`: `k#function(uint)returns(uint)
↦ 0` (`valueRows?`), as a `bytesN`'s is `k#bytes ↦ N`. -/

/-- A function type's spelling (`fnTyStr`). -/
def fnTy? (s : String) : Bool := s.startsWith "function("

/-- `l` split at the commas where no bracket is open. -/
def splitTopCommas (s : String) : List String :=
  if s.isEmpty then [] else
    (Semantics.StructEnc.splitTop ',' 0 [] s.toList).map String.mk

/-- The spelling of a function type of these parameters and returns. -/
def fnTyStr (ps rs : List String) (ext : Bool) : String :=
  s!"function({",".intercalate ps})" ++ (if ext then "external" else "") ++
    (if rs.isEmpty then "" else s!"returns({",".intercalate rs})")

/-- A function type's parameters, returns, and whether it is `external`. -/
def fnParts? (s : String) : Option (List String × List String × Bool) := do
  guard (fnTy? s)
  let cs := (s.drop 9).toList
  -- the `)` that closes the parameters
  let rec close : Nat → List Char → List Char → Option (List Char × List Char)
    | _, _, [] => none
    | d, acc, c :: cs =>
      if c == ')' && d == 0 then some (acc.reverse, cs)
      else
        let d' := if c == '(' || c == '[' then d + 1 else if c == ')' || c == ']' then d - 1 else d
        close d' (c :: acc) cs
  let (ps, rest) ← close 0 [] cs
  let rest := String.mk rest
  let ext := rest.startsWith "external"
  let rest := if ext then rest.drop 8 else rest
  let rs ← if rest.isEmpty then pure []
    else if rest.startsWith "returns(" && rest.endsWith ")" then
      pure (splitTopCommas ((rest.drop 8).dropRight 1))
    else none
  pure (splitTopCommas (String.mk ps), rs, ext)

/-- A function type's spelling with each component as the elaborator reads
it: `uint256` and `address` are `uint`, an enum of `enums` is `uint`. -/
partial def canonFnTy (enums : List String) (s : String) : String :=
  match fnParts? s with
  | some (ps, rs, ext) =>
    let comp (c : String) : String :=
      if fnTy? c then canonFnTy enums c else
      match PrimTy.ofName? c with
      | some p => p.toStr
      | none => if enums.contains c then "uint" else c
    fnTyStr (ps.map comp) (rs.map comp) ext
  | none => s

/-- Why a narrow type is refused where it stands. -/
def narrowNestedMsg (s : String) : String :=
  s!"{s}: a narrow integer type stands in the type of a local, a parameter, a return value, " ++
  "a state variable or a struct of the table (`structWidths`), not here"

declare_syntax_cat sol_ty (behavior := both)
syntax:max ident : sol_ty
syntax:max &"mapping" "(" sol_ty " => " sol_ty ")" : sol_ty
syntax:max sol_ty:max "[" "]" : sol_ty
/-- `uint[3]`: a fixed-size array; `uint[2][3]` is three `uint[2]`. -/
syntax:max sol_ty:max "[" num "]" : sol_ty
/-- `address payable`: an `address`, read as `uint`. -/
syntax:max &"address" &"payable" : sol_ty
/-- `function (uint) pure returns (uint)`: a function type, read as the
`uint` tag of a function (`fnTy?`, "Function types" below); its mutability
is dropped. -/
syntax:max (name := solFnTy) &"function" "(" sol_ty,* ")"
  (ppSpace (&"internal" <|> &"external" <|> &"pure" <|> &"view" <|> &"payable"))*
  (ppSpace &"returns" " (" sol_ty,* ")")? : sol_ty

/-- `ty!(mapping(uint => Person))`: a type written as Solidity does. -/
syntax "ty!(" sol_ty ")" : term

/-- `pty!(uint)`: a value type, as a mapping's key is. -/
syntax "pty!(" sol_ty ")" : term

macro_rules
  | `(pty!($x:ident)) =>
      match PrimTy.ofName? (x.getId.toString false) with
      | some .uint => `(PrimTy.uint)
      | some .int => `(PrimTy.int)
      | some .bool => `(PrimTy.bool)
      | none => Lean.Macro.throwErrorAt x "a mapping's key is a value type"
  | `(pty!(address payable)) => `(PrimTy.uint)
  | `(pty!($t)) => Lean.Macro.throwErrorAt t "a mapping's key is a value type"

macro_rules
  | `(ty!($x:ident)) =>
      let s := (x.getId.toString false)
      match PrimTy.ofName? s with
      | some .uint => `(Ty.uint)
      | some .int => `(Ty.int)
      | some .bool => `(Ty.bool)
      | none =>
        -- a struct of the table; an enum never reaches here (`expandMemberTy`),
        -- nor does a narrow type where one may stand (`expandMemberTyW`)
        if (narrowTy? s).isSome || (bytesTy? s).isSome || dynBytesTy s then
          Lean.Macro.throwErrorAt x (narrowNestedMsg s)
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

end Solidity
