import Solidity.AST

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
-/

namespace Solidity

open Semantics

/-! ## The contract

Struct bodies are `Semantics.structDef`, the table the interpreter expands
structs through, so a contract cannot disagree with what runs: a contract
is its storage roots, in declaration order, and `fieldType` reads the
table. -/

structure Contract where
  vars : List (Name × Ty)
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

declare_syntax_cat sol_ty (behavior := both)
syntax:max ident : sol_ty
syntax:max &"mapping" "(" sol_ty " => " sol_ty ")" : sol_ty
syntax:max sol_ty:max "[" "]" : sol_ty

declare_syntax_cat sol_member (behavior := both)
syntax sol_ty ident ";" : sol_member

/-- `contract!{ uint total; Person alice; mapping(uint => Person) folks; }`:
a contract written as Solidity declares its state. -/
syntax "contract!{" sol_member* "}" : term

/-- `ty!(mapping(uint => Person))`: a type written as Solidity does. -/
syntax "ty!(" sol_ty ")" : term

macro_rules
  | `(ty!($x:ident)) =>
      match x.getId.toString with
      | "uint" | "address" => `(Ty.uint)
      | "int" => `(Ty.int)
      | "bool" => `(Ty.bool)
      | s => `(Ty.struct $(Lean.quote s))
  | `(ty!(mapping($K => $V))) => `(Ty.mapping ty!($K) ty!($V))
  | `(ty!($T[])) => `(Ty.array ty!($T))

macro_rules
  | `(contract!{ $ms:sol_member* }) => do
      let rows ← ms.mapM fun
        | `(sol_member| $T:sol_ty $x:ident ;) => `(($(Lean.quote x.getId.toString), ty!($T)))
        | _ => Lean.Macro.throwUnsupported
      `(({ vars := [$rows,*] } : Contract))

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

/-- `solc/SolcControlFlow.sol`. -/
def SolcControlFlow : Contract := contract!{
  Pair sx; Pair sy; Pair target; uint[] values;
}

/-! ## Expressions

The sorts of the paper's schema variables are types here:

| sort | paper | is |
|---|---|---|
| `Simple C p` | `se` | a literal or a stack local |
| `SPath C T` | `sp`, `nsp` | a storage path: an alias or a location |
| `Loc C T` | `gsp`, `sp.fld`, `sp[e]` | a state variable, a member, an entry |
| `Val C p` | `e`, `nse` | a value: simple, a read, an operator, a conditional |
| `MPath C T`, `MLoc C T` | `mv`, `nmp` | the same in memory, which has no roots |

`isSimple` tells `sp` from `nsp` and `se` from `nse`: which one a statement
has decides which rule runs, not which statements can be written. -/

/-- How a reference type is indexed: a mapping by its key, an array by a
`uint`.  One `Loc.index` serves both, so a rule that does not care which
is one constructor, and the ones that do fix it. -/
inductive IndexTy : RefTy → PrimTy → Ty → Type where
  | map {k : PrimTy} {V : Ty} : IndexTy (.mapping (.prim k) V) k V
  | arr {E : Ty} : IndexTy (.array E) .uint E

/-- A simple value (`se`): a literal or a stack local. -/
inductive Simple (C : Contract) : PrimTy → Type where
  | lit {p : PrimTy} (n : Int) (h : p.isNumeric = true) : Simple C p
  | bool (b : Bool) : Simple C .bool
  | local {p : PrimTy} (x : Var) : Simple C p

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
  | index {E : Ty} (b : MPath C (.array E)) (i : Val C .uint) : MLoc C E

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

/-- What a memory local is bound to: a memory object by identity
(`m = n;`), or a fresh deep copy of a storage object (`m = alice;`). -/
inductive MRhs (C : Contract) (R : RefTy) where
  | alias (p : MPath C (.ref R))
  | copy (p : SPath C (.ref R)) (hm : (Ty.ref R).mapFree = true)

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
  | mindex {p : PrimTy} (b : MPath C (.array (.prim p))) (i : Simple C .uint) : OpLoc C p

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
  | .mfield b _ _ | .mindex b _ => b.isSimple
  | _ => true

/-- `v`, if it is simple. -/
def Val.toSimple? {C : Contract} {p : PrimTy} : Val C p → Option (Simple C p)
  | .simple s => some s
  | _ => none

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
  /-- `if (c) { … } else { … }` -/
  | ite (c : Val C .bool) (thn els : List (Stmt C))
  /-- `require(c);` -/
  | require (c : Val C .bool)
  /-- `assert(c);` -/
  | assert (c : Val C .bool)
  /-- `revert();` -/
  | revert

/-- A block. -/
abbrev Prog (C : Contract) := List (Stmt C)

/-! ## Printing

`Prog.toStr` writes a block back as the Solidity it came from, which
`sol{ … }` reads again.  An operator application is parenthesised unless it
is the whole expression. -/

section Print

variable {C : Contract} [FreshNames]

def BinOp.sym : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .pow => "**" | .div => "/" | .mod => "%"
  | .lt => "<" | .gt => ">" | .le => "<=" | .ge => ">="
  | .eqB => "==" | .neB => "!=" | .and => "&&" | .or => "||"

def UnOp.sym : UnOp → String
  | .neg => "-" | .not => "!"

def Ty.toStr : Ty → String
  | .prim .uint => "uint" | .prim .int => "int" | .prim .bool => "bool"
  | .ref (.struct s) => s
  | .ref (.array T) => T.toStr ++ "[]"
  | .ref (.mapping K V) => s!"mapping({K.toStr} => {V.toStr})"

def Simple.toStr {p : PrimTy} : Simple C p → String
  | .lit n _ => toString n
  | .bool b => toString b
  | .local x => toString x

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
  | .index b i => s!"{b.toStr}[{i.toStr true}]"

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
  | .mindex b i => s!"{b.toStr}[{i.toStr}]"

def MRhs.toStr {R : RefTy} : MRhs C R → String
  | .alias p => p.toStr
  | .copy p _ => p.toStr

def MSrc.toStr {T : Ty} : MSrc C T → String
  | .val v => v.toStr true
  | .ref p => p.toStr

/-- `x++`, `--x`. -/
def IncDec.show (op : IncDec) (x : String) : String :=
  let t := if op.isIncrement then "++" else "--"
  if op.isPre then t ++ x else x ++ t

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
  | .assignIncDec x op _ l _ => s!"{x} = {IncDec.show op l.toStr};"
  | .delete l => s!"delete {l.toStr};"
  | .ite c thn els => s!"if ({c.toStr true}) \{ {Prog.toStr thn} } else \{ {Prog.toStr els} }"
  | .require c => s!"require({c.toStr true});"
  | .assert c => s!"assert({c.toStr true});"
  | .revert => "revert();"

def Prog.toStr : List (Stmt C) → String
  | [] => ""
  | [s] => s.toStr
  | s :: P => s!"{s.toStr} {Prog.toStr P}"

end

/-- One statement per line, for display. -/
def Prog.show : List (Stmt C) → String
  | [] => ""
  | [s] => s.toStr
  | s :: P => s!"{s.toStr}\n{Prog.show P}"

end Print

/-! ## Surface syntax -/

inductive RawTy where
  | named (s : String)
  | mapping (k v : RawTy)
  | array (t : RawTy)
  deriving Repr, Inhabited

inductive RawExpr where
  | num (n : Nat)
  | name (x : String)
  | bool (b : Bool)
  | field (e : RawExpr) (f : String)
  | index (e k : RawExpr)
  | binop (op : BinOp) (a b : RawExpr)
  | unop (op : UnOp) (a : RawExpr)
  | ternary (c a b : RawExpr)
  deriving Repr, Inhabited

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
  deriving Repr, Inhabited

declare_syntax_cat sol_expr (behavior := both)
syntax:max num : sol_expr
syntax:max ident : sol_expr
syntax:max sol_expr:max "." ident : sol_expr
syntax:max sol_expr:max "[" sol_expr "]" : sol_expr
syntax:max "(" sol_expr ")" : sol_expr
syntax:80 "!" sol_expr:80 : sol_expr
syntax:80 "-" sol_expr:80 : sol_expr
syntax:70 sol_expr:70 " * " sol_expr:71 : sol_expr
syntax:70 sol_expr:70 " / " sol_expr:71 : sol_expr
syntax:70 sol_expr:70 " % " sol_expr:71 : sol_expr
syntax:65 sol_expr:65 " + " sol_expr:66 : sol_expr
syntax:65 sol_expr:65 " - " sol_expr:66 : sol_expr
syntax:50 sol_expr:51 " < " sol_expr:51 : sol_expr
syntax:50 sol_expr:51 " > " sol_expr:51 : sol_expr
syntax:50 sol_expr:51 " <= " sol_expr:51 : sol_expr
syntax:50 sol_expr:51 " >= " sol_expr:51 : sol_expr
syntax:45 sol_expr:46 " == " sol_expr:46 : sol_expr
syntax:45 sol_expr:46 " != " sol_expr:46 : sol_expr
syntax:35 sol_expr:36 " && " sol_expr:35 : sol_expr
syntax:30 sol_expr:31 " || " sol_expr:30 : sol_expr
syntax:20 sol_expr:21 " ? " sol_expr:21 " : " sol_expr:20 : sol_expr

declare_syntax_cat sol_stmt (behavior := both)
declare_syntax_cat sol_block (behavior := both)
syntax "{" (sol_stmt ";")* "}" : sol_block
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
syntax sol_ty &"storage" ident " = " sol_expr ".push()" : sol_stmt
syntax sol_expr ".transfer(" sol_expr ")" : sol_stmt
syntax sol_expr "(" ")" : sol_stmt
syntax sol_expr "(" sol_expr ")" : sol_stmt
syntax sol_expr " = " sol_expr "(" ")" : sol_stmt
syntax sol_ty &"storage" ident " = " sol_expr "(" ")" : sol_stmt
syntax sol_expr "++" : sol_stmt
syntax "++" sol_expr : sol_stmt
syntax sol_expr " = " sol_expr "++" : sol_stmt
syntax sol_expr " = " "++" sol_expr : sol_stmt
syntax sol_expr " += " sol_expr : sol_stmt
syntax sol_expr " -= " sol_expr : sol_stmt
syntax sol_expr " *= " sol_expr : sol_stmt
syntax sol_expr " /= " sol_expr : sol_stmt
syntax sol_expr " %= " sol_expr : sol_stmt
syntax "if " "(" sol_expr ") " sol_block (" else " sol_block)? : sol_stmt
syntax (name := solRequire) &"require" "(" sol_expr ")" : sol_stmt
syntax (name := solAssert) &"assert" "(" sol_expr ")" : sol_stmt
syntax (name := solRevert) &"revert" "(" ")" : sol_stmt

/-- `sol_raw!{ s₁; s₂; … }`: the raw statements, before elaboration. -/
syntax "sol_raw!{" (sol_stmt ";")* "}" : term

/-- The dot-separated parts of a name: `alice.account` is `["alice", "account"]`. -/
def nameParts : Lean.Name → List String
  | .anonymous => []
  | .str p s => nameParts p ++ [s]
  | .num p n => nameParts p ++ [toString n]

section Expand
open Lean

/-- `alice.account.age` arrives as one identifier; split it into members. -/
def expandIdent (x : Ident) : MacroM Term := do
  match nameParts x.getId with
  | [] => Macro.throwError "empty identifier"
  | ["true"] => `(RawExpr.bool true)
  | ["false"] => `(RawExpr.bool false)
  | root :: flds =>
    flds.foldlM (init := ← `(RawExpr.name $(quote root)))
      fun acc f => `(RawExpr.field $acc $(quote f))

partial def expandExpr : TSyntax `sol_expr → MacroM Term
  | `(sol_expr| $n:num) => `(RawExpr.num $n)
  | `(sol_expr| $x:ident) => expandIdent x
  | `(sol_expr| $e:sol_expr . $f:ident) => do
      (nameParts f.getId).foldlM (init := ← expandExpr e)
        fun acc c => `(RawExpr.field $acc $(quote c))
  | `(sol_expr| $e:sol_expr [ $k:sol_expr ]) => do
      `(RawExpr.index $(← expandExpr e) $(← expandExpr k))
  | `(sol_expr| ( $e:sol_expr )) => expandExpr e
  | `(sol_expr| ! $a) => do `(RawExpr.unop .not $(← expandExpr a))
  | `(sol_expr| - $a) => do `(RawExpr.unop .neg $(← expandExpr a))
  | `(sol_expr| $c ? $a : $b) => do
      `(RawExpr.ternary $(← expandExpr c) $(← expandExpr a) $(← expandExpr b))
  | `(sol_expr| $a * $b) => bin ``BinOp.mul a b
  | `(sol_expr| $a / $b) => bin ``BinOp.div a b
  | `(sol_expr| $a % $b) => bin ``BinOp.mod a b
  | `(sol_expr| $a + $b) => bin ``BinOp.add a b
  | `(sol_expr| $a - $b) => bin ``BinOp.sub a b
  | `(sol_expr| $a < $b) => bin ``BinOp.lt a b
  | `(sol_expr| $a > $b) => bin ``BinOp.gt a b
  | `(sol_expr| $a <= $b) => bin ``BinOp.le a b
  | `(sol_expr| $a >= $b) => bin ``BinOp.ge a b
  | `(sol_expr| $a == $b) => bin ``BinOp.eqB a b
  | `(sol_expr| $a != $b) => bin ``BinOp.neB a b
  | `(sol_expr| $a && $b) => bin ``BinOp.and a b
  | `(sol_expr| $a || $b) => bin ``BinOp.or a b
  | _ => Macro.throwUnsupported
where
  bin (op : Lean.Name) (a b : TSyntax `sol_expr) : MacroM Term := do
    `(RawExpr.binop $(mkIdent op) $(← expandExpr a) $(← expandExpr b))

partial def expandTy : TSyntax `sol_ty → MacroM Term
  | `(sol_ty| $x:ident) => `(RawTy.named $(quote x.getId.toString))
  | `(sol_ty| mapping ( $k => $v )) => do `(RawTy.mapping $(← expandTy k) $(← expandTy v))
  | `(sol_ty| $t[]) => do `(RawTy.array $(← expandTy t))
  | _ => Macro.throwUnsupported

partial def expandStmt (s : TSyntax `sol_stmt) : MacroM Term := do
  -- `delete x` also parses as a declaration `T x` of a type called
  -- `delete`, and `require(c)` as a call (the categories read keywords as
  -- identifiers too): of an ambiguous parse, take the reading that starts
  -- with a keyword.
  if s.raw.isOfKind choiceKind then
    let alts := s.raw.getArgs
    let kw := alts.filter (·[0].isAtom)
    for alt in kw ++ alts do
      try return ← expandStmt ⟨alt⟩ catch _ => pure ()
    Macro.throwUnsupported
  -- the four keyword statements, by their node kind: a quotation pattern
  -- for them would be as ambiguous as the parse
  match s.raw.getKind with
  | ``solDelete => `(RawStmt.delete $(← expandExpr ⟨s.raw[1]⟩))
  | ``solRequire => `(RawStmt.require $(← expandExpr ⟨s.raw[2]⟩))
  | ``solAssert => `(RawStmt.assert $(← expandExpr ⟨s.raw[2]⟩))
  | ``solRevert => `(RawStmt.revert)
  | _ => expandStmt1 s
where
  expandStmt1 : TSyntax `sol_stmt → MacroM Term
  | `(sol_stmt| $l:sol_expr = $r:sol_expr) => do
      `(RawStmt.assign $(← expandExpr l) $(← expandExpr r))
  | `(sol_stmt| $l:sol_expr = $b:sol_expr .push()) => do
      `(RawStmt.assignPush $(← expandExpr l) $(← expandExpr b))
  | `(sol_stmt| $l:sol_expr = $f:sol_expr ( )) => do
      `(RawStmt.assignPush $(← expandExpr l) $(← pushRecv f))
  | `(sol_stmt| $T:sol_ty storage $x:ident = $b:sol_expr .push()) => do
      `(RawStmt.declStoragePush $(← expandTy T) $(quote x.getId.toString) $(← expandExpr b))
  | `(sol_stmt| $T:sol_ty storage $x:ident = $f:sol_expr ( )) => do
      `(RawStmt.declStoragePush $(← expandTy T) $(quote x.getId.toString) $(← pushRecv f))
  | `(sol_stmt| $T:sol_ty storage $x:ident = $e) => do
      `(RawStmt.declStorage $(← expandTy T) $(quote x.getId.toString) (some $(← expandExpr e)))
  | `(sol_stmt| $T:sol_ty storage $x:ident) => do
      `(RawStmt.declStorage $(← expandTy T) $(quote x.getId.toString) none)
  | `(sol_stmt| $T:sol_ty memory $x:ident = $e) => do
      `(RawStmt.declMemory $(← expandTy T) $(quote x.getId.toString) (some $(← expandExpr e)))
  | `(sol_stmt| $T:sol_ty memory $x:ident) => do
      `(RawStmt.declMemory $(← expandTy T) $(quote x.getId.toString) none)
  | `(sol_stmt| $T:sol_ty $x:ident = $e) => do
      `(RawStmt.decl $(← expandTy T) $(quote x.getId.toString) (some $(← expandExpr e)))
  | `(sol_stmt| $T:sol_ty $x:ident) => do
      `(RawStmt.decl $(← expandTy T) $(quote x.getId.toString) none)
  | `(sol_stmt| $b:sol_expr .push( $a:sol_expr )) => do
      `(RawStmt.call (.field $(← expandExpr b) "push") [$(← expandExpr a)])
  | `(sol_stmt| $b:sol_expr .push()) => do `(RawStmt.call (.field $(← expandExpr b) "push") [])
  | `(sol_stmt| $b:sol_expr .pop()) => do `(RawStmt.call (.field $(← expandExpr b) "pop") [])
  | `(sol_stmt| $r:sol_expr .transfer( $a:sol_expr )) => do
      `(RawStmt.call (.field $(← expandExpr r) "transfer") [$(← expandExpr a)])
  | `(sol_stmt| $f:sol_expr ( )) => do `(RawStmt.call $(← expandExpr f) [])
  | `(sol_stmt| $f:sol_expr ( $a:sol_expr )) => do
      `(RawStmt.call $(← expandExpr f) [$(← expandExpr a)])
  | `(sol_stmt| $l:sol_expr ++) => do `(RawStmt.incDec .postInc $(← expandExpr l))
  | `(sol_stmt| ++ $l:sol_expr) => do `(RawStmt.incDec .preInc $(← expandExpr l))
  | `(sol_stmt| $x:sol_expr = $l:sol_expr ++) => do
      `(RawStmt.assignIncDec $(← expandExpr x) .postInc $(← expandExpr l))
  | `(sol_stmt| $x:sol_expr = ++ $l:sol_expr) => do
      `(RawStmt.assignIncDec $(← expandExpr x) .preInc $(← expandExpr l))
  | `(sol_stmt| $l:sol_expr += $r) => do `(RawStmt.opAssign .add $(← expandExpr l) $(← expandExpr r))
  | `(sol_stmt| $l:sol_expr -= $r) => do `(RawStmt.opAssign .sub $(← expandExpr l) $(← expandExpr r))
  | `(sol_stmt| $l:sol_expr *= $r) => do `(RawStmt.opAssign .mul $(← expandExpr l) $(← expandExpr r))
  | `(sol_stmt| $l:sol_expr /= $r) => do `(RawStmt.opAssign .div $(← expandExpr l) $(← expandExpr r))
  | `(sol_stmt| $l:sol_expr %= $r) => do `(RawStmt.opAssign .mod $(← expandExpr l) $(← expandExpr r))
  | `(sol_stmt| if ($c) $t $[else $f]?) => do
      let els ← match f with
        | some f => expandBlock f
        | none => `([])
      `(RawStmt.ite $(← expandExpr c) $(← expandBlock t) $els)
  | _ => Macro.throwUnsupported
  /-- `values.push` (one identifier) or `e.push`: the receiver `values`, `e`. -/
  pushRecv (f : TSyntax `sol_expr) : MacroM Term := do
    match f with
    | `(sol_expr| $x:ident) =>
      match (nameParts x.getId).reverse with
      | "push" :: r :: rs =>
        (rs.reverse.foldlM (init := ← `(RawExpr.name $(quote r))) fun acc c =>
          `(RawExpr.field $acc $(quote c))) >>= fun e => pure e
      | _ => Macro.throwErrorAt f "only `b.push()` is a call on the right of `=`"
    | `(sol_expr| $e:sol_expr . $g:ident) =>
      if g.getId.toString == "push" then expandExpr ⟨e.raw⟩
      else Macro.throwErrorAt f "only `b.push()` is a call on the right of `=`"
    | _ => Macro.throwErrorAt f "only `b.push()` is a call on the right of `=`"
  expandBlock : TSyntax `sol_block → MacroM Term
    | `(sol_block| { $[$ss:sol_stmt;]* }) => do `([$(← ss.mapM expandStmt),*])
    | _ => Macro.throwUnsupported

macro_rules
  | `(sol_raw!{ $[$ss:sol_stmt;]* }) => do `([$(← ss.mapM expandStmt),*])

end Expand

/-! ## The elaborator

Synthesis returns a path or a value with its type; checking takes the
expected primitive type, which is how a literal gets one.  Every proof a
constructor needs comes from a `match h : …` on the check that justifies
it.  A local shadows nothing: a declaration may not reuse the name of a
local in scope or of a state variable. -/

/-- What a local in scope holds. -/
inductive LocalTy where
  | val (p : PrimTy)
  | alias (R : RefTy)
  | mem (R : RefTy)
  deriving DecidableEq, Repr

/-- The locals in scope, most recent first. -/
abbrev ECtx := List (Name × LocalTy)

def elabTy : RawTy → Ty
  | .named "uint" | .named "address" => .uint
  | .named "int" => .int
  | .named "bool" => .bool
  | .named s => .struct s
  | .mapping k v => .mapping (elabTy k) (elabTy v)
  | .array t => .array (elabTy t)

def primName : PrimTy → String
  | .uint => "uint" | .int => "int" | .bool => "bool"

/-- A synthesised expression: a storage path, a memory path, or a value. -/
inductive TExpr (C : Contract) where
  | path (T : Ty) (p : SPath C T)
  | mpath (T : Ty) (p : MPath C T)
  | val (p : PrimTy) (v : Val C p)

/-- A path of primitive type is read as a value. -/
def TExpr.toVal? {C : Contract} : TExpr C → Option ((p : PrimTy) × Val C p)
  | .val p v => some ⟨p, v⟩
  | .path (.prim p) (.loc l) => some ⟨p, .read l⟩
  | .mpath (.prim p) (.loc l) => some ⟨p, .readMem l⟩
  | .path _ _ | .mpath _ _ => none

section Elab

variable [FreshNames] (C : Contract)

mutual

def synth (Γ : ECtx) : RawExpr → Except String (TExpr C)
  | .num n => pure (.val .uint (.simple (.lit n rfl)))
  | .bool b => pure (.val .bool (.simple (.bool b)))
  | .name x =>
    match lookupBy x Γ with
    | some (.val p) => pure (.val p (.simple (.local (Var.ofName x))))
    | some (.alias R) => pure (.path (.ref R) (.alias (Var.ofName x)))
    | some (.mem R) => pure (.mpath (.ref R) (.var (Var.ofName x)))
    | none =>
      match hr : C.rootType x with
      | some T => pure (.path T (.loc (.root x hr)))
      | none => throw s!"unknown name {x}"
  | .field e f => do
    match ← synth Γ e with
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
    | .path (.ref (.array E)) b => pure (.path E (.loc (.index .arr b (← check Γ .uint k))))
    | .mpath (.ref (.array E)) b => pure (.mpath E (.loc (.index b (← check Γ .uint k))))
    | _ => throw "indexing something that is not a mapping or an array"
  | .binop op a b => do
    -- the operand type: the first operand that is not a literal gives it
    let t ← if a matches .num _ then synth Γ b else synth Γ a
    let some ⟨p, _⟩ := t.toVal? | throw "an operand of reference type"
    match h : op.accepts p with
    | true => pure (.val _ (.binop op h rfl (← check Γ p a) (← check Γ p b)))
    | false => throw s!"operator {BinOp.sym op} does not take {primName p}"
  | .ternary c a b => do
    let t ← if a matches .num _ then synth Γ b else synth Γ a
    let some ⟨p, _⟩ := t.toVal? | throw "a conditional of reference type"
    pure (.val p (.ternary (← check Γ .bool c) (← check Γ p a) (← check Γ p b)))
  | .unop op a => do
    let some ⟨p, a⟩ := (← synth Γ a).toVal? | throw "an operand of reference type"
    match h : op.accepts p with
    | true => pure (.val _ (.unop op h rfl a))
    | false => throw s!"operator {UnOp.sym op} does not take {primName p}"
termination_by e => (sizeOf e, 0)

def check (Γ : ECtx) (p : PrimTy) : RawExpr → Except String (Val C p)
  | .num n =>
    match h : p.isNumeric with
    | true => pure (.simple (.lit n h))
    | false => throw s!"a number where a {primName p} is expected"
  | e => do
    let some ⟨q, v⟩ := (← synth Γ e).toVal? |
      throw s!"a storage reference where a {primName p} is expected"
    if h : q = p then pure (h ▸ v) else throw s!"a {primName q} where a {primName p} is expected"
termination_by e => (sizeOf e, 1)

end

/-- `e` as a storage path of type `T`. -/
def checkPath (Γ : ECtx) (T : Ty) (e : RawExpr) : Except String (SPath C T) := do
  match ← synth C Γ e with
  | .path T' p => if h : T' = T then pure (h ▸ p) else throw "a storage path of another type"
  | .mpath .. | .val .. => throw "a value where a storage reference is expected"

/-- `e` as a memory path of type `T`. -/
def checkMPath (Γ : ECtx) (T : Ty) (e : RawExpr) : Except String (MPath C T) := do
  match ← synth C Γ e with
  | .mpath T' p => if h : T' = T then pure (h ▸ p) else throw "a memory path of another type"
  | .path .. | .val .. => throw "a memory reference is expected"

/-- What a memory local is bound to: a memory path by identity, or a storage
path deep-copied. -/
def elabMRhs (Γ : ECtx) (R : RefTy) (e : RawExpr) : Except String (MRhs C R) := do
  match ← synth C Γ e with
  | .mpath T p => if h : T = .ref R then pure (.alias (h ▸ p)) else throw "a memory path of another type"
  | .path T p =>
    if h : T = .ref R then
      match hm : (Ty.ref R).mapFree with
      | true => pure (.copy (h ▸ p) hm)
      | false => throw "a copy into memory of a type that holds a mapping"
    else throw "a storage path of another type"
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
variable a capture declares. -/
abbrev ElabM := StateT (ECtx × Nat) (Except String)

/-- A fresh variable for a capture, `ie1`, `sp2`: numbered past every
variable the program itself writes. -/
def freshCapture (base : String) : ElabM Var := do
  let (Γ, k) ← get
  set (Γ, k + 1)
  pure (.fresh base k)

/-- A compound assignment's target, with a non-simple index captured into a
fresh `ie` first: `values[i + 1] += 1;` is `uint ie1 = i + 1; values[ie1] += 1;`. -/
def elabOpTarget (l : RawExpr) : ElabM (Prog C × (p : PrimTy) × OpLoc C p) := do
  let (Γ, _) ← get
  match ← synth C Γ l with
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
  | .mpath (.prim p) (.loc (.index b i)) =>
    match i.toSimple? with
    | some ie => pure ([], ⟨p, .mindex b ie⟩)
    | none =>
      let x ← freshCapture "ie"
      pure ([.declLocal .uint x (some i)], ⟨p, .mindex b (.local x)⟩)
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
    | .mindex b i =>
      let x ← freshCapture "mv"
      pure (pre ++ [.declMem (.array _) x (some (.alias b)) rfl], ⟨p, .mindex (.var x) i, rfl⟩)
    | .local _ | .root .. => nomatch hs

/-- Declare `x` in scope. -/
def declare (x : Name) (t : LocalTy) : ElabM Unit := do
  let (Γ, k) ← get
  checkFresh C Γ x
  set (setBy x t Γ, k)

mutual

/-- A statement, as a block: a compound target may need a capture first. -/
def elabStmt : RawStmt → ElabM (Prog C)
  | .assign l r => do
    let (Γ, _) ← get
    match ← synth C Γ l with
    | .val p (.simple (.local x)) => pure [.assignLocal x (← check C Γ p r)]
    | .val .. => throw "assigning to a value"
    | .path (.prim p) (.loc l) => pure [.assign l (.val (← check C Γ p r))]
    | .path (.ref R) (.loc l) =>
      match ← synth C Γ r with
      | .mpath T mp =>
        if hT : T = .ref R then pure [.assignFromMem l (hT ▸ mp)]
        else throw "a memory path of another type"
      | _ =>
        match h : (Ty.ref R).mapFree with
        | true => pure [.assign l (.copy (← checkPath C Γ (.ref R) r) h)]
        | false => throw "a storage copy of a type that holds a mapping"
    | .path (.ref R) (.alias x) => pure [.rebind x (.path (← checkPath C Γ (.ref R) r))]
    | .mpath (.ref R) (.var x) => pure [.rebindMem x (← elabMRhs C Γ R r)]
    | .mpath (.prim p) (.loc l) => pure [.assignMem l (.val (← check C Γ p r))]
    | .mpath (.ref R) (.loc l) => pure [.assignMem l (.ref (← checkMPath C Γ (.ref R) r))]
  | .decl T x init => do
    let .prim p := elabTy T | throw s!"{x}: a reference type needs a data location"
    let (Γ, _) ← get
    let init ← StateT.lift (init.mapM (check C Γ p))
    declare C x (.val p)
    pure [.declLocal p (Var.ofName x) init]
  | .declStorage T x init => do
    let .ref R := elabTy T | throw s!"{x}: `storage` on a value type"
    let (Γ, _) ← get
    let init ← StateT.lift (init.mapM fun e => ARhs.path <$> checkPath C Γ (.ref R) e)
    declare C x (.alias R)
    pure [.declStorage R (Var.ofName x) init]
  | .declStoragePush T x b => do
    let .ref R := elabTy T | throw s!"{x}: `storage` on a value type"
    let (Γ, _) ← get
    let r ← elabPush C Γ R b
    declare C x (.alias R)
    pure [.declStorage R (Var.ofName x) (some r)]
  | .assignPush l b => do
    let (Γ, _) ← get
    match ← synth C Γ l with
    | .path (.ref R) (.alias x) => pure [.rebind x (← elabPush C Γ R b)]
    | _ => throw "`= b.push()` binds a storage pointer"
  | .declMemory T x init => do
    let .ref R := elabTy T | throw s!"{x}: `memory` on a value type"
    let (Γ, _) ← get
    let s ← match init with
      | some e => pure (Stmt.declMem R (Var.ofName x) (some (← elabMRhs C Γ R e)) rfl)
      | none =>
        match hd : (Ty.ref R).defaultOkS with
        | true => pure (Stmt.declMem R (Var.ofName x) none (by simp [hd]))
        | false => throw s!"{x}: a memory object whose default is not well-formed"
    declare C x (.mem R)
    pure [s]
  | .delete e => do
    let (Γ, _) ← get
    match ← synth C Γ e with
    | .path T (.loc l) =>
      if T matches .ref (.mapping ..) then throw "a mapping cannot be deleted"
      else pure [.delete l]
    | .path _ (.alias _) => throw "`delete` on a storage pointer"
    | .mpath .. => throw "`delete` in memory is not a statement yet"
    | .val .. => throw "`delete` needs a storage location"
  | .opAssign op l r => do
    let (pre, ⟨p, t⟩) ← elabOpTarget C l
    let (Γ, _) ← get
    match hop : op.hasCompoundAssign, hp : p.isNumeric with
    | true, true => pure (pre ++ [.opAssign op hop hp t (← check C Γ p r)])
    | false, _ => throw s!"no compound assignment for {BinOp.sym op}"
    | _, false => throw s!"a compound assignment at {primName p}"
  | .incDec op l => do
    let (pre, ⟨p, t⟩) ← elabOpTarget C l
    match hp : p.isNumeric with
    | true => pure (pre ++ [.incDec op hp t])
    | false => throw s!"++ or -- at {primName p}"
  | .assignIncDec x op l => do
    let (pre, ⟨p, t, hs⟩) ← elabIncTarget C l
    let (Γ, _) ← get
    match ← synth C Γ x with
    | .val q (.simple (.local y)) =>
      match hp : p.isNumeric with
      | true => if q = p then pure (pre ++ [.assignIncDec y op hp t hs])
                else throw s!"a {primName p} assigned to a {primName q}"
      | false => throw s!"++ or -- at {primName p}"
    | _ => throw "the result of ++ or -- goes to a stack local"
  | .call (.field e "push") args => do
    let (Γ, _) ← get
    let .path (.ref (.array E)) b ← synth C Γ e | throw "push on something that is not an array"
    match args with
    | [] =>
      match hd : E.defaultOkS with
      | true => pure [.push b none (by simp [hd])]
      | false => throw "push() of an element whose default is not well-formed"
    | [a] =>
      match E with
      | .prim p => pure [.push b (some (.val (← check C Γ p a))) rfl]
      | .ref R =>
        match h : (Ty.ref R).mapFree with
        | true => pure [.push b (some (.copy (← checkPath C Γ (.ref R) a) h)) rfl]
        | false => throw "a push copying a type that holds a mapping"
    | _ => throw "push takes at most one argument"
  | .call (.field e "pop") [] => do
    let (Γ, _) ← get
    let .path (.ref (.array _)) b ← synth C Γ e | throw "pop on something that is not an array"
    pure [.pop b]
  | .call (.field e "transfer") [a] => do
    let (Γ, _) ← get
    pure [.transfer (← check C Γ .uint e) (← check C Γ .uint a)]
  | .call .. => throw "only push, pop and transfer are calls here"
  | .ite c thn els => do
    let (Γ, _) ← get
    let c ← check C Γ .bool c
    let thn ← elabBranch thn
    let els ← elabBranch els
    pure [.ite c thn els]
  | .require c => do
    let (Γ, _) ← get
    pure [.require (← check C Γ .bool c)]
  | .assert c => do
    let (Γ, _) ← get
    pure [.assert (← check C Γ .bool c)]
  | .revert => pure [.revert]

/-- A block. -/
def elabStmts : List RawStmt → ElabM (Prog C)
  | [] => pure []
  | s :: ss => do
    let P ← elabStmt s
    let Q ← elabStmts ss
    pure (P ++ Q)

/-- A branch: its declarations stay inside it. -/
def elabBranch (ss : List RawStmt) : ElabM (Prog C) := do
  let (Γ, _) ← get
  let P ← elabStmts ss
  let (_, k) ← get
  set (Γ, k)
  pure P

end

mutual

/-- The largest index among the fresh variables a raw program writes. -/
def RawExpr.maxIdx : RawExpr → Nat
  | .name x => (Var.ofName x).idx
  | .field e _ => e.maxIdx
  | .index e k => max e.maxIdx k.maxIdx
  | .binop _ a b => max a.maxIdx b.maxIdx
  | .unop _ a => a.maxIdx
  | .ternary c a b => max c.maxIdx (max a.maxIdx b.maxIdx)
  | .num _ | .bool _ => 0

end

def RawExpr.maxIdxs : List RawExpr → Nat
  | [] => 0
  | e :: es => max e.maxIdx (RawExpr.maxIdxs es)

mutual

def RawStmt.maxIdx : RawStmt → Nat
  | .assign l r | .assignPush l r => max l.maxIdx r.maxIdx
  | .decl _ x i | .declStorage _ x i | .declMemory _ x i =>
    max (Var.ofName x).idx ((i.map RawExpr.maxIdx).getD 0)
  | .declStoragePush _ x b => max (Var.ofName x).idx b.maxIdx
  | .delete e | .incDec _ e | .require e | .assert e => e.maxIdx
  | .opAssign _ l r | .assignIncDec l _ r => max l.maxIdx r.maxIdx
  | .call f as => max f.maxIdx (RawExpr.maxIdxs as)
  | .ite c t e => max c.maxIdx (max (RawStmt.maxIdxs t) (RawStmt.maxIdxs e))
  | .revert => 0

def RawStmt.maxIdxs : List RawStmt → Nat
  | [] => 0
  | s :: ss => max s.maxIdx (RawStmt.maxIdxs ss)

end

/-- Elaborate a block against `C`, from no locals.  A capture is numbered
past every fresh variable the block writes. -/
def elabProg (ss : List RawStmt) : Except String (Prog C) :=
  (elabStmts C ss).run' ([], RawStmt.maxIdxs ss + 1)

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

section Quote
open Lean (mkAppN mkConst toExpr)

/-- `a = a`. -/
def quoteRefl (α a : Lean.Expr) : Lean.Expr := mkAppN (mkConst ``Eq.refl [1]) #[α, a]

/-- `true = true`: every Boolean side condition. -/
def rflTrue : Lean.Expr := quoteRefl (mkConst ``Bool) (mkConst ``Bool.true)

/-- `some T = some T`: every contract lookup. -/
def rflSome (T : Ty) : Lean.Expr :=
  quoteRefl (mkAppN (mkConst ``Option [0]) #[mkConst ``Ty])
    (mkAppN (mkConst ``Option.some [0]) #[mkConst ``Ty, toExpr T])

def optE (α : Lean.Expr) : Option Lean.Expr → Lean.Expr
  | none => mkAppN (mkConst ``Option.none [0]) #[α]
  | some a => mkAppN (mkConst ``Option.some [0]) #[α, a]

def IndexTy.quote : {R : RefTy} → {k : PrimTy} → {V : Ty} → IndexTy R k V → Lean.Expr
  | _, _, _, @IndexTy.map k V => mkAppN (mkConst ``IndexTy.map) #[toExpr k, toExpr V]
  | _, _, _, @IndexTy.arr E => mkAppN (mkConst ``IndexTy.arr) #[toExpr E]

variable {C : Contract} (c : Lean.Expr)

def Simple.quote : (p : PrimTy) → Simple C p → Lean.Expr
  | p, .lit n _ => mkAppN (mkConst ``Simple.lit) #[c, toExpr p, toExpr n, rflTrue]
  | _, .bool b => mkAppN (mkConst ``Simple.bool) #[c, toExpr b]
  | p, .local x => mkAppN (mkConst ``Simple.local) #[c, toExpr p, toExpr x]

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
  | E, .index b i => mkAppN (mkConst ``MLoc.index) #[c, toExpr E, MPath.quote _ b, Val.quote .uint i]

def Val.quote : (p : PrimTy) → Val C p → Lean.Expr
  | p, .simple s => mkAppN (mkConst ``Val.simple) #[c, toExpr p, Simple.quote c p s]
  | p, .read l => mkAppN (mkConst ``Val.read) #[c, toExpr p, Loc.quote _ l]
  | _, @Val.binop _ p q op _ _ a b =>
    mkAppN (mkConst ``Val.binop) #[c, toExpr p, toExpr q, toExpr op, rflTrue,
      quoteRefl (mkConst ``PrimTy) (toExpr q), Val.quote p a, Val.quote p b]
  | _, @Val.unop _ p q op _ _ a =>
    mkAppN (mkConst ``Val.unop) #[c, toExpr p, toExpr q, toExpr op, rflTrue,
      quoteRefl (mkConst ``PrimTy) (toExpr q), Val.quote p a]
  | p, .ternary cv a b =>
    mkAppN (mkConst ``Val.ternary) #[c, toExpr p, Val.quote .bool cv, Val.quote p a, Val.quote p b]
  | p, .readMem l => mkAppN (mkConst ``Val.readMem) #[c, toExpr p, MLoc.quote _ l]

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
  | p, .mindex b i =>
    mkAppN (mkConst ``OpLoc.mindex) #[c, toExpr p, MPath.quote c _ b, Simple.quote c .uint i]

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
  | .declMem R x init _ =>
    mkAppN (mkConst ``Stmt.declMem) #[c, toExpr R, toExpr x,
      optE (mkAppN (mkConst ``MRhs) #[c, toExpr R]) (init.map (MRhs.quote c R)), rflTrue]
  | @Stmt.rebindMem _ R x r => mkAppN (mkConst ``Stmt.rebindMem) #[c, toExpr R, toExpr x, MRhs.quote c R r]
  | @Stmt.assignFromMem _ R l p =>
    mkAppN (mkConst ``Stmt.assignFromMem) #[c, toExpr R, Loc.quote c _ l, MPath.quote c _ p]
  | @Stmt.assignMem _ T l r => mkAppN (mkConst ``Stmt.assignMem) #[c, toExpr T, MLoc.quote c T l, MSrc.quote c T r]
  | @Stmt.delete _ T l => mkAppN (mkConst ``Stmt.delete) #[c, toExpr T, Loc.quote c T l]
  | .ite cond thn els =>
    mkAppN (mkConst ``Stmt.ite) #[c, Val.quote c .bool cond, Prog.quote thn, Prog.quote els]
  | .require cond => mkAppN (mkConst ``Stmt.require) #[c, Val.quote c .bool cond]
  | .assert cond => mkAppN (mkConst ``Stmt.assert) #[c, Val.quote c .bool cond]
  | .revert => mkAppN (mkConst ``Stmt.revert) #[c]

def Prog.quote : List (Stmt C) → Lean.Expr
  | [] => mkAppN (mkConst ``List.nil [0]) #[mkAppN (mkConst ``Stmt) #[c]]
  | s :: P => mkAppN (mkConst ``List.cons [0]) #[mkAppN (mkConst ``Stmt) #[c], Stmt.quote s, Prog.quote P]

end

end Quote

/-! ## `sol[C]{ … }` -/

/-- `sol[C]{ s₁; s₂; … }`: the statements, elaborated against the named
contract `C`. -/
syntax "sol[" term "]{" (sol_stmt ";")* "}" : term

/-- `sol{ … }`: `sol[C]{ … }` for the file's `InContract` contract. -/
syntax "sol{" (sol_stmt ";")* "}" : term

open Lean Elab Term Meta in
/-- Run `f C` at compile time for the contract the term `c` names, and splice
the term it computes; an elaboration error is reported at the source.  `c`
is unfolded through instances only, so it may be `InContract.contract` but
must end at a named contract. -/
def elabAgainst (c : Lean.Term) (f : Lean.Term → TermElabM Lean.Term) : TermElabM Lean.Expr := do
  let C ← withTransparency .instances <| whnf (← elabTermAndSynthesize c (mkConst ``Contract))
  let some n := C.constName? | throwError "not a named contract: {C}"
  let t ← f (← `(Lean.mkConst $(quote n)))
  let ty := mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String) (mkConst ``Lean.Expr)
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  match ← unsafe evalExpr (Except String Lean.Expr) ty e with
  | .ok r => pure r
  | .error msg => throwError "Solidity elaboration failed: {msg}"

open Lean Elab Term Meta in
elab_rules : term
  | `(sol[ $c ]{ $[$ss:sol_stmt;]* }) => do
    let raw ← `(sol_raw!{ $[$ss;]* })
    elabAgainst c fun q => `((elabProg $c $raw).map (Prog.quote $q))

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

end Examples

end Solidity
