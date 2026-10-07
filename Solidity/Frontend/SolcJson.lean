import Lean.Data.Json
import Solidity.Syntax

/-!
# solc's JSON AST, printed as `sol` text

The front end reads a contract from the AST solc writes
(`scripts/solc-ast.mjs` makes the fixture) and prints each function's body
as the text `sol_raw!{ … }` reads, so the one lowering path is the macros'
(`Syntax.lean`): nothing here builds a `RawStmt`.  The printer only
normalises what the grammar spells differently from Solidity:

* an expression of literals only (solc's type `int_const …` or
  `rational_const …`) is folded to its decimal value, in exact rational
  arithmetic as solc evaluates it at compile time (`2**256 - 1`,
  `7 / 2 * 2` is `7`), units (`1 gwei`, `2 days`, `unitFactor?`) and
  spellings (`0xff`, `1_000`, `2e3`, `0.5 ether`) included; a value that is
  not an integer is a `Gap`;
* a conversion to `address`, `address payable` or a contract is the address
  itself (an `address` is a `uint`), so `payable(owner)` is `owner`;
* `++`/`--` are spelt from solc's `prefix` flag, the decrement `−−` (two
  U+2212: `--` opens a Lean comment);
* a `bool` key of a mapping is the `uint` solc encodes it as, `0` or `1`: the
  mapping is declared `mapping(uint => V)` and `m[b]` is `m[b ? 1 : 0]`;
* a member of a pushed element reads the element through a storage local
  declared before the statement
  (`T storage pushRef1 = x.push(); pushRef1.f = v;`), only where that is
  solc's order: the left-hand side of an assignment of a constant, or a
  declaration's whole initial value.  Anywhere else (a right-hand side that
  reads state, a condition, a short-circuit operand) the hoisted push would
  run before, or instead of, what solc runs first, so it is a `Gap`;
* named arguments, `h({b: 1, a: 2})`, are put in the callee's parameter
  order, the order solc evaluates them in;
* a local named like a state variable or a Lean keyword is renamed with a
  trailing `_`, by its declaration (`referencedDeclaration`), so a member of
  the same name is untouched;
* a struct is the struct table's (`Semantics.structDef`), under the renames
  the import names, and its members are checked against the table, member
  by member; a struct that is not there, or differs, leaves out what uses it;
* a tuple of several components is printed where solkey reads one
  (`SolJSONParser.parseTupleStatement`): `(a, , b) = v`,
  `(uint x, , bool y) = v` and `return (a, b)`, the value a tuple or a call
  of a function by name (`requireTupleValue`);
* `(bool ok, ) = R.call{value: V}("")`, matched exactly as
  `SolJSONParser.isValueCall` matches it, is `bool ok = R.send(V)`; any
  other value call is a `Gap`.  solc forwards all gas there and `send` the
  2300-gas stipend, so the result is faithful only under the callback
  reading (`holdsC`, `docs/solc-alignment.md`);
* an unnamed value a `try`'s call returns is bound to a fresh `tryRetN`,
  which nothing reads;
* a loop is printed as written, `while`, `for`, `do … while`, `break`,
  `continue` (the macros lower them), its `/// @custom:key` clauses above it
  from the fixture's `loopSpec` (`loopSpec`);
* every function called by name is a `contract!` member
  (`SolcContract.funMembers`), callees first: a call is inlined where it is
  called.  A call that recurses, or of a function left out, leaves the
  caller out.

What the printer cannot write is a `Gap`, reported with its source line:
`excluded` where the model has no counterpart (a struct recursive through a
mapping), `unsupported` where the printer or the grammar lacks the form.
What would change a function's meaning if it were dropped is a `Gap` too: a
modifier on the function, a `constant` or `immutable` state variable (a
value, not a storage slot), an overloaded name.  A contract that inherits
is refused whole.  A mutable state variable's initial value and the
constructor are creation code: an obligation holds from any well-typed
storage (solkey's do too), so they are read past, not reported.
-/

namespace Solidity.Frontend

open Lean (Json)
open Semantics

/-- Why a function, or a state variable, is left out. -/
inductive Gap where
  /-- The model has no counterpart (`docs/testsuite-proofs.md` lists them). -/
  | excluded (msg : String) (line : Nat := 0)
  /-- The printer or the grammar lacks the form. -/
  | unsupported (msg : String) (line : Nat := 0)
  deriving Repr, Inhabited

def Gap.msg : Gap → String
  | .excluded m _ | .unsupported m _ => m

/-- The source line of the statement it arose in, `0` if none. -/
def Gap.line : Gap → Nat
  | .excluded _ l | .unsupported _ l => l

/-- solkey's obligation for a function, from its `@custom:key` clauses and
its contract's (`tagOf`). -/
inductive Tag where
  /-- unspecified: `⟨f⟩ true` -/
  | diamond
  /-- unspecified, `@custom:key box`: `[f] true` -/
  | box
  /-- `@custom:key skip`: no obligation -/
  | skip
  /-- a `requires`, `ensures` or `invariant` clause, its own or its
  contract's: solkey's obligation is the specification's, not stated here -/
  | specified
  /-- neither `public` nor `external`: solkey states no obligation -/
  | internal
  /-- a clause solkey refuses to read: no obligation -/
  | malformed
  deriving Repr, DecidableEq, Inhabited

def Tag.toStr : Tag → String
  | .diamond => "diamond"
  | .box => "box"
  | .skip => "skip"
  | .specified => "specified"
  | .internal => "internal"
  | .malformed => "malformed"

/-- A function as read: its parameters (name, `sol` type) and its body as
statements of `sol` text, or why there is none. -/
structure SolcFun where
  name : String
  line : Nat
  tag : Tag
  params : List (String × String)
  /-- The statements, each with the source line of the statement it prints. -/
  body : Except Gap (List (Nat × String))
  /-- Its return variables (name, `sol` type), the name `""` when unnamed. -/
  rets : List (String × String) := []
  /-- The functions of the contract it calls, directly or not, callees first. -/
  calls : List String := []
  deriving Inhabited

/-- A contract as read: the `contract!` members of the state variables it
keeps, the ones it leaves out and why, its functions. -/
structure SolcContract where
  name : String
  members : List String
  dropped : List (String × Gap)
  funs : List SolcFun
  /-- The functions some function calls, each as its `contract!` member
  (`function f(uint x) returns (uint) { … }`), callees first. -/
  funMembers : List (String × String) := []
  deriving Inhabited

/-! ## Reading the JSON -/

namespace J

def get (j : Json) (k : String) : Except Gap Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error e => throw (.unsupported s!"solc JSON: {e}")

def opt (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

def str (j : Json) (k : String) : Except Gap String :=
  match j.getObjValAs? String k with
  | .ok v => pure v
  | .error e => throw (.unsupported s!"solc JSON: {e}")

def arr (j : Json) (k : String) : Except Gap (List Json) := do
  match (← get j k).getArr? with
  | .ok a => pure a.toList
  | .error e => throw (.unsupported s!"solc JSON: {e}")

def kind (j : Json) : String := (j.getObjValAs? String "nodeType").toOption.getD ""

def line (j : Json) : Nat := (j.getObjValAs? Nat "line").toOption.getD 0

def ref? (j : Json) : Option Int := (j.getObjValAs? Int "referencedDeclaration").toOption

def id? (j : Json) : Option Int := (j.getObjValAs? Int "id").toOption

/-- solc's type of an expression, `typeDescriptions.typeString`. -/
def tyStr (j : Json) : String :=
  ((j.getObjVal? "typeDescriptions").toOption.bind
    fun t => (t.getObjValAs? String "typeString").toOption).getD ""

/-- Every node of `j`, depth first. -/
partial def nodes (j : Json) : List Json :=
  match j with
  | .arr a => a.toList.flatMap nodes
  | .obj kvs =>
    let sub := kvs.toList.flatMap fun (_, v) => nodes v
    if (j.getObjVal? "nodeType").isOk then j :: sub else sub
  | _ => []

end J

/-! ## Types -/

/-- Lean's reserved words a Solidity local could be named. -/
def leanKeywords : List String :=
  ["at", "by", "do", "fun", "have", "show", "from", "in", "let", "then", "with", "where",
   "match", "end", "open", "import", "structure", "class", "instance", "theorem", "def",
   "example", "abbrev", "namespace", "section", "variable", "universe", "local", "macro",
   "syntax", "deriving", "mutual", "partial", "private", "protected", "noncomputable",
   "unsafe", "calc", "suffices", "obtain", "nomatch", "nofun", "forall", "exists", "Type",
   "Sort", "Prop", "if", "else", "for", "unless", "return", "try", "catch", "finally",
   "break", "continue", "mut", "rec", "fun", "λ", "delete", "new", "true", "false"]

/-- The structs as the import reads them: the Solidity name, and the table's
name or why it is left out. -/
abbrev Structs := List (String × Except Gap String)

/-- The `sol` spelling of an elementary type. -/
def elemTy (name : String) (payable : Bool) : String :=
  match name with
  | "uint256" => "uint"
  | "int256" => "int"
  | "address" => if payable then "address payable" else "address"
  | n => n

/-- A type node as `sol` text: a mapping's `bool` key is its `uint`. -/
partial def tyText (S : Structs) (j : Json) : Except Gap String := do
  match J.kind j with
  | "ElementaryTypeName" =>
    let n ← J.str j "name"
    pure (elemTy n ((J.opt j "stateMutability").any (· == .str "payable")))
  | "UserDefinedTypeName" =>
    let n ← match J.opt j "pathNode" with
      | some p => J.str p "name"
      | none => J.str j "name"
    match lookupBy n S with
    | some (.ok m) => pure m
    | some (.error g) => throw g
    | none => throw (.unsupported s!"type `{n}` is not a struct of the contract")
  | "ArrayTypeName" =>
    let b ← tyText S (← J.get j "baseType")
    match J.opt j "length" with
    | none => pure s!"{b}[]"
    | some l => pure s!"{b}[{← J.str l "value"}]"
  | "Mapping" =>
    let k ← tyText S (← J.get j "keyType")
    let k := if k == "bool" then "uint" else k
    pure s!"mapping({k} => {← tyText S (← J.get j "valueType")})"
  | k => throw (.unsupported s!"type node `{k}`")

/-- A type node as a `Ty`, to compare a struct's members with the table. -/
partial def tyOf (S : List (String × String)) (j : Json) : Except String Ty := do
  match J.kind j with
  | "ElementaryTypeName" =>
    let n ← (j.getObjValAs? String "name")
    match PrimTy.ofName? n with
    | some p => pure (.prim p)
    | none => throw s!"type `{n}`"
  | "UserDefinedTypeName" =>
    let n ← match (j.getObjVal? "pathNode").toOption with
      | some p => p.getObjValAs? String "name"
      | none => j.getObjValAs? String "name"
    pure (.ref (.struct ((lookupBy n S).getD n)))
  | "ArrayTypeName" =>
    let b ← tyOf S (← j.getObjVal? "baseType")
    match (j.getObjVal? "length").toOption with
    | none | some .null => pure (.ref (.array b))
    | some l =>
      let v ← l.getObjValAs? String "value"
      match v.toNat? with
      | some n => pure (.ref (.fixed b n))
      | none => throw s!"array length `{v}`"
  | "Mapping" =>
    pure (.ref (.mapping (← tyOf S (← j.getObjVal? "keyType")) (← tyOf S (← j.getObjVal? "valueType"))))
  | k => throw s!"type node `{k}`"

/-- Does the type node name the struct `s`? -/
partial def mentionsStruct (s : String) (j : Json) : Bool :=
  (J.nodes j).any fun n =>
    J.kind n == "UserDefinedTypeName" &&
      ((J.opt n "pathNode").bind (fun p => (p.getObjValAs? String "name").toOption)) == some s

/-- Does a mapping inside the type node name the struct `s`? -/
def mentionsThroughMapping (s : String) (j : Json) : Bool :=
  (J.nodes j).any fun n => J.kind n == "Mapping" && mentionsStruct s n

/-- The contract's structs against the table: each renamed by `ren`, and
kept when its members are the table's, in order, at the same types. -/
def readStructs (ren : List (String × String)) (defs : List Json) : Structs :=
  defs.map fun d =>
    let n := ((d.getObjValAs? String "name").toOption).getD ""
    let m := (lookupBy n ren).getD n
    let line := J.line d
    let check : Except Gap String := do
      let ms ← J.arr d "members"
      if ms.any (fun x => (J.opt x "typeName").any (mentionsThroughMapping n)) then
        throw (.excluded s!"struct `{n}` (line {line}) is recursive through a mapping: \
          its default value is infinite, and the model's are finite")
      if ms.any (fun x => (J.opt x "typeName").any (mentionsStruct n)) then
        throw (.unsupported s!"struct `{n}` (line {line}) is recursive through an array: \
          the struct table is well-founded by rank (`structDef_rank_lt`), so no struct \
          contains itself")
      let got ← ms.mapM fun x => do
        let f ← J.str x "name"
        match tyOf ren (← J.get x "typeName") with
        | .ok t => pure (f, t)
        | .error e => throw (.unsupported s!"struct `{n}`, member `{f}`: {e}")
      if structDef m == got then pure m
      else if (structDef m).isEmpty then
        throw (.unsupported s!"struct `{n}` (line {line}) is not in the struct table \
          (`Semantics.structDef`)")
      else
        throw (.unsupported s!"struct `{n}` (line {line}) differs from the table's `{m}`: \
          {got.map (·.1)} against {(structDef m).map (·.1)}")
    (n, check)

/-! ## Expressions and statements -/

/-- The printer's state: the name each declaration is printed as, the state
variables left out, the structs, each function's parameter names (by its
declaration's id), the statements to put before the current one (a pushed
element's storage local), a counter for their names, and whether the
current position may hoist a push. -/
structure PState where
  names : List (Int × String) := []
  dropped : List (Int × String × Gap) := []
  structs : Structs := []
  funParams : List (Int × List String) := []
  pre : Array String := #[]
  fresh : Nat := 0
  pushOk : Bool := false
  deriving Inhabited

abbrev PM := StateT PState (Except Gap)

def PM.lift {α : Type} (x : Except Gap α) : PM α := StateT.lift x

/-- An exact rational in lowest terms, `den > 0`: the value solc gives an
expression of literals only. -/
structure Q where
  num : Int
  den : Nat := 1
  deriving BEq, Inhabited

namespace Q

/-- `n / d` in lowest terms; `none` for `d = 0`. -/
def make (n d : Int) : Option Q :=
  if d == 0 then none else
  let g : Nat := Nat.gcd n.natAbs d.natAbs
  let s : Int := if d < 0 then -1 else 1
  some { num := s * n / g, den := d.natAbs / g }

def ofInt (n : Int) : Q := { num := n }

def add (a b : Q) : Option Q := make (a.num * b.den + b.num * a.den) (a.den * b.den)
def sub (a b : Q) : Option Q := make (a.num * b.den - b.num * a.den) (a.den * b.den)
def mul (a b : Q) : Option Q := make (a.num * b.num) (a.den * b.den)
def div (a b : Q) : Option Q := make (a.num * b.den) (a.den * b.num)

/-- The integer, if it is one. -/
def int? (a : Q) : Option Int := if a.den == 1 then some a.num else none

/-- `a ** e`, refused past 4096 bits, as solc refuses a too large constant. -/
def pow (a : Q) (e : Q) : Option Q := do
  let e ← e.int?
  let bits : Nat := Nat.max (Nat.log2 a.num.natAbs) (Nat.log2 a.den) + 1
  if a.num.natAbs > 1 || a.den > 1 then
    if bits * e.natAbs > 4096 then none
  let p : Q := { num := a.num ^ e.natAbs, den := a.den ^ e.natAbs }
  if e < 0 then make p.den p.num else pure p

end Q

/-- A literal's rational value: `0x…` hex, `_` separators, a decimal point,
`MeN` with `N` possibly negative. -/
def parseRational (s : String) : Option Q :=
  let s := s.replace "_" ""
  if s.startsWith "0x" || s.startsWith "0X" then
    (s.drop 2).foldl (fun acc c => do
      let a ← acc
      let d ← if c.isDigit then some (c.toNat - '0'.toNat)
        else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
        else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
        else none
      pure (Q.ofInt (a.num * 16 + d))) (some (Q.ofInt 0))
  else do
    let (m, e) ← match (s.replace "E" "e").splitOn "e" with
      | [m] => some (m, (0 : Int))
      | [m, e] => do
        let e ← if e.startsWith "-" then (e.drop 1).toNat?.map fun n => -(n : Int) else e.toInt?
        pure (m, e)
      | _ => none
    let (i, f) ← match m.splitOn "." with
      | [i] => some (i, "")
      | [i, f] => some (i, f)
      | _ => none
    let digits := i ++ f
    if digits.isEmpty || e.natAbs > 4096 then none
    let n ← digits.toNat?
    let q ← Q.make n (10 ^ f.length)
    if e < 0 then Q.div q (Q.ofInt (10 ^ e.natAbs)) else Q.mul q (Q.ofInt (10 ^ e.natAbs))

/-- Is solc's type of the expression a compile-time constant? -/
def constTy (j : Json) : Bool :=
  let t := J.tyStr j
  t.startsWith "int_const" || t.startsWith "rational_const"

/-- The value of an expression of literals only, as solc computes it: exact
rational arithmetic, the bitwise operators and shifts on integers (`&`, `|`,
`^` on non-negative ones), `%` with the dividend's sign. -/
partial def constVal (j : Json) : Option Q := do
  match J.kind j with
  | "Literal" =>
    let v ← (j.getObjValAs? String "value").toOption
    let q ← parseRational v
    match J.opt j "subdenomination" with
    | some (.str u) => Q.mul q (Q.ofInt (← unitFactor? u))
    | _ => pure q
  | "TupleExpression" =>
    match (j.getObjVal? "components").toOption.bind (·.getArr?.toOption) with
    | some #[c] => constVal c
    | _ => none
  | "UnaryOperation" =>
    let a ← constVal (← (j.getObjVal? "subExpression").toOption)
    match (j.getObjValAs? String "operator").toOption with
    | some "-" => pure { a with num := - a.num }
    | some "~" => pure (Q.ofInt (- (← a.int?) - 1))
    | _ => none
  | "BinaryOperation" =>
    let a ← constVal (← (j.getObjVal? "leftExpression").toOption)
    let b ← constVal (← (j.getObjVal? "rightExpression").toOption)
    let nat (q : Q) : Option Nat := do
      let n ← q.int?
      if n < 0 then none else pure n.toNat
    match (j.getObjValAs? String "operator").toOption with
    | some "+" => a.add b
    | some "-" => a.sub b
    | some "*" => a.mul b
    | some "/" => a.div b
    | some "%" =>
      let x ← a.int?
      let y ← b.int?
      if y == 0 then none else pure (Q.ofInt (x.tmod y))
    | some "**" => a.pow b
    | some "&" => pure (Q.ofInt ((← nat a) &&& (← nat b)))
    | some "|" => pure (Q.ofInt ((← nat a) ||| (← nat b)))
    | some "^" => pure (Q.ofInt ((← nat a) ^^^ (← nat b)))
    | some "<<" =>
      let k ← nat b
      if k > 4096 then none else pure (Q.ofInt ((← a.int?) * 2 ^ k))
    | some ">>" =>
      let k ← nat b
      if k > 4096 then none else pure (Q.ofInt ((← nat a) / 2 ^ k))
    | _ => none
  | _ => none

/-- Is the node an operand that needs parentheses inside an operator? -/
def compound (j : Json) : Bool :=
  ["BinaryOperation", "Conditional", "Assignment"].contains (J.kind j)

def unsupported {α : Type} (msg : String) : PM α := throw (.unsupported msg)

/-- `e ? 1 : 0`, solc's encoding of a `bool` key, folded on a literal. -/
def boolKey (j : Json) (e : String) : String :=
  if J.kind j == "Literal" then (if e == "true" then "1" else "0") else s!"({e} ? 1 : 0)"

/-- The declared name of a local, as printed. -/
def nameOf (j : Json) : PM String := do
  let n ← PM.lift (J.str j "name")
  match J.id? j with
  | some i => pure ((lookupBy i (← get).names).getD n)
  | none => pure n

/-- The element type of a `push()`, from solc's type of the call. -/
def pushedTy (j : Json) : PM String := do
  let t := J.tyStr j
  let t := (t.replace " storage ref" "").replace " storage pointer" ""
  let t := if t.startsWith "struct " then
      ((t.drop 7).splitOn ".").getLast!
    else t
  match lookupBy t (← get).structs with
  | some (.ok m) => pure m
  | some (.error g) => throw g
  | none => unsupported s!"a member of a pushed `{t}`"

/-- Is the node `x.push()`? -/
def isPushCall (e : Json) : Bool :=
  J.kind e == "FunctionCall" &&
    ((J.opt e "expression").any fun f => J.kind f == "MemberAccess" &&
      (f.getObjValAs? String "memberName").toOption == some "push")

/-- Is the node `x.push().f`? -/
def isPushedMember (e : Json) : Bool :=
  J.kind e == "MemberAccess" && (J.opt e "expression").any isPushCall

/-- `x` run where a pushed member may be hoisted, or not. -/
def withPush {α : Type} (ok : Bool) (x : PM α) : PM α := do
  modify fun st => { st with pushOk := ok }
  let a ← x
  modify fun st => { st with pushOk := false }
  pure a

mutual

partial def expr (j : Json) : PM String := do
  if constTy j && ["Literal", "UnaryOperation", "BinaryOperation", "TupleExpression"].contains
      (J.kind j) then
    let some q := constVal j
      | unsupported s!"the constant expression of type `{J.tyStr j}`"
    let some n := q.int?
      | unsupported s!"the constant `{q.num}/{q.den}`, which is not an integer"
    return toString n
  match J.kind j with
  | "Identifier" =>
    let n ← PM.lift (J.str j "name")
    match J.ref? j with
    | some r =>
      if let some (v, g) := lookupBy r (← get).dropped then
        throw (match g with
          | .excluded m _ => .excluded s!"it reads the state variable `{v}`: {m}"
          | .unsupported m _ => .unsupported s!"it reads the state variable `{v}`: {m}")
      pure ((lookupBy r (← get).names).getD n)
    | none => pure n
  | "Literal" =>
    let v ← PM.lift (J.str j "value")
    match (← PM.lift (J.str j "kind")) with
    | "bool" => pure v
    | "number" =>
      -- an address literal: its type is `address`, not a constant's
      match (parseRational v).bind Q.int? with
      | some n => pure (toString n)
      | none => unsupported s!"the number literal `{v}`"
    | k => unsupported s!"a {k} literal"
  | "TupleExpression" =>
    match (← PM.lift (J.arr j "components")) with
    | [c] => pure s!"({← expr c})"
    | _ => unsupported "a tuple"
  | "UnaryOperation" =>
    let a ← J.get j "subExpression" |> PM.lift
    let s ← operand a false
    let pre := (J.opt j "prefix").any (· == .bool true)
    match (← PM.lift (J.str j "operator")) with
    | "!" => pure s!"!{s}"
    | "-" => pure s!"-{s}"
    | "~" => pure s!"~{s}"
    | "++" => pure (if pre then s!"++{s}" else s!"{s}++")
    | "--" => pure (if pre then s!"−−{s}" else s!"{s}−−")
    | "delete" => pure s!"delete {s}"
    | o => unsupported s!"the operator `{o}`"
  | "BinaryOperation" =>
    let op ← PM.lift (J.str j "operator")
    let l ← operand (← PM.lift (J.get j "leftExpression")) (op == "**")
    let r ← operand (← PM.lift (J.get j "rightExpression")) (op == "**")
    pure s!"{l} {op} {r}"
  | "Conditional" =>
    let c ← operand (← PM.lift (J.get j "condition")) false
    let a ← operand (← PM.lift (J.get j "trueExpression")) false
    let b ← operand (← PM.lift (J.get j "falseExpression")) false
    pure s!"{c} ? {a} : {b}"
  | "Assignment" =>
    let op ← PM.lift (J.str j "operator")
    pure s!"{← expr (← PM.lift (J.get j "leftHandSide"))} {op} {← expr (← PM.lift (J.get j "rightHandSide"))}"
  | "IndexAccess" =>
    let b ← expr (← PM.lift (J.get j "baseExpression"))
    let some ij := J.opt j "indexExpression" | unsupported "an index access with no index"
    let i ← expr ij
    pure s!"{b}[{if J.tyStr ij == "bool" then boolKey ij i else i}]"
  | "MemberAccess" =>
    let e ← PM.lift (J.get j "expression")
    let m ← PM.lift (J.str j "memberName")
    if isPushCall e then
      -- `x.push().f`: the element read through a storage local first
      unless (← get).pushOk do
        unsupported "a member of a pushed element (`x.push().f`) other than an assignment's \
          left-hand side of a constant or a declaration's whole initial value: hoisting the \
          push would change solc's order of evaluation"
      modify fun st => { st with pushOk := false }
      let T ← pushedTy e
      let call ← expr e
      let st ← get
      let x := s!"pushRef{st.fresh + 1}"
      set { st with fresh := st.fresh + 1, pre := st.pre.push s!"{T} storage {x} = {call}" }
      pure s!"{x}.{m}"
    else pure s!"{← expr e}.{m}"
  | "FunctionCall" => call j
  | "NewExpression" =>
    pure s!"new {← PM.lift (tyText (← get).structs (← PM.lift (J.get j "typeName")))}"
  | k => unsupported s!"the expression `{k}`"

/-- An operand, parenthesised when it is itself an operator (`pow`: also a
unary one, which `**` would otherwise take inside). -/
partial def operand (j : Json) (pow : Bool) : PM String := do
  let s ← expr j
  pure (if compound j || (pow && J.kind j == "UnaryOperation") then s!"({s})" else s)

partial def call (j : Json) : PM String := do
  let f ← PM.lift (J.get j "expression")
  let args ← PM.lift (J.arr j "arguments")
  match (← PM.lift (J.str j "kind")) with
  | "typeConversion" =>
    match args with
    | [a] =>
      let to := J.tyStr f
      if to.startsWith "type(address" || to.startsWith "type(contract " then expr a
      else
        let n ← match J.kind f with
          | "ElementaryTypeNameExpression" =>
            PM.lift (J.str (← PM.lift (J.get f "typeName")) "name")
          | _ => unsupported s!"the conversion to `{to}`"
        pure s!"{elemTy n false}({← expr a})"
    | _ => unsupported "a conversion of several arguments"
  | "functionCall" =>
    let names : List String := ((J.opt j "names").bind (·.getArr?.toOption)).map
      (·.toList.filterMap (·.getStr?.toOption)) |>.getD []
    let args ← if names.isEmpty then pure args else
      -- named arguments, put in the callee's parameter order
      let some ps := (J.ref? f).bind (lookupBy · (← get).funParams)
        | unsupported "named arguments to a callee whose parameters the import does not know"
      ps.mapM fun p => match names.idxOf? p with
        | some i => match args[i]? with
          | some a => pure a
          | none => unsupported s!"the named argument `{p}`"
        | none => unsupported s!"the named arguments leave out `{p}`"
    let as ← args.mapM expr
    pure s!"{← expr f}({", ".intercalate as})"
  | k => unsupported s!"a call of kind `{k}`"

end

/-- Is the node a tuple of several components, `(a, b)`, and not an inline
array (`SolJSONParser.isTuple`)? -/
def isTuple (j : Json) : Bool :=
  J.kind j == "TupleExpression" && !(J.opt j "isInlineArray").any (· == .bool true) &&
    ((J.opt j "components").bind (·.getArr?.toOption)).any (·.size > 1)

/-- Is the node a call by name, `f(a)`: of a function of the contract, where
a tuple is its value (`SolJSONParser.requireTupleValue`)? -/
def isNamedCall (j : Json) : Bool :=
  J.kind j == "FunctionCall" && (J.opt j "expression").any (J.kind · == "Identifier")

/-- The receiver and the amount of `(bool ok, ) = R.call{value: V}("")`, the
one value call solkey reads, matched as `SolJSONParser.isValueCall` matches
it: two declarations, a `bool` and an empty one; the options exactly
`value`; the member `call`; one argument, the empty string. -/
def valueCall? (j : Json) : Option (Json × Json × Json) := do
  let [d, Json.null] := ((J.opt j "declarations").bind (·.getArr?.toOption)).map (·.toList) |>.getD []
    | none
  let call ← J.opt j "initialValue"
  let opts ← J.opt call "expression"
  let m ← J.opt opts "expression"
  guard (d != .null && J.tyStr d == "bool")
  guard (J.kind call == "FunctionCall" && J.kind opts == "FunctionCallOptions")
  let [Json.str "value"] := ((J.opt opts "names").bind (·.getArr?.toOption)).map (·.toList) |>.getD []
    | none
  guard (J.kind m == "MemberAccess" && (m.getObjValAs? String "memberName").toOption == some "call")
  let [a] := ((J.opt call "arguments").bind (·.getArr?.toOption)).map (·.toList) |>.getD []
    | none
  guard (J.kind a == "Literal" && (a.getObjValAs? String "kind").toOption == some "string" &&
    (a.getObjValAs? String "value").toOption == some "")
  let v ← ((J.opt opts "options").bind (·.getArr?.toOption)).bind (·[0]?)
  pure (d, ← J.opt m "expression", v)

/-- A tuple's components, one left out printed empty: `(a, , b)`. -/
def tuple (j : Json) : PM String := do
  let cs ← (← PM.lift (J.arr j "components")).mapM fun c =>
    if c == .null then pure "" else expr c
  pure s!"({", ".intercalate cs})"

/-- What a tuple is assigned from: a tuple, or a call of a function of the
contract (`SolJSONParser.requireTupleValue`). -/
def tupleValue (v : Json) : PM String := do
  if isTuple v then tuple v
  else if isNamedCall v then expr v
  else unsupported "a tuple assigned from neither a tuple, nor a call of a function of this \
    contract, nor `(bool ok, ) = a.call{value: v}(\"\")`"

/-- A local's declaration, `T [storage|memory] x`. -/
def declText (d : Json) : PM String := do
  let T ← PM.lift (tyText (← get).structs (← PM.lift (J.get d "typeName")))
  let loc ← match J.opt d "storageLocation" with
    | some (.str "storage") => pure " storage"
    | some (.str "memory") => pure " memory"
    | _ => pure ""
  pure s!"{T}{loc} {← nameOf d}"

mutual

/-- A statement as `sol` text, after the storage locals it reads pushed
elements through. -/
partial def stmt (j : Json) : PM (List String) := do
  let line := J.line j
  let s ← tryCatch (stmt1 j) fun g => throw (match g with
    | .excluded m 0 => .excluded m line
    | .unsupported m 0 => .unsupported m line
    | g => g)
  let st ← get
  set { st with pre := #[] }
  pure (st.pre.toList ++ s)

partial def block (j : Json) : PM String := do
  let ss ← if J.kind j == "Block" then
      do (← PM.lift (J.arr j "statements")).flatMapM stmt
    else stmt j
  pure ("{ " ++ String.join (ss.map (· ++ "; ")) ++ "}")

partial def stmt1 (j : Json) : PM (List String) := do
  match J.kind j with
  | "ExpressionStatement" =>
    let e ← PM.lift (J.get j "expression")
    if J.kind e == "Assignment" && (J.opt e "operator").any (· == .str "=") &&
        (J.opt e "leftHandSide").any isTuple then
      -- `(a, , b) = v`
      return [s!"{← tuple (← PM.lift (J.get e "leftHandSide"))} = \
        {← tupleValue (← PM.lift (J.get e "rightHandSide"))}"]
    -- `x.push().f = c`: solc pushes, then stores the constant
    let ok := J.kind e == "Assignment" && (J.opt e "leftHandSide").any isPushedMember &&
      (J.opt e "rightHandSide").any fun r =>
        constTy r || (J.kind r == "Literal" && J.tyStr r == "bool")
    pure [← withPush ok (expr e)]
  | "VariableDeclarationStatement" =>
    if let some (d, r, v) := valueCall? j then
      -- `(bool ok, ) = R.call{value: V}("")` is `bool ok = R.send(V)`, as solkey reads it;
      -- faithful only under `holdsC` (full gas, re-entry)
      return [s!"{← declText d} = {← operand r false}.send({← expr v})"]
    let ds ← PM.lift (J.arr j "declarations")
    if ds.length ≥ 2 then
      -- `(uint a, , bool b) = v`
      let ts ← ds.mapM fun d => if d == .null then pure "" else declText d
      let some v := J.opt j "initialValue" | unsupported "a declaration of several variables, \
        with no value"
      return [s!"({", ".intercalate ts}) = {← tupleValue v}"]
    let [d] := ds | unsupported "a declaration of no variable"
    let dt ← declText d
    match J.opt j "initialValue" with
    | some v => pure [s!"{dt} = {← withPush (isPushedMember v) (expr v)}"]
    | none => pure [dt]
  | "Return" =>
    match J.opt j "expression" with
    | none => pure ["return"]
    | some e => pure [s!"return {← if isTuple e then tuple e else expr e}"]
  | "Block" => pure [← block j]
  | "IfStatement" =>
    let c ← expr (← PM.lift (J.get j "condition"))
    let t ← block (← PM.lift (J.get j "trueBody"))
    match J.opt j "falseBody" with
    | some e => pure [s!"if ({c}) {t} else {← block e}"]
    | none => pure [s!"if ({c}) {t}"]
  | "TryStatement" =>
    let c ← expr (← PM.lift (J.get j "externalCall"))
    match (← PM.lift (J.arr j "clauses")) with
    | ok :: catches =>
      let params (cl : Json) : PM (List String) := do
        match J.opt cl "parameters" with
        | some ps => (← PM.lift (J.arr ps "parameters")).mapM fun p => do
            let t ← declText p
            pure (if (p.getObjValAs? String "name").toOption == some "" then t.trimRight else t)
        | none => pure []
      -- an unnamed return value is bound to a fresh local no statement reads:
      -- `sol{}` names what an external call returns
      let rets ← match J.opt ok "parameters" with
        | some ps => (← PM.lift (J.arr ps "parameters")).mapM fun p => do
            let t ← declText p
            if (p.getObjValAs? String "name").toOption != some "" then pure t else
              let st ← get
              set { st with fresh := st.fresh + 1 }
              pure s!"{t.trimRight} tryRet{st.fresh + 1}"
        | none => pure []
      let rets := if rets.isEmpty then "" else s!" returns ({", ".intercalate rets})"
      let cs ← catches.mapM fun cl => do
        let e := ((cl.getObjValAs? String "errorName").toOption).getD ""
        let b ← block (← PM.lift (J.get cl "block"))
        match e, ← params cl with
        | "", [] => pure s!"catch {b}"
        | "", [p] => pure s!"catch ({p}) {b}"
        | "Error", [p] => pure s!"catch Error({p}) {b}"
        | "Panic", [p] => pure s!"catch Panic({p}) {b}"
        | e, _ => unsupported s!"the catch clause `{e}`"
      pure [s!"try {c}{rets} {← block (← PM.lift (J.get ok "block"))} {" ".intercalate cs}"]
    | [] => unsupported "a try with no clause"
  | "WhileStatement" =>
    let c ← expr (← PM.lift (J.get j "condition"))
    pure [s!"{← loopSpec j}while ({c}) {← block (← PM.lift (J.get j "body"))}"]
  | "DoWhileStatement" =>
    let c ← expr (← PM.lift (J.get j "condition"))
    pure [s!"{← loopSpec j}do {← block (← PM.lift (J.get j "body"))} while ({c})"]
  | "ForStatement" =>
    -- `for (init; c; upd)`, each part optional
    let part (k : String) : PM String := do
      match J.opt j k with
      | none | some .null => pure ""
      | some p =>
        match ← stmt1 p with
        | [t] => pure t
        | _ => unsupported s!"a `for` whose {k} is not one statement"
    let init ← part "initializationExpression"
    let c ← match J.opt j "condition" with
      | none | some .null => pure ""
      | some c => expr c
    let upd ← part "loopExpression"
    pure [s!"{← loopSpec j}for ({init}; {c}; {upd}) {← block (← PM.lift (J.get j "body"))}"]
  | "Break" => pure ["break"]
  | "Continue" => pure ["continue"]
  | k => unsupported s!"the statement `{k}`"

/-- A loop's specification, the `/// @custom:key` clauses above it that the
fixture keeps (`loopSpec`, read from the source by the loop's `src` offset as
solkey's `LoopSpecCompiler` reads them), each on a line of its own.  A clause
in the specification language proper (`\forall`, `\old`) is not a program
expression, which the grammar reads. -/
partial def loopSpec (j : Json) : PM String := do
  let some (.arr cs) := J.opt j "loopSpec" | pure ""
  let mut out := ""
  for c in cs do
    let some t := c.getStr?.toOption | unsupported "a loop clause that is not text"
    if t.contains '\\' then unsupported s!"the loop clause `{t}`: the specification language"
    out := out ++ s!"/// @custom:key {t}\n"
  pure out

end

/-! ## A contract -/

/-- The NatSpec text of a node, `""` if none. -/
def docText (n : Json) : String :=
  ((J.opt n "documentation").bind fun d => (d.getObjValAs? String "text").toOption).getD ""

/-- One `@custom:key` clause: its directive and its text. -/
structure KeyClause where
  kind : String
  text : String
  deriving Inhabited

/-- A line's leading tag (`@` and a letter, then word characters, `:` or
`-`) and the rest of the line, after spaces and tabs. -/
def tagWord? (l : String) : Option (String × String) :=
  let t := l.dropWhile fun c => c == ' ' || c == '\t'
  match t.toList with
  | '@' :: c :: _ =>
    if c.isAlpha then
      let w := t.takeWhile fun c => c == '@' || c.isAlphanum || c == '_' || c == ':' || c == '-'
      some (w, t.drop w.length)
    else none
  | _ => none

/-- One clause's body: its directive word and the rest, whitespace collapsed. -/
def keyClause (body : String) : Except String KeyClause := do
  let ws := (body.split Char.isWhitespace).filter (· != "")
  let some w := ws.head? | throw "`@custom:key` needs a directive"
  let rest := " ".intercalate ws.tail
  unless ["box", "skip", "invariant", "requires", "ensures", "assignable"].contains w do
    throw s!"unknown `@custom:key` directive `{w}`"
  if ["invariant", "requires", "ensures"].contains w && rest.isEmpty then
    throw s!"`@custom:key {w}` needs an expression"
  if (w == "box" || w == "skip") && !rest.isEmpty then
    throw s!"`@custom:key {w}` takes no argument, got `{rest}`"
  pure { kind := w, text := rest }

/-- The `@custom:key` clauses of a NatSpec text, as solkey's `KeyNatspec`
reads them: a tag starts a line, and a clause runs to the next tag, so a tag
quoted inside a sentence is prose. -/
def keyClauses (doc : String) : Except String (List KeyClause) := do
  let mut out : Array KeyClause := #[]
  let mut cur : Option String := none
  for l in doc.splitOn "\n" do
    match tagWord? l with
    | some (w, rest) =>
      if let some b := cur then out := out.push (← keyClause b)
      cur := if w == "@custom:key" then some rest else none
    | none => cur := cur.map (· ++ "\n" ++ l)
  if let some b := cur then out := out.push (← keyClause b)
  pure out.toList

/-- Does a comment carry a specification proper (`KeyNatspec.isSpecified`)? -/
def isSpecified (cs : List KeyClause) : Bool :=
  cs.any fun c => ["invariant", "requires", "ensures"].contains c.kind

/-- solkey's obligation for the function `f` of a contract whose clauses are
`contract`, in `SolidityProblemSynthesizer`'s order: only a `public` or
`external` function has one, `skip` drops it, a specification replaces the
plain one, and `box` chooses its modality.  A clause solkey refuses is the
error. -/
def tagOf (contract : List KeyClause) (f : Json) : Except String Tag := do
  let vis := ((f.getObjValAs? String "visibility").toOption).getD ""
  unless vis == "public" || vis == "external" do return .internal
  let cs ← keyClauses (docText f)
  if cs.any (·.kind == "skip") then return .skip
  if isSpecified contract || isSpecified cs then return .specified
  if cs.any (·.kind == "box") then return .box
  return .diamond

/-- Every declaration of a function that must be renamed: one named like a
state variable or a Lean keyword gets `_` until it is fresh. -/
def renames (stateVars : List String) (f : Json) : List (Int × String) :=
  let decls := (J.nodes f).filter fun n =>
    J.kind n == "VariableDeclaration" &&
      (n.getObjValAs? Bool "stateVariable").toOption != some true
  let taken := stateVars ++ decls.filterMap fun d => (d.getObjValAs? String "name").toOption
  decls.filterMap fun d => do
    let n ← (d.getObjValAs? String "name").toOption
    let i ← J.id? d
    if n != "" && (stateVars.contains n || leanKeywords.contains n) then
      let rec fresh (k : Nat) (x : String) : String :=
        match k with
        | 0 => x
        | k + 1 => if taken.contains x then fresh k (x ++ "_") else x
      pure (i, fresh 8 (n ++ "_"))
    else none

/-- The functions among `ids` that `f` calls by name, in order, each once. -/
def callees (ids : List Int) (f : Json) : List Int :=
  (J.nodes f).foldl (init := []) fun acc n =>
    let r := if J.kind n == "FunctionCall" then
        (J.opt n "expression").bind fun e => if J.kind e == "Identifier" then J.ref? e else none
      else none
    match r with
    | some r => if ids.contains r && !acc.contains r then acc ++ [r] else acc
    | none => acc

/-- The functions `f` reaches through `calls`, callees first and `f` last,
added to `done`; or a function on a cycle.  Each level adds a function to
`path`, so one more than the number of functions is enough `fuel`. -/
def reach (calls : Int → List Int) : Nat → List Int → List Int → Int → Except Int (List Int)
  | 0, _, _, f => throw f
  | fuel + 1, path, done, f =>
    if path.contains f then throw f
    else if done.contains f then pure done
    else do
      let done ← (calls f).foldlM (reach calls fuel (f :: path)) done
      pure (done ++ [f])

/-- A function as a `contract!` member, its body `ss`:
`function f(uint x) returns (uint lo, uint) { … }`. -/
def SolcFun.member (f : SolcFun) (ss : List String) : String :=
  let ps := ", ".intercalate (f.params.map fun (x, t) => s!"{t} {x}")
  let rs := if f.rets.isEmpty then "" else
    s!" returns ({", ".intercalate (f.rets.map fun (x, t) => if x.isEmpty then t else s!"{t} {x}")})"
  s!"function {f.name}({ps}){rs} \{ {String.join (ss.map (· ++ "; "))}}"

/-- The contract `name` of the source unit `ast`, its structs renamed by `ren`. -/
def readContract (ast : Json) (name : String) (ren : List (String × String)) :
    Except String SolcContract := do
  let units := match ast.getObjVal? "nodes" with
    | .ok (.arr a) => a.toList
    | _ => []
  let some c := units.find? fun u =>
      J.kind u == "ContractDefinition" && (u.getObjValAs? String "name").toOption == some name
    | throw s!"no contract `{name}` in the AST"
  if let some (.arr bs) := J.opt c "baseContracts" then
    unless bs.isEmpty do
      throw s!"contract `{name}` inherits: the import reads one contract's own members"
  let nodes := match c.getObjVal? "nodes" with
    | .ok (.arr a) => a.toList
    | _ => []
  let cspec ← (keyClauses (docText c)).mapError fun m => s!"contract `{name}`'s NatSpec: {m}"
  let S := readStructs ren (nodes.filter (J.kind · == "StructDefinition"))
  let vars := nodes.filter fun n =>
    J.kind n == "VariableDeclaration" && (n.getObjValAs? Bool "stateVariable").toOption == some true
  let mut members : List String := []
  let mut dropped : List (Int × String × Gap) := []
  let mut droppedNames : List (String × Gap) := []
  for v in vars do
    let n := ((v.getObjValAs? String "name").toOption).getD ""
    let i := (J.id? v).getD 0
    let mutab := ((v.getObjValAs? String "mutability").toOption).getD "mutable"
    let fixed := (v.getObjValAs? Bool "constant").toOption == some true || mutab != "mutable"
    match (do
        if fixed then
          throw (.unsupported s!"`{n}` (line {J.line v}) is {if mutab == "mutable" then "constant" else mutab}: \
            a value fixed before any call, not a storage slot")
        tyText S (← J.get v "typeName") : Except Gap String) with
    | .ok t => members := members ++ [s!"{t} {n};"]
    | .error g =>
      dropped := dropped ++ [(i, n, g)]
      droppedNames := droppedNames ++ [(n, g)]
  let stateVars := vars.filterMap fun v => (v.getObjValAs? String "name").toOption
  -- every function but the constructor (creation code, see the module doc)
  let funs := nodes.filter fun n =>
    J.kind n == "FunctionDefinition" && (n.getObjValAs? String "kind").toOption != some "constructor"
  let nameOfFun (f : Json) : String :=
    match (f.getObjValAs? String "kind").toOption with
    | some "function" | none => ((f.getObjValAs? String "name").toOption).getD ""
    | some k => k
  let funNames := funs.map nameOfFun
  let funParams : List (Int × List String) := funs.filterMap fun f => do
    let i ← J.id? f
    let ps ← (f.getObjVal? "parameters").toOption
    let ps ← (ps.getObjVal? "parameters").toOption
    let ps ← ps.getArr?.toOption
    pure (i, ps.toList.filterMap fun p => (p.getObjValAs? String "name").toOption)
  let read := funs.map fun f =>
    let fname := nameOfFun f
    -- what would change the function's meaning, or its constant's name
    let kind := ((f.getObjValAs? String "kind").toOption).getD "function"
    let modifier : Option String := match J.opt f "modifiers" with
      | some (.arr ms) => ms[0]?.map fun m =>
        ((J.opt m "modifierName").bind fun x => (x.getObjValAs? String "name").toOption).getD "?"
      | _ => none
    let refused : Option String :=
      if kind != "function" then some s!"a `{kind}` function"
      else if let some m := modifier then some s!"the modifier `{m}`: its code would be dropped"
      else if (funNames.filter (· == fname)).length > 1 then
        some s!"`{fname}` is overloaded: the import names a program by its function's name"
      else if fname == "report" then some "named like the import's `report` table"
      else none
    let st : PState := { names := renames stateVars f, dropped, structs := S, funParams }
    let ps : Except Gap (List (String × String)) := (do
      let pl ← J.get f "parameters"
      (← J.arr pl "parameters").mapM fun p => do
        let ((t, x), _) ← (do pure ((← PM.lift (tyText S (← PM.lift (J.get p "typeName")))),
          ← nameOf p) : PM (String × String)).run st
        pure (x, t))
    let rs : Except Gap (List (String × String)) := do
      let some pl := J.opt f "returnParameters" | pure []
      (← J.arr pl "parameters").mapM fun p => do
        let ((t, x), _) ← (do
            let t ← PM.lift (tyText S (← PM.lift (J.get p "typeName")))
            let loc := if J.opt p "storageLocation" == some (.str "memory") then " memory" else ""
            pure (t ++ loc, ← nameOf p) : PM (String × String)).run st
        pure (x, t)
    let tag := tagOf cspec f
    let body : Except Gap (List (Nat × String)) := do
      if let .error m := tag then throw (.unsupported s!"its NatSpec: {m}" (J.line f))
      if let some m := refused then throw (.unsupported m (J.line f))
      let b ← J.get f "body"
      let (ss, _) ← ((← J.arr b "statements").flatMapM fun s => do
        pure ((← stmt s).map (J.line s, ·))).run st
      pure ss
    { name := fname, line := J.line f, tag := (tag.toOption).getD .malformed,
      params := (ps.toOption).getD [], rets := (rs.toOption).getD [],
      body := do let _ ← ps; let _ ← rs; body : SolcFun }
  -- the internal calls: a function is read with every function it reaches,
  -- and the ones called are the contract's members, callees first
  let ids := funs.filterMap J.id?
  let callsOf : List (Int × List Int) := funs.filterMap fun f => (J.id? f).map (·, callees ids f)
  let calls (i : Int) : List Int := (lookupBy i callsOf).getD []
  let byId : List (Int × SolcFun) := (funs.zip read).filterMap fun (f, r) => (J.id? f).map (·, r)
  let nameAt (i : Int) : String := ((lookupBy i byId).map (·.name)).getD "?"
  let withCalls (i : Int) (r : SolcFun) : SolcFun :=
    let body : Except Gap (List (Nat × String)) := do
      let ss ← r.body
      match reach calls (ids.length + 1) [] [] i with
      | .error g => throw (.unsupported s!"the call of `{nameAt g}` is recursive: \
          a call is inlined, and the inlining would not end" r.line)
      | .ok order =>
        for c in order.dropLast do
          if let some { body := .error g, .. } := lookupBy c byId then
            throw (match g with
              | .excluded m _ => .excluded s!"it calls `{nameAt c}`, which is left out: {m}" r.line
              | .unsupported m _ => .unsupported s!"it calls `{nameAt c}`, which is left out: {m}" r.line)
        pure ss
    let cs := ((reach calls (ids.length + 1) [] [] i).toOption.getD []).dropLast
    { r with body, calls := cs.map nameAt }
  let closed : List (Int × SolcFun) := byId.map fun (i, r) => (i, withCalls i r)
  let order := ids.foldl (fun done i => (reach calls (ids.length + 1) [] done i).toOption.getD done) []
  let called := callsOf.flatMap (·.2)
  let funMembers := order.filterMap fun i => do
    guard (called.contains i)
    let r ← lookupBy i closed
    let ss ← r.body.toOption
    pure (r.name, r.member (ss.map (·.2)))
  let funs := (funs.zip read).map fun (f, r) => ((J.id? f).map (withCalls · r)).getD r
  pure { name, members, dropped := droppedNames, funs, funMembers }

end Solidity.Frontend

