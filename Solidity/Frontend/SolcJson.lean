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
  by member; a struct that is not there, or differs, leaves out what uses it.

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

/-- solkey's reading of a function, from its NatSpec `@custom:key` tag. -/
inductive Tag where
  | diamond
  | box
  | skip
  deriving Repr, DecidableEq, Inhabited

def Tag.toStr : Tag → String
  | .diamond => "diamond"
  | .box => "box"
  | .skip => "skip"

/-- A function as read: its parameters (name, `sol` type) and its body as
statements of `sol` text, or why there is none. -/
structure SolcFun where
  name : String
  line : Nat
  tag : Tag
  params : List (String × String)
  /-- The statements, each with the source line of the statement it prints. -/
  body : Except Gap (List (Nat × String))
  deriving Inhabited

/-- A contract as read: the `contract!` members of the state variables it
keeps, the ones it leaves out and why, its functions. -/
structure SolcContract where
  name : String
  members : List String
  dropped : List (String × Gap)
  funs : List SolcFun
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
    -- `x.push().f = c`: solc pushes, then stores the constant
    let ok := J.kind e == "Assignment" && (J.opt e "leftHandSide").any isPushedMember &&
      (J.opt e "rightHandSide").any fun r =>
        constTy r || (J.kind r == "Literal" && J.tyStr r == "bool")
    pure [← withPush ok (expr e)]
  | "VariableDeclarationStatement" =>
    let [some d] := (← PM.lift (J.arr j "declarations")).map fun d =>
        if d == .null then none else some d
      | unsupported "a declaration of several variables"
    let dt ← declText d
    match J.opt j "initialValue" with
    | some v => pure [s!"{dt} = {← withPush (isPushedMember v) (expr v)}"]
    | none => pure [dt]
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
      let rets ← params ok
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
  | k => unsupported s!"the statement `{k}`"

end

/-! ## A contract -/

/-- The NatSpec tag of a function: `@custom:key box`, `@custom:key skip`. -/
def tagOf (f : Json) : Tag :=
  let t := ((J.opt f "documentation").bind fun d => (d.getObjValAs? String "text").toOption).getD ""
  if (t.splitOn "@custom:key box").length > 1 then .box
  else if (t.splitOn "@custom:key skip").length > 1 then .skip
  else .diamond

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
  let funs := funs.map fun f =>
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
    let body : Except Gap (List (Nat × String)) := do
      if let some m := refused then throw (.unsupported m (J.line f))
      let b ← J.get f "body"
      let (ss, _) ← ((← J.arr b "statements").flatMapM fun s => do
        pure ((← stmt s).map (J.line s, ·))).run st
      pure ss
    { name := fname, line := J.line f, tag := tagOf f,
      params := (ps.toOption).getD [],
      body := do let _ ← ps; body }
  pure { name, members, dropped := droppedNames, funs }

end Solidity.Frontend

