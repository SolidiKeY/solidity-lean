import Solidity.Calculus.DecideLang

/-!
# The closer's notation: `key{ … }`

The target language of `sol_decide` (`Calculus/DecideLang.lean`: `LTerm`,
`LPath`, `LStor`, `LMem`, `LId`, `LSel`, `LMV`) written as solkey writes its
terms, so a clause of the closer reads as the taclet it transcribes:

```
| key{ write(mem, id1, a1, v) }, id2, a2 => …      -- readOnWrite
| key{ save(st, P, w) }, Q => …                    -- selectOnSaveCons
| .pop _, L => key{ if(0 < L) then true else err } -- storagePopSave
```

| notation | term |
|---|---|
| `key{ t }` | every name a Lean variable (a pattern variable in a `match`); a literal name is a string, `find(storage, Q."age")` |
| `key!{ t }` | every name a literal: `key!{ find(storage, alice.age) }`, `idC(idp0, nil)` |

Both are macros: they expand to the constructor applications, no `def`
in between, so a closer clause and its equation lemmas are the same terms
as written raw, and the kernel's evaluation of the closer meets no new
constant.  A pattern goes one constructor deep, and is linear.

## Spellings

The sort of a term is read off its head, then off the argument position.

| sort | spelling | constructor |
|---|---|---|
| storage | `storage`, `save(s, q, w)`, `delAt(s, q)` | `LStor.init`, `.save`, `.del` |
| | `save(s, q, find(src, sq))`, `save(s, q, copyMem(mtSt, m, i))` | `.copy s q src sq`, `.copy s q (.view m i) (.root viewRoot)` |
| | `copyMem(mtSt, m, i)`, `push(s, q, w)`, `arr(op, s, q, w)` | `.view`, `.arr .push`, `.arr` |
| | `staleSave(s, q, w)`, `stale(op, s, q, w)` | `.stale none`, `.stale (some op)` (Lean only) |
| memory | `memory`, `addM(m, shaped(k, R))`, `write(m, i, a, v)` | `LMem.init`, `.addM m k R`, `.write` |
| | `write(addM(m, shaped(k, R)), idC(k, nil), size, n)` | `.newArr m k R n` (KeY's allocation and write of `size`) |
| | `copySt(m, k, find(s, q))` | `.copySt m k s q` |
| memory name | `idC(k, nil)`, `idC(idp0, [f, at(2)])` | `LId.mk` |
| selector | `f`, `at(t)`, `size` | `LSel.fld`, `.idx`, `.size` |
| memory value | `idC(…)`, any term | `LMV.ref`, `.word` |
| term | `find(s, q)`, `find(s, q.length)`, `if(a = b) then t else e`, `if(c) then t else e` | `.find`, `.len`, `.kite`, `.ite` |
| | `select(s, q)` | `.find` again: the spelling of a read as a `save`'s value, where `find` is a copy |
| | `delValue(a)`, `(d; a)`, `err`, `msg.sender`, `address(this)` | `.zero`, `.seq`, `.err`, `.env` |
| | `has`, `isMap`/`isFixed`, `ok`, `okSt`/`okPath`, `copyOk`, `orElse`, `findP` | the guards only Lean has |
| | `a + b`, `a < b`, `a == b`, … at `uint` (`&&`, `\|\|` at `bool`); `binop(op, p, a, b)`, `unop(op, p, a)` | `.binop`, `.unop` |
| | `lit(v)`, `var(x)`, `env(k)`; `cast(v)` (right-hand side only) | `.lit`, `.var`, `.env`; `LMV.wordT v` |

`‹e›` is the Lean term `e` at any position, and `_` a hole.  Reserved
names: `storage`, `memory`, `mtSt`, `err`, `size`, `nil`, `true`, `false`,
`this`, and `length` as a path's last member.  In `key!{ }`, `idp0` is the
allocation `0`, and an identifier in a term is the program variable of
that name (`Var.ofName` when it ends in a digit, so that `se1` is the fresh
one).  `ok(x)` is `okSt` or `okPath` by the shape of `x`; of a variable it
is written out.

## Printing

`ppKey` prints a term of these sorts in this notation.  It reads the term
as it is written (no `whnf`), and prints a subterm past `keyCutoff` nodes as
`‹⋯›`.  The delaborators on the constructors print `key!{ … }` for a
closed term and `key{ … }` for one over variables, unless `pp.sol.dl` is
off.
-/

namespace Solidity

namespace Decide

open Semantics

/-! ## The syntax -/

declare_syntax_cat key_term
syntax:max (name := ktNum) num : key_term
syntax:max (name := ktNeg) "-" num : key_term
syntax:max (name := ktStr) str : key_term
syntax:max (name := ktIdent) ident : key_term
syntax:max (name := ktHole) "_" : key_term
syntax:max (name := ktField) key_term:max "." ident : key_term
syntax:max (name := ktFieldStr) key_term:max "." str : key_term
syntax:max (name := ktIndex) key_term:max "[" key_term "]" : key_term
syntax:max (name := ktArr) key_term:max "[" "]" : key_term
syntax:max (name := ktCall) ident noWs "(" key_term,* ")" : key_term
syntax:max (name := ktAt) "at" noWs "(" key_term ")" : key_term
syntax:max (name := ktKite)
  "if" noWs "(" key_term " = " key_term ")" " then " key_term " else " key_term : key_term
syntax:max (name := ktIte) "if" noWs "(" key_term ")" " then " key_term " else " key_term : key_term
syntax:max (name := ktSeq) "(" key_term "; " key_term ")" : key_term
syntax:max (name := ktParen) "(" key_term ")" : key_term
syntax:max (name := ktList) "[" key_term,* "]" : key_term
syntax:max (name := ktEsc) "‹" term "›" : key_term
syntax:70 (name := ktMul) key_term:70 " * " key_term:71 : key_term
syntax:70 (name := ktDiv) key_term:70 " / " key_term:71 : key_term
syntax:70 (name := ktMod) key_term:70 " % " key_term:71 : key_term
syntax:65 (name := ktAdd) key_term:65 " + " key_term:66 : key_term
syntax:65 (name := ktSub) key_term:65 " - " key_term:66 : key_term
syntax:50 (name := ktLt) key_term:51 " < " key_term:51 : key_term
syntax:50 (name := ktLe) key_term:51 " <= " key_term:51 : key_term
syntax:50 (name := ktGt) key_term:51 " > " key_term:51 : key_term
syntax:50 (name := ktGe) key_term:51 " >= " key_term:51 : key_term
syntax:50 (name := ktEq) key_term:51 " == " key_term:51 : key_term
syntax:50 (name := ktNe) key_term:51 " != " key_term:51 : key_term
syntax:35 (name := ktAnd) key_term:36 " && " key_term:35 : key_term
syntax:30 (name := ktOr) key_term:31 " || " key_term:30 : key_term

/-- A term of the closer, every name a Lean variable. -/
syntax "key{ " key_term " }" : term
/-- A term of the closer, every name a literal. -/
syntax "key!{ " key_term " }" : term

/-- The infix operators: the syntax, the operator, the type it is read at. -/
def keyInfix : List (Lean.SyntaxNodeKind × Lean.Name × Lean.Name) :=
  [(``ktMul, ``BinOp.mul, ``PrimTy.uint), (``ktDiv, ``BinOp.div, ``PrimTy.uint),
   (``ktMod, ``BinOp.mod, ``PrimTy.uint), (``ktAdd, ``BinOp.add, ``PrimTy.uint),
   (``ktSub, ``BinOp.sub, ``PrimTy.uint), (``ktLt, ``BinOp.lt, ``PrimTy.uint),
   (``ktLe, ``BinOp.le, ``PrimTy.uint), (``ktGt, ``BinOp.gt, ``PrimTy.uint),
   (``ktGe, ``BinOp.ge, ``PrimTy.uint), (``ktEq, ``BinOp.eqB, ``PrimTy.uint),
   (``ktNe, ``BinOp.neB, ``PrimTy.uint), (``ktAnd, ``BinOp.and, ``PrimTy.bool),
   (``ktOr, ``BinOp.or, ``PrimTy.bool)]

/-- The names no variable may take. -/
def keyReserved : List String :=
  ["storage", "memory", "mtSt", "err", "size", "nil", "true", "false", "this"]

/-- The heads of a storage, of a memory. -/
def storHeads : List String :=
  ["save", "delAt", "push", "arr", "stale", "staleSave", "copyMem"]
def memHeads : List String := ["addM", "write", "copySt"]

/-- The sort a position of `key{ … }` asks for. -/
inductive KSort where
  | term | value | var | path | stor | mem | id | sel | mv | name | ord | nat | int
  | segs | seg | ty | refty | prim | binop | unop | aop | shape | env | bool
  deriving DecidableEq, Inhabited

/-- What the sort is, for an error. -/
def KSort.what : KSort → String
  | .term => "a term" | .value => "a value" | .var => "a variable"
  | .path => "a storage path" | .stor => "a storage" | .mem => "a memory"
  | .id => "a memory name" | .sel => "a selector" | .mv => "a memory value"
  | .name => "a name" | .ord => "an allocation" | .nat => "a number" | .int => "an integer"
  | .segs => "a list of selectors" | .seg => "a selector" | .ty => "a type"
  | .refty => "a reference type" | .prim => "a primitive type" | .binop => "an operator"
  | .unop => "an operator" | .aop => "an array operation" | .shape => "a shape"
  | .env => "an environment value" | .bool => "a Boolean"

/-- The children of a node that are not tokens. -/
def keyArgs (stx : Lean.Syntax) : Array Lean.Syntax := stx.getArgs.filter (!·.isAtom)

/-- The head of a call, `""` for anything else. -/
def keyHead (stx : Lean.Syntax) : String :=
  if stx.getKind == ``ktCall then
    match nameParts (keyArgs stx)[0]!.getId.eraseMacroScopes with
    | [h] => h
    | _ => ""
  else ""

/-- The arguments of a call. -/
def keyCallArgs (stx : Lean.Syntax) : Array (Lean.TSyntax `key_term) :=
  (keyArgs stx)[1]!.getSepArgs.map (⟨·⟩)

/-- The parts of an identifier: `alice.age` is `alice`, `age`. -/
def keyParts (stx : Lean.Syntax) : List String := nameParts stx.getId.eraseMacroScopes

/-- The sort the head of a term gives it, when it stands alone. -/
partial def keyTop (stx : Lean.TSyntax `key_term) : KSort :=
  let k := stx.raw.getKind
  if k == ``ktParen then keyTop ⟨(keyArgs stx)[0]!⟩
  else if k == ``ktIdent then
    match keyParts (keyArgs stx)[0]! with
    | ["storage"] => .stor
    | ["memory"] => .mem
    | ["size"] => .sel
    | ["msg", "sender"] | ["msg", "value"] | ["block", "timestamp"] => .term
    | _ :: _ :: _ => .path
    | _ => .term
  else if k == ``ktField then
    if keyHead (keyArgs stx)[0]! == "address" then .term else .path
  else if k == ``ktFieldStr || k == ``ktIndex then .path
  else if k == ``ktAt then .sel
  else if k == ``ktCall then
    let h := keyHead stx
    if storHeads.contains h then .stor
    else if memHeads.contains h then .mem
    else if h == "idC" then .id
    else .term
  else .term

section Expand
open Lean (Ident Macro MacroM mkIdent mkIdentFrom mkCIdentFrom Name TSyntax Syntax quote)

/-- An error at `stx`: `what` cannot stand where `s` is asked for. -/
def keyErr (stx : Syntax) (what : String) (s : KSort) : MacroM α :=
  Macro.throwErrorAt stx s!"key\{}: {what} cannot stand for {s.what} here"

/-- The allocation `k` of `idpk`. -/
def idpOrd? (s : String) : Option Nat :=
  if s.startsWith "idp" then (s.drop 3).toNat? else none

/-- The program variable `n`: a name ending in a digit may be a fresh one,
which the file's `FreshNames` reads (`se1`); any other is a user's. -/
def keyVar (n : String) : MacroM Lean.Term :=
  if n.back.isDigit then `(Var.ofName $(quote n)) else `(Var.user $(quote n))

/-- A one-part name at the sort `s`: a reserved name, a literal (`key!`),
or a Lean variable (`key`). -/
def keyName1 (lit : Bool) (s : KSort) (x : Ident) (n : String) : MacroM Lean.Term := do
  let prim? : Option Lean.Term ← match n with
    | "uint" | "address" => some <$> `(PrimTy.uint)
    | "int" => some <$> `(PrimTy.int)
    | "bool" => some <$> `(PrimTy.bool)
    | _ => pure none
  match s, n with
  | .term, "true" => `(LTerm.lit (PrimVal.bool true))
  | .term, "false" => `(LTerm.lit (PrimVal.bool false))
  | .term, "err" => `(LTerm.err)
  | .value, "true" => `(PrimVal.bool true)
  | .value, "false" => `(PrimVal.bool false)
  | .bool, "true" => `(true)
  | .bool, "false" => `(false)
  | .stor, "storage" => `(LStor.init)
  | .mem, "memory" => `(LMem.init)
  | .sel, "size" => `(LSel.size)
  | .segs, "nil" => `([])
  | .aop, "push" => `(AOp.push)
  | .shape, "map" => `(KShape.map)
  | .shape, "fixed" => `(KShape.fixed)
  | .prim, _ =>
    match prim? with
    | some p => pure p
    | none => if lit then keyErr x n s else pure x
  | .ty, _ =>
    match prim? with
    | some p => `(Ty.prim $p)
    | none => if lit then `(Ty.ref (RefTy.struct $(quote n))) else pure x
  | .refty, _ =>
    if prim?.isSome then keyErr x n s
    else if lit then `(RefTy.struct $(quote n)) else pure x
  | _, _ =>
    if keyReserved.contains n then keyErr x s!"`{n}`" s
    else if !lit then pure x
    else match s with
      | .term => `(LTerm.var $(← keyVar n))
      | .var => keyVar n
      | .path => `(LPath.root $(quote n))
      | .sel => `(LSel.fld $(quote n))
      | .name => pure (quote n)
      | .seg => `(Seg.field $(quote n))
      | .ord => match idpOrd? n with
        | some k => pure (Syntax.mkNumLit (toString k))
        | none => keyErr x s!"`{n}` (an allocation is `idp0`, `idp1`, …)" s
      | .binop => pure (mkCIdentFrom x (`Solidity.BinOp ++ Name.mkSimple n))
      | .unop => pure (mkCIdentFrom x (`Solidity.UnOp ++ Name.mkSimple n))
      | .env => pure (mkCIdentFrom x (`Solidity.EnvKey ++ Name.mkSimple n))
      | _ => keyErr x s!"the name `{n}`" s

mutual

/-- A term of `key{ … }` (`lit`: of `key!{ … }`) at the sort `s`. -/
partial def keyAt (lit : Bool) (s : KSort) (stx : TSyntax `key_term) : MacroM Lean.Term := do
  let k := stx.raw.getKind
  let ps := keyArgs stx
  let sub (i : Nat) : TSyntax `key_term := ⟨ps[i]!⟩
  if k == ``ktEsc then return ⟨ps[0]!⟩
  if k == ``ktParen then return ← keyAt lit s (sub 0)
  if k == ``ktHole then return ← `(_)
  -- a memory value: a name, a variable of the sort, or a word
  if s == .mv then
    if k == ``ktIdent && !lit then
      if let [n] := keyParts ps[0]! then
        if !keyReserved.contains n then return ⟨ps[0]!⟩
    if keyHead stx == "idC" then return ← `(LMV.ref $(← keyAt lit .id stx))
    return ← `(LMV.word $(← keyAt lit .term stx))
  if k == ``ktIdent then
    let x : Ident := ⟨ps[0]!⟩
    match keyParts x with
    | [n] => return ← keyName1 lit s x n
    | ["msg", "sender"] => if s == .term then return ← `(LTerm.env EnvKey.msgSender)
    | ["msg", "value"] => if s == .term then return ← `(LTerm.env EnvKey.msgValue)
    | ["block", "timestamp"] => if s == .term then return ← `(LTerm.env EnvKey.timestamp)
    | _ => pure ()
    match keyParts x with
    | h :: fs@(_ :: _) =>
      unless s == .path do
        keyErr x "a path" s
      keyFields lit (← keyName1 lit .path (partIdent x h) h) (fs.map (partIdent x))
    | _ => keyErr x "this name" s
  else if k == ``ktStr then
    let some v := ps[0]!.isStrLit? | keyErr stx "this string" s
    let vs := v
    let v := quote v
    match s with
    | .name => return v
    | .path => `(LPath.root $v)
    | .term => `(LTerm.var $(← keyVar vs))
    | .var => keyVar vs
    | .sel => `(LSel.fld $v)
    | .seg => `(Seg.field $v)
    | .ty => `(Ty.ref (RefTy.struct $v))
    | .refty => `(RefTy.struct $v)
    | _ => keyErr stx "a string" s
  else if k == ``ktNum then
    let n : TSyntax `num := ⟨ps[0]!⟩
    match s with
    | .term => `(LTerm.lit (PrimVal.int $n))
    | .value => `(PrimVal.int $n)
    | .ord | .nat | .int => pure n
    | _ => keyErr stx "a number" s
  else if k == ``ktNeg then
    let n : TSyntax `num := ⟨ps[0]!⟩
    match s with
    | .term => `(LTerm.lit (PrimVal.int (-$n)))
    | .value => `(PrimVal.int (-$n))
    | .int => `(-$n)
    | _ => keyErr stx "a negative number" s
  else if k == ``ktField then
    let f : Ident := ⟨ps[1]!⟩
    if s == .term && keyHead ps[0]! == "address" && keyParts f == ["balance"] then
      let _ ← keyAt lit .term (sub 0)
      return ← `(LTerm.env EnvKey.selfBalance)
    unless s == .path do keyErr stx "a path" s
    keyFields lit (← keyAt lit .path (sub 0)) ((keyParts f).map (partIdent f))
  else if k == ``ktFieldStr then
    unless s == .path do keyErr stx "a path" s
    let some v := ps[1]!.isStrLit? | keyErr stx "this member" s
    `(LPath.field $(← keyAt lit .path (sub 0)) $(quote v))
  else if k == ``ktIndex then
    match s with
    | .path => `(LPath.at $(← keyAt lit .path (sub 0)) $(← keyAt lit .term (sub 1)))
    | .ty => `(Ty.ref (RefTy.fixed $(← keyAt lit .ty (sub 0)) $(← keyAt lit .nat (sub 1))))
    | .refty => `(RefTy.fixed $(← keyAt lit .ty (sub 0)) $(← keyAt lit .nat (sub 1)))
    | _ => keyErr stx "an element" s
  else if k == ``ktArr then
    match s with
    | .ty => `(Ty.ref (RefTy.array $(← keyAt lit .ty (sub 0))))
    | .refty => `(RefTy.array $(← keyAt lit .ty (sub 0)))
    | _ => keyErr stx "an array type" s
  else if k == ``ktAt then
    match s with
    | .sel => `(LSel.idx $(← keyAt lit .term (sub 0)))
    | .seg => `(Seg.at $(← keyAt lit .int (sub 0)))
    | _ => keyErr stx "`at(…)`" s
  else if k == ``ktKite then
    unless s == .term do keyErr stx "a conditional" s
    `(LTerm.kite $(← keyAt lit .term (sub 0)) $(← keyAt lit .term (sub 1))
        $(← keyAt lit .term (sub 2)) $(← keyAt lit .term (sub 3)))
  else if k == ``ktIte then
    unless s == .term do keyErr stx "a conditional" s
    `(LTerm.ite $(← keyAt lit .term (sub 0)) $(← keyAt lit .term (sub 1))
        $(← keyAt lit .term (sub 2)))
  else if k == ``ktSeq then
    unless s == .term do keyErr stx "a sequence" s
    `(LTerm.seq $(← keyAt lit .term (sub 0)) $(← keyAt lit .term (sub 1)))
  else if k == ``ktList then
    unless s == .segs do keyErr stx "a list" s
    let es ← ps[0]!.getSepArgs.mapM fun e => keyAt lit .seg ⟨e⟩
    `([$es,*])
  else if let some (_, op, p) := keyInfix.find? (·.1 == k) then
    unless s == .term do keyErr stx "an operation" s
    `(LTerm.binop $(mkCIdentFrom stx op) $(mkCIdentFrom stx p) $(← keyAt lit .term (sub 0))
        $(← keyAt lit .term (sub 1)))
  else if k == ``ktCall then
    keyCall lit s stx
  else keyErr stx "this" s

/-- The members `fs` of the path `b`. -/
partial def keyFields (lit : Bool) (b : Lean.Term) (fs : List Ident) : MacroM Lean.Term :=
  fs.foldlM (init := b) fun (acc : Lean.Term) (f : Ident) => do
    let some n := (keyParts f).head? | keyErr f "this member" .name
    if n == "length" then
      Macro.throwErrorAt f "key{}: a length is a term, `find(s, q.length)`"
    `(LPath.field $acc $(← keyName1 lit .name f n))

/-- The path before a last member `length`, if `q` ends in one. -/
partial def keyLength? (lit : Bool) (q : TSyntax `key_term) : MacroM (Option Lean.Term) := do
  let k := q.raw.getKind
  let ps := keyArgs q
  if k == ``ktIdent then
    let x : Ident := ⟨ps[0]!⟩
    match keyParts x with
    | h :: fs@(_ :: _) =>
      if fs.getLast? != some "length" then return none
      some <$> keyFields lit (← keyName1 lit .path (partIdent x h) h)
        (fs.dropLast.map (partIdent x))
    | _ => return none
  else if k == ``ktField then
    let f : Ident := ⟨ps[1]!⟩
    let fs := keyParts f
    if fs.getLast? != some "length" then return none
    some <$> keyFields lit (← keyAt lit .path ⟨ps[0]!⟩) (fs.dropLast.map (partIdent f))
  else if k == ``ktParen then keyLength? lit ⟨ps[0]!⟩
  else return none

/-- A call, `save(s, q, w)`, at the sort `s`. -/
partial def keyCall (lit : Bool) (s : KSort) (stx : TSyntax `key_term) : MacroM Lean.Term := do
  let h := keyHead stx
  let as := keyCallArgs stx
  let arity (n : Nat) : MacroM Unit := do
    unless as.size == n do
      Macro.throwErrorAt stx s!"key\{}: `{h}` takes {n} arguments"
  let at_ (s : KSort) (i : Nat) : MacroM Lean.Term := keyAt lit s as[i]!
  match s, h with
  -- terms
  | .term, "find" | .term, "select" => do
    arity 2
    match ← keyLength? lit as[1]! with
    | some q => `(LTerm.len $(← at_ .stor 0) $q)
    | none => `(LTerm.find $(← at_ .stor 0) $(← at_ .path 1))
  | .term, "findP" => do arity 2; `(LTerm.findP $(← at_ .stor 0) $(← at_ .path 1))
  | .term, "has" => do arity 2; `(LTerm.has $(← at_ .stor 0) $(← at_ .path 1))
  | .term, "copyOk" => do arity 2; `(LTerm.cpok $(← at_ .stor 0) $(← at_ .path 1))
  | .term, "isMap" => do arity 2; `(LTerm.kmap KShape.map $(← at_ .stor 0) $(← at_ .path 1))
  | .term, "isFixed" => do arity 2; `(LTerm.kmap KShape.fixed $(← at_ .stor 0) $(← at_ .path 1))
  | .term, "kmap" => do
    arity 3; `(LTerm.kmap $(← at_ .shape 0) $(← at_ .stor 1) $(← at_ .path 2))
  | .term, "okSt" => do arity 1; `(LTerm.sok $(← at_ .stor 0))
  | .term, "okPath" => do arity 1; `(LTerm.pok $(← at_ .path 0))
  | .term, "ok" => do
    arity 1
    let a := as[0]!
    let k := a.raw.getKind
    let stor := keyTop a == .stor
    let path := keyTop a == .path || k == ``ktStr || (lit && k == ``ktIdent)
    if stor then `(LTerm.sok $(← at_ .stor 0))
    else if path then `(LTerm.pok $(← at_ .path 0))
    else Macro.throwErrorAt a "key{}: `ok` of a variable: write `okSt(…)` or `okPath(…)`"
  | .term, "orElse" => do arity 2; `(LTerm.orElse $(← at_ .term 0) $(← at_ .term 1))
  | .term, "delValue" => do arity 1; `(LTerm.zero $(← at_ .term 0))
  | .term, "binop" => do
    arity 4
    `(LTerm.binop $(← at_ .binop 0) $(← at_ .prim 1) $(← at_ .term 2) $(← at_ .term 3))
  | .term, "unop" => do
    arity 3; `(LTerm.unop $(← at_ .unop 0) $(← at_ .prim 1) $(← at_ .term 2))
  | .term, "lit" => do arity 1; `(LTerm.lit $(← at_ .value 0))
  | .term, "var" => do arity 1; `(LTerm.var $(← at_ .var 0))
  | .term, "env" => do arity 1; `(LTerm.env $(← at_ .env 0))
  | .term, "address" => do
    arity 1
    unless keyParts (keyArgs as[0]!)[0]! == ["this"] && as[0]!.raw.getKind == ``ktIdent do
      Macro.throwErrorAt as[0]! "key{}: `address(this)`"
    `(LTerm.env EnvKey.selfAddress)
  | .term, "cast" => do
    -- `LMV.wordT` is defined downstream (`MemRead`), so it is named, not resolved here
    arity 1; `($(mkCIdentFrom stx `Solidity.Decide.LMV.wordT) $(← at_ .mv 0))
  -- storages
  | .stor, "save" => do
    arity 3
    let w := as[2]!
    match keyHead w with
    | "find" =>
      let src := keyCallArgs w
      unless src.size == 2 do Macro.throwErrorAt w "key{}: `find` takes 2 arguments"
      `(LStor.copy $(← at_ .stor 0) $(← at_ .path 1) $(← keyAt lit .stor src[0]!)
          $(← keyAt lit .path src[1]!))
    | "copyMem" =>
      `(LStor.copy $(← at_ .stor 0) $(← at_ .path 1) $(← keyAt lit .stor w)
          (LPath.root "#view"))
    | _ => `(LStor.save $(← at_ .stor 0) $(← at_ .path 1) $(← at_ .term 2))
  | .stor, "delAt" => do arity 2; `(LStor.del $(← at_ .stor 0) $(← at_ .path 1))
  | .stor, "push" => do
    arity 3; `(LStor.arr AOp.push $(← at_ .stor 0) $(← at_ .path 1) $(← at_ .term 2))
  | .stor, "arr" => do
    arity 4; `(LStor.arr $(← at_ .aop 0) $(← at_ .stor 1) $(← at_ .path 2) $(← at_ .term 3))
  | .stor, "staleSave" => do
    arity 3; `(LStor.stale none $(← at_ .stor 0) $(← at_ .path 1) $(← at_ .term 2))
  | .stor, "stale" => do
    arity 4
    `(LStor.stale (some $(← at_ .aop 0)) $(← at_ .stor 1) $(← at_ .path 2) $(← at_ .term 3))
  | .stor, "copyMem" => do
    arity 3
    unless keyParts (keyArgs as[0]!)[0]! == ["mtSt"] && as[0]!.raw.getKind == ``ktIdent do
      Macro.throwErrorAt as[0]! "key{}: `copyMem(mtSt, m, i)`"
    `(LStor.view $(← at_ .mem 1) $(← at_ .id 2))
  -- memories
  | .mem, "addM" => do
    arity 2
    let (m, k, R) ← keyShaped lit as[0]! as[1]!
    `(LMem.addM $m $k $R)
  | .mem, "write" => do
    arity 4
    let a := as[2]!
    if a.raw.getKind == ``ktIdent && keyParts (keyArgs a)[0]! == ["size"] then
      -- `write(addM(m, shaped(k, R)), idC(k, nil), size, n)`: an array allocated
      let al := as[0]!
      unless keyHead al == "addM" && (keyCallArgs al).size == 2 do
        Macro.throwErrorAt al "key{}: a write of `size` is an allocation, \
          `write(addM(m, shaped(k, R)), idC(k, nil), size, n)`"
      let (m, k, R) ← keyShaped lit (keyCallArgs al)[0]! (keyCallArgs al)[1]!
      let i := as[1]!
      let ok := keyHead i == "idC" && (keyCallArgs i).size == 2 &&
        (keyCallArgs i)[0]!.raw.structEq (keyCallArgs (keyCallArgs al)[1]!)[0]!.raw &&
        (keyArgs (keyCallArgs i)[1]!)[0]?.map keyParts == some ["nil"]
      unless ok do Macro.throwErrorAt i "key{}: the array allocated, `idC(k, nil)`"
      `(LMem.newArr $m $k $R $(← at_ .term 3))
    else
      `(LMem.write $(← at_ .mem 0) $(← at_ .id 1) $(← at_ .sel 2) $(← at_ .mv 3))
  | .mem, "copySt" => do
    arity 3
    let src := keyCallArgs as[2]!
    unless keyHead as[2]! == "find" && src.size == 2 do
      Macro.throwErrorAt as[2]! "key{}: `copySt(m, k, find(s, q))`"
    `(LMem.copySt $(← at_ .mem 0) $(← at_ .ord 1) $(← keyAt lit .stor src[0]!)
        $(← keyAt lit .path src[1]!))
  -- the rest
  | .id, "idC" => do arity 2; `(LId.mk $(← at_ .ord 0) $(← at_ .segs 1))
  | .aop, "slot" => do arity 1; `(AOp.slot $(← at_ .ty 0))
  | .aop, "pop" => do arity 1; `(AOp.pop $(← at_ .bool 0))
  | .ty, "mapping" => do arity 2; `(Ty.ref (RefTy.mapping $(← at_ .ty 0) $(← at_ .ty 1)))
  | .refty, "mapping" => do arity 2; `(RefTy.mapping $(← at_ .ty 0) $(← at_ .ty 1))
  | _, _ => keyErr stx s!"`{h}(…)`" s

/-- `m, shaped(k, R)`, the arguments of an `addM`. -/
partial def keyShaped (lit : Bool) (m sh : TSyntax `key_term) : MacroM (Lean.Term × Lean.Term × Lean.Term) := do
  unless keyHead sh == "shaped" && (keyCallArgs sh).size == 2 do
    Macro.throwErrorAt sh "key{}: an allocation is `shaped(k, R)`"
  let as := keyCallArgs sh
  return (← keyAt lit .mem m, ← keyAt lit .ord as[0]!, ← keyAt lit .refty as[1]!)

end

macro_rules
  | `(key{ $t }) => keyAt false (keyTop t) t
  | `(key!{ $t }) => keyAt true (keyTop t) t

end Expand

/-! ## Printing -/

section Print
open Lean Meta PrettyPrinter Delaborator SubExpr
set_option hygiene false

@[category_parenthesizer key_term] def key_term.parenthesizer : CategoryParenthesizer
  | prec => Parenthesizer.maybeParenthesize `key_term false
      (fun stx => Unhygienic.run `(key_term| ($(⟨stx⟩)))) prec
      (Parenthesizer.parenthesizeCategoryCore `key_term prec)

/-- The most nodes `ppKey` prints; past them a subterm prints as `‹⋯›`. -/
def keyCutoff : Nat := 2000

/-- A printer of this notation: whether names print as literals (`key!`),
and the nodes left to print. -/
abbrev KeyM := ReaderT Bool (StateRefT Nat MetaM)

/-- The types of the language. -/
def keyTypes : List Lean.Name := [``LTerm, ``LPath, ``LStor, ``LMem, ``LSel, ``LMV, ``LId]

/-- The sort a constructor of the language builds. -/
def keySortOf? (c : Lean.Name) : Option KSort :=
  match c.getPrefix with
  | ``LTerm => some .term | ``LPath => some .path | ``LStor => some .stor
  | ``LMem => some .mem | ``LSel => some .sel | ``LMV => some .mv | ``LId => some .id
  | _ => none

/-- `e` as Lean prints it, in `‹…›`; a term of the language with this
notation off, so that it does not print itself again. -/
def keyEscTerm (e : Expr) : MetaM Lean.Term := do
  let own := match e.getAppFn.constName? with
    | some c => keyTypes.contains c.getPrefix
    | none => false
  if own then withOptions (fun o => pp.sol.dl.set o false) (PrettyPrinter.delab e)
  else PrettyPrinter.delab e

def kEsc (e : Expr) : KeyM (TSyntax `key_term) := do
  let t ← keyEscTerm e
  `(key_term| ‹$t›)

/-- One node more, unless the budget is spent. -/
def kTick : KeyM Bool := do
  let n ← get
  if n == 0 then return false
  set (n - 1)
  return true

/-- What is left past the budget. -/
def kElided : KeyM (TSyntax `key_term) := do
  let o ← `(⋯)
  `(key_term| ‹$o›)

/-- A string literal (`viewRoot` is one). -/
def keyStrLit? (e : Expr) : Option String :=
  match e.consumeMData with
  | .lit (.strVal s) => some s
  | .const ``viewRoot _ => some viewRoot
  | _ => none

/-- A natural number literal, raw or through `OfNat`. -/
def keyNatLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match (e.getArg! 1).consumeMData with
      | .lit (.natVal n) => some n
      | _ => none
    else none

/-- A non-negative integer literal. -/
def keyNonNeg? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  if e.isAppOfArity ``Int.ofNat 1 then keyNatLit? e.appArg! else keyNatLit? e

/-- An integer literal: `3`, `-3`, `Int.negSucc 2`. -/
def keyIntLit? (e : Expr) : Option Int :=
  let e := e.consumeMData
  if e.isAppOfArity ``Int.negSucc 1 then (keyNatLit? e.appArg!).map Int.negSucc
  else if e.isAppOfArity ``Neg.neg 3 then (keyNonNeg? e.appArg!).map fun n => -(n : Int)
  else (keyNonNeg? e).map Int.ofNat

/-- A name that reads back as itself where a literal name stands. -/
def keyPlain (s : String) : Bool :=
  !s.isEmpty && s != "_" && s != "length" && !keyReserved.contains s &&
    (s.front.isAlpha || s.front == '_') &&
    s.all fun c => c.isAlphanum || c == '_' || c == '\''

def kNum (n : Nat) : KeyM (TSyntax `key_term) := `(key_term| $(Syntax.mkNumLit (toString n)):num)

def kInt (i : Int) : KeyM (TSyntax `key_term) :=
  if i < 0 then `(key_term| -$(Syntax.mkNumLit (toString i.natAbs)):num) else kNum i.toNat

def kIdent (s : String) : KeyM (TSyntax `key_term) := `(key_term| $(mkIdent (Lean.Name.mkSimple s)):ident)

def kStr (s : String) : KeyM (TSyntax `key_term) := `(key_term| $(Syntax.mkStrLit s):str)

/-- A variable of the term, in `key{ }`: its name, when that reads back. -/
def kFVar? (e : Expr) : KeyM (Option (TSyntax `key_term)) := do
  if ← read then return none
  let .fvar fv := e.consumeMData | return none
  let n ← fv.getUserName
  if n.hasMacroScopes then return none
  let .str .anonymous s := n | return none
  if !keyPlain s then return none
  return some (← kIdent s)

/-- A literal name: an identifier in `key!{ }`, a string in `key{ }`. -/
def kLitName (s : String) : KeyM (TSyntax `key_term) := do
  if (← read) && keyPlain s then kIdent s else kStr s

/-- A name: a literal, or a variable. -/
def kName (e : Expr) : KeyM (TSyntax `key_term) := do
  if let some s := keyStrLit? e then return ← kLitName s
  if let some x ← kFVar? e then return x
  kEsc e

/-- The default spelling of fresh variables, `se1`. -/
def keyFresh : FreshNames := .ofPrefixes "se" "sp" "ie" "mv"

/-- A variable of the program (`Var`). -/
def kVar? (e : Expr) : KeyM (Option (TSyntax `key_term)) := do
  let e := e.consumeMData
  let s? : Option String :=
    if e.isAppOfArity ``Var.ofName 2 then keyStrLit? e.appArg!
    else if e.isAppOfArity ``Var.user 1 then
      (keyStrLit? e.appArg!).filter fun s => (keyFresh.parse s).isNone
    else if e.isAppOfArity ``Var.fresh 2 then
      match keyStrLit? (e.getArg! 0), keyNatLit? (e.getArg! 1) with
      | some b, some k =>
        let s := keyFresh.name b k
        if keyFresh.parse s == some (b, k) then some s else none
      | _, _ => none
    else none
  match s? with
  | some s => return some (← kLitName s)
  | none => return none

/-- A constructor named in `key!{ }`, escaped in `key{ }`. -/
def kCtor (e : Expr) (ns : Lean.Name) : KeyM (TSyntax `key_term) := do
  match e.consumeMData with
  | .const c _ =>
    if (← read) && c.getPrefix == ns then
      if let .str _ s := c then return ← kIdent s
    kEsc e
  | _ => if let some x ← kFVar? e then pure x else kEsc e

/-- The primitive type's name, which both notations read. -/
def kPrim (e : Expr) : KeyM (TSyntax `key_term) := do
  match e.consumeMData with
  | .const ``PrimTy.uint _ => kIdent "uint"
  | .const ``PrimTy.int _ => kIdent "int"
  | .const ``PrimTy.bool _ => kIdent "bool"
  | _ => if let some x ← kFVar? e then pure x else kEsc e

/-- The printed operator `a op b`, at its own type. -/
def kInfix (op p : Expr) (a b : TSyntax `key_term) : KeyM (Option (TSyntax `key_term)) := do
  let (.const o _, .const t _) := (op.consumeMData, p.consumeMData) | return none
  let some (k, _, _) := keyInfix.find? fun (_, o', t') => o' == o && t' == t | return none
  let r : Option (TSyntax `key_term) ← match k with
    | ``ktMul => some <$> `(key_term| $a * $b) | ``ktDiv => some <$> `(key_term| $a / $b)
    | ``ktMod => some <$> `(key_term| $a % $b) | ``ktAdd => some <$> `(key_term| $a + $b)
    | ``ktSub => some <$> `(key_term| $a - $b) | ``ktLt => some <$> `(key_term| $a < $b)
    | ``ktLe => some <$> `(key_term| $a <= $b) | ``ktGt => some <$> `(key_term| $a > $b)
    | ``ktGe => some <$> `(key_term| $a >= $b) | ``ktEq => some <$> `(key_term| $a == $b)
    | ``ktNe => some <$> `(key_term| $a != $b) | ``ktAnd => some <$> `(key_term| $a && $b)
    | ``ktOr => some <$> `(key_term| $a || $b)
    | _ => pure none
  return r

/-- Whether a printed term reads back as a variable or an escape at any
sort, so that it cannot stand for a word or a name in a memory slot. -/
def kBare (t : TSyntax `key_term) : Bool :=
  t.raw.getKind == ``ktIdent || t.raw.getKind == ``ktEsc

mutual

/-- A term (`LTerm`). -/
partial def pkTerm (e : Expr) : KeyM (TSyntax `key_term) := do
  unless ← kTick do return ← kElided
  let e := e.consumeMData
  if let some x ← kFVar? e then return x
  match_expr e with
  | LTerm.lit v =>
    let v := v.consumeMData
    if v.isAppOfArity ``PrimVal.int 1 then
      if let some i := keyIntLit? v.appArg! then return ← kInt i
    if v.isAppOfArity ``PrimVal.bool 1 then
      match v.appArg!.consumeMData with
      | .const ``Bool.true _ => return ← kIdent "true"
      | .const ``Bool.false _ => return ← kIdent "false"
      | _ => pure ()
    let some x ← kFVar? v | kEsc e
    `(key_term| lit($x))
  | LTerm.var x =>
    if let some t ← kVar? x then
      -- a literal in `key{ }` is a string, which the term position reads as one
      return t
    let x' ← match ← kFVar? x with
      | some t => pure t
      | none => kEsc x
    `(key_term| var($x'))
  | LTerm.binop op p a b =>
    let a' ← pkTerm a
    let b' ← pkTerm b
    if let some t ← kInfix op p a' b' then return t
    `(key_term| binop($(← kCtor op ``BinOp), $(← kPrim p), $a', $b'))
  | LTerm.unop op p a => `(key_term| unop($(← kCtor op ``UnOp), $(← kPrim p), $(← pkTerm a)))
  | LTerm.ite c a b => `(key_term| if($(← pkTerm c)) then $(← pkTerm a) else $(← pkTerm b))
  | LTerm.find s q => `(key_term| find($(← pkStor s), $(← pkPath q)))
  | LTerm.has s q => `(key_term| has($(← pkStor s), $(← pkPath q)))
  | LTerm.kmap sh s q =>
    match sh.consumeMData with
    | .const ``KShape.map _ => `(key_term| isMap($(← pkStor s), $(← pkPath q)))
    | .const ``KShape.fixed _ => `(key_term| isFixed($(← pkStor s), $(← pkPath q)))
    | _ =>
      let sh' ← match ← kFVar? sh with
        | some t => pure t
        | none => kEsc sh
      `(key_term| kmap($sh', $(← pkStor s), $(← pkPath q)))
  | LTerm.len s q => `(key_term| find($(← pkStor s), $(← kLength (← pkPath q))))
  | LTerm.sok s =>
    let s' ← pkStor s
    if kBare s' && keyTop s' != .stor then `(key_term| okSt($s')) else `(key_term| ok($s'))
  | LTerm.pok q =>
    let q' ← pkPath q
    if kBare q' && !(← read) || q'.raw.getKind == ``ktEsc then `(key_term| okPath($q'))
    else `(key_term| ok($q'))
  | LTerm.seq d a => `(key_term| ($(← pkTerm d); $(← pkTerm a)))
  | LTerm.orElse a b => `(key_term| orElse($(← pkTerm a), $(← pkTerm b)))
  | LTerm.kite a b t f =>
    `(key_term| if($(← pkTerm a) = $(← pkTerm b)) then $(← pkTerm t) else $(← pkTerm f))
  | LTerm.zero a => `(key_term| delValue($(← pkTerm a)))
  | LTerm.err => kIdent "err"
  | LTerm.env k =>
    match k.consumeMData with
    | .const ``EnvKey.msgSender _ => `(key_term| msg.sender)
    | .const ``EnvKey.msgValue _ => `(key_term| msg.value)
    | .const ``EnvKey.timestamp _ => `(key_term| block.timestamp)
    | .const ``EnvKey.selfAddress _ => `(key_term| address(this))
    | .const ``EnvKey.selfBalance _ => `(key_term| address(this).balance)
    | _ => `(key_term| env($(← kCtor k ``EnvKey)))
  | LTerm.findP s q => `(key_term| findP($(← pkStor s), $(← pkPath q)))
  | LTerm.cpok s q => `(key_term| copyOk($(← pkStor s), $(← pkPath q)))
  | _ => kEsc e

/-- `q.length`, the path `q` asked for its length. -/
partial def kLength (q : TSyntax `key_term) : KeyM (TSyntax `key_term) := do
  match q with
  | `(key_term| $x:ident) => `(key_term| $(mkIdent (x.getId.str "length")):ident)
  | _ => `(key_term| $q:key_term . length)

/-- A path (`LPath`). -/
partial def pkPath (e : Expr) : KeyM (TSyntax `key_term) := do
  unless ← kTick do return ← kElided
  let e := e.consumeMData
  if let some x ← kFVar? e then return x
  match_expr e with
  | LPath.root r =>
    let some s := keyStrLit? r | kEsc e
    kLitName s
  | LPath.field q f =>
    let q' ← pkPath q
    if let some s := keyStrLit? f then
      if (← read) && keyPlain s then
        if let `(key_term| $x:ident) := q' then
          return ← `(key_term| $(mkIdent (x.getId.str s)):ident)
        return ← `(key_term| $q':key_term . $(mkIdent (Lean.Name.mkSimple s)):ident)
      return ← `(key_term| $q':key_term . $(Syntax.mkStrLit s):str)
    let some f' ← kFVar? f | kEsc e
    let `(key_term| $fx:ident) := f' | kEsc e
    if let `(key_term| $x:ident) := q' then
      return ← `(key_term| $(mkIdent (x.getId ++ fx.getId)):ident)
    `(key_term| $q':key_term . $fx:ident)
  | LPath.at q k => `(key_term| $(← pkPath q)[$(← pkTerm k)])
  | _ => kEsc e

/-- A storage (`LStor`). -/
partial def pkStor (e : Expr) : KeyM (TSyntax `key_term) := do
  unless ← kTick do return ← kElided
  let e := e.consumeMData
  if let some x ← kFVar? e then return x
  match_expr e with
  | LStor.init => kIdent "storage"
  | LStor.save s q w =>
    -- a read written is `select`: `find` there is a copy
    let w' ← match_expr w.consumeMData with
      | LTerm.find s' q' => `(key_term| select($(← pkStor s'), $(← pkPath q')))
      | LTerm.len s' q' => `(key_term| select($(← pkStor s'), $(← kLength (← pkPath q'))))
      | _ => pkTerm w
    `(key_term| save($(← pkStor s), $(← pkPath q), $w'))
  | LStor.del s q => `(key_term| delAt($(← pkStor s), $(← pkPath q)))
  | LStor.arr op s q w =>
    if op.consumeMData.isConstOf ``AOp.push then
      `(key_term| push($(← pkStor s), $(← pkPath q), $(← pkTerm w)))
    else `(key_term| arr($(← pkAOp op), $(← pkStor s), $(← pkPath q), $(← pkTerm w)))
  | LStor.stale o s q w =>
    let o := o.consumeMData
    if o.isAppOfArity ``Option.none 1 then
      `(key_term| staleSave($(← pkStor s), $(← pkPath q), $(← pkTerm w)))
    else if o.isAppOfArity ``Option.some 2 then
      `(key_term| stale($(← pkAOp o.appArg!), $(← pkStor s), $(← pkPath q), $(← pkTerm w)))
    else kEsc e
  | LStor.copy s q src sq =>
    let viewAt := match_expr sq.consumeMData with
      | LPath.root r => keyStrLit? r == some viewRoot
      | _ => false
    let src' ← pkStor src
    let w ← if viewAt && src.consumeMData.isAppOfArity ``LStor.view 2 then pure src'
      else `(key_term| find($src', $(← pkPath sq)))
    `(key_term| save($(← pkStor s), $(← pkPath q), $w))
  | LStor.view m i => `(key_term| copyMem(mtSt, $(← pkMem m), $(← pkId i)))
  | _ => kEsc e

/-- An array operation (`AOp`). -/
partial def pkAOp (e : Expr) : KeyM (TSyntax `key_term) := do
  let e := e.consumeMData
  if let some x ← kFVar? e then return x
  match_expr e with
  | AOp.push => kIdent "push"
  | AOp.slot T => `(key_term| slot($(← pkTy T)))
  | AOp.pop b =>
    match b.consumeMData with
    | .const ``Bool.true _ => `(key_term| pop(true))
    | .const ``Bool.false _ => `(key_term| pop(false))
    | _ => match ← kFVar? b with
      | some b' => `(key_term| pop($b'))
      | none => kEsc e
  | _ => kEsc e

/-- A type (`Ty`). -/
partial def pkTy (e : Expr) : KeyM (TSyntax `key_term) := do
  let e := e.consumeMData
  if let some x ← kFVar? e then return x
  match_expr e with
  | Ty.prim p => kPrim p
  | Ty.ref R => pkRefTy R
  | _ => kEsc e

/-- A reference type (`RefTy`). -/
partial def pkRefTy (e : Expr) : KeyM (TSyntax `key_term) := do
  let e := e.consumeMData
  if let some x ← kFVar? e then return x
  match_expr e with
  | RefTy.struct n =>
    let some s := keyStrLit? n | kEsc e
    if (← read) && keyPlain s && !["uint", "int", "bool", "address"].contains s then kIdent s
    else kStr s
  | RefTy.array E => `(key_term| $(← pkTy E)[])
  | RefTy.fixed E n =>
    let some k := keyNatLit? n | kEsc e
    `(key_term| $(← pkTy E)[$(← kNum k)])
  | RefTy.mapping K V => `(key_term| mapping($(← pkTy K), $(← pkTy V)))
  | _ => kEsc e

/-- A memory (`LMem`). -/
partial def pkMem (e : Expr) : KeyM (TSyntax `key_term) := do
  unless ← kTick do return ← kElided
  let e := e.consumeMData
  if let some x ← kFVar? e then return x
  match_expr e with
  | LMem.init => kIdent "memory"
  | LMem.addM m k R =>
    `(key_term| addM($(← pkMem m), shaped($(← pkOrd k), $(← pkRefTy R))))
  | LMem.newArr m k R n =>
    let k' ← pkOrd k
    `(key_term| write(addM($(← pkMem m), shaped($k', $(← pkRefTy R))), idC($k', nil), size,
        $(← pkTerm n)))
  | LMem.copySt m k s q =>
    `(key_term| copySt($(← pkMem m), $(← pkOrd k), find($(← pkStor s), $(← pkPath q))))
  | LMem.write m i a v =>
    -- a write of `size` would read as an allocation
    let a' ← if a.consumeMData.isConstOf ``LSel.size then kEsc a else pkSel a
    `(key_term| write($(← pkMem m), $(← pkId i), $a', $(← pkMV v)))
  | _ => kEsc e

/-- An allocation's ordinal: `idp0` in `key!{ }`, `0` in `key{ }`. -/
partial def pkOrd (e : Expr) : KeyM (TSyntax `key_term) := do
  if let some k := keyNatLit? e then
    return ← if ← read then kIdent s!"idp{k}" else kNum k
  if let some x ← kFVar? e then return x
  kEsc e

/-- A memory name (`LId`). -/
partial def pkId (e : Expr) : KeyM (TSyntax `key_term) := do
  unless ← kTick do return ← kElided
  let e := e.consumeMData
  if let some x ← kFVar? e then return x
  match_expr e with
  | LId.mk k p => `(key_term| idC($(← pkOrd k), $(← pkSegs p)))
  | _ => kEsc e

/-- The selectors of a memory name: `nil`, `[f, at(2)]`. -/
partial def pkSegs (e : Expr) : KeyM (TSyntax `key_term) := do
  let e := e.consumeMData
  if let some x ← kFVar? e then return x
  let rec go (e : Expr) (acc : Array (TSyntax `key_term)) :
      KeyM (Option (Array (TSyntax `key_term))) := do
    let e := e.consumeMData
    if e.isAppOfArity ``List.nil 1 then return some acc
    if e.isAppOfArity ``List.cons 3 then
      let some s ← pkSeg (e.getArg! 1) | return none
      return ← go e.appArg! (acc.push s)
    return none
  let some ss ← go e #[] | kEsc e
  if ss.isEmpty then kIdent "nil" else `(key_term| [$ss,*])

/-- A selector of a memory name (`Seg`). -/
partial def pkSeg (e : Expr) : KeyM (Option (TSyntax `key_term)) := do
  let e := e.consumeMData
  match_expr e with
  | Seg.field f =>
    if let some s := keyStrLit? f then return some (← kLitName s)
    return ← kFVar? f
  | Seg.at i =>
    if let some k := keyIntLit? i then return some (← `(key_term| at($(← kInt k))))
    let some i' ← kFVar? i | return none
    return some (← `(key_term| at($i')))
  | _ => return none

/-- A selector (`LSel`). -/
partial def pkSel (e : Expr) : KeyM (TSyntax `key_term) := do
  let e := e.consumeMData
  if let some x ← kFVar? e then return x
  match_expr e with
  | LSel.fld f =>
    let some s := keyStrLit? f | kEsc e
    kLitName s
  | LSel.idx t => `(key_term| at($(← pkTerm t)))
  | LSel.size => kIdent "size"
  | _ => kEsc e

/-- A memory value (`LMV`): a name, or a word. -/
partial def pkMV (e : Expr) : KeyM (TSyntax `key_term) := do
  let e := e.consumeMData
  if let some x ← kFVar? e then return x
  match_expr e with
  | LMV.word t =>
    let t' ← pkTerm t
    -- a variable here is a memory value, and an escape is one too
    if t'.raw.getKind == ``ktEsc || (t'.raw.getKind == ``ktIdent && !(← read)) then kEsc e
    else pure t'
  | LMV.ref i =>
    let i' ← pkId i
    if kBare i' then kEsc e else pure i'
  | _ => kEsc e

end

/-- The term at the sort `s`. -/
def pkAt (s : KSort) (e : Expr) : KeyM (TSyntax `key_term) :=
  match s with
  | .term => pkTerm e | .path => pkPath e | .stor => pkStor e | .mem => pkMem e
  | .id => pkId e | .sel => pkSel e | .mv => pkMV e | _ => kEsc e

/-- A term of the language in this notation, and whether it is closed
(`key!{ }`). -/
def ppKey (e : Expr) : MetaM (TSyntax `key_term × Bool) := do
  let e ← instantiateMVars e
  let s := (e.getAppFn.constName? >>= keySortOf?).getD .term
  let lit := !e.hasFVar && !e.hasMVar
  let t ← (pkAt s e).run lit |>.run' keyCutoff
  return (t, lit)

/-- `key!{ t }` for a closed term of the language, `key{ t }` for one over
variables.  A term that would read back at another sort (a lone root, a
lone field, a word) prints as Lean prints it. -/
def delabKey : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  let some s := keySortOf? c | failure
  guard (e.getAppNumArgs == (← getConstInfo c).type.getNumHeadForalls)
  let (t, lit) ← ppKey e
  guard (keyTop t == s)
  guard (t.raw.getKind != ``ktEsc)
  if lit then `(key!{ $t }) else `(key{ $t })

attribute [delab app.Solidity.Decide.LTerm.lit, delab app.Solidity.Decide.LTerm.var,
  delab app.Solidity.Decide.LTerm.binop, delab app.Solidity.Decide.LTerm.unop,
  delab app.Solidity.Decide.LTerm.ite, delab app.Solidity.Decide.LTerm.find,
  delab app.Solidity.Decide.LTerm.has, delab app.Solidity.Decide.LTerm.kmap,
  delab app.Solidity.Decide.LTerm.len, delab app.Solidity.Decide.LTerm.sok,
  delab app.Solidity.Decide.LTerm.pok, delab app.Solidity.Decide.LTerm.seq,
  delab app.Solidity.Decide.LTerm.orElse, delab app.Solidity.Decide.LTerm.kite,
  delab app.Solidity.Decide.LTerm.zero, delab app.Solidity.Decide.LTerm.err,
  delab app.Solidity.Decide.LTerm.env, delab app.Solidity.Decide.LTerm.findP,
  delab app.Solidity.Decide.LTerm.cpok,
  delab app.Solidity.Decide.LPath.field, delab app.Solidity.Decide.LPath.at,
  delab app.Solidity.Decide.LStor.init, delab app.Solidity.Decide.LStor.save,
  delab app.Solidity.Decide.LStor.del, delab app.Solidity.Decide.LStor.arr,
  delab app.Solidity.Decide.LStor.stale, delab app.Solidity.Decide.LStor.copy,
  delab app.Solidity.Decide.LStor.view,
  delab app.Solidity.Decide.LMem.init, delab app.Solidity.Decide.LMem.addM,
  delab app.Solidity.Decide.LMem.newArr, delab app.Solidity.Decide.LMem.copySt,
  delab app.Solidity.Decide.LMem.write, delab app.Solidity.Decide.LId.mk,
  delab app.Solidity.Decide.LSel.idx, delab app.Solidity.Decide.LSel.size] delabKey

end Print

end Decide

end Solidity

/-! ## Round trips

Each line reads to the constructors written beside it (`rfl`), and prints
back as it was written (`#guard_msgs`). -/

namespace Solidity.Decide
open Semantics

example : key!{ save(storage, alice.age, 42) } =
    LStor.save .init (.field (.root "alice") "age") (.lit (.int 42)) := rfl

example : key!{ find(save(storage, balances[msg.sender], find(storage, balances[msg.sender]) - 1),
      total) } =
    LTerm.find (.save .init (.at (.root "balances") (.env .msgSender))
      (.binop .sub .uint (.find .init (.at (.root "balances") (.env .msgSender))) (.lit (.int 1))))
      (.root "total") := rfl

example : key!{ if(i = j) then 7 else find(delAt(storage, values), values[i]) } =
    LTerm.kite (.var (.user "i")) (.var (.user "j")) (.lit (.int 7))
      (.find (.del .init (.root "values")) (.at (.root "values") (.var (.user "i")))) := rfl

-- a copy, a read written, a length
example : key!{ save(storage, alice, find(storage, bob)) } =
    LStor.copy .init (.root "alice") .init (.root "bob") := rfl
example : key!{ save(storage, total, select(storage, values.length)) } =
    LStor.save .init (.root "total") (.len .init (.root "values")) := rfl

-- memory: an array allocated and written, copied back to storage
example : key!{ save(storage, values, copyMem(mtSt, write(write(addM(memory, shaped(idp0, uint[])),
      idC(idp0, nil), size, n), idC(idp0, nil), at(i), 7), idC(idp0, nil))) } =
    LStor.copy .init (.root "values")
      (.view (.write (.newArr .init 0 (.array (.prim .uint)) (.var (.user "n"))) ⟨0, []⟩
        (.idx (.var (.user "i"))) (.word (.lit (.int 7)))) ⟨0, []⟩) (.root viewRoot) := rfl

example : key!{ write(memory, idC(idp0, [account, at(2)]), balance, idC(idp1, nil)) } =
    LMem.write .init ⟨0, [.field "account", .at 2]⟩ (.fld "balance") (.ref ⟨1, []⟩) := rfl

example : key!{ staleSave(stale(pop(false), storage, values, 0), values[0], -1) } =
    LStor.stale none (.stale (some (.pop false)) .init (.root "values") (.lit (.int 0)))
      (.at (.root "values") (.lit (.int 0))) (.lit (.int (-1))) := rfl

example : key!{ (ok(alice.age); if(0 < x) then true else err) } =
    LTerm.seq (.pok (.field (.root "alice") "age"))
      (.ite (.binop .lt .uint (.lit (.int 0)) (.var (.user "x"))) (.lit (.bool true)) .err) := rfl

-- a fresh variable reads as `FreshNames` spells it
example : key!{ se1 } = LTerm.var (Var.ofName "se1") := rfl

/-- info: key!{ save(storage, alice.age, 42) } : LStor -/
#guard_msgs in #check key!{ save(storage, alice.age, 42) }

/--
info: key!{ find(save(storage, balances[msg.sender], find(storage, balances[msg.sender]) - 1), total) } : LTerm
-/
#guard_msgs in
#check key!{ find(save(storage, balances[msg.sender], find(storage, balances[msg.sender]) - 1),
  total) }

/--
info: key!{
  save(storage, values,
    copyMem(mtSt, write(write(addM(memory, shaped(idp0, uint[])), idC(idp0, nil), size, n), idC(idp0, nil), at(i), 7),
      idC(idp0, nil))) } : LStor
-/
#guard_msgs in
#check key!{ save(storage, values, copyMem(mtSt, write(write(addM(memory, shaped(idp0, uint[])),
  idC(idp0, nil), size, n), idC(idp0, nil), at(i), 7), idC(idp0, nil))) }

/-- info: key!{ save(storage, total, select(storage, values.length)) } : LStor -/
#guard_msgs in #check key!{ save(storage, total, select(storage, values.length)) }

/-- info: key!{ copySt(addM(memory, shaped(idp0, Person)), idp1, find(storage, alice)) } : LMem -/
#guard_msgs in #check key!{ copySt(addM(memory, shaped(idp0, Person)), idp1, find(storage, alice)) }

/-- info: key!{ staleSave(stale(pop(false), storage, values, 0), values[0], -1) } : LStor -/
#guard_msgs in #check key!{ staleSave(stale(pop(false), storage, values, 0), values[0], -1) }

/--
info: key!{ binop(add, int, delValue(x), address(this).balance) && msg.value >= block.timestamp } : LTerm
-/
#guard_msgs in
#check key!{ binop(add, int, delValue(x), address(this).balance) && msg.value >= block.timestamp }

/-- info: key!{ orElse(findP(storage, alice.age), has(storage, alice)) || ok(storage) } : LTerm -/
#guard_msgs in #check key!{ orElse(findP(storage, alice.age), has(storage, alice)) || ok(storage) }

-- a fresh variable, and a name that is reserved
/-- info: key!{ save(storage, "storage", se1) } : LStor -/
#guard_msgs in #check LStor.save .init (.root "storage") (.var (.fresh "se" 1))

-- over variables: a literal name is a string
/-- info: fun s q w => key{ find(save(s, q, w), q."age") } : LStor → LPath → LTerm → LTerm -/
#guard_msgs in #check fun (s : LStor) (q : LPath) (w : LTerm) => key{ find(save(s, q, w), q."age") }

/-- info: fun Q L => key{ (okPath(Q); if(0 < L) then true else err) } : LPath → LTerm → LTerm -/
#guard_msgs in
#check fun (Q : LPath) (L : LTerm) => key{ (okPath(Q); if(0 < L) then true else err) }

-- a lone root would read back as a variable, so it prints as Lean prints it
/-- info: LPath.root "alice" : LPath -/
#guard_msgs in #check LPath.root "alice"

/-! ## A pattern

A clause matches one constructor deep, its names pattern variables: the
arm below is solkey's `\find(read(write(mem, id1, a1, v), id2, a2))` split
over its arguments. -/

/-- The value of the newest write, when it is to `id2` at `a2`. -/
def lastWrite? : LMem → LId → LSel → Option LMV
  | key{ write(_, id1, a1, v) }, id2, a2 =>
    if id1 = id2 ∧ a1 = a2 then some v else none
  | _, _, _ => none

example : lastWrite? key!{ write(memory, idC(idp0, nil), at(3), 7) } key!{ idC(idp0, nil) }
    (.idx key!{ 3 }) = some (.word key!{ 7 }) := rfl

end Solidity.Decide
