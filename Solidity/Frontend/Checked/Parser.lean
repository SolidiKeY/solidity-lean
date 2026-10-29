import Solidity.Frontend.Checked.Print

/-!
# The parser (G09–G11)

A recursive-descent parser from located tokens (`Solidity/Frontend/Checked/Lexer.lean`)
to S00's intrinsic syntax (`Syn .unit`), with the layout of attribute orders
and string fragments it read (`Choice`, `Solidity/Frontend/Checked/Print.lean`).
It is untrusted: `Solidity.Frontend.Checked.parse` (`Check.lean`) accepts
its result only if the tree's yield under that layout is the token sequence
and the tree satisfies the precedence predicate (`Syn.prec`).

It follows solc's parser where solc decides what the grammar leaves open:
expressions by precedence climbing with solc's levels (a conditional's
branches and an assignment's right side are whole expressions), call options
only when `{` is followed by `identifier :`, a statement beginning with a
type name followed by a data location or an identifier is a declaration,
`revert` followed by an identifier is a revert statement, `emit`/`revert`
targets are paths, attribute keywords are taken at most once and greedily
(so `function () internal x;` gives the function type the visibility, and a
second visibility ends a function type's attributes).

Recursion is structural on a fuel argument (`16 ×` the token count plus
one), so the kernel can evaluate a parse; fuel bounds the nesting depth, and
running out is an error, never a wrong tree.
-/

namespace Solidity.Frontend.Checked

open Solidity.Source

/-! ## The parser monad -/

structure St where
  ts : List Located
  /-- The layout read so far, reversed. -/
  ch : List Choice
  eof : Nat

abbrev P := StateT St (Except Error)

def St.pos (s : St) : Nat :=
  match s.ts with
  | t :: _ => t.start
  | [] => s.eof

def P.fail {α : Type} (msg : String) : P α := fun s => .error ⟨s.pos, msg⟩

def peekN (i : Nat) : P (Option Tok) := fun s => .ok ((s.ts.drop i).head?.map (·.tok), s)
def peek : P (Option Tok) := peekN 0

def advance : P Unit := fun s => .ok ((), { s with ts := s.ts.drop 1 })

def isTok (t : Tok) : P Bool := do return (← peek) == some t
def isP (p : Punct) : P Bool := isTok (.punct p)
def isK (k : Kw) : P Bool := isTok (.kw k)

/-- Consume `t` if it is next. -/
def eat (t : Tok) : P Bool := do
  if ← isTok t then advance; return true else return false

def expect (t : Tok) (what : String) : P Unit := do
  if ← isTok t then advance else P.fail s!"expected {what}"

def expectP (p : Punct) : P Unit := expect (.punct p) s!"'{p.spell}'"

def ident : P String := do
  match ← peek with
  | some (.ident s) => advance; return s
  | _ => P.fail "expected an identifier"

/-- Run `p`; on failure restore the state. -/
def attempt {α : Type} (p : P α) : P (Option α) := fun s =>
  match p s with
  | .ok (a, s') => .ok (some a, s')
  | .error _ => .ok (none, s)

/-- Run `p` with an empty layout and return what it read, without
recording it. -/
def capture {α : Type} (p : P α) : P (α × List Choice) := fun s =>
  match p { s with ch := [] } with
  | .ok (a, s') => .ok ((a, s'.ch.reverse), { s' with ch := s.ch })
  | .error e => .error e

def record (cs : List Choice) : P Unit := fun s => .ok ((), { s with ch := cs.reverse ++ s.ch })

/-! ## Combinators -/

def sepByAux {α : Type} (p : P α) : Nat → P (List α)
  | 0 => P.fail "too many list elements"
  | n + 1 => do
    if ← eat (.punct .comma) then
      let a ← p
      let r ← sepByAux p n
      return a :: r
    else return []

/-- `p (, p)*`. -/
def sepBy1 {α : Type} (p : P α) : P (List α) := do
  let a ← p
  let r ← fun s => sepByAux p (s.ts.length + 1) s
  return a :: r

def manyAux {α : Type} (p : P (Option α)) : Nat → P (List α)
  | 0 => P.fail "no progress"
  | n + 1 => do
    match ← p with
    | some a =>
      let r ← manyAux p n
      return a :: r
    | none => return []

/-- `p*`, where `p` answers `none` to stop. -/
def many {α : Type} (p : P (Option α)) : P (List α) := fun s => manyAux p (s.ts.length + 1) s

/-- `identifierPath`. -/
def idPath : P IdPath := do
  let h ← ident
  let t ← many do
    if (← peek) == some (.punct .period) then
      match ← peekN 1 with
      | some (.ident s) => advance; advance; return some s
      | _ => return none
    else return none
  return ⟨h, t⟩

def toSynList {c : Cat} : List (Syn c) → Syn (.list c)
  | [] => .nil
  | x :: xs => .cons x (toSynList xs)

def toSynOpt {c : Cat} : Option (Syn c) → Syn (.opt c)
  | Option.none => .none
  | Option.some x => .some x

def visOf : Tok → Option Visibility
  | .kw .internal => some .internal | .kw .external => some .external
  | .kw .private_ => some .priv | .kw .public_ => some .pub | _ => none

def mutOf : Tok → Option Mutability
  | .kw .pure => some .pure | .kw .view => some .view | .kw .payable => some .payable
  | _ => none

def locOf : Tok → Option DataLoc
  | .kw .memory => some .memory | .kw .storage => some .storage
  | .kw .calldata => some .calldata | _ => none

def assignOf : Tok → Option AssignOp
  | .punct .assign => some .assign | .punct .assignBitOr => some .bitOr
  | .punct .assignBitXor => some .bitXor | .punct .assignBitAnd => some .bitAnd
  | .punct .assignShl => some .shl | .punct .assignSar => some .sar
  | .punct .assignShr => some .shr | .punct .assignAdd => some .add
  | .punct .assignSub => some .sub | .punct .assignMul => some .mul
  | .punct .assignDiv => some .div | .punct .assignMod => some .mod
  | _ => none

/-- A binary operator: its level and its node. -/
def binOf : Tok → Option (Nat × (Syn .expr → Syn .expr → Syn .expr))
  | .punct .or => some (2, .or) | .punct .and => some (3, .and)
  | .punct .equal => some (4, .equality .eq) | .punct .notEqual => some (4, .equality .ne)
  | .punct .lt => some (5, .order .lt) | .punct .gt => some (5, .order .gt)
  | .punct .le => some (5, .order .le) | .punct .ge => some (5, .order .ge)
  | .punct .bitOr => some (6, .bitOr) | .punct .bitXor => some (7, .bitXor)
  | .punct .bitAnd => some (8, .bitAnd)
  | .punct .shl => some (9, .shift .shl) | .punct .sar => some (9, .shift .sar)
  | .punct .shr => some (9, .shift .shr)
  | .punct .add => some (10, .addSub .add) | .punct .sub => some (10, .addSub .sub)
  | .punct .mul => some (11, .mulDivMod .mul) | .punct .div => some (11, .mulDivMod .div)
  | .punct .mod => some (11, .mulDivMod .mod)
  | .punct .exp => some (12, .exp)
  | _ => none

def prefixOf : Tok → Option PrefixOp
  | .punct .inc => some .inc | .punct .dec => some .dec | .punct .not => some .not
  | .punct .bitNot => some .bitNot | .kw .delete => some .delete | .punct .sub => some .neg
  | _ => none

def userOpOf : Tok → Option UserOp
  | .punct .bitAnd => some .bitAnd | .punct .bitNot => some .bitNot
  | .punct .bitOr => some .bitOr | .punct .bitXor => some .bitXor | .punct .add => some .add
  | .punct .div => some .div | .punct .mod => some .mod | .punct .mul => some .mul
  | .punct .sub => some .sub | .punct .equal => some .eq | .punct .gt => some .gt
  | .punct .ge => some .ge | .punct .lt => some .lt | .punct .le => some .le
  | .punct .notEqual => some .ne | _ => none

def isAscii (b : Bytes) : Bool := b.all (·.toNat < 128)

/-- A string token's bytes as a path or flag (ASCII only). -/
def strArg (what : String) : P String := do
  match ← peek with
  | some (.str b) =>
    if b.isEmpty then P.fail s!"empty {what}"
    else if isAscii b then advance; return b.str else P.fail s!"non-ASCII {what}"
  | _ => P.fail s!"expected {what}"

/-- A string literal's fragments: consecutive tokens of one kind. -/
def fragments (sel : Tok → Option Bytes) : P (List Bytes) := many do
  match ← peek with
  | some t => match sel t with
    | some b => advance; return some b
    | none => return none
  | none => return none

/-- The elementary type at a type position (`address payable` allowed). -/
def elemTypeName : P Elem := do
  match ← peek with
  | some (.elem e) =>
    advance
    if e == .address then
      if ← eat (.kw .payable) then return .addressPayable
    return e
  | _ => P.fail "expected an elementary type name"

/-- A Yul literal. -/
def yulLitOf : Tok → Option YulLit
  | .yulDec n => some (.dec n) | .yulHex n => some (.hex n) | .str b => some (.str b)
  | .hexStr b => some (.hexStr b) | .bool b => some (.bool b) | _ => none

/-- Yul identifiers separated by commas, possibly none before `stop`. -/
def identList : P (List String) := sepBy1 ident

/-- A function type's attributes: a visibility and a mutability, each at
most once.  A second visibility ends the run (it is the state variable's, as
the grammar's `{!$visibilitySet}?` and solc read it); a second mutability is
an error. -/
def fnTypeAttrs : Nat → Option Visibility → Option Mutability → List Slot →
    P (Option Visibility × Option Mutability × List Slot)
  | 0, v, m, o => pure (v, m, o.reverse)
  | k + 1, v, m, o => do
    match ← peek with
    | some t =>
      match visOf t, mutOf t with
      | some x, _ =>
        if v.isSome then pure (v, m, o.reverse)
        else do advance; fnTypeAttrs k (some x) m (.vis :: o)
      | _, some x =>
        if m.isSome then P.fail "repeated function type attribute"
        else do advance; fnTypeAttrs k v (some x) (.mutab :: o)
      | _, _ => pure (v, m, o.reverse)
    | none => pure (v, m, o.reverse)

/-- A list of absent options (a tuple's empty components). -/
def allNone : {c : Cat} → Syn c → Bool
  | _, .nil => true
  | _, .cons .none r => allNone r
  | _, _ => false

/-! ## The grammar -/

/-- An optional identifier. -/
def optIdent : P (Option String) := do
  match ← peek with
  | some (.ident s) => advance; return some s
  | _ => return none

/-- An `emit`/`revert` target: a path. -/
def pathExpr : P (Syn .expr) := do
  let p ← idPath
  return p.tail.foldl .member (.ident p.head)

def yulPathParts : P (List String) := do
  let h ← ident
  let t ← many do
    if ← eat (.punct .period) then return some (← ident) else return none
  return h :: t

def overrideSpec : P (Option (List IdPath)) := do
  if ← eat (.kw .override) then
    if ← eat (.punct .lparen) then
      let ps ← sepBy1 idPath
      expectP .rparen
      return some ps
    else return some []
  else return none

/-- One attribute of an attribute run: its slot and its tokens' meaning. -/
inductive Attr where
  | vis (v : Visibility)
  | mutA (m : Mutability)
  | virt
  | over (ps : List IdPath)
  | modInv (m : Syn .modInv)
  | payable
  | ext

def Attr.slot : Attr → Slot
  | .vis _ => .vis | .mutA _ => .mutab | .virt => .virt | .over _ => .over
  | .modInv _ => .modInv | .payable => .payable | .ext => .ext


mutual

/-- `typeName`. -/
def typeName : Nat → P (Syn .typeName)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    let base ← match ← peek with
      | some (.elem _) => do pure (Syn.elem (← elemTypeName))
      | some (.kw .function) => fnType n
      | some (.kw .mapping) => mappingType n
      | some (.ident _) => do pure (Syn.userType (← idPath))
      | _ => P.fail "expected a type name"
    typeSuffix n base

def typeSuffix : Nat → Syn .typeName → P (Syn .typeName)
  | 0, _ => P.fail "nesting too deep"
  | n + 1, base => do
    if ← eat (.punct .lbrack) then
      if ← eat (.punct .rbrack) then typeSuffix n (.array base .none)
      else
        let e ← expr n
        expectP .rbrack
        typeSuffix n (.array base (.some e))
    else return base

def fnType : Nat → P (Syn .typeName)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    expect (.kw .function) "'function'"
    let (ps, cps) ← capture (paramsParen n)
    let (vis, mu, order) ← fnTypeAttrs 3 none none []
    record [.attrs order]
    record cps
    let rets ← returnsOpt n
    return .fnType ps vis mu rets

def mappingType : Nat → P (Syn .typeName)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    expect (.kw .mapping) "'mapping'"
    expectP .lparen
    let key ← match ← peek with
      | some (.elem e) => do
        advance
        if h : e = .addressPayable then P.fail "payable mapping key" else pure (MapKey.elem e h)
      | some (.ident _) => do pure (MapKey.path (← idPath))
      | _ => P.fail "expected a mapping key type"
    let kn ← optIdent
    expectP .doubleArrow
    let v ← typeName n
    let vn ← optIdent
    expectP .rparen
    return .mapping key kn v vn

/-- `(parameterList?)`. -/
def paramsParen : Nat → P (Syn (.list .param))
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    expectP .lparen
    if ← eat (.punct .rparen) then return .nil
    let ps ← sepBy1 (param n)
    expectP .rparen
    return toSynList ps

def param : Nat → P (Syn .param)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    let t ← typeName n
    let loc ← do match ← peek with
      | some tk => match locOf tk with
        | some l => advance; pure (some l)
        | none => pure none
      | none => pure none
    let name ← optIdent
    return .param t loc name

/-- `(returns (parameterList))?`. -/
def returnsOpt : Nat → P (Syn (.list .param))
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    if ← eat (.kw .returns) then
      let ps ← paramsParen n
      match ps with
      | .nil => P.fail "empty returns list"
      | _ => return ps
    else return .nil

-- Expressions

/-- `expression`: a binary expression, then an assignment or a
conditional (solc's `parseExpression`). -/
def expr : Nat → P (Syn .expr)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    let lhs ← binary n 2
    match ← peek with
    | some t =>
      match assignOf t with
      | some op => do advance; return .assign op lhs (← expr n)
      | none =>
        if t == .punct .question then
          advance
          let a ← expr n
          expectP .colon
          let b ← expr n
          return .cond lhs a b
        else return lhs
    | none => return lhs

/-- Precedence climbing from level `p`. -/
def binary : Nat → Nat → P (Syn .expr)
  | 0, _ => P.fail "nesting too deep"
  | n + 1, p => do
    let lhs ← unary n
    binLoop n p lhs

def binLoop : Nat → Nat → Syn .expr → P (Syn .expr)
  | 0, _, _ => P.fail "nesting too deep"
  | n + 1, p, lhs => do
    match ← peek with
    | some t =>
      match binOf t with
      | some (q, mk) =>
        if p ≤ q then
          advance
          let rhs ← binary n (if q == 12 then 12 else q + 1)
          binLoop n p (mk lhs rhs)
        else return lhs
      | none => return lhs
    | none => return lhs

def unary : Nat → P (Syn .expr)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    match ← peek with
    | some t =>
      match prefixOf t with
      | some op => do advance; return .unaryPrefix op (← unary n)
      | none => postfixE n
    | none => postfixE n

def postfixE : Nat → P (Syn .expr)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    let e ← primary n
    postLoop n e

def postLoop : Nat → Syn .expr → P (Syn .expr)
  | 0, _ => P.fail "nesting too deep"
  | n + 1, e => do
    match ← peek with
    | some (.punct .lbrack) =>
      advance
      if ← eat (.punct .rbrack) then postLoop n (.index e .none)
      else if ← eat (.punct .colon) then
        let j ← optExprBefore n .rbrack
        expectP .rbrack
        postLoop n (.slice e .none j)
      else
        let i ← expr n
        if ← eat (.punct .colon) then
          let j ← optExprBefore n .rbrack
          expectP .rbrack
          postLoop n (.slice e (.some i) j)
        else
          expectP .rbrack
          postLoop n (.index e (.some i))
    | some (.punct .period) =>
      advance
      match ← peek with
      | some (.ident s) => advance; postLoop n (.member e s)
      | some (.elem .address) => advance; postLoop n (.member e "address")
      | _ => P.fail "expected a member name"
    | some (.punct .lbrace) =>
      if (← peekN 2) == some (.punct .colon) then
        match ← peekN 1 with
        | some (.ident _) =>
          advance
          let as ← sepBy1 (namedArg n)
          expectP .rbrace
          match as with
          | a :: rest => postLoop n (.callOptions e a (toSynList rest))
          | [] => P.fail "empty call options"
        | _ => return e
      else return e
    | some (.punct .lparen) => do postLoop n (.call e (← callArgs n))
    | some (.punct .inc) => advance; postLoop n (.unarySuffix .inc e)
    | some (.punct .dec) => advance; postLoop n (.unarySuffix .dec e)
    | _ => return e

/-- An optional expression, absent when `stop` is next. -/
def optExprBefore : Nat → Punct → P (Syn (.opt .expr))
  | 0, _ => P.fail "nesting too deep"
  | n + 1, stop => do
    if ← isP stop then return .none else return .some (← expr n)

def namedArg : Nat → P (Syn .namedArg)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    let name ← ident
    expectP .colon
    return .namedArg name (← expr n)

/-- `callArgumentList`. -/
def callArgs : Nat → P (Syn .callArgs)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    expectP .lparen
    if ← eat (.punct .lbrace) then
      if ← eat (.punct .rbrace) then
        expectP .rparen
        return .named .nil
      let as ← sepBy1 (namedArg n)
      expectP .rbrace
      expectP .rparen
      return .named (toSynList as)
    else if ← eat (.punct .rparen) then return .positional .nil
    else
      let es ← sepBy1 (expr n)
      expectP .rparen
      return .positional (toSynList es)

def primary : Nat → P (Syn .expr)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    match ← peek with
    | some (.ident s) => advance; return .ident s
    | some (.num v) =>
      advance
      match ← peek with
      | some (.denom d) => advance; return .litUnit v d
      | _ => return .lit (.num v)
    | some (.bool b) => advance; return .lit (.bool b)
    | some (.str _) =>
      let fs ← fragments fun | .str b => some b | _ => none
      record [.frags (fs.map List.length)]
      return .lit (.str fs.flatten)
    | some (.hexStr _) =>
      let fs ← fragments fun | .hexStr b => some b | _ => none
      record [.frags (fs.map List.length)]
      return .lit (.hexStr fs.flatten)
    | some (.unicodeStr _) =>
      let fs ← fragments fun | .unicodeStr b => some b | _ => none
      record [.frags (fs.map List.length)]
      return .lit (.unicodeStr fs.flatten)
    | some (.elem e) =>
      advance
      if h : e = .addressPayable then P.fail "unexpected type" else return .elemType e h
    | some (.kw .payable) => do advance; return .payableConv (← callArgs n)
    | some (.kw .type_) =>
      advance
      expectP .lparen
      let t ← typeName n
      expectP .rparen
      -- solc reads `type(…)`'s argument as an expression: no `address
      -- payable`, mapping or function type.
      match t with
      | .elem .addressPayable | .mapping .. | .fnType .. => P.fail "expected a type expression"
      | _ => return .metaType t
    | some (.kw .new) => do advance; return .new (← typeName n)
    | some (.punct .lparen) =>
      advance
      let first ← tupleComp n
      let rest ← many do
        if ← eat (.punct .comma) then return some (← tupleComp n) else return none
      expectP .rparen
      return .tuple first (toSynList rest)
    | some (.punct .lbrack) =>
      advance
      -- `[]`: solc's parser accepts it (a type error later), the grammar does
      -- not; refused (`sepBy1` needs an element).
      let es ← sepBy1 (expr n)
      expectP .rbrack
      match es with
      | e :: rest => return .inlineArray e (toSynList rest)
      | [] => P.fail "expected an expression"
    | _ => P.fail "expected an expression"

/-- A tuple component: absent before `,` or `)`. -/
def tupleComp : Nat → P (Syn (.opt .expr))
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    if (← isP .comma) || (← isP .rparen) then return .none else return .some (← expr n)

-- Statements

def varDecl : Nat → P (Syn .varDecl)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    let t ← typeName n
    let loc ← do match ← peek with
      | some tk => match locOf tk with
        | some l => advance; pure (some l)
        | none => pure none
      | none => pure none
    return .varDecl t loc (← ident)

/-- A declaration head: a type name followed by a location or a name. -/
def declHead : Nat → P (Syn .varDecl)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    let t ← typeName n
    match ← peek with
    | some (.ident s) => advance; return .varDecl t none s
    | some tk => match locOf tk with
      | some l => advance; return .varDecl t (some l) (← ident)
      | none => P.fail "not a declaration"
    | none => P.fail "not a declaration"

/-- A tuple declaration `( , T x, , U y) = e`. -/
def declTuple : Nat → P (Syn .simple)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    expectP .lparen
    let holes ← many do return if ← eat (.punct .comma) then some () else none
    let d ← declHead n
    let rest ← many do
      if ← eat (.punct .comma) then
        if (← isP .comma) || (← isP .rparen) then return some Option.none
        else return some (some (← varDecl n))
      else return none
    expectP .rparen
    expectP .assign
    let e ← expr n
    return .declTuple holes.length d (toSynList (rest.map toSynOpt)) e

/-- `simpleStatement` without its `;`. -/
def simple : Nat → P (Syn .simple)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    if ← isP .lparen then
      match ← attempt (declTuple n) with
      | some s => return s
      | none =>
        let e ← expr n
        -- solc's statement parser needs an expression among a leading
        -- tuple's components (`() = f();` is a ParserError there).
        match e with
        | .tuple .none rest | .assign _ (.tuple .none rest) _ =>
          if allNone rest then P.fail "expected a primary expression" else return .exprStmt e
        | _ => return .exprStmt e
    else
      match ← attempt (declHead n) with
      | some d =>
        if ← eat (.punct .assign) then return .declVar d (.some (← expr n))
        else return .declVar d .none
      | none => return .exprStmt (← expr n)

def stmt : Nat → (k : SCtx) → P (Syn (.stmt k))
  | 0, _ => P.fail "nesting too deep"
  | n + 1, k => do
    match ← peek with
    | some (.punct .lbrace) => do return .blockStmt (← block n k)
    | some (.kw .if_) =>
      advance
      expectP .lparen
      let c ← expr n
      expectP .rparen
      let t ← stmt n k
      if ← eat (.kw .else_) then return .ifStmt c t (.some (← stmt n k))
      else return .ifStmt c t .none
    | some (.kw .for_) =>
      advance
      expectP .lparen
      let i ← if ← eat (.punct .semi) then pure Syn.none else do
        let s ← simple n
        expectP .semi
        pure (Syn.some s)
      let c ← optExprBefore n .semi
      expectP .semi
      let u ← optExprBefore n .rparen
      expectP .rparen
      match k with
      | ⟨l, uc⟩ => do return Syn.forStmt (l := l) i c u (← stmt n ⟨true, uc⟩)
    | some (.kw .while_) =>
      advance
      expectP .lparen
      let c ← expr n
      expectP .rparen
      match k with
      | ⟨l, uc⟩ => do return Syn.whileStmt (l := l) c (← stmt n ⟨true, uc⟩)
    | some (.kw .do_) =>
      advance
      match k with
      | ⟨l, uc⟩ => do
        let b ← stmt n ⟨true, uc⟩
        expect (.kw .while_) "'while'"
        expectP .lparen
        let c ← expr n
        expectP .rparen
        expectP .semi
        return Syn.doWhile (l := l) b c
    | some (.kw .continue_) =>
      match k with
      | ⟨true, _⟩ => do advance; expectP .semi; return .continueStmt
      | ⟨false, _⟩ => P.fail "continue outside a loop"
    | some (.kw .break_) =>
      match k with
      | ⟨true, _⟩ => do advance; expectP .semi; return .breakStmt
      | ⟨false, _⟩ => P.fail "break outside a loop"
    | some (.kw .try_) =>
      advance
      let e ← expr n
      let rets ← returnsOpt n
      let b ← block n k
      let cs ← many do
        if ← isK .catch_ then return some (← catchClause n k) else return none
      match cs with
      | c :: rest => return .tryStmt e rets b c (toSynList rest)
      | [] => P.fail "expected a catch clause"
    | some (.kw .return_) =>
      advance
      let e ← optExprBefore n .semi
      expectP .semi
      return .returnStmt e
    | some (.kw .emit) =>
      advance
      let e ← pathExpr
      let a ← callArgs n
      expectP .semi
      return .emit e a
    | some (.ident "revert") =>
      match ← peekN 1 with
      | some (.ident _) =>
        advance
        let e ← pathExpr
        let a ← callArgs n
        expectP .semi
        return .revert e a
      | _ => simpleStmt n k
    | some (.kw .assembly) =>
      advance
      let evm ← match ← peek with
        | some (.str b) => if b == ascii "evmasm" then do advance; pure true else pure false
        | _ => pure false
      let flags ← if ← eat (.punct .lparen) then do
          let fs ← sepBy1 (strArg "assembly flag")
          expectP .rparen
          pure fs
        else pure []
      return .assembly evm flags (← yulBody n)
    | _ => simpleStmt n k

def simpleStmt : Nat → (k : SCtx) → P (Syn (.stmt k))
  | 0, _ => P.fail "nesting too deep"
  | n + 1, _ => do
    let s ← simple n
    expectP .semi
    return .simpleStmt s

def catchClause : Nat → (k : SCtx) → P (Syn (.catchClause k))
  | 0, _ => P.fail "nesting too deep"
  | n + 1, k => do
    expect (.kw .catch_) "'catch'"
    if ← isP .lbrace then return .catchPlain (← block n k)
    let name ← optIdent
    let ps ← paramsParen n
    match ps with
    | .cons p rest => return .catchSig name p rest (← block n k)
    | .nil => P.fail "empty catch parameters"

def block : Nat → (k : SCtx) → P (Syn (.block k))
  | 0, _ => P.fail "nesting too deep"
  | n + 1, k => do
    expectP .lbrace
    let items ← many do
      if ← isP .rbrace then return none
      match ← peek with
      | none => return none
      | _ => return some (← item n k)
    expectP .rbrace
    return .block (toSynList items)

def item : Nat → (k : SCtx) → P (Syn (.item k))
  | 0, _ => P.fail "nesting too deep"
  | n + 1, k => do
    if ← isK .unchecked then
      match k with
      | ⟨l, false⟩ => do advance; return .uncheckedItem (← block n ⟨l, true⟩)
      | ⟨_, true⟩ => P.fail "nested unchecked block"
    else return .stmtItem (← stmt n k)

-- Yul

/-- `{ yulStatement* }`. -/
def yulBody : Nat → P (Syn (.list .yulStmt))
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    expectP .lbrace
    let ss ← many do
      if (← isP .rbrace) || (← peek).isNone then return none
      return some (← yulStmt n)
    expectP .rbrace
    return toSynList ss

def yulExpr : Nat → P (Syn .yulExpr)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    match ← peek with
    | some (.ident _) =>
      let p ← yulPathParts
      match p with
      | [f] =>
        if ← eat (.punct .lparen) then
          if ← eat (.punct .rparen) then return .yulCall f .nil
          let as ← sepBy1 (yulExpr n)
          expectP .rparen
          return .yulCall f (toSynList as)
        else return .yulPath f []
      | h :: t => return .yulPath h t
      | [] => P.fail "expected a Yul path"
    | some t =>
      match yulLitOf t with
      | some l => advance; return .yulLit l
      | none => P.fail "expected a Yul expression"
    | none => P.fail "expected a Yul expression"

def yulStmt : Nat → P (Syn .yulStmt)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    match ← peek with
    | some (.punct .lbrace) => do return .yulBlock (← yulBody n)
    | some (.yulKw .let_) =>
      advance
      let vs ← identList
      match vs with
      | v :: rest =>
        if ← eat (.punct .yulAssign) then return .yulLet v rest (.some (← yulExpr n))
        else return .yulLet v rest .none
      | [] => P.fail "expected a Yul variable"
    | some (.yulKw .if_) =>
      advance
      let c ← yulExpr n
      return .yulIf c (← yulBody n)
    | some (.yulKw .for_) =>
      advance
      let i ← yulBody n
      let c ← yulExpr n
      let p ← yulBody n
      return .yulFor i c p (← yulBody n)
    | some (.yulKw .switch) =>
      advance
      let e ← yulExpr n
      let cs ← many do
        if ← eat (.yulKw .case) then
          match ← peek with
          | some t => match yulLitOf t with
            | some l => do advance; return some (Syn.yulCase l (← yulBody n))
            | none => P.fail "expected a Yul literal"
          | none => P.fail "expected a Yul literal"
        else return none
      if ← eat (.yulKw .default) then return .yulSwitch e (toSynList cs) (.some (← yulBody n))
      else return .yulSwitch e (toSynList cs) .none
    | some (.yulKw .function) =>
      advance
      let name ← ident
      expectP .lparen
      let args ← if ← isP .rparen then pure [] else identList
      expectP .rparen
      let rets ← if ← eat (.punct .rightArrow) then identList else pure []
      return .yulFun name args rets (← yulBody n)
    | some (.yulKw .leave) => advance; return .yulLeave
    | some (.yulKw .break_) => advance; return .yulBreak
    | some (.yulKw .continue_) => advance; return .yulContinue
    | some (.ident _) =>
      if (← peekN 1) == some (.punct .lparen) then return .yulExprStmt (← yulExpr n)
      let p ← yulPathParts
      let ps ← many do
        if ← eat (.punct .comma) then return some (← yulPathParts) else return none
      if ← eat (.punct .yulAssign) then return .yulAssign p ps (← yulExpr n)
      else match p, ps with
        | h :: t, [] => return .yulExprStmt (.yulPath h t)
        | _, _ => P.fail "expected ':='"
    | _ => do return .yulExprStmt (← yulExpr n)

-- Definitions

def modInv : Nat → P (Syn .modInv)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    let p ← idPath
    if ← isP .lparen then
      -- solc's parser takes positional arguments only here.
      match ← callArgs n with
      | .named _ => P.fail "expected a primary expression"
      | args => return .modInv p (.some args)
    else return .modInv p .none

/-- The body of a function-like definition: `;` or a block. -/
def bodyOpt : Nat → P (Syn (.opt (.block .body)))
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    if ← eat (.punct .semi) then return .none else return .some (← block n .body)

/-- An attribute run of a function-like definition.  `allowed` says which
keyword attributes this definition takes. -/
def attrRun : Nat → (Tok → Option Attr) → P (List Attr)
  | 0, _ => P.fail "nesting too deep"
  | n + 1, allowed => many do
    match ← peek with
    | some (.kw .override) =>
      match ← overrideSpec with
      | some ps => return some (Attr.over ps)
      | none => return none
    | some (.kw .virtual) => advance; return some .virt
    | some (.ident _) => do return some (Attr.modInv (← modInv n))
    | some t => match allowed t with
      | some a => advance; return some a
      | none => return none
    | none => return none

def functionDef : Nat → (t : Bool) → P (Syn (.part t))
  | 0, _ => P.fail "nesting too deep"
  | n + 1, _ => do
    expect (.kw .function) "'function'"
    let name ← match ← peek with
      | some (.ident s) => do advance; pure (FnName.ident s)
      | some (.kw .fallback) => do advance; pure FnName.fallback
      | some (.kw .receive) => do advance; pure FnName.receive
      | _ => P.fail "expected a function name"
    let (ps, cps) ← capture (paramsParen n)
    let (as, cas) ← capture (attrRun n fun t => match visOf t, mutOf t with
      | some v, _ => some (.vis v) | _, some m => some (.mutA m) | _, _ => none)
    let vis := as.filterMap fun | .vis v => some v | _ => none
    let mu := as.filterMap fun | .mutA m => some m | _ => none
    let virt := as.filter fun | .virt => true | _ => false
    let over := as.filterMap fun | .over p => some p | _ => none
    let mods := as.filterMap fun | .modInv m => some m | _ => none
    if vis.length > 1 || mu.length > 1 || virt.length > 1 || over.length > 1 then
      P.fail "repeated function attribute"
    else
      record [.attrs (as.map Attr.slot)]
      record cps
      record cas
      let rets ← returnsOpt n
      let body ← bodyOpt n
      return .function name ps vis.head? mu.head? (toSynList mods) (!virt.isEmpty) over.head?
        rets body

def eventParam : Nat → P (Syn .eventParam)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    let t ← typeName n
    let idx ← eat (.kw .indexed)
    return .eventParam t idx (← optIdent)

def errorParam : Nat → P (Syn .errorParam)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    let t ← typeName n
    return .errorParam t (← optIdent)

def structMember : Nat → P (Syn .structMember)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    let t ← typeName n
    let name ← ident
    expectP .semi
    return .structMember t name

/-- The definitions allowed in a contract and at file level. -/
def sharedPart : Nat → (t : Bool) → P (Option (Syn (.part t)))
  | 0, _ => P.fail "nesting too deep"
  | n + 1, t => do
    match ← peek with
    | some (.kw .function) =>
      -- `function (` begins a function type (a state variable or constant).
      if (← peekN 1) == some (.punct .lparen) then return none
      return some (← functionDef n t)
    | some (.kw .struct) =>
      advance
      let name ← ident
      expectP .lbrace
      let ms ← many do
        if ← isP .rbrace then return none else return some (← structMember n)
      expectP .rbrace
      match ms with
      | m :: rest => return some (.struct name m (toSynList rest))
      | [] => P.fail "empty struct"
    | some (.kw .enum) =>
      advance
      let name ← ident
      expectP .lbrace
      let vs ← sepBy1 ident
      expectP .rbrace
      match vs with
      | v :: rest => return some (.enum name v rest)
      | [] => P.fail "empty enum"
    | some (.kw .type_) =>
      advance
      let name ← ident
      expect (.kw .is) "'is'"
      let e ← elemTypeName
      expectP .semi
      return some (.udvt name e)
    | some (.kw .event) =>
      advance
      let name ← ident
      expectP .lparen
      let ps ← if ← isP .rparen then pure [] else sepBy1 (eventParam n)
      expectP .rparen
      let anon ← eat (.kw .anonymous)
      expectP .semi
      return some (.event name (toSynList ps) anon)
    | some (.ident "error") =>
      match ← peekN 1, ← peekN 2 with
      | some (.ident _), some (.punct .lparen) =>
        advance
        let name ← ident
        expectP .lparen
        let ps ← if ← isP .rparen then pure [] else sepBy1 (errorParam n)
        expectP .rparen
        expectP .semi
        return some (.error name (toSynList ps))
      | _, _ => return none
    | some (.kw .using) =>
      advance
      let u ← if ← eat (.punct .lbrace) then do
          let as ← sepBy1 do
            let p ← idPath
            if ← eat (.kw .as_) then
              match ← peek with
              | some tk => match userOpOf tk with
                | some o => advance; pure (Syn.usingAlias p (some o))
                | none => P.fail "expected a user-definable operator"
              | none => P.fail "expected a user-definable operator"
            else pure (Syn.usingAlias p none)
          expectP .rbrace
          expect (.kw .for_) "'for'"
          let ty ← if ← eat (.punct .mul) then pure Syn.none else do pure (Syn.some (← typeName n))
          let glob ← eat (.ident "global")
          match as with
          | a :: rest => pure (Syn.usingAliases a (toSynList rest) ty glob)
          | [] => P.fail "empty using list"
        else do
          let p ← idPath
          expect (.kw .for_) "'for'"
          let ty ← if ← eat (.punct .mul) then pure Syn.none else do pure (Syn.some (← typeName n))
          let glob ← eat (.ident "global")
          pure (Syn.usingPath p ty glob)
      expectP .semi
      return some (.usingPart u)
    | _ => return none

/-- A `contractBodyElement`. -/
def contractPart : Nat → P (Syn (.part false))
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    match ← sharedPart n false with
    | some p => return p
    | none => contractPart' n

def contractPart' : Nat → P (Syn (.part false))
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    match ← peek with
    | some (.kw .constructor) =>
      advance
      let (ps, cps) ← capture (paramsParen n)
      let (as, cas) ← capture (attrRun n fun
        | .kw .payable => some .payable | .kw .internal => some (.vis .internal)
        | .kw .public_ => some (.vis .pub) | _ => none)
      let vis := as.filterMap fun
        | .vis .internal => some CtorVis.internal | .vis _ => some CtorVis.pub | _ => none
      let pay := as.filter fun | .payable => true | _ => false
      if vis.length > 1 || pay.length > 1 ||
          as.any (fun | .virt => true | .over _ => true | _ => false) then
        P.fail "invalid constructor attribute"
      else
        record [.attrs (as.map Attr.slot)]
        record cps
        record cas
        let mods := as.filterMap fun | .modInv m => some m | _ => none
        return .constructor ps (toSynList mods) (!pay.isEmpty) vis.head? (← block n .body)
    | some (.kw .modifier) =>
      advance
      let name ← ident
      let (ps, cps) ← capture do
        if ← isP .lparen then pure (Syn.some (← paramsParen n)) else pure Syn.none
      let as ← many do
        match ← peek with
        | some (.kw .virtual) => advance; return some Attr.virt
        | some (.kw .override) =>
          match ← overrideSpec with
          | some p => return some (Attr.over p)
          | none => return none
        | _ => return none
      let virt := as.filter fun | .virt => true | _ => false
      let over := as.filterMap fun | .over p => some p | _ => none
      if virt.length > 1 || over.length > 1 then P.fail "repeated modifier attribute"
      else
        record [.attrs (as.map Attr.slot)]
        record cps
        return .modifier name ps (!virt.isEmpty) over.head? (← bodyOpt n)
    | some (.kw .fallback) =>
      advance
      let (ps, cps) ← capture (paramsParen n)
      let (as, cas) ← capture (attrRun n fun t => match mutOf t with
        | some m => some (.mutA m)
        | none => if t == .kw .external then some .ext else none)
      let (rets, crs) ← capture (returnsOpt n)
      let ext := as.filter fun | .ext => true | _ => false
      let mu := as.filterMap fun | .mutA m => some m | _ => none
      let virt := as.filter fun | .virt => true | _ => false
      let over := as.filterMap fun | .over p => some p | _ => none
      let mods := as.filterMap fun | .modInv m => some m | _ => none
      if ext.length > 1 || mu.length > 1 || virt.length > 1 || over.length > 1 then
        P.fail "repeated fallback attribute"
      else
        let sig ← match ps, rets with
          | .nil, .nil => pure Syn.fbNoParams
          | .cons p rest, r => pure (Syn.fbParams p rest r)
          | .nil, _ => P.fail "fallback without parameters has no returns"
        record [.attrs (as.map Attr.slot)]
        record cps
        record crs
        record cas
        return .fallback sig (!ext.isEmpty) mu.head? (toSynList mods) (!virt.isEmpty) over.head?
          (← bodyOpt n)
    | some (.kw .receive) =>
      advance
      expectP .lparen
      expectP .rparen
      let (as, cas) ← capture (attrRun n fun
        | .kw .payable => some .payable | .kw .external => some .ext | _ => none)
      let ext := as.filter fun | .ext => true | _ => false
      let pay := as.filter fun | .payable => true | _ => false
      let virt := as.filter fun | .virt => true | _ => false
      let over := as.filterMap fun | .over p => some p | _ => none
      let mods := as.filterMap fun | .modInv m => some m | _ => none
      if ext.length > 1 || pay.length > 1 || virt.length > 1 || over.length > 1 then
        P.fail "repeated receive attribute"
      else
        record [.attrs (as.map Attr.slot)]
        record cas
        return .receive (!ext.isEmpty) (!pay.isEmpty) (toSynList mods) (!virt.isEmpty) over.head?
          (← bodyOpt n)
    | _ =>
      -- A state variable.
      let (ty, cty) ← capture (typeName n)
      let as ← many do
        match ← peek with
        | some (.kw .public_) => advance; return some (Slot.vis, Sum.inl StateVis.pub)
        | some (.kw .private_) => advance; return some (Slot.vis, Sum.inl StateVis.priv)
        | some (.kw .internal) => advance; return some (Slot.vis, Sum.inl StateVis.internal)
        | some (.kw .constant) => advance; return some (Slot.const, Sum.inr (Sum.inl Constness.constant))
        | some (.kw .immutable) => advance; return some (Slot.const, Sum.inr (Sum.inl Constness.immutable))
        | some (.kw .override) =>
          match ← overrideSpec with
          | some p => return some (Slot.over, Sum.inr (Sum.inr (some p)))
          | none => return none
        | some (.ident "transient") =>
          match ← peekN 1 with
          | some (.punct .semi) | some (.punct .assign) => return none
          | _ => advance; return some (Slot.transient, Sum.inr (Sum.inr none))
        | _ => return none
      let vis := as.filterMap fun | (_, .inl v) => some v | _ => none
      let const := as.filterMap fun | (_, .inr (.inl c)) => some c | _ => none
      let over := as.filterMap fun | (_, .inr (.inr (some p))) => some p | _ => none
      let trans := as.filter fun | (.transient, _) => true | _ => false
      if vis.length > 1 || const.length > 1 || over.length > 1 || trans.length > 1 then
        P.fail "repeated state variable attribute"
      else
        let name ← ident
        record [.attrs (as.map (·.1))]
        record cty
        let init ← if ← eat (.punct .assign) then pure (Syn.some (← expr n)) else pure Syn.none
        expectP .semi
        return .stateVar ty vis.head? const.head? over.head? (!trans.isEmpty) name init

/-- `{ contractBodyElement* }`. -/
def contractBody : Nat → P (Syn (.list (.part false)))
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    expectP .lbrace
    let ps ← many do
      if (← isP .rbrace) || (← peek).isNone then return none
      return some (← contractPart n)
    expectP .rbrace
    return toSynList ps

def inheritList : Nat → P (Syn (.list .inherit))
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    let is ← sepBy1 do
      let p ← idPath
      if ← isP .lparen then
        match ← callArgs n with
        | .named _ => P.fail "expected a primary expression"
        | args => pure (Syn.inherit p (.some args))
      else pure (Syn.inherit p .none)
    return toSynList is

/-- A `sourceUnit` element. -/
def topLevel : Nat → P (Syn .top)
  | 0 => P.fail "nesting too deep"
  | n + 1 => do
    match ← peek with
    | some (.kw .pragma) =>
      advance
      let ws ← many do
        match ← peek with
        | some (.pragmaWord w) => advance; return some w
        | _ => return none
      expectP .semi
      return .pragma ws
    | some (.kw .import_) =>
      advance
      match ← peek with
      | some (.punct .mul) =>
        advance
        expect (.kw .as_) "'as'"
        let a ← ident
        expect (.ident "from") "'from'"
        let p ← strArg "import path"
        expectP .semi
        return .importStar a p
      | some (.punct .lbrace) =>
        advance
        let as ← sepBy1 do
          let s ← ident
          if ← eat (.kw .as_) then pure (Syn.importAlias s (some (← ident)))
          else pure (Syn.importAlias s none)
        expectP .rbrace
        expect (.ident "from") "'from'"
        let p ← strArg "import path"
        expectP .semi
        match as with
        | a :: rest => return .importSymbols a (toSynList rest) p
        | [] => P.fail "empty import list"
      | _ =>
        let p ← strArg "import path"
        let a ← if ← eat (.kw .as_) then pure (some (← ident)) else pure none
        expectP .semi
        return .importPath p a
    | some (.kw .abstract) | some (.kw .contract) =>
      let abs ← eat (.kw .abstract)
      expect (.kw .contract) "'contract'"
      let name ← ident
      let hdr ← many do
        if (← peek) == some (.ident "layout") then
          advance
          expect (.ident "at") "'at'"
          let (e, ce) ← capture (expr n)
          return some (Sum.inl (e, ce))
        else if ← eat (.kw .is) then
          let (i, ci) ← capture (inheritList n)
          return some (Sum.inr (i, ci))
        else return none
      let lays := hdr.filterMap fun | .inl x => some x | _ => none
      let inhs := hdr.filterMap fun | .inr x => some x | _ => none
      if lays.length > 1 || inhs.length > 1 then P.fail "repeated contract header"
      else
        match lays, inhs with
        | [_], [_] => record [.layoutFirst (hdr.head?.map (fun | .inl _ => true | _ => false) |>.getD true)]
        | _, _ => pure ()
        record (lays.flatMap (·.2))
        record (inhs.flatMap (·.2))
        let lay := match lays with | (e, _) :: _ => Syn.some e | [] => Syn.none
        let inh := match inhs with | (i, _) :: _ => i | [] => Syn.nil
        return .contract abs name lay inh (← contractBody n)
    | some (.kw .interface) =>
      advance
      let name ← ident
      let inh ← if ← eat (.kw .is) then inheritList n else pure Syn.nil
      return .interface name inh (← contractBody n)
    | some (.kw .library) =>
      advance
      let name ← ident
      return .library name (← contractBody n)
    | _ =>
      match ← sharedPart n true with
      | some p => return .topPart p
      | none =>
        let t ← typeName n
        expect (.kw .constant) "'constant'"
        let name ← ident
        expectP .assign
        let e ← expr n
        expectP .semi
        return .topPart (.constant t name e)

end

/-- `sourceUnit`: every token. -/
def sourceUnit (fuel : Nat) : P (Syn .unit) := do
  let tops ← many do
    if (← peek).isNone then return none else return some (← topLevel fuel)
  return .unit (toSynList tops)

/-- **The parser**: the tree and the layout it read, or a located error. -/
def parseTokens (eof : Nat) (ts : List Located) : Except Error (Syn .unit × List Choice) :=
  match sourceUnit (16 * (ts.length + 1)) ⟨ts, [], eof⟩ with
  | .ok (u, s) => .ok (u, s.ch.reverse)
  | .error e => .error e

end Solidity.Frontend.Checked
