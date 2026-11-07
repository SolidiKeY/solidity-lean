import Solidity.SolcValidation.IrSyntax

/-!
# Certifying parser for solc's object-dialect Yul text

`lex` turns IR text into tokens (comments, including solc's `/// @src` and
`/** @src */` annotations, are dropped). `parse` builds the intrinsic tree of
`SolcValidation/IrSyntax.lean`: names are resolved to memberships, function
groups are hoisted over their block, arities are checked, misplaced
`leave`/`break`/`continue` are unrepresentable. The parser itself is not
trusted: a result is returned only together with the proofs that printing the
tree reproduces exactly the lexed token stream and that the tree passes the
scoping and static checks `objectWf` (`Parsed.sound`).

The trusted boundary is the lexer, the printer and `objectWf`, all short
structural functions. Numeric spellings are compared by value (`0x80` and `128` lex
alike); comments and whitespace are not part of the provenance. Object data
must be a `hex"…"` literal (what solc 0.8.38 emits); a plain-string data
section is refused. Refused although solc accepts them: single-quoted strings,
unescaped non-ASCII characters, hex literals as expressions, `_` in numbers.
Object names and operation labels are compared by their raw text (escapes are
not decoded); whether a label exists is checked when it is evaluated.
This tree is evaluated by compiled code, not by the kernel on a hot path:
Gate G0's conditions (recursor forms, names out of the index) are not applied;
the kernel controls run on inputs of a few dozen tokens.
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

/-! ## Lexer -/

def isIdStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'
def isIdChar (c : Char) : Bool := isIdStart c || c.isDigit || c == '.'

/-- Raw string body up to the closing quote; escapes are kept verbatim. -/
def lexString : List Char → List Char → Option (String × List Char)
  | acc, '"' :: rest => some (String.mk acc.reverse, rest)
  | acc, '\\' :: c :: rest => lexString (c :: '\\' :: acc) rest
  | _, '\n' :: _ => none
  | acc, c :: rest => lexString (c :: acc) rest
  | _, [] => none

/-- Bytes of a `hex"…"` body: an even number of hex digits. -/
def lexHex : List Char → List (Fin 256) → Option (List (Fin 256) × List Char)
  | '"' :: rest, acc => some (acc.reverse, rest)
  | h :: l :: rest, acc => do
      let hi ← hexDigit? h
      let lo ← hexDigit? l
      let b ← toByte? (hi * 16 + lo)
      lexHex rest (b :: acc)
  | _, _ => none

def dropLine : List Char → List Char
  | [] => []
  | '\n' :: rest => rest
  | _ :: rest => dropLine rest

def dropBlock : List Char → Option (List Char)
  | '*' :: '/' :: rest => some rest
  | _ :: rest => dropBlock rest
  | [] => none

def decValue (digits : List Char) : Nat :=
  digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def hexValue (digits : List Char) : Option Nat :=
  digits.foldlM (fun acc c => (fun d => acc * 16 + d) <$> hexDigit? c) 0

/-- A number literal: `0x` followed by hex digits, or decimal digits; it may
not run into an identifier character. -/
def lexNumber (c : Char) (cs : List Char) : Option (Nat × List Char) :=
  match c, cs with
  | '0', 'x' :: rest =>
      let (digits, after) := rest.span (fun d => (hexDigit? d).isSome)
      if digits.isEmpty || (after.head?.map isIdChar).getD false then none
      else (fun v => (v, after)) <$> hexValue digits
  | _, _ =>
      let (digits, after) := (c :: cs).span Char.isDigit
      if (after.head?.map isIdChar).getD false || (c == '0' && digits.length > 1) then none
      else some (decValue digits, after)

/-- Each step consumes at least one character, so `length + 1` fuel suffices. -/
def lexGo : Nat → List Char → List Tok → Option (List Tok)
  | 0, _, _ => none
  | _ + 1, [], acc => some acc.reverse
  | fuel + 1, c :: cs, acc =>
      if c.isWhitespace then lexGo fuel cs acc else
      match c, cs with
      | '/', '/' :: rest => lexGo fuel (dropLine rest) acc
      | '/', '*' :: rest => dropBlock rest >>= fun r => lexGo fuel r acc
      | '{', _ => lexGo fuel cs (.lbrace :: acc)
      | '}', _ => lexGo fuel cs (.rbrace :: acc)
      | '(', _ => lexGo fuel cs (.lparen :: acc)
      | ')', _ => lexGo fuel cs (.rparen :: acc)
      | ',', _ => lexGo fuel cs (.comma :: acc)
      | ':', '=' :: rest => lexGo fuel rest (.assign :: acc)
      | '-', '>' :: rest => lexGo fuel rest (.arrow :: acc)
      | '"', _ => lexString [] cs >>= fun (raw, rest) => lexGo fuel rest (.str raw :: acc)
      | _, _ =>
        if c.isDigit then
          lexNumber c cs >>= fun (n, rest) => lexGo fuel rest (.num n :: acc)
        else if isIdStart c then
          let (more, rest) := cs.span isIdChar
          let word := String.mk (c :: more)
          match word, rest with
          | "hex", '"' :: body => lexHex body [] >>= fun (bytes, r) => lexGo fuel r (.hex bytes :: acc)
          | _, _ => lexGo fuel rest (.ident word :: acc)
        else none

def lex (text : String) : Option (List Tok) :=
  lexGo (text.length + 1) text.toList []

/-! ## Name resolution -/

def findVar : (L : List String) → (x : String) → Option (Mem L x)
  | [], _ => none
  | y :: ys, x =>
      if h : y = x then some (h ▸ Mem.here) else (findVar ys x).map Mem.there

def findFn : (F : List FnSig) → String → Option ((s : FnSig) × Mem F s)
  | [], _ => none
  | s :: ss, x =>
      if s.name = x then some ⟨s, .here⟩
      else (findFn ss x).map fun found => ⟨found.1, .there found.2⟩

def mkLit (t : LitTok) : Except String Lit :=
  match h : t.decode with
  | some v => .ok ⟨t, v, h⟩
  | none => .error s!"literal out of range: {repr t}"

def litTok? : Tok → Option LitTok
  | .num n => some (.num n)
  | .str raw => some (.str raw)
  | .ident "true" => some (.bool true)
  | .ident "false" => some (.bool false)
  | _ => none

def keywords : List String :=
  ["let", "function", "if", "switch", "case", "default", "for", "break", "continue",
   "leave", "true", "false"]

/-- Object-dialect names; they are never ordinary builtins or functions. -/
def objectNames : List String :=
  ["datasize", "dataoffset", "datacopy", "setimmutable", "loadimmutable",
   "linkersymbol", "memoryguard"]

def reserved (x : String) : Bool :=
  keywords.contains x || objectNames.contains x || (Solidity.Yul.lookupBuiltin x).isSome

/-- Fresh, pairwise distinct, non-reserved declared names. -/
def freshNames (L : List String) (xs : List String) : Except String Unit :=
  if xs.any (fun x => L.contains x || reserved x) then .error s!"shadowing or reserved name in {xs}"
  else if xs.eraseDups.length = xs.length then .ok ()
  else .error s!"duplicate names in {xs}"

/-! ## Expressions -/

def single {F L} (e : (r : Nat) × Expr F L r) : Except String (Expr F L 1) :=
  if h : e.1 = 1 then .ok (h ▸ e.2) else .error s!"expected one value, got {e.1}"

mutual
def parseExpr (F : List FnSig) (L : List String) :
    Nat → List Tok → Except String ((r : Nat) × Expr F L r × List Tok)
  | 0, _ => .error "parser fuel"
  | fuel + 1, .ident x :: .lparen :: rest => parseCall F L fuel x rest
  | _ + 1, t :: rest =>
      match litTok? t, t with
      | some lt, _ => do let l ← mkLit lt; pure ⟨1, .lit l, rest⟩
      | none, .ident x =>
          match findVar L x with
          | some m => .ok ⟨1, .var x m, rest⟩
          | none => .error s!"unknown variable {x}"
      | none, _ => .error s!"expected expression at {repr t}"
  | _ + 1, [] => .error "expected expression at end of input"

/-- Arguments after `(`, through the closing `)`. -/
def parseArgs (F : List FnSig) (L : List String) :
    Nat → List Tok → Except String ((k : Nat) × Args F L k × List Tok)
  | 0, _ => .error "parser fuel"
  | _ + 1, .rparen :: rest => .ok ⟨0, .nil, rest⟩
  | fuel + 1, toks => parseArgs1 F L fuel toks

def parseArgs1 (F : List FnSig) (L : List String) :
    Nat → List Tok → Except String ((k : Nat) × Args F L k × List Tok)
  | 0, _ => .error "parser fuel"
  | fuel + 1, toks => do
      let ⟨r, e, rest⟩ ← parseExpr F L fuel toks
      let e ← single ⟨r, e⟩
      match rest with
      | .comma :: more =>
          let ⟨k, args, after⟩ ← parseArgs1 F L fuel more
          pure ⟨k + 1, .cons e args, after⟩
      | .rparen :: after => pure ⟨1, .cons e .nil, after⟩
      | _ => .error "expected , or ) in arguments"

/-- A call after `name (`: user function, object operation or EVM builtin. -/
def parseCall (F : List FnSig) (L : List String) :
    Nat → String → List Tok → Except String ((r : Nat) × Expr F L r × List Tok)
  | 0, _, _ => .error "parser fuel"
  | fuel + 1, x, rest =>
      match findFn F x with
      | some ⟨s, m⟩ => do
          let ⟨k, args, after⟩ ← parseArgs F L fuel rest
          if h : k = s.params.length then pure ⟨s.rets.length, .call m (h ▸ args), after⟩
          else .error s!"{x}: expected {s.params.length} arguments, got {k}"
      | none =>
        match x, rest with
        | "datasize", .str l :: .rparen :: after => .ok ⟨1, .op (.object (.datasize l)) .nil, after⟩
        | "dataoffset", .str l :: .rparen :: after => .ok ⟨1, .op (.object (.dataoffset l)) .nil, after⟩
        | "loadimmutable", .str l :: .rparen :: after =>
            .ok ⟨1, .op (.object (.loadimmutable l)) .nil, after⟩
        | "linkersymbol", .str l :: .rparen :: after =>
            .ok ⟨1, .op (.object (.linkersymbol l)) .nil, after⟩
        | "memoryguard", .num n :: .rparen :: after =>
            if h : n < 2 ^ 256 then .ok ⟨1, .op (.object (.memoryguard ⟨n, h⟩)) .nil, after⟩
            else .error "memoryguard literal out of range"
        | "setimmutable", toks => do
            let ⟨r, offset, after⟩ ← parseExpr F L fuel toks
            let offset ← single ⟨r, offset⟩
            match after with
            | .comma :: .str l :: .comma :: more => do
                let ⟨k, args, after⟩ ← parseArgs1 F L fuel more
                if h : k = 1 then
                  pure ⟨0, .op (.object (.setimmutable l)) (.cons offset (h ▸ args)), after⟩
                else .error "setimmutable: expected three arguments"
            | _ => .error "setimmutable: expected a literal name"
        | "datacopy", toks => do
            let ⟨k, args, after⟩ ← parseArgs F L fuel toks
            if h : k = 3 then pure ⟨0, .op (.object .datacopy) (h ▸ args), after⟩
            else .error "datacopy: expected three arguments"
        | _, toks =>
          if objectNames.contains x then .error s!"{x}: malformed literal argument" else
          match Solidity.Yul.lookupBuiltin x with
          | some ⟨a, r, b⟩ => do
              let ⟨k, args, after⟩ ← parseArgs F L fuel toks
              if h : k = a then pure ⟨r, .op (.evm b) (h ▸ args), after⟩
              else .error s!"{x}: expected {a} arguments, got {k}"
          | none => .error s!"unknown function {x}"
end

/-! ## Statements and blocks -/

/-- `x (, y)*` identifiers; stops before the first non-matching token. -/
def parseNames : Nat → List Tok → List String × List Tok
  | 0, toks => ([], toks)
  | fuel + 1, .ident x :: .comma :: rest =>
      let (xs, after) := parseNames fuel rest
      (x :: xs, after)
  | _ + 1, .ident x :: rest => ([x], rest)
  | _ + 1, toks => ([], toks)

/-- A function header after `function`, up to (not including) its body. -/
def parseHeader (toks : List Tok) : Except String (FnSig × List Tok) :=
  match toks with
  | .ident name :: .lparen :: rest =>
      let (params, rest) := parseNames rest.length rest
      match rest with
      | .rparen :: .arrow :: more =>
          let (rets, after) := parseNames more.length more
          if rets.isEmpty then .error s!"{name}: empty return list" else .ok (⟨name, params, rets⟩, after)
      | .rparen :: after => .ok (⟨name, params, []⟩, after)
      | _ => .error s!"{name}: malformed parameter list"
  | _ => .error "malformed function header"

/-- The signatures of the functions defined directly in a block (after its `{`). -/
def scanSigs : Nat → Nat → List Tok → Except String (List FnSig)
  | 0, _, _ => .error "scan fuel"
  | _ + 1, _, [] => .error "unterminated block"
  | _ + 1, 0, .rbrace :: _ => .ok []
  | fuel + 1, depth + 1, .rbrace :: rest => scanSigs fuel depth rest
  | fuel + 1, depth, .lbrace :: rest => scanSigs fuel (depth + 1) rest
  | fuel + 1, 0, .ident "function" :: rest => do
      let (s, _) ← parseHeader rest
      let ss ← scanSigs fuel 0 rest
      pure (s :: ss)
  | fuel + 1, depth, _ :: rest => scanSigs fuel depth rest

abbrev FnBody (F : List FnSig) := (s : FnSig) × Block F ⟨true, false⟩ (s.params ++ s.rets)

def assemble (F : List FnSig) : (ss : List FnSig) → List (FnBody F) → Except String (Bodies F ss)
  | [], [] => .ok .nil
  | s :: ss, ⟨t, body⟩ :: rest =>
      if h : t = s then (Bodies.cons (h ▸ body)) <$> assemble F ss rest
      else .error s!"function {t.name} out of order"
  | _, _ => .error "function count mismatch"

def resolveTargets (L : List String) : List String → Except String (List (Var L))
  | [] => .ok []
  | x :: xs =>
      match findVar L x with
      | some m => (⟨x, m⟩ :: ·) <$> resolveTargets L xs
      | none => .error s!"unknown assignment target {x}"

/-- A `let` declaration's optional initializer, after its names. -/
def parseInit (F : List FnSig) (L : List String) (xs : List String) (fuel : Nat) :
    List Tok → Except String (Option (Expr F L xs.length) × List Tok)
  | .assign :: rest => do
      let ⟨r, e, after⟩ ← parseExpr F L fuel rest
      if h : r = xs.length then pure (some (h ▸ e), after)
      else .error s!"let {xs}: initializer returns {r} values"
  | toks => .ok (none, toks)

mutual
def parseBlock (F : List FnSig) (c : Ctl) (L : List String) :
    Nat → List Tok → Except String (Block F c L × List Tok)
  | 0, _ => .error "parser fuel"
  | fuel + 1, .lbrace :: rest => do
      let ss ← scanSigs (rest.length + 1) 0 rest
      let (items, bodies, after) ← parseItems (ss ++ F) c L ss 0 fuel rest
      let group ← assemble (ss ++ F) ss bodies
      pure (.mk ss group items, after)
  | _ + 1, _ => .error "expected {"

def parseItems (F : List FnSig) (c : Ctl) (L : List String) (ss : List FnSig) (k : Nat) :
    Nat → List Tok → Except String (Items F c L ss.length × List (FnBody F) × List Tok)
  | 0, _ => .error "parser fuel"
  | _ + 1, .rbrace :: rest => .ok (.nil, [], rest)
  | fuel + 1, .ident "let" :: rest => do
      let (xs, rest) := parseNames rest.length rest
      if xs.isEmpty then .error "let without names" else
      freshNames L xs
      let (init, rest) ← parseInit F L xs fuel rest
      let (items, bodies, after) ← parseItems F c (xs ++ L) ss k fuel rest
      pure (.let_ xs init items, bodies, after)
  | fuel + 1, .ident "function" :: rest => do
      let (s, rest) ← parseHeader rest
      if hk : k < ss.length then
        if ss[k] = s then
          freshNames [] (s.params ++ s.rets)
          let (body, rest) ← parseBlock F ⟨true, false⟩ (s.params ++ s.rets) fuel rest
          let (items, bodies, after) ← parseItems F c L ss (k + 1) fuel rest
          pure (.fn ⟨k, hk⟩ items, ⟨s, body⟩ :: bodies, after)
        else .error s!"function {s.name}: header disagrees with scan"
      else .error s!"function {s.name}: not in this block's group"
  | fuel + 1, toks => do
      let (s, rest) ← parseStmt F c L fuel toks
      let (items, bodies, after) ← parseItems F c L ss k fuel rest
      pure (.stmt s items, bodies, after)

def parseStmt (F : List FnSig) (c : Ctl) (L : List String) :
    Nat → List Tok → Except String (Stmt F c L × List Tok)
  | 0, _ => .error "parser fuel"
  | fuel + 1, toks@(.lbrace :: _) => do
      let (b, after) ← parseBlock F c L fuel toks
      pure (.block b, after)
  | fuel + 1, .ident "if" :: rest => do
      let ⟨r, e, rest⟩ ← parseExpr F L fuel rest
      let e ← single ⟨r, e⟩
      let (b, after) ← parseBlock F c L fuel rest
      pure (.if_ e b, after)
  | fuel + 1, .ident "switch" :: rest => do
      let ⟨r, e, rest⟩ ← parseExpr F L fuel rest
      let e ← single ⟨r, e⟩
      let (cs, rest) ← parseCases F c L fuel rest
      match rest with
      | .ident "default" :: more => do
          let (b, after) ← parseBlock F c L fuel more
          pure (.switchDefault e cs b, after)
      | _ => pure (.switch e cs, rest)
  | fuel + 1, .ident "for" :: .lbrace :: rest => do
      let (lp, after) ← parseLoop F c L fuel rest
      pure (.for_ lp, after)
  | _ + 1, .ident "leave" :: rest =>
      match c with
      | ⟨true, _⟩ => .ok (.leave, rest)
      | ⟨false, _⟩ => .error "leave outside a function"
  | _ + 1, .ident "break" :: rest =>
      match c with
      | ⟨_, true⟩ => .ok (.break_, rest)
      | ⟨_, false⟩ => .error "break outside a loop body"
  | _ + 1, .ident "continue" :: rest =>
      match c with
      | ⟨_, true⟩ => .ok (.continue_, rest)
      | ⟨_, false⟩ => .error "continue outside a loop body"
  | fuel + 1, toks@(.ident _ :: .comma :: _) | fuel + 1, toks@(.ident _ :: .assign :: _) => do
      let (xs, rest) := parseNames toks.length toks
      let targets ← resolveTargets L xs
      match rest with
      | .assign :: more => do
          let ⟨r, e, after⟩ ← parseExpr F L fuel more
          if h : r = targets.length then pure (.assign targets (h ▸ e), after)
          else .error s!"assignment to {xs}: expression returns {r} values"
      | _ => .error "expected :="
  | fuel + 1, toks => do
      let ⟨r, e, after⟩ ← parseExpr F L fuel toks
      if h : r = 0 then pure (.discard (h ▸ e), after)
      else .error s!"expression statement returns {r} values"

def parseCases (F : List FnSig) (c : Ctl) (L : List String) :
    Nat → List Tok → Except String (Cases F c L × List Tok)
  | 0, _ => .error "parser fuel"
  | fuel + 1, .ident "case" :: t :: rest =>
      match litTok? t with
      | some lt => do
          let l ← mkLit lt
          let (b, rest) ← parseBlock F c L fuel rest
          let (cs, after) ← parseCases F c L fuel rest
          pure (.cons l b cs, after)
      | none => .error "case label is not a literal"
  | _ + 1, toks => .ok (.nil, toks)

def parseLoop (F : List FnSig) (c : Ctl) (L : List String) :
    Nat → List Tok → Except String (Loop F c L × List Tok)
  | 0, _ => .error "parser fuel"
  | fuel + 1, .rbrace :: rest => do
      let ⟨r, e, rest⟩ ← parseExpr F L fuel rest
      let e ← single ⟨r, e⟩
      let (post, rest) ← parseBlock F ⟨c.function, false⟩ L fuel rest
      let (body, after) ← parseBlock F ⟨c.function, true⟩ L fuel rest
      pure (.run e post body, after)
  | fuel + 1, .ident "let" :: rest => do
      let (xs, rest) := parseNames rest.length rest
      if xs.isEmpty then .error "let without names" else
      freshNames L xs
      let (init, rest) ← parseInit F L xs fuel rest
      let (lp, after) ← parseLoop F c (xs ++ L) fuel rest
      pure (.let_ xs init lp, after)
  | _ + 1, .ident "function" :: _ => .error "function in a for-loop initializer"
  | fuel + 1, toks => do
      let (s, rest) ← parseStmt F ⟨c.function, false⟩ L fuel toks
      let (lp, after) ← parseLoop F c L fuel rest
      pure (.stmt s lp, after)
end

/-! ## Objects and the certificate -/

/-- The parts of a code-bearing object; the root of an artifact is never data. -/
structure ObjectParts where
  name : String
  code : Code
  children : List (Object Code)

def ObjectParts.root (p : ObjectParts) : Object Code := .object p.name p.code p.children

mutual
def parseObject (fuel : Nat) : Nat → List Tok → Except String (ObjectParts × List Tok)
  | 0, _ => .error "object fuel"
  | depth + 1, .ident "object" :: .str name :: .lbrace :: .ident "code" :: rest => do
      let (code, rest) ← parseBlock [] ⟨false, false⟩ [] fuel rest
      let (children, after) ← parseChildren fuel depth rest
      pure (⟨name, code, children⟩, after)
  | _ + 1, _ => .error "expected object \"name\" { code { … } … }"

def parseChildren (fuel : Nat) : Nat → List Tok → Except String (List (Object Code) × List Tok)
  | 0, _ => .error "object fuel"
  | _ + 1, .rbrace :: rest => .ok ([], rest)
  | depth + 1, .ident "data" :: .str name :: .hex bytes :: rest => do
      let (more, after) ← parseChildren fuel depth rest
      pure (.data name bytes :: more, after)
  | depth + 1, toks@(.ident "object" :: _) => do
      let (child, rest) ← parseObject fuel depth toks
      let (more, after) ← parseChildren fuel depth rest
      pure (child.root :: more, after)
  | _ + 1, _ => .error "expected object, hex data or }"
end

/-! ## Well-formedness, checked and certified

The printer prints names only, so the token certificate alone does not fix
which binder a name refers to. `objectWf` checks, on the returned tree, the
scoping rules that make resolution unique: every variable and call points at
the first (innermost) binder of its name, and no declaration reuses a visible
variable, function or reserved name, so that binder is the only one. It also
checks what solc's analyzer requires beyond the grammar: each function body
printed exactly once in order, nonempty and distinct `let`/assignment names,
switches with a case or default and distinct case values, no function in a
for-loop initializer, no `pc`, distinct object member names. -/

def nodupNames (xs : List String) : Bool := xs.eraseDups.length == xs.length

/-- A declaration of `xs` with functions `F` and locals `L` visible. -/
def declOk (F : List FnSig) (L : List String) (xs : List String) : Bool :=
  nodupNames xs && xs.all fun x => !L.contains x && !(F.any (·.name == x)) && !reserved x

def nodupWords : List Word → Bool
  | [] => true
  | w :: ws => !ws.contains w && nodupWords ws

mutual
def Expr.wf {F L r} : Expr F L r → Bool
  | .lit _ => true
  | .var x m => m.index == L.idxOf x
  | .op o args => o.name != "pc" && args.wf
  | @Expr.call _ _ s m args => m.index == (F.map FnSig.name).idxOf s.name && args.wf

def Args.wf {F L k} : Args F L k → Bool
  | .nil => true
  | .cons e rest => e.wf && rest.wf
end

def initWf {F L} {xs : List String} : Option (Expr F L xs.length) → Bool
  | none => true
  | some e => e.wf

mutual
/-- `init`: inside a for-loop initializer, where functions are refused. -/
def Stmt.wf {F c L} (init : Bool) : Stmt F c L → Bool
  | .block b => b.wf init
  | .discard e => e.wf
  | .assign ts e => !ts.isEmpty && nodupNames (ts.map Sigma.fst) && e.wf
  | .if_ e b => e.wf && b.wf init
  | .switch e cs => e.wf && cs.nonempty && nodupWords cs.values && cs.wf init
  | .switchDefault e cs b => e.wf && nodupWords cs.values && cs.wf init && b.wf init
  | .for_ lp => lp.wf
  | .leave | .break_ | .continue_ => true

def Cases.wf {F c L} (init : Bool) : Cases F c L → Bool
  | .nil => true
  | .cons _ b rest => b.wf init && rest.wf init

def Cases.values {F c L} : Cases F c L → List Word
  | .nil => []
  | .cons l _ rest => l.value :: rest.values

def Cases.nonempty {F c L} : Cases F c L → Bool
  | .nil => false
  | .cons _ _ _ => true

def Loop.wf {F c L} : Loop F c L → Bool
  | .stmt st rest => st.wf true && rest.wf
  | .let_ xs e rest => !xs.isEmpty && declOk F L xs && initWf e && rest.wf
  | .run e post body => e.wf && post.wf false && body.wf false

/-- `next`: the index the next function marker must carry. -/
def Items.wf {F c L g} (init : Bool) (next : Nat) : Items F c L g → Bool
  | .nil => next == g
  | .stmt st rest => st.wf init && rest.wf init next
  | .let_ xs e rest => !xs.isEmpty && declOk F L xs && initWf e && rest.wf init next
  | .fn k rest => k.val == next && rest.wf init (next + 1)

def Block.wf {F c L} (init : Bool) : Block F c L → Bool
  | .mk ss bodies items =>
      (!init || ss.isEmpty) && declOk F L (ss.map FnSig.name) && bodies.wf && items.wf init 0

def Bodies.wf {G ss} : Bodies G ss → Bool
  | .nil => true
  | @Bodies.cons _ s _ body rest => declOk G [] (s.params ++ s.rets) && body.wf false && rest.wf
end

def memberName : Object Code → String
  | .object name _ _ => name
  | .data name _ => name

mutual
def objectWf : Object Code → Bool
  | .object _ code children => Block.wf false code && objectsWf children &&
      nodupNames (children.map memberName)
  | .data _ _ => true

def objectsWf : List (Object Code) → Bool
  | [] => true
  | o :: os => objectWf o && objectsWf os
end

/-- Two memberships at the same position are the same membership: a checked
`m.index = L.idxOf x` determines the binder from the printed name. -/
theorem Mem.eq_of_index {α : Type} {L : List α} {x : α} :
    (m₁ m₂ : Mem L x) → m₁.index = m₂.index → m₁ = m₂
  | .here, .here, _ => rfl
  | .there m₁, .there m₂, h => by
      simp only [Mem.index, Nat.add_right_cancel_iff] at h
      rw [Mem.eq_of_index m₁ m₂ h]
  | .here, .there _, h => by simp only [Mem.index] at h; omega
  | .there _, .here, h => by simp only [Mem.index] at h; omega

/-- A parsed IR text: its lexed tokens and a tree printing back to exactly them. -/
structure Parsed (text : String) where
  parts : ObjectParts
  tokens : List Tok
  lexed : lex text = some tokens
  printed : objectToks parts.root = tokens
  wellFormed : objectWf parts.root = true

def parse (text : String) : Except String (Parsed text) :=
  match h : lex text with
  | none => .error "lexical error"
  | some toks => do
      let fuel := 4 * toks.length + 8
      let (parts, rest) ← parseObject fuel fuel toks
      unless rest.isEmpty do .error "trailing tokens after the root object"
      if hp : objectToks parts.root = toks then
        if hw : objectWf parts.root = true then .ok ⟨parts, toks, h, hp, hw⟩
        else .error "tree violates scoping or static rules"
      else .error "printed tree differs from the lexed text"

/-- Provenance: the returned tree prints to exactly the token stream of the
input text, and passes the checked scoping and static rules (`objectWf`).
Both are checked on the result; the untrusted parser is not assumed correct. -/
theorem Parsed.sound {text : String} (p : Parsed text) :
    lex text = some (objectToks p.parts.root) ∧ objectWf p.parts.root = true :=
  ⟨by rw [p.lexed, p.printed], p.wellFormed⟩

/-- The root of a parsed text is the code-bearing object it names. -/
def Parsed.artifact {text : String} (p : Parsed text) (mode : IrMode)
    (source : List (Fin 256)) : IrArtifact Code :=
  ⟨mode, source, p.parts.name, p.parts.code, p.parts.children⟩

theorem Parsed.artifact_root {text : String} (p : Parsed text) (mode : IrMode)
    (source : List (Fin 256)) : (p.artifact mode source).root = p.parts.root := rfl

end Solidity.SolcValidation.IrSyntax
