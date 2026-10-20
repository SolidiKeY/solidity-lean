import Lean
import Solidity.Frontend.SolcJson
import Solidity.Syntax.Splice

/-!
# `solc_import`: a contract from solc's AST, at elaboration time

`solc_import "f.ast.json" hash 0x… as N renaming Triple => FixedTriple`
reads a fixture of `scripts/solc-ast.mjs` (the path is relative to the
importing file) and defines

* `N : Contract`, the contract's state variables and the functions called
  by name through `contract!{ … }`, each function checked alone first;
* `N.f : Prog N Γ Γ'` for each function `f` that elaborates, its body read
  against `N` with its parameters as locals in scope (`Γ`, newest first:
  `paramCtx`), after its return variables declared at their defaults, its
  loops and then its `return`s lowered (`lowerLoops`, `lowerReturns`), as a
  call inlines it;
* `N.constructor : Prog N Γ Γ'` for a declared constructor, a deployment:
  `constructor(x̄);` with its parameters as locals in scope (`elabCtor`).
  The contract declares the constructor (its member last, since it may
  call every function) and the state variables' initializers
  (`SolcContract.initMembers`) only if it expands with both, else neither:
  an implicit constructor's initializers left out are a warning, a declared
  one's a row;
* `N.report : List ImportRow`, one row per function, the constructor's
  first: its solkey tag
  (`tagOf`: which obligation solkey states, if any) and parameters, what
  became of it and why, with the source line.  A function whose obligation
  is a specification's, or that has none (`internal`), is still a program:
  only its plain statement is not made (`solc_scoped_problems`).

Each body is printed as `sol` text (`SolcJson.lean`), parsed as
`sol_raw!{ … }` and elaborated to a `List RawStmt` term by the macros, the
one lowering path `sol[C]{ … }` takes.  Those terms and the contract are
then evaluated together, one `evalExpr`, and the typed elaborator runs on
each as ordinary compiled code (`elabProgAtS.go`); `sol[C]{ … }` would
compile one program per function.  Its result, the scoped program, is
quoted back hash-consed with every proof `Eq.refl` (`Prog.quoteShared`,
`Prog.define`), so the kernel re-checks what it computed: every local the
program reads is in scope, at its type.  The programs are not compiled
(about half the import's time for the TestSuite): what evaluates one reads
its value (`#solc_show N.f`; an obligation, `Frontend/Problems.lean`).

Lake does not track the fixture, so the command names its hash (FNV-1a 64
over the bytes) and refuses a fixture of another one; the script that
writes the fixture rewrites the literal, which makes Lake re-check the
importing module.

A function that does not elaborate is a row, not an error: the import
never fails on one function.  Each body's elaboration has its own
heartbeats and catches runtime exceptions too (`tryCatchRuntimeEx`), so a
body that exhausts its budget is a row as well.  A row is found by its
index, not its name. Overloaded declarations have distinct internal names;
the reader refuses an unmangled function named `report` before any constant is made.
-/

namespace Solidity.Frontend

open Lean Elab Command Term Meta

/-- What the import made of a function. -/
inductive ImportStatus where
  /-- A constant `N.f : Prog N Γ Γ'`. -/
  | elaborated
  /-- solkey's `@custom:key skip`: no obligation. -/
  | skipped
  /-- The model has no counterpart (`Gap.excluded`). -/
  | excluded
  /-- The printer, the grammar or the typed elaborator lacks the form. -/
  | unsupported
  deriving Repr, DecidableEq, Inhabited

def ImportStatus.toStr : ImportStatus → String
  | .elaborated => "elaborated"
  | .skipped => "skipped"
  | .excluded => "excluded"
  | .unsupported => "unsupported"

/-- A function of the imported contract and what became of it; `reason` is
`file:line: …`. -/
structure ImportRow where
  name : String
  /-- The Solidity name; `name` identifies the generated Lean declaration. -/
  sourceName : String := ""
  sourceSignature : String := ""
  tag : Tag
  params : List (String × String)
  /-- Elaborated parameter types, newest first, including reference locations. -/
  paramTypes : Ctx := []
  status : ImportStatus
  reason : String
  /-- Declared `payable`. -/
  payable : Bool := false
  /-- It may call a callee that writes the state (`SolcFun.writingCall`). -/
  writingCall : Bool := true
  /-- The parameters the ABI decoder bounds (`SolcFun.paramRanges`). -/
  paramRanges : List (String × Int × Int) := []
  /-- The memory array parameters whose elements it bounds (`SolcFun.elemRanges`). -/
  elemRanges : List (String × Int × Int × Option Nat) := []
  deriving Repr, Inhabited

deriving instance ToExpr for Tag
deriving instance ToExpr for ImportStatus
deriving instance ToExpr for ImportRow

/-- The row of an imported function. -/
def ImportRow.ofFun (f : SolcFun) (status : ImportStatus) (reason : String) : ImportRow :=
  { name := f.name, sourceName := f.sourceName, sourceSignature := f.sourceSignature,
    tag := f.tag, params := f.params, status, reason, payable := f.payable,
    writingCall := f.writingCall, paramRanges := f.paramRanges, elemRanges := f.elemRanges }

/-- The declaration `N.f` of the row `f` of `N`'s import. -/
def ImportRow.declName (N : Lean.Name) (r : ImportRow) : Lean.Name := N ++ Lean.Name.mkSimple r.name

/-- The counts by status, then every row that did not elaborate. -/
def ImportRow.summary (rows : List ImportRow) : String :=
  let count (s : ImportStatus) := (rows.filter (·.status == s)).length
  let tags := ", ".intercalate <| [Tag.diamond, .box, .skip, .specified, .internal, .malformed]
    |>.filterMap fun t =>
      let n := (rows.filter (·.tag == t)).length
      if n == 0 && t != .diamond && t != .box && t != .skip then none
      else some s!"{n} {t.toStr}"
  let head := s!"{rows.length} functions ({tags}): {count .elaborated} elaborated, \
    {count .skipped} skipped, {count .excluded} excluded, {count .unsupported} unsupported"
  let rest := rows.filter (·.status != .elaborated) |>.map fun r =>
    s!"{r.status.toStr} {r.name}: {r.reason}"
  "\n".intercalate (head :: rest)

/-- FNV-1a 64 over the bytes, `scripts/solc-ast.mjs`'s `hash`. -/
def fnv1a64 (b : ByteArray) : UInt64 :=
  b.foldl (fun h x => (h ^^^ x.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

/-- `0x` and 16 hex digits, as `scripts/solc-ast.mjs` writes the hash. -/
def hex16 (h : UInt64) : String :=
  let d := (Nat.toDigits 16 h.toNat).asString
  "0x" ++ "".pushn '0' (16 - d.length) ++ d

/-- Every position of `stx` moved to `ref`'s, so a parsed text never
points into a string the file does not have. -/
partial def atRef (ref : Syntax) (stx : Syntax) : Syntax :=
  let info := SourceInfo.fromRef ref
  match stx with
  | .node _ k args => .node info k (args.map (atRef ref))
  | .atom _ v => .atom info v
  | .ident _ raw v pre => .ident info raw v pre
  | .missing => .missing

/-- The parameters of a function as locals in scope, most recent first. -/
def paramCtx (C : Contract) (ps : List RawStmt) : Except String ECtx := do
  let rows ← ps.reverse.mapM fun s => match s with
    | .decl T x none => do
      let (.prim p, n) ← elabDeclTy C T | throw s!"reference parameter {x} needs a data location"
      pure [(x, .val p n)]
    | .declStorage T x none => do
      let (.ref R, ws) ← elabTyW C T | throw s!"storage location on value parameter {x}"
      pure (shapeEntry x ws ++ [(x, .alias R)])
    | .declMemory T x none => do
      let (.ref R, ws) ← elabTyW C T | throw s!"memory location on value parameter {x}"
      unless (Ty.ref R).mapFree do throw s!"memory parameter {x} holds a mapping"
      pure (shapeEntry x ws ++ [(x, .mem R)])
    | _ => throw "invalid parameter declaration"
  pure rows.flatten

/-- A function's return variables, an unnamed one named as `contract!` names
it: `_ret`, or `_ret0`, `_ret1`, … of several (Lean's spelling; KeY names
them `ret0`, `ret1`, …). -/
def retNames (f : SolcFun) : List (String × String) :=
  f.rets.zipIdx.map fun ((x, t), i) =>
    (if !x.isEmpty then x else if f.rets.length == 1 then "_ret" else s!"_ret{i}", t)

/-- Whether a loop in the statement, at any depth, has a `return` inside. -/
partial def hasLoopReturn (s : RawStmt) : Bool :=
  ((s matches .whileLoop .. | .forLoop .. | .doWhile .. | .loop ..) && s.hasReturn) ||
    s.blocks.any (·.any hasLoopReturn)

/-- A body's loops lowered (`lowerLoops`), solkey's `LoopLowering` after its
`ReturnLowering`: a `return` inside a loop becomes a flag, and the
`if (ret) return;` after the outermost loop is left to `lowerReturns`.  That
splices the loop's block, and a `for`'s declaration in it, over the
statements after it, so a body with such a loop is first renamed fresh past
its `nRets` return variables (`renameStmts`, as a call inlines it): a
sibling `for (uint i …)` then declares a name of its own. -/
def lowerBodyLoops (rets : List String) (nRets : Nat) (raw : List RawStmt) :
    ElabM (List RawStmt) := do
  let raw ← if raw.any hasLoopReturn then
      pure (raw.take nRets ++ (← renameStmts [] (raw.drop nRets)))
    else pure raw
  lowerLoops (some rets) raw

syntax (name := solcImport) "solc_import " str " hash " num " as " ident
  (" renaming " sepBy1(ident " => " ident, ", "))? (&" testing")? : command

/-- A large imported function table, compiled in bounded list segments.
For example, the testing import retains all of TestSuite's public functions.
Lean's list notation uses nested lets, so expose only the spine, retaining
the original heads. Every generated segment is checked by the kernel. -/
private def compileListSegments (owner : Lean.Name) (value : Expr) : TermElabM Expr := do
  let mut rest : Expr := ← whnf value
  let mut cells : Array Expr := #[]
  while rest.isAppOfArity ``List.cons 3 do
    cells := cells.push rest
    rest ← whnf rest.appArg!
  if cells.size ≤ 64 then return value
  let mut rebuilt : Expr := rest
  let mut count : Nat := 0
  for cell in cells.reverse do
    rebuilt := cell.appFn!.app rebuilt
    count := count + 1
    if count % 64 == 0 then
      let name ← mkFreshUserName (owner ++ `_list)
      addAndCompile <| .defnDecl {
        name, levelParams := [], type := ← inferType rebuilt, value := rebuilt,
        hints := .abbrev, safety := .safe }
      rebuilt := mkConst name
  return rebuilt

/-- Define an imported contract such as `TestSuite` without compiling its
whole function table in one expression. A kernel-checked reflexivity proof
certifies that segmentation preserves the complete original contract. -/
private def defineImportedContract (name : Lean.Name) (contractSyntax : Syntax) : TermElabM Unit := do
  let original ← elabTermEnsuringType contractSyntax (mkConst ``Contract)
  synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  let original ← whnf original
  unless original.isAppOfArity ``Contract.mk 8 do
    throwError "solc_import: expected a contract literal"
  let mut fields : Array Expr := #[]
  for arg in original.getAppArgs do
    fields := fields.push (← compileListSegments name arg)
  let value : Expr := mkAppN original.getAppFn fields
  let certificate ← mkFreshUserName (name ++ `_inputEq)
  -- Check in the kernel directly: a metaprogram's recursive comparison of
  -- the full unsegmented table would itself exceed the elaborator's depth.
  addDecl <| .thmDecl {
    name := certificate, levelParams := [],
    type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Contract) original value,
    value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Contract) original }
  addAndCompile <| .defnDecl {
    name, levelParams := [], type := mkConst ``Contract, value,
    hints := .regular 0, safety := .safe }

/-! Renaming specification parameters is a syntax operation. In particular,
quantified variables shadow parameters, and member labels are not variables. -/

private partial def specCommentTokens (depth : Nat) : List String → List String × List String
  | [] => ([], [])
  | "/" :: "-" :: rest =>
    let (body, tail) := specCommentTokens (depth + 1) rest
    (["/", "-"] ++ body, tail)
  | "-" :: "/" :: rest =>
    if depth == 1 then (["-", "/"], rest) else
      let (body, tail) := specCommentTokens (depth - 1) rest
      (["-", "/"] ++ body, tail)
  | token :: rest =>
    let (body, tail) := specCommentTokens depth rest
    (token :: body, tail)

private partial def escapeSpecBindings (names : List String) : List String → List String
  | [] => []
  | "\\" :: keyword :: rest => "\\" :: keyword :: escapeSpecBindings names rest
  | "«" :: rest =>
    let quoted := rest.takeWhile (· != "»")
    let tail := rest.drop quoted.length
    match tail with
    | [] => "«" :: quoted
    | closing :: tail => "«" :: quoted ++ closing :: escapeSpecBindings names tail
  | "-" :: "-" :: rest =>
    let comment := rest.takeWhile (· != "\n")
    ["-", "-"] ++ comment ++ escapeSpecBindings names (rest.drop comment.length)
  | "/" :: "-" :: rest =>
    let (comment, tail) := specCommentTokens 1 rest
    ["/", "-"] ++ comment ++ escapeSpecBindings names tail
  | token :: rest =>
    let token := ".".intercalate (token.splitOn "." |>.map fun name =>
      if names.contains name && leanKeywords.contains name then s!"«{name}»" else name)
    token :: escapeSpecBindings names rest

private partial def renameSpecSyntax (params rets : List (String × String)) (stx : Syntax) : Syntax :=
  match stx with
  | `(spec_expr| \forall $T:ident $x:ident; $body) =>
    let _ := T
    stx.setArg (stx.getNumArgs - 1)
      (renameSpecSyntax (params.filter (·.1 != x.getId.toString))
        (rets.filter (·.1 != x.getId.toString)) body.raw)
  | `(spec_expr| \exists $T:ident $x:ident; $body) =>
    let _ := T
    stx.setArg (stx.getNumArgs - 1)
      (renameSpecSyntax (params.filter (·.1 != x.getId.toString))
        (rets.filter (·.1 != x.getId.toString)) body.raw)
  | `(spec_expr| \old($body)) =>
    stx.setArg (stx.getNumArgs - 2) (renameSpecSyntax params [] body.raw)
  | `(spec_expr| $x:ident) =>
    match x.getId.components.map (·.toString) with
    | head :: tail =>
      match Semantics.lookupBy head (params ++ rets) with
      | none => stx
      | some renamed =>
        let name := (renamed :: tail).foldl Lean.Name.str .anonymous
        let ident := Syntax.ident x.raw.getHeadInfo (name.toString.toSubstring) name []
        match stx with
        | .node info kind args => .node info kind (args.map fun a => if a == x.raw then ident else a)
        | _ => ident
    | [] => stx
  | _ =>
    match stx with
    | .node info kind args => .node info kind (args.map (renameSpecSyntax params rets))
    | _ => stx

private def rewriteSpecBindings (env : Environment) (kind : String)
    (params rets : List (String × String)) (text : String) : Except String String := do
  let names := params ++ rets
  if names.isEmpty || !["requires", "ensures", "invariant", "assignable"].contains kind then
    return text
  let escaped := String.join (escapeSpecBindings (names.map Prod.fst) (specTokens text))
  let stx ← Parser.runParserCategory env `sol_member s!"{kind} {escaped};"
  let some member := (renameSpecSyntax params (if kind == "ensures" then rets else []) stx).reprint
    | throw "renamed specification cannot be printed"
  -- Keep the reader's raw directive/text representation; validation parses
  -- the complete member again before it can enter a contract.
  let member := member.trim
  let directivePrefix := kind ++ " "
  unless member.startsWith directivePrefix && member.endsWith ";" do
    throw "renamed specification has an unexpected member shape"
  return (member.drop directivePrefix.length).take (member.length - directivePrefix.length - 1)

private partial def renameLoopSyntax (names : List (String × String)) (stx : Syntax) : Syntax :=
  match stx with
  | `(sol_expr| $x:ident) =>
    match x.getId.components.map (·.toString) with
    | head :: tail =>
      match Semantics.lookupBy head names with
      | none => stx
      | some renamed =>
        let name := (renamed :: tail).foldl Lean.Name.str .anonymous
        let ident := Syntax.ident x.raw.getHeadInfo (name.toString.toSubstring) name []
        match stx with
        | .node info kind args => .node info kind (args.map fun a => if a == x.raw then ident else a)
        | _ => ident
    | [] => stx
  | _ =>
    match stx with
    | .node info kind args => .node info kind (args.map (renameLoopSyntax names))
    | _ => stx

private def rewriteLoopBindings (env : Environment) (names : List (String × String))
    (text : String) : Except String String := do
  unless names.any (fun (a, b) => a != b) do return text
  let text := text.trim
  let directive := text.takeWhile (!Char.isWhitespace ·)
  unless ["invariant", "decreases"].contains directive do return text
  let expression := (text.drop directive.length).trimLeft
  let escaped := String.join (escapeSpecBindings (names.map Prod.fst) (specTokens expression))
  let stx ← Parser.runParserCategory env `sol_expr escaped
  let some expression := (renameLoopSyntax names stx).reprint
    | throw "renamed loop specification cannot be printed"
  return directive ++ " " ++ expression

/-- The text of a contract with these members. -/
private def contractText (members : List String) : String :=
  s!"contract!\{ {" ".intercalate members} }"

/-- Why `s` does not elaborate as a contract, if it does not. -/
private def contractError? (s : Syntax) : TermElabM (Option String) :=
  withEnableInfoTree false <| withoutErrToSorry do
    tryCatchRuntimeEx (withCurrHeartbeats do
        let _ ← elabTermEnsuringType s (Lean.mkConst ``Contract)
        synthesizeSyntheticMVarsNoPostponing
        pure none)
      fun ex => do pure (some (← ex.toMessageData.toString))

/-- Why a function calling `calls` is left out, if one of them is. -/
private def callsLeftOut? (bad : List (String × String)) (calls : List String) : Option String :=
  calls.findSome? fun g =>
    (Semantics.lookupBy g bad).map fun m => s!"it calls `{g}`, which is left out: {m}"

@[command_elab solcImport]
def elabSolcImport : CommandElab := fun stx => do
  let ref := stx
  let path : String := stx[1].isStrLit?.getD ""
  let expected : Nat := stx[3].isNatLit?.getD 0
  let N : Lean.Name := stx[5].getId
  let ren : List (String × String) :=
    if stx[6].getNumArgs > 0 then
      stx[6][1].getSepArgs.toList.map fun p => (p[0].getId.toString, p[2].getId.toString)
    else []
  let file := System.FilePath.mk (← getFileName)
  let fixture := (file.parent.getD ".") / path
  let bytes ← IO.FS.readBinFile fixture
  let h := fnv1a64 bytes
  unless h.toNat == expected do
    throwError "{path} has the hash {hex16 h}, not the one named: \
      re-run scripts/solc-ast.mjs, which rewrites the literal"
  let some text := String.fromUTF8? bytes | throwError "{path} is not UTF-8"
  let j ← ofExcept (Json.parse text)
  let ast ← ofExcept (j.getObjVal? "ast")
  let source := ((j.getObjVal? "header").toOption.bind fun hd =>
    (hd.getObjValAs? String "source").toOption).getD "?"
  let srcName := (System.FilePath.mk source).fileName.getD source
  let env ← getEnv
  let c ← ofExcept (readContract ast N.getString! ren (!stx[7].isNone)
    (rewriteSpecBindings env) (rewriteLoopBindings env))
  let parse (cat : Lean.Name) (s : String) : Except String Syntax :=
    (Parser.runParserCategory env cat s).map (atRef ref)
  if !stx[7].isNone then
    -- A clause must parse alone. Otherwise `ensures false; requires false`
    -- could inject a second member and turn a failing specification vacuous.
    for m in c.members do
      let _ ← ofExcept (parse `sol_member m)
    for f in c.funs ++ c.ctor.toList do
      -- A refused body contributes no member or specification. Keep its
      -- unsupported row local, even when its unimported clause needs a
      -- renamed parameter (such as Solidity's `from`).
      if let .ok _ := f.body then
        for (kind, text) in f.specClauses do
          let _ ← ofExcept (parse `sol_member s!"{kind} {text};")
  -- the functions called, each checked alone first: one that does not
  -- expand is left out, with every function that calls it
  -- A malformed unused modifier must not enter every function's wrapper.
  -- Its users still fail expansion because the named modifier is absent.
  let modifierMembers := c.modifierMembers.filter fun m =>
    match parse `sol_member m with | .ok _ => true | .error _ => false
  let mut funMembers : Array String := #[]
  let mut badMembers : List (String × String) := []
  for (g, m) in c.funMembers do
    let calls := ((c.funs.find? (·.name == g)).map (·.calls)).getD []
    let r ← match callsLeftOut? badMembers calls,
        parse `term (contractText [" ".intercalate modifierMembers, m]) with
      | some e, _ => pure (some e)
      | none, .error e => pure (some s!"its declaration does not parse: {e}")
      | none, .ok s => liftTermElabM (contractError? s)
    match r with
    | none => funMembers := funMembers.push m
    | some e => badMembers := badMembers ++ [(g, e)]
  let at_ (f : SolcFun) (line : Nat) (msg : String) : String :=
    s!"{srcName}:{if line == 0 then f.line else line}: {msg}"
  -- the constructor, its member last (it may call every function): its row
  -- now if it is left out, else once its program is made
  let mut ctorRow : Option ImportRow := none
  let mut ctorMember : Option String := none
  if let some f := c.ctor then
    if let some m := callsLeftOut? badMembers f.calls then
      ctorRow := some (.ofFun f .unsupported (at_ f 0 m))
    else match f.body with
      | .error (.excluded m l) => ctorRow := some (.ofFun f .excluded (at_ f l m))
      | .error (.unsupported m l) => ctorRow := some (.ofFun f .unsupported (at_ f l m))
      | .ok ss => ctorMember := some (f.ctorMember (ss.map (·.2)))
  -- an implicit constructor's initializer that does not print, or calls a
  -- function left out: the initializers are left out, which a deployment of
  -- `N` would not run
  if c.ctor.isNone then
    if let some g := c.initGap then
      logWarning m!"solc_import: the initializers are left out: {g.msg}"
  -- the contract, with the initializers and the constructor if it expands
  -- with them, else without
  let plain := c.members ++ modifierMembers ++ funMembers.toList
  let mut memberList := plain
  -- a declared constructor left out takes the initializers with it: the
  -- implicit one would run them alone
  if (ctorMember.isSome || c.initMembers != c.members) && (c.ctor.isNone || ctorMember.isSome) then
    let full := c.initMembers ++ modifierMembers ++ funMembers.toList ++ ctorMember.toList
    let r ← match parse `term (contractText full) with
      | .error e => pure (some s!"it does not parse: {e}")
      | .ok s => liftTermElabM (contractError? s)
    match r, c.ctor, ctorMember with
    | none, _, _ => memberList := full
    | some e, some f, some _ =>
      ctorRow := some (.ofFun f .unsupported
        (at_ f 0 s!"the contract with its constructor and initializers: {e}"))
      ctorMember := none
    | some e, _, _ =>
      logWarning m!"solc_import: the initializers are left out: the contract with them: {e}"
  let ctStx ← ofExcept (parse `term (contractText memberList))
  liftTermElabM <| defineImportedContract N ctStx
  -- each body, read by the macros to a `List RawStmt` term
  let rawTy := mkApp (mkConst ``List [0]) (mkConst ``RawStmt)
  let mut rows : Array ImportRow := #[]
  let mut raws : Array (Nat × SolcFun × List (Nat × String) × Expr) := #[]
  for f in c.funs do
    let row := ImportRow.ofFun f
    if f.tag == .skip then
      rows := rows.push (row .skipped (at_ f 0 "tagged `@custom:key skip`"))
      continue
    if let some m := callsLeftOut? badMembers f.calls then
      rows := rows.push (row .unsupported (at_ f 0 m))
      continue
    match f.body with
    | .error (.excluded m l) => rows := rows.push (row .excluded (at_ f l m))
    | .error (.unsupported m l) => rows := rows.push (row .unsupported (at_ f l m))
    | .ok ss =>
      let ss := if f.modifierApps.isEmpty then ss else
        [(f.line, s!"{f.name}({", ".intercalate (f.params.map Prod.fst)})")]
      -- its return variables first, at their defaults
      let ss := (retNames f).map (fun (x, t) => (f.line, s!"{t} {x}")) ++ ss
      let params := f.params.map fun (x, t) => s!"{t} {x}; "
      let text := "sol_raw!{ " ++ String.join params ++ String.join (ss.map fun (_, s) => s ++ "; ") ++ "}"
      match parse `term text with
      | .error e => rows := rows.push (row .unsupported (at_ f 0 s!"the printed text does not parse: {e}"))
      | .ok s =>
        -- no info trees: the server would keep every expansion, all at this command
        let r ← liftTermElabM <| withEnableInfoTree false <| withoutErrToSorry do
          tryCatchRuntimeEx (withCurrHeartbeats do
              let e ← elabTermEnsuringType s rawTy
              synthesizeSyntheticMVarsNoPostponing
              let e ← instantiateMVars e
              if e.hasMVar then pure (Except.error "the macros leave a hole")
              else pure (.ok e))
            fun ex => do pure (.error (← ex.toMessageData.toString))
        match r with
        | .error m => rows := rows.push (row .unsupported (at_ f 0 m))
        | .ok e =>
          raws := raws.push (rows.size, f, ss, e)
          rows := rows.push (row .elaborated "")
  -- the contract and every body, evaluated once
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Contract)
    (mkApp (mkConst ``List [0]) rawTy)
  let val := mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Contract)
    (mkApp (mkConst ``List [0]) rawTy) (mkConst N) (← liftTermElabM <| mkListLit rawTy (raws.map (·.2.2.2)).toList)
  let (C, bodies) ← liftTermElabM <| unsafe evalExpr (Contract × List (List RawStmt)) pairTy val
  -- the typed elaborator on each, the program quoted back and checked
  for ((k, f, ss, _), raw) in raws.toList.zip bodies do
    let fail (msg : String) : Array ImportRow :=
      rows.set! k { rows[k]! with status := .unsupported, reason := msg }
    -- its loops, then its `return`s lowered, which moves statements: an
    -- error is then the function's
    let (params, raw) := raw.splitAt f.params.length
    let lower := !f.rets.isEmpty || raw.any RawStmt.hasReturn
    let rets := (retNames f).map (·.1)
    let lowered : ECtx → Except String (List RawStmt × (ECtx × Nat)) := fun Γ => do
      let (raw, st) ← ((lowerBodyLoops rets rets.length raw).run { funs := C.funs }).run
        (Γ, RawStmt.maxIdxs raw + 1)
      pure ((← if lower then lowerReturns rets raw else pure raw), st)
    let scope := paramCtx C params
    if let .ok Γ := scope then rows := rows.set! k { rows[k]! with paramTypes := (ECtx.toNCtx Γ).ctx }
    match scope >>= lowered with
    | .error m => rows := fail (at_ f 0 m)
    | .ok (raw, st) =>
      match elabProgAtS.go C 0 raw st (source := true) with
      | .error (j, m) =>
        rows := fail (at_ f (if lower then 0 else (ss[j]?.map (·.1)).getD 0) m)
      | .ok ⟨_, P⟩ =>
        let n : Lean.Name := N ++ Lean.Name.mkSimple f.name
        match ← liftCoreM (Prog.define n N P) with
        | none => pure ()
        | some m => rows := fail (at_ f 0 m)
  -- the constructor's program, a deployment: `constructor(x̄);` with its
  -- parameters in scope (`elabCtor`), the obligation's program
  if let (some f, some _) := (c.ctor, ctorMember) then
    let row := ImportRow.ofFun f
    if f.tag == .skip then
      ctorRow := some (row .skipped (at_ f 0 "tagged `@custom:key skip`"))
    else
      let raw : List RawStmt := [.call (.name "constructor") (f.params.map fun (x, _) => RawExpr.name x)]
      match (C.ctor.getD { params := [], body := [] }).paramCtx with
      | .error m => ctorRow := some (row .unsupported (at_ f 0 m))
      | .ok Γ =>
        let row := fun st msg => { (row st msg) with paramTypes := (ECtx.toNCtx Γ).ctx }
        match elabProgAtS.go C 0 raw (Γ, RawStmt.maxIdxs raw + 1) (source := true) with
        | .error (_, m) => ctorRow := some (row .unsupported (at_ f 0 m))
        | .ok ⟨_, P⟩ =>
          let n : Lean.Name := N ++ Lean.Name.mkSimple f.name
          match ← liftCoreM (Prog.define n N P) with
          | none => ctorRow := some (row .elaborated "")
          | some m => ctorRow := some (row .unsupported (at_ f 0 m))
  -- not compiled: compiling the scoped literals costs about half the import
  -- (TestSuite: 5.9 s); a reader evaluates a program's value (`#solc_show`,
  -- `Frontend/Problems.lean`'s `obligation`)
  let rowsTy := mkApp (mkConst ``List [0]) (mkConst ``ImportRow)
  let rep : Lean.Name := N ++ `report
  liftCoreM <| addAndCompile <| .defnDecl {
    name := rep, levelParams := [], type := rowsTy, value := toExpr (ctorRow.toList ++ rows.toList),
    hints := .abbrev, safety := .safe }

/-- The value of the imported program `n` (a literal: the import does not
compile it), its contexts' terms and its parameters' names, newest first. -/
def programValue (n : Lean.Name) (r : ImportRow) : CoreM (Expr × Expr × Expr × List Var) := do
  let ci ← getConstInfo n
  let ty := ci.type.consumeMData
  unless ty.isAppOfArity ``Prog 3 && ci.value?.isSome do throwError "{n} is not a scoped program"
  pure (ci.value!, ty.appFn!.appArg!, ty.appArg!, r.params.reverse.map fun (x, _) => Var.ofName x)

/-- `#solc_show N.f`: the imported program `N.f`, one statement per line
(`Prog.show`, its parameters named), its value evaluated. -/
syntax (name := solcShow) "#solc_show " ident : command

@[command_elab solcShow]
def elabSolcShow : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let N := n.getPrefix
  let rows ← liftTermElabM <| unsafe evalConst (List ImportRow) (N ++ `report)
  let some r := rows.find? (·.declName N == n) | throwError "{n} is no row of {N}"
  let (v, _, _, ns) ← liftCoreM <| programValue n r
  logInfo (← liftTermElabM do
    unsafe evalExpr String (mkConst ``String) (← mkAppM ``Prog.show #[toExpr ns, v]))

end Solidity.Frontend
