import Lean
import Solidity.Frontend.SolcJson

/-!
# `solc_import`: a contract from solc's AST, at elaboration time

`solc_import "f.ast.json" hash 0x… as N renaming Triple => FixedTriple`
reads a fixture of `scripts/solc-ast.mjs` (the path is relative to the
importing file) and defines

* `N : Contract`, the contract's state variables and the functions called
  by name through `contract!{ … }`, each function checked alone first;
* `N.f : Prog N` for each function `f` that elaborates, its body read
  against `N` with its parameters as locals in scope, after its return
  variables declared at their defaults, its `return`s lowered
  (`lowerReturns`), as a call inlines it;
* `N.constructor : Prog N` for a declared constructor, a deployment:
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
  only its plain statement is not made (`solc_problems`).

Each body is printed as `sol` text (`SolcJson.lean`), parsed as
`sol_raw!{ … }` and elaborated to a `List RawStmt` term by the macros, the
one lowering path `sol[C]{ … }` takes.  Those terms and the contract are
then evaluated together, one `evalExpr`, and the typed elaborator runs on
each as ordinary compiled code (`elabProgAt.go`); `sol[C]{ … }` would
compile one program per function.  Its result is quoted back with every
proof `Eq.refl` (`Prog.quote`), so the kernel re-checks what it computed.

Lake does not track the fixture, so the command names its hash (FNV-1a 64
over the bytes) and refuses a fixture of another one; the script that
writes the fixture rewrites the literal, which makes Lake re-check the
importing module.

A function that does not elaborate is a row, not an error: the import
never fails on one function.  Each body's elaboration has its own
heartbeats and catches runtime exceptions too (`tryCatchRuntimeEx`), so a
body that exhausts its budget is a row as well.  A row is found by its
index, not its name, and the reader refuses an overloaded name or one named
`report` before any constant is made.
-/

namespace Solidity.Frontend

open Lean Elab Command Term Meta

/-- What the import made of a function. -/
inductive ImportStatus where
  /-- A constant `N.f : Prog N`. -/
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
  tag : Tag
  params : List (String × String)
  status : ImportStatus
  reason : String
  deriving Repr, Inhabited

deriving instance ToExpr for Tag
deriving instance ToExpr for ImportStatus
deriving instance ToExpr for ImportRow

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

/-- The value type a parameter's type names, with its width: what a
parameter may be (`paramCtx`), and what its obligation binds
(`solc_problems`). -/
def paramTy? (t : String) : Option (PrimTy × Nat) :=
  match PrimTy.ofName? t, narrowTy? t with
  | some p, _ => some (p, 256)
  | none, some pn => some pn
  | none, none => if t == "address payable" then some (.uint, 256) else none

/-- The parameters of a function as locals in scope, most recent first. -/
def paramCtx (ps : List (String × String)) : Except String ECtx :=
  ps.reverse.mapM fun (x, t) =>
    match paramTy? t with
    | some (p, n) => pure (x, .val p n)
    | none => throw s!"the parameter `{x}` has the type `{t}`, which is not a value type"

/-- A function's return variables, an unnamed one named as `contract!` names
it: `_ret`, or `_ret0`, `_ret1`, … of several (Lean's spelling; KeY names
them `ret0`, `ret1`, …). -/
def retNames (f : SolcFun) : List (String × String) :=
  f.rets.zipIdx.map fun ((x, t), i) =>
    (if !x.isEmpty then x else if f.rets.length == 1 then "_ret" else s!"_ret{i}", t)

syntax (name := solcImport) "solc_import " str " hash " num " as " ident
  (" renaming " sepBy1(ident " => " ident, ", "))? : command

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
  let c ← ofExcept (readContract ast N.getString! ren)
  let env ← getEnv
  let parse (cat : Lean.Name) (s : String) : Except String Syntax :=
    (Parser.runParserCategory env cat s).map (atRef ref)
  -- the functions called, each checked alone first: one that does not
  -- expand is left out, with every function that calls it
  let ctTy := Lean.mkConst ``Contract
  let mut funMembers : Array String := #[]
  let mut badMembers : List (String × String) := []
  for (g, m) in c.funMembers do
    let calls := ((c.funs.find? (·.name == g)).map (·.calls)).getD []
    let r ← match calls.findSome? fun h => (Semantics.lookupBy h badMembers).map (h, ·),
        parse `term s!"contract!\{ {m} }" with
      | some (h, e), _ => pure (some s!"it calls `{h}`, which is left out: {e}")
      | none, .error e => pure (some s!"its declaration does not parse: {e}")
      | none, .ok s => liftTermElabM <| withEnableInfoTree false <| withoutErrToSorry do
          tryCatchRuntimeEx (withCurrHeartbeats do
              let _ ← elabTermEnsuringType s ctTy
              synthesizeSyntheticMVarsNoPostponing
              pure none)
            fun ex => do pure (some (← ex.toMessageData.toString))
    match r with
    | none => funMembers := funMembers.push m
    | some e => badMembers := badMembers ++ [(g, e)]
  let at_ (f : SolcFun) (line : Nat) (msg : String) : String :=
    s!"{srcName}:{if line == 0 then f.line else line}: {msg}"
  -- the constructor, its member last (it may call every function): its row
  -- now if it is left out, else once its program is made
  let ctorRowOf (f : SolcFun) (st : ImportStatus) (msg : String) : ImportRow :=
    { name := f.name, tag := f.tag, params := f.params, status := st, reason := msg }
  let mut ctorRow : Option ImportRow := none
  let mut ctorMember : Option String := none
  if let some f := c.ctor then
    if let some (g, m) := f.calls.findSome? fun g => (Semantics.lookupBy g badMembers).map (g, ·) then
      ctorRow := some (ctorRowOf f .unsupported (at_ f 0 s!"it calls `{g}`, which is left out: {m}"))
    else match f.body with
      | .error (.excluded m l) => ctorRow := some (ctorRowOf f .excluded (at_ f l m))
      | .error (.unsupported m l) => ctorRow := some (ctorRowOf f .unsupported (at_ f l m))
      | .ok ss => ctorMember := some (f.ctorMember (ss.map (·.2)))
  -- the contract, with the initializers and the constructor if it expands
  -- with them, else without
  let plain := c.members ++ funMembers.toList
  let mut memberList := plain
  -- a declared constructor left out takes the initializers with it: the
  -- implicit one would run them alone
  if (ctorMember.isSome || c.initMembers != c.members) && (c.ctor.isNone || ctorMember.isSome) then
    let full := c.initMembers ++ funMembers.toList ++ ctorMember.toList
    let r ← match parse `term s!"contract!\{ {" ".intercalate full} }" with
      | .error e => pure (some s!"it does not parse: {e}")
      | .ok s => liftTermElabM <| withEnableInfoTree false <| withoutErrToSorry do
          tryCatchRuntimeEx (withCurrHeartbeats do
              let _ ← elabTermEnsuringType s ctTy
              synthesizeSyntheticMVarsNoPostponing
              pure none)
            fun ex => do pure (some (← ex.toMessageData.toString))
    match r, c.ctor, ctorMember with
    | none, _, _ => memberList := full
    | some e, some f, some _ =>
      ctorRow := some (ctorRowOf f .unsupported
        (at_ f 0 s!"the contract with its constructor and initializers: {e}"))
      ctorMember := none
    | some e, _, _ =>
      logWarning m!"solc_import: the initializers are left out: the contract with them: {e}"
  let ctStx ← ofExcept (parse `term s!"contract!\{ {" ".intercalate memberList} }")
  let id := mkIdentFrom ref N
  elabCommand (← `(command| def $id : Solidity.Contract := $(⟨ctStx⟩)))
  -- each body, read by the macros to a `List RawStmt` term
  let rawTy := mkApp (mkConst ``List [0]) (mkConst ``RawStmt)
  let mut rows : Array ImportRow := #[]
  let mut raws : Array (Nat × SolcFun × List (Nat × String) × Expr) := #[]
  for f in c.funs do
    let row (st : ImportStatus) (msg : String) : ImportRow :=
      { name := f.name, tag := f.tag, params := f.params, status := st, reason := msg }
    if f.tag == .skip then
      rows := rows.push (row .skipped (at_ f 0 "tagged `@custom:key skip`"))
      continue
    if let some (g, m) := f.calls.findSome? fun g => (Semantics.lookupBy g badMembers).map (g, ·) then
      rows := rows.push (row .unsupported (at_ f 0 s!"it calls `{g}`, which is left out: {m}"))
      continue
    match f.body with
    | .error (.excluded m l) => rows := rows.push (row .excluded (at_ f l m))
    | .error (.unsupported m l) => rows := rows.push (row .unsupported (at_ f l m))
    | .ok ss =>
      -- its return variables first, at their defaults
      let ss := (retNames f).map (fun (x, t) => (f.line, s!"{t} {x}")) ++ ss
      let text := "sol_raw!{ " ++ String.join (ss.map fun (_, s) => s ++ "; ") ++ "}"
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
  let progTy := mkApp (mkConst ``Prog) (mkConst N)
  let mut defined : Array Lean.Name := #[]
  for ((k, f, ss, _), raw) in raws.toList.zip bodies do
    let fail (msg : String) : Array ImportRow :=
      rows.set! k { rows[k]! with status := .unsupported, reason := msg }
    -- its `return`s lowered, which moves statements: an error is then the function's
    let lower := !f.rets.isEmpty || raw.any RawStmt.hasReturn
    match paramCtx f.params, (if lower then lowerReturns ((retNames f).map (·.1)) raw else pure raw) with
    | .error m, _ | _, .error m => rows := fail (at_ f 0 m)
    | .ok Γ, .ok raw =>
      match elabProgAt.go C 0 raw (Γ, RawStmt.maxIdxs raw + 1) with
      | .error (j, m) =>
        rows := fail (at_ f (if lower then 0 else (ss[j]?.map (·.1)).getD 0) m)
      | .ok P =>
        let n : Lean.Name := N ++ Lean.Name.mkSimple f.name
        let decl := Declaration.defnDecl {
          name := n, levelParams := [], type := progTy, value := Prog.quote (mkConst N) P,
          hints := .abbrev, safety := .safe }
        let ok ← liftCoreM <| tryCatchRuntimeEx (do addDecl decl; pure (Except.ok ()))
          fun ex => do pure (.error (← ex.toMessageData.toString))
        match ok with
        | .ok () => defined := defined.push n
        | .error m => rows := fail (at_ f 0 s!"the kernel rejects the program: {m}")
  -- the constructor's program, a deployment: `constructor(x̄);` with its
  -- parameters in scope (`elabCtor`), the obligation's program
  if let (some f, some _) := (c.ctor, ctorMember) then
    let row := ctorRowOf f
    if f.tag == .skip then
      ctorRow := some (row .skipped (at_ f 0 "tagged `@custom:key skip`"))
    else
      let raw : List RawStmt := [.call (.name "constructor") (f.params.map fun (x, _) => RawExpr.name x)]
      match paramCtx f.params with
      | .error m => ctorRow := some (row .unsupported (at_ f 0 m))
      | .ok Γ =>
        match elabProgAt.go C 0 raw (Γ, RawStmt.maxIdxs raw + 1) with
        | .error (_, m) => ctorRow := some (row .unsupported (at_ f 0 m))
        | .ok P =>
          let n : Lean.Name := N ++ Lean.Name.mkSimple f.name
          let decl := Declaration.defnDecl {
            name := n, levelParams := [], type := progTy, value := Prog.quote (mkConst N) P,
            hints := .abbrev, safety := .safe }
          let ok ← liftCoreM <| tryCatchRuntimeEx (do addDecl decl; pure (Except.ok ()))
            fun ex => do pure (.error (← ex.toMessageData.toString))
          match ok with
          | .ok () =>
            defined := defined.push n
            ctorRow := some (row .elaborated "")
          | .error m => ctorRow := some (row .unsupported (at_ f 0 s!"the kernel rejects the program: {m}"))
  -- compiled for `sol_prove`; a failure here leaves the definitions, uncompiled
  let compiled ← liftCoreM <| tryCatchRuntimeEx (do compileDecls defined; pure none)
    fun ex => do pure (some (← ex.toMessageData.toString))
  if let some m := compiled then
    logWarning m!"solc_import: the programs are defined but not compiled: {m}"
  let rowsTy := mkApp (mkConst ``List [0]) (mkConst ``ImportRow)
  let rep : Lean.Name := N ++ `report
  liftCoreM <| addAndCompile <| .defnDecl {
    name := rep, levelParams := [], type := rowsTy, value := toExpr (ctorRow.toList ++ rows.toList),
    hints := .abbrev, safety := .safe }

end Solidity.Frontend
