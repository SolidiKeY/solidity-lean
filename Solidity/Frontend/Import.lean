import Lean
import Solidity.Frontend.SolcJson

/-!
# `solc_import`: a contract from solc's AST, at elaboration time

`solc_import "f.ast.json" hash 0x… as N renaming Triple => FixedTriple`
reads a fixture of `scripts/solc-ast.mjs` (the path is relative to the
importing file) and defines

* `N : Contract`, the contract's state variables through `contract!{ … }`;
* `N.f : Prog N` for each function `f` that elaborates, its body read
  against `N` with its parameters as locals in scope;
* `N.report : List ImportRow`, one row per function: its solkey tag and
  parameters, what became of it and why, with the source line.

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
never fails on one function.
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
  let tags := s!"{(rows.filter (·.tag == .diamond)).length} diamond, \
    {(rows.filter (·.tag == .box)).length} box, {(rows.filter (·.tag == .skip)).length} skip"
  let head := s!"{rows.length} functions ({tags}): {count .elaborated} elaborated, \
    {count .skipped} skipped, {count .excluded} excluded, {count .unsupported} unsupported"
  let rest := rows.filter (·.status != .elaborated) |>.map fun r =>
    s!"{r.status.toStr} {r.name}: {r.reason}"
  "\n".intercalate (head :: rest)

/-- FNV-1a 64 over the bytes, `scripts/solc-ast.mjs`'s `hash`. -/
def fnv1a64 (b : ByteArray) : UInt64 :=
  b.foldl (fun h x => (h ^^^ x.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

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
def paramCtx (ps : List (String × String)) : Except String ECtx :=
  ps.reverse.mapM fun (x, t) =>
    match PrimTy.ofName? t, narrowTy? t with
    | some p, _ => pure (x, .val p)
    | none, some (p, n) => pure (x, .val p n)
    | none, none =>
      if t == "address payable" then pure (x, .val .uint)
      else throw s!"the parameter `{x}` has the type `{t}`, which is not a value type"

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
    throwError "{path} has the hash {(Nat.toDigits 16 h.toNat).asString}, not the one named: \
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
  -- the contract
  let members := " ".intercalate c.members
  let ctStx ← ofExcept (parse `term s!"contract!\{ {members} }")
  let id := mkIdentFrom ref N
  elabCommand (← `(command| def $id : Solidity.Contract := $(⟨ctStx⟩)))
  -- each body, read by the macros to a `List RawStmt` term
  let rawTy := mkApp (mkConst ``List [0]) (mkConst ``RawStmt)
  let mut rows : Array ImportRow := #[]
  let mut raws : Array (SolcFun × List (Nat × String) × Expr) := #[]
  let at_ (f : SolcFun) (line : Nat) (msg : String) : String :=
    s!"{srcName}:{if line == 0 then f.line else line}: {msg}"
  for f in c.funs do
    let row (st : ImportStatus) (msg : String) : ImportRow :=
      { name := f.name, tag := f.tag, params := f.params, status := st, reason := msg }
    if f.tag == .skip then
      rows := rows.push (row .skipped (at_ f 0 "tagged `@custom:key skip`"))
      continue
    match f.body with
    | .error (.excluded m l) => rows := rows.push (row .excluded (at_ f l m))
    | .error (.unsupported m l) => rows := rows.push (row .unsupported (at_ f l m))
    | .ok ss =>
      let text := "sol_raw!{ " ++ String.join (ss.map fun (_, s) => s ++ "; ") ++ "}"
      match parse `term text with
      | .error e => rows := rows.push (row .unsupported (at_ f 0 s!"the printed text does not parse: {e}"))
      | .ok s =>
        let r ← liftTermElabM <| withoutErrToSorry do
          try
            let e ← elabTermEnsuringType s rawTy
            synthesizeSyntheticMVarsNoPostponing
            let e ← instantiateMVars e
            if e.hasMVar then pure (Except.error "the macros leave a hole")
            else pure (.ok e)
          catch ex => pure (.error (← ex.toMessageData.toString))
        match r with
        | .error m => rows := rows.push (row .unsupported (at_ f 0 m))
        | .ok e =>
          rows := rows.push (row .elaborated "")
          raws := raws.push (f, ss, e)
  -- the contract and every body, evaluated once
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Contract)
    (mkApp (mkConst ``List [0]) rawTy)
  let val := mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Contract)
    (mkApp (mkConst ``List [0]) rawTy) (mkConst N) (← liftTermElabM <| mkListLit rawTy (raws.map (·.2.2)).toList)
  let (C, bodies) ← liftTermElabM <| unsafe evalExpr (Contract × List (List RawStmt)) pairTy val
  -- the typed elaborator on each, the program quoted back and checked
  let progTy := mkApp (mkConst ``Prog) (mkConst N)
  let mut defined : Array Lean.Name := #[]
  for ((f, ss, _), raw) in raws.toList.zip bodies do
    let some k := rows.findIdx? (·.name == f.name) | continue
    let fail (msg : String) : Array ImportRow :=
      rows.set! k { rows[k]! with status := .unsupported, reason := msg }
    match paramCtx f.params with
    | .error m => rows := fail (at_ f 0 m)
    | .ok Γ =>
      match elabProgAt.go C 0 raw (Γ, RawStmt.maxIdxs raw + 1) with
      | .error (j, m) => rows := fail (at_ f ((ss[j]?.map (·.1)).getD 0) m)
      | .ok P =>
        let n : Lean.Name := N ++ Lean.Name.mkSimple f.name
        let decl := Declaration.defnDecl {
          name := n, levelParams := [], type := progTy, value := Prog.quote (mkConst N) P,
          hints := .abbrev, safety := .safe }
        try
          liftCoreM <| addDecl decl
          defined := defined.push n
        catch ex => rows := fail (at_ f 0 s!"the kernel rejects the program: {← ex.toMessageData.toString}")
  liftCoreM <| compileDecls defined
  let rowsTy := mkApp (mkConst ``List [0]) (mkConst ``ImportRow)
  let rep : Lean.Name := N ++ `report
  liftCoreM <| addAndCompile <| .defnDecl {
    name := rep, levelParams := [], type := rowsTy, value := toExpr rows.toList,
    hints := .abbrev, safety := .safe }

end Solidity.Frontend
