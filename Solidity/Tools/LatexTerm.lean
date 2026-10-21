import LeanTeX
import Solidity.Calculus.Chains

/-!
# Scoped terms, updates and formulas as LaTeX

The renderer reads a scoped term, update or formula from its `Expr`, as the
printers of `Calculus/PrintTerm.lean` and `Calculus/PrintStmt.lean` do (their
views: `viewTmS`, `updPiecesS`, `viewF`, the name stacks), so it knows each
symbol by its constructor and each term by its sort.  A program is printed by
the scoped program printer (`ppItemsS`) and set verbatim as code.

**Two backends** (`Backend`): `plain`, self-contained (amsmath and amssymb),
and `macros`, which writes the pre-licenciate write-up's macros (`macros.sty`:
`\TFind{\intS}`, `\save`, `\storage`, `\upd`, `\dlf`, `\pField`, …) so that
the write-up's style file controls the look.  Every symbol's spelling, in both,
is one row of `symbols`; a symbol with no row prints as `\mathsf{ctor}(…)`
and the export records a warning (`uncovered` lists the constructors without
a row).  Sorts subscript the symbols that KeY indexes by their result sort
(`find`, `select`, `read`, `delValue`), read off the symbol's type
arguments (its `PrimTy` or `Ty`; a `select` is a `Struct`).

**Line breaking.**  A rendered line is a `Doc`: text with break points at
update elements, connectives and arguments, each at its nesting depth.
`Doc.lines` breaks a line longer than the width at the shallowest point.
-/

namespace Solidity.Latex

open Lean Meta

/-! ## Options -/

/-- `plain`: amsmath/amssymb only; `macros`: the write-up's macros (`macros.sty`). -/
inductive Backend where
  | plain
  | macros
  deriving DecidableEq, Repr, Inhabited

/-- How a derivation's arrows show their rule: not at all (the write-up's),
over the arrow, or as a tag at the right. -/
inductive Labels where
  | none
  | over
  | tag
  deriving DecidableEq, Repr, Inhabited

/-- The bookkeeping steps a derivation collapses into one `\rightsquigarrow^{*}`. -/
def defaultCollapse : List String :=
  ["valueDeclSkip", "assertConditionCapture", "localValueDeclInitDrop", "binopAssignment",
    "assertSimple", "sequentialToParallel"]

/-- What the export prints, and how. -/
structure Options where
  backend : Backend := .plain
  /-- The width of a line, in characters of the source text it prints. -/
  width : Nat := 90
  /-- The arrows' labels; `none` takes the backend's default (`over` for
  `plain`, none for `macros`). -/
  labels : Option Labels := none
  /-- Steps of a derivation collapsed into one `\rightsquigarrow^{*}`, by rule name. -/
  collapse : List String := defaultCollapse
  /-- Whether the strategy's grouped links (`~*>`) collapse too. -/
  groups : Bool := true
  /-- Whether a derivation's leading premise `A → ψ` is stated as `\Gamma = \{A\}`. -/
  premise : Bool := true
  /-- Whether a law's instance is shown on a side line; `none` takes the
  backend's default (on for `macros`). -/
  sides : Option Bool := none
  /-- Whether symbols carry their sort as a subscript. -/
  sorts : Bool := true
  /-- Whether a generated derivation goes on past the program (the rewrites
  to its last line), or stops where the strategy does. -/
  past : Bool := true
  /-- Visible symbol keys and exact document destinations. Only mapped heads
  become links; the empty list preserves the original output. -/
  definitions : List (String × String) := []
  deriving Inhabited

def Options.macros (o : Options) : Bool := o.backend == .macros

def Options.labelsOr (o : Options) : Labels :=
  o.labels.getD (if o.macros then .none else .over)

def Options.sidesOr (o : Options) : Bool := o.sides.getD o.macros

register_option latex.sol.macros : Bool := {
  defValue := false
  descr := "the LaTeX export of scoped formulas writes the write-up's macros (`Tools/LatexTerm.lean`)"
}

register_option latex.sol.width : Nat := {
  defValue := 90
  descr := "the width at which the LaTeX export breaks a line"
}

register_option latex.sol.definitions : String := {
  defValue := "[]"
  descr := "internal JSON map set by #latex_definition_targets"
}

/-- The options `set_option latex.sol.*` gives. -/
def Options.ofCore (o : Lean.Options) : Options :=
  { backend := if latex.sol.macros.get o then .macros else .plain
    width := latex.sol.width.get o
    definitions := ((Json.parse (latex.sol.definitions.get o)).bind
      (fromJson? (α := List (String × String)))).toOption.getD [] }

/-! ## Text -/

/-- Escape literal text for a LaTeX text or identifier argument. -/
def escape (s : String) : String :=
  String.join <| s.toList.map fun c => match c with
    | '\\' => "\\textbackslash{}"
    | '{' => "\\{" | '}' => "\\}"
    | '_' => "\\_" | '%' => "\\%" | '#' => "\\#" | '&' => "\\&"
    | '$' => "\\$" | '^' => "\\textasciicircum{}" | '~' => "\\textasciitilde{}"
    | _ => String.singleton c

/-- Preserve LeanTeX's Greek/subscript spelling while escaping TeX specials. -/
def identLatex (s : String) : String :=
  go s.toList ""
where
  sub (s : String) : String := if s.isEmpty then "" else "_{" ++ s ++ "}"
  go : List Char → String → String
    | [], acc => sub acc
    | c :: cs, acc =>
      let t := if "%&#$\\^~_{}".contains c then escape (String.singleton c)
        else c.toLatex
      if t.startsWith "_" then go cs (acc ++ String.mk (t.toList.drop 1))
      else
        let delim := if t.startsWith "\\" && t.toList.all (fun c => c == '\\' || c.isAlpha)
            && cs.head?.any Char.isAlpha then "{}" else ""
        sub acc ++ t ++ delim ++ go cs ""

/-- An identifier in math italic: `\mathit{d2}`; a lone Greek letter bare. -/
def identIt (s : String) : String :=
  let t := identLatex s
  if s.length == 1 && t.startsWith "\\" then t else "\\mathit{" ++ t ++ "}"

/-! ## Documents -/

/-- A rendered line: text, and the places it may break, each at the depth of
the structure it is in. -/
inductive Doc where
  | text (s : String) (w : Nat)
  | cat (ds : Array Doc)
  | brk
  | nest (d : Doc)
  /-- No break inside: a macro's argument (an `&` there would not align). -/
  | whole (d : Doc)
  deriving Inhabited

/-- A piece of a flattened line. -/
inductive Tok where
  | text (s : String) (w : Nat)
  | brk (d : Nat)
  deriving Inhabited

partial def Doc.toks (d : Doc) (depth : Nat := 0) (acc : Array Tok := #[]) : Array Tok :=
  match d with
  | .text s w => acc.push (.text s w)
  | .cat ds => ds.foldl (fun acc d => d.toks depth acc) acc
  | .brk => acc.push (.brk depth)
  | .nest d => d.toks (depth + 1) acc
  | .whole d => d.toks depth #[] |>.foldl (fun acc t => match t with
      | .text .. => acc.push t
      | .brk _ => acc) acc

def Tok.render (ts : Array Tok) : String :=
  (ts.foldl (fun s t => match t with | .text x _ => s ++ x | .brk _ => s) "").trim

/-- The line unbroken. -/
def Doc.flat (d : Doc) : String := Tok.render d.toks

/-- The source width of a line. -/
def Doc.width (d : Doc) : Nat :=
  d.toks.foldl (fun n t => match t with | .text _ w => n + w | .brk _ => n) 0

/-- The line broken where it is longer than `limit`, the first line starting
at `start` and the others at `cont`: each break at the shallowest point of
the line so far (the latest of those), past a third of the line. -/
def Doc.lines (d : Doc) (limit : Nat) (start : Nat := 0) (cont : Nat := 4) : Array String := Id.run do
  let ts := d.toks
  let mut out := #[]
  let mut i := 0
  let mut ind := start
  while i < ts.size do
    let mut w := ind
    let mut cands : Array (Nat × Nat × Nat) := #[]
    let mut cut : Option Nat := none
    let mut j := i
    while j < ts.size && cut.isNone do
      match ts[j]! with
      | .brk dp => if w > ind then cands := cands.push (j, dp, w)
      | .text _ tw =>
        w := w + tw
        if w > limit && !cands.isEmpty then
          let far := cands.filter fun (_, _, cw) => cw ≥ ind + (limit - min limit ind) / 3
          let cs := if far.isEmpty then cands else far
          let best := cs.foldl (fun (b : Nat × Nat × Nat) c => if c.2.1 ≤ b.2.1 then c else b) cs[0]!
          cut := some best.1
      j := j + 1
    match cut with
    | some k =>
      out := out.push (Tok.render (ts.extract i k))
      i := k + 1
    | none =>
      out := out.push (Tok.render (ts.extract i ts.size))
      i := ts.size
    ind := cont
  return out.filter (!·.isEmpty)

namespace Doc

/-- TeX `s` that prints as `w` characters of source. -/
def tx (s : String) (w : Nat := 1) : Doc := .text s w

instance : Append Doc := ⟨fun a b => .cat #[a, b]⟩

def join (ds : Array Doc) : Doc := .cat ds

/-- `ds` separated by `sep`, a break after each separator. -/
def sepBy (sep : Doc) (ds : Array Doc) : Doc := Id.run do
  let mut out := #[]
  for h : i in [0:ds.size] do
    if i > 0 then out := out.push sep |>.push .brk
    out := out.push ds[i]
  return .cat out

/-- `(d)` -/
def paren (d : Doc) : Doc := .cat #[tx "(", .nest d, tx ")"]

/-- `f(a, b, …)`, the arguments one level deeper. -/
def app (f : Doc) (args : Array Doc) : Doc :=
  .cat #[f, tx "(", .nest (sepBy (tx ", " 2) args), tx ")"]

/-- An infix operator: a break before it. -/
def bin (a : Doc) (op : String) (w : Nat) (b : Doc) : Doc :=
  .cat #[a, tx " " 0, .brk, tx (op ++ " ") (w + 2), b]

end Doc

/-- An identifier, `\mathit{x}`. -/
def Doc.ident (s : String) : Doc := .tx (identIt s) s.length

/-- A keyword, `\mathit{true}`. -/
def Doc.kw (s : String) : Doc := .tx ("\\mathit{" ++ s ++ "}") s.length

/-! ## The symbol table

One row per constructor: its spelling in the plain backend and in the macros
backend, and in the latter the macro that takes its sort as an argument
(`\TFind{\intS}`), if KeY indexes it so.  The constructors the renderer
reads by their shape (literals, paths, infix operators, the array writes
KeY spells as nested `save`s) have a row too: their head, or `""`. -/

/-- A symbol's spellings. -/
structure Sym where
  ctor : Lean.Name
  plain : String
  macroS : String
  /-- The macro over the result sort (`\TFind`), if any. -/
  sorted : Option String := none
  deriving Inhabited

/-- The symbols of `Op0` … `Op3`, `Tm`, `Rhs` and `UpdElem`. -/
def symbols : Array Sym := #[
  -- Op0
  ⟨``Op0.lit, "", "", none⟩, ⟨``Op0.env, "", "", none⟩, ⟨``Op0.root, "", "", none⟩,
  ⟨``Op0.storage, "\\mathit{storage}", "\\storage", none⟩,
  ⟨``Op0.memory, "\\mathit{memory}", "\\mem", none⟩,
  ⟨``Op0.mtSt, "\\mathit{mtSt}", "\\eStor", none⟩,
  ⟨``Op0.member, "", "", none⟩, ⟨``Op0.zlit, "", "", none⟩,
  -- Op1
  ⟨``Op1.unop, "", "", none⟩,
  ⟨``Op1.net, "\\mathit{net}", "\\net", none⟩,
  ⟨``Op1.delValue, "\\mathit{delValue}", "\\delValueSym", some "\\TDelValue"⟩,
  ⟨``Op1.field, "", "", none⟩, ⟨``Op1.next, "", "", none⟩, ⟨``Op1.sval, "", "", none⟩,
  ⟨``Op1.newArr, "\\mathit{newArr}", "\\funcFont{newArr}", none⟩,
  ⟨``Op1.alloc, "\\mathit{freshId}", "\\funcFont{freshId}", none⟩,
  ⟨``Op1.mfield, "", "", none⟩,
  ⟨``Op1.addM, "\\mathit{addM}", "\\funcFont{addM}", none⟩,
  ⟨``Op1.mval, "", "", none⟩, ⟨``Op1.ref, "", "", none⟩,
  ⟨``Op1.wt, "\\mathit{wt}", "\\wellformedSym", none⟩,
  ⟨``Op1.select, "\\mathit{select}", "\\select", some "\\TSelect"⟩,
  ⟨``Op1.selectIn, "\\mathit{select}", "\\select", some "\\TSelect"⟩,
  ⟨``Op1.fieldIn, "", "", none⟩,
  ⟨``Op1.toInt, "\\mathit{toInt}", "", none⟩,
  -- KeY erases the typed adapter: the macros backend prints its source alone
  ⟨``Op1.fixedCopy, "\\mathit{fixedCopy}", "", none⟩,
  -- Lean only: solkey has no such symbol
  ⟨``Op1.cleanTail, "\\mathit{cleanTail}", "\\mathit{cleanTail}", none⟩,
  -- Op2
  ⟨``Op2.binop, "", "", none⟩,
  ⟨``Op2.find, "\\mathit{find}", "\\find", some "\\TFind"⟩,
  ⟨``Op2.len, "\\mathit{find}", "\\find", some "\\TFind"⟩,
  ⟨``Op2.read, "\\mathit{read}", "\\readMem", some "\\TReadMem"⟩,
  ⟨``Op2.mlen, "\\mathit{read}", "\\readMem", some "\\TReadMem"⟩,
  ⟨``Op2.at, "", "", none⟩, ⟨``Op2.nextIn, "", "", none⟩,
  ⟨``Op2.delAt, "\\mathit{delAt}", "\\delAtSym", none⟩,
  ⟨``Op2.pushSlot, "\\mathit{save}", "\\save", none⟩,
  ⟨``Op2.pop, "\\mathit{save}", "\\save", none⟩,
  ⟨``Op2.shrink, "\\mathit{save}", "\\save", none⟩,
  ⟨``Op2.extend, "\\mathit{save}", "\\save", none⟩,
  ⟨``Op2.sfind, "\\mathit{find}", "\\find", some "\\TFind"⟩,
  ⟨``Op2.copyMem, "\\mathit{copyMem}", "\\copyMem", none⟩,
  ⟨``Op2.iread, "\\mathit{read}", "\\readRMem", none⟩,
  ⟨``Op2.copy, "\\mathit{freshId}", "\\funcFont{freshId}", none⟩,
  ⟨``Op2.mat, "", "", none⟩,
  ⟨``Op2.copySt, "\\mathit{copySt}", "\\copySt", none⟩,
  ⟨``Op2.findIn, "\\mathit{find}", "\\find", some "\\TFind"⟩,
  ⟨``Op2.delAtIn, "\\mathit{delAt}", "\\delAtSym", none⟩,
  ⟨``Op2.sfindIn, "\\mathit{find}", "\\find", some "\\TFind"⟩,
  ⟨``Op2.zbin, "", "", none⟩, ⟨``Op2.zcmp, "", "", none⟩,
  -- Op3
  ⟨``Op3.ite, "", "", none⟩,
  ⟨``Op3.save, "\\mathit{save}", "\\save", none⟩,
  ⟨``Op3.push, "\\mathit{save}", "\\save", none⟩,
  ⟨``Op3.atIn, "", "", none⟩,
  ⟨``Op3.write, "\\mathit{write}", "\\writeMem", none⟩,
  ⟨``Op3.saveIn, "\\mathit{save}", "\\save", none⟩,
  ⟨``Op3.modular, "", "", none⟩,
  -- Tm: the locals by their names
  ⟨``Tm.pvV, "", "", none⟩, ⟨``Tm.pvP, "", "", none⟩, ⟨``Tm.pvS, "", "", none⟩,
  ⟨``Tm.pvI, "", "", none⟩, ⟨``Tm.pvZ, "", "", none⟩,
  ⟨``Tm.netOf, "\\mathit{net}", "\\select", some "\\TSelect"⟩,
  ⟨``Tm.app0, "", "", none⟩, ⟨``Tm.app1, "", "", none⟩, ⟨``Tm.app2, "", "", none⟩,
  ⟨``Tm.app3, "", "", none⟩,
  -- Rhs
  ⟨``Rhs.val, "", "", none⟩, ⟨``Rhs.path, "", "", none⟩,
  ⟨``Rhs.unset, "\\mathit{unset}", "\\mathit{unset}", none⟩,
  ⟨``Rhs.mref, "", "", none⟩, ⟨``Rhs.store, "", "", none⟩,
  ⟨``Rhs.saveNet, "\\mathit{net}", "\\net", none⟩,
  ⟨``Rhs.saveNetMt, "\\mathit{mtSt}", "\\eStor", none⟩,
  ⟨``Rhs.zint, "", "", none⟩,
  -- UpdElem
  ⟨``UpdElem.local, "", "", none⟩,
  ⟨``UpdElem.storage, "\\mathit{storage}", "\\storage", none⟩,
  ⟨``UpdElem.memory, "\\mathit{memory}", "\\mem", none⟩,
  ⟨``UpdElem.selfBalance, "\\mathit{selfBalance}", "\\selfBalance", none⟩,
  ⟨``UpdElem.net, "\\mathit{net}", "\\net", none⟩,
  ⟨``UpdElem.pay, "\\mathit{net}", "\\net", none⟩,
  ⟨``UpdElem.netMt, "\\mathit{net}", "\\net", none⟩,
  ⟨``UpdElem.setBalance, "\\mathit{selfBalance}", "\\selfBalance", none⟩]

/-- The visible name of a table entry, shared by its typed variants (`len`
and `findIn` both print `find`). Paths, literals and invisible adapters have
no function head to link. -/
def Sym.definitionKey? (s : Sym) : Option String :=
  if s.plain.startsWith "\\mathit{" && s.plain.endsWith "}" then
    some ((s.plain.drop 8).dropRight 1)
  else none

/-- Keys accepted in a document's definition map. -/
def definitionKeys : Array String :=
  ((symbols.filterMap Sym.definitionKey?).toList ++ ["store", "at", "atMap"]).eraseDups.toArray

/-- Exact hyperref destination names, restricted to literal ASCII characters
so they cannot introduce TeX commands or group delimiters. -/
def validDefinitionTarget (s : String) : Bool :=
  !s.isEmpty && s.toList.all (fun c =>
    (c.toNat < 128 && c.isAlphanum) || ":_./-".contains c)

/-- The inductives whose every constructor needs a row of `symbols`. -/
def symbolFamilies : List Lean.Name :=
  [``Op0, ``Op1, ``Op2, ``Op3, ``Tm, ``Rhs, ``UpdElem]

/-- The constructors of `symbolFamilies` without a row of `symbols`. -/
def uncovered : MetaM (List Lean.Name) := do
  let mut out := []
  for f in symbolFamilies do
    let .inductInfo i ← getConstInfo f | throwError "{f} is no inductive"
    for c in i.ctors do
      unless symbols.any (·.ctor == c) do out := out ++ [c]
  return out

/-! ## The renderer's monad -/

/-- The options, and the warnings an export collects (a symbol with no
spelling, a part that does not compute). -/
abbrev RM := ReaderT Options (StateRefT (Array String) MetaM)

def warn (s : String) : RM Unit :=
  modify fun ws => if ws.contains s then ws else ws.push s

def macrosM : RM Bool := return (← read).macros

/-- A `PrM` of the scoped printers, block ends printed. -/
def pr {α : Type} (k : Delab.PrM α) : RM α := liftM (k.run { blockEnds := true } : MetaM α)

/-- The spelling of the symbol `c` in the backend; `\mathsf{c}` and a warning
where it has none. -/
def bareSymOf (c : Lean.Name) : RM String := do
  let some s := symbols.find? (·.ctor == c) | do
    warn s!"no LaTeX spelling for {c}: printed as \\mathsf"
    return "\\mathsf{" ++ escape (c.getString!) ++ "}"
  return if ← macrosM then s.macroS else s.plain

/-- Link one printed function head, leaving its arguments and layout widths
alone. The direct MetaM API rejects unsafe targets by warning and leaving
the spelling unchanged; command options reject them before rendering. -/
def definitionLink (key text : String) : RM String := do
  let some (_, target) := (← read).definitions.find? (·.1 == key) | return text
  unless validDefinitionTarget target do
    warn s!"invalid definition target for {key}: link omitted"
    return text
  return "\\hyperlink{" ++ target ++ "}{" ++ text ++ "}"

def symbolLink (c : Lean.Name) (text : String) : RM String := do
  if c == ``Tm.netOf && (← macrosM) then return ← definitionLink "select" text
  let some row := symbols.find? (·.ctor == c) | return text
  let some key := row.definitionKey? | return text
  definitionLink key text

/-- A symbol's spelling, linked to its configured document definition. -/
def symOf (c : Lean.Name) : RM String := do
  symbolLink c (← bareSymOf c)

/-- A macro or plain spelling: the macro, else `\mathit{plain}`. -/
def spell (plain macroS : String) : RM String := do
  return if ← macrosM then macroS else "\\mathit{" ++ plain ++ "}"

/-! ## Sorts -/

/-- KeY's sort of a primitive type. -/
def primSort (p : Expr) : RM String := do
  let mac ← macrosM
  match_expr (← whnf p) with
  | PrimTy.bool => return if mac then "\\boolS" else "\\mathsf{bool}"
  | PrimTy.uint => return if mac then "\\intS" else "\\mathsf{int}"
  | PrimTy.int => return if mac then "\\intS" else "\\mathsf{int}"
  | _ =>
    let n := (← fvarName? p).getD "T"
    return "\\mathsf{" ++ escape n ++ "}"

/-- KeY's sort of what a storage holds at the type `T`: a word's, or `Struct`. -/
def tySort (T : Expr) : RM String := do
  let T ← whnf T
  if T.isAppOfArity ``Ty.prim 1 then return ← primSort T.appArg!
  return if ← macrosM then "\\Struct" else "\\mathsf{Struct}"

/-- A symbol over its sort: `\TFind{\intS}` in the macros backend, `\mathit{find}_{\mathsf{int}}`
in the plain backend; without sorts, the symbol. -/
def sortedSym (c : Lean.Name) (sort : RM String) : RM String := do
  let s ← bareSymOf c
  unless (← read).sorts do return ← symbolLink c s
  let some row := symbols.find? (·.ctor == c) | return s
  let srt ← sort
  if ← macrosM then
    if let some m := row.sorted then return ← symbolLink c (m ++ "{" ++ srt ++ "}")
    return ← symbolLink c s
  symbolLink c (s ++ "_{" ++ srt ++ "}")

/-- Preserve the paper's composite macro when it needs no links; expose its
select/at/net heads when mapped. Keep the macro's existing layout width. -/
def netSelectDoc (arg : Doc) : RM Doc := do
  unless ← macrosM do return .app (.tx (← symOf ``Op1.net) 3) #[arg]
  unless (← read).definitions.any (fun d => ["select", "at", "net"].contains d.1) do
    return .cat #[.tx "\\netSelect{" 10, .whole arg, .tx "}"]
  -- The existing netSelect macro always includes its sort, even when the
  -- ordinary symbol renderer has sorts disabled. Preserve that spelling.
  let select ← withReader (fun o => { o with sorts := true })
    (sortedSym ``Tm.netOf (primSort (mkConst ``PrimTy.int)))
  let net ← symOf ``Op1.net
  let atHead ← definitionLink "at" "\\at"
  return .cat #[.tx select 6, .tx ("(" ++ net ++ ", " ++ atHead ++ "(") 4,
    .whole arg, .tx "))" 1]

/-! ## Terms -/

open Solidity.Delab in
/-- A literal of `Op0.lit`: a number, a Boolean, the default, a variable. -/
def litDoc (v : Expr) : RM (Option Doc) := do
  if v.isAppOfArity ``PrimTy.dflt 1 then return some (.kw "defVal")
  if let some n ← fvarName? v then return some (.ident n)
  let v0 := (← instantiateMVars v).consumeMData
  if v0.isAppOfArity ``PrimTy.ofLit 3 then
    if let some n ← intOf? (v0.getArg! 1) then return some (.tx (toString n) (toString n).length)
  let v' ← whnf v
  if v'.isAppOfArity ``PrimTy.dflt 1 then return some (.kw "defVal")
  match_expr v' with
  | Subtype.mk _ _ n _ =>
    let some n ← intOf? n | return none
    return some (.tx (toString n) (toString n).length)
  | Bool.true => return some (.kw "true")
  | Bool.false => return some (.kw "false")
  | _ => return none

/-- An infix operator of `BinOp`: its spelling, width and precedence. -/
def binOpTeX (op : Expr) : RM (Option (String × Nat × Nat)) := do
  if let some n ← fvarName? op then return some ("\\oplus_{" ++ identIt n ++ "}", 1, 9)
  let some c := (← whnf op).constName? | return none
  return match c with
    | ``BinOp.add => some ("+", 1, 9) | ``BinOp.sub => some ("-", 1, 9)
    | ``BinOp.mul => some ("\\cdot", 1, 10) | ``BinOp.div => some ("/", 1, 10)
    | ``BinOp.mod => some ("\\bmod", 3, 10) | ``BinOp.pow => some ("\\mathbin{**}", 2, 11)
    | ``BinOp.lt => some ("<", 1, 4) | ``BinOp.gt => some (">", 1, 4)
    | ``BinOp.le => some ("\\le", 2, 4) | ``BinOp.ge => some ("\\ge", 2, 4)
    | ``BinOp.eqB => some ("=", 2, 3) | ``BinOp.neB => some ("\\ne", 2, 3)
    | ``BinOp.and => some ("\\land", 2, 2) | ``BinOp.or => some ("\\lor", 2, 1)
    | ``BinOp.band => some ("\\mathbin{\\&}", 1, 7) | ``BinOp.bor => some ("\\mathbin{|}", 1, 5)
    | ``BinOp.bxor => some ("\\veebar", 1, 6)
    | ``BinOp.shl => some ("\\ll", 2, 8) | ``BinOp.shr => some ("\\gg", 2, 8)
    | ``BinOp.addW => some ("+_{w}", 2, 9) | ``BinOp.subW => some ("-_{w}", 2, 9)
    | ``BinOp.mulW => some ("\\cdot_{w}", 2, 10) | ``BinOp.powW => some ("\\mathbin{**}_{w}", 3, 11)
    | _ => none

/-- A term the renderer cannot read: `\mathsf{?}`, and a warning. -/
def unknownTm (e : Expr) : RM Doc := do
  warn s!"no LaTeX for the term {← ppExpr e}: printed as \\mathsf\{?}"
  return .tx "\\mathsf{?}" 1

/-- `p · f` in the macros backend, `p.f` in the plain backend. -/
def fieldDoc (p : Doc) (f : Doc) : RM Doc := do
  if ← macrosM then return .cat #[.tx "\\pField{", .whole p, .tx "}{" 1, .whole f, .tx "}"]
  return .cat #[p, .tx "." 1, f]

/-- `p · at(i)` in the macros backend (`atMap` for a mapping), `p[i]` in the plain backend. -/
def indexDoc (p i : Doc) (map : Bool := false) : RM Doc := do
  if ← macrosM then
    let key := if map then "atMap" else "at"
    if (← read).definitions.any (·.1 == key) then
      let head ← definitionLink key ("\\" ++ key)
      return .cat #[.tx "\\pField{" 1, .whole p, .tx "}{" 1, .tx head 2,
        .tx "(" 1, .whole i, .tx ")}" 1]
    let m := if map then "\\pIndexMap{" else "\\pIndex{"
    return .cat #[.tx m, .whole p, .tx "}{" 4, .whole i, .tx "}"]
  return .cat #[p, .tx "[", .nest i, .tx "]"]

/-- The `length` field. -/
def lengthDoc : RM Doc := do
  return if ← macrosM then .tx "\\lengthField" 6 else .kw "length"

/-- Whether an index type is a mapping's. -/
def isMapIndex (it : Expr) : MetaM Bool := return (← whnf it).isAppOf ``IndexTy.map

mutual

/-- A scoped term read at the names `ns`, and its precedence (`100`: an atom). -/
partial def tmP (ns : List Expr) (e : Expr) : RM (Doc × Nat) := do
  let (ns, v, e) ← Delab.viewTmS true ns e
  let atom (d : Doc) : RM (Doc × Nat) := return (d, 100)
  match v with
  | .var x =>
    let n := (← fvarName? x).getD "_"
    atom (.ident n)
  | .pv x =>
    let some x ← ppVar? x | atom (← unknownTm e)
    atom (.ident x.getId.toString)
  | .netOf x a =>
    let some x ← ppVar? x | atom (← unknownTm e)
    let a ← tm ns a
    if ← macrosM then
      return ← atom (.app (.tx (← sortedSym ``Tm.netOf (primSort (mkConst ``PrimTy.int))) 6)
        #[.ident x.getId.toString, .app (.tx (← definitionLink "at" "\\at") 2) #[a]])
    atom (.app (.tx (← symOf ``Tm.netOf) 3) #[.ident x.getId.toString, a])
  | .bumped _ _ t => atom (.cat #[← tm ns t, .tx "\\oplus\\oplus" 2])
  | .other => atom (← unknownTm e)
  | .sym k oargs xs => symDoc ns e k oargs xs

/-- A scoped term. -/
partial def tm (ns : List Expr) (e : Expr) : RM Doc := return (← tmP ns e).1

/-- An operand of an infix operator of precedence `p`: parenthesised when it
binds less tightly (`strict` on the right of a non-associative one). -/
partial def operand (ns : List Expr) (e : Expr) (p : Nat) (strict : Bool) : RM Doc := do
  let (d, q) ← tmP ns e
  if q < p || (strict && q == p) then return .paren d else return d

/-- `a op b` at its precedence. -/
partial def infixDoc (ns : List Expr) (a b : Expr) (op : String × Nat × Nat) : RM (Doc × Nat) := do
  let (s, w, p) := op
  -- `**` is right-associative (`p = 11`), the others left
  let right := p == 11
  return (.bin (← operand ns a p right) s w (← operand ns b p !right), p)

/-- `find(s, p.length)`: the length of the array at `p` read in `s`. -/
partial def lenDoc (ns : List Expr) (s p : Expr) : RM Doc := do
  let f ← sortedSym ``Op2.len (primSort (mkConst ``PrimTy.uint))
  return .app (.tx f 4) #[← tm ns s, ← fieldDoc (← tm ns p) (← lengthDoc)]

/-- A symbol applied: by its constructor. -/
partial def symDoc (ns : List Expr) (e : Expr) (k : Lean.Name) (oargs xs : Array Expr) :
    RM (Doc × Nat) := do
  let atom (d : Doc) : RM (Doc × Nat) := return (d, 100)
  let x (i : Nat) : RM Doc := tm ns xs[i]!
  let fn (w : Nat := 4) : RM Doc := return .tx (← symOf k) w
  let plainApp : RM (Doc × Nat) := do atom (.app (← fn) (← xs.mapM (tm ns)))
  let mac ← macrosM
  match k with
  | ``Op0.lit =>
    let some d ← litDoc oargs[1]! | atom (← unknownTm e)
    atom d
  | ``Op0.zlit =>
    let some n ← intOf? oargs[0]! | atom (← unknownTm e)
    if n < 0 then return (.tx (toString n) (toString n).length, 50)
    atom (.tx (toString n) (toString n).length)
  | ``Op0.env =>
    let s := match (← whnf oargs[0]!).constName? with
      | some ``EnvKey.msgSender => some ("msg.sender", "\\mathit{msg.sender}")
      | some ``EnvKey.msgValue => some ("msg.value", "\\mathit{msg.value}")
      | some ``EnvKey.timestamp => some ("block.timestamp", "\\mathit{block.timestamp}")
      | some ``EnvKey.selfBalance =>
        some ("selfBalance", if mac then "\\selfBalance" else "\\mathit{selfBalance}")
      | some ``EnvKey.selfAddress => some ("this", if mac then "\\code{self}" else "\\mathit{this}")
      | _ => none
    let some (t, s) := s | atom (← unknownTm e)
    atom (.tx s t.length)
  | ``Op0.root | ``Op0.member =>
    let some r ← nameOf? (if k == ``Op0.root then oargs[0]! else oargs[1]!) | atom (← unknownTm e)
    atom (.ident r)
  | ``Op0.storage | ``Op0.memory | ``Op0.mtSt => atom (← fn 7)
  | ``Op1.unop =>
    let op := oargs[0]!
    let a ← operand ns xs[0]! 12 false
    if (← fvarName? op).isSome then return (.cat #[.tx "\\ominus " 1, a], 12)
    match (← whnf op).constName? with
    | some ``UnOp.not => return (.cat #[.tx "\\lnot " 1, a], 12)
    | some ``UnOp.neg => return (.cat #[.tx "-" 1, a], 12)
    | some ``UnOp.bnot => return (.cat #[.tx "\\mathord{\\sim}" 1, a], 12)
    | some ``UnOp.toInt => atom (.cat #[.tx "\\mathit{int}(" 4, .whole (← x 0), .tx ")" 1])
    | some ``UnOp.toUint => atom (.cat #[.tx "\\mathit{uint}(" 5, .whole (← x 0), .tx ")" 1])
    | _ => atom (← unknownTm e)
  | ``Op1.net =>
    if mac then return ← atom (← netSelectDoc (← x 0))
    plainApp
  | ``Op1.field | ``Op1.fieldIn | ``Op1.mfield =>
    let f := if k == ``Op1.fieldIn then oargs[2]! else oargs[1]!
    let some f ← nameOf? f | atom (← unknownTm e)
    atom (← fieldDoc (← x 0) (.ident f))
  | ``Op1.next =>
    -- `p[p.length]`, the length read in `storage`
    let st ← symOf ``Op0.storage
    let len := Doc.app (.tx (← sortedSym ``Op2.len (primSort (mkConst ``PrimTy.uint))) 4)
      #[.tx st 7, ← fieldDoc (← x 0) (← lengthDoc)]
    atom (← indexDoc (← x 0) len)
  | ``Op1.sval | ``Op1.mval | ``Op1.ref => tmP ns xs[0]!
  | ``Op1.toInt => if mac then tmP ns xs[0]! else plainApp
  | ``Op1.fixedCopy => if mac then tmP ns xs[0]! else atom (.app (← fn 9) #[← x 0])
  | ``Op1.delValue =>
    atom (.app (.tx (← sortedSym k (primSort oargs[0]!)) 8) #[← x 0])
  | ``Op1.select | ``Op1.selectIn =>
    let r := if k == ``Op1.select then oargs[1]! else oargs[2]!
    let some r ← nameOf? r | atom (← unknownTm e)
    let structS : RM String := return if ← macrosM then "\\Struct" else "\\mathsf{Struct}"
    atom (.app (.tx (← sortedSym k structS) 6) #[← x 0, .ident r])
  | ``Op1.alloc =>
    atom (.app (← fn 7) #[.app (.tx (← symOf ``Op1.addM) 4) #[← x 0]])
  | ``Op1.newArr | ``Op1.addM | ``Op1.wt | ``Op1.cleanTail => plainApp
  | ``Op2.binop | ``Op2.zbin | ``Op2.zcmp =>
    let some op ← binOpTeX oargs[0]! | atom (← unknownTm e)
    infixDoc ns xs[0]! xs[1]! op
  | ``Op2.find | ``Op2.findIn =>
    let p := if k == ``Op2.find then oargs[0]! else oargs[1]!
    atom (.app (.tx (← sortedSym k (primSort p)) 4) #[← x 0, ← x 1])
  | ``Op2.sfind | ``Op2.sfindIn =>
    let T := if k == ``Op2.sfind then oargs[0]! else oargs[1]!
    atom (.app (.tx (← sortedSym k (tySort T)) 4) #[← x 0, ← x 1])
  | ``Op2.len => atom (← lenDoc ns xs[0]! xs[1]!)
  | ``Op2.read =>
    atom (.app (.tx (← sortedSym k (primSort oargs[0]!)) 4) #[← x 0, ← x 1])
  | ``Op2.mlen =>
    let f ← sortedSym k (primSort (mkConst ``PrimTy.uint))
    atom (.app (.tx f 4) #[← x 0, ← fieldDoc (← x 1) (← lengthDoc)])
  | ``Op2.at =>
    atom (← indexDoc (← x 0) (← x 1) (← isMapIndex oargs[3]!))
  | ``Op3.atIn =>
    let i ← indexDoc (← x 1) (← x 2) (← isMapIndex oargs[3]!)
    if mac then return ← atom i
    atom (.cat #[i, .tx "@" 1, ← x 0])
  | ``Op2.nextIn =>
    let i ← indexDoc (← x 1) (← lenDoc ns xs[0]! xs[1]!)
    if mac then return ← atom i
    atom (.cat #[i, .tx "@" 1, ← x 0])
  | ``Op2.mat => atom (← indexDoc (← x 0) (← x 1))
  | ``Op2.delAt | ``Op2.delAtIn | ``Op2.copySt | ``Op3.save | ``Op3.saveIn | ``Op3.write =>
    plainApp
  | ``Op2.iread => plainApp
  | ``Op2.copyMem =>
    atom (.app (← fn 7) #[.tx (← symOf ``Op0.mtSt) 4, ← x 0, ← x 1])
  | ``Op2.copy =>
    atom (.app (← fn 7) #[.app (.tx (← symOf ``Op2.copySt) 6) #[← x 0, ← x 1]])
  | ``Op2.pushSlot | ``Op2.extend | ``Op2.shrink | ``Op2.pop =>
    -- KeY's writes: the length saved one more or one less, a pop's last
    -- element deleted first
    let s ← x 0
    let p ← x 1
    let len ← lenDoc ns xs[0]! xs[1]!
    let plus := k == ``Op2.pushSlot || k == ``Op2.extend
    let len' := Doc.bin len (if plus then "+" else "-") 1 (.tx "1")
    let lenPath ← fieldDoc p (← lengthDoc)
    let base ← if k == ``Op2.pop then
        let last ← indexDoc p (.bin len "-" 1 (.tx "1"))
        pure (Doc.app (.tx (← symOf ``Op2.delAt) 5) #[s, last])
      else pure s
    atom (.app (← fn) #[base, lenPath, len'])
  | ``Op3.push =>
    let s ← x 0
    let p ← x 1
    let len ← lenDoc ns xs[0]! xs[1]!
    let slot ← indexDoc p len
    let inner := Doc.app (← fn) #[s, slot, ← x 2]
    atom (.app (← fn) #[inner, ← fieldDoc p (← lengthDoc), .bin len "+" 1 (.tx "1")])
  | ``Op3.ite =>
    let (c, a, b) := (← x 0, ← x 1, ← x 2)
    if mac then
      return (.cat #[.tx "\\fmlIf{" 3, .whole c, .tx "}{" 6, .whole a, .tx "}{" 6, .whole b, .tx "}"], 0)
    return (.cat #[.kw "if", .tx "\\;" 1, c, .tx "\\;" 1, .brk, .kw "then", .tx "\\;" 1, a,
      .tx "\\;" 1, .brk, .kw "else", .tx "\\;" 1, b], 0)
  | ``Op3.modular =>
    let n := match (← whnf oargs[0]!).constName? with
      | some ``ModOp.mulmod => "mulmod"
      | _ => "addmod"
    atom (.app (.tx (← spell n ("\\funcFont{" ++ n ++ "}")) 6) (← xs.mapM (tm ns)))
  | _ =>
    warn s!"no LaTeX shape for {k}: printed as \\mathsf"
    atom (.app (.tx ("\\mathsf{" ++ escape k.getString! ++ "}") 4) (← xs.mapM (tm ns)))

end

/-! ## Updates -/

/-- `:=` -/
def updSym : RM Doc := return if ← macrosM then .tx "\\upd" 2 else .tx "\\mathrel{:=}" 2

/-- `x := r`, `r` read at `ns`. -/
def rhsDoc (ns : List Expr) (x : Expr) (r : Expr) : RM Doc := do
  let xn := match ← ppVar? x with
    | some i => i.getId.toString
    | none => "_"
  let lhs := Doc.ident xn
  let r ← whnf (← instantiateMVars r)
  let t := r.getAppArgs.back?.getD r
  let rhs ← match r.getAppFn.constName? with
    | some ``Rhs.val | some ``Rhs.path | some ``Rhs.mref | some ``Rhs.store | some ``Rhs.zint =>
      tm ns t
    | some c@``Rhs.unset | some c@``Rhs.saveNet | some c@``Rhs.saveNetMt => pure (.tx (← symOf c) 4)
    | _ => unknownTm r
  return .cat #[lhs, .tx " " 1, ← updSym, .tx " " 1, rhs]

/-- An assigning element, its right-hand sides read at `ns` and its target at `ms`. -/
def elemDoc (ns ms : List Expr) (e : Expr) : RM Doc := do
  let e ← whnf (← instantiateMVars e)
  let args := e.getAppArgs
  let u ← updSym
  let asg (lhs : Doc) (rhs : Doc) : Doc := .cat #[lhs, .tx " " 1, u, .tx " " 1, rhs]
  let some c := e.getAppFn.constName? | unknownTm e
  unless symbols.any (·.ctor == c) do return ← unknownTm e
  let lhs : Doc := .tx (← symOf c) 7
  match c with
  | ``UpdElem.local => rhsDoc ns (← Delab.idxName ms args[4]!) args[5]!
  | ``UpdElem.storage => return asg lhs (← tm ns args[3]!)
  | ``UpdElem.memory => return asg lhs (← tm ns args[3]!)
  | ``UpdElem.setBalance => return asg lhs (← tm ns args[3]!)
  | ``UpdElem.selfBalance =>
    let op := if (← whnf args[3]!).isConstOf ``IntOp.sub then "-" else "+"
    return asg lhs (.bin (.tx (← symOf ``UpdElem.selfBalance) 11) op 1 (← tm ns args[4]!))
  | ``UpdElem.net | ``UpdElem.pay | ``UpdElem.netMt =>
    let r ← tm ns args[3]!
    let mac ← macrosM
    let sel ← netSelectDoc r
    let storeHead ← definitionLink "store" (if mac then "\\store" else "\\mathit{store}")
    let atHead ← definitionLink "at" (if mac then "\\at" else "\\mathit{at}")
    let store (base : Doc) (v : Doc) : Doc :=
      .app (.tx storeHead 5) #[base, .app (.tx atHead 2) #[r], v]
    let net : Doc := .tx (← symOf ``Op1.net) 3
    match c with
    | ``UpdElem.net =>
      let op := if (← whnf args[4]!).isConstOf ``IntOp.sub then "-" else "+"
      return asg lhs (store net (.bin sel op 1 (← tm ns args[5]!)))
    | ``UpdElem.pay =>
      let a ← tm ns args[4]!
      let self : Doc := if mac then .tx "\\code{self}" 4 else .kw "this"
      return asg lhs (.cat #[.kw "if", .tx "\\;(" 2, r, .tx " = " 3, self, .tx ")\\;" 2, .brk,
        .kw "then", .tx "\\;" 1, net, .tx "\\;" 1, .brk, .kw "else", .tx "\\;" 1,
        store net (.bin sel "-" 1 a)])
    | _ => return asg lhs (store (.tx (← symOf ``Op0.mtSt) 4) (← tm ns args[4]!))
  | _ => unknownTm e

/-- An update read at `ns` (`none` where it prints as nothing: pops and
drops), and the names of the context it leaves. -/
def updDoc (ns : List Expr) (U : Expr) : RM (Option Doc × List Expr) := do
  let (ps, ms) ← Delab.updPiecesS ns U
  if ps.isEmpty then return (none, ms)
  let mut es : Array Doc := #[]
  for p in ps do
    match p with
    | .elem ns' ms' e => es := es.push (← elemDoc ns' ms' e)
    | .decl ns' x r => es := es.push (← rhsDoc ns' x r)
    | .var U => es := es.push (.ident ((← fvarName? U).getD "U"))
    | .stuck => es := es.push (← unknownTm U)
  let sep : Doc := .tx " \\parallel " 3
  return (some (.cat #[.tx "\\{", .nest (Doc.sepBy sep es), .tx "\\}"]), ms)

/-! ## Programs -/

/-- Whether code goes in the write-up's `\code{…}` (`\lstinline|…|` in a macro
argument): ASCII, no `|`, `%`, `#` or `\`, and balanced braces. -/
def codeSafe (s : String) : Bool :=
  s.all (fun c => c.toNat < 128 && !"|%#\\&$^~".contains c) &&
    (s.toList.foldl (fun (n : Int) c => if n < 0 then n else if c == '{' then n + 1
      else if c == '}' then n - 1 else n) 0) == 0

/-- Code text as TeX source: the program printer's `−` (U+2212, a
decrement's) as `-`, other non-ASCII characters as math (`\ensuremath`). -/
def codeText (s : String) : String :=
  s.map fun c => if c == '−' then '-' else c

/-- `escape`, a non-ASCII character as LeanTeX spells it, in math. -/
def escapeCode (s : String) : String :=
  String.join <| s.toList.map fun c =>
    if c.toNat < 128 then escape (String.singleton c)
    else "\\ensuremath{" ++ c.toLatex ++ "}"

/-- Code: `\code{…}` in the macros backend where it is safe, else `\texttt{…}`. -/
def codeDoc (s : String) : RM Doc := do
  let s := codeText s
  if (← macrosM) && codeSafe s then return .tx ("\\code{" ++ s ++ "}") s.length
  return .tx ("\\texttt{" ++ escapeCode s ++ "}") s.length

/-- A statement's text, one line. -/
def stmtText (s : TSyntax `sol_stmt) : MetaM String := do
  if Delab.isBlockEnd s.raw then return "}"
  let f ← PrettyPrinter.ppCategory `sol_stmt s
  let t := (f.pretty 100000).replace "\n" " "
  return t ++ ";"

/-- The program of a modality as code and, where it ends in a program
variable, that variable (`..ω`). -/
def progParts (items : Array Delab.SPiece) : RM (Option (String × Option String)) := do
  if let #[.var P] := items then
    if let some n ← fvarName? P then return some ("", some n)
  if let some ss ← pr (Delab.ppItemsS items) then
    return some (" ".intercalate (← ss.toList.mapM fun s => stmtText s), none)
  let some (ss, t) ← pr (Delab.ppPartsS items) | return none
  return some (" ".intercalate (← ss.toList.mapM fun s => stmtText s), t.map (·.getId.toString))

/-! ## Formulas -/

/-- How a formula is read where it is an operand: a connective in
parentheses (`Delab.isConnectiveS`). -/
def isConnective (ns : List Expr) (e : Expr) : RM Bool := pr (Delab.isConnectiveS ns e)

/-- Whether a postcondition prints without parentheses in the macros backend: `true`,
`false`, a formula variable, an update or a modality in front of one. -/
def isAtomicPost (ns : List Expr) (e : Expr) : RM Bool := do
  let (_, e) ← pr (Delab.viewF ns e)
  if (← fmlVar? e).isSome then return true
  if e.isAppOfArity ``Fml.tt 2 || e.isAppOf ``Fml.upd || e.isAppOf ``Fml.modal then return true
  if e.isAppOfArity ``Fml.not 3 then return (← whnf e.appArg!).isAppOfArity ``Fml.tt 2
  return false

/-- A comparison symbol of `Delab.cmpPartsS`. -/
def cmpTeX : String → String
  | "<" => "<" | "<=" => "\\le" | ">" => ">" | ">=" => "\\ge" | _ => "="

/-- A side of an equation or a comparison: a term in parentheses where it
binds less tightly than a comparison (a conditional, `=`, `∧`). -/
def side (ns : List Expr) (e : Expr) : RM Doc := operand ns e 4 false

mutual

/-- A scoped formula read at the names `ns`. -/
partial def fml (ns : List Expr) (e : Expr) : RM Doc := do
  let (ns, e) ← pr (Delab.viewF ns e)
  if let some x ← fmlVar? e then return .ident x.getId.toString
  let mac ← macrosM
  let kw (s : String) : Doc := .kw s
  match_expr e with
  | Fml.tt _ _ => return kw "true"
  | Fml.not _ _ φ =>
    if (← pr (Delab.viewF ns φ)).2.isAppOfArity ``Fml.tt 2 then return kw "false"
    if let some ((na, a), (nb, b)) ← pr (Delab.orPartsS ns e) then
      return .bin (← fmlArg na a) "\\lor" 1 (← fmlArg nb b)
    if let some (x, p, na, a) ← pr (Delab.exPartsS ns e) then
      if let (some x, some T) := (← ppVar? x, ← primName? p) then
        return .cat #[.tx "\\exists " 1, .tx ("\\mathsf{" ++ T ++ "}") T.length, .tx "\\," 1,
          .ident x.getId.toString, .tx ";\\ " 2, ← fml na a]
    return .cat #[.tx "\\lnot " 1, ← fmlArg ns φ]
  | Fml.eq _ _ _ a b =>
    if let some (sym, k, (nl, l), (nr, r)) ← liftM (Delab.cmpPartsS ns a ns b : MetaM _) then
      if k then
        if sym == "=" then return .bin (← side nl l) "=" 1 (← side nl r)
      else
        return .bin (← side nl l) (cmpTeX sym) 2 (← side nr r)
    return .bin (← side ns a) "=" 1 (← side ns b)
  | Fml.wellFormed _ _ s =>
    if mac then
      if (← read).definitions.any (·.1 == "wt") then
        return .cat #[.tx (← definitionLink "wt" "\\wellformedSym") 11, .tx "(" 0,
          .whole (← tm ns s), .tx ")" 1]
      return .cat #[.tx "\\wellformed{" 11, .whole (← tm ns s), .tx "}"]
    return .app (.tx (← definitionLink "wt" "\\mathit{wt}") 2) #[← tm ns s]
  | Fml.all _ _ x p φ =>
    let x := x.consumeMData
    let some xi ← ppVar? x | unknownFml e
    let T := (← primName? p).getD "T"
    return .cat #[.tx "\\forall " 1, .tx ("\\mathsf{" ++ T ++ "}") T.length, .tx "\\," 1,
      .ident xi.getId.toString, .tx ";\\ " 2, ← fml (x :: ns) φ]
  | Fml.and _ _ φ ψ =>
    if let some ((na, a), (nb, b)) ← pr (Delab.iffPartsS ns e) then
      return .bin (← fmlArg na a) "\\leftrightarrow" 3 (← fmlArg nb b)
    let r ← fml ns ψ
    let r := if (← pr (Delab.viewF ns ψ)).2.isAppOfArity ``Fml.imp 4 then Doc.paren r else r
    return .bin (← fmlArg ns φ) "\\land" 1 r
  | Fml.imp _ _ φ ψ => return .bin (← fmlArg ns φ) "\\rightarrow" 2 (← fml ns ψ)
  | Fml.upd _ _ _ _ U φ =>
    let (u, ms) ← updDoc ns U
    let body ← fmlArg ms φ
    match u with
    | some u => return .cat #[u, .brk, body]
    | none => return body
  | Fml.havoc _ _ φ =>
    return .cat #[.tx "\\{" 1, .tx (← spell "havoc" "\\havoc") 5, .tx "\\}" 1, .brk, ← fmlArg ns φ]
  | Fml.anon _ _ xs φ =>
    let some xs ← listElems? xs | unknownFml e
    let ids ← xs.mapM fun x => do
      let n ← Delab.idxName ns (← whnf x).appArg!
      return Doc.ident ((← ppVar? n).map (·.getId.toString) |>.getD "_")
    return .cat #[.tx "\\{" 1, .app (.kw "anon") ids, .tx "\\}" 1, .brk, ← fmlArg ns φ]
  | Fml.modal _ _ _ _ m P κ φ =>
    let (ps, ms) ← Delab.progPiecesS ns P
    let (qs, ms) ← pr (Delab.framePiecesS ms κ)
    let some (code, rest) ← progParts (ps ++ qs) | unknownFml e
    let code := codeText code
    let post ← if mac && !(← isAtomicPost ms φ) then pure (Doc.paren (← fml ms φ))
      else fmlArg ms φ
    let m' ← whnf m
    let kind : Nat := if m'.isConstOf ``Modality.diamond then 0
      else if m'.isConstOf ``Modality.box then 1 else 2
    -- the write-up's `\dlf{code}{post}`, where the post fits on the line
    if mac && rest.isNone && !code.isEmpty && codeSafe code && post.width ≤ 40 then
      let mac := #["\\dlf{", "\\dlboxf{", "\\dlbothf{"][kind]!
      return .cat #[.tx (mac ++ code ++ "}{") (code.length + 2), .whole post, .tx "}"]
    let (l, r) := #[("\\langle ", "\\rangle "), ("[", "]"), ("\\langle[", "]\\rangle ")][kind]!
    let codeD ← if code.isEmpty then pure (Doc.tx "" 0) else codeDoc code
    let restD : Doc := match rest with
      | some ω => .cat #[.tx (if code.isEmpty then "" else "\\ ") 1, .tx (".." ++ identIt ω) 3]
      | none => .tx "" 0
    return .cat #[.tx l 1, codeD, restD, .tx r 1, .brk, post]
  | _ => unknownFml e

/-- An operand of a connective, `¬`, `{U}` or a modality: a connective in
parentheses. -/
partial def fmlArg (ns : List Expr) (φ : Expr) : RM Doc := do
  let d ← fml ns φ
  if ← isConnective ns φ then return .paren d else return d

/-- A formula the renderer cannot read: `\mathsf{?}`, and a warning. -/
partial def unknownFml (e : Expr) : RM Doc := do
  warn s!"no LaTeX for the formula {← ppExpr e}: printed as \\mathsf\{?}"
  return .tx "\\mathsf{?}" 1

end

/-- Run a renderer: its result and the warnings it collected. -/
def RM.run' {α : Type} (o : Options) (k : RM α) : MetaM (α × Array String) := do
  let (a, ws) ← (k o).run #[]
  return (a, ws)

end Solidity.Latex
