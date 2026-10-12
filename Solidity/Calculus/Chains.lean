import Solidity.Calculus.ChainKit
import Solidity.Calculus.Notation
import Solidity.Calculus.Completeness
import Solidity.Calculus.Delab

/-!
# Chains on scoped formulas: `φ ~> ψ`, `φ ~[r]~> ψ`, `φ ~*> ψ`

The chains of `.claude/rules/derivations.md` on the scoped formulas of
`Calculus/Fml.lean` (W2 of `docs/intrinsic.md`); the relations are
`Calculus/ChainKit.lean`'s.  The notation is the same: a chain whose
first line is a scoped formula (`cdl![m]{ … }`) is read here, any other is
refused (`Calculus/RewriteChains.lean`), and `sol_chain` and `#derivation`
dispatch on the goal's head constant the same way.

**The lines are computed.**  A scoped line keeps what its print does not
show: the scope ends of a rule's fresh locals (`Frames.pop .capture`), the
rest of the program as a frame, the hidden binder.  So a written line after
the first is not read into the chain: the strategy computes it, and the
written text must be the computed line read in names: the two compare by
their keys (`Fml.lineKey`; `matchWritten`), the line as text in names (its
terms and updates, `Tm.keyStr`, `Upd.keyStrs`, and a modality's program,
`Prog.keyStrs`), what prints as nothing (a hidden binder, a scope end) left
out, the text read scoped with its parameters open (`elabDlOpen`), a
postcondition by its slot.  A line printed with a block's end
(`}`, `Delab`'s `core_item`) reads without it.  The statement holds
the computed lines, which `Delab` prints as written.

**While the program is open**, `~[sequentialToParallel]~>` merges the
scoped line's update spine (`Fml.MergeBy`, `Calculus/Merge.lean`), and a
literal law or a term taclet (in an update's right-hand sides or in the
line's equations), `applyOnRigid`, `concrete` and `simplifyUpdate` rewrite
the scoped line (`Fml.RwBy`, `Calculus/RewriteScoped.lean`;
`scopedRwCands`); `~=>` takes the first merge or rewrite that gives the
line written (`openRwSteps`).  The strategy goes on from the line a rewrite
leaves, so a step and a rewrite are links of one chain.

**`~~>` and `calc`**: `A ~~> B` reads `B` as a line of `A`'s derivation (or
one with its spine merged, or up to `openRwDepth` merges and rewrites past
one while the program is open, `openRwPath`, a bounded search that
`sol_chain?` writes out as links), else past the program as the line it
names (`Fml.LeadsK`: a line the rewrites reach that is `B`, read where it
stands, up to its binders' names); a
`calc` step `_ R B` leaves `B` a metavariable that `sol_chain` computes
from the line before and checks against the text (`pendingLines`), a
rewrite's too while the program is open (`Fml.RwBy`).

**Past the program** every rewrite arrow (`~[sequentialToParallel]~>`,
`~[findOnSave]~>`, `~=>`) rewrites the scoped line too: the merges and
`simplifyUpdate` of `Calculus/RewritePast.lean`, the laws in an update's
right-hand sides of `Calculus/RewriteLaws.lean` (the laws of
`Calculus/TermLaws.lean`, found at the update's scope), and the rewrites of
`Calculus/RewriteScoped.lean`.
A rewrite that gives no line written says why (`pastRefusal`): it applies
nowhere (a side condition, a modality), or what it gives.

**Proving a link** is the kernel's: `sol_chain` runs the strategy as
compiled code (`Fml.chainLines`, the postconditions in slots and a
modality `m` run as the diamond and the box), and proves each step
`Fml.stepFocusR k φ = some (f, ψ)` by `rfl` where no postcondition stands in
the way; where one does, along the line's connectives (`focusProof`, the
postcondition's `Post.inactive` past a goal that is done), with the fresh
index from `Post.noFresh` (`maxIdxProof`).  A rule that looks at a variable
modality is proved by `Modality.casesOn`, both cases by `rfl`.
-/

namespace Solidity

open Solidity (Modality)

variable {C : Contract}

/-! ## The strategy as compiled code -/

/-- Every position of a context, innermost first. -/
def Ctx.positions : (Γ : Ctx) → List ((t : LTy) × Idx Γ t)
  | [] => []
  | t :: Γ => ⟨t, .here⟩ :: (Ctx.positions Γ).map fun x => ⟨x.1, .there x.2⟩

/-- The slot of the `i`th postcondition while the strategy runs: a formula
with no modality and no fresh name, as a postcondition is, that names
every position of its context (`{anon(…)}`). -/
def Fml.chainSlot {Γ : Ctx} (i : Nat) : Fml C Γ :=
  .anon (Ctx.positions Γ) (Fml.slotMark i)

/-- `Fml.stepFocusR` as compiled code (`Fml.stepAt`'s shape). -/
def Fml.stepFocusAt (k : Nat) : {Γ : Ctx} → Fml C Γ → Option (Focus C × Fml C Γ)
  | _, φ => Fml.casesOn (motive := fun Γ _ => Option (Focus C × Fml C Γ)) φ
    (tt := none) (eq := fun _ _ => none) (defined := fun _ => none) (not := fun _ => none)
    (and := fun φ ψ => match Fml.stepFocusAt k φ with
      | some (f, φ') => some (f, .and φ' ψ)
      | none => (Fml.stepFocusAt k ψ).map fun (f, ψ') => (f, .and φ ψ'))
    (imp := fun a φ => (Fml.stepFocusAt k φ).map fun (f, φ') => (f, .imp a φ'))
    (upd := fun m U φ => (Fml.stepFocusAt k φ).map fun (f, φ') => (f, .upd m U φ'))
    (modal := fun m P κ φ => Fml.modalFocus k m P κ φ)
    (havoc := fun φ => (Fml.stepFocusAt k φ).map fun (f, φ') => (f, .havoc φ'))
    (all := fun x p φ => (Fml.stepFocusAt k φ).map fun (f, φ') => (f, .all x p φ'))
    (bind := fun m x t φ => (Fml.stepFocusAt k φ).map fun (f, φ') => (f, .bind m x t φ'))
    (anon := fun xs φ => (Fml.stepFocusAt k φ).map fun (f, φ') => (f, .anon xs φ'))
  termination_by structural _ φ => φ

/-- A focus, quoted. -/
def Focus.quoteRaw (c : Lean.Expr) : Focus C → Lean.Expr
  | @Focus.stmt _ k m Γ Γ' s =>
    Lean.mkAppN (Lean.mkConst ``Focus.stmt) #[c, Lean.toExpr k, Lean.toExpr m, Quote.qCtxRaw Γ,
      Quote.qCtxRaw Γ', (Quote.qStmt Γ Γ' s).run c]
  | .empty => Lean.mkApp (Lean.mkConst ``Focus.empty) c

/-- A line of a derivation as compiled code leaves it: the line and the
statement the step that reached it fired on (`Prod.mk f φ`, hash-consed
together), the step's fresh index, and the line's key (`Fml.lineKey`,
quoted). -/
structure LineQ where
  pair : Lean.Expr
  fresh : Nat
  keys : Lean.Expr

/-- The names a line's context gets in its key: none known. -/
def Ctx.blankNames (Γ : Ctx) : List Var := List.replicate Γ.length (.user "_")

/-! ### A line's key

A written line is compared with a computed one by its text, read in names:
the key of a line (`Fml.lineKey`) names each position as the line binds it
(a hidden binder, a declaration, a `∀`), prints a term's symbols as they are
(`Tm.keyStr`), and leaves out what a line prints as nothing: a hidden
binder, a scope end, a pop.  A line the strategy reaches and the line
written that names it are then one key, whatever bookkeeping each keeps. -/

/-! `Tm.keyStr`, a term's text by name, is `Calculus/NamedTerm.lean`'s, beside
the key `NTm` reads a written term to. -/

/-- `x := r` as text, its right-hand side named by `ns`. -/
def Rhs.keyStr {Γ : Ctx} (ns : List Var) (x : Var) : {t : LTy} → Rhs C Γ t → String
  | _, .val t => s!"{reprStr x} := {Tm.keyStr ns t}"
  | _, .path p => s!"{reprStr x} := {Tm.keyStr ns p}"
  | _, .unset => s!"{reprStr x} := unset"
  | _, .mref i => s!"{reprStr x} := {Tm.keyStr ns i}"
  | _, .store t => s!"{reprStr x} := {Tm.keyStr ns t}"
  | _, .saveNet => s!"{reprStr x} := net"
  | _, .saveNetMt => s!"{reprStr x} := mtNet"

/-- An element as text, its right-hand sides named by `ns`, its target by `ms`. -/
def UpdElem.keyStr {Γ Δ : Ctx} (ns ms : List Var) : UpdElem C Γ Δ → String
  | .local i r => r.keyStr ns (i.name ms)
  | .storage t => s!"storage := {Tm.keyStr ns t}"
  | .memory t => s!"memory := {Tm.keyStr ns t}"
  | .selfBalance op a => s!"selfBalance {reprStr op} {Tm.keyStr ns a}"
  | .net r op a => s!"net {Tm.keyStr ns r} {reprStr op} {Tm.keyStr ns a}"
  | .pay r a => s!"pay {Tm.keyStr ns r} {Tm.keyStr ns a}"
  | .netMt r a => s!"netMt {Tm.keyStr ns r} {Tm.keyStr ns a}"
  | .setBalance a => s!"setBalance {Tm.keyStr ns a}"

/-- An update's elements as text, in order; a pop and a drop are nothing. -/
def Upd.keyStrs {Γ : Ctx} (ns : List Var) : {Δ : Ctx} → Upd C Γ Δ → List String
  | _, .nil => []
  | _, .snoc U e => Upd.keyStrs ns U ++ [e.keyStr ns (U.names ns)]
  | _, .decl U x r => Upd.keyStrs ns U ++ [r.keyStr ns x]
  | _, .pop U _ => Upd.keyStrs ns U
  | _, .drop U _ => Upd.keyStrs ns U

mutual

/-- A statement as `Stmt.toStr` prints it, but a branch's, a loop body's and
a `try` clause's statements by `Prog.keyStrs`: a block is flattened at every
depth, as a line's print and the elaborator flatten it (`whileUnwind` leaves
`if (c) { {body} while … }`). -/
partial def Stmt.keyStr {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → String
  | .ite c thn els =>
    s!"if ({c.toStr ns true}) {braced (Prog.keyStrs 0 ns thn)} else {braced (Prog.keyStrs 0 ns els)}"
  | .tryCall c rets ok err code pnc other =>
    let args := ", ".intercalate (c.args.map fun a => a.2.toStr ns)
    let rs := rets.toList
    let retsS := if rs.isEmpty then "" else
      s!" returns ({", ".intercalate (rs.map fun (p, x) => s!"{Ty.toStr (.prim p)} {x}")})"
    let codeS := match code.names with
      | [x] => s!"uint {x}"
      | _ => "uint"
    s!"try address({c.addr.toStr ns}).{c.fn}({args}){retsS} \
      {braced (Prog.keyStrs 0 (rets.names ++ ns) ok)} \
      catch Error(string memory) {braced (Prog.keyStrs 0 ns err)} \
      catch Panic({codeS}) {braced (Prog.keyStrs 0 (code.names ++ ns) pnc)} \
      catch {braced (Prog.keyStrs 0 ns other)}"
  | .loop a c body =>
    s!"{a.toStr ns}while ({c.toStr ns true}) {braced (Prog.keyStrs 0 ns body)}"
  | s => s.toStr ns

/-- The statements of a block, one string each, as `Prog.toStrs` prints
them, but a block statement (`{ … }`, what a call's expansion leaves) its
statements, as a line's print flattens it, at every depth (`Stmt.keyStr`). -/
partial def Prog.keyStrs (skip : Nat) (ns : List Var) {Γ Γ' : Ctx} : Prog C Γ Γ' → List String
  | .nil => []
  | .cons s P =>
    match skip with
    | k + 1 => Prog.keyStrs k (s.outNames ns) P
    | 0 =>
      match s with
      | .block body => Prog.keyStrs 0 ns body ++ Prog.keyStrs 0 ns P
      | s =>
        match Stmt.tupleCallStr? ns s P with
        | some (c, k) => c :: Prog.keyStrs k (s.outNames ns) P
        | none =>
          match Stmt.memCallStr? ns s P with
          | some c => c :: Prog.keyStrs 1 (s.outNames ns) P
          | none => s.keyStr ns :: Prog.keyStrs 0 (s.outNames ns) P

end

/-- The statements the frames hold, one string each (`Prog.keyStrs`): a
scope end is nothing, as `}` is in a written line. -/
def Frames.keyStrs (ns : List Var) : {Γ Γ₀ : Ctx} → Frames C Γ Γ₀ → List String
  | _, _, .nil => []
  | _, _, .seq ω κ => Prog.keyStrs 0 ns ω ++ κ.keyStrs (ω.outNames ns)
  | _, _, .pop _ h κ => κ.keyStrs (ns.drop h.depth)
  | _, _, .drop h κ => κ.keyStrs (h.names ns)

/-- The slot a formula is, if it is one: `{anon(…)}` over a slot's mark
(`Fml.slotMark`; `Fml.chainSlot`, `Fml.slotC`). -/
def Fml.slot? {Γ : Ctx} : Fml C Γ → Option Nat
  | .anon _ φ => φ.slotMark?
  | _ => none

/-- **A line's comparison key**, the positions named by `ns`: its terms and
updates as text (`Tm.keyStr`, `Upd.keyStrs`), the modality with the
program's text (`Prog.keyStrs`, then the frames'), a postcondition by its
slot; a hidden binder and an update of pops only are nothing. -/
def Fml.lineKey : {Γ : Ctx} → List Var → Fml C Γ → LineKey
  | _, ns, φ =>
    match φ.slot? with
    | some i => .slot i
    | none =>
    match φ with
    | .tt => .tt
    | .eq a b => .eq (a.keyStr ns) (b.keyStr ns)
    | .defined t => .defined (t.keyStr ns)
    | .not φ => .not (φ.lineKey ns)
    | .and φ ψ => .and (φ.lineKey ns) (ψ.lineKey ns)
    | .imp φ ψ => .imp (φ.lineKey ns) (ψ.lineKey ns)
    | .upd m U φ =>
      match U.keyStrs ns with
      | [] => φ.lineKey (U.names ns)
      | U' => .upd m U' (φ.lineKey (U.names ns))
    | .modal m P κ φ =>
      .modal m (Prog.keyStrs 0 ns P ++ κ.keyStrs (P.outNames ns))
        (φ.lineKey (κ.outNames (P.outNames ns)))
    | .havoc φ => .havoc (φ.lineKey ns)
    | .all x p φ => .all x p (φ.lineKey (x :: ns))
    | .bind _ x _ φ => φ.lineKey (x :: ns)
    | .anon xs φ => .anon (xs.map fun x => x.2.name ns) (φ.lineKey ns)

/-- The key of `φ` (`Fml.lineKey`), its context named `ns`, quoted: what a
written line's reading is compared with (`readingMatches`). -/
def Fml.lineKeyQ {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : Lean.Expr :=
  (φ.lineKey ns).quote

/-- The key of a written line read open (`elabDlOpen`), quoted. -/
def Fml.openKeyQ (r : (Γ : NCtx) × Fml C Γ.ctx) : Lean.Expr :=
  r.2.lineKeyQ r.1.names

/-- The lines of the derivation of `φ`, at most `n` of them. -/
def Fml.chainLines (c : Lean.Expr) {Γ : Ctx} : Nat → Fml C Γ → List LineQ
  | 0, _ => []
  | n + 1, φ =>
    let k := φ.fresh
    match φ.stepFocusAt k with
    | some (f, ψ) =>
      let pair := Lean.ShareCommon.shareCommon
        (Lean.mkApp2 (Lean.mkConst ``Prod.mk [0, 0]) (f.quoteRaw c) ((Quote.qFml Γ ψ).run c))
      ⟨pair, k, ψ.lineKeyQ Γ.blankNames⟩ :: Fml.chainLines c n ψ
    | none => []

/-- The lines of the derivation of `φ` and its key (`Fml.lineKey`, quoted):
one evaluation. -/
def Fml.chainRunQ (c : Lean.Expr) {Γ : Ctx} (n : Nat) (φ : Fml C Γ) : List LineQ × Lean.Expr :=
  (Fml.chainLines c n φ, φ.lineKeyQ Γ.blankNames)

/-- The merges of `φ`'s update spine (`Fml.mergeRun`), quoted: for each
position `k` and count `n`, the longest first, that merges, the line and its
key (`Fml.lineKey`, quoted). -/
def Fml.mergeCandsQ (c : Lean.Expr) {Γ : Ctx} (φ : Fml C Γ) :
    List (Nat × Nat × Lean.Expr × Lean.Expr) :=
  (List.range 8).flatMap fun k => (List.range 8).reverse.filterMap fun n =>
    (φ.mergeRun k (n + 1)).map fun ψ => (k, n + 1, (Quote.qFml Γ ψ).run c, ψ.lineKeyQ Γ.blankNames)

/-- Each rewrite of `fs` on `φ` (`Calculus/RewriteScoped.lean`), quoted: the
line it leaves and that line's key (`Fml.lineKey`, quoted), or `none`. -/
def Fml.rwResultsQ (c : Lean.Expr) {Γ : Ctx} (φ : Fml C Γ)
    (fs : List (Fml C Γ → Option (Fml C Γ))) : List (Option (Lean.Expr × Lean.Expr)) :=
  fs.map fun f => (f φ).map fun ψ => ((Quote.qFml Γ ψ).run c, ψ.lineKeyQ Γ.blankNames)

/-- `⟨[ s; … } ω ]⟩ φ`: a modality `m` that is a variable, its program
running into the end of a block (`Delab`'s `core_item`). -/
syntax:max "⟨" "[ " (sol_stmt "; ")* "} " core_item* "]" "⟩ " dl_fml:50 : dl_fml

namespace Chain

open Lean Meta Elab Term

/-! ## Postconditions and the modality, out of the way -/

/-- The Lean terms of a line: its modality, a variable, and its
postconditions `↑φ` (`Post.fml C Γ φ`), the `i`th in slot `i`. -/
structure Splice where
  modality : Option Expr := none
  posts : Array Expr := #[]

/-- Whether `e` is a postcondition `↑φ` over a variable. -/
def isPost (e : Expr) : Bool := e.isAppOfArity ``Post.fml 3 && e.hasFVar

/-- Whether a line holds a postcondition. -/
def hasPost (e : Expr) : Bool := (e.find? isPost).isSome

/-- The postconditions of `e`, in order, added to `sp`. -/
def collectPosts (e : Expr) (sp : Splice) : MetaM Splice := do
  let ref ← IO.mkRef sp
  forEachExpr' e fun x => do
    if isPost x then
      ref.modify fun sp => if sp.posts.contains x then sp else { sp with posts := sp.posts.push x }
      return false
    return true
  ref.get

/-- The slot of postcondition `i` at the context `Γ`. -/
def slotE (C Γ : Expr) (i : Nat) : Expr :=
  mkApp3 (mkConst ``Fml.chainSlot) C Γ (toExpr i)

/-- The line with each postcondition in its slot. -/
def punch (C : Expr) (sp : Splice) (e : Expr) : Expr :=
  e.replace fun x =>
    if isPost x then (sp.posts.idxOf? x).map fun i => slotE C (x.getArg! 1) i else none

/-- The line with each slot's postcondition put back. -/
def unpunch (sp : Splice) (e : Expr) : Expr :=
  e.replace fun x => do
    let (i, _) ← slotIdxC? x
    sp.posts[i]?

/-- The modality of a line with its postconditions in their slots, when it
is a variable; no other variable may be left. -/
def modalityOf? (φ : Expr) : MetaM (Option Expr) := do
  let fvs := (collectFVars {} φ).fvarIds
  if fvs.isEmpty then return none
  for x in fvs do
    let ty ← instantiateMVars (← x.getType)
    if ty.isConstOf ``Modality && fvs.size == 1 then return some (.fvar x)
    unless ty.isConstOf ``Modality do
      throwError "sol_chain: {mkFVar x} is free in the line: only a modality `m` and \
        postconditions `φ : Post C Γ` may be{indentExpr φ}"
  throwError "sol_chain: the line is under two modalities: take `cases` on one{indentExpr φ}"

/-- The line whose readings at the diamond and at the box are `d` and `b`:
the variable `m` where `d` has the diamond and `b` the box, the rest shared
(a modality a line fixes, a hidden binder's `.box`, stays). -/
partial def mergeModality (m d b : Expr) : Option Expr :=
  if d == b then some d
  else if d.isConstOf ``Modality.diamond && b.isConstOf ``Modality.box then some m
  else match d, b with
    | .app f x, .app g y => do pure (.app (← mergeModality m f g) (← mergeModality m x y))
    | .mdata k x, .mdata _ y => do pure (.mdata k (← mergeModality m x y))
    | _, _ => none

/-! ## Printing a line -/

/-- `⟨[ … ]⟩ φ` with a block's end among its statements, as `Delab`'s
`fixBlockEnds` prints `⟨ … ⟩ φ` and `[ … ] φ`. -/
partial def fixEitherBlockEnds (stx : Syntax) : MetaM Syntax := do
  let .node info k args := stx | return stx
  let args ← args.mapM fixEitherBlockEnds
  let stx := Syntax.node info k args
  unless args.size == 6 && args[0]!.isToken "⟨" && args[1]!.isToken "[" do return stx
  let ss := Delab.stmtItems args[2]!
  let some i := ss.findIdx? Delab.isBlockEnd | return stx
  let pre : Array (TSyntax `sol_stmt) := (ss.extract 0 i).map (⟨·⟩)
  let rest ← (ss.extract (i + 1) ss.size).mapM fun s =>
    if Delab.isBlockEnd s then `(core_item| } ) else `(core_item| $(⟨s⟩):sol_stmt ; )
  let φ : TSyntax `dl_fml := ⟨args[5]!⟩
  return (← `(dl_fml| ⟨[ $[$pre;]* } $rest* ]⟩ $φ)).raw

/-- A scoped line: `dl{ φ }`, a postcondition `↑φ` printed as `φ` (a local
of its name stands for it, which `Delab` prints as a formula variable). -/
def ppCoreLine (e : Expr) : MetaM Lean.Term := do
  let sp ← collectPosts e {}
  let rec go (i : Nat) (e : Expr) : MetaM Lean.Term := do
    if h : i < sp.posts.size then
      let p := sp.posts[i]
      let n ← match p.appArg! with
        | .fvar fv => fv.getUserName
        | _ => pure `φ
      withLocalDeclD n (mkApp2 (mkConst ``Fml) (p.getArg! 0) (p.getArg! 1)) fun x =>
        go (i + 1) (e.replace fun y => if y == p then some x else none)
    else
      let φ : TSyntax `dl_fml := ⟨← fixEitherBlockEnds (← Delab.ppFmlE e)⟩
      if Solidity.isEscape φ then Solidity.escapeTerm e else `(dl{ $φ:dl_fml })
  go 0 e

/-- A scoped line in a message. -/
def showLine (e : Expr) : MetaM MessageData := do
  let e ← instantiateMVars e
  try return m!"{← ppCoreLine e}" catch _ => return m!"{e}"

/-- A scoped line in a message, indented. -/
def indentLine (e : Expr) : MetaM MessageData := do
  return indentD (← showLine e)

/-! ## Running the strategy -/

/-- A line of a derivation: the line and the statement the step that reached
it fired on (`Focus`), its Lean terms back; the step's fresh index; and the
line's key, its postconditions in their slots, once per modality it was
run under (the diamond first). -/
structure Line where
  fml : Expr
  focus : Expr
  fresh : Nat
  keys : Array Expr

/-- The most lines a run computes. -/
def runFuel : Nat := 200

/-- `evalExpr` without the kernel's check of the throwaway definition it
compiles (`debug.skipKernelTC`): the value is a quoted term, and every line
or proof built from it is checked by the kernel where it is used.  The check
was a third of a short chain's time (`docs/intrinsic.md`, W3 `chains`). -/
unsafe def evalQuoted (α) (ty e : Expr) : MetaM α :=
  withOptions (debug.skipKernelTC.set · true) (evalExpr α ty e)

/-- The evaluated runs of this declaration, by their closed formula: a
theorem's proof sees its binders as new variables, so `runCache` misses
there, but the formula with its postconditions in slots is the same. -/
initialize closedCache : EnvExtension (Std.HashMap Expr (List LineQ × Expr)) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/-- The lines of the derivation of the closed formula `φ : Fml C Γ`, and
its key, quoted. -/
def closedRun (n : Lean.Name) (C Γ φ : Expr) : MetaM (List LineQ × Expr) := do
  if let some r := (closedCache.getState (← getEnv))[φ]? then return r
  let ty := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) (mkConst ``LineQ))
    (mkConst ``Expr)
  let r ← unsafe evalQuoted (List LineQ × Expr) ty
    (mkAppN (mkConst ``Fml.chainRunQ) #[C, quoteConstName n, Γ, toExpr runFuel, φ])
  modifyEnv fun env => closedCache.modifyState env (·.insert φ r)
  return r

/-- A derivation: the Lean terms of its first line, the key of that line
(once per modality), its lines, and whether they stop because the next rule
depends on the modality. -/
structure Run where
  splice : Splice
  keys : Array Expr
  lines : List Line
  modalStop : Bool

/-- Whether the program of the run's first line is still open: the strategy
has a line to give, or, under a modality variable, a step that reads it. -/
def Run.isOpen (r : Run) : Bool := !r.lines.isEmpty || r.modalStop

/-- The runs of this declaration, by every line they pass (as
today's chains' `runCache` did). -/
initialize runCache : EnvExtension (Std.HashMap Expr (Run × Nat)) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/-- The contract and the context of a scoped line. -/
def lineType (φ : Expr) : MetaM (Expr × Expr) := do
  let ty ← whnfR (← instantiateMVars (← inferType φ))
  unless ty.isAppOfArity ``Fml 2 do throwError "not a scoped formula{indentExpr φ}"
  return (ty.getArg! 0, ty.getArg! 1)

/-- Whether `e`'s type is a scoped formula. -/
def isCoreLine (e : Expr) : MetaM Bool := do
  let ty ← whnfR (← instantiateMVars (← inferType e))
  return ty.isAppOfArity ``Fml 2

/-- The pair `(f, ψ)` of a quoted line. -/
def unpair (e : Expr) : Expr × Expr := (e.appFn!.appArg!, e.appArg!)

/-- A merge of a line's update spine: the position, the count, the line it
leaves, and that line's keys (once per modality it was computed under). -/
structure MergeCand where
  k : Nat
  n : Nat
  fml : Expr
  keys : Array Expr

/-- The merges of the scoped line `φ` (`Fml.mergeCandsQ`), its postconditions
in slots and a modality `m` computed as the diamond and as the box. -/
def mergeCands (φ : Expr) : MetaM (Splice × List MergeCand) := do
  let φ ← instantiateMVars φ
  let (C, Γ) ← lineType φ
  let some nm := (← whnfR C).constName?
    | throwError "sol_chain: the contract is not a named constant: {C}"
  let sp ← collectPosts φ {}
  let φ' := punch C sp φ
  let m? ← modalityOf? φ'
  let sp := { sp with modality := m? }
  let ty := mkApp (mkConst ``List [0]) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat)
    (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat)
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr) (mkConst ``Expr))))
  let eval (ψ : Expr) : MetaM (List (Nat × Nat × Expr × Expr)) :=
    unsafe evalQuoted (List (Nat × Nat × Expr × Expr)) ty
      (mkAppN (mkConst ``Fml.mergeCandsQ) #[C, quoteConstName nm, Γ, ψ])
  match m? with
  | none =>
    let cs ← eval φ'
    return (sp, cs.map fun (k, n, f, e) => { k, n, fml := unpunch sp f, keys := #[e] })
  | some m =>
    let ds ← eval (φ'.replaceFVar m (mkConst ``Modality.diamond))
    let bs ← eval (φ'.replaceFVar m (mkConst ``Modality.box))
    let out := ds.filterMap fun (k, n, f, e) => do
      let (_, _, f', e') ← bs.find? fun (k', n', _, _) => k' == k && n' == n
      let g ← mergeModality m f f'
      pure { k, n, fml := unpunch sp g, keys := #[e, e'] }
    return (sp, out)

/-- The paths to the updates of a line (a quoted constructor term, its
postconditions in slots) below one of its connectives at least, at most
`d` steps deep (`FmlRw.mergeIn`). -/
partial def updPaths (e : Expr) : Nat → List (List PathStep)
  | 0 => []
  | d + 1 =>
    let e := e.consumeMData
    if e.isAppOfArity ``Fml.and 4 then
      (updPaths e.appFn!.appArg! d).map (.andL :: ·) ++ (updPaths e.appArg! d).map (.andR :: ·)
    else if e.isAppOfArity ``Fml.imp 4 then (updPaths e.appArg! d).map (.impR :: ·)
    else if e.isAppOfArity ``Fml.upd 6 then [] :: (updPaths e.appArg! d).map (.upd :: ·)
    else if e.isAppOfArity ``Fml.all 5 || e.isAppOfArity ``Fml.bind 6 then
      (updPaths e.appArg! d).map (.binder :: ·)
    else []

/-- A rewrite of a scoped line while its program is open: the rewrite
(`FmlRw`), the line it leaves, and that line's keys (once per modality
it was computed under). -/
structure RwCand where
  rw : Expr
  fml : Expr
  keys : Array Expr

/-- The law `c` in each update's right-hand sides past the program, at the
update's scope (`FmlRw.lawUpdS`, `Calculus/RewriteLaws.lean`): at each of
its instances in the scoped line `φ` (`lawInstances`) whose scope is an
update's of the spine (`scopes`).  A term taclet onto a term that cannot
halt where the update holds its write (`LawCov.covered`), a frame or
delete-value law (`LawCov.ref`), a member-wise law (`LawCov.eqv`), a
memory law (`LawCov.eval`, `evalLaw`). -/
def lawUpdCands (C : Expr) (c : Lean.Name) (evalLaw : Bool) (φ : Expr) (scopes : List Ctx)
    (keep : Expr → Bool := fun _ => true) : TermElabM (Array Expr × Option MessageData) := do
  if scopes.isEmpty then return (#[], none)
  let (is, failed) ← lawInstances c φ
  let is := is.filter fun (t, _, _) => keep t
  if is.isEmpty then return (#[], failed)
  let refCtor? :=
    if c == ``TermTaclet.findOnSaveFrame then some ``TermTaclet.RefLaw.findOnSaveFrame
    else if c == ``TermTaclet.findOnDelAtValue then some ``TermTaclet.RefLaw.findOnDelAtValue
    else if c == ``TermTaclet.findOnDelAtFrame then some ``TermTaclet.RefLaw.findOnDelAtFrame
    else if c == ``TermTaclet.lenOnSaveFrame then some ``TermTaclet.RefLaw.lenOnSaveFrame
    else if c == ``TermTaclet.lenOnDelAtFrame then some ``TermTaclet.RefLaw.lenOnDelAtFrame
    else if c == ``TermTaclet.findOnPushFrame then some ``TermTaclet.RefLaw.findOnPushFrame
    else if c == ``TermTaclet.findOnPopFrame then some ``TermTaclet.RefLaw.findOnPopFrame
    else none
  let mut out := #[]
  for (t, t', pf) in is do
    -- the instance's scope and sort: `Tm C Γ u`
    let ty ← whnfR (← inferType t)
    unless ty.isAppOfArity ``Tm 3 do continue
    let Γt := ty.getArg! 1
    let u := ty.getArg! 2
    let some un := (← whnfR u).getAppFn.constName? | continue
    if un == ``Srt.st || un == ``Srt.mem then continue
    -- the law's coverings of an update
    let mut Es : Array Expr := #[]
    if evalLaw then
      Es := Es.push (← mkAppM ``LawCov.eval #[pf])
    else
      if ← isDefEq (← mkAppM ``Tm.isLit #[t']) (mkConst ``Bool.true) then
        Es := Es.push (← mkAppM ``LawCov.covered #[pf, ← mkEqRefl (mkConst ``Bool.true)])
      if let some refCtor := refCtor? then
        let hr := mkAppN (mkConst refCtor) pf.getAppArgs
        Es := Es.push (← mkAppM ``LawCov.ref #[hr])
      -- by the kernel: the base reads compare member names (`String`s)
      let sb ← instantiateMVars (← mkAppM ``Tm.sameBase #[t, t'])
      if !sb.hasMVar && Kernel.isDefEqGuarded (← getEnv) (← getLCtx) sb (mkConst ``Bool.true) then
        Es := Es.push (← mkAppOptM ``LawCov.eqv
          #[none, none, none, t, t', ← mkEqRefl (mkConst ``Bool.true)])
    if Es.isEmpty then continue
    let q ← mkAppOptM ``LawPair.mk #[C, Γt, u, t, t']
    for (Γi, i) in scopes.zipIdx do
      unless ← isDefEq Γt (toExpr Γi) do continue
      for E in Es do
        out := out.push (mkAppN (mkConst ``FmlRw.lawUpdS) #[C, Γt, q, E, toExpr i])
  return (out, failed)

/-- A scoped storage term holding no write: the state variable, a storage
variable, or a member of one. -/
partial def plainStorageS (s : Expr) : Bool :=
  let args := s.getAppArgs
  if s.isAppOf ``Tm.app0 then (args.back?.map (·.isAppOf ``Op0.storage)).getD false
  else if s.isAppOf ``Tm.pvS then true
  else if s.isAppOf ``Tm.app1 && args.size ≥ 2 then
    (args[args.size - 2]!.isAppOf ``Op1.select || args[args.size - 2]!.isAppOf ``Op1.selectIn) &&
      plainStorageS args.back!
  else false

/-- A read of the state as the program found it (`find(storage, p)`,
`find(select(storage, r), p)`): nothing resolves it, and the member-wise laws
that apply to it only respell it, so a search does not take them. -/
def plainReadAny (t : Expr) : Bool :=
  t.isAppOf ``Tm.app2 && t.getAppArgs.size ≥ 3 &&
    (t.getAppArgs[t.getAppArgs.size - 3]!.isAppOf ``Op2.find ||
      t.getAppArgs[t.getAppArgs.size - 3]!.isAppOf ``Op2.findIn) &&
    plainStorageS t.getAppArgs[t.getAppArgs.size - 2]!

/-- The rewrites `~[r]~>` names on the scoped line `φ` while its program is
open (`Calculus/RewriteScoped.lean`), each with the line it leaves, in the
order they are tried: `applyOnRigid` at each update of the spine, along the
skeleton of the formula under it; `concrete` below each number of updates; a
literal law at each instance (found among the line's closed terms, as
past the program) in each update's right-hand sides; a term taclet onto a literal
in each box update's, its scoped twin (`TermTaclet`, `scopedLaw?`) matched
against the line's closed terms read at the empty scope
(`Tm.closedNilVals`); a law in the equations along the
skeleton below each number of updates (`FmlRw.litEq`, `FmlRw.lawEq`);
`simplifyUpdate` at each update (absorbing the scope ends after it where the line under it is an update); `applyOnPV` along the skeleton under
each update (`FmlRw.applyOnPV`); `applyOnRigidBox` as `applyOnRigid`,
`applyStorageBox` on a box update of the storage (`FmlRw.applyStorageBox`); for `sequentialToParallel`, the merges
over a storage or memory write at each update (`FmlRw.stateMerge`) and the
merges under a branch (`FmlRw.mergeIn`), the spine's own being `mergeCands`'.  Their postconditions in slots and a
modality `m` computed as the diamond and as the box; and why a law found no
instance. -/
def scopedRwCandsMany (φ : Expr) (as : Array RwArrow)
    (branches := true) (past := false) (keep : Expr → Bool := fun _ => true) :
    TermElabM (Splice × Array (List RwCand × Option MessageData)) := do
  let φ ← instantiateMVars φ
  let (C, Γ) ← lineType φ
  let some nm := (← whnfR C).constName?
    | throwError "sol_chain: the contract is not a named constant: {C}"
  let sp ← collectPosts φ {}
  let φ' := punch C sp φ
  let m? ← modalityOf? φ'
  let sp := { sp with modality := m? }
  let φb := match m? with
    | some m => φ'.replaceFVar m (mkConst ``Modality.box)
    | none => φ'
  let skels ← unsafe evalQuoted (List Skel) (mkApp (mkConst ``List [0]) (mkConst ``Skel))
    (mkAppN (mkConst ``Fml.spineSkels) #[C, Γ, φb])
  let k := skels.length - 1
  -- past the program, the scopes of the spine's updates, once
  -- (`Fml.spineScopes`), for the laws read at an update's scope
  let scopes : List Ctx ← if !past || !(← whnfR Γ).isAppOf ``List.nil then pure []
    else do
      let scopesE := mkAppN (mkConst ``Fml.spineScopes) #[C, Γ, φb]
      unsafe evalQuoted (List Ctx) (mkApp (mkConst ``List [0]) (mkConst ``Ctx)) scopesE
  -- the line's closed terms read at the empty scope, once for every law
  let mut tsMemo : Option (Array Expr) := none
  let mut rsAll : Array Expr := #[]
  let mut owner : Array Nat := #[]
  let mut fails : Array (Option MessageData) := #[]
  for h : ai in [0:as.size] do
    let a := as[ai]
    let mut rs : Array Expr := #[]
    let mut failed := none
    match a with
    | .table n =>
      if n == `applyOnRigid || n == `applyOnRigidBox then
        -- under the box `applyOnRigid` applies any update, under the diamond one
        -- that cannot halt (`FmlRw.applyOnRigid`): `applyOnRigidBox` too
        -- (proposal 105)
        for i in List.range k do
          let s := skels[i + 1]!
          if s.pushable then
            rs := rs.push (mkApp3 (mkConst ``FmlRw.applyOnRigid) C (toExpr i) (toExpr s))
      else if n == `applyStorageBox then
        -- past the program: a lone storage write on a first-order line, `storage`
        -- substituted (`FmlRw.applyStorageBoxP`, `Calculus/RewritePast.lean`)
        if past then
          for i in List.range k do
            rs := rs.push (mkApp2 (mkConst ``FmlRw.applyStorageBoxP) C (toExpr i))
        -- the box's only, on an update of the storage and locals (`FmlRw.applyStorageBox`)
        for i in List.range k do
          let s := skels[i + 1]!
          if s.pushable then
            rs := rs.push (mkApp3 (mkConst ``FmlRw.applyStorageBox) C (toExpr i) (toExpr s))
      else if n == `applyOnPV then
        for i in List.range k do
          let s := skels[i + 1]!
          if s.hasLit then
            rs := rs.push (mkApp3 (mkConst ``FmlRw.applyOnPV) C (toExpr i) (toExpr s))
      else if n == `concrete then
        for i in List.range (k + 1) do
          let s := skels[i]!
          if s.hasLit then rs := rs.push (mkApp3 (mkConst ``FmlRw.concrete) C (toExpr i) (toExpr s))
      else if n == `simplifyUpdate then
        -- past the program: the locals no one reads dropped with their writes
        -- (`FmlRw.simplifyPast`, `Calculus/RewritePast.lean`)
        if past then
          for i in List.range k do
            for every in [false, true] do
              -- the scope ends after the update merged in only where the line
              -- under it is an update: the kernel never looks into a postcondition
              for absorb in [true, false] do
                if absorb && !(skels[i + 1]! matches .upd _) then continue
                rs := rs.push (mkApp4 (mkConst ``FmlRw.simplifyPast) C (toExpr i) (toExpr every)
                  (toExpr absorb))
        -- the scope ends after the update absorbed only where the line under it
        -- is an update (`Fml.simpAtB`)
        for i in List.range k do
          for b in [false, true] do
            if b && !(skels[i + 1]! matches .upd _) then continue
            rs := rs.push (mkApp3 (mkConst ``FmlRw.simplifyUpdate) C (toExpr i) (toExpr b))
      else if n == `sequentialToParallel then
        if past then
          -- past the program: the longest run of the spine from each position
          -- that merges (`FmlRw.mergePast`, `Calculus/RewritePast.lean`)
          for i in List.range k do
            for j in (List.range (k - i)).reverse do
              rs := rs.push (mkApp3 (mkConst ``FmlRw.mergePast) C (toExpr i) (toExpr j))
        for i in List.range k do
          for r in [``MergeNameS.storage, ``MergeNameS.memory, ``MergeNameS.localsMemory] do
            rs := rs.push (mkApp3 (mkConst ``FmlRw.stateMerge) C (mkConst r) (toExpr i))
        let below := if !branches then [] else
          (updPaths φb 16).filter (·.any fun d => d matches .andL | .andR | .impR)
        for p in below do
          for j in (List.range 7).reverse do
            rs := rs.push (mkApp3 (mkConst ``FmlRw.mergeIn) C (toExpr p) (toExpr (j + 1)))
    | .litLaw c =>
      -- a literal law at each closed term of the line read at the empty scope
      let ts ← match tsMemo with
        | some ts => pure ts
        | none => Tm.closedNilVals φb
      tsMemo := some ts
      let (is, f) ← if h : 0 < ts.size then
          lawInstances c (← mkListLit (← inferType ts[0]) ts.toList)
        else pure (#[], none)
      failed := f
      for (t, t', pf) in is do
        unless keep t do continue
        for i in List.range k do
          rs := rs.push (← mkAppM ``FmlRw.lit #[pf, toExpr i])
        for i in List.range (k + 1) do
          let s := skels[i]!
          if s.hasLit then
            rs := rs.push (← mkAppM ``FmlRw.litEq #[pf, toExpr i, toExpr s])
    | .law c₀ =>
      -- the law matched against the line's closed terms read at the empty scope;
      -- a law with a twin in a storage of members (`findOnSave` and
      -- `findOnSaveIn`, …) is either
      let ts ← match tsMemo with
        | some ts => pure ts
        | none => Tm.closedNilVals φb
      tsMemo := some ts
      for c in Chain.lawTwins (← getEnv) c₀ do
        let (is, f) ← if h : 0 < ts.size then
            lawInstances c (← mkListLit (← inferType ts[0]) ts.toList)
          else pure (#[], none)
        if failed.isNone then failed := f
        for (t, t', pf) in is do
          unless keep t do continue
          if ← isDefEq (← mkAppM ``Tm.isLit #[t']) (mkConst ``Bool.true) then
            let ht ← mkEqRefl (mkConst ``Bool.true)
            for i in List.range k do
              rs := rs.push (← mkAppM ``FmlRw.lawUpd #[pf, ht, toExpr i])
          for i in List.range (k + 1) do
            let s := skels[i]!
            if s.hasLit then
              rs := rs.push (← mkAppM ``FmlRw.lawEq #[pf, toExpr i, toExpr s])
        -- past the program: in an update's right-hand sides under any modality,
        -- the law at the update's scope (`FmlRw.lawUpdS`)
        if past then
          let (es, f) ← lawUpdCands C c false φb scopes keep
          rs := rs ++ es
          -- the side condition, as solkey's taclet states it
          if f.isSome then failed := f
    | .evalLaw c =>
      -- a law of a memory read, in an update's right-hand sides under any
      -- modality, where the update holds the write it reads past
      -- (`FmlRw.lawUpdS`)
      let (es, f) ← lawUpdCands C c true φb scopes keep
      rs := rs ++ es
      failed := f
    rsAll := rsAll ++ rs
    owner := owner ++ Array.replicate rs.size ai
    fails := fails.push failed
  let none' : Array (List RwCand × Option MessageData) := fails.map fun f => ([], f)
  if rsAll.isEmpty then return (sp, none')
  let rs := rsAll
  let fml := mkApp2 (mkConst ``Fml) C Γ
  -- the rewrites' functions alone, their proofs dropped
  let fs ← rs.mapM fun r => whnf (mkAppN (mkConst ``FmlRw.apply) #[C, r, Γ])
  let list ← mkListLit (← mkArrow fml (mkApp (mkConst ``Option [0]) fml)) fs.toList
  let ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``Option [0])
    (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr) (mkConst ``Expr)))
  let eval (ψ : Expr) : MetaM (List (Option (Expr × Expr))) :=
    unsafe evalQuoted (List (Option (Expr × Expr))) ty
      (mkAppN (mkConst ``Fml.rwResultsQ) #[C, quoteConstName nm, Γ, ψ, list])
  let split (cs : List (Nat × RwCand)) : Array (List RwCand) :=
    (Array.range as.size).map fun ai => (cs.filter (·.1 == ai)).map (·.2)
  match m? with
  | none =>
    let qs ← eval φ'
    let cs := ((rs.toList.zip owner.toList).zip qs).filterMap fun ((r, o), q?) =>
      q?.map fun (f, e) => (o, { rw := r, fml := unpunch sp f, keys := #[e] })
    return (sp, (split cs).zipWith (fun c f => (c, f)) fails)
  | some m =>
    let ds ← eval (φ'.replaceFVar m (mkConst ``Modality.diamond))
    let bs ← eval φb
    let all := (rs.toList.zip owner.toList).zip (ds.zip bs)
    let cs := all.filterMap fun
      | ((r, o), some (fd, ed), some (fb, eb)) => do
        let g ← mergeModality m fd fb
        pure (o, { rw := r, fml := unpunch sp g, keys := #[ed, eb] })
      | _ => none
    let outs := split cs
    return (sp, (Array.range as.size).map fun ai => Id.run do
      let out := outs[ai]!
      let failed := fails[ai]!
      -- past the program, a rewrite that applies under one modality only
      let mine := (all.filter (·.1.2 == ai)).map (·.2)
      let parts := mine.any fun (d, b) => d.isSome != b.isSome
      let boxOnly := mine.all fun (d, b) => d.isNone || b.isSome
      let failed' := if past && out.isEmpty && failed.isNone && parts then
          if boxOnly then some m!"it applies under the box only, where an update that halts \
            makes the line true: go on after `cases {m}`"
          else some m!"it applies under one modality only: go on after `cases {m}`"
        else failed
      return (out, failed'))

/-- `scopedRwCandsMany` for one arrow. -/
def scopedRwCands (φ : Expr) (a : RwArrow) (branches := true)
    (past := false) (keep : Expr → Bool := fun _ => true) :
    TermElabM (Splice × List RwCand × Option MessageData) := do
  let (sp, rs) ← scopedRwCandsMany φ #[a] branches past keep
  let (cs, f) := rs[0]!
  return (sp, cs, f)

/-- The derivation of `φ`: its postconditions in slots, and, under a
modality `m`, run as the diamond and as the box, whose shared lines (read
with `m` back) are the lines under `m`. -/
def runChain (φ : Expr) : MetaM Run := do
  let φ ← instantiateMVars φ
  if φ.hasMVar then throwError "sol_chain: the formula is not known{indentExpr φ}"
  if let some (r, i) := (runCache.getState (← getEnv))[φ]? then
    return { r with lines := r.lines.drop i }
  let (C, Γ) ← lineType φ
  let some n := (← whnfR C).constName?
    | throwError "sol_chain: the contract is not a named constant: {C}"
  let sp ← collectPosts φ {}
  let φ' := punch C sp φ
  let m? ← modalityOf? φ'
  let sp := { sp with modality := m? }
  let line (q : LineQ) : Line :=
    let (f, ψ) := unpair q.pair
    { fml := unpunch sp ψ, focus := unpunch sp f, fresh := q.fresh, keys := #[q.keys] }
  let (keys, ls, modalStop) ← match m? with
    | none =>
      let (ls, e) ← closedRun n C Γ φ'
      pure (#[e], ls.map line, false)
    | some m =>
      let φd := φ'.replaceFVar m (mkConst ``Modality.diamond)
      let φb := φ'.replaceFVar m (mkConst ``Modality.box)
      let (ds, ed) ← closedRun n C Γ φd
      let (bs, eb) ← closedRun n C Γ φb
      let rec shared : List LineQ → List LineQ → List Line × Bool
        | d :: ds, b :: bs =>
          if let (some p, true) := (mergeModality m d.pair b.pair, d.fresh == b.fresh) then
            let (f, ψ) := unpair p
            let (ls, s) := shared ds bs
            ({ fml := unpunch sp ψ, focus := unpunch sp f, fresh := d.fresh,
               keys := #[d.keys, b.keys] } :: ls, s)
          else ([], true)
        | [], [] => ([], false)
        | _, _ => ([], true)
      let (ls, s) := shared ds bs
      pure (#[ed, eb], ls, s)
  let r : Run := { splice := sp, keys, lines := ls, modalStop }
  modifyEnv fun env => runCache.modifyState env fun c => Id.run do
    let mut c := c.insert φ (r, 0)
    if ls.length < runFuel then
      for (l, j) in ls.zipIdx do
        c := c.insert l.fml ({ r with keys := l.keys }, j + 1)
    return c
  return r

/-! ## Proofs of the steps -/

/-- `a ≡ b` by the kernel's definitional equality (`Calculus/RewriteChains.lean`'s
`kernelDefEq`). -/
def kernelDefEq (a b : Expr) : MetaM Bool := do
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  if a.hasMVar || b.hasMVar then return false
  return Kernel.isDefEqGuarded (← getEnv) (← getLCtx) a b

/-- The kernel's value of a closed `Nat` term. -/
def kernelNat (e : Expr) : MetaM Nat := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok r =>
    let some n := r.rawNatLit? <|> r.nat? | throwError "sol_chain: not a number{indentExpr r}"
    return n
  | .error _ => throwError "sol_chain: cannot compute{indentExpr e}"

/-- `e = n` by `rfl`, `n` the kernel's value of `e`. -/
def natRefl (e : Expr) : MetaM (Nat × Expr) := do
  let n ← kernelNat e
  let ty ← mkEq e (toExpr n)
  return (n, ← mkExpectedTypeHint (← mkEqRefl (toExpr n)) ty)

/-- `A.maxIdx = n`: the postconditions' `Post.noFresh`, put together along
the connectives, the kernel's value of the rest. -/
partial def maxIdxProof (A : Expr) : MetaM (Nat × Expr) := do
  let A := A.consumeMData
  if isPost A then
    return (0, mkApp3 (mkConst ``Post.noFresh) (A.getArg! 0) (A.getArg! 1) A.appArg!)
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  if !hasPost A then return ← natRefl (mkApp3 (mkConst ``Fml.maxIdx) C Γ A)
  let a := A.getAppArgs
  let unary (lem : Lean.Name) (pre : Array Expr) (child : Expr) : MetaM (Nat × Expr) := do
    let (n, h) ← maxIdxProof child
    return (n, mkAppN (mkConst lem) (pre ++ #[child, toExpr n, h]))
  match A.getAppFn.constName? with
  | some ``Fml.not => unary ``Fml.maxIdx_not_eq #[C, Γ] a[2]!
  | some ``Fml.havoc => unary ``Fml.maxIdx_havoc_eq #[C, Γ] a[2]!
  | some ``Fml.anon => unary ``Fml.maxIdx_anon_eq #[C, Γ, a[2]!] a[3]!
  | some ``Fml.and | some ``Fml.imp =>
    let lem := if A.isAppOf ``Fml.and then ``Fml.maxIdx_and_eq else ``Fml.maxIdx_imp_eq
    let (n₁, h₁) ← maxIdxProof a[2]!
    let (n₂, h₂) ← maxIdxProof a[3]!
    return (max n₁ n₂,
      mkAppN (mkConst lem) #[C, Γ, a[2]!, a[3]!, toExpr n₁, toExpr n₂, h₁, h₂])
  | some ``Fml.upd =>
    -- `upd {C Γ Γ'} m U φ`
    let (n₁, h₁) ← natRefl (mkApp4 (mkConst ``Upd.maxIdx) C Γ a[2]! a[4]!)
    let (n₂, h₂) ← maxIdxProof a[5]!
    return (max n₁ n₂, mkAppN (mkConst ``Fml.maxIdx_upd_eq)
      #[C, Γ, a[2]!, a[3]!, a[4]!, a[5]!, toExpr n₁, toExpr n₂, h₁, h₂])
  | some ``Fml.modal =>
    -- `modal {C Γ Γ₁ Γ₀} m P κ φ`
    let pk ← mkAppM ``Max.max #[mkAppN (mkConst ``Prog.maxIdx) #[C, Γ, a[2]!, a[5]!],
      mkAppN (mkConst ``Frames.maxIdx) #[C, a[2]!, a[3]!, a[6]!]]
    let (n₁, h₁) ← natRefl pk
    let (n₂, h₂) ← maxIdxProof a[7]!
    return (max n₁ n₂, mkAppN (mkConst ``Fml.maxIdx_modal_eq)
      #[C, Γ, a[2]!, a[3]!, a[4]!, a[5]!, a[6]!, a[7]!, toExpr n₁, toExpr n₂, h₁, h₂])
  | some ``Fml.all =>
    let (n, h) ← maxIdxProof a[4]!
    let x ← kernelNat (mkApp (mkConst ``Var.idx) a[2]!)
    return (max x n, mkAppN (mkConst ``Fml.maxIdx_all_eq) #[C, Γ, a[2]!, a[3]!, a[4]!, toExpr n, h])
  | some ``Fml.bind =>
    -- `bind {C Γ} m x t φ`
    let (n, h) ← maxIdxProof a[5]!
    let x ← kernelNat (mkApp (mkConst ``Var.idx) a[3]!)
    return (max x n,
      mkAppN (mkConst ``Fml.maxIdx_bind_eq) #[C, Γ, a[2]!, a[3]!, a[4]!, a[5]!, toExpr n, h])
  | _ => throwError "sol_chain: cannot compute the fresh index of{indentExpr A}"

/-- `A.active = false`: the postconditions' `Post.inactive`, put together
along the connectives, the kernel's `rfl` where none is left below one. -/
partial def inactiveProof (A : Expr) : MetaM (Option Expr) := do
  let A := A.consumeMData
  if isPost A then
    return some (mkApp3 (mkConst ``Post.inactive) (A.getArg! 0) (A.getArg! 1) A.appArg!)
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  if !hasPost A then
    let goal := mkApp3 (mkConst ``Fml.active) C Γ A
    unless ← kernelDefEq goal (toExpr false) do return none
    return some (← mkExpectedTypeHint (← mkEqRefl (toExpr false)) (← mkEq goal (toExpr false)))
  let a := A.getAppArgs
  let one (lem : Lean.Name) (pre : Array Expr) (child : Expr) : MetaM (Option Expr) := do
    let some h ← inactiveProof child | return none
    return some (mkAppN (mkConst lem) (pre ++ #[child, h]))
  match A.getAppFn.constName? with
  | some ``Fml.not => one ``Fml.active_not_false #[C, Γ] a[2]!
  | some ``Fml.havoc => one ``Fml.active_havoc_false #[C, Γ] a[2]!
  | some ``Fml.anon => one ``Fml.active_anon_false #[C, Γ, a[2]!] a[3]!
  | some ``Fml.upd => one ``Fml.active_upd_false #[C, Γ, a[2]!, a[3]!, a[4]!] a[5]!
  | some ``Fml.all => one ``Fml.active_all_false #[C, Γ, a[2]!, a[3]!] a[4]!
  | some ``Fml.bind => one ``Fml.active_bind_false #[C, Γ, a[2]!, a[3]!, a[4]!] a[5]!
  | some ``Fml.and | some ``Fml.imp =>
    let lem := if A.isAppOf ``Fml.and then ``Fml.active_and_false else ``Fml.active_imp_false
    let some h₁ ← inactiveProof a[2]! | return none
    let some h₂ ← inactiveProof a[3]! | return none
    return some (mkAppN (mkConst lem) #[C, Γ, a[2]!, a[3]!, h₁, h₂])
  | _ => return none

/-- The type `Focus C × Fml C Γ`. -/
def pairTy (C Γ : Expr) : Expr :=
  mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``Focus) C) (mkApp2 (mkConst ``Fml) C Γ)

/-- `some (f, B)`. -/
def someFocus (C Γ f B : Expr) : Expr :=
  mkApp2 (mkConst ``Option.some [0]) (pairTy C Γ)
    (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkApp (mkConst ``Focus) C) (mkApp2 (mkConst ``Fml) C Γ) f B)

/-- Why the line after is not written under the modality `m`. -/
def modalityStop (m : Expr) : MessageData :=
  m!"depends on the modality {m}, through a rule that reads it (`revertBox`, \
    `revertDiamond`, a loop's invariant rule): go on after `cases {m}`"

/-- `lhs = rhs` by `rfl`, the kernel's; under a modality `m` that the
kernel cannot compute past, by `Modality.casesOn m`, each case by `rfl`. -/
def kernelReflOrCases (m? : Option Expr) (lhs rhs : Expr) : MetaM Expr := do
  let ty ← mkEq lhs rhs
  if ← kernelDefEq lhs rhs then
    return ← mkExpectedTypeHint (← mkEqRefl rhs) ty
  let some m := m? | throwError "sol_chain: the kernel does not compute{indentExpr lhs}\nto{indentExpr rhs}"
  let motive ← withLocalDeclD `m (mkConst ``Modality) fun x => do
    mkLambdaFVars #[x] (ty.replaceFVar m x)
  let case (μ : Lean.Name) : MetaM Expr := do
    let l := lhs.replaceFVar m (mkConst μ)
    let r := rhs.replaceFVar m (mkConst μ)
    unless ← kernelDefEq l r do
      throwError "sol_chain: the line after the step{indentExpr lhs}\n{modalityStop m}"
    mkExpectedTypeHint (← mkEqRefl r) (← mkEq l r)
  return mkAppN (mkConst ``Modality.casesOn [levelZero])
    #[motive, m, ← case ``Modality.diamond, ← case ``Modality.box]

/-- `A.stepFocusR K = some (f, B)`: along the connectives to the statement
that fires where a postcondition stands in the way (past a goal that is
done, its `Post.inactive`), the kernel's `rfl` from there. -/
partial def focusProof (m? : Option Expr) (K : Nat) (A f B : Expr) : MetaM Expr := do
  let A := A.consumeMData
  let B := B.consumeMData
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  let kE := toExpr K
  let leaf : MetaM Expr := do
    kernelReflOrCases m? (mkApp4 (mkConst ``Fml.stepFocusR) C kE Γ A) (someFocus C Γ f B)
  unless hasPost A do return ← leaf
  let a := A.getAppArgs
  let b := B.getAppArgs
  let same (n : Lean.Name) : Bool := A.isAppOf n && B.isAppOf n && a.size == b.size
  if same ``Fml.and then
    if a[2]! == b[2]! then
      let some h ← inactiveProof a[2]! |
        throwError "sol_chain: the step after{← indentLine A}\nasks whether a goal is done, \
          which the kernel does not compute"
      let h₀ := mkAppN (mkConst ``Fml.stepFocusR_eq_none) #[C, kE, Γ, a[2]!, h]
      return mkAppN (mkConst ``Fml.stepFocusR_and_right)
        #[C, kE, Γ, a[2]!, a[3]!, b[3]!, f, h₀, ← focusProof m? K a[3]! f b[3]!]
    return mkAppN (mkConst ``Fml.stepFocusR_and_left)
      #[C, kE, Γ, a[2]!, a[3]!, b[2]!, f, ← focusProof m? K a[2]! f b[2]!]
  if same ``Fml.imp then
    return mkAppN (mkConst ``Fml.stepFocusR_imp)
      #[C, kE, Γ, a[2]!, a[3]!, b[3]!, f, ← focusProof m? K a[3]! f b[3]!]
  if same ``Fml.upd then
    return mkAppN (mkConst ``Fml.stepFocusR_upd)
      #[C, kE, Γ, a[2]!, a[3]!, a[4]!, a[5]!, b[5]!, f, ← focusProof m? K a[5]! f b[5]!]
  if same ``Fml.havoc then
    return mkAppN (mkConst ``Fml.stepFocusR_havoc)
      #[C, kE, Γ, a[2]!, b[2]!, f, ← focusProof m? K a[2]! f b[2]!]
  if same ``Fml.all then
    return mkAppN (mkConst ``Fml.stepFocusR_all)
      #[C, kE, Γ, a[2]!, a[3]!, a[4]!, b[4]!, f, ← focusProof m? K a[4]! f b[4]!]
  if same ``Fml.bind then
    return mkAppN (mkConst ``Fml.stepFocusR_bind)
      #[C, kE, Γ, a[2]!, a[3]!, a[4]!, a[5]!, b[5]!, f, ← focusProof m? K a[5]! f b[5]!]
  if same ``Fml.anon then
    return mkAppN (mkConst ``Fml.stepFocusR_anon)
      #[C, kE, Γ, a[2]!, a[3]!, b[3]!, f, ← focusProof m? K a[3]! f b[3]!]
  leaf

/-- `A.fresh = K`. -/
def freshProof (A : Expr) (K : Nat) : MetaM Expr := do
  let (n, h) ← maxIdxProof A
  unless n + 1 = K do throwError "sol_chain: the fresh index of{← indentLine A}\nis {n + 1}, not {K}"
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  return mkAppN (mkConst ``Fml.fresh_eq) #[C, Γ, A, toExpr n, h]

/-- `A ~> B` along the computed line `B`. -/
def oneStepProof (sp : Splice) (A : Expr) (B : Line) : MetaM Expr := do
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  return mkAppN (mkConst ``Fml.OneStep.ofFocus)
    #[C, Γ, A, B.fml, toExpr B.fresh, B.focus, ← freshProof A B.fresh,
      ← focusProof sp.modality B.fresh A B.focus B.fml]

/-- `A ~[r]~> B`, `r` a label whose focus is `B.focus`. -/
def stepByProof (sp : Splice) (r A : Expr) (B : Line) : MetaM Expr := do
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  let fr := mkApp2 (mkConst ``StepRule.focus) C r
  let h ← focusProof sp.modality B.fresh A B.focus B.fml
  let h ← mkExpectedTypeHint h (← mkEq (mkApp4 (mkConst ``Fml.stepFocusR) C (toExpr B.fresh) Γ A)
    (someFocus C Γ fr B.fml))
  return mkAppN (mkConst ``Fml.StepBy.ofFocus)
    #[C, Γ, A, B.fml, toExpr B.fresh, r, ← freshProof A B.fresh, h]

/-- `A ~*> Z` along the computed lines `ls`, `Z` the last. -/
def stepsProof (sp : Splice) (A : Expr) (ls : List Line) : MetaM Expr := do
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  let Z := (ls.getLast?.map (·.fml)).getD A
  let rec go (A : Expr) : List Line → MetaM Expr
    | [] => pure (mkApp3 (mkConst ``Fml.Steps.refl) C Γ A)
    | B :: ls => do
      let s ← oneStepProof sp A B
      pure (mkAppN (mkConst ``Fml.Steps.cons) #[C, Γ, A, B.fml, Z, s, ← go B.fml ls])
  go A ls

/-! ## Naming the rule -/

/-- The derivation of the constructor `c` (of `Taclet` or
`LeanTaclet`) on the statement `s` under `m`, fresh names at `k`: its
schema variables by unification (a hole's statement by its candidates,
`matchFind`), its side conditions by `rfl` or `decide`; the label
`StepRule.taclet k m s p d`. -/
def labelAs? (c : Lean.Name) (k m s : Expr)
    (pre : Option (List (Expr × Expr) × FindHeads) := none) : MetaM (Option Expr) := do
  let sTy ← whnfR (← inferType s)
  let C := sTy.getArg! 0
  let (cands, hs) ← match pre with
    | some p => pure p
    | none => do
      let cands ← holeCandidates s
      pure (cands, ← FindHeads.of s cands)
  unless ← mayFind c hs do return none
  let st ← saveState
  let r ← observing? do
    let ctor ← mkConstWithFreshMVarLevels c
    let (xs, _, ty) ← forallMetaTelescopeReducing (← inferType ctor)
    let args := ty.getAppArgs
    unless args.size == 7 do failure
    unless ← isDefEq args[0]! C <&&> isDefEq args[1]! k <&&> isDefEq args[2]! m do failure
    unless ← matchFind args[5]! s cands do failure
    for x in xs do
      if (← instantiateMVars x).isMVar then
        let t ← whnfR (← instantiateMVars (← inferType x))
        let t := if t.isAppOfArity ``autoParam 2 then t.getArg! 0 else t
        if let some (_, a, b) := t.eq? then
          unless ← isDefEq a b do failure
          x.mvarId!.assign (← mkEqRefl a)
        else if ← isProp t then
          x.mvarId!.assign (← mkDecideProof t)
    -- a local's type that only a side condition's proof mentions (a rule's
    -- `MRhs.mapFree` under a pushed local): no unification sets it, and any
    -- type will do there
    let mut defaulted := false
    for x in xs do
      if (← instantiateMVars x).isMVar then
        if (← whnfR (← instantiateMVars (← inferType x))).isConstOf ``LTy then
          x.mvarId!.assign (mkApp (mkConst ``LTy.val) (mkConst ``PrimTy.uint))
          defaulted := true
    let d ← instantiateMVars (mkAppN ctor xs)
    let p ← instantiateMVars args[6]!
    if d.hasMVar || p.hasMVar then failure
    if defaulted then Meta.check d
    let wrap := if (`Solidity.Taclet).isPrefixOf c then ``Rule.key else ``Rule.lean
    let rule ← mkAppM wrap #[d]
    mkAppM ``StepRule.taclet #[k, m, s, p, rule]
  if r.isNone then st.restore
  return r

/-- The constructors a name may be. -/
def ruleCtors (r : Lean.Name) : MetaM (List Lean.Name) := do
  let env ← getEnv
  return [`Solidity.Taclet ++ r, `Solidity.LeanTaclet ++ r].filter env.contains

/-- Every rule constructor, solkey's first. -/
def allRuleCtors : MetaM (List Lean.Name) := do
  let mut out := []
  for J in [``Taclet, ``LeanTaclet] do
    let some (.inductInfo ii) := (← getEnv).find? J | continue
    out := out ++ ii.ctors
  return out

/-- The rule `Stmt.step` fires on the focus `f` (quoted), by name, and its
label: `emptyModality`, or the first constructor that derives it. -/
def labelOfFocus? (f : Expr) : MetaM (Option (Lean.Name × Expr)) := do
  if f.isAppOf ``Focus.empty then
    return some (`emptyModality, mkApp (mkConst ``StepRule.emptyModality) (f.getArg! 0))
  let a := f.getAppArgs
  unless a.size == 6 do return none
  let cands ← holeCandidates a[5]!
  let pre := (cands, ← FindHeads.of a[5]! cands)
  for c in ← allRuleCtors do
    if let some l ← labelAs? c a[1]! a[2]! a[5]! pre then return some (lastName c, l)
  return none

/-- The label of `~[r]~>` on the focus `f`: the constructor `r` must derive it. -/
def labelFor (r : Lean.Name) (f : Expr) (where_ : Expr) : MetaM Expr := do
  -- printed only for an error: a line's print is a delaboration
  let at_ : MetaM MessageData := indentLine where_
  if r == `emptyModality then
    unless f.isAppOf ``Focus.empty do
      throwError "~[{r}]~>: the program of{← at_}\nis not done"
    return mkApp (mkConst ``StepRule.emptyModality) (f.getArg! 0)
  let a := f.getAppArgs
  unless a.size == 6 do throwError "~[{r}]~>: the step on{← at_}\nends a program"
  for c in ← ruleCtors r do
    if let some l ← labelAs? c a[1]! a[2]! a[5]! then return l
  let found := match ← labelOfFocus? f with
    | some (n, _) => m!"{n}"
    | none => m!"no rule of the table"
  throwError "~[{r}]~>: the rule for{← at_}\nis {found}, not {r}"

/-- A derivation, with the auxiliary lemmas the elaborator abstracted it into
unfolded, down to a constructor. -/
partial def tacletHead (d : Expr) : MetaM Expr := do
  let d ← whnfCore d
  let .const c us := d.getAppFn | return d
  if (`Solidity.Taclet).isPrefixOf c || (`Solidity.LeanTaclet).isPrefixOf c then return d
  match ← getConstInfo c with
  | info@(.thmInfo _) => tacletHead ((← instantiateValueLevelParams info us).beta d.getAppArgs)
  | _ => return d

/-- The name `~[r]~>` shows for a label. -/
def ruleName? (r : Expr) : MetaM (Option Lean.Name) := do
  let r ← whnfR (← instantiateMVars r)
  if r.isAppOf ``StepRule.emptyModality then return some `emptyModality
  unless r.isAppOf ``StepRule.taclet do return none
  let rule ← whnfCore r.appArg!
  unless rule.isAppOf ``Rule.key || rule.isAppOf ``Rule.lean do return none
  let d ← tacletHead rule.appArg!
  return d.getAppFn.constName?.map lastName

/-! ## Written lines -/

/-- A written line: left to be found (`_`), a formula in `dl`'s text, or a
term. -/
inductive Written where
  | hole
  | text (c : Lean.Term) (m? : Option Lean.Term) (φ : TSyntax `dl_fml)
  | term (t : Lean.Term)

/-- The `}` items of a modality's program dropped: `core_item`'s text read
as the statements it holds. -/
partial def dropBlockEnds (stx : Syntax) : Syntax :=
  let stx := stx.setArgs (stx.getArgs.map dropBlockEnds)
  match (⟨stx⟩ : TSyntax `dl_fml) with
  | `(dl_fml| ⟨ $[$ss;]* } $items* ⟩ $φ:dl_fml) =>
    let ss' := ss ++ items.filterMap fun i => match i with
      | `(core_item| $s:sol_stmt ;) => some s
      | _ => none
    Unhygienic.run `(dl_fml| ⟨ $[$ss';]* ⟩ $φ) |>.raw
  | `(dl_fml| ⟨[ $[$ss;]* } $items* ]⟩ $φ:dl_fml) =>
    let ss' := ss ++ items.filterMap fun i => match i with
      | `(core_item| $s:sol_stmt ;) => some s
      | _ => none
    Unhygienic.run `(dl_fml| ⟨[ $[$ss';]* ]⟩ $φ) |>.raw
  | `(dl_fml| [ $[$ss;]* } $items* ] $φ:dl_fml) =>
    let ss' := ss ++ items.filterMap fun i => match i with
      | `(core_item| $s:sol_stmt ;) => some s
      | _ => none
    Unhygienic.run `(dl_fml| [ $[$ss';]* ] $φ) |>.raw
  | _ => stx

/-- How a line is written. -/
def Written.of (stx : Syntax) : Written :=
  if stx.isOfKind ``Lean.Parser.Term.hole || stx.isOfKind ``Lean.Parser.Term.syntheticHole then .hole
  else
    let dlf (φ : TSyntax `dl_fml) : TSyntax `dl_fml := ⟨dropBlockEnds φ⟩
    match (⟨stx⟩ : Lean.Term) with
    | `(cdl![ $m ]{ $φ:dl_fml }) => .text (Unhygienic.run `(InContract.contract)) (some m) (dlf φ)
    | `(cdl!{ $φ:dl_fml }) => .text (Unhygienic.run `(InContract.contract)) none (dlf φ)
    | `(cdl[ $c, $m ]{ $φ:dl_fml }) => .text c (some m) (dlf φ)
    | `(cdl[ $c ]{ $φ:dl_fml }) => .text c none (dlf φ)
    | `(dl![ $m ]{ $φ:dl_fml }) => .text (Unhygienic.run `(InContract.contract)) (some m) (dlf φ)
    | `(dl!{ $φ:dl_fml }) => .text (Unhygienic.run `(InContract.contract)) none (dlf φ)
    | `(dl[ $c, $m ]{ $φ:dl_fml }) => .text c (some m) (dlf φ)
    | `(dl[ $c ]{ $φ:dl_fml }) => .text c none (dlf φ)
    | t => .term t

/-- The holes of a written formula, elaborated: each a Lean term. -/
def holeTerms (φ : TSyntax `dl_fml) : TermElabM (Array Syntax × Array Expr) := do
  let holes := fmlHoles φ
  let es ← holes.mapM fun h => do
    let some t := fmlHole? h | throwError "dl: not a formula hole"
    withRef h do
      let e ← withoutAutoBoundImplicit <| elabTerm t none
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
  return (holes, es)

/-- The `i` of a slot's key (`LineKey.slot i`, quoted). -/
def keySlot? (e : Expr) : Option Nat := do
  guard (e.isAppOfArity ``LineKey.slot 1)
  e.appArg!.rawNatLit? <|> e.appArg!.nat?

/-- The readings of a written formula, its Lean formulas in slots (the
`j`th hole's `LineKey.slot j`), each its key, quoted: the scoped reading
with its parameters open (`elabDlOpen`, `Fml.lineKey`), or with no modality
the line read by name (`elabKeyQ`).  At the diamond and at the box when `m`
is a variable, once otherwise. -/
def readings (c : Lean.Term) (m? : Option Expr) (holes : Array Syntax) (φ : TSyntax `dl_fml) :
    TermElabM (Array Expr) := do
  let μs : Array (Option Lean.Name) := match m? with
    | some m =>
      if m.isConstOf ``Modality.diamond || m.isConstOf ``Modality.box then #[m.constName?]
      else #[``Modality.diamond, ``Modality.box]
    | none => #[none]
  -- `elabAgainst`'s evaluation, both readings in one (each evaluation compiles
  -- its term), with no kernel check of the throwaway definition
  -- (`evalQuoted`): the readings are compared with the computed lines'
  let reads ← μs.mapM fun μ => do
    let raw ← liftMacroM (expandFml { either := μ.map fun n => (mkCIdent n : Lean.Term), holes } φ)
    -- applications built directly: in a quotation `$a $b` reads `$b` as a chain arrow
    if rawHasModal raw then
      let rd : Lean.Term := Syntax.mkApp (mkCIdent ``elabDlOpen) #[c, raw]
      pure (Syntax.mkApp (mkCIdent ``Except.map) #[mkCIdent ``Fml.openKeyQ, rd])
    else
      -- with no modality, read by name (`elabKeyQ`): a line past the program
      -- need not declare a memory local it no longer writes
      pure (Syntax.mkApp (mkCIdent ``elabKeyQ) #[c, raw])
  let ty := mkApp (mkConst ``List [0]) (mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String)
    (mkConst ``Lean.Expr))
  let e ← elabTermEnsuringType (← `([$reads,*])) ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let rs ← unsafe evalQuoted (List (Except String Lean.Expr)) ty e
  rs.toArray.mapM fun
    | .ok r => pure r
    | .error msg => throwError "Solidity elaboration failed: {msg}"

/-- A key with each slot read as the written formula's: `LineKey.slot j`,
`j` the hole of the postcondition in slot `i`. -/
def toWrittenSlots (sp : Splice) (holes : Array Expr) (e : Expr) : Expr :=
  e.replace fun x => do
    let i ← keySlot? x
    let p ← sp.posts[i]?
    let j ← holes.findIdx? fun h => h == p.appArg! || h == p
    pure (mkApp (mkConst ``LineKey.slot) (toExpr j))

/-- A key and the keys under its leading `∀`s. -/
partial def underAlls (e : Expr) : List Expr :=
  if e.isAppOfArity ``LineKey.all 3 then e :: underAlls e.appArg! else [e]

/-- The written text `φ` read (`readings`), with its holes elaborated; none
when its modality is not the chain's. -/
def readWritten (sp : Splice) (c : Lean.Term) (m? : Option Lean.Term) (φ : TSyntax `dl_fml) :
    TermElabM (Option (Array Expr × Array Expr)) := do
  let m? ← m?.mapM fun m => do instantiateMVars (← elabTermEnsuringType m (mkConst ``Modality))
  -- the written modality is the chain's
  if let (some m, some m') := (m?, sp.modality) then
    unless m == m' do return none
  let (hs, es) ← holeTerms φ
  let rs ← readings c (m?.orElse fun _ => sp.modality) hs φ
  return some (es, rs)

/-- Whether the readings `rs` of a written text, its holes `es`, are the
computed line whose keys are `keys` (once per modality run). -/
def readingMatches (sp : Splice) (es rs keys : Array Expr) : Bool :=
  let es' := keys.map (toWrittenSlots sp es)
  -- the written text may leave out the parameters `cdl!` binds outermost
  let same (r e : Expr) : Bool := (underAlls e).contains r
  if rs.size == es'.size then (rs.zip es').all fun (r, e) => same r e
  -- a constant modality read once against both runs: the run's own
  else es'.any (same rs[0]! ·)

/-- Whether the written line `w` is the computed line whose keys are
`keys` (once per modality run), the formulas of the computed lines `sp`. -/
def matchWritten (sp : Splice) (w : Written) (B : Expr) (keys : Array Expr) :
    TermElabM Bool := do
  match w with
  | .hole => return true
  | .term t =>
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    return e == B || (← withReducible (isDefEq e B))
  | .text c m? φ =>
    let some (es, rs) ← readWritten sp c m? φ | return false
    return readingMatches sp es rs keys

/-- `matchWritten w` against many computed lines (a `~*>`'s, a `~~>`'s, the
merges): the written text read once, on the first line it is checked
against, since its reading (two evaluations under a modality variable) does
not depend on the line. -/
def writtenMatcher (w : Written) :
    TermElabM (Splice → Expr → Array Expr → TermElabM Bool) := do
  match w with
  | .text c m? φ =>
    let memo ← IO.mkRef (none : Option (Option Expr × Option (Array Expr × Array Expr)))
    return fun sp _ keys => do
      let r ← match ← memo.get with
        | some (μ, r) => if μ == sp.modality then pure r else readWritten sp c m? φ
        | none =>
          let r ← readWritten sp c m? φ
          memo.set (some (sp.modality, r))
          pure r
      let some (es, rs) := r | return false
      return readingMatches sp es rs keys
  | _ => return fun sp B keys => matchWritten sp w B keys

/-- The computed line, shown (`#derivation`). -/
def showLines (φ : Expr) (lines : List Line) : MetaM MessageData := do
  let mut out := m!"{← indentLine φ}"
  for l in lines do
    let r := match ← labelOfFocus? l.focus with
      | some (n, _) => toString n
      | none => "?"
    out := out ++ m!"\n  ~[{r}]~>{← indentLine l.fml}"
  return out

/-- The computed lines, shown for an error as today's `sol_chain` shows them
(as today's chains' `notReached` did): every line with the rule that
reached it. -/
def showLinesErr (φ : Expr) (lines : List Line) : MetaM MessageData := do
  let mut out := m!"    {← showLine φ}"
  for l in lines do
    let r := match ← labelOfFocus? l.focus with
      | some (n, _) => toString n
      | none => "?"
    out := out ++ m!"\n  ~[{r}]~>\n    {← showLine l.fml}"
  return out

def modalStopNote (run : Run) : MessageData :=
  match run.modalStop, run.splice.modality with
  | true, some m => m!"\n  (the line after {modalityStop m})"
  | _, _ => m!""

/-! ## Past the program: the line written -/

/-- The identifiers of a piece of syntax, in order. -/
partial def synIdents : Syntax → List String
  | .ident _ _ n _ => [n.eraseMacroScopes.toString]
  | .node _ _ args => args.toList.flatMap synIdents
  | _ => []

/-- The line written `w`, read where it stands (`cdl[c, m]{ … }`), as a scoped
formula, its postcondition at the context it stands in: with the
parameters it reads before anything binds them, or, where its
postcondition then stands at another context, with one of its names kept
a parameter (`elabDlCN`'s `keep`: a local an update assigns past the
program, `{ … ‖ v := 0 }`, that the first line reads as a parameter). -/
def writtenFml (w : Written) : TermElabM Expr := do
  match w with
  | .hole => throwError "the line written is `_`"
  | .term t =>
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  | .text c m? φ =>
    let names := synIdents φ.raw
    for keep in [] :: names.eraseDups.map ([·]) do
      let s ← saveState
      try
        let e ← instantiateMVars (← withoutErrToSorry (elabCdlAt c m? φ (keep := keep)))
        if e.hasSyntheticSorry then throwError "not read"
        Meta.check e
        return e
      catch _ => s.restore
    throwError "the line written does not read where it stands"

/-- The line written `w` in a message: read where it stands, or as text. -/
def writtenMsg (w : Written) : TermElabM MessageData := do
  let s ← saveState
  try indentLine (← writtenFml w)
  catch _ => s.restore; pure m!" the line written"

/-- The rewrites `~~>` tries on a line while its program is open, after the
merges: KeY's names, no law (a law is named, `~[r]~>`). -/
def openRwNames : List Lean.Name :=
  [`sequentialToParallel, `applyOnRigid, `applyOnPV, `concrete, `simplifyUpdate]

/-- One rewrite of a line while its program is open: the line it leaves,
that line's splice and keys, the KeY name a chain writes it by, its
link (`Link.merge`, `Link.rw`), and the proof of `L ~~> it`, built when
asked. -/
structure OpenStep where
  fml : Expr
  splice : Splice
  keys : Array Expr
  name : Lean.Name
  link : Expr
  proof : TermElabM Expr

/-- The rewrites of the line `L` while its program is open: the merges of
its spine, then `openRwNames`. -/
def openRwSteps (L : Expr) : TermElabM (List OpenStep) := do
  let run ← runChain L
  unless run.isOpen do return []
  let (C, Γ) ← lineType L
  let fml := mkApp2 (mkConst ``Fml) C Γ
  let mut out := []
  let (sp, ms) ← mergeCands L
  for c in ms do
    let pf : TermElabM Expr := do
      let lhs := mkAppN (mkConst ``Fml.mergeRun) #[C, Γ, toExpr c.k, toExpr c.n, L]
      let h ← kernelReflOrCases sp.modality lhs (mkApp2 (mkConst ``Option.some [0]) fml c.fml)
      mkAppM ``Fml.mergeRun_leads #[toExpr c.k, toExpr c.n, L, h]
    let lnk := mkApp3 (mkConst ``Link.merge) C (toExpr c.k) (toExpr c.n)
    out := out ++ [OpenStep.mk c.fml sp c.keys `sequentialToParallel lnk pf]
  for n in openRwNames do
    let (sp, cs, _) ← scopedRwCands L (.table n)
    for c in cs do
      let pf : TermElabM Expr := do
        let lhs := mkAppN (mkConst ``FmlRw.apply) #[C, c.rw, Γ, L]
        let h ← kernelReflOrCases sp.modality lhs (mkApp2 (mkConst ``Option.some [0]) fml c.fml)
        mkExpectedTypeHint (mkAppN (mkConst ``FmlRw.sound) #[C, c.rw, Γ, L, c.fml, h])
          (mkApp4 (mkConst ``Fml.Leads) C Γ L c.fml)
      let lnk := mkApp3 (mkConst ``Link.rw) C (toExpr n.toString) c.rw
      out := out ++ [OpenStep.mk c.fml sp c.keys n lnk pf]
  return out

/-- How many rewrites `~~>` looks for while the program is open. -/
def openRwDepth : Nat := 3

/-- How many lines `openRwPath` expands at most. -/
def openRwNodes : Nat := 48

/-- At most `depth` rewrites of the line `L` while its program is open
(`openRwSteps`), breadth first, each line expanded once and at most
`openRwNodes` of them, each with its own heartbeats: the rewrites to the
first line `fits` accepts, and why the search stopped short, if it did (a
step that failed or ran out of heartbeats is a leaf). -/
def openRwPath (L : Expr) (fits : Expr → Splice → Array Expr → TermElabM Bool)
    (depth : Nat := openRwDepth) : TermElabM (Option (List OpenStep) × Option MessageData) := do
  let mut frontier : Array (Expr × List OpenStep) := #[(L, [])]
  let mut seen : Std.HashSet Expr := ({} : Std.HashSet Expr).insert L
  let mut nodes := 0
  let mut note : Option MessageData := none
  for _ in [0:depth] do
    let mut next := #[]
    for (X, path) in frontier do
      if nodes ≥ openRwNodes then
        return (none, some m!"the search stopped after {openRwNodes} lines")
      nodes := nodes + 1
      let r : Except Exception (List OpenStep) ←
        tryCatchRuntimeEx (.ok <$> withCurrHeartbeats (openRwSteps X)) fun e => pure (.error e)
      match r with
      | .error e => note := note <|> some m!"a step of the search failed: {e.toMessageData}"
      | .ok steps =>
        for st in steps do
          if ← fits st.fml st.splice st.keys then return (some (path ++ [st]), none)
        for st in steps do
          unless seen.contains st.fml do
            seen := seen.insert st.fml
            next := next.push (st.fml, path ++ [st])
    frontier := next
  return (none, note)

/-- The proof of `L ~~> B` along the rewrites `path` from `L`. -/
def OpenStep.leads (L : Expr) : List OpenStep → TermElabM Expr
  | [] => mkAppM ``Fml.Leads.self #[L]
  | [st] => st.proof
  | st :: rest => do mkAppM ``Fml.Leads.comp #[← st.proof, ← OpenStep.leads st.fml rest]

/-- Whether a line written may keep a program: a rewrite while the program
is open keeps it, so a line written with none (no program brackets, no
term escape, no formula variable but a postcondition) is not looked for
among them (`openRwPath`), and reads past the program. -/
partial def Written.mayBeOpen (w : Written) : TermElabM Bool := do
  match w with
  | .text _ _ φ => go φ.raw
  | _ => return true
where
  go (s : Syntax) : TermElabM Bool := do
    match s with
    | .atom _ v => return v == "⟨" || v == "[" || v == "‹"
    | .node _ k args =>
      if k == ``Solidity.dlFmlVar then
        let some d := (← getLCtx).findFromUserName? s[0].getId | return true
        let ty ← whnfR (← instantiateMVars d.type)
        return !(ty.isAppOf ``Solidity.Post)
      args.anyM go
    | _ => return false

/-! ## The chain, elaborated -/

/-- `Link.one`, `Link.many`, `Link.rule r` and the pair type of a chain. -/
def linkTy (C : Expr) : Expr := mkApp (mkConst ``Link) C

/-- Why no rewrite past the program gives the line written `w` after `L`:
the rewrite applies nowhere (and why: a side condition, a modality), or
what it gives; `~=>`, what each rewrite that applies gives. -/
def pastRefusal (L : Expr) (w : Written) (rw? : Option (Option (Ident × RwArrow))) :
    TermElabM MessageData := do
  let written : TermElabM MessageData := writtenMsg w
  match rw? with
  | some (some (r, a)) =>
    let n := r.getId
    let (sp, cands, failed) ← scopedRwCands L a (past := true)
    if cands.isEmpty then
      if n == `simplifyUpdate && !sp.posts.isEmpty then
        return m!"~[{n}]~>: on{← indentLine L}\nit looks at the line's modality or postcondition, \
          which are not known: state the line for a concrete one"
      let note := match failed with
        | some m => m!"\n({m})"
        | none => m!""
      return m!"~[{n}]~>: {n} does not apply to{← indentLine L}{note}"
    let ls ← cands.mapM fun c => indentLine c.fml
    return m!"~[{n}]~>: on{← indentLine L}\nit gives{MessageData.joinSep ls ""}\nnot{← written}"
  | _ =>
    let mut gives : Array MessageData := #[]
    let arrows := (← rwAnyArrows).toArray
    let (_, rs) ← scopedRwCandsMany L (arrows.map (·.2)) (past := true)
    for ((n, _), (cands, _)) in arrows.zip rs do
      if let some c := cands.head? then
        gives := gives.push m!"{n} gives{← indentLine c.fml}"
    let note := if gives.isEmpty then m!"\nno rewrite applies to it" else
      m!"\n{MessageData.joinSep gives.toList "\n"}"
    return m!"~=>: no rewrite gives{← written}\nfrom{← indentLine L}{note}"

/-- A written chain whose first line `A` is a scoped formula: every line
after it computed, checked against its text (`matchWritten`), past the
program by `Calculus/RewritePast.lean`'s and `Calculus/RewriteLaws.lean`'s
rewrites. -/
def elabCoreChain (stx : Syntax) (A : Expr) : TermElabM Expr := do
  let (C, Γ) ← lineType A
  let fml := mkApp2 (mkConst ``Fml) C Γ
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (linkTy C) fml
  let mk (l B : Expr) : Expr := mkAppN (mkConst ``Prod.mk [0, 0]) #[linkTy C, fml, l, B]
  let mut cur := A
  let mut ws : Array Expr := #[]
  let mut single : Option Expr := none
  let links := stx[1].getArgs
  for h : i in [0:links.size] do
    let l := links[i]
    let w := Written.of l[1]
    let arrow : TSyntax `chain_arrow := ⟨l[0]⟩
    let rw? ← match arrow with
      | `(chain_arrow| ~[ $r:ident ]~>) => do
        if !(← ruleCtors r.getId).isEmpty then pure none
        else pure ((← rwArrow? r).map fun a => (some (r, a)))
      | `(chain_arrow| ~=>) => pure (some none)
      | _ => pure none
    -- a merge or rewrite of the scoped line, while its program is open and
    -- past it (`Calculus/RewriteScoped.lean`, `Calculus/RewritePast.lean`,
    -- `Calculus/RewriteLaws.lean`)
    let isOpen ← if rw?.isSome then (·.isOpen) <$> runChain cur else pure false
    let onScoped := rw?.isSome
    -- past the program a written line the scoped reading refuses fits no rewrite
    let fitsS (fits : Splice → Expr → Array Expr → TermElabM Bool) (sp : Splice) (B : Expr)
        (er : Array Expr) : TermElabM Bool := do
      if isOpen then return ← fits sp B er
      let s ← saveState
      try Term.withoutErrToSorry (fits sp B er) catch _ => s.restore; pure false
    if let some (some (r, .table `sequentialToParallel)) := rw? then
      if onScoped then
        -- past the program the merges are `FmlRw.mergePast`'s (`scopedRwCands`)
        let (sp, cands) ← if isOpen then mergeCands cur else pure ({}, [])
        let fits ← writtenMatcher w
        if let some c ← cands.findM? fun c => fitsS fits sp c.fml c.keys then
          let lnk := mkApp3 (mkConst ``Link.merge) C (toExpr c.k) (toExpr c.n)
          ws := ws.push (mk lnk c.fml)
          if links.size == 1 then
            single := some (mkAppN (mkConst ``Fml.MergeBy) #[C, Γ, toExpr c.k, toExpr c.n, cur, c.fml])
          cur := c.fml
          continue
        -- over a state write, under a branch (`FmlRw.stateMerge`, `FmlRw.mergeIn`)
        let (sp', below, _) ← scopedRwCands cur (.table `sequentialToParallel)
          (branches := isOpen) (past := !isOpen)
        if let some c ← below.findM? fun c => fitsS fits sp' c.fml c.keys then
          let n := toExpr r.getId.toString
          ws := ws.push (mk (mkApp3 (mkConst ``Link.rw) C n c.rw) c.fml)
          if links.size == 1 then
            single := some (mkAppN (mkConst ``Fml.RwBy) #[C, Γ, n, c.rw, cur, c.fml])
          cur := c.fml
          continue
        if isOpen then
          if cands.isEmpty && below.isEmpty then
            throwError "~[{r}]~>: {r} does not apply to{← indentLine cur}"
          throwError "~[{r}]~>: no merge of the update spine of{← indentLine cur}\n\
            is the line written{indentD (.ofSyntax l[1])}\n\
            The merges:{← (cands.map (·.fml) ++ below.map (·.fml)).foldlM (fun acc c => do
              pure (acc ++ m!"\n  ~[sequentialToParallel]~>{← indentLine c}")) m!""}"
    if let some (some (r, a)) := rw? then
      if onScoped then
        let run ← runChain cur
        let (sp, cands, failed) ← scopedRwCands cur a (past := !isOpen)
        let fits ← writtenMatcher w
        if let some c ← cands.findM? fun c => fitsS fits sp c.fml c.keys then
          let n := toExpr r.getId.toString
          ws := ws.push (mk (mkApp3 (mkConst ``Link.rw) C n c.rw) c.fml)
          if links.size == 1 then
            single := some (mkAppN (mkConst ``Fml.RwBy) #[C, Γ, n, c.rw, cur, c.fml])
          cur := c.fml
          continue
        if isOpen then
          let note := match failed with
            | some m => m!"\n({m})"
            | none => m!""
          if cands.isEmpty then
            throwError "~[{r}]~>: {r} does not apply to{← indentLine cur}\n\
              while the program is open{note}"
          throwError "~[{r}]~>: no rewrite by {r} of{← indentLine cur}\n\
            is the line written{indentD (.ofSyntax l[1])}\n\
            It gives:{← cands.foldlM (fun acc c => do
              pure (acc ++ m!"\n  ~[{r}]~>{← indentLine c.fml}")) m!""}"
    if let some none := rw? then
      if onScoped then
        -- `~=>`: the first merge or rewrite of the scoped line that gives the
        -- line written (`openRwSteps`)
        let fits ← writtenMatcher w
        if let some st ← (← openRwSteps cur).findM?
            fun st => fitsS fits st.splice st.fml st.keys then
          ws := ws.push (mk st.link st.fml)
          cur := st.fml
          continue
        if isOpen then
          throwError "~=>: no merge nor rewrite ({", ".intercalate (openRwNames.map toString)}) \
            of{← indentLine cur}\nis the line written{indentD (.ofSyntax l[1])}\n\
            while the program is open"
        -- past the program: the first rewrite of `rwAnyArrows`, in order,
        -- that gives the line written
        let run ← runChain cur
        let arrows := (← rwAnyArrows).toArray
        let (sp, rs) ← scopedRwCandsMany cur (arrows.map (·.2)) (past := true)
        let mut found := none
        for ((n, _), (cands, _)) in arrows.zip rs do
          if let some c ← cands.findM? fun c => fitsS fits sp c.fml c.keys then
            found := some (n, c)
            break
        if let some (n, c) := found then
          ws := ws.push (mk (mkApp3 (mkConst ``Link.rw) C (toExpr n) c.rw) c.fml)
          cur := c.fml
          continue
    if onScoped && !isOpen then
      throwError (← pastRefusal cur w rw?)
    let run ← runChain cur
    -- the line written, as a line prints where it elaborates alone (no
    -- hole, no postcondition of the line before), else its text; lazily, so
    -- that an error a search catches costs nothing
    let written : TermElabM MessageData := do
      let stx := l[1]
      return indentD <| .ofLazyM do
        let shown? ← (Term.withoutErrToSorry do
          try
            let e ← elabTerm stx none
            synthesizeSyntheticMVarsNoPostponing
            let e ← instantiateMVars e
            if e.hasMVar then return none
            return some (← showLine e)
          catch _ => return none : TermElabM _).run'
        return shown?.getD (.ofSyntax stx)
    let notReached (ls : List Line) : TermElabM Unit := do
      throwError "sol_chain: the derivation of{← indentLine cur}\ndoes not reach{← written}\n\
        Its lines:\n{← showLinesErr cur ls}{modalStopNote run}"
    match arrow with
    | `(chain_arrow| ~*>) =>
      -- a line given as a term is the relation's, unchecked here (`∃ ψ, φ ~*> ψ`)
      if let .term t := w then
        let B ← elabTermEnsuringType t fml
        ws := ws.push (mk (mkApp (mkConst ``Link.many) C) B)
        if links.size == 1 then single := some (mkAppN (mkConst ``Fml.Steps) #[C, Γ, cur, B])
        cur := B
        continue
      let cands : List (Expr × Array Expr) := (cur, run.keys) :: run.lines.map fun l => (l.fml, l.keys)
      let pick ← match w with
        | .hole => pure (cands.getLast?.map (·.1))
        | _ => do
          let fits ← writtenMatcher w
          cands.findSomeM? fun (B, er) => do
            if ← fits run.splice B er then pure (some B) else pure none
      let some B := pick | notReached run.lines
      ws := ws.push (mk (mkApp (mkConst ``Link.many) C) B)
      if links.size == 1 then single := some (mkAppN (mkConst ``Fml.Steps) #[C, Γ, cur, B])
      cur := B
    | `(chain_arrow| ~>) =>
      -- a line given as a term is the relation's, unchecked here (`∃ ψ, φ ~> ψ`)
      if let .term t := w then
        let B ← elabTermEnsuringType t fml
        ws := ws.push (mk (mkApp (mkConst ``Link.one) C) B)
        if links.size == 1 then single := some (mkAppN (mkConst ``Fml.OneStep) #[C, Γ, cur, B])
        cur := B
        continue
      let some B := run.lines.head? |
        match run.modalStop, run.splice.modality with
        | true, some m => throwError "sol_chain: the line after{← indentLine cur}\n{modalityStop m}"
        | _, _ => throwError "sol_chain: no rule applies to{← indentLine cur}"
      unless ← matchWritten run.splice w B.fml B.keys do notReached [B]
      ws := ws.push (mk (mkApp (mkConst ``Link.one) C) B.fml)
      if links.size == 1 then single := some (mkAppN (mkConst ``Fml.OneStep) #[C, Γ, cur, B.fml])
      cur := B.fml
    | _ =>
      let some B := run.lines.head? |
        match run.modalStop, run.splice.modality with
        | true, some m => throwError "sol_chain: the line after{← indentLine cur}\n{modalityStop m}"
        | _, _ => throwError "sol_chain: no rule applies to{← indentLine cur}"
      unless ← matchWritten run.splice w B.fml B.keys do notReached [B]
      match arrow with
      | `(chain_arrow| ~[ $r:ident ]~>) =>
        let lbl ← labelFor r.getId B.focus cur
        ws := ws.push (mk (mkApp2 (mkConst ``Link.rule) C lbl) B.fml)
        if links.size == 1 then single := some (mkAppN (mkConst ``Fml.StepBy) #[C, Γ, lbl, cur, B.fml])
      | _ =>
        ws := ws.push (mk (mkApp (mkConst ``Link.one) C) B.fml)
        if links.size == 1 then single := some (mkAppN (mkConst ``Fml.OneStep) #[C, Γ, cur, B.fml])
      cur := B.fml
  if let some e := single then return e
  return mkAppN (mkConst ``Fml.Via) #[C, Γ, A, ← mkListLit pairTy ws.toList]

/-- A chain, read here when its first line is a scoped formula, and by
`Calculus/RewriteChains.lean` otherwise. -/
syntax (name := chainAnyStx) "chain_any% " term : term

/-- Every chain goes through `elabChainAny`, which reads its first line once
to pick the reader. -/
@[macro Solidity.chainStx] def expandChainAny : Macro := fun stx =>
  return mkNode ``chainAnyStx #[mkAtom "chain_any% ", stx]

/-- The written lines of `calc` steps, by the metavariable that stands for the
line until `sol_chain` computes it from the line before: the text and the
rule `~[r]~>` names. -/
initialize pendingLines : EnvExtension (Std.HashMap MVarId (Syntax × Option Lean.Name)) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/-- A `calc` step `_ R B` on scoped lines: `_` the line before, which `calc`
fills in, and `B` a line computed from it, a metavariable for now that
`sol_chain` assigns (`pendingLines`), the text checked then. -/
def elabCalcStep (inner : Syntax) : TermElabM (Option Expr) := do
  let links := inner[1].getArgs
  unless links.size == 1 do return none
  let l := links[0]!
  let some b ← observing? (do
      let b ← elabTerm l[1] none
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars b) | return none
  unless ← isCoreLine b do return none
  let (C, Γ) ← lineType b
  let fml := mkApp2 (mkConst ``Fml) C Γ
  let A ← mkFreshExprMVar fml
  let B ← mkFreshExprMVar fml
  let arrow : TSyntax `chain_arrow := ⟨l[0]⟩
  let rule? : Option Lean.Name := match arrow with
    | `(chain_arrow| ~[ $r:ident ]~>) => some r.getId
    | _ => none
  let pend (key : Expr) : TermElabM Unit :=
    modifyEnv fun env => pendingLines.modifyState env (·.insert key.mvarId! (l[1], rule?))
  match arrow with
  | `(chain_arrow| ~>) => pend B; return some (mkAppN (mkConst ``Fml.OneStep) #[C, Γ, A, B])
  | `(chain_arrow| ~*>) => pend B; return some (mkAppN (mkConst ``Fml.Steps) #[C, Γ, A, B])
  | `(chain_arrow| ~[ $r:ident ]~>) =>
    if r.getId == `sequentialToParallel then
      let k ← mkFreshExprMVar (mkConst ``Nat)
      pend k
      return some (mkAppN (mkConst ``Fml.MergeBy)
        #[C, Γ, k, ← mkFreshExprMVar (mkConst ``Nat), A, B])
    if (← ruleCtors r.getId).isEmpty && r.getId != `emptyModality then
      -- a rewrite while the program is open (the line written still has it)
      let some _ ← rwArrow? r | return none
      unless (← runChain b).isOpen do return none
      let rw ← mkFreshExprMVar (mkApp (mkConst ``FmlRw) C)
      pend rw
      return some (mkAppN (mkConst ``Fml.RwBy) #[C, Γ, toExpr r.getId.toString, rw, A, B])
    let lbl ← mkFreshExprMVar (mkApp (mkConst ``StepRule) C)
    pend lbl
    return some (mkAppN (mkConst ``Fml.StepBy) #[C, Γ, lbl, A, B])
  | _ => return none

@[term_elab chainAnyStx] def elabChainAny : TermElab := fun stx expectedType? => do
  let inner := stx[1]
  -- `calc` writes the step's `_` as `(_ : T)`, `T` the type of the line before
  let isHole (s : Syntax) : Bool := s.isOfKind ``Lean.Parser.Term.hole ||
    (s.isOfKind ``Lean.Parser.Term.typeAscription && s[1].isOfKind ``Lean.Parser.Term.hole)
  if isHole inner[0] then
    if let some e ← elabCalcStep inner then return e
  let st ← saveState
  let first? ← observing? do
    let a ← elabTerm inner[0] none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars a
  if let some a := first? then
    if !a.hasMVar && (← isCoreLine a) then return ← elabCoreChain inner a
  st.restore
  elabTerm (← liftMacroM (Solidity.expandChainStx inner)) expectedType?

/-! ## `φ ~~> ψ` on scoped lines

With `open scoped Solidity.Scoped`, `A ~~> B` whose first line is scoped
reads `B` as the line of `A`'s derivation it is written as (`Fml.Leads`),
else as a scoped line with a program still open (a merged line, or one up
to `openRwDepth` merges and rewrites past a line of the derivation,
`Fml.Leads`), else past the program, the line it names (`Fml.LeadsK`,
`B` read where it stands, equal up to its binders' names to a line the
rewrites reach from the strategy's last line); where the
derivation stops on a modality variable the program is still open, and
that last reading is refused. -/

/-- `leads% A B`: `A ~~> B`, read by the first line's kind. -/
syntax (name := leadsAnyStx) "leads% " term:max term:max : term

@[term_elab leadsAnyStx] def elabLeadsAny : TermElab := fun stx _ => do
  let st ← saveState
  let first? ← observing? do
    let a ← elabTerm stx[1] none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars a
  let some A := first? | throwError "~~>: the first line is not known"
  unless !A.hasMVar && (← isCoreLine A) do
    st.restore
    throwError "~~>: the first line is a scoped formula: write it `dl!\{ … }` under \
      `open scoped Solidity.Scoped`{indentExpr A}"
  let (C, Γ) ← lineType A
  let bStx := if stx[2].isOfKind ``Lean.Parser.Term.paren then stx[2][1] else stx[2]
  let w := Written.of bStx
  let run ← runChain A
  let cands : List (Expr × Array Expr) := (A, run.keys) :: run.lines.map fun l => (l.fml, l.keys)
  let fits ← writtenMatcher w
  if let some B ← cands.findSomeM? (fun (B, er) => do
      if ← fits run.splice B er then pure (some B) else pure none) then
    return mkApp4 (mkConst ``Fml.Leads) C Γ A B
  -- a line of the derivation with its update spine merged (the program open)
  for (L, _) in cands do
    if !(← runChain L).isOpen then continue
    let (sp, ms) ← mergeCands L
    if let some c ← ms.findM? (fun c => fits sp c.fml c.keys) then
      return mkApp4 (mkConst ``Fml.Leads) C Γ A c.fml
  -- rewrites of a line whose program is still open (`Calculus/RewriteScoped.lean`)
  let mut stopped : Option MessageData := none
  if ← w.mayBeOpen then
    for (L, _) in cands do
      if !(← runChain L).isOpen then continue
      let (path?, note) ← openRwPath L (fun B sp er => fits sp B er)
      stopped := stopped <|> note
      if let some st := path?.bind (·.getLast?) then
        return mkApp4 (mkConst ``Fml.Leads) C Γ A st.fml
  let stopNote := match stopped with
    | some m => m!"\n({m})"
    | none => m!""
  unless (← whnfR Γ).isAppOf ``List.nil do
    throwError "~~>: the line after is no line of the derivation of{← indentLine A}{stopNote}"
  -- past the program the line after is `Update.lean`'s; where the derivation
  -- stops on a modality variable, the program is still open
  if run.modalStop then
    throwError "~~>: the line after is no line of the derivation of{← indentLine A}\n\
      nor reached from one by {", ".intercalate (openRwNames.map toString)} \
      (at most {openRwDepth} of them) while the program is open{modalStopNote run}{stopNote}"
  -- the line written, read where it stands: it names the line a chain of
  -- rewrites reaches, up to its binders' names (`Fml.LeadsK`)
  let L ← writtenFml w
  unless ← isDefEq (← inferType L) (mkApp2 (mkConst ``Fml) C Γ) do
    throwError "~~>: the line after is no scoped line of the contract{indentExpr L}"
  return mkAppN (mkConst ``Fml.LeadsK) #[C, A, L]

/-- `A ~~> B` on scoped lines prints as written. -/
@[app_unexpander Fml.Leads]
def unexpandLeads : PrettyPrinter.Unexpander
  | `($_ $a:term $b:term) => `($a:term ~~> $b:term)
  | _ => throw ()

/-! ## `sol_chain` on scoped chains -/

/-- The computed line `B` after `A`, its run. -/
def nextLine (A B : Expr) : MetaM (Run × Line) := do
  let run ← runChain A
  let some q := run.lines.head? | throwError "sol_chain: no rule applies to{← indentLine A}"
  if B.isMVar then
    unless ← isDefEq B q.fml do throwError "sol_chain: the line after is not{indentExpr B}"
    return (run, q)
  unless q.fml == B do
    throwError "sol_chain: the derivation of{← indentLine A}\ndoes not reach{← indentLine B}\n\
      Its lines:\n{← showLinesErr A [q]}{modalStopNote run}"
  return (run, q)

/-- Whether a goal is a scoped chain's. -/
partial def isCoreGoal (ty : Expr) : MetaM Bool := do
  let ty ← instantiateMVars ty
  if ty.isAppOf ``Fml.OneStep || ty.isAppOf ``Fml.StepBy || ty.isAppOf ``Fml.Steps ||
      ty.isAppOf ``Fml.MergeBy || ty.isAppOf ``Fml.RwBy || ty.isAppOf ``Fml.Via then return true
  if ty.isAppOfArity ``Nonempty 1 then return ← isCoreGoal ty.appArg!
  return false

/-- `sol_chain` on a scoped goal: each link by the kernel (`oneStepProof`,
`stepByProof`, `stepsProof`, `kernelReflOrCases` for a rewrite or a merge),
past the program too. -/
partial def solveCore (g : MVarId) : TermElabM Unit := do
  let ty ← instantiateMVars (← g.getType)
  -- a `calc` step: its line after computed from the line before, and checked
  -- against the text while it is a metavariable (`pendingLines`, keyed by the
  -- step's label, or by its line after for `~>`, `~*>`)
  let args := ty.getAppArgs
  let key? : Option Expr :=
    if ty.isAppOf ``Fml.StepBy || ty.isAppOf ``Fml.MergeBy then args[2]?
    else if ty.isAppOf ``Fml.RwBy then args[3]? else args.back?
  let pending := pendingLines.getState (← getEnv)
  let pend? : Option (Syntax × Option Lean.Name) := do
    let key ← key?
    guard key.isMVar
    pending[key.mvarId!]?
  if let some (wStx, rule?) := pend? then
    let A := args[args.size - 2]!
    let B := args.back!
    let w := Written.of wStx
    -- the line after: the text, while unknown; the line `calc` gave it, else
    let written ← writtenMatcher w
    let fits (B' : Expr) (sp : Splice) (er : Array Expr) : TermElabM Bool := do
      if B.isMVar then written sp B' er else isDefEq B B'
    if ty.isAppOf ``Fml.RwBy then
      let some r := rule? | throwError "sol_chain: no rewrite named"
      let some a ← rwArrow? (mkIdent r) | throwError "~[{r}]~>: no rewrite"
      let (sp, cands, _) ← scopedRwCands A a
      let some c ← cands.findM? fun c => fits c.fml sp c.keys
        | throwError "~[{r}]~>: no rewrite by {r} of{← indentLine A}\nis the line written"
      unless ← isDefEq B c.fml <&&> isDefEq args[3]! c.rw do
        throwError "sol_chain: the rewrite is not the next one"
    else if ty.isAppOf ``Fml.MergeBy then
      let (sp, cands) ← mergeCands A
      let some c ← cands.findM? fun c => fits c.fml sp c.keys
        | throwError "~[sequentialToParallel]~>: no merge of{← indentLine A}\nis the line written"
      unless ← isDefEq B c.fml <&&> isDefEq args[2]! (toExpr c.k) <&&> isDefEq args[3]! (toExpr c.n) do
        throwError "sol_chain: the merge is not the next one"
    else
      let run ← runChain A
      let cands : List (Expr × Array Expr) := if ty.isAppOf ``Fml.Steps then
          (A, run.keys) :: run.lines.map fun l => (l.fml, l.keys)
        else (run.lines.head?.map fun l => (l.fml, l.keys)).toList
      let some (B', _) ← cands.findM? fun (B', er) => fits B' run.splice er
        | throwError "sol_chain: the derivation of{← indentLine A}\ndoes not reach{indentD (.ofSyntax wStx)}\n\
            Its lines:\n{← showLines A run.lines}{modalStopNote run}"
      unless ← isDefEq B B' do throwError "sol_chain: the computed line is not the next one"
      if ty.isAppOf ``Fml.StepBy then
        let some q := run.lines.head? | throwError "sol_chain: no rule applies to{← indentLine A}"
        let some r := rule? | throwError "sol_chain: no rule named"
        let lbl ← labelFor r q.focus A
        unless ← isDefEq args[2]! lbl do throwError "sol_chain: the label does not fit"
    let ty' ← instantiateMVars ty
    if let some key := key? then
      if (← instantiateMVars key).isMVar then
        throwError "sol_chain: the `calc` step's line after is still unknown"
    return ← solveCore (← g.replaceTargetDefEq ty')
  match_expr ty with
  | Fml.OneStep _ _ A B =>
    let (run, q) ← nextLine A B
    g.assign (← oneStepProof run.splice A q)
  | Fml.StepBy _ _ r A B =>
    let (run, q) ← nextLine A B
    g.assign (← stepByProof run.splice r A q)
  | Fml.Steps _ _ A B =>
    let run ← runChain A
    -- a line left unknown (`∃ ψ, φ ~*> ψ`): the derivation's last
    if B.isMVar then
      let Z := (run.lines.getLast?.map (·.fml)).getD A
      unless ← isDefEq B Z do throwError "sol_chain: the last line is not{indentExpr B}"
      if (← instantiateMVars B).isMVar then throwError "sol_chain: the last line is unknown"
      return ← solveCore g
    let i ← if A == B then pure 0 else
      match run.lines.findIdx? (·.fml == B) with
      | some i => pure (i + 1)
      | none => throwError "sol_chain: the derivation of{← indentLine A}\ndoes not reach{← indentLine B}"
    g.assign (← stepsProof run.splice A (run.lines.take i))
  | Fml.MergeBy C Γ k n A B =>
    let sp ← collectPosts A {}
    let m? ← modalityOf? (punch C sp A)
    let lhs := mkAppN (mkConst ``Fml.mergeRun) #[C, Γ, k, n, A]
    let rhs := mkApp2 (mkConst ``Option.some [0]) (mkApp2 (mkConst ``Fml) C Γ) B
    g.assign (← kernelReflOrCases m? lhs rhs)
  | Fml.RwBy C Γ _ r A B =>
    let sp ← collectPosts A {}
    let m? ← modalityOf? (punch C sp A)
    let lhs := mkAppN (mkConst ``FmlRw.apply) #[C, r, Γ, A]
    let rhs := mkApp2 (mkConst ``Option.some [0]) (mkApp2 (mkConst ``Fml) C Γ) B
    g.assign (← kernelReflOrCases m? lhs rhs)
  | Nonempty T =>
    let t ← mkFreshExprMVar T
    solveCore t.mvarId!
    g.assign (mkApp2 (mkConst ``Nonempty.intro [1]) T t)
  | And P Q =>
    let a ← mkFreshExprMVar P
    let b ← mkFreshExprMVar Q
    solveCore a.mvarId!
    solveCore b.mvarId!
    g.assign (mkApp4 (mkConst ``And.intro) P Q a b)
  | Eq T a b =>
    unless ← kernelDefEq a b do
      throwError "sol_chain: the last scoped line, its binders' names aside, is not{indentExpr b}"
    g.assign (← mkExpectedTypeHint (← mkEqRefl b) (mkApp3 (mkConst ``Eq [1]) T a b))
  | True => g.assign (mkConst ``True.intro)
  | _ =>
    let ty' ← whnfR ty
    if ty' != ty then return ← solveCore (← g.replaceTargetDefEq ty')
    throwError "sol_chain: the goal is no chain on scoped lines{indentExpr ty}"

elab_rules : tactic
  | `(tactic| sol_chain) => Tactic.withMainContext do
    let g ← Tactic.getMainGoal
    unless ← isCoreGoal (← g.getType) do throwUnsupportedSyntax
    solveCore g
    Tactic.replaceMainGoal []

/-- Whether the term `t` is today's notation (`dl!{ … }`, `dl[C]{ … }`)
with the scope's switch off (`core_surface%`, `Calculus/Surface.lean`):
it reads as `Update.lean`'s formula, which no command here reads, so the
command refuses it without elaborating it (`notScopedNotation`;
`Tools/ProofTree.lean`'s `elabCoreFormula?` does the same). -/
def todaysNotation (t : Syntax) : TermElabM Bool := do
  let some (.atom _ v) := t.getHead? | return false
  unless v.startsWith "dl" do return false
  let flag := mkNode `Solidity.coreSurfaceFlag #[mkAtom "core_surface%"]
  let some out ← liftMacroM (expandMacro? flag) | return true
  return !(out.isIdent && out.getId.eraseMacroScopes == `true)

/-- What a command on scoped formulas says of `todaysNotation`. -/
def notScopedNotation {α : Type} (cmd : String) : TermElabM α :=
  throwError "{cmd}: not a scoped formula: write `cdl!\{ … }` or \
    `open scoped Solidity.Scoped`"

/-- `#derivation φ` for a scoped `φ`: the lines the strategy takes, each with
the rule that reached it. -/
elab_rules : command
  | `(command| #derivation $t) => Command.runTermElabM fun _ => do
    if ← todaysNotation t then notScopedNotation "#derivation"
    let φ ← instantiateMVars (← elabTerm t none)
    synthesizeSyntheticMVarsNoPostponing
    let φ ← instantiateMVars φ
    unless ← isCoreLine φ do throwUnsupportedSyntax
    let run ← runChain φ
    logInfo ((← showLines φ run.lines) ++ modalStopNote run)

/-! ## Printing -/

section Print
open PrettyPrinter Delaborator SubExpr

/-- The arrow a scoped link stands for. -/
def arrowOf (l : Expr) : MetaM (TSyntax `chain_arrow) := do
  let l ← whnfR (← instantiateMVars l)
  if l.isAppOf ``Link.one then `(chain_arrow| ~>)
  else if l.isAppOf ``Link.many then `(chain_arrow| ~*>)
  else if l.isAppOf ``Link.merge then `(chain_arrow| ~[$(mkIdent `sequentialToParallel):ident]~>)
  else if l.isAppOf ``Link.rw then
    let .lit (.strVal n) := l.getArg! 1 | failure
    `(chain_arrow| ~[$(mkIdent (.mkSimple n)):ident]~>)
  else if l.isAppOf ``Link.rule then
    let some n ← ruleName? l.appArg! | failure
    `(chain_arrow| ~[$(mkIdent n):ident]~>)
  else failure

/-- The links of a list of `(link, line)` pairs, printed. -/
def linkLines (ws : Expr) : MetaM (Array (TSyntax `chain_arrow × Lean.Term)) := do
  let some ws ← Solidity.listElems? ws | failure
  ws.mapM fun w => do
    let w ← whnfR w
    guard (w.isAppOfArity ``Prod.mk 4)
    pure (← arrowOf (w.getArg! 2), ← ppCoreLine (w.getArg! 3))

@[delab app.Solidity.Fml.OneStep]
def delabOneStep : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  return chainNode (← ppCoreLine (e.getArg! 2))
    #[(← `(chain_arrow| ~>), ← ppCoreLine (e.getArg! 3))]

@[delab app.Solidity.Fml.Steps]
def delabSteps : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  return chainNode (← ppCoreLine (e.getArg! 2))
    #[(← `(chain_arrow| ~*>), ← ppCoreLine (e.getArg! 3))]

@[delab app.Solidity.Fml.StepBy]
def delabStepBy : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 5)
  let some n ← ruleName? (e.getArg! 2) | failure
  return chainNode (← ppCoreLine (e.getArg! 3))
    #[(← `(chain_arrow| ~[$(mkIdent n):ident]~>), ← ppCoreLine (e.getArg! 4))]

/-- `φ ~[n]~> ψ`, a rewrite of the scoped line (`Calculus/RewriteScoped.lean`). -/
@[delab app.Solidity.Fml.RwBy]
def delabRwBy : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 6)
  let .lit (.strVal n) := e.getArg! 2 | failure
  return chainNode (← ppCoreLine (e.getArg! 4))
    #[(← `(chain_arrow| ~[$(mkIdent (.mkSimple n)):ident]~>), ← ppCoreLine (e.getArg! 5))]

/-- `φ ~[sequentialToParallel]~> ψ`, a merge of the scoped line's spine
(`Calculus/Merge.lean`). -/
@[delab app.Solidity.Fml.MergeBy]
def delabMergeBy : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 6)
  return chainNode (← ppCoreLine (e.getArg! 4))
    #[(← `(chain_arrow| ~[$(mkIdent `sequentialToParallel):ident]~>), ← ppCoreLine (e.getArg! 5))]

@[delab app.Solidity.Fml.Via]
def delabVia : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  let arrows ← linkLines (e.getArg! 3)
  guard !arrows.isEmpty
  return chainNode (← ppCoreLine (e.getArg! 2)) arrows

/-- `Fml.LeadsK A L`: `A ~~> L`, the line written `L` printed as it reads. -/
@[delab app.Solidity.Fml.LeadsK]
def delabLeadsK : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  let a ← ppCoreLine (e.getArg! 1)
  let b ← ppCoreLine (e.getArg! 2)
  `($a ~~> $b)

end Print

end Chain

namespace Scoped

scoped macro_rules
  | `($a:term ~~> $b:term) => `(leads% $a $b)

end Scoped

end Solidity
