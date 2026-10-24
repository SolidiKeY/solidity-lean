import Solidity.Calculus.ChainKit
import Solidity.Calculus.Notation
import Solidity.Calculus.Completeness
import Solidity.Calculus.Delab
import Solidity.Calculus.ExpandLaws

/-!
# Chains: the strategy

The strategy as compiled code, a line's key, postconditions and the
modality, printing a line, running the strategy.

A piece of `Calculus/Chains.lean`, whose docstring describes the whole.
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
    (tt := none) (eq := fun _ _ => none) (wellFormed := fun _ => none) (not := fun _ => none)
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
    (allocAll := fun x A φ => (Fml.stepFocusAt k φ).map fun (f, φ') => (f, .allocAll x A φ'))
    (grow := fun φ => (Fml.stepFocusAt k φ).map fun (f, φ') => (f, .grow φ'))
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
  | _, .zint t => s!"{reprStr x} := {Tm.keyStr ns t}"

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
  | .tryCall c rets ok err code pnc other _ _ _ =>
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
          | none =>
            match Stmt.storageCallStr? ns s P with
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
  | .anon _ φ | .allocAll _ _ φ | .grow φ => φ.slotMark?
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
    | .wellFormed t => .wt (t.keyStr ns)
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
    | .allocAll x _ φ => .anon [x] (φ.lineKey (x :: ns))
    | .grow φ => .anon [] (φ.lineKey ns)

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

/-- A scoped line as the compiled code reads it: its contract, its
context, the contract's name, its postconditions in slots (`punch`), the
line with them punched, and its modality, if it is a variable. -/
structure Prepared where
  C : Expr
  Γ : Expr
  name : Lean.Name
  sp : Splice
  fml : Expr
  modality : Option Expr

/-- `φ` prepared (`Prepared`). -/
def prepare (φ : Expr) : MetaM Prepared := do
  let (C, Γ) ← lineType φ
  let some name := (← whnfR C).constName?
    | throwError "sol_chain: the contract is not a named constant: {C}"
  let sp ← collectPosts φ {}
  let fml := punch C sp φ
  let m? ← modalityOf? fml
  return { C, Γ, name, sp := { sp with modality := m? }, fml, modality := m? }

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
  let { C, Γ, name := nm, sp, fml := φ', modality := m? } ← prepare φ
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

/-- The premises a line begins with (`A → ψ`), as the path to `ψ`, and `ψ`. -/
partial def premisePath (e : Expr) (p : List PathStep) : List PathStep × Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``Fml.imp 4 then premisePath e.appArg! (p ++ [.impR]) else (p, e)

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
merges under a branch (`FmlRw.mergeIn`), the spine's own being `mergeCands`'; `applyOnRigid` through the
scope ends under an update (`FmlRw.applyOnRigidPops`).  Past the program a line
`A → ψ` is read through its premises (`premisePath`): each rewrite is computed
on `ψ` and applied there (`FmlRw.inPath`), and `concrete`, a law in the
equations and the merges under a branch also on the whole line, where they
reach `A`.  Their postconditions in slots and a
modality `m` computed as the diamond and as the box; and why a law found no
instance. -/
def scopedRwCandsMany (φ : Expr) (as : Array RwArrow)
    (branches := true) (past := false) (keep : Expr → Bool := fun _ => true) :
    TermElabM (Splice × Array (List RwCand × Option MessageData)) := do
  let φ ← instantiateMVars φ
  let { C, Γ, name := nm, sp, fml := φ', modality := m? } ← prepare φ
  let φb := match m? with
    | some m => φ'.replaceFVar m (mkConst ``Modality.box)
    | none => φ'
  -- past the program, the premises the line begins with (`A → ψ`, an
  -- obligation's `wt(storage)`) read through: the rewrites are
  -- computed on `ψ` and applied there (`FmlRw.inPath`)
  let (pre, φb₀) := if past then premisePath φb [] else ([], φb)
  let lift (r : Expr) : Expr :=
    if pre.isEmpty then r else mkApp3 (mkConst ``FmlRw.inPath) C (toExpr pre) r
  let φl := φb
  let φb := φb₀
  -- the skeleton of the whole line, where it begins with premises: the
  -- candidates there (`top`) are not lifted
  let skelL? : Option Skel ← if pre.isEmpty then pure none else
    pure (← unsafe evalQuoted (List Skel) (mkApp (mkConst ``List [0]) (mkConst ``Skel))
      (mkAppN (mkConst ``Fml.spineSkels) #[C, Γ, φl]))[0]?
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
    let mut top : Array Expr := #[]
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
          -- through the scope ends under the update (`FmlRw.applyOnRigidPops`)
          if s matches .upd _ then
            rs := rs.push (mkApp2 (mkConst ``FmlRw.applyOnRigidPops) C (toExpr i))
      else if let some ek := ExpandKind.ofLink? n then
        -- past the program: a whole value's write as its words, Lean only
        -- (`FmlRw.expandPast`, `Calculus/ExpandLaws.lean`)
        if past then
          for i in List.range k do
            rs := rs.push (mkApp3 (mkConst ``FmlRw.expandPast) C (mkConst ek.constName) (toExpr i))
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
        -- the premises too: `A → true ⇝ true`, on the whole line
        if let some s := skelL? then
          if s.hasLit then top := top.push (mkApp3 (mkConst ``FmlRw.concrete) C (toExpr 0) (toExpr s))
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
        -- the merges under a branch, on the whole line; past the program not
        -- those on the spine under the premises, which the lifted merges take
        let onSpine (p : List PathStep) : Bool := past && !pre.isEmpty &&
          p.take pre.length == pre && (p.drop pre.length).all (· matches .upd | .binder)
        let below := if !branches then [] else
          (updPaths φl 16).filter fun p => p.any (· matches .andL | .andR | .impR) && !onSpine p
        for p in below do
          for j in (List.range 7).reverse do
            top := top.push (mkApp3 (mkConst ``FmlRw.mergeIn) C (toExpr p) (toExpr (j + 1)))
    | .litLaw c =>
      -- a literal law at each closed term of the line read at the empty scope
      let ts ← match tsMemo with
        | some ts => pure ts
        | none => Tm.closedNilVals φl
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
        -- in the premises too, on the whole line
        if let some s := skelL? then
          if s.hasLit then top := top.push (← mkAppM ``FmlRw.litEq #[pf, toExpr 0, toExpr s])
    | .law c₀ =>
      -- the law matched against the line's closed terms read at the empty scope;
      -- a law with a twin in a storage of members (`findOnSave` and
      -- `findOnSaveIn`, …) is either
      let ts ← match tsMemo with
        | some ts => pure ts
        | none => Tm.closedNilVals φl
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
          if let some s := skelL? then
            if s.hasLit then top := top.push (← mkAppM ``FmlRw.lawEq #[pf, toExpr 0, toExpr s])
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
      -- (and its twin in a storage of members, `findOnCopyIn`)
      for c' in Chain.lawTwins (← getEnv) c do
        let (es, f) ← lawUpdCands C c' true φb scopes keep
        rs := rs ++ es
        if failed.isNone || !es.isEmpty then failed := f
    -- the candidates on `ψ` lifted under the premises, the whole line's as they are
    rs := rs.map lift ++ top
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
    let bs ← eval φl
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
  let { C, Γ, name := n, sp, fml := φ', modality := m? } ← prepare φ
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

end Chain

end Solidity
