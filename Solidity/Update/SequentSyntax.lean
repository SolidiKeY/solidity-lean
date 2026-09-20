import Solidity.Update.Step

/-!
# `seq!` — a derivation line, written as the calculus writes it

`solbox!{ … }` writes the *program* half of a derivation line and `sol!{ <[ … ]> ‹φ› }`
the judgment.  Neither can write the half the calculus puts in front:

```
Γ ⟹ {rv := 10 ‖ sp := alice·account} ⟨[ sp.balance = rv; ]⟩ φ
```

`seq!` is that line.  It is the same grammar throughout — the statements are
`sol_stmt`, the operands of an update are `sol_expr`, the postcondition is a
`sol_post` — so a derivation stays readable as Solidity and the update stays
readable as KeY.

## The shape

```
seq!{ Γ => {U₁} {U₂} <[ stmts ]>(φ) }      -- a program goal
seq!{ Γ => {U} (φ) }                       -- the paper's last line
seq!{ Γ ⟹ {U} ⊤ }                          -- an obligation goal
```

* `Γ` is a comma-separated list of side formulas, possibly empty; the
  turnstile is always written, as the calculus writes it.  `=>` and `⟹` are
  the same line: the paper draws no turnstile on an unbranched line at all,
  and writing one on every line is what makes a chain uniform.
* Each `{…}` is one *parallel* update, `‖`-separated; several in a row are the
  *sequential* stack `{U₁}{U₂}`, and the merge line of a derivation is what
  collapses them.
* The goal is a modality (`<[ ]>`, `[ ]`, `< >`) with a postcondition, the
  paper's bare `(φ)` once no program is left, or a formula.

## Four token notes

`‖` (U+2016) separates the elements of a parallel update, **not** `||`:
`sol_expr` already has `" || "` as Boolean disjunction (`AST.lean`), so
`x := a || y := b` would parse the `||` as part of `a`.  `⟹` is the token
`sol_rule` already declares for a goal line (`Calculus/RuleSyntax.lean`), reused here.
And `storage`/`memory`/`havoc`/`CInv` are written `&"..."`, non-reserved
keywords: as plain atoms they would become global tokens and
`Account storage sp = alice.account;` would stop lexing inside `sol_stmt`,
which is the hazard `Calculus/RuleSyntax.lean`'s header records for `sol_rule`.
And `(φ)` is read as a Lean term only when it is a **bare, atomic**
identifier.  That the parenthesised identifier wins at all is parser priority,
because `"(" sol_expr ")"` is itself a `sol_expr` and two alternatives that
stop at the same position with the same priority build a `choice` node no
quotation pattern can read.  That `(alice.age)` is still a program is decided
*after* parsing (`expandIdentPost`), because the lexer reads a dotted name as
one identifier token and the grammar cannot see the difference.
`(result == 10)` never reaches that production at all.

## Why not in `Calculus/Rules.lean`

The vocabulary an update is written in is `Rules.UpdElem` and this module only
gives it surface syntax.  `Calculus/Rules.lean` is the `SolKey` reader's dependency
surface and has to stay cheap to elaborate, so the notation lives here — the
same split as `sol_rule`, whose grammar is `Calculus/RuleSyntax.lean` and whose
vocabulary is `Calculus/Rules.lean`.
-/

namespace Solidity
namespace SequentSyntax

open Lean SoliditySyntax

/-- A name the *expanded* code refers to.  As in `Calculus/RuleSyntax.lean`: these
constants are `Calculus/Rules.lean`'s, so writing them as plain identifiers inside a
quotation would tag them with this module's macro scope and they would not
resolve at the use site. -/
private def gen (x : Lean.Name) : Ident := mkIdent x

/-! ## Views on a `sol_expr`

The KeY-side vocabulary of an update -- `save(p, t)`, `path(sp)`,
`transfer(a, v)` -- is written as an **application** and read off its head,
which is what `sol_rule` does for a schema-variable rule
(`Calculus/RuleSyntax.lean`, `callHead?`).  The reason is the same and it is not
cosmetic: a production spelled with a bare atom (`"storage" " := " "save(" …`)
makes those words *global tokens*, and `Account storage sp = alice.account;`
then stops lexing inside `sol_stmt`.  `sol_expr` already has an `ident(args)`
production, so reading the head costs no token at all. -/

/-- A `sol_expr` that is a bare identifier. -/
def identName? : TSyntax `sol_expr → Option String
  | `(sol_expr| $x:ident) => some x.getId.toString
  | _ => none

/-- A `sol_expr` that is an application, as its head and arguments. -/
def callHead? : TSyntax `sol_expr → Option (String × Array (TSyntax `sol_expr))
  | `(sol_expr| $f:ident($args,*)) => some (f.getId.toString, args.getElems)
  | _ => none

/-! ## Side formulas -/

declare_syntax_cat sol_formula
/-- The trivially true antecedent, and the box `revert` branch's goal. -/
syntax "⊤" : sol_formula
/-- The diamond `revert` branch's goal. -/
syntax "⊥" : sol_formula
syntax "¬" sol_formula : sol_formula
/-- A guard of the calculus, read off its head: `inBounds(e)` (the index
access's bounds test), `nonEmpty(arr)` (the `pop` guard), `nonZero(e)`,
`rhsNonZero(e)`, `funded(se)` (the diamond `transfer` obligation), `CInv` (the
payment rules' contract invariant) -- or any Boolean expression of the program,
which is KeY's `se = TRUE`. -/
syntax sol_expr : sol_formula

partial def expandFormula : TSyntax `sol_formula → MacroM (TSyntax `term)
  | `(sol_formula| ⊤) => `($(gen ``SideFormula.const) true)
  | `(sol_formula| ⊥) => `($(gen ``SideFormula.const) false)
  | `(sol_formula| ¬ $f:sol_formula) => do
      `($(gen ``SideFormula.neg) $(← expandFormula f))
  | `(sol_formula| $e:sol_expr) => do
      match callHead? e with
      | some ("inBounds", #[p]) => `($(gen ``SideFormula.inBounds) $(← expandSolExpr p))
      | some ("nonEmpty", #[p]) => `($(gen ``SideFormula.nonEmpty) $(← expandSolExpr p))
      | some ("nonZero", #[p]) => `($(gen ``SideFormula.nonZero) $(← expandSolExpr p))
      | some ("rhsNonZero", #[p]) => `($(gen ``SideFormula.rhsNonZero) $(← expandSolExpr p))
      | some ("funded", #[p]) => `($(gen ``SideFormula.funded) $(← expandSolExpr p))
      | _ =>
          if identName? e == some "CInv" then `($(gen ``SideFormula.cinv))
          else `($(gen ``SideFormula.holds) $(← expandSolExpr e))
  | stx => Macro.throwErrorAt stx "unexpected side formula"

/-! ## Elementary updates

One production per `UpdElem`, named as the taclet names it: `storage := save(p, t)`,
`sp := path(alice.account)`, `memory := write(p, t)`, `transfer(a, se)`,
`bump(t++)`.  The component and the KeY function are read off the two sides,
so the grammar itself is just "an assignment, or a bare application". -/

declare_syntax_cat sol_upd
/-- `x := t`: the right-hand side names the KeY term -- `save(p, t)`,
`copy(p, sp)`, `copyMem(p, mv)`, `push(arr)`, `push(arr, v)`, `pop(arr)`,
`clear(p)` under `storage`; a `MemTerm` -- `write(m, p, v)`, `alloc(T)`,
`alloc(T, sp)`, `memory` -- under `memory`;
`path(sp)`, `ref(m)`, `freshId(m)`, `slot(arr.push())`, `default(T)`, `length(arr)`,
`net(a)`, `current(p)` for a name; anything else is the value itself. -/
syntax sol_expr " := " sol_expr : sol_upd
/-- `t ⊕= se` -- the write-back a compound assignment performs, `t op se`
computed at the *target's* type.  Spelled as the program's own compound
assignment because that is what it is: `Sym.combined` carries the target
twice, so the calculus's `{storage := save(p, alice·age + 1)}` and this line
are the same element.  The tokens are `sol_stmt`'s already. -/
syntax sol_expr " += " sol_expr : sol_upd
syntax sol_expr " -= " sol_expr : sol_upd
syntax sol_expr " *= " sol_expr : sol_upd
syntax sol_expr " /= " sol_expr : sol_upd
syntax sol_expr " %= " sol_expr : sol_upd
/-- An update with no left-hand side: `transfer(a, se)` and `bump(t++)` write
two things at once, `alloc(T, m)` / `alloc(T, m, sp)` is a memory declaration,
`clear(m)` a memory delete, and `havoc` the callback re-binding. -/
syntax sol_expr : sol_upd

partial def expandUpd (stx : TSyntax `sol_upd) : MacroM (TSyntax `term) := do
  match stx with
  | `(sol_upd| $t:sol_expr += $v:sol_expr) => compound ``BinOp.add t v
  | `(sol_upd| $t:sol_expr -= $v:sol_expr) => compound ``BinOp.sub t v
  | `(sol_upd| $t:sol_expr *= $v:sol_expr) => compound ``BinOp.mul t v
  | `(sol_upd| $t:sol_expr /= $v:sol_expr) => compound ``BinOp.div t v
  | `(sol_upd| $t:sol_expr %= $v:sol_expr) => compound ``BinOp.mod t v
  | `(sol_upd| $lhs:sol_expr := $rhs:sol_expr) =>
      let comp := identName? lhs
      match comp, callHead? rhs with
      | some "storage", some ("save", #[p, t]) =>
          `($(gen ``UpdElem.storage) (.save $(← expandSolExpr p) (.read $(← expandSolExpr t))))
      | some "storage", some ("copy", #[p, q]) =>
          `($(gen ``UpdElem.storage) (.copy $(← expandSolExpr p) $(← expandSolExpr q)))
      | some "storage", some ("copyMem", #[p, q]) =>
          `($(gen ``UpdElem.storage) (.copyFromMem $(← expandSolExpr p) $(← expandSolExpr q)))
      | some "storage", some ("push", #[a]) =>
          `($(gen ``UpdElem.storage) (.push $(← expandSolExpr a) none))
      | some "storage", some ("push", #[a, v]) =>
          `($(gen ``UpdElem.storage) (.push $(← expandSolExpr a) (some $(← expandSolExpr v))))
      | some "storage", some ("pushSlot", #[p]) =>
          `($(gen ``UpdElem.storage) (.pushPlace $(← expandSolExpr p)))
      | some "storage", some ("pop", #[a]) =>
          `($(gen ``UpdElem.storage) (.pop $(← expandSolExpr a)))
      | some "storage", some ("clear", #[p]) =>
          `($(gen ``UpdElem.storage) (.clear $(← expandSolExpr p)))
      | some "memory", _ => `($(gen ``UpdElem.heap) $(← expandMemTerm rhs))
      | some c, some (f, _) =>
          if c == "storage" || c == "memory" then
            Macro.throwErrorAt rhs s!"`{c} := {f}(…)` is not an update of the calculus"
          else expandNamed lhs rhs
      | _, _ => expandNamed lhs rhs
  | `(sol_upd| $e:sol_expr) =>
      match callHead? e with
      | some ("transfer", #[a, v]) =>
          `($(gen ``UpdElem.transfer) $(← expandSolExpr a) $(← expandSolExpr v))
      | some ("bump", #[t]) => `($(gen ``UpdElem.bumpOf) $(← expandSolExpr t))
      | some ("clear", #[m]) => `($(gen ``UpdElem.memDelete) $(← expandSolExpr m))

      | _ =>
          if identName? e == some "havoc" then `($(gen ``UpdElem.havoc))
          else Macro.throwErrorAt e "unexpected elementary update"
  | stx => Macro.throwErrorAt stx "unexpected elementary update"
where
  /-- `t ⊕= se`: one write-back of `Sym.combined`, at whichever data location
  the target lives in.  The same term `Rules.compoundGoals` builds. -/
  compound (op : Lean.Name) (t v : TSyntax `sol_expr) : MacroM (TSyntax `term) := do
    let tTerm ← expandSolExpr t
    `($(gen ``Rules.writeBack) $tTerm
        (.combined $(gen op) $tTerm $(← expandSolExpr v)))
  /-- A memory term: `memoryRules.key`'s `write`/`addM`/`copySt` over the
  `memory` program variable, nesting as KeY's do. -/
  expandMemTerm (e : TSyntax `sol_expr) : MacroM (TSyntax `term) := do
    match callHead? e with
    | some ("alloc", #[t]) =>
        let some ty := identName? t | Macro.throwErrorAt t "`alloc` takes a type"
        `($(gen ``Rules.allocTerm)
            ($(gen ``SoliditySyntax.declTy) $(Syntax.mkStrLit ty)) none)
    | some ("alloc", #[t, p]) =>
        let some ty := identName? t | Macro.throwErrorAt t "`alloc` takes a type"
        `($(gen ``Rules.allocTerm)
            ($(gen ``SoliditySyntax.declTy) $(Syntax.mkStrLit ty))
            (some $(← expandSolExpr p)))
    | some ("write", #[m, p, v]) =>
        `($(gen ``MemTerm.write) $(← expandMemTerm m) $(← expandSolExpr p)
            $(← expandMemVal v))
    | _ =>
        if identName? e == some "memory" then `($(gen ``MemTerm.cur))
        else Macro.throwErrorAt e "not a memory term"

  /-- A `write`'s value slot. -/
  expandMemVal (e : TSyntax `sol_expr) : MacroM (TSyntax `term) := do
    match callHead? e with
    | some ("image", #[src]) => `($(gen ``MemVal.image) $(← expandSolExpr src))
    | _ =>
        if identName? e == some "fresh" then `($(gen ``MemVal.fresh))
        else `($(gen ``MemVal.sym) (.read $(← expandSolExpr e)))

  /-- `x := …` for a name: a binding, or -- when the right-hand side is a
  plain term -- a write-back at whichever data location `x` lives in. -/
  expandNamed (lhs rhs : TSyntax `sol_expr) : MacroM (TSyntax `term) := do
    match callHead? rhs with
    | some ("path", #[p]) =>
        `($(gen ``UpdElem.bind) ($(gen ``Rules.varName) $(← expandSolExpr lhs))
            (.path $(← expandSolExpr p)))
    | some ("ref", #[p]) =>
        `($(gen ``UpdElem.bind) ($(gen ``Rules.varName) $(← expandSolExpr lhs))
            (.mref $(← expandSolExpr p)))
    | some ("freshId", #[m]) =>
        `($(gen ``UpdElem.bind) ($(gen ``Rules.varName) $(← expandSolExpr lhs))
            (.freshId $(← expandMemTerm m)))
    | some ("slot", #[p]) =>
        `($(gen ``UpdElem.bind) ($(gen ``Rules.varName) $(← expandSolExpr lhs))
            (.pushSlot $(← expandSolExpr p)))
    | some ("default", #[t]) =>
        let some ty := identName? t | Macro.throwErrorAt t "`default` takes a type"
        `($(gen ``UpdElem.bind) ($(gen ``Rules.varName) $(← expandSolExpr lhs))
            (.val (.deflt ($(gen ``SoliditySyntax.declTy) $(Syntax.mkStrLit ty)))))
    | some ("length", #[a]) =>
        `($(gen ``Rules.writeBack) $(← expandSolExpr lhs) (.length $(← expandSolExpr a)))
    | some ("net", #[a]) =>
        `($(gen ``Rules.writeBack) $(← expandSolExpr lhs) (.netOf $(← expandSolExpr a)))
    | some ("current", #[p]) =>
        `($(gen ``Rules.writeBack) $(← expandSolExpr lhs) (.current $(← expandSolExpr p)))
    | _ => `($(gen ``Rules.writeBack) $(← expandSolExpr lhs) (.read $(← expandSolExpr rhs)))

/-! ## The line -/

/-! ### The postcondition position

A goal written the way the paper draws it ends in `(φ)`, and that text is
ambiguous: `"(" sol_expr ")"` is itself a `sol_expr` (`AST.lean`), so `(φ)`
would silently become a Solidity variable *named* `φ`.  The rule here is that
a **bare identifier** in parentheses is a Lean term -- the calculus's opaque
postcondition -- and anything else is the ordinary expression grammar.

That is a parser *priority*, not a declaration order: two alternatives that
stop at the same position with the same priority produce a `choice` node, and
a quotation pattern cannot read one.  `(alice.age)` is not ambiguous at all --
the identifier alternative fails at the `.` -- and `‹t›` is unchanged. -/
declare_syntax_cat sol_seq_post
/-- `(φ)` -- the opaque postcondition, any Lean term of that name. -/
syntax (priority := high) "(" ident ")" : sol_seq_post
/-- A concrete postcondition, or the explicit `‹t›` escape. -/
syntax sol_post : sol_seq_post

/-- `(x)` for an identifier: the calculus's opaque postcondition when the name
is *atomic*, the program's own expression when it is dotted.  The split is
here rather than in the grammar because the lexer reads `alice.age` as **one**
identifier token, so the parser cannot tell the two apart. -/
def expandIdentPost (x : Ident) : MacroM (TSyntax `term) :=
  if x.getId.isAtomic then pure x
  else expandSolPathExpr (x.getId.components.map Lean.Name.toString)

def expandSeqPost : TSyntax `sol_seq_post → MacroM (TSyntax `term)
  | `(sol_seq_post| ($x:ident)) => expandIdentPost x
  | `(sol_seq_post| $p:sol_post) => expandSolPost p
  | stx => Macro.throwErrorAt stx "unexpected postcondition"

declare_syntax_cat sol_seq_goal
/-- The combined modality, the default of every worked example. -/
syntax "<[" sepBy(sol_stmt, ";", ";") "]>" sol_seq_post : sol_seq_goal
syntax "[" sepBy(sol_stmt, ";", ";") "]" sol_seq_post : sol_seq_goal
syntax "<" sepBy(sol_stmt, ";", ";") ">" sol_seq_post : sol_seq_goal
/-- The paper's last line: `{U} φ`, with the modality no longer drawn because
no program is left.  The modality is still *there* -- it is the one the chain
started in -- so the caller supplies it, and a chain's last line agrees with
its first by construction.

A parenthesised goal is a **postcondition over the empty program**, never an
obligation: `⊤`, `⊥`, `funded(se)` and the rest are written without
parentheses, which is how the calculus writes them anyway.

One thing this form cannot say: a *comparison* postcondition.  `(x == 10)` is
one `sol_expr` whose parentheses belong to the comparison, so it is not
`"(" sol_expr ")"` and falls through to the formula reading.  Write the
modality out — `<[ ]>(x == 10)` — which is what a concrete postcondition wants
anyway; the bare line is for the calculus's opaque `φ`. -/
syntax (priority := high) "(" sol_expr ")" : sol_seq_goal
/-- No program left: KeY's `\replacewith(φ)`. -/
syntax sol_formula : sol_seq_goal

/-- The modality a goal writes, if it writes one.  Read off the syntax, not
the elaborated term, for the reason `Examples/Common.lean` gives for the layer
sniff: a line typically mentions a section `variable (φ : WrappedExpr)`. -/
def goalMode? : TSyntax `sol_seq_goal → Option Ident
  | `(sol_seq_goal| <[ $_;* ]> $_:sol_seq_post) => some (gen ``SolidityModality.both)
  | `(sol_seq_goal| [ $_;* ] $_:sol_seq_post) => some (gen ``SolidityModality.box)
  | `(sol_seq_goal| < $_;* > $_:sol_seq_post) => some (gen ``SolidityModality.diamond)
  | _ => none

/-- `mode` is used only by the bare `(φ)` form, whose modality is not written. -/
def expandSeqGoal (mode : TSyntax `term) : TSyntax `sol_seq_goal → MacroM (TSyntax `term)
  | `(sol_seq_goal| <[ $stmts;* ]> $post:sol_seq_post) => do
      `($(gen ``SeqGoal.prog) ($(gen ``SolidityBlock.mk) .both $(← expandSolBlock stmts.getElems))
          $(← expandSeqPost post))
  | `(sol_seq_goal| [ $stmts;* ] $post:sol_seq_post) => do
      `($(gen ``SeqGoal.prog) ($(gen ``SolidityBlock.mk) .box $(← expandSolBlock stmts.getElems))
          $(← expandSeqPost post))
  | `(sol_seq_goal| < $stmts;* > $post:sol_seq_post) => do
      `($(gen ``SeqGoal.prog) ($(gen ``SolidityBlock.mk) .diamond $(← expandSolBlock stmts.getElems))
          $(← expandSeqPost post))
  | `(sol_seq_goal| ($e:sol_expr)) => do
      let post ← match e with
        | `(sol_expr| $x:ident) => expandIdentPost x
        | _ => expandSolExpr e
      `($(gen ``SeqGoal.prog) ($(gen ``SolidityBlock.mk) $mode (([] : $(gen ``Block))))
          $post)
  | `(sol_seq_goal| $f:sol_formula) => do
      `($(gen ``SeqGoal.obl) $(← expandFormula f))
  | stx => Macro.throwErrorAt stx "unexpected sequent goal"

/-- One parallel update `{a ‖ b ‖ c}`; several in a row are the sequential
stack `{U₁}{U₂}`.  Its own category so that the repetition has a plain
antiquotation in the `seq!` expander. -/
declare_syntax_cat sol_par_upd
syntax "{" sepBy1(sol_upd, " ‖ ") "}" : sol_par_upd

/-- One formula of the antecedent, with the update stack it is read under.

A guard is read **outside** the update the same goal installs -- KeY writes
`guard → {u}⟨rest⟩φ` -- so a guard a rule adds part-way through a derivation
is read under whatever had been accumulated *before* that rule fired, and a
line that states it has to say so.  Written with no `{…}` prefix the formula
is read in the state the derivation starts from, which is what every guard
added at the first step means. -/
declare_syntax_cat sol_ante
syntax (sol_par_upd)* sol_formula : sol_ante

/-- Read at the raw-`Syntax` level: `‖` is not a separator a quotation
pattern can splice, so the elements come off the `sepBy` node directly --
the same way `Calculus/RuleSyntax.lean` reads its own `||`-separated updates. -/
def expandParUpd (stx : TSyntax `sol_par_upd) : MacroM (TSyntax `term) := do
  let elems ← stx.raw[1].getSepArgs.mapM fun u => expandUpd ⟨u⟩
  `(([$elems,*] : $(gen ``UpdTerm)))

def expandAnte : TSyntax `sol_ante → MacroM (TSyntax `term)
  | `(sol_ante| $upds:sol_par_upd* $f:sol_formula) => do
      let updTerms ← upds.mapM expandParUpd
      `((([$updTerms,*] : List $(gen ``UpdTerm)), $(← expandFormula f)))
  | stx => Macro.throwErrorAt stx "unexpected antecedent"

/-! ### The line

`Γ ⟹ {U₁}…{Uₙ} goal`, with `=>` as the ASCII turnstile.  The paper draws no
turnstile on an unbranched line at all; writing one on every line is what
makes a chain uniform, and `=>` is what a reader can type.  Two productions
rather than one with an alternation, so that each has a plain quotation
pattern; `=>` is already a token (`fun x => …`), so no new token enters the
global table. -/
declare_syntax_cat sol_line
syntax sepBy(sol_ante, ", ") " ⟹ " (sol_par_upd)* sol_seq_goal : sol_line
/-- The ASCII turnstile, the spelling a derivation is written in. -/
syntax sepBy(sol_ante, ", ") " => " (sol_par_upd)* sol_seq_goal : sol_line

/-- The modality a line writes, if any: the caller of a chain reads it off the
*first* line and hands it to every bare `(φ)` line after it. -/
def lineMode? : TSyntax `sol_line → Option Ident
  | `(sol_line| $_ante:sol_ante,* ⟹ $_upds:sol_par_upd* $goal:sol_seq_goal) => goalMode? goal
  | `(sol_line| $_ante:sol_ante,* => $_upds:sol_par_upd* $goal:sol_seq_goal) => goalMode? goal
  | _ => none

def expandLine (mode : TSyntax `term) : TSyntax `sol_line → MacroM (TSyntax `term)
  | `(sol_line| $ante:sol_ante,* ⟹ $upds:sol_par_upd* $goal:sol_seq_goal)
  | `(sol_line| $ante:sol_ante,* => $upds:sol_par_upd* $goal:sol_seq_goal) => do
      let anteTerms ← ante.getElems.mapM expandAnte
      let updTerms ← upds.mapM expandParUpd
      `($(gen ``Sequent.mk) [$anteTerms,*] [$updTerms,*] $(← expandSeqGoal mode goal))
  | stx => Macro.throwErrorAt stx "unexpected derivation line"

/-- One derivation line, as the calculus draws it.  A standalone line has no
chain to inherit a modality from, so a bare `(φ)` goal is read as the combined
one -- the default of every worked example. -/
syntax "seq!" "{" sol_line "}" : term

macro_rules
  | `(seq!{ $l:sol_line }) => do
      expandLine (← `($(gen ``SolidityModality.both))) l
/-! ## Smoke tests

Grammar only -- every production of `sol_upd`, `sol_formula`, `sol_ante` and
`sol_seq_goal` once, so that a parser problem and a proof problem are
distinguishable (the same reason `AST.lean` keeps its `#check`
section). -/

section
open StandardExample
variable (φ : WrappedExpr)

-- the three modalities, the opaque postcondition, and a concrete one
#check seq!{ ⟹ <[ alice.account.balance = 10 ]> ‹φ› }
#check seq!{ ⟹ [ alice.age = ageVal ] ‹φ› }
#check seq!{ ⟹ < result = alice.age > (result == 0) }
#check seq!{ ⟹ <[ ]> ‹φ› }

-- obligation goals
#check seq!{ ⟹ ⊤ }
#check seq!{ ⟹ ⊥ }
#check seq!{ ⟹ funded(amount) }

-- antecedents: bare, several, negated, and under an update stack
#check seq!{ flag ⟹ <[ ]> ‹φ› }
#check seq!{ inBounds(values[i]), ¬nonEmpty(values) ⟹ <[ ]> ‹φ› }
#check seq!{ { pv@uint := 3 } funded(pv@uint) ⟹ { pv@uint := 3 } <[ ]> ‹φ› }
#check seq!{ nonZero(i), rhsNonZero((i + 1)), CInv ⟹ <[ ]> ‹φ› }

-- the storage component
#check seq!{ ⟹ { storage := save(alice.age, ageVal) } <[ ]> ‹φ› }
#check seq!{ ⟹ { storage := copy(alice.account, bob.account) } <[ ]> ‹φ› }
#check seq!{ ⟹ { storage := copyMem(alice.account, mv@Account) } <[ ]> ‹φ› }
#check seq!{ ⟹ { storage := push(values) } <[ ]> ‹φ› }
#check seq!{ ⟹ { storage := push(values, 42) } <[ ]> ‹φ› }
#check seq!{ ⟹ { storage := pop(values) } <[ ]> ‹φ› }
#check seq!{ ⟹ { storage := clear(alice.account) } <[ ]> ‹φ› }

-- the memory component
#check seq!{ ⟹ { memory := write(memory, mv@Account.balance, 7) } <[ ]> ‹φ› }
#check seq!{ ⟹ { memory := write(memory, mv@Person.account, image(alice.account)) }
             <[ ]> ‹φ› }
#check seq!{ ⟹ { memory := write(alloc(Person), mv@Person.account, fresh) } <[ ]> ‹φ› }

-- names
#check seq!{ ⟹ { sp@Account := path(alice.account) } <[ ]> ‹φ› }
#check seq!{ ⟹ { mv@Person := ref(carol) } <[ ]> ‹φ› }
#check seq!{ ⟹ { sp@UintArray := slot(values.push()) } <[ ]> ‹φ› }
#check seq!{ ⟹ { rv@uint := default(uint) } <[ ]> ‹φ› }
#check seq!{ ⟹ { v := length(values) } <[ ]> ‹φ› }
#check seq!{ ⟹ { v := net(to) } <[ ]> ‹φ› }
#check seq!{ ⟹ { v := current(alice.age) } <[ ]> ‹φ› }
#check seq!{ ⟹ { result := alice.age } <[ ]> ‹φ› }

-- the compound write-back
#check seq!{ ⟹ { alice.age += 1 } <[ ]> ‹φ› }
#check seq!{ ⟹ { values[i] *= amount } <[ ]> ‹φ› }

-- the pairs, and the parallel form
#check seq!{ ⟹ { transfer(to, amount) } <[ ]> ‹φ› }
#check seq!{ ⟹ { bump(age++) } <[ ]> ‹φ› }
#check seq!{ ⟹ { mv@Person := freshId(alloc(Person)) ‖ memory := alloc(Person) }
             <[ ]> ‹φ› }
#check seq!{ ⟹ { mv@Person := freshId(alloc(Person, alice)) ‖ memory := alloc(Person, alice) }
             <[ ]> ‹φ› }
#check seq!{ ⟹ { clear(mv@Person) } <[ ]> ‹φ› }
#check seq!{ ⟹ { havoc } <[ ]> ‹φ› }
#check seq!{ ⟹ { rv@uint := 10 ‖ sp@Account := path(alice.account)
                 ‖ storage := save(alice.account.balance, 10) } <[ ]> ‹φ› }

-- a sequential stack, and a branching line
#check seq!{ ⟹ { rv@uint := 10 } { sp@Account := path(alice.account) } <[ ]> ‹φ› }
#check (seq!{ ⟹ <[ ]> ‹φ› } : Frontier)
#check ([ seq!{ inBounds(values[i]) ⟹ { v := values[i] } [ ] ‹φ› },
          seq!{ ¬inBounds(values[i]) ⟹ ⊤ } ] : Frontier)

-- the ASCII turnstile, and `(φ)` in each of the three modalities
#check seq!{ => <[ alice.account.balance = 10 ]>(φ) }
#check seq!{ => [ v = values[i] ](φ) }
#check seq!{ => < v = values[i] >(φ) }
#check seq!{ inBounds(values[i]) => { v := values[i] } [ ](φ) }
#check seq!{ => ⊤ }

-- the paper's last line: no modality drawn, the chain's own supplied.  A
-- concrete postcondition reads the same way; an obligation is unparenthesised.
#check seq!{ => { rv@uint := 10 ‖ storage := save(alice.account.balance, 10) } (φ) }
#check seq!{ => { storage := save(alice.age, 10) } (alice.age) }
#check seq!{ => { storage := save(alice.age, 10) } <[ ]>(alice.age == 10) }
#check seq!{ => { rv@uint := 10 } funded(rv@uint) }

-- …and the same text read as a program, which is what settles the priority:
-- a bare identifier is the Lean term, anything else the expression grammar.
#check seq!{ => <[ ]>(alice.age) }
#check seq!{ => <[ ]>(result == 10) }
#check seq!{ => <[ ]> ‹φ› }
end

end SequentSyntax

export SequentSyntax (expandFormula expandUpd expandParUpd expandAnte expandSeqPost
  expandSeqGoal expandLine goalMode? lineMode?)

end Solidity
