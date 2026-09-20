import Lean

/-!
# The `rule` declaration syntax

`Rules.lean` used to spell every rule of the calculus three times: a
`RuleName` constructor, a `ruleEffect` arm and a `ruleNames` entry, with the
same section banners repeated in all three, the condition written twice
(once in `cond`, once re-matched with the proof in `goals`), a box/diamond
twin pair duplicated verbatim except for one token, and an operator-indexed
family's fourteen instances listed by hand.

This module replaces the three tables by one declaration per rule, written
the way the paper draws it and the way `solidityProgramRules.key` writes a
taclet:

```
/-- KeY `storageFieldWriteSave`. -/
sol_rule storageFieldWriteSave from storageFieldWriteSave :
  <[ sp.fld = se ]> ⇝ { storage := save(sp.fld, se) } <[ ]>
```

Read it as the paper's fraction turned on its side: the *conclusion* — the
statement the rule matches — on the left of `⇝`, the *premises* on the
right, and the sequent contexts `π`, `ω`, `φ` dropped because they are
constant. `<[ ]>` is the empty continuation `⟨[ π ω ]⟩φ`; `box`/`diamond`
mark a goal that holds in one modality only, reserved — as in the
paper, which keeps `[·]`/`⟨·⟩` for them — for the rules that really do
differ by modality.

## What the declaration says that the old arm did not

**The kind of a schema variable is carried by its name**, which is the
paper's central device (`docs/LATEX.md`: "Never reintroduce an `\is...`
side condition; name a variable whose declaration carries the kind"). So
`sp.fld = se` *is* the condition `isSimple sp ∧ isSe se` together with the
pattern `WrappedExpr.field Kind.storage _ sp _`, and `arr[i] = se` adds the
trailing `isArray arr` that separates it from the mapping rule. The table
is in `schemaVar` below; `where` adds the conjuncts no name can carry, and
`where cond := …` writes the condition out when a rule's spelling is
irregular.

**A residual is a program, not a list of constructors.** `T se = e` is the
value freeze, `T storage sp = nsp` the path capture, and a later `sp.fld`
is the alias read-back — the three statements the paper writes as
`T_e se = e; T_nsp storage sp = nsp; sp.fld = se;`.  Three spellings say
which capture is meant, because the alias name alone cannot: `T se = e`
freezes on the stack, `_ se = e` at the expression's own location, and
`T se ?= e` only *if* there is a value to freeze — a reference is aliased,
not read, and a source that already is the scratch value is left alone, so
the residual below a `?=` is written twice, once per branch.  `T ie ?= e`
is the same split for an index.

**Twins are one declaration.** `twins` generates the `Box` and `Diamond`
constructors, box first, and the entry in `twinPairs` that
`CandidateStep.twins_box_first` checks.

**A family is one declaration.** `(op : BinOp)` generates the constructor
parameter, the `op = opR ∧ …` head conjuncts, and all fourteen `ruleNames`
entries.  `(op : BinOp | g)` restricts it to the instances `g` admits, as a
conjunct right behind the operator equation.

## The two escapes

Every rule of the table is written this way, and two clauses carry the ones
the schema-variable convention cannot reach on its own.

`where cond := P` replaces the generated condition by `P`, for the handful
whose applicability is a bespoke predicate (`isSimpleStorageDeleteTarget`) or
a shape the pattern language does not have.

`⟦ b ⟧` in place of a residual gives the block as a Lean term, with the
condition proof in scope as `h`, for the handful whose residual is *computed*
from that proof rather than written out.  Both keep the conclusion
declarative: what the rule matches is still read off the statement.

## How it is assembled

A `rule` command elaborates nothing. It translates its own syntax into a
`StepEffect` term — built from the combinators `Rules.lean` already has, so
the generated term is the one the hand-written arm produced — and pushes a
`RuleDecl` into `ruleExt`. `sol_assemble_rules` then emits, in declaration
order, the `RuleName` inductive, `ruleEffect`, `ruleNames` and `twinPairs`.

Nothing here imports the rest of the package: the module generates syntax,
and the names it generates (`isSe`, `terminalGoal`, `Stmt.assign`, …)
resolve where the generated code lands, inside `Rules.lean`. That keeps the
`SolKey` reader's dependency surface unchanged.
-/

namespace Solidity.RuleSyntax

open Lean Elab Command Term

/-! ## The declaration record -/

/-- How a rule is parameterized, if it is: the binder and its type, e.g.
`(op : BinOp)`. Both idents are the user's own, so the name bridging the
rule's body and the assembled `match` alternative is the same clean
identifier in each (a re-`mkIdent`ed copy elaborates as `op✝`). -/
structure RuleBinder where
  name : Ident
  type : Ident
  deriving Inhabited

/-- One `rule` declaration, as `sol_assemble_rules` needs it. -/
structure RuleDecl where
  /-- The rule's own syntax, so a later error points at the declaration. -/
  ref : Syntax
  /-- The constructor name; for a twin pair, the stem without `Box`/`Diamond`. -/
  name : Ident
  doc : Option (TSyntax ``Lean.Parser.Command.docComment)
  binder : Option RuleBinder
  /-- The `StepEffect` term, built from `Rules.lean`'s own combinators. -/
  effect : Term
  /-- The diamond twin's effect, when `twins` is set; the `effect` field is
  then the box twin's. -/
  effectDia : Option Term := none
  /-- Generate a `Box`/`Diamond` constructor pair rather than one constructor. -/
  twins : Bool
  /-- Omit from `ruleNames`: KeY's `\choice` alternative
  (`transferWithCallback` is the only one). -/
  alternative : Bool
  deriving Inhabited

/-- The rules declared so far, in declaration order.  Non-persistent: every
`rule` and the `sol_assemble_rules` that consumes them live in one module.
State in the `Environment` rather than an `IO.Ref` so that the language
server's incremental re-elaboration restores it instead of accumulating
duplicates. -/
initialize ruleExt : EnvExtension (Array RuleDecl) ←
  registerEnvExtension (pure #[])

def pushRule (decl : RuleDecl) : CommandElabM Unit :=
  modifyEnv fun env => ruleExt.modifyState env (·.push decl)


/-! ## The grammar

One expression language, and everything else dispatched from it.

That is forced, not chosen.  Lean's category parser indexes an alternative
by its leading token, and a *non-reserved* keyword (`&"save"`) is indexed
apart from the identifier bucket, so a category that also has a bare
`rule_expr` alternative never reaches its keyword-headed ones.  Reserving
the keywords instead is worse: `save`, `push`, `assert`, `transfer` and
friends are spelled with parentheses all over the corpus and inside `sol!`
programs, and a reserved `push(` would change how they lex.

So the KeY-side vocabulary — `save(storage, p, t)`, `read(se)`,
`inBounds(p)`, `default(T)` — is written as *applications*, which is how
`solidityProgramRules.key` writes it anyway, and the meaning is read off the
head name.  A misspelled head is an error at the rule, not a parse failure
three tokens later.
-/

declare_syntax_cat rule_expr

/-- A schema variable: `se`, `sp`, `arr`, `gsp`, … Its *kind* is its name
(`schemaVar`), as in the paper. -/
syntax:max (name := exprVar) ident : rule_expr
/-- `p.fld` — a struct member; `fld` names the `Field` binder. -/
syntax:100 (name := exprField) rule_expr:100 noWs "." noWs ident : rule_expr
/-- `arr[i]` — an array element or mapping entry. -/
syntax:100 (name := exprIndex) rule_expr:100 noWs "[" rule_expr "]" : rule_expr
/-- `arr.push()` as an *expression*: KeY's push place. -/
syntax:100 (name := exprPushPlace) rule_expr:100 noWs ".push()" : rule_expr
/-- `gsp++` — the schematic increment or decrement.  The paper writes
`gsp++`; which of the four it is comes from the rule's `IncDec` parameter,
not from the spelling. -/
syntax:90 (name := exprIncDec) rule_expr:100 noWs "++" : rule_expr
/-- An application: the KeY-side vocabulary, and the statement forms that
take arguments (`require(se)`, `delete(sp.fld)`, `revert()`). -/
syntax:max (name := exprCall) ident noWs "(" rule_expr,* ")" : rule_expr
/-- `t ⊕ se` — the schematic operator, the paper's `⊕`.

In a *goal*, `⊕` and the statement forms below denote the operator the
**statement** carries, which the condition's first conjunct ties to the
family index; that operator is in scope under the name `opS`, and a `when`
guard — a raw Lean term, so it is not translated — has to spell it.  The
distinction is not cosmetic: `Rules.compoundGoals` is handed the statement's
operator, and the two are equal only under that conjunct. -/
syntax:65 (name := exprCombine) rule_expr:65 " ⊕ " rule_expr:66 : rule_expr
/-- `⊖ se` — the schematic unary operator, indexed by the rule's `UnOp`
parameter exactly as `⊕` is by its `BinOp` one. -/
syntax:75 (name := exprUnop) "⊖" rule_expr:75 : rule_expr
/-- `! se` — logical negation, the one unary operator a rule names outright
(`ifElseNegated` matches on it). -/
syntax:75 (name := exprNot) "!" rule_expr:75 : rule_expr
/-- `se && nse` / `se || nse` — the short-circuiting connectives, named
outright because the rules that match them are about the short circuit.

Both sit *below* the precedence an update's right-hand side accepts, so a
parallel update `{ a := t || b := u }` still splits on its own `||`. -/
syntax:35 (name := exprAnd) rule_expr:36 " && " rule_expr:36 : rule_expr
syntax:30 (name := exprOr) rule_expr:31 " || " rule_expr:31 : rule_expr
/-- `c ? e1 : e2`. -/
syntax:20 (name := exprTernary) rule_expr:21 " ? " rule_expr:21 " : " rule_expr:21 : rule_expr
/-- Escape to a Lean term. -/
syntax:max (name := exprEscape) "‹" term "›" : rule_expr

declare_syntax_cat rule_stmt

/-- `sp.fld = se` -/
syntax (name := stAssign) rule_expr " = " rule_expr : rule_stmt
/-- `sp.fld ⊕= se` — the paper's compound assignment; which operator it is
comes from the rule's `BinOp` parameter, as `⊕ ∈ {+,−,*}` does there. -/
syntax (name := stCompound) rule_expr " ⊕= " rule_expr : rule_stmt
/-- `T v` / `T v = e` — a stack declaration. -/
syntax (name := stStackDecl) ident ident : rule_stmt
syntax (name := stStackDeclInit) ident ident " = " rule_expr : rule_stmt
/-- `_ se = e` — the capture whose declaration kind is the *expression's*
(`Rules.captureValue`), where `T se = e` forces the stack
(`Rules.captureStackValue`).  The underscore is the point: the rule does not
name the location, the expression does. -/
syntax (name := stValueDecl) "_ " ident " = " rule_expr : rule_stmt
/-- `T se ?= e` — a *conditional* capture, and which one the alias name says.

`T se ?= e` is the freeze of a value operand (`Rules.freezeRhs`): a primitive
`e` is snapshotted into `se` and the rest of the residual reads `se`, while a
reference `e`, or an `e` that already is the scratch value, is left in place
and `se` *is* `e` — binding a reference is aliasing, not a read, so there is
nothing to freeze.

`T ie ?= e` is the index capture (`Rules.indexWriteResolveBlock`): a complex
index is hoisted and the rest reads `ie`, a simple one is left in place.

Either way the *whole* residual below it is written twice, once per branch,
because that is what the block it stands for does. -/
syntax (name := stFreezeDecl) ident ident " ?= " rule_expr : rule_stmt
/-- `T alias sp = e` — KeY's storage *place* alias
(`Stmt.storagePlaceAlias`): a declaration that binds a path, not a value. -/
syntax (name := stAliasDecl) ident &" alias " ident " = " rule_expr : rule_stmt
/-- `T storage sp` / `T storage sp = nsp` -/
syntax (name := stStorageDecl) ident &" storage " ident : rule_stmt
syntax (name := stStorageDeclInit) ident &" storage " ident " = " rule_expr : rule_stmt
/-- `T memory mv` / `T memory mv = nmp` -/
syntax (name := stMemoryDecl) ident &" memory " ident : rule_stmt
syntax (name := stMemoryDeclInit) ident &" memory " ident " = " rule_expr : rule_stmt
/-! `require`, `assert` and `revert` are already reserved tokens (the `sol!`
grammar declares them), so they cannot be identifiers and need productions of
their own; their leading token is distinct, so they do not compete with the
bare-expression form. -/
syntax (name := stRequire) "require" "(" rule_expr ")" : rule_stmt
syntax (name := stAssert) "assert" "(" rule_expr ")" : rule_stmt
syntax (name := stRevert) "revert" "(" ")" : rule_stmt
/-- `delete(p)` — reserved for the same reason, and the one statement whose
argument is a place. -/
syntax (name := stDelete) "delete" "(" rule_expr ")" : rule_stmt
syntax (name := stPushValue) rule_expr noWs ".push(" rule_expr ")" : rule_stmt
syntax (name := stPushEmpty) rule_expr noWs ".push()" : rule_stmt
syntax (name := stPop) rule_expr noWs ".pop()" : rule_stmt
syntax (name := stTransfer) rule_expr noWs ".transfer(" rule_expr ")" : rule_stmt
/-- `if (nse) thn else els` — the branches are schematic blocks. -/
syntax (name := stIte) "if" " (" rule_expr ") " ident " else " ident : rule_stmt
/-- `if (se) { … } else { … }` — the branches written out, for the rules whose
residual *builds* a conditional rather than passing one through. -/
syntax (name := stIteWrite) "if" " (" rule_expr ") " "{" sepBy(rule_stmt, "; ", "; ", allowTrailingSep) "}"
  " else " "{" sepBy(rule_stmt, "; ", "; ", allowTrailingSep) "}" : rule_stmt
/-- A bare expression statement, and — through the application form — the
statements that read as calls: `require(se)`, `assert(se)`, `revert()`,
`delete(sp.fld)`. -/
syntax (name := stExpr) rule_expr : rule_stmt
/-- Escape to a Lean term of type `Stmt`. -/
syntax (name := stEscape) "‹" term "›" : rule_stmt

/-! An update, a term and a side formula are all `rule_expr`; only the
update's `:=` and the formula's connectives need syntax of their own. -/

declare_syntax_cat rule_upd
/-! An update's operands are parsed above the precedence of `||`, so that the
parallel update's own `||` separator still splits the list. -/

/-- `storage := save(p, t)`, `v := se`, `lsv := path(sp)`, `mv := alloc(sp)`. -/
syntax (name := updAssign) rule_expr:36 " := " rule_expr:36 : rule_upd
/-- `havoc`, `bump(e)`, `transfer(sadr, se)`, `clear(mv)`. -/
syntax (name := updBare) rule_expr:36 : rule_upd

declare_syntax_cat rule_formula
syntax (name := fmTop) "⊤" : rule_formula
syntax (name := fmBot) "⊥" : rule_formula
syntax (name := fmNeg) "¬" rule_formula : rule_formula
/-- `(φ when b)` — the guard KeY writes only for the operators that need it
(`/=` and `%=`); elsewhere it is `true`, and the reverting goal beside it is
dead. -/
syntax (name := fmWhen) "(" rule_formula " when " term ")" : rule_formula
/-- `inBounds(p)`, `nonEmpty(arr)`, `funded(se)`, `CInv`, or a condition
that must hold. -/
syntax (name := fmAtom) rule_expr : rule_formula

declare_syntax_cat rule_result
/-- `{u} <[ … ]>` — an update and what is left to run. -/
syntax (name := resUpdProg) "{" sepBy1(rule_upd, " || ") "} " "<[" sepBy(rule_stmt, "; ", "; ", allowTrailingSep) "]>" : rule_result
/-- `<[ … ]>` — a rewriting rule: no update, a residual program. -/
syntax (name := resProg) "<[" sepBy(rule_stmt, "; ", "; ", allowTrailingSep) "]>" : rule_result
/-- `{u} φ` / `φ` — KeY's `\replacewith(φ)`: an obligation, no program.
`revert()` here is the `\else` half of a guarded split. -/
syntax (name := resUpdObl) "{" sepBy1(rule_upd, " || ") "} " rule_formula : rule_result
syntax (name := resObl) rule_formula : rule_result
/-- `revert()` — the `\else` half of a guarded split
(`RuleResidual.reverting`). -/
syntax (name := resRevert) "revert" "(" ")" : rule_result
/-- `⟦ b ⟧` — the residual as a Lean `Block`, for the handful of rules whose
residual is *computed* from the condition proof (which is in scope as `h`)
rather than written out.  The conclusion and the condition stay declarative;
only the block is a term. -/
syntax (name := resEscape) "⟦" term "⟧" : rule_result

declare_syntax_cat rule_guard
/-- The negation of the preceding goal's guard. -/
syntax (name := guardElse) "else" : rule_guard
syntax (name := guardFormula) rule_formula : rule_guard

declare_syntax_cat rule_goal
/-- `| "label" : box : φ ⟹ result` — one goal of the taclet.  The label is
KeY's own goal name where it has one; the modality marker is the paper's
`[·]`/`⟨·⟩`, reserved for the rules that really do differ by modality. -/
syntax (name := goalLine) "| " (str " : ")? ((&"box" <|> &"diamond") " : ")?
  (rule_guard)? "⟹ " rule_result : rule_goal

declare_syntax_cat rule_goals
syntax (name := goalsOne) rule_result : rule_goals
syntax (name := goalsMany) (rule_goal)+ : rule_goals

/-- `from t1, t2` names the KeY taclets the rule transcribes; `from (e)`
gives a `KeyOrigin` term, for the operator-indexed families whose taclet is
chosen by an index table.  A rule with no `from` is Lean-only. -/
syntax ruleFrom := " from " (("(" term ")") <|> ident,+)

/-- `where c1, c2` appends conjuncts to the condition the pattern's schema
variables generate; `where cond := P` replaces it. -/
syntax ruleWhere := " where " ((&"cond" " := " term) <|> term,+)

/-- One rule of the calculus. -/
syntax ruleBinder := " (" ident " : " ident (" | " term)? ")"

/-- One rule of the calculus — the only way to write one.  `(op : BinOp | g)`
restricts the family to the instances `g` admits, as a conjunct right behind
the operator equation, which is where KeY's own sort restriction sits. -/
syntax (name := ruleDecl) (docComment)? "sol_rule " ident (&" twins")? (&" alternative")?
  (ruleBinder)? (ruleFrom)? " : "
  "<[" rule_stmt "]>" " ⇝ " rule_goals
  (&"after" rule_expr,+)? (ruleWhere)? : command

/-! ## Schema variables

The paper's central device: a variable's *kind* is its name, so the rules
are pairwise disjoint without an applicability predicate (`docs/LATEX.md`:
"Never reintroduce an `\is...` side condition; name a variable whose
declaration carries the kind").  This table is that convention, made
mechanical.

`kind` is the data location the name forces in a pattern, `free` the
conjuncts it contributes standing alone, `base` the ones it contributes as
the *base* of a path — fewer, because the pattern's `Kind.storage` has
already said the rest — and `trail` the conjunct emitted after all the
others.  The split matters: `Rules.lean` keeps `isArray`/`isMapping` last
and the `isStack ∧ isSimple` pair before them unfolded, because `And` is
right-nested and only a tail pair folds into `isSe`.
-/

/-- What a schema variable's name says about it. -/
structure Schema where
  kind : Option Name := none
  free : Array Name := #[]
  base : Array Name := #[]
  trail : Array Name := #[]
  /-- Spell the kind as `PlaceExpr.kind x = Kind.k ∧ isSimple x` when the
  variable stands alone as an assignment *target*, rather than as the `free`
  conjuncts.  `Rules.lean` keeps the two spellings distinct for the memory
  roots ("Where the conditions do not fold, and why"), and `Uniqueness.lean`
  bridges them. -/
  placeKind : Bool := false
  deriving Inhabited

/-- A name with its disambiguating digits dropped: `sp1` and `sp2` are both
the schema variable `sp` (the paper numbers them "target first and source
second"). -/
def stemOf (s : String) : String :=
  let t := s.dropRightWhile Char.isDigit
  if t.isEmpty then s else t

/-- The table.  Each row is one of the paper's schema variables; the kinds
that are single predicates are deliberately not aliased in `Rules.lean`, so
this is where the correspondence is written down. -/
def schemaVar (name : String) : Schema :=
  match stemOf name with
  | "se" => { free := #[`isSe] }
  | "nse" => { free := #[`isComplex], base := #[`isComplex] }
  | "v" => { free := #[`isStack] }
  | "lv" => { free := #[`isStackVar] }
  | "sp" => { kind := some `storage, free := #[`isSp], base := #[`isSimple] }
  | "nsp" => { kind := some `storage, free := #[`isStorage, `isComplex],
               base := #[`isComplex] }
  | "gsp" => { kind := some `storage, free := #[`isGlobal] }
  | "lsv" => { kind := some `storage, free := #[`isLocal] }
  | "arr" => { kind := some `storage, base := #[`isSimple], trail := #[`isArray] }
  | "map" => { kind := some `storage, base := #[`isSimple], trail := #[`isMapping] }
  | "ie" => { free := #[`isSimple], base := #[`isSimple] }
  | "mv" => { kind := some `memory, free := #[`isMv], base := #[`isSimple],
              placeKind := true }
  -- `ap`/`ar`: a memory array variable whose elements are primitive, resp.
  -- references — the paper's memory `delete` targets, which fix the element
  -- kind by name rather than by a side condition.
  | "ap" => { kind := some `memory, free := #[`isMv], base := #[`isSimple],
              trail := #[`isPrimArray], placeKind := true }
  | "ar" => { kind := some `memory, free := #[`isMv], base := #[`isSimple],
              trail := #[`isRefArray], placeKind := true }
  | "nmp" => { kind := some `memory, free := #[`isMemory, `isComplex],
               base := #[`isComplex] }
  | "sadr" => { free := #[`isSimple] }
  | "nadr" => { free := #[`isComplex] }
  | "nlhs" => { free := #[`isStorage, `isComplex] }
  -- `path`/`mpath`: a target whose *location* is fixed and whose shape the
  -- rule does not look at, the paper's unconstrained path.
  | "path" => { kind := some `storage }
  | "mpath" => { kind := some `memory, free := #[`isMemory] }
  -- `s`: simple at whatever location it lives in, weaker than `se`, which
  -- also says "stack".  `x`: constrained by the rule's `where` alone.
  | "s" => { free := #[`isSimple], base := #[`isSimple] }
  | "x" => {}
  | _ => {}

/-! ## Translation -/

/-- Structural syntax equality, ignoring source positions.  Used to tell
whether an expression written in a goal *is* the conclusion's target: if it
is, it denotes the whole parameter and must not be re-matched, which is the
terminal-rule discipline of `StepEffect`'s docstring ("a terminal rule's
goals never match on the place its `cond` matched"). -/
partial def sameSyntax : Syntax -> Syntax -> Bool
  | .missing, .missing => true
  | .atom _ a, .atom _ b => a == b
  | .ident _ _ a _, .ident _ _ b _ => a == b
  | .node _ k a, .node _ k' b =>
      k == k' && a.size == b.size &&
        (Array.zip a b).all (fun p => sameSyntax p.1 p.2)
  | _, _ => false

/-- Where an identifier in a goal comes from. -/
inductive Binding where
  /-- A condition parameter, or a binder of the conclusion's match. -/
  | plain
  /-- A scratch alias a capture statement introduced: the `Rules` name
  constant, the data location, and the expression captured from. -/
  | scratch (constName : Name) (kind : Name) (source : Term)
  /-- A value the conditional freeze bound (`Rules.freezeRhs`'s lambda), or
  the conditional index capture: the term the rest of the residual reads. -/
  | frozen (v : Term)
  /-- The name a declaration in the *conclusion* binds, with the data location
  and type it was declared at: as an expression it is that variable. -/
  | declared (kind : Name) (ty : Ident)
  /-- A `PlaceExpr` taken apart by the conclusion's pattern: the expression is
  its first component and `proof` its assignability witness, so writing the
  name back in a place position rebuilds the pair. -/
  | placeOf (proof : Ident)
  /-- The alias `_ pv = e` binds: read back at the *expression's* location
  (`Rules.valueAlias`), where `T pv = e` forces the stack. -/
  | valueScratch (source : Term)
  /-- A branch of the conclusion's `if`, which is a whole `Block`. -/
  | blockParam
  deriving Inhabited

/-- The names in scope while a goal is translated. -/
structure Scope where
  /-- The condition's parameters, each paired with the pattern it was
  destructured into (when it was), so that a goal can recognise the whole
  target. -/
  params : Array (Ident × Option Syntax) := #[]
  binds : Array (Name × Binding) := #[]
  /-- The type binder of the destructured parameter. -/
  tyName : Ident
  /-- The family binder, when the rule has one. -/
  opName : Option Ident := none
  /-- The conjunct the family binder's guard contributes, right behind the
  operator equation. -/
  opGuard : Option Term := none
  /-- The `Option` parameter a declaration's initialiser or a push's value is:
  a rule that mentions it writes the *parameter*, not `some e`, exactly as the
  hand-written arms did — the condition has already pinned which it is. -/
  optionParam : Option Ident := none

def Scope.find? (sc : Scope) (n : Name) : Option Binding :=
  (sc.binds.find? (fun p => p.1 == n)).map (·.2)

def Scope.withBind (sc : Scope) (n : Name) (b : Binding) : Scope :=
  { sc with binds := sc.binds.push (n, b) }

/-- The parameter an expression denotes outright, if any. -/
def Scope.asParam? (sc : Scope) (stx : Syntax) : Option Ident := Id.run do
  for (p, pat) in sc.params do
    if let some pat := pat then
      if sameSyntax pat stx then
        return some p
  return none


/-- A name the *generated* code refers to.  These constants live in
`Rules.lean` and `AST.lean`, not here — this module imports only `Lean` — so
they cannot be written as plain identifiers inside a quotation: hygiene
would tag them with this module's macro scope and they would not resolve
where the generated declaration lands. -/
def gen (x : Name) : Ident := mkIdent x

/-! ### Views

Matching on node kinds rather than quotation patterns: the postfix
productions share token prefixes (`.push()` against `.push(`), which makes a
quotation over them ambiguous for the tokenizer. -/

/-- The children of a production that carry something.  Its atoms are the
tokens, and indexing past them is what makes an accessor drift when a token
is split; every view below indexes `args`, not `getArgs`. -/
def args (stx : Syntax) : Array Syntax :=
  stx.getArgs.filter fun a => match a with | .atom _ _ => false | _ => true

/-- A parsed `rule_expr`. -/
inductive ExprView where
  | var (x : Ident)
  | field (base : Syntax) (fld : Ident)
  | index (base : Syntax) (idx : Syntax)
  | pushPlace (base : Syntax)
  | incDec (base : Syntax)
  /-- An application: the KeY-side vocabulary, read off the head name. -/
  | call (fn : Ident) (as : Array Syntax)
  | combine (lhs rhs : Syntax)
  /-- `⊖ e`: the schematic unary operator. -/
  | unop (arg : Syntax)
  /-- A named operator the rule matches outright. -/
  | fixedUnop (op : Name) (arg : Syntax)
  | fixedBinop (op : Name) (lhs rhs : Syntax)
  | ternary (c t e : Syntax)
  | escape (t : Term)

/-- Split a dotted identifier.  Lean's lexer reads `sp.fld` as **one**
identifier, so the `p.fld` production never fires on it; the components are
recovered here instead, exactly as `SoliditySyntax.expandSolPathExpr` does
for the `sol!` grammar. -/
def dottedParts (x : Ident) : List String :=
  x.getId.components.map (·.toString)

/-- A `rule_expr` node for a bare schema variable. -/
def varNode (x : Ident) : Syntax := mkNode ``exprVar #[x]

def exprView? (stx : Syntax) : Option ExprView :=
  let a := args stx
  if stx.isOfKind ``exprVar then
    let x : Ident := ⟨a[0]!⟩
    match dottedParts x with
    | [_] => some (.var x)
    | [base, fld] =>
        let b := mkIdentFrom x (Name.mkSimple base)
        let f := mkIdentFrom x (Name.mkSimple fld)
        some (.field (mkNode ``exprVar #[b]) f)
    | _ => none
  else if stx.isOfKind ``exprField then some (.field a[0]! ⟨a[1]!⟩)
  else if stx.isOfKind ``exprIndex then some (.index a[0]! a[1]!)
  else if stx.isOfKind ``exprPushPlace then some (.pushPlace a[0]!)
  else if stx.isOfKind ``exprIncDec then some (.incDec a[0]!)
  else if stx.isOfKind ``exprCall then
    -- `nsp.push()` is one identifier to the lexer, so the postfix production
    -- never fires on it; the receiver is recovered here.
    let f : Ident := ⟨a[0]!⟩
    let as := a[1]!.getSepArgs
    match f.getId.components.reverse, as.isEmpty with
    | last :: base :: [], true =>
        if last.toString == "push" then
          some (.pushPlace (varNode (mkIdentFrom f base)))
        else some (.call f as)
    | _, _ => some (.call f as)
  else if stx.isOfKind ``exprCombine then some (.combine a[0]! a[1]!)
  else if stx.isOfKind ``exprUnop then some (.unop a[0]!)
  else if stx.isOfKind ``exprNot then some (.fixedUnop `not a[0]!)
  else if stx.isOfKind ``exprAnd then some (.fixedBinop `and a[0]! a[1]!)
  else if stx.isOfKind ``exprOr then some (.fixedBinop `or a[0]! a[1]!)
  else if stx.isOfKind ``exprTernary then some (.ternary a[0]! a[1]! a[2]!)
  else if stx.isOfKind ``exprEscape then some (.escape ⟨a[0]!⟩)
  else none

/-- Is this expression a bare schema variable? -/
def isPlainVar (stx : Syntax) : Option Ident :=
  match exprView? stx with
  | some (.var x) => some x
  | _ => none

/-- The Boolean literal a bare `true`/`false` denotes. -/
def boolLit? (stx : Syntax) : Option Bool :=
  match exprView? stx with
  | some (.var x) =>
      match x.getId.toString with
      | "true" => some true
      | "false" => some false
      | _ => none
  | _ => none

/-- The head of an application, if the expression is one. -/
def callHead? (stx : Syntax) : Option (String × Array Syntax) :=
  match exprView? stx with
  | some (.call f as) => some (f.getId.toString, as)
  | _ => none

/-- The head of an application read off the *node*, before `exprView?` gets to
reinterpret it.  `sp.push()` is a push place in an expression and a push
statement on its own, and only the position tells them apart. -/
def rawCallHead? (stx : Syntax) : Option (String × Array Syntax) :=
  if stx.isOfKind ``exprCall then
    let a := args stx
    some ((⟨a[0]!⟩ : Ident).getId.toString, a[1]!.getSepArgs)
  else none

/-- The head identifier of a path expression: the schema variable the whole
path hangs off, and so the name that decides its kind. -/
partial def headName (stx : Syntax) : Name :=
  match exprView? stx with
  | some (.var x) => x.getId
  | some (.field b _) | some (.index b _) | some (.pushPlace b)
  | some (.incDec b) => headName b
  | _ => Name.anonymous

/-- The schema variable a path hangs off, reaching through an `incDec`
wrapper: `sp.fld++` is a rule about `sp`. -/
partial def targetOf (stx : Syntax) : Syntax :=
  match exprView? stx with
  | some (.incDec b) => targetOf b
  | _ => stx

/-- `Kind.storage` / `Kind.memory` / `Kind.stack` as a term. -/
def kindTerm (k : Name) : CommandElabM Term := do
  let i := mkIdent (`Kind ++ k)
  `($i:ident)

/-- The data location a schema name forces, defaulting to the stack. -/
def kindOfName (n : Name) : Name :=
  (schemaVar n.toString).kind.getD `stack

/-- The `Rules` constant naming the scratch alias a capture binds, and where
it lives.  Four fixed names, the paper's kind-names, where KeY generates
fresh ones — see `Rules.lean`'s fresh-name conventions. -/
def scratchOf (n : Name) : Option (Name × Name) :=
  match stemOf n.toString with
  | "sp" => some (`storagePathAliasName, `storage)
  | "mv" => some (`memoryPathAliasName, `memory)
  | "se" => some (`valueAliasName, `stack)
  | "ie" => some (`indexAliasName, `stack)
  | _ => none

/-- When a path's base is a scratch alias, its constant, kind and source. -/
def baseScratch? (sc : Scope) (b : Syntax) : Option (Name × Name × Term) :=
  match exprView? b with
  | some (.var x) =>
      match sc.find? x.getId with
      | some (.scratch c k src) => some (c, k, src)
      | _ => none
  | _ => none

/-- A `rule_expr` as a `WrappedExpr`, or with `asPlace` as a `PlaceExpr`. -/
partial def transExpr (sc : Scope) (asPlace : Bool) (stx : Syntax) :
    CommandElabM Term := do
  -- An expression that *is* the conclusion's target denotes the whole
  -- parameter: a terminal rule hands the place to its update undecomposed,
  -- which is the discipline `StepEffect`'s docstring states.
  if let some p := sc.asParam? stx then
    return p
  let some view := exprView? stx
    | throwErrorAt stx "unsupported rule expression"
  match view with
  | .escape t => return t
  | .call f _ => throwErrorAt stx s!"`{f.getId}` is a term, not a program expression"
  | .combine a b =>
      let some op := sc.opName
        | throwErrorAt stx "`⊕` needs the rule to declare a `BinOp` parameter"
      `($(gen `WrappedExpr.binop) $op $(← transExpr sc false a) $(← transExpr sc false b))
  | .unop a =>
      let some op := sc.opName
        | throwErrorAt stx "`⊖` needs the rule to declare a `UnOp` parameter"
      `($(gen `WrappedExpr.unop) $op $(← transExpr sc false a))
  | .fixedUnop op a =>
      let oi := mkIdent (`UnOp ++ op)
      `($(gen `WrappedExpr.unop) $oi $(← transExpr sc false a))
  | .fixedBinop op a b =>
      let oi := mkIdent (`BinOp ++ op)
      `($(gen `WrappedExpr.binop) $oi $(← transExpr sc false a) $(← transExpr sc false b))
  | .ternary c t e =>
      `($(gen `WrappedExpr.ternary) $(← transExpr sc false c) $(← transExpr sc false t)
          $(← transExpr sc false e))
  | .var x =>
      if let some b := boolLit? stx then
        let bt := mkIdent (if b then `Bool.true else `Bool.false)
        return (← `($(gen `WrappedExpr.bool) $bt))
      match sc.find? x.getId with
      | some (.frozen v) => return v
      | some (.blockParam) => return x
      | some (.valueScratch src) =>
          if asPlace then throwErrorAt stx "a value capture is not a place"
          else `($(gen `Rules.valueAlias) $src)
      | some (.declared k ty) =>
          -- A declared name is a `Name`, not an expression; it reaches a goal
          -- only as an assignment target or as an update's binder.
          if asPlace then `($(gen `SoliditySyntax.varPlace) $(← kindTerm k) $ty $x)
          else throwErrorAt stx s!"`{x.getId}` is a declared name, not an expression"
      | some (.placeOf hass) =>
          if asPlace then `((⟨$x, $hass⟩ : $(gen `PlaceExpr))) else return x
      | some (.scratch c k src) =>
          let kt ← kindTerm k
          let ci := mkIdent (`Rules ++ c)
          if asPlace then `($(gen `Rules.aliasPlace) $kt ($src).ty $ci)
          else match stemOf x.getId.toString with
            | "se" => `($(gen `Rules.stackValueAlias) $src)
            | "ie" => `($(gen `Rules.indexAlias) $src)
            | _ => `($(gen `Rules.aliasExpr) $kt ($src).ty $ci)
      | _ => return x
  | .field b f =>
      let ty := sc.tyName
      match baseScratch? sc b with
      | some (c, k, src) =>
          let kt ← kindTerm k
          let ci := mkIdent (`Rules ++ c)
          if asPlace then `($(gen `Rules.fieldFromAlias) $kt $ci $ty $src $f)
          else `(($(gen `Rules.fieldFromAlias) $kt $ci $ty $src $f : $(gen `WrappedExpr)))
      | none =>
          let bt ← transExpr sc false b
          -- A push place is a storage slot, and the field's own type is the
          -- one the access has: `sp.push().fld` names the slot's member.
          let isPush := match exprView? b with | some (.pushPlace _) => true | _ => false
          let kt ← kindTerm (if isPush then `storage else kindOfName (headName b))
          let ty : Term ← if isPush then `(($f).ty) else pure ty
          if asPlace then `($(gen `PlaceExpr.field) $kt $ty $bt $f)
          else `($(gen `WrappedExpr.field) $kt $ty $bt $f)
  | .index b i =>
      let ty := sc.tyName
      let it ← transExpr sc false i
      match baseScratch? sc b with
      | some (c, k, src) =>
          let kt ← kindTerm k
          let ci := mkIdent (`Rules ++ c)
          if asPlace then `($(gen `Rules.indexFromAlias) $kt $ci $ty $src $it)
          else `(($(gen `Rules.indexFromAlias) $kt $ci $ty $src $it : $(gen `WrappedExpr)))
      | none =>
          let bt ← transExpr sc false b
          let kt ← kindTerm (kindOfName (headName b))
          if asPlace then `($(gen `PlaceExpr.index) $kt $ty $bt $it)
          else `($(gen `WrappedExpr.index) $kt $ty $bt $it)
  | .pushPlace b =>
      let bt ← transExpr sc asPlace b
      if asPlace then `($(gen `PlaceExpr.pushPlace) $bt) else `($(gen `WrappedExpr.pushPlace) $bt)
  | .incDec b =>
      let bt ← transExpr sc false b
      let some op := sc.opName
        | throwErrorAt stx "`++` needs the rule to declare an `IncDec` parameter"
      `($(gen `WrappedExpr.incDec) $op $bt)

/-! ### The KeY side of a goal

`Sym`, `SideFormula`, `UpdElem` and `Premise` are all written as
applications, and each is read off its head name. -/

/-- A `rule_expr` as a `Rules.Sym`.

An expression that *is* the conclusion's parameter denotes the parameter, and
is read whole: `{ lv := se1 ⊕ se2 }` on a conclusion that matched the operator
node is `read rhs`, not `combined` of its pieces, which is what
`binopAssignment` writes. -/
def transSym (sc : Scope) (stx : Syntax) : CommandElabM Term := do
  if let some p := sc.asParam? stx then
    return (← `($(gen `Sym.read) $p))
  match callHead? stx with
  | some ("current", #[p]) => `($(gen `Sym.current) $(← transExpr sc false p))
  | some ("length", #[a]) => `($(gen `Sym.length) $(← transExpr sc false a))
  | some ("net", #[a]) => `($(gen `Sym.netOf) $(← transExpr sc false a))
  | some ("read", #[e]) => `($(gen `Sym.read) $(← transExpr sc false e))
  | some ("default", #[t]) =>
      let some (.var ty) := exprView? t
        | throwErrorAt t "`default` takes a type"
      `($(gen `Sym.deflt) $ty)
  | _ =>
      match exprView? stx with
      | some (.combine a b) =>
          let some op := sc.opName
            | throwErrorAt stx "`⊕` needs the rule to declare a `BinOp` parameter"
          `($(gen `Sym.combined) $op $(← transExpr sc false a) $(← transExpr sc false b))
      | _ => `($(gen `Sym.read) $(← transExpr sc false stx))

/-- A `rule_formula` as a `Rules.SideFormula`. -/
partial def transFormula (sc : Scope) (stx : Syntax) : CommandElabM Term := do
  let k := stx.getKind
  let a := args stx
  if k == ``fmTop then `($(gen `SideFormula.const) true)
  else if k == ``fmBot then `($(gen `SideFormula.const) false)
  else if k == ``fmNeg then `($(gen `SideFormula.neg) $(← transFormula sc a[0]!))
  else if k == ``fmWhen then do
    let inner ← transFormula sc a[0]!
    let cond : Term := ⟨a[1]!⟩
    `(if $cond then $inner else $(gen `SideFormula.const) true)
  else if k == ``fmAtom then
    let e := a[0]!
    match callHead? e with
    | some ("inBounds", #[p]) => `($(gen `SideFormula.inBounds) $(← transExpr sc false p))
    | some ("nonEmpty", #[p]) => `($(gen `SideFormula.nonEmpty) $(← transExpr sc false p))
    | some ("nonZero", #[p]) => `($(gen `SideFormula.nonZero) $(← transExpr sc false p))
    | some ("rhsNonZero", #[p]) => `($(gen `SideFormula.rhsNonZero) $(← transExpr sc false p))
    | some ("funded", #[p]) => `($(gen `SideFormula.funded) $(← transExpr sc false p))
    | _ =>
        match exprView? e with
        | some (.var x) =>
            if x.getId.toString == "CInv" then `($(gen `SideFormula.cinv))
            else `($(gen `SideFormula.holds) $(← transExpr sc false e))
        | _ => `($(gen `SideFormula.holds) $(← transExpr sc false e))
  else throwErrorAt stx "unsupported side formula"

/-- Is this result the `\else` half of a guarded split — KeY's bare
`revert()`? -/
def isRevertResult (stx : Syntax) : Bool :=
  stx.getKind == ``resRevert

mutual
/-- A `rule_upd`'s memory term.  `memory` is the program variable, and the
allocating and writing forms nest as KeY's do -- `write(addM(memory), mv.fld,
fresh)` is `memoryFieldDeleteReference` verbatim. -/
partial def transMemTerm (sc : Scope) (stx : Syntax) : CommandElabM Term := do
  match callHead? stx with
  | some ("alloc", as) =>
      -- `alloc(mv)` allocates for `mv`'s type, taking the source from the
      -- rule's `Option` parameter; `alloc(mv, sp)` names the source outright.
      let ty : Term <-
        match exprView? as[0]! with
        | some (.var x) =>
            match sc.find? x.getId with
            | some (.declared _ t) => (pure t : CommandElabM Term)
            | _ => do let t <- transExpr sc false as[0]!; `(($t).ty)
        | _ => do let t <- transExpr sc false as[0]!; `(($t).ty)
      if h : as.size = 2 then
        `($(gen `Rules.allocTerm) $ty (some $(<- transExpr sc false as[1])))
      else
        `($(gen `Rules.allocTerm) $ty $(sc.optionParam.getD (mkIdent `init)))
  | some ("addM", #[m, x]) =>
      let t <- transExpr sc false x
      `($(gen `MemTerm.addM) $(<- transMemTerm sc m) ($t).ty)
  | some ("write", #[m, p, v]) =>
      `($(gen `MemTerm.write) $(<- transMemTerm sc m) $(<- transExpr sc false p)
          $(<- transMemVal sc v))
  | _ =>
      match exprView? stx with
      | some (.var x) =>
          if x.getId.toString == "memory" then `($(gen `MemTerm.cur))
          else throwErrorAt stx "not a memory term"
      | _ => throwErrorAt stx "not a memory term"

/-- A `write`'s value slot. -/
partial def transMemVal (sc : Scope) (stx : Syntax) : CommandElabM Term := do
  match callHead? stx with
  | some ("image", #[src]) => `($(gen `MemVal.image) $(<- transExpr sc false src))
  | some ("defVal", #[x]) =>
      let t <- transExpr sc false x
      `($(gen `MemVal.defVal) ($t).ty)
  | _ =>
      match exprView? stx with
      | some (.var x) =>
          if x.getId.toString == "fresh" then `($(gen `MemVal.fresh))
          else `($(gen `MemVal.sym) $(<- transSym sc stx))
      | _ => `($(gen `MemVal.sym) $(<- transSym sc stx))
end

/-- A `rule_upd` as a `Rules.UpdElem`. -/
def transUpd (sc : Scope) (stx : Syntax) : CommandElabM Term := do
  let a := args stx
  if stx.getKind == ``updBare then
    let e := a[0]!
    match callHead? e with
    | some ("bump", #[t]) => `($(gen `UpdElem.bumpOf) $(← transExpr sc false t))
    | some ("transfer", #[r, v]) =>
        `($(gen `UpdElem.transfer) $(← transExpr sc false r) $(← transExpr sc false v))
    | some ("clear", #[t]) => `($(gen `UpdElem.memDelete) $(← transExpr sc false t))
    | _ =>
        match exprView? e with
        | some (.var x) =>
            if x.getId.toString == "havoc" then `($(gen `UpdElem.havoc))
            else throwErrorAt e "unsupported update"
        | _ => throwErrorAt e "unsupported update"
  else
    let lhs := a[0]!
    let rhs := a[1]!
    let component : Option String :=
      match exprView? lhs with
      | some (.var x) =>
          let n := x.getId.toString
          if n == "storage" || n == "memory" then some n else none
      | _ => none
    -- A declaration's own name on the left: the update binds the *name*, and
    -- `alloc`/`default` are the two right-hand sides that reach it.
    if let some (.var x) := exprView? lhs then
      if let some (.declared _ ty) := sc.find? x.getId then
        let bind (r : Term) : CommandElabM Term := `($(gen `UpdElem.bind) $x $r)
        match callHead? rhs with
        | some ("freshId", #[m]) =>
            return (← bind (← `($(gen `BindRhs.freshId) $(← transMemTerm sc m))))
        | some ("default", _) =>
            return (← bind (← `($(gen `BindRhs.val) ($(gen `Sym.deflt) $ty))))
        | some ("path", #[t]) =>
            return (← bind (← `($(gen `BindRhs.path) $(← transExpr sc false t))))
        | some ("ref", #[t]) =>
            return (← bind (← `($(gen `BindRhs.mref) $(← transExpr sc false t))))
        | some ("slot", #[t]) =>
            return (← bind (← `($(gen `BindRhs.pushSlot) $(← transExpr sc false t))))
        | _ => return (← bind (← `($(gen `BindRhs.val) $(← transSym sc rhs))))
    match component, callHead? rhs with
    | some "storage", some ("save", #[p, t]) =>
        `($(gen `UpdElem.storage) ($(gen `StorageUpd.save) $(← transExpr sc false p) $(← transSym sc t)))
    | some "storage", some ("copy", #[p, s]) =>
        `($(gen `UpdElem.storage) ($(gen `StorageUpd.copy) $(← transExpr sc false p) $(← transExpr sc false s)))
    | some "storage", some ("copyMem", #[p, s]) =>
        `($(gen `UpdElem.storage) ($(gen `StorageUpd.copyFromMem) $(← transExpr sc false p) $(← transExpr sc false s)))
    | some "storage", some ("push", as) =>
        let arr ← transExpr sc false as[0]!
        -- `push(sp, se)` and `push(sp)` are the same update at different
        -- sorts; which it is the condition has already said, so the element
        -- written is the `Option` parameter itself.
        match sc.optionParam with
        | some v => `($(gen `UpdElem.storage) ($(gen `StorageUpd.push) $arr $v))
        | none =>
            if h : as.size = 2 then
              `($(gen `UpdElem.storage) ($(gen `StorageUpd.push) $arr (some $(← transExpr sc false as[1]))))
            else `($(gen `UpdElem.storage) ($(gen `StorageUpd.push) $arr none))
    | some "storage", some ("pushSlot", #[p]) =>
        `($(gen `UpdElem.storage) ($(gen `StorageUpd.pushPlace) $(← transExpr sc false p)))
    | some "storage", some ("pop", #[p]) =>
        `($(gen `UpdElem.storage) ($(gen `StorageUpd.pop) $(← transExpr sc false p)))
    | some "storage", some ("clear", #[p]) =>
        `($(gen `UpdElem.storage) ($(gen `StorageUpd.clear) $(← transExpr sc false p)))
    | some "memory", _ => `($(gen `UpdElem.heap) $(← transMemTerm sc rhs))
    | none, some ("freshId", #[m]) =>
        `($(gen `UpdElem.bind) ($(gen `Rules.varName) $(← transExpr sc false lhs))
            ($(gen `BindRhs.freshId) $(← transMemTerm sc m)))
    | none, some ("path", #[s]) =>
        `($(gen `UpdElem.bind) ($(gen `Rules.varName) $(← transExpr sc false lhs))
            ($(gen `BindRhs.path) $(← transExpr sc false s)))
    | none, some ("ref", #[s]) =>
        `($(gen `UpdElem.bind) ($(gen `Rules.varName) $(← transExpr sc false lhs))
            ($(gen `BindRhs.mref) $(← transExpr sc false s)))
    | none, some ("slot", #[s]) =>
        `($(gen `UpdElem.bind) ($(gen `Rules.varName) $(← transExpr sc false lhs))
            ($(gen `BindRhs.pushSlot) $(← transExpr sc false s)))
    | none, _ => `($(gen `Rules.writeBack) $(← transExpr sc true lhs) $(← transSym sc rhs))
    | _, _ => throwErrorAt stx "unsupported update"

/-- An `after` entry as a `Rules.Premise`. -/
def transPremise (sc : Scope) (stx : Syntax) : CommandElabM Term := do
  match callHead? stx with
  | some ("read", #[t]) => `($(gen `Premise.read) $(← transSym sc t))
  | some ("resolve", #[p]) => `($(gen `Premise.resolve) $(← transExpr sc false p))
  | some ("image", #[s]) => `($(gen `Premise.image) $(← transExpr sc false s))
  | _ => throwErrorAt stx "a premise is `read(t)`, `resolve(p)` or `image(s)`"

/-! ### Residual statements

A residual is a program, and the capture idioms are the statements the paper
writes as `T_e se = e;` and `T_nsp storage sp = nsp;`.  Each binds a scratch
alias, so a later `sp.fld` is the alias read-back rather than a second
occurrence of the path. -/

/-- A parsed `rule_stmt`. -/
inductive StmtView where
  | assign (lhs rhs : Syntax)
  | compound (lhs rhs : Syntax)
  | require (cond : Syntax)
  | assert (cond : Syntax)
  | revert
  | decl (kind : Name) (ty name : Ident) (init : Option Syntax)
  | push (target : Syntax) (value : Option Syntax)
  | pop (target : Syntax)
  | transfer (recipient amount : Syntax)
  | ite (cond : Syntax) (thn els : Ident)
  /-- `if (se) { … } else { … }` — the branches written out. -/
  | iteWrite (cond : Syntax) (thn els : Array Syntax)
  /-- `_ se = e` — the capture at the *expression's* location. -/
  | valueDecl (name : Ident) (src : Syntax)
  /-- `T se ?= e` — a conditional capture; which one the name says. -/
  | freezeDecl (name : Ident) (src : Syntax)
  /-- `T alias sp = e` — a storage *place* alias. -/
  | aliasDecl (ty name : Ident) (src : Syntax)
  /-- `delete(p)`. -/
  | delete (target : Syntax)
  | expr (e : Syntax)
  | escape (t : Term)
  deriving Inhabited

/-- The receiver of a dotted call head (`sp.pop`, `alice.account.push`): the
components before the method name, rebuilt as a path. -/
def receiverOf (parts : List String) (ref : Syntax) : Option Syntax :=
  match parts with
  | [b] => some (varNode (mkIdentFrom ref (Name.mkSimple b)))
  | [b, f] =>
      some (mkNode ``exprField
        #[varNode (mkIdentFrom ref (Name.mkSimple b)), mkAtomFrom ref ".",
          mkIdentFrom ref (Name.mkSimple f)])
  | _ => none

def stmtView? (stx : Syntax) : Option StmtView :=
  let k := stx.getKind
  let a := args stx
  if k == ``stAssign then some (.assign a[0]! a[1]!)
  else if k == ``stRequire then some (.require a[0]!)
  else if k == ``stAssert then some (.assert a[0]!)
  else if k == ``stRevert then some .revert
  else if k == ``stDelete then some (.delete a[0]!)
  else if k == ``stCompound then some (.compound a[0]! a[1]!)
  else if k == ``stStackDecl then some (.decl `stack ⟨a[0]!⟩ ⟨a[1]!⟩ none)
  else if k == ``stStackDeclInit then some (.decl `stack ⟨a[0]!⟩ ⟨a[1]!⟩ (some a[2]!))
  else if k == ``stStorageDecl then some (.decl `storage ⟨a[0]!⟩ ⟨a[1]!⟩ none)
  else if k == ``stStorageDeclInit then some (.decl `storage ⟨a[0]!⟩ ⟨a[1]!⟩ (some a[2]!))
  else if k == ``stMemoryDecl then some (.decl `memory ⟨a[0]!⟩ ⟨a[1]!⟩ none)
  else if k == ``stMemoryDeclInit then some (.decl `memory ⟨a[0]!⟩ ⟨a[1]!⟩ (some a[2]!))
  else if k == ``stPushValue then some (.push a[0]! (some a[1]!))
  else if k == ``stPushEmpty then some (.push a[0]! none)
  else if k == ``stPop then some (.pop a[0]!)
  else if k == ``stTransfer then some (.transfer a[0]! a[1]!)
  else if k == ``stIte then some (.ite a[0]! ⟨a[1]!⟩ ⟨a[2]!⟩)
  else if k == ``stIteWrite then
    some (.iteWrite a[0]! a[1]!.getSepArgs a[2]!.getSepArgs)
  else if k == ``stValueDecl then some (.valueDecl ⟨a[0]!⟩ a[1]!)
  else if k == ``stFreezeDecl then some (.freezeDecl ⟨a[1]!⟩ a[2]!)
  else if k == ``stAliasDecl then some (.aliasDecl ⟨a[0]!⟩ ⟨a[1]!⟩ a[2]!)
  else if k == ``stExpr then
    -- `sp.pop()`, `arr.push(se)`, `sadr.transfer(se)`: one identifier to the
    -- lexer, a method call here.
    match rawCallHead? a[0]! with
    | some (fn, as) =>
        let parts := fn.splitOn "."
        match parts.reverse with
        | "pop" :: rest =>
            match receiverOf rest.reverse a[0]!, as.isEmpty with
            | some r, true => some (.pop r)
            | _, _ => some (.expr a[0]!)
        | "push" :: rest =>
            match receiverOf rest.reverse a[0]! with
            | some r => some (.push r (if h : as.size = 1 then some as[0] else none))
            | none => some (.expr a[0]!)
        | "transfer" :: rest =>
            match receiverOf rest.reverse a[0]!, as.size == 1 with
            | some r, true => some (.transfer r as[0]!)
            | _, _ => some (.expr a[0]!)
        | _ => some (.expr a[0]!)
    | none => some (.expr a[0]!)
  else if k == ``stEscape then some (.escape ⟨a[0]!⟩)
  else none

/-! A residual is a program, and two of its statements are not statements at
all but *splits*: a conditional capture stands for the whole block below it,
written twice.  `transBlock` is therefore where the shape is decided and
`transStmt` only ever sees an ordinary statement. -/

mutual

/-- One residual statement, and the scope it leaves behind: a capture binds
its scratch alias for the statements that follow. -/
partial def transStmt (sc : Scope) (stx : Syntax) : CommandElabM (Term × Scope) := do
  let some view := stmtView? stx
    | throwErrorAt stx "unsupported rule statement"
  match view with
  | .escape t => return (t, sc)
  | .freezeDecl _ _ =>
      throwErrorAt stx "a `?=` capture stands for the whole residual below it, \
        so it may not appear inside one"
  | .valueDecl name src =>
      let t ← transExpr sc false src
      return (← `($(gen `Rules.captureValue) $t), sc.withBind name.getId (.valueScratch t))
  | .aliasDecl ty name src =>
      return (← `($(gen `Stmt.storagePlaceAlias) $ty $name $(← transExpr sc false src)), sc)
  | .decl kind ty name init =>
      let ctor := match kind with
        | `storage => mkIdent `Stmt.storageDecl
        | `memory => mkIdent `Stmt.memoryDecl
        | _ => mkIdent `Stmt.stackDecl
      let some initStx := init
        | return (← `($ctor $ty $name none), sc)
      let src ← transExpr sc false initStx
      -- The conclusion's own declared variable, re-declared: not a capture,
      -- even where its name is spelled like a scratch alias (`mv`).
      if let some (.declared ..) := sc.find? name.getId then
        return (← `($ctor $ty $name (some $src)), sc)
      -- The capture idioms, named by the scratch alias the declaration binds.
      match scratchOf name.getId, kind with
      | some (`storagePathAliasName, _), `storage =>
          return (← `($(gen `Rules.captureStoragePath) $src),
                  sc.withBind name.getId (.scratch `storagePathAliasName `storage src))
      | some (`memoryPathAliasName, _), `memory =>
          return (← `($(gen `Rules.captureMemoryPath) $src),
                  sc.withBind name.getId (.scratch `memoryPathAliasName `memory src))
      | some (c, k), `stack =>
          let helper := match c with
            | `indexAliasName => `Rules.captureIndex
            | _ => `Rules.captureStackValue
          let h := mkIdent helper
          return (← `($h $src), sc.withBind name.getId (.scratch c k src))
      | _, _ => return (← `($ctor $ty $name (some $src)), sc)
  | .assign lhs rhs =>
      return (← `($(gen `Stmt.assign) $(← transExpr sc true lhs) $(← transExpr sc false rhs)), sc)
  | .compound lhs rhs =>
      let some op := sc.opName
        | throwErrorAt stx "`⊕=` needs the rule to declare a `BinOp` parameter"
      return (← `($(gen `Stmt.compoundAssign) $op $(← transExpr sc true lhs)
                    $(← transExpr sc false rhs)), sc)
  | .push target value =>
      let t ← transExpr sc true target
      match value with
      | none => return (← `($(gen `Stmt.push) $t none), sc)
      | some v => return (← `($(gen `Stmt.push) $t (some $(← transExpr sc false v))), sc)
  | .pop target => return (← `($(gen `Stmt.pop) $(← transExpr sc true target)), sc)
  | .transfer r a =>
      return (← `($(gen `Stmt.transfer) $(← transExpr sc false r) $(← transExpr sc false a)), sc)
  | .ite c thn els =>
      return (← `($(gen `Stmt.ite) $(← transExpr sc false c) $thn $els), sc)
  | .iteWrite c thn els =>
      return (← `($(gen `Stmt.ite) $(← transExpr sc false c)
                    $(← transBlock sc thn) $(← transBlock sc els)), sc)
  | .require c => return (← `($(gen `Stmt.requireStmt) $(← transExpr sc false c)), sc)
  | .assert c => return (← `($(gen `Stmt.assertStmt) $(← transExpr sc false c)), sc)
  | .revert => return (← `($(gen `Stmt.revert) none), sc)
  | .delete t => return (← `($(gen `Stmt.delete) $(← transExpr sc true t)), sc)
  | .expr e =>
      match callHead? e with
      | some ("delete", #[t]) =>
          return (← `($(gen `Stmt.delete) $(← transExpr sc true t)), sc)
      | _ => return (← `($(gen `Stmt.expr) $(← transExpr sc false e)), sc)

/-- A list of ordinary statements, folded left to right. -/
partial def transStmts (sc : Scope) (stmts : Array Syntax) : CommandElabM Term := do
  let mut sc := sc
  let mut out : Array Term := #[]
  for st in stmts do
    let (t, sc') ← transStmt sc st
    out := out.push t
    sc := sc'
  `([$out,*])

/-- A residual program.

Three shapes, in the order they are recognised.  A lone block parameter is
that block (`ifElseTrue`'s residual is its own `then` branch).  A `?=` capture
is a *split*: the freeze wraps everything below it in `Rules.freezeRhs`, and
the index capture writes the whole list twice, once with the hoist and once
without — which is what `Rules.indexWriteResolveBlock` does by hand, and why
the two are written as one statement rather than an `if` the rule spells out.
Anything else is the statements themselves. -/
partial def transBlock (sc : Scope) (stmts : Array Syntax) : CommandElabM Term := do
  -- A branch of the conclusion's own `if`, passed through whole.
  if h : stmts.size = 1 then
    if let some (.expr e) := stmtView? stmts[0] then
      if let some x := isPlainVar e then
        if let some .blockParam := sc.find? x.getId then
          return x
  -- A conditional capture: the freeze leads, the index capture may not.
  for h : i in [0:stmts.size] do
    if let some (.freezeDecl name src) := stmtView? stmts[i] then
      let t ← transExpr sc false src
      if stemOf name.getId.toString == "ie" then
        let rest := stmts[0:i].toArray ++ stmts[i+1:stmts.size].toArray
        let hoisted := stmts[0:i].toArray ++ #[stmts[i]] ++ stmts[i+1:stmts.size].toArray
        let scC := sc.withBind name.getId (.frozen (← `($(gen `Rules.indexAlias) $t)))
        -- The capture itself, in the branch that performs it.
        let mut out : Array Term := #[]
        let mut scc := scC
        for st in hoisted do
          if let some (.freezeDecl _ _) := stmtView? st then
            out := out.push (← `($(gen `Rules.captureIndex) $t))
          else
            let (tm, sc') ← transStmt scc st
            out := out.push tm
            scc := sc'
        let thenB : Term ← `([$out,*])
        let elseB ← transStmts (sc.withBind name.getId (.frozen t)) rest
        return (← `(if ($t).complex then $thenB else $elseB))
      else
        if i != 0 then
          throwErrorAt stmts[i] "a value freeze wraps the residual below it, \
            so it has to come first"
        let rest := stmts[1:stmts.size].toArray
        let body ← transBlock (sc.withBind name.getId (.frozen name)) rest
        return (← `($(gen `Rules.freezeRhs) $t (fun $name => $body)))
  transStmts sc stmts

end

/-! ### Goals -/

/-- A parsed goal line. -/
structure GoalView where
  label : Option String := none
  mode : Option Name := none
  guardStx : Option Syntax := none
  isElse : Bool := false
  result : Syntax
  ref : Syntax
  deriving Inhabited

/-- The contents of an optional group.  `Syntax.getOptional?` only answers
for a group of exactly one element, and these groups carry their separator
(`"label" :`, `box :`, `after e, e`), so the null node is read directly. -/
def group? (stx : Syntax) : Option Syntax :=
  if stx.getNumArgs == 0 then none else some stx

def goalView? (stx : Syntax) : Option GoalView :=
  if stx.getKind != ``goalLine then none else
  let label := (group? stx[1]).bind fun g => g[0].isStrLit?
  -- The marker is a non-reserved keyword inside an optional group, so it is
  -- found rather than indexed: the group also carries its `:` separator, and
  -- the alternation may or may not wrap it in a node.
  let hasAtom (g : Syntax) (v : String) : Bool :=
    g.getArgs.any fun a => a.getAtomVal == v || a.getArgs.any (·.getAtomVal == v)
  let mode := (group? stx[2]).map fun g =>
    if hasAtom g "box" then `box else `diamond
  let g := (group? stx[3]).map fun gg => gg[0]
  let isElse := match g with | some gg => gg.getKind == ``guardElse | none => false
  let guardStx := match g with
    | some gg => if gg.getKind == ``guardFormula then some gg[0] else none
    | none => none
  some { label := label, mode := mode, guardStx := guardStx, isElse := isElse
         result := stx[5], ref := stx }

/-- What a goal's result says. -/
inductive ResultView where
  | prog (upds : Array Syntax) (stmts : Array Syntax)
  | obligation (upds : Array Syntax) (φ : Syntax)
  | reverting
  /-- `⟦ b ⟧` — the residual as a term. -/
  | escape (b : Term)

def resultView? (stx : Syntax) : Option ResultView :=
  let k := stx.getKind
  let a := args stx
  if isRevertResult stx then some .reverting
  else if k == ``resEscape then some (.escape ⟨a[0]!⟩)
  else if k == ``resUpdProg then some (.prog a[0]!.getSepArgs a[1]!.getSepArgs)
  else if k == ``resProg then some (.prog #[] a[0]!.getSepArgs)
  else if k == ``resUpdObl then some (.obligation a[0]!.getSepArgs a[1]!)
  else if k == ``resObl then some (.obligation #[] a[0]!)
  else none


/-! ### The conclusion

The statement a rule matches decides three things at once: which `*Effect`
builder carries it, which parameter (if any) is destructured, and — through
the schema variables' names — what the condition says. -/

/-- A conjunct of a rule's condition, kept unapplied so that the folding
rule can be decided once the whole conjunction is known. -/
inductive Cond where
  /-- A `Rules` predicate at a schema variable. -/
  | pred (p : Name) (x : Ident)
  /-- A conjunct written out: a `where` clause, or an operator equation. -/
  | raw (t : Term)

/-- The pairs `Rules.lean` names as reducible `abbrev`s.  They may be used
only at the *tail* of a condition: `And` is right-nested and not
definitionally associative, so a pair that something follows has to stay
unfolded — which is exactly why the array and mapping terminals spell
`isStack se ∧ isSimple se` out (`Rules.lean`, "Where the conditions do not
fold, and why"). -/
def foldedPair : Name -> Option (Name × Name)
  | `isSe => some (`isStack, `isSimple)
  | `isSp => some (`isStorage, `isSimple)
  | `isMv => some (`isMemory, `isSimple)
  | `isNmp => some (`isMemory, `isComplex)
  | _ => none

/-- Apply a predicate of `Rules` to a schema variable. -/
def applyPred (p : Name) (x : Ident) : CommandElabM Term := do
  let f := mkIdent (`Rules ++ p)
  `($f $x)

/-- The condition, right-nested, with each folded pair expanded unless it is
the tail. -/
def renderConds (cs : Array Cond) : CommandElabM Term := do
  let mut flat : Array Term := #[]
  for h : i in [0:cs.size] do
    let isLast := i + 1 == cs.size
    match cs[i] with
    | .raw t => flat := flat.push t
    | .pred p x =>
        match foldedPair p, isLast with
        | some (a, b), false =>
            flat := flat.push (← applyPred a x)
            flat := flat.push (← applyPred b x)
        | _, _ => flat := flat.push (← applyPred p x)
  if flat.isEmpty then `(True)
  else
    let mut acc := flat[flat.size - 1]!
    for i in [1:flat.size] do
      let c := flat[flat.size - 1 - i]!
      acc ← `($c ∧ $acc)
    return acc

/-- The conjuncts a free schema variable contributes. -/
def freeConds (x : Ident) : Array Cond :=
  (schemaVar x.getId.toString).free.map (Cond.pred · x)

/-- What a matched expression contributes: the pattern it is destructured by,
the conjuncts that must lead the whole condition (an operator equation, which
ties the statement's operator to the family index), the conjuncts its schema
variables contribute, and the ones that must trail them.

`holes` writes `_` where the condition does not look — the static type, and a
field the rule does not name.

The `base`/`free` split is the paper's: a variable *under* a path pattern has
already had its location said by the pattern's `Kind`, a variable standing
under an operator has not. -/
partial def analyzePat (holes : Bool) (sc : Scope) (stx : Syntax) :
    CommandElabM (Option (Term × Array Cond × Array Cond × Array Cond)) := do
  let some view := exprView? stx | return none
  let ty := sc.tyName
  let tyPat : Term ← if holes then `(_) else `($ty)
  -- An operand of an operator pattern: a variable contributes its `free`
  -- conjuncts, anything else is matched in turn.
  let operand (e : Syntax) : CommandElabM (Term × Array Cond) := do
    match isPlainVar e with
    | some x => return (x, freeConds x)
    | none =>
        match ← analyzePat holes sc e with
        | some (p, lead, cs, tr) => return (p, lead ++ cs ++ tr)
        | none => throwErrorAt e "unsupported pattern"
  let opEq : CommandElabM (Ident × Array Cond) := do
    let some op := sc.opName
      | throwErrorAt stx "this conclusion needs the rule to declare an operator parameter"
    let opS := mkIdent `opS
    let guard : Array Cond := match sc.opGuard with
      | some g => #[Cond.raw g]
      | none => #[]
    return (opS, #[Cond.raw (← `($opS = $op))] ++ guard)
  match view with
  | .field b f =>
      let some (.var bx) := exprView? b | return none
      let kt ← kindTerm (kindOfName bx.getId)
      let fPat : Term ← if holes then `(_) else `($f)
      let pat ← `($(gen `WrappedExpr.field) $kt $tyPat $bx $fPat)
      let sch := schemaVar bx.getId.toString
      return some (pat, #[], sch.base.map (Cond.pred · bx), sch.trail.map (Cond.pred · bx))
  | .index b i =>
      let some (.var bx) := exprView? b | return none
      let some (.var ix) := exprView? i | return none
      let kt ← kindTerm (kindOfName bx.getId)
      let pat ← `($(gen `WrappedExpr.index) $kt $tyPat $bx $ix)
      let sb := schemaVar bx.getId.toString
      let si := schemaVar ix.getId.toString
      return some (pat, #[],
                   sb.base.map (Cond.pred · bx) ++ si.base.map (Cond.pred · ix),
                   sb.trail.map (Cond.pred · bx) ++ si.trail.map (Cond.pred · ix))
  | .pushPlace b =>
      let some (.var bx) := exprView? b | return none
      let pat ← `($(gen `WrappedExpr.pushPlace) $bx)
      let sch := schemaVar bx.getId.toString
      -- A push place carries no `Kind` of its own, so the receiver's location
      -- is a conjunct rather than part of the pattern.
      let kindCond : Array Cond ← match sch.kind with
        | some k => pure #[Cond.raw (← `(($bx).kind = $(← kindTerm k)))]
        | none => pure #[]
      return some (pat, #[], kindCond ++ sch.base.map (Cond.pred · bx), #[])
  | .incDec b =>
      let (opS, lead) ← opEq
      match isPlainVar b with
      | some bx =>
          let pat ← `($(gen `WrappedExpr.incDec) $opS $bx)
          return some (pat, lead, freeConds bx, #[])
      | none =>
          let some (inner, _, cs, tr) ← analyzePat holes sc b
            | throwErrorAt b "unsupported `++` target"
          return some (← `($(gen `WrappedExpr.incDec) $opS $inner), lead, cs, tr)
  | .combine a b =>
      let (opS, lead) ← opEq
      let (pa, ca) ← operand a
      let (pb, cb) ← operand b
      return some (← `($(gen `WrappedExpr.binop) $opS $pa $pb), lead, ca ++ cb, #[])
  | .fixedBinop op a b =>
      let opS := mkIdent `opS
      let oi := mkIdent (`BinOp ++ op)
      let (pa, ca) ← operand a
      let (pb, cb) ← operand b
      return some (← `($(gen `WrappedExpr.binop) $opS $pa $pb),
                   #[Cond.raw (← `($opS = $oi))], ca ++ cb, #[])
  | .unop a =>
      let (opS, lead) ← opEq
      let (pa, ca) ← operand a
      return some (← `($(gen `WrappedExpr.unop) $opS $pa), lead, ca, #[])
  | .fixedUnop op a =>
      let oi := mkIdent (`UnOp ++ op)
      let (pa, ca) ← operand a
      return some (← `($(gen `WrappedExpr.unop) $oi $pa), #[], ca, #[])
  | .ternary c t e =>
      let (pc, cc) ← operand c
      let (pt, _) ← operand t
      let (pe, _) ← operand e
      return some (← `($(gen `WrappedExpr.ternary) $pc $pt $pe), #[], cc, #[])
  | .var _ =>
      -- A Boolean literal is a pattern with nothing to say.
      let some b := boolLit? stx | return none
      let bt := mkIdent (if b then `Bool.true else `Bool.false)
      return some (← `($(gen `WrappedExpr.bool) $bt), #[], #[], #[])
  | _ => return none

/-! ## Assembly

`sol_assemble_rules` turns the declarations collected so far into the three
tables `Rules.lean` used to carry by hand, in declaration order:
`RuleName`, `ruleEffect` and `ruleNames`.  Their order is load-bearing —
`FirstStepCase` takes the first applicable rule under the block modality
`.both`, so a box twin has to precede its diamond twin — and declaration
order is the only order there now is. -/

/-- The constructors of the inductive a family is indexed by (`BinOp`,
`IncDec`, `UnOp`), in declaration order, which is the order `ruleNames` has
always listed the instances in. -/
def familyCtors (ty : Ident) : CommandElabM (Array Name) := do
  let n ← liftCoreM <| realizeGlobalConstNoOverload ty
  let .inductInfo info ← getConstInfo n
    | throwErrorAt ty "`{n}` is not an inductive type"
  return info.ctors.toArray

syntax (name := assembleRules) "sol_assemble_rules" : command

@[command_elab assembleRules]
def elabAssembleRules : CommandElab := fun _ => do
  let decls := ruleExt.getState (← getEnv)
  if decls.isEmpty then
    logWarning "no `rule` declarations to assemble"
  -- The `rule` declarations sit inside `namespace Rules`, but `RuleName` is
  -- the package's, so the inductive is declared at its own root and referred
  -- to unqualified (which resolves, `Rules` being nested in `Solidity`).
  let ruleNameDecl := mkIdent `_root_.Solidity.RuleName
  let ruleName := mkIdent `RuleName
  -- The inductive, docstrings carried.
  -- A twin pair is two constructors, box first: under the block modality
  -- both apply, and `FirstStepCase` takes whichever `ruleNames` reaches
  -- first, so the order decides which name a `⇝[.rule]` derivation pins.
  let names (d : RuleDecl) : Array Ident :=
    if d.twins then
      #[mkIdent (d.name.getId.appendAfter "Box"), mkIdent (d.name.getId.appendAfter "Diamond")]
    else #[d.name]
  let mut ctors := #[]
  for d in decls do
    for n in names d do
      let c ← match d.binder with
        | none => `(Lean.Parser.Command.ctor| $[$(d.doc):docComment]? | $n:ident)
        | some b =>
            `(Lean.Parser.Command.ctor|
                $[$(d.doc):docComment]? | $n:ident ($(b.name):ident : $(b.type):ident))
      ctors := ctors.push c
  elabCommand (← `(command|
    inductive $ruleNameDecl:ident where $ctors:ctor* deriving DecidableEq, Repr))
  -- `ruleEffect`, in the equation-compiler style the old table used, so
  -- that `simp only [Rules.ruleEffect]` keeps firing on the same `eq_N`
  -- lemmas.
  let mut alts := #[]
  for d in decls do
    let bodies := if d.twins then #[d.effect, d.effectDia.getD d.effect] else #[d.effect]
    for (n, body) in (names d).zip bodies do
      let alt ← withRef d.ref <| match d.binder with
        | none => `(Lean.Parser.Term.matchAltExpr| | .$n:ident => $body)
        | some b => `(Lean.Parser.Term.matchAltExpr| | .$n:ident $(b.name):ident => $body)
      alts := alts.push alt
  elabCommand (← `(command|
    def $(mkIdent `ruleEffect):ident :
      $ruleName:ident -> $(mkIdent `StepEffect):ident $alts:matchAlt*))
  -- `ruleNames`: every instance of every family, minus the `\choice`
  -- alternatives, in declaration order.
  let mut entries : Array Term := #[]
  for d in decls do
    if d.alternative then continue
    for n in names d do
      match d.binder with
      | none => entries := entries.push (← `(.$n:ident))
      | some b =>
          for c in ← familyCtors b.type do
            let ci := mkIdent (Name.mkSimple c.getString!)
            entries := entries.push (← `(.$n:ident .$ci:ident))
  elabCommand (← `(command|
    def $(mkIdent `ruleNames):ident : List $ruleName:ident := [$entries,*]))
  -- The twin pairs, for `CandidateStep.twins_box_first`.
  let mut pairs : Array Term := #[]
  for d in decls do
    if d.twins then
      let ns := names d
      pairs := pairs.push (← `((.$(ns[0]!):ident, .$(ns[1]!):ident)))
  elabCommand (← `(command|
    /-- The box/diamond twin pairs, box first. -/
    def $(mkIdent `twinPairs):ident : List ($ruleName:ident × $ruleName:ident) :=
      [$pairs,*]))

/-! ## The `rule` command -/

/-- `from t1, t2` as a `KeyOrigin` term, or `none` for a Lean-only rule. -/
def originOf? (stx : Option Syntax) : CommandElabM (Option Term) := do
  let some stx := stx | return none
  let arg := (args stx)[0]!
  if arg.getKind == ``Lean.Parser.Term.paren || arg[0].getAtomVal == "(" then
    return some ⟨arg[1]⟩
  let names := arg.getSepArgs
  if names.size == 1 then
    let t := mkIdent (`KeyTaclet ++ (names[0]!.getId))
    return some (← `($(gen `KeyOrigin.taclet) $t))
  let ts : Array Term ← names.mapM fun n => do
    let t := mkIdent (`KeyTaclet ++ n.getId)
    `($t:ident)
  return some (← `($(gen `KeyOrigin.merged) [$ts,*]))

/-- Wrap an effect in its provenance, so that the `\heuristics` of the
taclets `from` names are taken from `KeyTaclets.lean` rather than repeated
(`Rules.withOrigin`). -/
def withOriginOf (o : Option Term) (e : Term) : CommandElabM Term := do
  match o with
  | none => return e
  | some o => `($(gen `Rules.withOrigin) $o <| $e)


/-- The analysis of a conclusion: which builder carries it, what its
parameters are called, which one is destructured, and what the schema
variables say. -/
structure Concl where
  builder : Name
  params : Array Ident
  /-- The destructured parameter: index, `cond` pattern, `goals` pattern,
  and whether the scrutinee is the place coercion `(lhs : $(gen `WrappedExpr))` —
  the case where the `goals` match has to take the `PlaceExpr` apart as
  `⟨PAT, _⟩`, because the condition reaches it as an unreduced beta-redex
  (`StepEffect`'s docstring, "two wrinkles").

  The `cond` pattern is absent where the condition already matches on its own:
  an `Option` parameter's conjunct *is* a match, and wrapping it in a second
  one would say the same thing twice. -/
  destruct : Option (Nat × Option Term × Term × Bool) := none
  conds : Array Cond := #[]
  paramPats : Array (Ident × Option Syntax) := #[]
  /-- An extra leading `CaseMode` argument, as `popEffect` takes. -/
  modeFirst : Bool := false
  /-- The receiver of a matched push *place*.  `WrappedExpr.pushPlace` carries
  no assignability invariant of its own, so a goal that pushes through it has
  to reuse the witness the matched `PlaceExpr` came with. -/
  placeBase : Option Ident := none
  /-- The *statement's* operator, where the conclusion binds one.  A goal
  must use this and not the family index: the two are equal only under the
  condition's first conjunct, so `compoundGoals` is handed the operator the
  statement carries, exactly as the hand-written arms did. -/
  stmtOp : Option Ident := none

/-- One side of a two-sided conclusion: its parameter name, the conjuncts that
must lead the condition, the conjuncts it contributes, and — when it is a path
or an operator node — the pattern it is matched by.

`kindSpelling` asks for the *target* spelling of a variable's location,
`PlaceExpr.kind x = Kind.k ∧ <base>`, rather than its `free` conjuncts.  A
push or pop receiver always wants it; an assignment target wants it only where
the schema says so, because `Rules.lean` keeps `isMemory mv` and
`mv.kind = Kind.memory` as distinct terms. -/
private def side (sc : Scope) (fallback : Name) (stx : Syntax)
    (isPlace : Bool := false) (forceKindSpelling : Bool := false) :
    CommandElabM (Ident × Array Cond × Array Cond ×
      Option (Term × Term × Array Cond)) := do
  match (if (boolLit? stx).isSome then none else isPlainVar stx) with
  | some x =>
      let sch := schemaVar x.getId.toString
      match isPlace && (forceKindSpelling || sch.placeKind), sch.kind with
      | true, some k =>
          let kt ← kindTerm k
          return (x, #[], #[Cond.raw (← `($(gen `PlaceExpr.kind) $x = $kt))] ++
                       sch.base.map (Cond.pred · x), none)
      | _, _ => return (x, #[], freeConds x, none)
  | none =>
      let some (condPat, lead, cs, trail) ← analyzePat true sc stx
        | throwErrorAt stx "unsupported conclusion shape"
      let some (goalPat, _, _, _) ← analyzePat false sc stx
        | throwErrorAt stx "unsupported conclusion shape"
      return (mkIdent fallback, lead, cs, some (condPat, goalPat, trail))

/-- Does this expression bind an operator the goals must read?  A conclusion
that matched `⊕`, `⊖` or `++` carries the *statement's* operator, and a goal
has to use that and not the family index. -/
def bindsStmtOp (stx : Syntax) : Bool :=
  match exprView? stx with
  | some (.combine _ _) | some (.unop _) | some (.incDec _) => true
  | some (.fixedBinop _ _ _) => true
  | _ => false

/-- The `Option` parameter of a declaration's initialiser or a push's value,
and the conjuncts it contributes.  The condition names the parameter, not the
expression under it: which shape it is is exactly what the condition says. -/
private def optionCond (sc : Scope) (vp : Ident) (arg : Option Syntax) :
    CommandElabM (Array Cond × Option (Term × Term × Array Cond)) := do
  let some e := arg
    | return (#[Cond.raw (← `($vp = none))], none)
  match isPlainVar e with
  | some x =>
      let cs := freeConds x
      if cs.isEmpty then
        return (#[Cond.raw (← `(Option.isSome $vp))],
                some (← `(some _), ← `(some $x), #[]))
      let inner ← renderConds cs
      return (#[Cond.raw (← `(match $vp:ident with | some $x:ident => $inner | none => False))],
              some (← `(some _), ← `(some $x), #[]))
  | none =>
      let some (condPat, lead, cs, trail) ← analyzePat true sc e
        | throwErrorAt e "unsupported initialiser"
      let some (goalPat, _, _, _) ← analyzePat false sc e
        | throwErrorAt e "unsupported initialiser"
      let inner ← renderConds (lead ++ cs ++ trail)
      return (#[Cond.raw (← `(match $vp:ident with | some $condPat => $inner | _ => False))],
              some (← `(some $condPat), ← `(some $goalPat), #[]))

/-- The conclusion of a rule. -/
def analyzeConcl (sc : Scope) (stx : Syntax) : CommandElabM Concl := do
  let some view := stmtView? stx
    | throwErrorAt stx s!"unsupported conclusion (kind {stx.getKind})"
  let two (builder : Name) (a b : Syntax) (aPlace bPlace : Bool)
      (extraLead : Array Cond := #[]) (leadParams : Array Ident := #[]) :
      CommandElabM Concl := do
    let (ap, alead, ac, apat) ← side sc `lhs a (isPlace := aPlace)
    let (bp, blead, bc, bpat) ← side sc `rhs b (isPlace := bPlace)
    if apat.isSome && bpat.isSome then
      throwErrorAt stx "a rule matches at most one side of its conclusion"
    let n := leadParams.size
    let params := leadParams ++ #[ap, bp]
    let trail := (apat.map (·.2.2)).getD ((bpat.map (·.2.2)).getD #[])
    let destruct : Option (Nat × Option Term × Term × Bool) :=
      match apat, bpat with
      | some (c, g, _), _ => some (n, some c, g, aPlace)
      | _, some (c, g, _) => some (n + 1, some c, g, bPlace)
      | _, _ => none
    let opS := mkIdent `opS
    let placeBase : Option Ident :=
      if aPlace && apat.isSome then
        match exprView? a with
        | some (.pushPlace b) => isPlainVar b
        | _ => none
      else none
    return { builder := builder, params := params
             destruct := destruct, placeBase := placeBase
             conds := alead ++ blead ++ extraLead ++ ac ++ bc ++ trail
             paramPats := #[(ap, if apat.isSome then some a else none),
                            (bp, if bpat.isSome then some b else none)]
             stmtOp := if bindsStmtOp a || bindsStmtOp b then some opS else none }
  let one (builder : Name) (a : Syntax) (aPlace : Bool)
      (placeKind : Bool := false) : CommandElabM Concl := do
    let (ap, alead, ac, apat) ← side sc `target a (isPlace := aPlace)
      (forceKindSpelling := placeKind)
    let opS := mkIdent `opS
    return { builder := builder, params := #[ap]
             destruct := apat.map fun (c, g, _) => (0, some c, g, aPlace)
             conds := alead ++ ac ++ (apat.map (·.2.2)).getD #[]
             paramPats := #[(ap, if apat.isSome then some a else none)]
             stmtOp := if bindsStmtOp a then some opS else none }
  match view with
  | .delete t => one `deleteEffect t true
  | .assign lhs rhs =>
      -- `res = fn(args)`: the one conclusion whose right-hand side is a call
      -- to a *parameter*, which is how a call statement is written.
      match isPlainVar lhs, callHead? rhs with
      | some res, some (_, as) =>
          if h : as.size = 1 then
            if let some argv := isPlainVar as[0] then
              if let some (.call fnI _) := exprView? rhs then
                return { builder := `callEffect, params := #[res, fnI, argv]
                         paramPats := #[(res, none), (fnI, none), (argv, none)] }
      | _, _ => pure ()
      two `assignEffect lhs rhs true false
  | .compound lhs rhs => do
      let some op := sc.opName
        | throwErrorAt stx "`⊕=` needs the rule to declare a `BinOp` parameter"
      let opS := mkIdent `opS
      let lead := #[Cond.raw (← `($opS = $op)),
                    Cond.raw (← `($(gen `BinOp.hasCompoundAssign) $opS = true))]
      let c ← two `compoundAssignEffect lhs rhs true false lead #[opS]
      return { c with stmtOp := some opS }
  | .expr e =>
      match callHead? e with
      | some ("delete", #[t]) => one `deleteEffect t true
      | some ("pushAssign", #[t, v]) => do
          let some tp := isPlainVar t | throwErrorAt t "a push-assign target is a variable"
          let some vp := isPlainVar v | throwErrorAt v "a push-assign value is a variable"
          return { builder := `pushAssignEffect, params := #[tp, vp]
                   paramPats := #[(tp, none), (vp, none)] }
      | some ("pushFieldAssign", #[t, f, v]) => do
          let some tp := isPlainVar t | throwErrorAt t "a push-assign target is a variable"
          let some fp := isPlainVar f | throwErrorAt f "a push-assign field is a variable"
          let some vp := isPlainVar v | throwErrorAt v "a push-assign value is a variable"
          return { builder := `pushFieldAssignEffect, params := #[tp, fp, vp]
                   paramPats := #[(tp, none), (fp, none), (vp, none)] }
      | _ => one `exprEffect e false
  | .require c => one `requireEffect c false
  | .assert c => one `assertEffect c false
  | .revert => return { builder := `revertEffect, params := #[], conds := #[] }
  | .pop t => one `popEffect t true (placeKind := true)
  | .transfer r a => two `transferEffect r a false false
  | .aliasDecl ty name src => do
      let some sp := isPlainVar src | throwErrorAt src "an alias source is a variable"
      return { builder := `storagePlaceAliasEffect, params := #[ty, name, sp]
               paramPats := #[(ty, none), (name, none), (sp, none)] }
  | .push target value => do
      let (tp, tlead, tc, tpat) ← side sc `target target (isPlace := true)
        (forceKindSpelling := true)
      let vp := mkIdent `value
      let (vc, vpat) ← optionCond sc vp value
      return { builder := `pushEffect, params := #[tp, vp]
               destruct := (tpat.map fun (c, g, _) => (0, some c, g, true)) <|>
                 (vpat.map fun (_, g, _) => (1, none, g, false))
               conds := tlead ++ tc ++ vc
               paramPats := #[(tp, if tpat.isSome then some target else none),
                              (vp, none)] }
  | .decl kind ty name init => do
      let builder := match kind with
        | `storage => `storageDeclEffect
        | `memory => `memoryDeclEffect
        | _ => `stackDeclEffect
      let initP := mkIdent `init
      let (cs, ipat) ← optionCond sc initP init
      return { builder := builder, params := #[ty, name, initP]
               destruct := ipat.map fun (_, g, _) => (2, none, g, false)
               conds := cs
               paramPats := #[(ty, none), (name, none), (initP, none)] }
  | .ite c thn els => do
      let (cp, clead, cc, cpat) ← side sc `cond c
      return { builder := `iteEffect, params := #[cp, thn, els]
               destruct := cpat.map fun (cc', g, _) => (0, some cc', g, false)
               conds := clead ++ cc ++ (cpat.map (·.2.2)).getD #[]
               paramPats := #[(cp, if cpat.isSome then some c else none),
                              (thn, none), (els, none)] }
  | _ => throwErrorAt stx "unsupported conclusion"

/-! ### Goals

The goal lines are read back into the combinators `Rules.lean` names, so a
declaration produces the term the hand-written arm produced: `unfoldGoal`
for a rewriting rule, `terminalGoal` for an unguarded update, `splitGoals`
for KeY's guarded pair, `assertGoals` and `revertGoals` for the two shapes
that are obligations rather than programs.  Anything else becomes a literal
`List RuleGoal`, which is what KeY's own goal list is. -/

/-- `Rules.CaseMode` for a goal's modality marker. -/
def modeTerm (m : Name) : CommandElabM Term := do
  let i := mkIdent (`CaseMode ++ m)
  `($i:ident)

/-- The updates and residual of a result. -/
def transResult (sc : Scope) (r : ResultView) : CommandElabM Term := do
  match r with
  | .reverting => `($(gen `RuleResidual.reverting))
  | .escape b => `($(gen `RuleResidual.prog) [] $b)
  | .prog upds stmts =>
      let us ← upds.mapM (transUpd sc)
      let b ← transBlock sc stmts
      `($(gen `RuleResidual.prog) [$us,*] $b)
  | .obligation upds φ =>
      let us ← upds.mapM (transUpd sc)
      `($(gen `RuleResidual.obligation) [$us,*] $(← transFormula sc φ))

/-- A goal as a `RuleGoal` record. -/
def transGoalRecord (sc : Scope) (g : GoalView) (prems : Array Term)
    (prev : Option Syntax) : CommandElabM Term := do
  let some rv := resultView? g.result
    | throwErrorAt g.result "unsupported goal result"
  let res ← transResult sc rv
  let φ ← match g.guardStx, g.isElse, prev with
    | some f, _, _ => transFormula sc f
    | none, true, some p => do `($(gen `SideFormula.neg) $(← transFormula sc p))
    | _, _, _ => `($(gen `SideFormula.const) true)
  let label : Term := Syntax.mkStrLit (g.label.getD "")
  let mode ← modeTerm (g.mode.getD `both)
  `({ label := $label, mode := $mode,
      guard := { premises := [$prems,*], formula := $φ },
      residual := $res })

/-- The `goals` of a rule, as the combinator its shape names. -/
def transGoals (sc : Scope) (goals : Array GoalView) (premStx : Array Syntax) :
    CommandElabM Term := do
  let prems ← premStx.mapM (transPremise sc)
  let plain (g : GoalView) : Bool :=
    g.label.isNone && g.mode.isNone && g.guardStx.isNone && !g.isElse
  -- One goal: a rewriting rule, or an unguarded update.
  if h : goals.size = 1 then
    let g := goals[0]
    if plain g then
      if let some (.prog upds stmts) := resultView? g.result then
        if upds.isEmpty then
          return (← `($(gen `Rules.unfoldGoal) <| $(← transBlock sc stmts)))
        if stmts.isEmpty then
          let us ← upds.mapM (transUpd sc)
          -- `{ bump(e) || v := e }` is the increment/decrement pair, which
          -- KeY writes as one parallel update and `Rules` names.
          if us.size == 2 && (premStx.isEmpty) then
            if let some (.prog _ _) := resultView? g.result then
              if (callHead? (args upds[0]!)[0]!).map (·.1) == some "bump" then
                let some (_, bargs) := callHead? (args upds[0]!)[0]!
                  | pure ()
                let wb := args upds[1]!
                if wb.size == 2 && sameSyntax bargs[0]! wb[1]! then
                  let e ← transExpr sc false bargs[0]!
                  let v ← transExpr sc true wb[0]!
                  return (← `($(gen `Rules.incDecGoals) $v $e))
          return (← `($(gen `Rules.terminalGoal) [$us,*]))
  -- Two goals: the guarded pair, the assert pair, or the revert pair.
  if h : goals.size = 2 then
    let g1 := goals[0]
    let g2 := goals[1]
    -- `revert();`: KeY's `\replacewith(true)` / `\replacewith(false)`.
    if g1.mode == some `box && g2.mode == some `diamond then
      if let (some (.obligation u1 f1), some (.obligation u2 f2)) :=
          (resultView? g1.result, resultView? g2.result) then
        if u1.isEmpty && u2.isEmpty && f1.getKind == ``fmTop && f2.getKind == ``fmBot then
          return (← `($(gen `Rules.revertGoals)))
    -- `assert(se);`: the "Holds"/"Violated" pair, whose second goal is an
    -- obligation and *not* a revert.
    if g1.label == some "Holds" && g2.label == some "Violated" then
      if let some f := g1.guardStx then
        if f.getKind == ``fmAtom then
          return (← `($(gen `Rules.assertGoals) $(← transExpr sc false (args f)[0]!)))
    -- The guarded split.
    if g2.isElse then
      if let (some (.prog upds stmts), some .reverting) :=
          (resultView? g1.result, resultView? g2.result) then
        if stmts.isEmpty then
          let some f := g1.guardStx
            | throwErrorAt g1.ref "a split's first goal needs a guard"
          let us ← upds.mapM (transUpd sc)
          return (← `($(gen `Rules.splitGoals) $(← transFormula sc f) [$prems,*] [$us,*]))
  -- Otherwise: the goal list itself, as KeY writes it.
  let mut out : Array Term := #[]
  let mut prev : Option Syntax := none
  for g in goals do
    out := out.push (← transGoalRecord sc g prems prev)
    if g.guardStx.isSome then prev := g.guardStx
  `([$out,*])

/-- The scope a rule's goals are read in.

Beyond the condition's parameters a goal may name three things the conclusion
introduced: a declaration's `Option` initialiser or a push's value — written as
the *parameter*, because the condition has already said which shape it is —
the branches of a matched `if`, which are whole blocks, and the receiver of a
matched push place, which comes with the assignability witness the matched
`PlaceExpr` was built from. -/
def goalScope (concl : Concl) (tyName : Ident) (familyOp : Option Ident)
    (hass : Ident) : Scope := Id.run do
  let params := concl.params
  let declKind : Option Name := match concl.builder with
    | `storageDeclEffect | `storagePlaceAliasEffect => some `storage
    | `memoryDeclEffect => some `memory
    | `stackDeclEffect => some `stack
    | _ => none
  let mut binds : Array (Name × Binding) := #[]
  if concl.builder == `iteEffect then
    binds := binds.push (params[1]!.getId, .blockParam)
    binds := binds.push (params[2]!.getId, .blockParam)
  if let some b := concl.placeBase then
    binds := binds.push (b.getId, .placeOf hass)
  if let some kind := declKind then
    binds := binds.push (params[1]!.getId, .declared kind params[0]!)
  -- The place alias's initialiser is not optional, so it has no such parameter.
  let optionParam : Option Ident :=
    if concl.builder == `pushEffect then some params[1]!
    else if declKind.isSome && concl.builder != `storagePlaceAliasEffect then
      some params[2]!
    else none
  return { params := concl.paramPats, tyName := tyName, binds := binds
           opName := concl.stmtOp <|> familyOp, optionParam := optionParam }

/-- Every identifier a term mentions. -/
partial def identsOf (stx : Syntax) : Array Name :=
  match stx with
  | .ident _ _ n _ => #[n]
  | .node _ _ as => as.foldl (fun acc a => acc ++ identsOf a) #[]
  | _ => #[]

/-- The names the conclusion's *pattern* binds and nothing else does: the
schema variables under the matched expression, the fields it names, and the
type binder — minus the parameters, which are in scope either way.

Lean's lexer reads `sp.fld` as one identifier, so a dotted name stands for its
components here as it does everywhere else in this module. -/
def patternBinders (conclStx : Syntax) (tyName : Ident) (params : Array Ident) :
    Array Name :=
  let raw := (identsOf conclStx).flatMap fun n =>
    (n.components.map (Name.mkSimple ·.toString)).toArray
  (raw.push tyName.getId).filter fun n => !params.any (·.getId == n)

def mentionsAny (t : Syntax) (names : Array Name) : Bool :=
  (identsOf t).any (names.contains ·)

/-- The declarative form: the conclusion, the goals, and the conditions the
schema variables do not carry. -/
@[command_elab Solidity.RuleSyntax.ruleDecl]
def elabRuleDecl : CommandElab := fun stx => do
  -- `args` drops the tokens, so the accessors below survive a token split:
  -- doc?, name, twins?, alternative?, binder?, from?, conclusion, goals,
  -- after?, where?.
  let a := args stx
  let doc : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    (group? a[0]!).map fun g => ⟨g[0]⟩
  let name : Ident := ⟨a[1]!⟩
  let twins := (group? a[2]!).isSome
  let alternative := (group? a[3]!).isSome
  let binderStx := (group? a[4]!).map fun g => (args g[0])
  let binder : Option RuleBinder :=
    binderStx.map fun ga => { name := ⟨ga[0]!⟩, type := ⟨ga[1]!⟩ }
  -- `(op : BinOp | g)`: the guard is a conjunct, not a binder.
  let opGuard : Option Term :=
    binderStx.bind fun ga => (group? ga[2]!).map fun g => ⟨(args g)[0]!⟩
  let origin ← originOf? ((group? a[5]!).map fun g => g[0])
  let conclStx := a[6]!
  let goalsStx := a[7]!
  let premStx : Array Syntax :=
    match group? a[8]! with
    | some g => g[1].getSepArgs
    | none => #[]
  let whereStx := (group? a[9]!).map fun g => g[0]
  -- The scope the conclusion is read in.
  let tyName := mkIdent `ty
  let sc0 : Scope := { tyName := tyName, opName := binder.map (·.name)
                       opGuard := opGuard }
  let concl ← analyzeConcl sc0 conclStx
  -- The condition: the schema variables, then whatever `where` adds — or,
  -- when the spelling is irregular, whatever `where cond :=` says outright.
  let mut conds := concl.conds
  let mut condOverride : Option Term := none
  if let some w := whereStx then
    let arg := (args w)[0]!
    if arg[0].getAtomVal == "cond" then
      condOverride := some ⟨arg[2]⟩
    else
      for t in arg.getSepArgs do
        conds := conds.push (Cond.raw ⟨t⟩)
  let condBody ← match condOverride with
    | some t => pure t
    | none => renderConds conds
  -- The condition matches the statement's shape, `_` where it does not look,
  -- and falls through to `False`: the arm the match compiler keeps is what
  -- makes a `goals` arm's proof reduce to `False` everywhere else.
  let condBody ← match concl.destruct, condOverride with
    | some (idx, some condPat, _, placeCoerced), none =>
        let p := concl.params[idx]!
        let scrut : Term ←
          if placeCoerced then `(($p : $(gen `WrappedExpr))) else `($p)
        `(match $scrut:term with | $condPat => $condBody | _ => False)
    | _, _ => pure condBody
  let params := concl.params
  -- The goals read the *statement's* operator where the conclusion binds
  -- one; the condition's first conjunct is what ties it to the family index.
  let hass := mkIdent `hass
  let scope := goalScope concl tyName (binder.map (·.name)) hass
  -- The goals.
  let goalViews : Array GoalView ←
    if goalsStx.getKind == ``goalsOne then
      let some rv := resultView? goalsStx[0]
        | throwErrorAt goalsStx "unsupported goal"
      let _ := rv
      pure #[{ result := goalsStx[0], ref := goalsStx }]
    else
      goalsStx[0].getArgs.mapM fun g => do
        let some v := goalView? g | throwErrorAt g "unsupported goal"
        pure v
  let isUnfold := goalViews.any fun g =>
    match resultView? g.result with
    | some (.prog _ stmts) => !stmts.isEmpty
    | some (.escape _) => true
    | _ => false
  -- A rule whose residual is a term reads the condition proof, so the proof
  -- is bound rather than dropped.
  let readsProof := goalViews.any fun g =>
    match resultView? g.result with | some (.escape _) => true | _ => false
  -- `cond`, and — where the rule rewrites — `goals` re-matching the same
  -- scrutinee with the condition proof as a second discriminant.
  let condFn ← `(fun $params:ident* => $condBody)
  let hName := mkIdent `h
  let unfoldBody : CommandElabM Term := do
    if goalsStx.getKind == ``goalsOne || goalViews.size == 1 then
      match resultView? goalViews[0]!.result with
      | some (.prog _ stmts) => transBlock scope stmts
      | some (.escape b) => pure b
      | _ => transGoals scope goalViews premStx
    else transGoals scope goalViews premStx
  let goalsFn ←
    match concl.destruct, isUnfold with
    | some (idx, _, goalPat, placeCoerced), true =>
        let p := params[idx]!
        let inner ← unfoldBody
        -- The match is there to *name* the pattern's binders.  Where the
        -- residual never reaches for one — because it writes the matched
        -- expression whole, which denotes the parameter — there is nothing to
        -- name, and the hand-written arm did not match either.
        let bound := patternBinders conclStx tyName params
        if !readsProof && !(mentionsAny inner bound) then
          `(fun $params:ident* _ => $(gen `Rules.unfoldGoal) <| $inner)
        else
        let alt ←
          if placeCoerced then
            `(Lean.Parser.Term.matchAltExpr| | ⟨$goalPat, $hass⟩, _ => $inner)
          else
            `(Lean.Parser.Term.matchAltExpr| | $goalPat, _ => $inner)
        `(fun $params:ident* $hName:ident => $(gen `Rules.unfoldGoal) <|
            match $p:ident, $hName:ident with $alt:matchAlt)
    | _, true =>
        let inner ← unfoldBody
        if readsProof then
          `(fun $params:ident* $hName:ident => $(gen `Rules.unfoldGoal) <| $inner)
        else `(fun $params:ident* _ => $(gen `Rules.unfoldGoal) <| $inner)
    | _, _ =>
        let body ← transGoals scope goalViews premStx
        if readsProof then `(fun $params:ident* $hName:ident => $body)
        else `(fun $params:ident* _ => $body)
  let builder := mkIdent (`Rules ++ concl.builder)
  -- Where the modality is an argument of the builder it is passed; elsewhere
  -- a twin is the same effect under `withMode`, which is how `Rules.lean`
  -- has always written the twelve pairs.
  let mkEffect (mode : Option Name) : CommandElabM Term := do
    let m ← modeTerm (mode.getD `both)
    let base ←
      if concl.builder == `revertEffect then
        `($builder $m $(← transGoals scope goalViews premStx))
      else if concl.builder == `popEffect then `($builder $m $condFn $goalsFn)
      else
        let e ← `($builder $condFn $goalsFn)
        match mode with
        | none => pure e
        | some _ => `($(gen `Rules.withMode) $m <| $e)
    withOriginOf origin base
  let effect ← mkEffect (if twins then some `box else none)
  let effectDia ← if twins then some <$> mkEffect (some `diamond) else pure none
  pushRule { ref := stx, name := name, doc := doc, binder := binder
             effect := effect, effectDia := effectDia
             twins := twins, alternative := alternative }

end Solidity.RuleSyntax
