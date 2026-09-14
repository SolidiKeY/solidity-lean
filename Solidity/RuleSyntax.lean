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

**A residual is a program, not a list of constructors.** `T rv = e` is the
value freeze, `T storage sp = nsp` the path capture, and a later `sp.fld`
is the alias read-back — the three statements the paper writes as
`T_e se = e; T_nsp storage sp = nsp; sp.fld = se;`.

**Twins are one declaration.** `twins` generates the `Box` and `Diamond`
constructors, box first, and the entry in `twinPairs` that
`CandidateStep.twins_box_first` checks.

**A family is one declaration.** `(op : BinOp)` generates the constructor
parameter, the `op = opR ∧ …` head conjuncts, and all fourteen `ruleNames`
entries.

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
syntax (name := stPushValue) rule_expr noWs ".push(" rule_expr ")" : rule_stmt
syntax (name := stPushEmpty) rule_expr noWs ".push()" : rule_stmt
syntax (name := stPop) rule_expr noWs ".pop()" : rule_stmt
syntax (name := stTransfer) rule_expr noWs ".transfer(" rule_expr ")" : rule_stmt
/-- `if (nse) thn else els` — the branches are schematic blocks. -/
syntax (name := stIte) "if" " (" rule_expr ") " ident " else " ident : rule_stmt
/-- A bare expression statement, and — through the application form — the
statements that read as calls: `require(se)`, `assert(se)`, `revert()`,
`delete(sp.fld)`. -/
syntax (name := stExpr) rule_expr : rule_stmt
/-- Escape to a Lean term of type `Stmt`. -/
syntax (name := stEscape) "‹" term "›" : rule_stmt

/-! An update, a term and a side formula are all `rule_expr`; only the
update's `:=` and the formula's connectives need syntax of their own. -/

declare_syntax_cat rule_upd
/-- `storage := save(storage, p, t)`, `v := se`, `lsv := path(sp)`. -/
syntax (name := updAssign) rule_expr " := " rule_expr : rule_upd
/-- `havoc`, `bump(e)`, `transfer(sadr, se)`, `alloc(T, mv)`. -/
syntax (name := updBare) rule_expr : rule_upd

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
syntax (name := ruleDecl) (docComment)? "sol_rule " ident (&" twins")? (&" alternative")?
  (" (" ident " : " ident ")")? (ruleFrom)? " : "
  "<[" rule_stmt "]>" " ⇝ " rule_goals
  (&"after" rule_expr,+)? (ruleWhere)? : command

/-- The opaque form: the effect is given as a term.  For the rules whose
condition is a bespoke predicate, or whose goals consume the condition proof
— the handful the schema-variable convention cannot reach. -/
syntax (name := ruleOpaque) (docComment)? "sol_rule " ident (&" twins")? (&" alternative")?
  (" (" ident " : " ident ")")? (ruleFrom)? " := " term : command

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
  | "nse" => { free := #[`isComplex] }
  | "v" => { free := #[`isStack] }
  | "lv" => { free := #[`isStackVar] }
  | "sp" => { kind := some `storage, free := #[`isSp], base := #[`isSimple] }
  | "nsp" => { kind := some `storage, free := #[`isStorage, `isComplex],
               base := #[`isComplex] }
  | "gsp" => { kind := some `storage, free := #[`isGlobal] }
  | "lsv" => { kind := some `storage, free := #[`isLocal] }
  | "arr" => { kind := some `storage, base := #[`isSimple], trail := #[`isArray] }
  | "map" => { kind := some `storage, base := #[`isSimple], trail := #[`isMapping] }
  | "i" => { free := #[`isSimple], base := #[`isSimple] }
  | "mv" => { kind := some `memory, free := #[`isMv], base := #[`isSimple] }
  | "nmp" => { kind := some `memory, free := #[`isMemory, `isComplex],
               base := #[`isComplex] }
  | "sadr" => { free := #[`isSimple] }
  | "nadr" => { free := #[`isComplex] }
  | "nlhs" => { free := #[`isStorage, `isComplex] }
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
  /-- A value the conditional freeze bound (`Rules.freezeRhs`'s lambda). -/
  | frozen (v : Ident)
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
  | escape (t : Term)

/-- Split a dotted identifier.  Lean's lexer reads `sp.fld` as **one**
identifier, so the `p.fld` production never fires on it; the components are
recovered here instead, exactly as `SoliditySyntax.expandSolPathExpr` does
for the `sol!` grammar. -/
def dottedParts (x : Ident) : List String :=
  x.getId.components.map (·.toString)

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
  else if stx.isOfKind ``exprCall then some (.call ⟨a[0]!⟩ a[1]!.getSepArgs)
  else if stx.isOfKind ``exprCombine then some (.combine a[0]! a[1]!)
  else if stx.isOfKind ``exprEscape then some (.escape ⟨a[0]!⟩)
  else none

/-- The head of an application, if the expression is one. -/
def callHead? (stx : Syntax) : Option (String × Array Syntax) :=
  match exprView? stx with
  | some (.call f as) => some (f.getId.toString, as)
  | _ => none

/-- The head identifier of a path expression: the schema variable the whole
path hangs off, and so the name that decides its kind. -/
partial def headName (stx : Syntax) : Name :=
  match exprView? stx with
  | some (.var x) => x.getId
  | some (.field b _) | some (.index b _) | some (.pushPlace b)
  | some (.incDec b) => headName b
  | _ => Name.anonymous

/-- `Kind.storage` / `Kind.memory` / `Kind.stack` as a term. -/
def kindTerm (k : Name) : CommandElabM Term := do
  let i := mkIdent (`Kind ++ k)
  `($i:ident)

/-- The data location a schema name forces, defaulting to the stack. -/
def kindOfName (n : Name) : Name :=
  (schemaVar n.toString).kind.getD `stack

/-- The `Rules` constant naming the scratch alias a capture binds, and where
it lives.  Five fixed names, where KeY generates fresh ones — see
`Rules.lean`'s fresh-name conventions. -/
def scratchOf (n : Name) : Option (Name × Name) :=
  match stemOf n.toString with
  | "sp" => some (`storagePathAliasName, `storage)
  | "mv" => some (`memoryPathAliasName, `memory)
  | "pv" => some (`valueAliasName, `stack)
  | "rv" => some (`rhsValueAliasName, `stack)
  | "idx" => some (`indexAliasName, `stack)
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
  | .combine _ _ => throwErrorAt stx "`⊕` is a term, not a program expression"
  | .var x =>
      match sc.find? x.getId with
      | some (.frozen v) => return v
      | some (.scratch c k src) =>
          let kt ← kindTerm k
          let ci := mkIdent (`Rules ++ c)
          if asPlace then `($(gen `Rules.aliasPlace) $kt ($src).ty $ci)
          else match stemOf x.getId.toString with
            | "pv" => `($(gen `Rules.stackValueAlias) $src)
            | "rv" => `($(gen `Rules.rhsValueAlias) $src)
            | "idx" => `($(gen `Rules.indexAlias) $src)
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
          let kt ← kindTerm (kindOfName (headName b))
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

/-- A `rule_expr` as a `Rules.Sym`. -/
def transSym (sc : Scope) (stx : Syntax) : CommandElabM Term := do
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
    | some ("alloc", as) =>
        let some (.var nm) := exprView? as[1]!
          | throwErrorAt e "`alloc` takes a type and a name"
        if h : as.size = 3 then
          `($(gen `UpdElem.memDecl) $(sc.tyName) $nm (some $(← transExpr sc false as[2])))
        else `($(gen `UpdElem.memDecl) $(sc.tyName) $nm none)
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
    match component, callHead? rhs with
    | some "storage", some ("save", #[p, t]) =>
        `($(gen `UpdElem.storage) ($(gen `StorageUpd.save) $(← transExpr sc false p) $(← transSym sc t)))
    | some "storage", some ("copy", #[p, s]) =>
        `($(gen `UpdElem.storage) ($(gen `StorageUpd.copy) $(← transExpr sc false p) $(← transExpr sc false s)))
    | some "storage", some ("copyMem", #[p, s]) =>
        `($(gen `UpdElem.storage) ($(gen `StorageUpd.copyFromMem) $(← transExpr sc false p) $(← transExpr sc false s)))
    | some "storage", some ("push", as) =>
        let arr ← transExpr sc false as[0]!
        if h : as.size = 2 then
          `($(gen `UpdElem.storage) ($(gen `StorageUpd.push) $arr (some $(← transExpr sc false as[1]))))
        else `($(gen `UpdElem.storage) ($(gen `StorageUpd.push) $arr none))
    | some "storage", some ("pushSlot", #[p]) =>
        `($(gen `UpdElem.storage) ($(gen `StorageUpd.pushPlace) $(← transExpr sc false p)))
    | some "storage", some ("pop", #[p]) =>
        `($(gen `UpdElem.storage) ($(gen `StorageUpd.pop) $(← transExpr sc false p)))
    | some "storage", some ("clear", #[p]) =>
        `($(gen `UpdElem.storage) ($(gen `StorageUpd.clear) $(← transExpr sc false p)))
    | some "memory", some ("write", #[p, t]) =>
        `($(gen `UpdElem.heap) ($(gen `HeapUpd.write) $(← transExpr sc false p) $(← transSym sc t)))
    | some "memory", some ("writeRef", #[p, s]) =>
        `($(gen `UpdElem.heap) ($(gen `HeapUpd.writeRef) $(← transExpr sc false p) $(← transExpr sc false s)))
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
  | expr (e : Syntax)
  | escape (t : Term)
  deriving Inhabited

/-- A `rule_expr` node for a bare schema variable. -/
def varNode (x : Ident) : Syntax := mkNode ``exprVar #[x]

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
  else if k == ``stExpr then
    -- `sp.pop()`, `arr.push(se)`, `sadr.transfer(se)`: one identifier to the
    -- lexer, a method call here.
    match callHead? a[0]! with
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

/-- One residual statement, and the scope it leaves behind: a capture binds
its scratch alias for the statements that follow. -/
def transStmt (sc : Scope) (stx : Syntax) : CommandElabM (Term × Scope) := do
  let some view := stmtView? stx
    | throwErrorAt stx "unsupported rule statement"
  match view with
  | .escape t => return (t, sc)
  | .decl kind _ty name init =>
      let ctor := match kind with
        | `storage => mkIdent `Stmt.storageDecl
        | `memory => mkIdent `Stmt.memoryDecl
        | _ => mkIdent `Stmt.stackDecl
      let some initStx := init
        | return (← `($ctor $(sc.tyName) $name none), sc)
      let src ← transExpr sc false initStx
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
            | `rhsValueAliasName => `Rules.captureRhsValue
            | `indexAliasName => `Rules.captureIndex
            | _ => `Rules.captureStackValue
          let h := mkIdent helper
          return (← `($h $src), sc.withBind name.getId (.scratch c k src))
      | _, _ => return (← `($ctor $(sc.tyName) $name (some $src)), sc)
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
  | .require c => return (← `($(gen `Stmt.requireStmt) $(← transExpr sc false c)), sc)
  | .assert c => return (← `($(gen `Stmt.assertStmt) $(← transExpr sc false c)), sc)
  | .revert => return (← `($(gen `Stmt.revert) none), sc)
  | .expr e =>
      match callHead? e with
      | some ("delete", #[t]) =>
          return (← `($(gen `Stmt.delete) $(← transExpr sc true t)), sc)
      | _ => return (← `($(gen `Stmt.expr) $(← transExpr sc false e)), sc)

/-- A residual program: statements folded left to right, each capture
extending the scope the rest is read in. -/
def transBlock (sc : Scope) (stmts : Array Syntax) : CommandElabM Term := do
  let mut sc := sc
  let mut out : Array Term := #[]
  for s in stmts do
    let (t, sc') ← transStmt sc s
    out := out.push t
    sc := sc'
  `([$out,*])

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
  let mode := (group? stx[2]).map fun g =>
    if g[0].getAtomVal == "box" then `box else `diamond
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

def resultView? (stx : Syntax) : Option ResultView :=
  let k := stx.getKind
  let a := args stx
  if isRevertResult stx then some .reverting
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

/-- The pattern a matched expression is destructured by, and the conjuncts
its schema variables contribute.  `holes` writes `_` where the condition
does not look — the static type, and a field the rule does not name. -/
def analyzePat (holes : Bool) (sc : Scope) (stx : Syntax) :
    CommandElabM (Option (Term × Array Cond × Array Cond)) := do
  let some view := exprView? stx | return none
  let ty := sc.tyName
  let tyPat : Term ← if holes then `(_) else `($ty)
  match view with
  | .field b f =>
      let some (.var bx) := exprView? b | return none
      let kt ← kindTerm (kindOfName bx.getId)
      let fPat : Term ← if holes then `(_) else `($f)
      let pat ← `($(gen `WrappedExpr.field) $kt $tyPat $bx $fPat)
      let sch := schemaVar bx.getId.toString
      return some (pat, sch.base.map (Cond.pred · bx), sch.trail.map (Cond.pred · bx))
  | .index b i =>
      let some (.var bx) := exprView? b | return none
      let some (.var ix) := exprView? i | return none
      let kt ← kindTerm (kindOfName bx.getId)
      let pat ← `($(gen `WrappedExpr.index) $kt $tyPat $bx $ix)
      let sb := schemaVar bx.getId.toString
      let si := schemaVar ix.getId.toString
      return some (pat, sb.base.map (Cond.pred · bx) ++ si.base.map (Cond.pred · ix),
                   sb.trail.map (Cond.pred · bx) ++ si.trail.map (Cond.pred · ix))
  | .pushPlace b =>
      let some (.var bx) := exprView? b | return none
      let pat ← `($(gen `WrappedExpr.pushPlace) $bx)
      let sch := schemaVar bx.getId.toString
      return some (pat, sch.base.map (Cond.pred · bx), #[])
  | .incDec b =>
      let some (.var bx) := exprView? b | return none
      let some op := sc.opName
        | throwErrorAt stx "`++` needs the rule to declare an `IncDec` parameter"
      let opS := mkIdent `opS
      let pat ← `($(gen `WrappedExpr.incDec) $opS $bx)
      let sch := schemaVar bx.getId.toString
      return some (pat, #[Cond.raw (← `($opS = $op))] ++ sch.free.map (Cond.pred · bx), #[])
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

/-- The opaque form: the effect is given as a term.  For the rules whose
condition is a bespoke predicate, or whose goals consume the condition proof
(`storageDeleteComplexTarget`, `functionCallArgCapture`, …) — the handful
the schema-variable convention cannot reach. -/
@[command_elab Solidity.RuleSyntax.ruleOpaque]
def elabRuleOpaque : CommandElab := fun stx => do
  match stx with
  | `(command| $[$doc:docComment]? sol_rule $name:ident $[twins%$tw]? $[alternative%$alt]?
        $[($b:ident : $bty:ident)]? $[$fr:ruleFrom]? := $e:term) => do
      let o ← originOf? (fr.map (·.raw))
      let effect ← withOriginOf o e
      pushRule { ref := stx, name := name, doc := doc
                 binder := match b, bty with
                   | some b, some t => some { name := b, type := t }
                   | _, _ => none
                 effect := effect, twins := tw.isSome, alternative := alt.isSome }
  | _ => throwUnsupportedSyntax

/-! ### The declarative form -/

/-- Is this expression a bare schema variable? -/
def isPlainVar (stx : Syntax) : Option Ident :=
  match exprView? stx with
  | some (.var x) => some x
  | _ => none

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
  (`StepEffect`'s docstring, "two wrinkles"). -/
  destruct : Option (Nat × Term × Term × Bool) := none
  conds : Array Cond := #[]
  paramPats : Array (Ident × Option Syntax) := #[]
  /-- An extra leading `CaseMode` argument, as `popEffect` takes. -/
  modeFirst : Bool := false
  /-- The *statement's* operator, where the conclusion binds one.  A goal
  must use this and not the family index: the two are equal only under the
  condition's first conjunct, so `compoundGoals` is handed the operator the
  statement carries, exactly as the hand-written arms did. -/
  stmtOp : Option Ident := none

/-- One side of a two-sided conclusion: its parameter name, the conjuncts it
contributes, and — when it is a path — the pattern it is matched by. -/
private def side (sc : Scope) (fallback : Name) (stx : Syntax)
    (isPlace : Bool := false) :
    CommandElabM (Ident × Array Cond × Option (Term × Term × Array Cond)) := do
  match isPlainVar stx with
  | some x =>
      match isPlace, (schemaVar x.getId.toString).kind with
      | true, some k =>
          let kt ← kindTerm k
          return (x, #[Cond.raw (← `($(gen `PlaceExpr.kind) $x = $kt)),
                       Cond.pred `isSimple x], none)
      | _, _ => return (x, freeConds x, none)
  | none =>
      let some (condPat, cs, trail) ← analyzePat true sc stx
        | throwErrorAt stx "unsupported conclusion shape"
      let some (goalPat, _, _) ← analyzePat false sc stx
        | throwErrorAt stx "unsupported conclusion shape"
      return (mkIdent fallback, cs, some (condPat, goalPat, trail))

/-- The conclusion of a rule. -/
def analyzeConcl (sc : Scope) (stx : Syntax) : CommandElabM Concl := do
  let some view := stmtView? stx
    | throwErrorAt stx s!"unsupported conclusion (kind {stx.getKind})"
  let two (builder : Name) (a b : Syntax) (aPlace bPlace : Bool)
      (lead : Array Cond := #[]) (leadParams : Array Ident := #[]) :
      CommandElabM Concl := do
    let (ap, ac, apat) ← side sc `lhs a
    let (bp, bc, bpat) ← side sc `rhs b
    if apat.isSome && bpat.isSome then
      throwErrorAt stx "a rule matches at most one side of its conclusion"
    let n := leadParams.size
    let params := leadParams ++ #[ap, bp]
    let trail := (apat.map (·.2.2)).getD ((bpat.map (·.2.2)).getD #[])
    let destruct : Option (Nat × Term × Term × Bool) :=
      match apat, bpat with
      | some (c, g, _), _ => some (n, c, g, aPlace)
      | _, some (c, g, _) => some (n + 1, c, g, bPlace)
      | _, _ => none
    return { builder := builder, params := params
             destruct := destruct
             conds := lead ++ ac ++ bc ++ trail
             paramPats := #[(ap, if apat.isSome then some a else none),
                            (bp, if bpat.isSome then some b else none)] }
  let one (builder : Name) (a : Syntax) (aPlace : Bool)
      (placeKind : Bool := false) : CommandElabM Concl := do
    let (ap, ac, apat) ← side sc `target a placeKind
    return { builder := builder, params := #[ap]
             destruct := apat.map fun (c, g, _) => (0, c, g, aPlace)
             conds := ac ++ (apat.map (·.2.2)).getD #[]
             paramPats := #[(ap, if apat.isSome then some a else none)] }
  match view with
  | .assign lhs rhs => two `assignEffect lhs rhs true false
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
      | _ => one `exprEffect e false
  | .require c => one `requireEffect c false
  | .assert c => one `assertEffect c false
  | .revert => return { builder := `revertEffect, params := #[], conds := #[] }
  | .pop t => one `popEffect t true (placeKind := true)
  | .transfer r a => two `transferEffect r a false false
  | .push target value => do
      let (tp, tc, tpat) ← side sc `target target true
      let vp := mkIdent `value
      let vc ← match value with
        | none => pure #[Cond.raw (← `($vp = none))]
        | some v =>
            match isPlainVar v with
            | some x =>
                let inner ← renderConds (freeConds x)
                pure #[Cond.raw (← `(match $vp:ident with | some $x:ident => $inner | none => False))]
            | none => throwErrorAt v "a push argument must be a schema variable"
      return { builder := `pushEffect, params := #[tp, vp]
               destruct := tpat.map fun (c, g, _) => (0, c, g, true)
               conds := tc ++ vc
               paramPats := #[(tp, if tpat.isSome then some target else none)] }
  | .decl kind ty name init => do
      let builder := match kind with
        | `storage => `storageDeclEffect
        | `memory => `memoryDeclEffect
        | _ => `stackDeclEffect
      let initP := mkIdent `init
      let cs ← match init with
        | none => pure #[Cond.raw (← `($initP = none))]
        | some _ => pure #[Cond.raw (← `(Option.isSome $initP))]
      let destruct ← match init with
        | none => pure none
        | some e =>
            let some x := isPlainVar e
              | throwErrorAt e "a declaration's initialiser must be a schema variable"
            let c ← `(some _)
            let g ← `(some $x)
            pure (some (2, c, g, false))
      return { builder := builder, params := #[ty, name, initP]
               destruct := destruct, conds := cs
               paramPats := #[(ty, none), (name, none), (initP, none)] }
  | .ite c thn els => do
      let (cp, cc, _) ← side sc `cond c
      return { builder := `iteEffect, params := #[cp, thn, els], conds := cc
               paramPats := #[(cp, none), (thn, none), (els, none)] }
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
  let binder : Option RuleBinder :=
    (group? a[4]!).map fun g =>
      let ga := args g
      { name := ⟨ga[0]!⟩, type := ⟨ga[1]!⟩ }
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
  let sc0 : Scope := { tyName := tyName, opName := binder.map (·.name) }
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
    | some (idx, condPat, _, placeCoerced), none =>
        let p := concl.params[idx]!
        let scrut : Term ←
          if placeCoerced then `(($p : $(gen `WrappedExpr))) else `($p)
        `(match $scrut:term with | $condPat => $condBody | _ => False)
    | _, _ => pure condBody
  let params := concl.params
  -- The goals read the *statement's* operator where the conclusion binds
  -- one; the condition's first conjunct is what ties it to the family index.
  let scope : Scope :=
    { params := concl.paramPats, tyName := tyName
      opName := concl.stmtOp <|> binder.map (·.name) }
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
    | _ => false
  -- `cond`, and — where the rule rewrites — `goals` re-matching the same
  -- scrutinee with the condition proof as a second discriminant.
  let condFn ← `(fun $params:ident* => $condBody)
  let hName := mkIdent `h
  let goalsFn ←
    match concl.destruct, isUnfold with
    | some (idx, _, goalPat, placeCoerced), true =>
        let p := params[idx]!
        let inner ←
          if goalsStx.getKind == ``goalsOne || goalViews.size == 1 then
            match resultView? goalViews[0]!.result with
            | some (.prog _ stmts) => transBlock scope stmts
            | _ => transGoals scope goalViews premStx
          else transGoals scope goalViews premStx
        let alt ←
          if placeCoerced then
            `(Lean.Parser.Term.matchAltExpr| | ⟨$goalPat, _⟩, _ => $inner)
          else
            `(Lean.Parser.Term.matchAltExpr| | $goalPat, _ => $inner)
        `(fun $params:ident* $hName:ident => $(gen `Rules.unfoldGoal) <|
            match $p:ident, $hName:ident with $alt:matchAlt)
    | _, _ =>
        let body ← transGoals scope goalViews premStx
        `(fun $params:ident* _ => $body)
  let builder := mkIdent (`Rules ++ concl.builder)
  -- Where the modality is an argument of the builder it is passed; elsewhere
  -- a twin is the same effect under `withMode`, which is how `Rules.lean`
  -- has always written the twelve pairs.
  let mkEffect (mode : Option Name) : CommandElabM Term := do
    let m ← modeTerm (mode.getD `both)
    let base ←
      if concl.builder == `revertEffect then `($builder $m)
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
