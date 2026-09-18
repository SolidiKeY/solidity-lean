import Solidity.AST
import Solidity.KeyTaclets
import Solidity.RuleSyntax

/-!
# The rules of the calculus

One `sol_rule` declaration per rule, from which `RuleName`, `ruleEffect`,
`ruleNames` and `twinPairs` are *generated* (`sol_assemble_rules`, below the
table).  **Declaration order is the order of all four, and it is
load-bearing**: `FirstStepCase` takes the first applicable rule under the
block modality, so a box twin must precede its diamond twin
(`CandidateStep.twins_box_first` checks all twelve pairs).  It is why
`revertBox` precedes `revertDiamond` here even though solkey's rule file
prints them the other way round.

The calculus has *only* these rules — there is no catch-all tier, so a
statement no rule covers is stuck (`Coverage.ResidueShape` enumerates those
shapes, `Progress.lean` refutes totality).

## A rule is a taclet

`StepEffect` carries **goals**, not a residual block: a list of `RuleGoal`s,
each of which may be guarded, may install an **update** ahead of the residual,
and may be a bare formula with no program left.  Reading a goal is reading
KeY's weakest precondition — for `⟨stmt; rest⟩post`, each goal contributes

    guard  →  {update} ⟨residual ++ rest⟩ post

and the rule means the conjunction over the goals whose `mode` applies.

The update language is **syntax only** — no `State`, no `Res`, nothing from
`Semantics.lean`.  That is load-bearing twice over: the `SolKey` reader's
decoder imports this file to compare a parsed taclet with a Lean rule and
needs it cheap to elaborate, and a table that could call the interpreter
could define its updates *as* the interpreter, which would make the bridge
theorems vacuous.  Evaluation is `Update/Eval.lean`, the wp reading
`Update/Wp.lean`, and each rule's update is proved against
`Wp.terminalUpdate?` in `Update/TacletTable.lean`.

## The organisation

Sections run: Storage (Steps 1-3) › require/assert, conditional, abrupt ›
Payment › Memory (same three steps) › Storage↔Memory copies › Arithmetic
(local/storage/memory) › rules with no counterpart upstream.

The three-step split is Solidity's evaluation order: the right-hand side of
an assignment is evaluated before the left-hand side, so Step 1 unfolds the
right-hand side, Step 2 the left, and Step 3 turns a fully simple statement
into an update.

`docs/lean-key-rule-map.md` is the authority on how these names line up with
solkey's taclets, and `lake exe solkeycheck` checks the sort annotations
against solkey's own rule file.  The banners here do not restate either.

The last section has no upstream counterpart by design: solkey's finer tiers
and the genuinely Lean-only rules (front-end normalisations, scratch
bindings, the call rules).  **Nothing checks this direction** — a Lean rule is
deliberately allowed to be finer than the presentation upstream.

## Writing a rule

The declarative form reads as the paper draws the rule, conclusion left of
`⇝`, premises right, the constant sequent contexts dropped:

```
sol_rule storageFieldWriteSave from storageFieldWriteSave :
  <[ sp.fld = se ]> ⇝ { storage := save(sp.fld, se) } <[ ]>
```

The *kind* of every schema variable is its name, which is the paper's central
device and **what makes the rules pairwise disjoint without an applicability
predicate**: `sp.fld = se` carries `isSimple sp ∧ isSe se` and the pattern
`WrappedExpr.field Kind.storage _ sp _`.  Inside a goal the statement's
operator is `opS`; `op` is the family index, and the two are equal only under
the family's own conjunct.  The grammar, the `where`/`twins`/`after` clauses
and the schema-variable table are `RuleSyntax.lean`; the checklist for adding
a rule is `.claude/rules/rule-table.md`.

Every rule of the table is written this way; there is no second form.  Two
clauses carry what a schema variable cannot say: `where cond := P` replaces
the generated condition for the handful whose applicability is a bespoke
predicate, and `⟦ b ⟧` in place of a residual gives the block as a term, with
the condition proof in scope as `h`, for the handful whose residual is
computed from that proof.  Both keep the conclusion declarative.

One exception worth knowing: `transferWithCallback` is marked `alternative`.
It is KeY's `\choice` alternative, never appears in `ruleNames`, and lives in
`ruleNamesWithCallback`.
-/


namespace Solidity

inductive Modality where
  | box
  | diamond
  deriving DecidableEq, Repr

inductive CaseMode where
  | both
  | box
  | diamond
  deriving DecidableEq, Repr

namespace CaseMode

def applies : CaseMode -> Modality -> Bool
  | both, _ => true
  | box, Modality.box => true
  | box, Modality.diamond => false
  | diamond, Modality.box => false
  | diamond, Modality.diamond => true

end CaseMode


  /-! ### The KeY side of a rule: updates, guards, goals

  A KeY taclet is not a program rewrite.  It is a *sequent* rewrite: one or
  more goals, each of which may be guarded, may install an **update** ahead of
  the residual modality, and may be a bare formula with no program left at all.
  `solidityProgramRules.key` writes all four:

  ```
  storageRootWriteStore:   \replacewith({storage := save(storage, gp, se)}
                               \modality{#mod}{c# #c}\endmodality(post))
  storageIndexWriteArraySave:
      "inBounds":    \replacewith(0 <= i & i < find(storage, consr(sp, size))
                         -> {storage := save(storage, consr(sp, at(i)), se)}…);
      "outOfBounds": \replacewith(!(0 <= i & i < …) -> …revert(); …)
  divisionAssignment:      \replacewith(\if(se2 != 0) \then({v := se1 / se2}…)
                                                      \else(…revert(); …))
  revertBox:               \replacewith(true)
  ```

  The vocabulary below is exactly that, and it is **syntax only**: no `State`,
  no `Res`, nothing imported from `Semantics.lean`.  That is deliberate and
  load-bearing in two directions.  the `SolKey` reader's decoder imports this file to
  compare a parsed taclet with a Lean rule, and it must stay cheap to elaborate;
  and a rule table that could call the interpreter could define its updates *as*
  the interpreter, which would make the bridge theorems of
  `Update/TacletTable.lean` vacuous.  Evaluation lives in `Update/Eval.lean`,
  and the weakest-precondition reading in `Update/Wp.lean`.

  The reading of a goal is KeY's, as a weakest precondition: for
  `⟨stmt; rest⟩post`, each goal contributes

      guard  →  {update} ⟨residual ++ rest⟩ post

  and the rule's meaning is the conjunction over the goals whose `mode`
  applies.  An *unfold* rule is the degenerate case — one goal, no guard, no
  update, a non-empty residual — which is why `StepEffect.block` below is still
  definable from `goals` and every existing consumer keeps working.

  ### Why a guard carries premises

  A guard is not just a formula.  The interpreter's fault order on
  `arr[i] = se` is right-hand side, then target, then bounds
  (`Semantics.execAssignNested`), so on `arr[i] = 1/0` with `i` out of bounds it
  is *stuck*, not reverting — while the pre-state formula `0 <= i < length(arr)`
  alone would say "revert".  `Guard.premises` lists the operands that are read
  first, in that order, purely for their halt; the formula is decided only once
  they have all succeeded.  A guard therefore evaluates to `Res Bool`, not
  `Bool`. -/

  /-- A term read in the state an update is applied in: the right-hand side of
  a KeY update, in KeY's vocabulary.  All the readers are the interpreter's, so
  what a rule *claims* and what the interpreter *does* stay comparable
  (`Update/Eval.lean`), and where they differ the difference is a row of
  `Update/SolcDelta.lean` rather than a silent re-definition. -/
  inductive Sym where
    /-- The value a *terminal* expression denotes: a literal, a variable, a
    simple storage/memory place (`find`/`read`), `se1 op se2`, `op se`, or the
    value of `++t` / `t--`.  Which of KeY's terms this spells is read off the
    expression — `{v := se1 + se2}` is `read` of the `+` node. -/
    | read (e : WrappedExpr)
    /-- The value currently at an *l-value*.  Distinct from `read` on a storage
    root: an l-value resolves by origin (`resolveLoc`), a read resolves env
    first (`resolveS`), and a non-global root is an alias on which the former
    is stuck. -/
    | current (target : WrappedExpr)
    /-- `find<[int]>(storage, consr(arr, size))`: an array's length. -/
    | length (arr : WrappedExpr)
    /-- `selectSt<[int]>(net, at(sadr))`: a ledger entry. -/
    | netOf (addr : WrappedExpr)
    /-- `t op se` at the target's type: the new value of `t op= se`, and — with
    the literal `1` — of `++t` / `t--`.  The value operand is read **before**
    the target, as solc evaluates it. -/
    | combined (op : BinOp) (target : WrappedExpr) (value : WrappedExpr)
    /-- `defaultForTy(T)`: what a declaration without initializer binds. -/
    | deflt (ty : Ty)
    deriving Repr

  /-- What `x := …` binds a name to.  KeY writes all of these the same way; the
  right-hand sides differ in which `Binding` they produce. -/
  inductive BindRhs where
    /-- `v := t` — a stack value. -/
    | val (t : Sym)
    /-- `sp := <path of src>` — a storage alias (`Binding.spath`). -/
    | path (src : WrappedExpr)
    /-- `lp := consr(arr, at(find(storage, consr(arr, size))))` — the slot
    `arr.push()` appends, addressed in the pre-state.  `place` is the whole
    push place `arr.push()`; it pairs with `StorageUpd.pushPlace`. -/
    | pushSlot (place : WrappedExpr)
    /-- `mv := <identity of src>` — a memory alias (`Binding.mref`). -/
    | mref (src : WrappedExpr)
    deriving Repr

  /-- `storage := …`. -/
  inductive StorageUpd where
    /-- `save(storage, p, t)`. -/
    | save (target : WrappedExpr) (t : Sym)
    /-- `save(storage, p, find<[StValue]>(storage, src))` — a storage source.
    The source's type is mapping-free: solc ≥ 0.7 and solkey's parser reject
    the copy otherwise, `TypedStmt.Assign.mk` cannot be built for it, and
    `stmtTypingOk` states the same predicate; so the write is the plain write
    this constructor evaluates to (`Theory/Storage.lean`'s collapsing leaf). -/
    | copy (target : WrappedExpr) (src : WrappedExpr)
    /-- `save(storage, p, copyMem(mtSt, memory, src))` — a memory source. -/
    | copyFromMem (target : WrappedExpr) (src : WrappedExpr)
    /-- `arr.push(se)` / `arr.push(sp)` / `arr.push()`: KeY's
    `storagePushValueSave`, `…CopySource` and `storagePushLengthSave`, which
    differ only in the *sort* of what is appended — the element, a copied
    source, or the slot a `pop` gave back (`value = none`).  Each writes the
    new slot and the new length.  The bare push is `delAt` at that slot, so it
    keeps the mapping members `delete` never clears (`Semantics.pushSlot`);
    the two valued forms overwrite it, and the leaf they would keep is
    invisible because the interpreter is stuck on a mapping-carrying source. -/
    | push (arr : WrappedExpr) (value : Option WrappedExpr)
    /-- The same extension, named through a push *place* (`p = arr.push()`):
    `place` is the whole `arr.push()` node. -/
    | pushPlace (place : WrappedExpr)
    /-- `arr.pop()`: `delAt` the last slot — which keeps its mapping members
    and hands the slot back for the next `push` — and decrement the length. -/
    | pop (arr : WrappedExpr)
    /-- `delete p`: the current value's default (`SVal.defaultOf`, which leaves
    mapping members alone — KeY's lazy `delAt`/`delNode`). -/
    | clear (target : WrappedExpr)
    deriving Repr

  /-- `memory := …`.  The heap and the allocation counter move together, so one
  constructor writes both. -/
  inductive HeapUpd where
    /-- `write(memory, mp, f, t)` / `write(memory, mp, at(i), t)`. -/
    | write (target : WrappedExpr) (t : Sym)
    /-- `write(memory, mp, …, <memory image of src>)` — a reference source,
    which deep-copies (and so allocates) from storage. -/
    | writeRef (target : WrappedExpr) (src : WrappedExpr)
    deriving Repr

  /-- One elementary update of a `\replacewith`; a taclet's update is a list of
  them, read in parallel (`Upd.Par`).

  Three constructors stand for a *pair* of KeY elements, because the pair is
  what KeY itself writes and neither half is meaningful alone:
  `memDecl`/`memDelete` are `{mp := idC(freshIdp, nil)}{memory := addM(…)}`,
  and `transfer` is `{selfBalance := … || net := …}`.  `Update/Eval.lean`
  expands each into the `Upd.Elem`s it names. -/
  inductive UpdElem where
    | bind (n : Name) (rhs : BindRhs)
    | storage (u : StorageUpd)
    | heap (u : HeapUpd)
    /-- `T memory m;` / `T memory m = sp;` — KeY
    `memoryReferenceDeclFreshAlloc` / `memoryArrayFreshAlloc` for `init = none`
    (`{mp := idC(freshIdp, nil)}{memory := addM(memory, freshIdp)}`), and the
    storage-copy declaration for `init = some sp` (`{mp := idC(freshIdp, nil)}
    {memory := copySt(addM(memory, freshIdp), freshIdp, find(storage, sp))}`,
    KeY `memoryStorageCopy`'s shape). -/
    | memDecl (ty : Ty) (name : Name) (init : Option WrappedExpr)
    /-- `delete m` / `delete m.f` / `delete m[se]`: KeY
    `memoryRootDeleteFreshRebind` rebinds the root to a fresh object, the field
    and index rules write the slot's default (allocating for a reference
    element). -/
    | memDelete (target : WrappedExpr)
    /-- The write-back of `++t` / `t--`, where `e` is the whole `incDec`
    expression: `{t := t + 1}` at whichever data location `t` lives in. -/
    | bumpOf (e : WrappedExpr)
    /-- `{selfBalance := selfBalance - se || net := storeSt(net, at(a),
    selectSt<[int]>(net, at(a)) - se)}` — the two halves of `a.transfer(se)`,
    which move together. -/
    | transfer (recipient amount : WrappedExpr)
    /-- KeY's skolem re-binding of the whole state after a re-entrant callback
    (`transferWithCallback`'s `{storage := storageSk || net := netSk ||
    selfBalance := selfBalanceSk}`).  It has no evaluator: its meaning is the
    relational layer `CallbackSemantics.ExecC`, not a state function. -/
    | havoc
    deriving Repr

  /-- The parallel update KeY writes `{a || b || c}`. -/
  abbrev UpdTerm := List UpdElem

  /-- An operand a guard reads before it decides, for its halt alone.  The list
  is in the interpreter's evaluation order. -/
  inductive Premise where
    /-- Read a term. -/
    | read (t : Sym)
    /-- Resolve a target's path. -/
    | resolve (target : WrappedExpr)
    /-- Take a source's storage/memory image (a reference source allocates). -/
    | image (src : WrappedExpr)
    deriving Repr

  /-- The formulas KeY guards a goal with, and the ones it leaves as bare
  obligations. -/
  inductive SideFormula where
    | const (b : Bool)
    | neg (φ : SideFormula)
    /-- `se = TRUE`. -/
    | holds (c : WrappedExpr)
    /-- `0 <= i & i < find<[int]>(consr(arr, size))` for the index access `e`
    performs, reaching through an `incDec` wrapper to its target.  A *mapping*
    receiver has no length and no bounds goal, so this is `true` there — which
    is what lets one Lean rule merge KeY's array and mapping taclets. -/
    | inBounds (e : WrappedExpr)
    /-- `0 < find<[int]>(consr(arr, size))`, the `pop` guard. -/
    | nonEmpty (arr : WrappedExpr)
    /-- `se != 0`. -/
    | nonZero (e : WrappedExpr)
    /-- `se2 != 0` for the binary operation `e = se1 / se2` — KeY's
    `\if(se2 != 0)` on `divisionAssignment` and `moduloAssignment`. -/
    | rhsNonZero (e : WrappedExpr)
    /-- `0 <= se & se <= selfBalance`, the diamond `transfer` obligation. -/
    | funded (amount : WrappedExpr)
    /-- `CInv(storage, net)`, the contract invariant of the payment rules.
    Uninterpreted: the goals that carry it are never executed. -/
    | cinv
    deriving Repr

  /-- A goal's guard: what to read first, then what must hold. -/
  structure Guard where
    premises : List Premise := []
    formula : SideFormula := SideFormula.const true
    deriving Repr

  /-- What is left of a goal once its guard holds. -/
  inductive RuleResidual where
    /-- `{upd}⟨block ++ rest⟩post` — the ordinary case.  An *unfold* goal has
    `upd = []` and a non-empty `block`; a *terminal* goal has a `block` of `[]`
    and an update that is usually not. -/
    | prog (upd : UpdTerm) (block : Block)
    /-- `⟨revert(); rest⟩post` — the `\else` half of every guarded split. -/
    | reverting
    /-- `{upd}φ`: a formula, no program.  Covers the constant goals
    (`revertBox`'s `\replacewith(true)`, `revertDiamond`'s `false`) and the
    real obligations (`assertSimple`'s "Violated", the diamond `transfer`'s
    "sufficient funds", `transferWithCallback`'s "invariant on exit"). -/
    | obligation (upd : UpdTerm) (φ : SideFormula)
    deriving Repr

  /-- One goal of a taclet.  `label` is KeY's own goal name where it has one
  (`"inBounds"`, `"Violated"`, `"sufficient funds"`), for reading. -/
  structure RuleGoal where
    label : String := ""
    mode : CaseMode := CaseMode.both
    guard : Guard := {}
    residual : RuleResidual
    deriving Repr

  /-- `goals` is *dependent on the condition proof*, and every rule below uses
  that: a rule's `goals` matches the same scrutinee its `cond` matches, passes the
  condition proof as a second discriminant, and lists **only** the arms the `cond`
  admits.  In every other arm the proof's type reduces to `False`, so the match
  compiler refutes it and there is no catch-all — an empty residual therefore means
  "terminal rule" and nothing else.

  One discipline on top of that, and it is what makes `RuleShapes` provable by
  `cases`: a **terminal** rule's goals never match on the place its `cond`
  matched.  They hand the whole `PlaceExpr`/`WrappedExpr` to the update term and
  let the evaluator decompose it into `consr(sp, at(i))`, exactly as
  `Wp.storageAssignUpd` takes its arguments whole.  Unfold goals keep the
  match, inside `unfoldGoal <| …`.

  Two wrinkles, because `cond` reaches `block` as an unreduced beta-redex
  (`(fun lhs rhs => …) lhs rhs`) and the match compiler does not `whnf` a
  hypothesis's type:

  * when the scrutinee is a plain variable (`rhs`, `init`, `value`, `expr`, …),
  `match rhs, h with` is enough — substituting the pattern beta-reduces `h`'s
  type and exposes the `False`;
  * when it is the projection `(lhs : WrappedExpr)`, that never happens, so those
  rules destructure the place instead: `match lhs, h with | ⟨PAT, _⟩, _ => …`.
  (`storagePushLhsToPushValue` also *needs* the `assignable` field this exposes.)
  `functionCallArgCapture`, whose scrutinee is an application, re-ascribes the
  condition with a `have` for the same reason. -/
  structure StepEffect where
  mode : Stmt -> CaseMode := fun _ => CaseMode.both
  cond : Stmt -> Prop
  goals : (stmt : Stmt) -> cond stmt -> List RuleGoal := fun _ _ => []
  /-- Which KeY taclet this rule transcribes (`KeyTaclets.lean`).  A rule with
  no taclet says so with `leanOnly`, and `RuleShapes.leanOnlyRules` makes it
  give a reason. -/
  origin : KeyOrigin := KeyOrigin.leanOnly
  /-- The `\heuristics` rule set(s) of the taclet(s) `origin` names, without
  repetition.  `Rules.withOrigin` computes it from `origin`, so the two cannot
  drift; it is a field rather than a function because a `StepEffect` is meant
  to carry everything the taclet header says.  Nothing in the calculus reads
  it (see `KeyTaclets.lean` on why KeY's strategy annotations have no Lean
  counterpart). -/
  heuristics : List Heuristic := []

  namespace StepEffect

  /-- The residual program of a goal list: the block of the first goal that
  still has one.  A guarded split states the same residual in both of its
  program goals, and a terminal rule has `[]` in its only one, so this is
  well defined without choosing. -/
  def mainBlock : List RuleGoal -> Block
    | [] => []
    | g :: rest =>
        match g.residual with
        | RuleResidual.prog _ b => b
        | _ => mainBlock rest

  /-- The rule's residual block, as the rewrite layer has always read it: the
  program part of its goals, with the updates and guards forgotten.  This used
  to be a field, and is kept definitionally equal to what that field held, so
  every `rfl`/`exact` about a residual still goes through. -/
  def block (e : StepEffect) (stmt : Stmt) (h : e.cond stmt) : Block :=
    mainBlock (e.goals stmt h)

  end StepEffect


  namespace Rules

  def storagePathAliasName : Name := "sp"
  /-- The calculus's own naming policy spells a memory path
  alias `mv`, beside the storage `sp`, the value `pv` and the index `idx`.
  (The examples of the calculus also use ad-hoc names — `acc`, `aliceAcc`,
  `tokRef` — which contradict that policy; that is an upstream matter, not
  something the Lean port chases.) -/
  def memoryPathAliasName : Name := "mv"
  def valueAliasName : Name := "pv"
  def indexAliasName : Name := "idx"
  /-- The value operand of an `=` / `op=` statement, frozen by an LHS-unfold
  rule *before* it captures any part of the target.  Distinct from `pv`: the
  `*ValueRhsCapture` family already binds `pv`, and its residual is consumed
  immediately afterwards by an LHS-unfold rule.  (solkey spells it `rv` too.) -/
  def rhsValueAliasName : Name := "rv"

  def isSimple (expr : WrappedExpr) : Prop := expr.simple = true
  def isComplex (expr : WrappedExpr) : Prop := expr.complex = true
  def isStack (expr : WrappedExpr) : Prop := expr.isStack = true
  def isStorage (expr : WrappedExpr) : Prop := expr.isStorage = true
  def isMemory (expr : WrappedExpr) : Prop := expr.isMemory = true
  def isLocal (expr : WrappedExpr) : Prop := expr.isLocal = true
  def isGlobal (expr : WrappedExpr) : Prop := expr.isGlobal = true
  def isPrimitive (expr : WrappedExpr) : Prop := expr.isPrimitive = true
  def isIdentity (expr : WrappedExpr) : Prop := expr.isIdentity = true
  def isArray (expr : WrappedExpr) : Prop :=
  ∃ elem, expr.ty = Ty.ref (RefTy.array elem)
  def isMapping (expr : WrappedExpr) : Prop :=
  ∃ key value, expr.ty = Ty.ref (RefTy.mapping key value)

  /-! ### Schema-variable kinds

  The rules above are the KeY *sort modifiers* one for one — `simple`,
  `complex`, `storage`, `memory`, `global`, `array`, `mapping`,
  `primitive`/`reference` — which is what lets the `SolKey` reader's decoder
  (`SolKey/Decode/Sorts.lean`) translate a `\program Sort[mods]` declaration
  into a Lean condition without a lookup table.

  The calculus writes its conditions one level up, in its own *schema
  variables*, for storage and for memory alike: a rule that
  matches `se` has already said "stack word", one that matches `sp` has said
  "simple storage path".  Four of those kinds are conjunctions, and they get a
  name here so the conditions below read as the calculus does.  The rest are
  single predicates and are *not* aliased — `gsp` is `isGlobal`, `lsv` is
  `isLocal`, `i` is `isSimple` on an index, `nsp` is `isComplex` on a storage
  path — because a one-for-one alias would only hide the KeY modifier.

  These are `abbrev`s, hence reducible: every condition that uses one is the
  same proposition it was before, up to unfolding.  Note the consequence for
  proofs, which is why they are not `def`s: `simp only [isStack, isSimple]`
  makes *no* progress on a folded hypothesis, so a tactic block that takes a
  condition apart with `simp only` must name the abbrev too (that is what the
  `Rules.isSe`/`isSp`/`isMv`/`isNmp` entries in `Uniqueness.lean`'s `simp only`
  lists are doing).  Destructuring with `obtain ⟨_, _⟩` and type ascription
  both work unchanged.

  **Where the conditions below do *not* fold, and why.**  `And` is right-nested
  and not definitionally associative, so a pair can be folded only when it is
  the tail of the chain, the whole condition, or the whole operand of a `¬`.
  Three families therefore keep the unfolded spelling on purpose:

  * the array and mapping terminals, whose pair is followed by
  `isArray path` / `isMapping path` (`storageIndexWriteArraySaveBox`, …);
  * the `nlhs` rules, whose pair (`isStorage lhs ∧ isComplex lhs`) is at the
  *head* (`storageFieldReadUnfoldRightSndResult`, …);
  * the memory-root *targets*, which spell the kind as
  `lhs.kind = Kind.memory ∧ isSimple lhs` rather than `isMemory lhs`
  (`memoryRootAlias`, `memoryStorageCopy`, `memoryFieldReadAliasRoot`, …);
  `Uniqueness.lean` bridges the two spellings and they must stay distinct
  terms here.

  One more asymmetry worth not "tidying": the `StoreRoot` rules ask
  `isSimple lhs ∧ isGlobal lhs` while the `RootWrite`/`RootCompoundAssign`
  rules ask bare `isGlobal lhs`.  That is a real difference in the conditions,
  not a spelling accident. -/

  /-- Schema variable `se`: a *simple expression* — a single stack-valued
  word, program variable or constant, whose evaluation has no side effects.
  KeY `SimpleExpression` (`solkey/docs/key-taclets.md:76`).

  Distinct from `isStackVar` below, which is the same predicate under the
  calculus's *target*-side name `v` (KeY `Variable[name=value]`); both are kept so
  that a rule reads as the calculus writes it. -/
  abbrev isSe (expr : WrappedExpr) : Prop := isStack expr ∧ isSimple expr

  /-- Schema variable `sp`: a *simple storage path* — a contract root or
  a generated alias.  KeY `Path[storage,simple]`. -/
  abbrev isSp (expr : WrappedExpr) : Prop := isStorage expr ∧ isSimple expr

  /-- Schema variable `mv`: a *memory variable* — a memory root or a
  generated identity alias.  KeY `Variable[memory]`. -/
  abbrev isMv (expr : WrappedExpr) : Prop := isMemory expr ∧ isSimple expr

  /-- Schema variable `nmp`: a *nonsimple memory path*, one with an
  unresolved base or receiver.  KeY `Path[memory,complex]`. -/
  abbrev isNmp (expr : WrappedExpr) : Prop := isMemory expr ∧ isComplex expr

  def isSimpleStorageDeleteTarget : WrappedExpr -> Prop
  | target@(WrappedExpr.var Kind.storage _ _) => isGlobal target
  | WrappedExpr.field Kind.storage _ path _ => isSimple path
  | WrappedExpr.index Kind.storage _ path index =>
      isSimple path ∧ isSimple index ∧ (isArray path ∨ isMapping path)
  | WrappedExpr.pushPlace path =>
      path.kind = Kind.storage ∧ isSimple path
  | _ => False

  def isSimpleMemoryDeleteTarget : WrappedExpr -> Prop
  | target@(WrappedExpr.var Kind.memory _ _) => isSimple target
  | WrappedExpr.field Kind.memory _ path field =>
      isSimple path ∧ (field.isPrimitive = true ∨ field.isIdentity = true)
  | target@(WrappedExpr.index Kind.memory _ path index) =>
      isSimple path ∧ isSimple index ∧
        (isPrimitive target ∨ isIdentity target)
  | _ => False

  def isComplexStorageDeleteTarget : WrappedExpr -> Prop
  | WrappedExpr.field Kind.storage _ path _ => isComplex path
  | WrappedExpr.index Kind.storage _ path index =>
      isComplex path ∨ (isSimple path ∧ isComplex index)
  | WrappedExpr.pushPlace path =>
      path.kind = Kind.storage ∧ isComplex path
  | _ => False

  def isComplexMemoryDeleteTarget : WrappedExpr -> Prop
  | WrappedExpr.field Kind.memory _ path _ => isComplex path
  | WrappedExpr.index Kind.memory _ path index =>
      isComplex path ∨ (isSimple path ∧ isComplex index)
  | _ => False

  def aliasField (kind : Kind) (ty : Ty) (name : Name) : Field :=
  match kind, ty with
  | Kind.storage, Ty.ref ref => Field.identity name ref (some StorageOrigin.local)
  | Kind.memory, Ty.ref ref => Field.identity name ref
  | _, _ => Field.primitive name ty

  def aliasExpr (kind : Kind) (ty : Ty) (name : Name) : WrappedExpr :=
  WrappedExpr.var kind ty (aliasField kind ty name)

  def aliasPlace (kind : Kind) (ty : Ty) (name : Name) : PlaceExpr :=
  PlaceExpr.var kind ty (aliasField kind ty name)

  /-- The declaration kind of the `pv` value capture. A primitive-typed
  memory read is captured into a typed value temporary (KeY
  `\newTypeOf(pv, nse)` gives `pv` the primitive type, so `T pv = nse;`
  is a value declaration): a memory declaration can only bind an object
  identity. Identity-typed captures keep the expression's own kind. -/
  def valueCaptureKind (expr : WrappedExpr) : Kind :=
  if expr.isMemory && expr.ty.isPrimitive then Kind.stack
  else expr.kind

  def valueAlias (expr : WrappedExpr) : WrappedExpr :=
  aliasExpr (valueCaptureKind expr) expr.ty valueAliasName

  def indexAlias (expr : WrappedExpr) : WrappedExpr :=
  aliasExpr Kind.stack expr.ty indexAliasName

  def storageAlias (expr : WrappedExpr) : WrappedExpr :=
  aliasExpr Kind.storage expr.ty storagePathAliasName

  def memoryAlias (expr : WrappedExpr) : WrappedExpr :=
  aliasExpr Kind.memory expr.ty memoryPathAliasName

  def capture (kind : Kind) (name : Name) (expr : WrappedExpr) : Stmt :=
  match kind with
  | Kind.storage => Stmt.storagePlaceAlias expr.ty name expr
  | Kind.memory => Stmt.memoryDecl expr.ty name (some expr)
  | Kind.stack => Stmt.stackDecl expr.ty name (some expr)

  def captureValue (expr : WrappedExpr) : Stmt :=
  capture (valueCaptureKind expr) valueAliasName expr

  /-- KeY `Variable[name=value]`: a simple stack ("value") variable — the calculus's
  read target `v`.  Definitionally `isSe`, but kept as its own `def` with the
  conjunction spelled out: the `simp only [Rules.isStackVar, Rules.isStack,
  Rules.isSimple]` lists in `Uniqueness.lean` take it apart in one step. -/
  def isStackVar (expr : WrappedExpr) : Prop :=
  isStack expr ∧ isSimple expr

  /-- Hoist an operand into the fresh value variable `pv` as a stack
  declaration (KeY `\newTypeOf(pv, ...)` capture step). -/
  def captureStackValue (expr : WrappedExpr) : Stmt :=
  capture Kind.stack valueAliasName expr

  /-- RHS shapes claimed by the `*ValueRhsCapture` trio (KeY
  `NonSimpleExpression[primitive]` restricted to the cells no other Lean
  rule covers): operator expressions, except an arithmetic operator over
  simple operands, which `binopUnfoldResult` already captures. -/
  def valueRhsCaptureRhs (rhs : WrappedExpr) : Prop :=
  match rhs with
  | WrappedExpr.binop op l r =>
      ¬ (op.isArith = true ∧ isSimple l ∧ isSimple r)
  | WrappedExpr.unop _ _ => True
  | WrappedExpr.incDec _ _ => True
  | _ => False

  def stackValueAlias (expr : WrappedExpr) : WrappedExpr :=
  aliasExpr Kind.stack expr.ty valueAliasName

  /-- Read back the frozen value operand.  Forced to `Kind.stack`, like
  `stackValueAlias`: `valueCaptureKind` would classify a primitive *storage*
  root such as `total` as `Kind.storage`, and the resulting
  `storagePlaceAlias` binds a *path*, so a later read would see the new value
  and the freeze would be a no-op. -/
  def rhsValueAlias (expr : WrappedExpr) : WrappedExpr :=
  aliasExpr Kind.stack expr.ty rhsValueAliasName

  /-- Freeze the value operand into `rv` as a stack declaration
  (`T rv = e;`), snapshotting it before any target capture runs. -/
  def captureRhsValue (expr : WrappedExpr) : Stmt :=
  capture Kind.stack rhsValueAliasName expr

  /-- Find the leftmost complex call argument; return it together with
  the argument list where it is replaced by the `pv` alias (the
  `functionCallArgCapture` residual data). -/
  def captureFirstComplexArg :
    List WrappedExpr -> Option (WrappedExpr × List WrappedExpr)
  | [] => none
  | a :: rest =>
      if a.complex then some (a, stackValueAlias a :: rest)
      else
        match captureFirstComplexArg rest with
        | some (c, rest') => some (c, a :: rest')
        | none => none

  theorem captureFirstComplexArg_isSome (args : List WrappedExpr) :
    (captureFirstComplexArg args).isSome = args.any (·.complex) := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
      by_cases h : a.complex = true
      · simp [captureFirstComplexArg, h]
      · simp only [Bool.not_eq_true] at h
        simp only [captureFirstComplexArg, h, List.any_cons, Bool.false_or]
        cases hr : captureFirstComplexArg rest with
        | none => simpa [hr] using ih
        | some x => simpa [hr] using ih

  def captureStoragePath (expr : WrappedExpr) : Stmt :=
  capture Kind.storage storagePathAliasName expr

  def captureMemoryPath (expr : WrappedExpr) : Stmt :=
  capture Kind.memory memoryPathAliasName expr

  def captureIndex (expr : WrappedExpr) : Stmt :=
  capture Kind.stack indexAliasName expr

  def fieldFromAlias
    (kind : Kind) (aliasName : Name) (ty : Ty) (base : WrappedExpr)
    (field : Field) : PlaceExpr :=
  PlaceExpr.field kind ty (aliasExpr kind base.ty aliasName) field

  def indexFromAlias
    (kind : Kind) (aliasName : Name) (ty : Ty) (base index : WrappedExpr) :
    PlaceExpr :=
  PlaceExpr.index kind ty (aliasExpr kind base.ty aliasName) index

  def asPlace? (expr : WrappedExpr) : Option PlaceExpr :=
  if h : expr.assignable = true then
    some ⟨expr, h⟩
  else
    none

  /-! ### Writing a rule's goals

  Eight words cover the whole table: `unfoldGoal` is every rewriting rule,
  `terminalGoal` every unguarded update, `splitGoals` every guarded pair, and
  the rest are shapes that occur often enough to name. -/

  /-- The single goal of a rewriting rule: no guard, no update, a residual
  program.  `StepEffect.block` reads exactly this back, which is why the rest
  of the development did not notice the change. -/
  def unfoldGoal (b : Block) : List RuleGoal :=
    [ { residual := RuleResidual.prog [] b } ]

  /-- The single goal of an unguarded terminal rule: an update, and nothing
  left to run. -/
  def terminalGoal (upd : UpdTerm) : List RuleGoal :=
    [ { residual := RuleResidual.prog upd [] } ]

  /-- KeY's guarded pair — `\if(φ) \then({u}…) \else(revert(); …)`, and the
  `"inBounds"`/`"outOfBounds"` spelling of the same thing, which differs only
  in whether the guard is written as an implication or `\add`ed to the sequent.
  `premises` are the operands that must be read before the guard can be
  decided, in the interpreter's order: on `arr[i] = 1 / 0` with `i` out of
  bounds the right-hand side faults first, and a guard that tested the bounds
  in the pre-state would call that a revert. -/
  def splitGoals (φ : SideFormula) (premises : List Premise) (upd : UpdTerm) :
      List RuleGoal :=
    [ { label := "holds", guard := { premises := premises, formula := φ }
        residual := RuleResidual.prog upd [] },
      { label := "fails"
        guard := { premises := premises, formula := SideFormula.neg φ }
        residual := RuleResidual.reverting } ]

  /-- A goal with no program left: KeY's `\replacewith(φ)`. -/
  def obligation (label : String) (mode : CaseMode) (upd : UpdTerm)
      (φ : SideFormula) : RuleGoal :=
    { label := label, mode := mode, residual := RuleResidual.obligation upd φ }

  /-- `revert();`: KeY states it as two taclets, `revertBox`'s
  `\replacewith(true)` and `revertDiamond`'s `\replacewith(false)`.  Both Lean
  twins carry both goals and let their own `mode` pick — keeping the data
  symmetric is what lets `CandidateStep.revert_twin` stay `rfl`. -/
  def revertGoals : List RuleGoal :=
    [ obligation "box" CaseMode.box [] (SideFormula.const true),
      obligation "diamond" CaseMode.diamond [] (SideFormula.const false) ]

  /-- `assert(se);` — KeY's `"Holds"`/`"Violated"` pair.  Note what it is *not*:
  there is no reverting goal, because KeY's violated branch is an obligation to
  prove the condition, not a revert.  The Lean interpreter reverts instead, and
  that is the one place where a rule of this table is *stronger* than the
  program it describes — `Update/SolcDelta.lean`'s `assertViolatedReverts` row,
  with `assertSimple_box_gap` as the witness. -/
  def assertGoals (c : WrappedExpr) : List RuleGoal :=
    [ { label := "Holds", guard := { formula := SideFormula.holds c }
        residual := RuleResidual.prog [] [] },
      obligation "Violated" CaseMode.both [] (SideFormula.holds c) ]

  /-- The name a variable expression carries; `""` on anything else, which no
  update ever reaches (a stack target is a variable by `WrappedExpr.assignable`
  and the rules' `isStack` condition). -/
  def varName : WrappedExpr -> Name
    | WrappedExpr.var _ _ fld => fld.name
    | _ => ""

  /-- Write a value to a target, wherever it lives.  KeY picks between
  `v := …`, `storage := save(…)` and `memory := write(…)` by the schema
  variable's sort; here the target's `kind` says it. -/
  def writeBack (target : WrappedExpr) (t : Sym) : UpdElem :=
    match target.kind with
    | Kind.stack => UpdElem.bind (varName target) (BindRhs.val t)
    | Kind.storage => UpdElem.storage (StorageUpd.save target t)
    | Kind.memory => UpdElem.heap (HeapUpd.write target t)

  /-- `t op= se;` — one write-back of `t op se`, computed at the target's type
  (KeY `storage{Root,Field,Index}{Add,…}Assign` and their local and memory
  twins).  `/=` and `%=` carry KeY's divisor guard; for every other operator
  the guard is `true` and the reverting goal beside it is dead.  Writing it
  that way rather than branching on the operator is what keeps
  `StepEffect.block` reducible without knowing which operator it is —
  `Wp.isTerminal_of_hasUpdate` is a `rfl` per rule, not per instance. -/
  def compoundGoals (op : BinOp) (target : WrappedExpr) (value : WrappedExpr) :
      List RuleGoal :=
    splitGoals (if op.needsGuard then SideFormula.nonZero value
                else SideFormula.const true)
      [Premise.read (Sym.read value)]
      [ writeBack target (Sym.combined op target value) ]

  /-- The same, at an *array* receiver, where KeY stacks the bounds split on
  top (`storageIndexArrayOpAssign`, `memoryIndexArrayOpAssign`).  A mapping
  receiver satisfies `inBounds` vacuously, which is what lets the two Lean
  index rules merge KeY's array and mapping families. -/
  def compoundIndexGoals (op : BinOp) (target : WrappedExpr)
      (value : WrappedExpr) : List RuleGoal :=
    splitGoals (SideFormula.inBounds target)
      [Premise.read (Sym.read value), Premise.resolve target]
      [ writeBack target (Sym.combined op target value) ]

  /-- `v = ++t;` / `v = t--;` as one parallel update: `{t := t + 1 || v := t + 1}`
  for a prefix operator, `{t := t + 1 || v := t}` for a postfix one.  Both
  elements read the pre-state, which is what makes the two spellings differ by
  the value alone; `rhs` is the whole `incDec` node, and `Update/Eval.lean`
  reads the operator off it. -/
  def incDecGoals (v : WrappedExpr) (rhs : WrappedExpr) : List RuleGoal :=
    terminalGoal [ UpdElem.bumpOf rhs, writeBack v (Sym.read rhs) ]

  /-- Record which KeY taclet a rule transcribes, and take the taclet's
  `\heuristics` from `KeyTaclets.lean` rather than repeating it here. -/
  @[reducible] def withOrigin (o : KeyOrigin) (e : StepEffect) : StepEffect :=
    { e with origin := o
             heuristics := (o.taclets.map KeyTaclet.heuristic).eraseDups }

  def assignEffect
    (cond : PlaceExpr -> WrappedExpr -> Prop)
    (goals : (lhs : PlaceExpr) -> (rhs : WrappedExpr) -> cond lhs rhs -> List RuleGoal) :
    StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.assign lhs rhs => cond lhs rhs
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case assign lhs rhs => exact goals lhs rhs hcond }

  def storageDeclEffect
    (cond : Ty -> Name -> Option WrappedExpr -> Prop)
    (goals : (ty : Ty) -> (name : Name) -> (init : Option WrappedExpr) ->
      cond ty name init -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.storageDecl ty name init => cond ty name init
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case storageDecl ty name init => exact goals ty name init hcond }

  def memoryDeclEffect
    (cond : Ty -> Name -> Option WrappedExpr -> Prop)
    (goals : (ty : Ty) -> (name : Name) -> (init : Option WrappedExpr) ->
      cond ty name init -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.memoryDecl ty name init => cond ty name init
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case memoryDecl ty name init => exact goals ty name init hcond }

  def stackDeclEffect
    (cond : Ty -> Name -> Option WrappedExpr -> Prop)
    (goals : (ty : Ty) -> (name : Name) -> (init : Option WrappedExpr) ->
      cond ty name init -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.stackDecl ty name init => cond ty name init
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case stackDecl ty name init => exact goals ty name init hcond }

  def compoundAssignEffect
    (cond : BinOp -> PlaceExpr -> WrappedExpr -> Prop)
    (goals : (op : BinOp) -> (lhs : PlaceExpr) -> (rhs : WrappedExpr) ->
      cond op lhs rhs -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.compoundAssign op lhs rhs => cond op lhs rhs
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case compoundAssign op lhs rhs => exact goals op lhs rhs hcond }

  def exprEffect
    (cond : WrappedExpr -> Prop)
    (goals : (expr : WrappedExpr) -> cond expr -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.expr expr => cond expr
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case expr expr => exact goals expr hcond }

  def assertEffect
    (cond : WrappedExpr -> Prop)
    (goals : (c : WrappedExpr) -> cond c -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.assertStmt c => cond c
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case assertStmt c => exact goals c hcond }

  def callEffect
    (cond : Option PlaceExpr -> Name -> List WrappedExpr -> Prop)
    (goals : (res : Option PlaceExpr) -> (fn : Name) ->
      (args : List WrappedExpr) -> cond res fn args -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.callStmt res fn args => cond res fn args
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case callStmt res fn args => exact goals res fn args hcond }

  def requireEffect
    (cond : WrappedExpr -> Prop)
    (goals : (c : WrappedExpr) -> cond c -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.requireStmt c => cond c
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case requireStmt c => exact goals c hcond }

  def iteEffect
    (cond : WrappedExpr -> Block -> Block -> Prop)
    (goals : (c : WrappedExpr) -> (thn els : Block) ->
      cond c thn els -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.ite c thn els => cond c thn els
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case ite c thn els => exact goals c thn els hcond }

  def transferEffect
    (cond : WrappedExpr -> WrappedExpr -> Prop)
    (goals : (recipient amount : WrappedExpr) ->
      cond recipient amount -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.transfer recipient amount => cond recipient amount
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case transfer recipient amount => exact goals recipient amount hcond }

  /-- `revert();` — the one rule with no schema variables at all, so its goals
  are a list rather than a function of the statement it matched. -/
  def revertEffect (mode : CaseMode) (goals : List RuleGoal) : StepEffect :=
  withOrigin (KeyOrigin.merged [KeyTaclet.revertBox, KeyTaclet.revertDiamond])
  { mode := fun _ => mode
    cond := fun stmt =>
      match stmt with
      | Stmt.revert _ => True
      | _ => False
    goals := fun _ _ => goals }

  def deleteEffect
    (cond : PlaceExpr -> Prop)
    (goals : (target : PlaceExpr) -> cond target -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.delete target => cond target
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case «delete» target => exact goals target hcond }

  def pushEffect
    (cond : PlaceExpr -> Option WrappedExpr -> Prop)
    (goals : (target : PlaceExpr) -> (value : Option WrappedExpr) ->
      cond target value -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.push target value => cond target value
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case push target value => exact goals target value hcond }

  /-- `p = e;` where `p` is a push *place*: the sugar `Stmt.pushAssign`, whose
  only rule lowers it to the `Stmt.assign` the interpreter delegates to. -/
  def pushAssignEffect
    (cond : PlaceExpr -> WrappedExpr -> Prop)
    (goals : (target : PlaceExpr) -> (value : WrappedExpr) ->
      cond target value -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.pushAssign target value => cond target value
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case pushAssign target value => exact goals target value hcond }

  def pushFieldAssignEffect
    (cond : PlaceExpr -> Field -> WrappedExpr -> Prop)
    (goals : (target : PlaceExpr) -> (field : Field) -> (value : WrappedExpr) ->
      cond target field value -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.pushFieldAssign target field value => cond target field value
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case pushFieldAssign target field value => exact goals target field value hcond }

  /-- `T storage sp = p;` — the scratch *path* binding a capture leaves behind,
  which is a declaration of an alias rather than of a variable. -/
  def storagePlaceAliasEffect
    (cond : Ty -> Name -> WrappedExpr -> Prop)
    (goals : (ty : Ty) -> (name : Name) -> (init : WrappedExpr) ->
      cond ty name init -> List RuleGoal) : StepEffect :=
  { cond := fun stmt =>
      match stmt with
      | Stmt.storagePlaceAlias ty name init => cond ty name init
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case storagePlaceAlias ty name init => exact goals ty name init hcond }

  def popEffect
    (mode : CaseMode)
    (cond : PlaceExpr -> Prop)
    (goals : (target : PlaceExpr) -> cond target -> List RuleGoal) : StepEffect :=
  { mode := fun _ => mode
    cond := fun stmt =>
      match stmt with
      | Stmt.pop target => cond target
      | _ => False
    goals := fun stmt hcond => by
      cases stmt <;> simp at hcond
      case pop target => exact goals target hcond }

  def withMode (mode : CaseMode) (effect : StepEffect) : StepEffect :=
  { effect with mode := fun _ => mode }

  /-- Prefix a *target*-capture residual with the freeze of the value operand
  that solc's RHS-first assignment order demands (`Semantics.execAssignNested`
  runs `rhsToSVal` before `resolveLoc`).  Without it a target capture whose
  path or index is impure runs its side effects *before* the value is read,
  and the rule disagrees with the interpreter — `values[i++] = i`,
  `Counterexamples/EvaluationOrder.lean`.

  Only a **primitive** value is frozen.  Binding a reference is aliasing, not
  a read, so the declaration would not snapshot the content that `rhsToSVal`
  reads off a storage source; the reference case keeps the plain residual and
  its non-interference side condition.  KeY splits the same way, on
  `SimpleExpression[primitive]` versus `[reference]`. -/
  def freezeRhs (rhs : WrappedExpr) (body : WrappedExpr -> Block) : Block :=
  if rhs.ty.isPrimitive then captureRhsValue rhs :: body (rhsValueAlias rhs)
  else body rhs

  def fieldWriteResolveBlock
    (kind : Kind) (aliasName : Name) (lhsTy : Ty) (path : WrappedExpr)
    (field : Field) (rhs : WrappedExpr) : Block :=
  let captureStmt :=
    match kind with
    | Kind.storage => captureStoragePath path
    | Kind.memory => captureMemoryPath path
    | Kind.stack => capture Kind.stack aliasName path
  freezeRhs rhs fun v =>
    [ captureStmt, Stmt.assign (fieldFromAlias kind aliasName lhsTy path field) v ]

  /-- The index-access twin.  A *complex* index is captured here as well, so
  this rule consumes the whole target in one step: were the index left in
  place, the left-snd rule would fire next on an already-frozen value and
  emit the degenerate `rv = rv;`, whose freshness side condition no soundness
  theorem can discharge (Lean reserves fixed alias names where KeY generates
  fresh ones). -/
  def indexWriteResolveBlock
    (kind : Kind) (aliasName : Name) (lhsTy : Ty) (path index rhs : WrappedExpr) :
    Block :=
  let captureStmt :=
    match kind with
    | Kind.storage => captureStoragePath path
    | Kind.memory => captureMemoryPath path
    | Kind.stack => capture Kind.stack aliasName path
  freezeRhs rhs fun v =>
    if index.complex then
      [ captureStmt, captureIndex index,
        Stmt.assign
          (indexFromAlias kind aliasName lhsTy path (indexAlias index)) v ]
    else
      [ captureStmt, Stmt.assign (indexFromAlias kind aliasName lhsTy path index) v ]

  def fieldReadResolveBlock
    (kind : Kind) (aliasName : Name) (lhs : PlaceExpr) (rhsTy : Ty)
    (path : WrappedExpr) (field : Field) : Block :=
  let captureStmt :=
    match kind with
    | Kind.storage => captureStoragePath path
    | Kind.memory => captureMemoryPath path
    | Kind.stack => capture Kind.stack aliasName path
  [ captureStmt,
    Stmt.assign lhs
      (WrappedExpr.field kind rhsTy (aliasExpr kind path.ty aliasName) field) ]

  def indexReadResolveBlock
    (kind : Kind) (aliasName : Name) (lhs : PlaceExpr) (rhsTy : Ty)
    (path index : WrappedExpr) : Block :=
  let captureStmt :=
    match kind with
    | Kind.storage => captureStoragePath path
    | Kind.memory => captureMemoryPath path
    | Kind.stack => capture Kind.stack aliasName path
  [ captureStmt,
    Stmt.assign lhs
      (WrappedExpr.index kind rhsTy (aliasExpr kind path.ty aliasName) index) ]

  def captureAssignBlock (lhs : PlaceExpr) (rhs : WrappedExpr) : Block :=
  [ captureValue rhs, Stmt.assign lhs (valueAlias rhs) ]

  /-- The left-snd unfold: a simple path with a complex index.  It is the
  left-fst residual at a path that happens to be simple — and it has to be.
  `resolveLoc` resolves the base **before** the index
  (`Semantics.resolveLoc`), so a residual that captured only the index would
  read the path after the index's side effects had run; capturing the path
  too pins it, exactly as the interpreter does.  With a simple path the
  capture is cheap, and it is what lets the soundness theorem drop
  `pureExpr index`. -/
  def captureIndexTargetBlock
    (kind : Kind) (lhsTy : Ty) (path index rhs : WrappedExpr) : Block :=
  indexWriteResolveBlock kind
    (match kind with
     | Kind.memory => memoryPathAliasName
     | _ => storagePathAliasName)
    lhsTy path index rhs

  def storageDeleteComplexTargetBlock (target : WrappedExpr)
    (h : isComplexStorageDeleteTarget target) : Block :=
  match target, h with
  | WrappedExpr.field Kind.storage ty path field, _ =>
      [ captureStoragePath path,
        Stmt.delete
          (fieldFromAlias Kind.storage storagePathAliasName ty path field) ]
  | WrappedExpr.index Kind.storage ty path index, _ =>
      if path.complex then
        [ captureStoragePath path,
          Stmt.delete
            (indexFromAlias Kind.storage storagePathAliasName ty path index) ]
      else
        [ captureIndex index,
          Stmt.delete
            (PlaceExpr.index Kind.storage ty path (indexAlias index)) ]
  | WrappedExpr.pushPlace path, _ =>
      [ captureStoragePath path,
        Stmt.delete
          (PlaceExpr.pushPlace
            (aliasPlace Kind.storage path.ty storagePathAliasName)) ]

  def memoryDeleteComplexTargetBlock (target : WrappedExpr)
    (h : isComplexMemoryDeleteTarget target) : Block :=
  match target, h with
  | WrappedExpr.field Kind.memory ty path field, _ =>
      [ captureMemoryPath path,
        Stmt.delete
          (fieldFromAlias Kind.memory memoryPathAliasName ty path field) ]
  | WrappedExpr.index Kind.memory ty path index, _ =>
      if path.complex then
        [ captureMemoryPath path,
          Stmt.delete
            (indexFromAlias Kind.memory memoryPathAliasName ty path index) ]
      else
        [ captureIndex index,
          Stmt.delete
            (PlaceExpr.index Kind.memory ty path (indexAlias index)) ]

  /-! ### Which taclet each operator instance is

  KeY names one taclet per operator; Lean has one rule per family, indexed by
  the operator.  These are the index — total functions, so a KeY-absent
  instance (`**=`, and the memory arithmetic that landed upstream after
  `e67a0d7c48`) says `leanOnly` rather than being forgotten. -/

  def localCompoundOrigin : BinOp -> KeyOrigin
    | .add => KeyOrigin.taclet KeyTaclet.localAddAssign
    | .sub => KeyOrigin.taclet KeyTaclet.localSubAssign
    | .mul => KeyOrigin.taclet KeyTaclet.localMulAssign
    | .pow => KeyOrigin.leanOnly
    | .div => KeyOrigin.taclet KeyTaclet.localDivAssign
    | .mod => KeyOrigin.taclet KeyTaclet.localModAssign
    | .lt => KeyOrigin.leanOnly
    | .gt => KeyOrigin.leanOnly
    | .le => KeyOrigin.leanOnly
    | .ge => KeyOrigin.leanOnly
    | .eqB => KeyOrigin.leanOnly
    | .neB => KeyOrigin.leanOnly
    | .and => KeyOrigin.leanOnly
    | .or => KeyOrigin.leanOnly

  def storageRootCompoundOrigin : BinOp -> KeyOrigin
    | .add => KeyOrigin.taclet KeyTaclet.storageRootAddAssign
    | .sub => KeyOrigin.taclet KeyTaclet.storageRootSubAssign
    | .mul => KeyOrigin.taclet KeyTaclet.storageRootMulAssign
    | .pow => KeyOrigin.leanOnly
    | .div => KeyOrigin.taclet KeyTaclet.storageRootDivAssign
    | .mod => KeyOrigin.taclet KeyTaclet.storageRootModAssign
    | .lt => KeyOrigin.leanOnly
    | .gt => KeyOrigin.leanOnly
    | .le => KeyOrigin.leanOnly
    | .ge => KeyOrigin.leanOnly
    | .eqB => KeyOrigin.leanOnly
    | .neB => KeyOrigin.leanOnly
    | .and => KeyOrigin.leanOnly
    | .or => KeyOrigin.leanOnly

  def storageFieldCompoundOrigin : BinOp -> KeyOrigin
    | .add => KeyOrigin.taclet KeyTaclet.storageFieldAddAssign
    | .sub => KeyOrigin.taclet KeyTaclet.storageFieldSubAssign
    | .mul => KeyOrigin.taclet KeyTaclet.storageFieldMulAssign
    | .pow => KeyOrigin.leanOnly
    | .div => KeyOrigin.taclet KeyTaclet.storageFieldDivAssign
    | .mod => KeyOrigin.taclet KeyTaclet.storageFieldModAssign
    | .lt => KeyOrigin.leanOnly
    | .gt => KeyOrigin.leanOnly
    | .le => KeyOrigin.leanOnly
    | .ge => KeyOrigin.leanOnly
    | .eqB => KeyOrigin.leanOnly
    | .neB => KeyOrigin.leanOnly
    | .and => KeyOrigin.leanOnly
    | .or => KeyOrigin.leanOnly

  def storageIndexCompoundOrigin : BinOp -> KeyOrigin
    | .add => KeyOrigin.merged [KeyTaclet.storageIndexMappingAddAssign, KeyTaclet.storageIndexArrayAddAssign]
    | .sub => KeyOrigin.merged [KeyTaclet.storageIndexMappingSubAssign, KeyTaclet.storageIndexArraySubAssign]
    | .mul => KeyOrigin.merged [KeyTaclet.storageIndexMappingMulAssign, KeyTaclet.storageIndexArrayMulAssign]
    | .pow => KeyOrigin.leanOnly
    | .div => KeyOrigin.merged [KeyTaclet.storageIndexMappingDivAssign, KeyTaclet.storageIndexArrayDivAssign]
    | .mod => KeyOrigin.merged [KeyTaclet.storageIndexMappingModAssign, KeyTaclet.storageIndexArrayModAssign]
    | .lt => KeyOrigin.leanOnly
    | .gt => KeyOrigin.leanOnly
    | .le => KeyOrigin.leanOnly
    | .ge => KeyOrigin.leanOnly
    | .eqB => KeyOrigin.leanOnly
    | .neB => KeyOrigin.leanOnly
    | .and => KeyOrigin.leanOnly
    | .or => KeyOrigin.leanOnly

  def storageFieldCompoundUnfoldOrigin : BinOp -> KeyOrigin
    | .add => KeyOrigin.taclet KeyTaclet.storageFieldAddAssign_unfold_leftFst
    | .sub => KeyOrigin.taclet KeyTaclet.storageFieldSubAssign_unfold_leftFst
    | .mul => KeyOrigin.taclet KeyTaclet.storageFieldMulAssign_unfold_leftFst
    | .pow => KeyOrigin.leanOnly
    | .div => KeyOrigin.taclet KeyTaclet.storageFieldDivAssign_unfold_leftFst
    | .mod => KeyOrigin.taclet KeyTaclet.storageFieldModAssign_unfold_leftFst
    | .lt => KeyOrigin.leanOnly
    | .gt => KeyOrigin.leanOnly
    | .le => KeyOrigin.leanOnly
    | .ge => KeyOrigin.leanOnly
    | .eqB => KeyOrigin.leanOnly
    | .neB => KeyOrigin.leanOnly
    | .and => KeyOrigin.leanOnly
    | .or => KeyOrigin.leanOnly

  def storageIndexCompoundUnfoldOrigin : BinOp -> KeyOrigin
    | .add => KeyOrigin.taclet KeyTaclet.storageIndexAddAssign_unfold_leftFst
    | .sub => KeyOrigin.taclet KeyTaclet.storageIndexSubAssign_unfold_leftFst
    | .mul => KeyOrigin.taclet KeyTaclet.storageIndexMulAssign_unfold_leftFst
    | .pow => KeyOrigin.leanOnly
    | .div => KeyOrigin.taclet KeyTaclet.storageIndexDivAssign_unfold_leftFst
    | .mod => KeyOrigin.taclet KeyTaclet.storageIndexModAssign_unfold_leftFst
    | .lt => KeyOrigin.leanOnly
    | .gt => KeyOrigin.leanOnly
    | .le => KeyOrigin.leanOnly
    | .ge => KeyOrigin.leanOnly
    | .eqB => KeyOrigin.leanOnly
    | .neB => KeyOrigin.leanOnly
    | .and => KeyOrigin.leanOnly
    | .or => KeyOrigin.leanOnly

  def storageRootIncDecOrigin : IncDec -> KeyOrigin
    | .preInc => KeyOrigin.taclet KeyTaclet.storageRootPreincrement
    | .preDec => KeyOrigin.taclet KeyTaclet.storageRootPredecrement
    | .postInc => KeyOrigin.taclet KeyTaclet.storageRootPostincrement
    | .postDec => KeyOrigin.taclet KeyTaclet.storageRootPostdecrement

  def storageFieldIncDecOrigin : IncDec -> KeyOrigin
    | .preInc => KeyOrigin.taclet KeyTaclet.storageFieldPreincrement
    | .preDec => KeyOrigin.taclet KeyTaclet.storageFieldPredecrement
    | .postInc => KeyOrigin.taclet KeyTaclet.storageFieldPostincrement
    | .postDec => KeyOrigin.taclet KeyTaclet.storageFieldPostdecrement

  def storageIndexIncDecOrigin : IncDec -> KeyOrigin
    | .preInc => KeyOrigin.merged [KeyTaclet.storageIndexMappingPreincrement, KeyTaclet.storageIndexArrayPreincrement]
    | .preDec => KeyOrigin.merged [KeyTaclet.storageIndexMappingPredecrement, KeyTaclet.storageIndexArrayPredecrement]
    | .postInc => KeyOrigin.merged [KeyTaclet.storageIndexMappingPostincrement, KeyTaclet.storageIndexArrayPostincrement]
    | .postDec => KeyOrigin.merged [KeyTaclet.storageIndexMappingPostdecrement, KeyTaclet.storageIndexArrayPostdecrement]

  def storageFieldIncDecUnfoldOrigin : IncDec -> KeyOrigin
    | .preInc => KeyOrigin.taclet KeyTaclet.storageFieldPreincrement_unfold_leftFst
    | .preDec => KeyOrigin.taclet KeyTaclet.storageFieldPredecrement_unfold_leftFst
    | .postInc => KeyOrigin.taclet KeyTaclet.storageFieldPostincrement_unfold_leftFst
    | .postDec => KeyOrigin.taclet KeyTaclet.storageFieldPostdecrement_unfold_leftFst

  def storageIndexIncDecUnfoldOrigin : IncDec -> KeyOrigin
    | .preInc => KeyOrigin.taclet KeyTaclet.storageIndexPreincrement_unfold_leftFst
    | .preDec => KeyOrigin.taclet KeyTaclet.storageIndexPredecrement_unfold_leftFst
    | .postInc => KeyOrigin.taclet KeyTaclet.storageIndexPostincrement_unfold_leftFst
    | .postDec => KeyOrigin.taclet KeyTaclet.storageIndexPostdecrement_unfold_leftFst

  def storageRootIncDecAssignOrigin : IncDec -> KeyOrigin
    | .preInc => KeyOrigin.taclet KeyTaclet.storageRootPreincrementAssignment
    | .preDec => KeyOrigin.taclet KeyTaclet.storageRootPredecrementAssignment
    | .postInc => KeyOrigin.taclet KeyTaclet.storageRootPostincrementAssignment
    | .postDec => KeyOrigin.taclet KeyTaclet.storageRootPostdecrementAssignment

  def storageFieldIncDecAssignOrigin : IncDec -> KeyOrigin
    | .preInc => KeyOrigin.taclet KeyTaclet.storageFieldPreincrementAssignment
    | .preDec => KeyOrigin.taclet KeyTaclet.storageFieldPredecrementAssignment
    | .postInc => KeyOrigin.taclet KeyTaclet.storageFieldPostincrementAssignment
    | .postDec => KeyOrigin.taclet KeyTaclet.storageFieldPostdecrementAssignment

  def storageIndexIncDecAssignOrigin : IncDec -> KeyOrigin
    | .preInc => KeyOrigin.merged [KeyTaclet.storageIndexMappingPreincrementAssignment, KeyTaclet.storageIndexArrayPreincrementAssignment]
    | .preDec => KeyOrigin.merged [KeyTaclet.storageIndexMappingPredecrementAssignment, KeyTaclet.storageIndexArrayPredecrementAssignment]
    | .postInc => KeyOrigin.merged [KeyTaclet.storageIndexMappingPostincrementAssignment, KeyTaclet.storageIndexArrayPostincrementAssignment]
    | .postDec => KeyOrigin.merged [KeyTaclet.storageIndexMappingPostdecrementAssignment, KeyTaclet.storageIndexArrayPostdecrementAssignment]

  def binopUnfoldLeftOrigin : BinOp -> KeyOrigin
    | .add => KeyOrigin.taclet KeyTaclet.addition_unfold_left
    | .sub => KeyOrigin.taclet KeyTaclet.subtraction_unfold_left
    | .mul => KeyOrigin.taclet KeyTaclet.multiplication_unfold_left
    | .pow => KeyOrigin.taclet KeyTaclet.power_unfold_left
    | .div => KeyOrigin.taclet KeyTaclet.division_unfold_left
    | .mod => KeyOrigin.taclet KeyTaclet.modulo_unfold_left
    | .lt => KeyOrigin.taclet KeyTaclet.lessThanCaptureLhs
    | .gt => KeyOrigin.taclet KeyTaclet.greaterThanCaptureLhs
    | .le => KeyOrigin.taclet KeyTaclet.lessEqualCaptureLhs
    | .ge => KeyOrigin.taclet KeyTaclet.greaterEqualCaptureLhs
    | .eqB => KeyOrigin.taclet KeyTaclet.boolEqualityCaptureLhs
    | .neB => KeyOrigin.taclet KeyTaclet.boolInequalityCaptureLhs
    | .and => KeyOrigin.taclet KeyTaclet.logicalAndCaptureLhs
    | .or => KeyOrigin.taclet KeyTaclet.logicalOrCaptureLhs

  def binopUnfoldRightOrigin : BinOp -> KeyOrigin
    | .add => KeyOrigin.taclet KeyTaclet.addition_unfold_right
    | .sub => KeyOrigin.taclet KeyTaclet.subtraction_unfold_right
    | .mul => KeyOrigin.taclet KeyTaclet.multiplication_unfold_right
    | .pow => KeyOrigin.taclet KeyTaclet.power_unfold_right
    | .div => KeyOrigin.taclet KeyTaclet.division_unfold_right
    | .mod => KeyOrigin.taclet KeyTaclet.modulo_unfold_right
    | .lt => KeyOrigin.taclet KeyTaclet.lessThanCaptureRhs
    | .gt => KeyOrigin.taclet KeyTaclet.greaterThanCaptureRhs
    | .le => KeyOrigin.taclet KeyTaclet.lessEqualCaptureRhs
    | .ge => KeyOrigin.taclet KeyTaclet.greaterEqualCaptureRhs
    | .eqB => KeyOrigin.taclet KeyTaclet.boolEqualityCaptureRhs
    | .neB => KeyOrigin.taclet KeyTaclet.boolInequalityCaptureRhs
    | .and => KeyOrigin.leanOnly
    | .or => KeyOrigin.leanOnly

  def binopAssignmentOrigin : BinOp -> KeyOrigin
    | .add => KeyOrigin.taclet KeyTaclet.additionAssignment
    | .sub => KeyOrigin.taclet KeyTaclet.subtractionAssignment
    | .mul => KeyOrigin.taclet KeyTaclet.multiplicationAssignment
    | .pow => KeyOrigin.taclet KeyTaclet.powerAssignment
    | .div => KeyOrigin.taclet KeyTaclet.divisionAssignment
    | .mod => KeyOrigin.taclet KeyTaclet.moduloAssignment
    | .lt => KeyOrigin.taclet KeyTaclet.lessThanAssignment
    | .gt => KeyOrigin.taclet KeyTaclet.greaterThanAssignment
    | .le => KeyOrigin.taclet KeyTaclet.lessEqualAssignment
    | .ge => KeyOrigin.taclet KeyTaclet.greaterEqualAssignment
    | .eqB => KeyOrigin.taclet KeyTaclet.boolEqualityAssignment
    | .neB => KeyOrigin.taclet KeyTaclet.boolInequalityAssignment
    | .and => KeyOrigin.taclet KeyTaclet.logicalAndAssignment
    | .or => KeyOrigin.taclet KeyTaclet.logicalOrAssignment

  def unopCaptureOrigin : UnOp -> KeyOrigin
    | .neg => KeyOrigin.taclet KeyTaclet.unaryMinusCapture
    | .not => KeyOrigin.taclet KeyTaclet.logicalNotCapture

  def unopAssignmentOrigin : UnOp -> KeyOrigin
    | .neg => KeyOrigin.taclet KeyTaclet.unaryMinusAssignment
    | .not => KeyOrigin.taclet KeyTaclet.logicalNotAssignment

  def compoundRhsCaptureOrigin : BinOp -> KeyOrigin
    | .add => KeyOrigin.taclet KeyTaclet.addAssignValueRhsCapture
    | .sub => KeyOrigin.taclet KeyTaclet.subAssignValueRhsCapture
    | .mul => KeyOrigin.taclet KeyTaclet.mulAssignValueRhsCapture
    | .pow => KeyOrigin.leanOnly
    | .div => KeyOrigin.taclet KeyTaclet.divAssignValueRhsCapture
    | .mod => KeyOrigin.taclet KeyTaclet.modAssignValueRhsCapture
    | .lt => KeyOrigin.leanOnly
    | .gt => KeyOrigin.leanOnly
    | .le => KeyOrigin.leanOnly
    | .ge => KeyOrigin.leanOnly
    | .eqB => KeyOrigin.leanOnly
    | .neB => KeyOrigin.leanOnly
    | .and => KeyOrigin.leanOnly
    | .or => KeyOrigin.leanOnly

  def localAssignIncDecOrigin : IncDec -> KeyOrigin
    | .preInc => KeyOrigin.merged [KeyTaclet.localAssignPreincrement, KeyTaclet.localDeclPreincrement]
    | .preDec => KeyOrigin.merged [KeyTaclet.localAssignPredecrement, KeyTaclet.localDeclPredecrement]
    | .postInc => KeyOrigin.merged [KeyTaclet.localAssignPostincrement, KeyTaclet.localDeclPostincrement]
    | .postDec => KeyOrigin.merged [KeyTaclet.localAssignPostdecrement, KeyTaclet.localDeclPostdecrement]

  def localIncDecOrigin : IncDec -> KeyOrigin
    | .preInc => KeyOrigin.taclet KeyTaclet.localPreincrement
    | .preDec => KeyOrigin.taclet KeyTaclet.localPredecrement
    | .postInc => KeyOrigin.taclet KeyTaclet.localPostincrement
    | .postDec => KeyOrigin.taclet KeyTaclet.localPostdecrement

  /-! ## The rules

  One `rule` declaration each, in the order the banners name, assembled
  into `RuleName`, `ruleEffect` and `ruleNames` by `#assemble_rules`
  below.  Declaration order is the order of all three, and it is
  load-bearing: `FirstStepCase` takes the first applicable rule under the
  block modality, so a box twin precedes its diamond twin. -/

  /-!
  ## Storage Rules

  Solidity evaluates the right-hand side
  of an assignment before the left-hand side, and the rules follow that order:
  Step 1 unfolds the right-hand side, Step 2 the left-hand side, Step 3 generates
  an update.
  -/

  /-!
  ### Step 1: unfolding the right-hand side

  `unfold_rightFst` instances (the rule set; solkey
  `storageFieldRead_unfold_rightFst`, `storageIndexRead_unfold_rightFst`).
  -/

  sol_rule storageFieldReadUnfoldRightFst from storageFieldRead_unfold_rightFst :
    <[ lhs = nsp.fld ]> ⇝ <[ T storage sp = nsp; lhs = sp.fld ]>
    where ¬ (lhs.kind = Kind.memory ∧ isComplex lhs)

  sol_rule storageIndexReadUnfoldRightFst from storageIndexRead_unfold_rightFst :
    <[ lhs = nsp[e] ]> ⇝ <[ T storage sp = nsp; lhs = sp[e] ]>
    where ¬ (lhs.kind = Kind.memory ∧ isComplex lhs)

  /-!
  `unfold_rightSnd`.  The push-argument rule is
  standalone: a push receiver is not an assignment right-hand side, but its
  argument is evaluated before the update.
  -/

  sol_rule storageIndexReadUnfoldRightSndIndex from storageIndexRead_unfold_rightSndIndex :
    <[ lhs = sp[nse] ]> ⇝ <[ T idx = nse; lhs = sp[idx] ]>
    where ¬ (lhs.kind = Kind.memory ∧ isComplex lhs)

  sol_rule storagePushValueUnfoldRightSndArgument from storagePushValue_unfold_rightSndArgument :
    <[ sp.push(nse) ]> ⇝ <[ _ pv = nse; sp.push(pv) ]>

  /-!
  `unfold_rightSndResult` (the rule set; solkey also folds
  `storageFieldWriteCaptureSrc` and `storageIndexWriteStorageRefRhsCapture`
  in here).
  -/

  sol_rule storageFieldReadUnfoldRightSndResult from storageFieldRead_unfold_rightSndResult, storageFieldWriteCaptureSrc :
    <[ nlhs = sp.fld ]> ⇝ <[ _ pv = sp.fld; nlhs = pv ]>

  sol_rule storageIndexReadUnfoldRightSndResult from storageIndexRead_unfold_rightSndResult, storageIndexWriteStorageRefRhsCapture :
    <[ nlhs = sp[i] ]> ⇝ <[ _ pv = sp[i]; nlhs = pv ]>

  /-!
  ### Step 2: unfolding the left-hand side

  `unfold_leftFst` instances.  The calculus's `RootRhs` pair
  is merged: Lean's `isSimple rhs` already admits a global root, which the
  calculus's `SimpleExpression` excludes.
  -/

  sol_rule storageFieldWriteUnfoldLeftFst from storageFieldWrite_unfold_leftFst, storageFieldWriteRootRhs_unfold_leftFst :
    <[ nsp.fld = e ]> ⇝ <[ T rv ?= e; T storage sp = nsp; sp.fld = rv ]>
    where isSimple e, ¬ isMemory e

  sol_rule storageIndexWriteUnfoldLeftFst from storageIndexWrite_unfold_leftFst, storageIndexWriteRootRhs_unfold_leftFst :
    <[ nsp[e1] = e2 ]> ⇝ <[ T rv ?= e2; T storage sp = nsp; T idx ?= e1; sp[idx] = rv ]>
    where isSimple e2

  /-!
  Storage receiver and delete-target simplification (the calculus,
  the rule set).  Not instances of the assignment-shaped template: their
  active statements are `delete`, `push`, `pop` or a push-return binding.  The
  calculus's `storageFieldDelete_unfold_leftFst` and `storageIndexDelete_unfold_leftFst`
  are merged into one rule over both target shapes.
  -/

  sol_rule storageDeleteComplexTarget from storageFieldDelete_unfold_leftFst, storageIndexDelete_unfold_leftFst, storageIndexDeleteNonSimpleIndexCapture :
    <[ delete(target) ]> ⇝ ⟦ storageDeleteComplexTargetBlock (target : WrappedExpr) h ⟧
    where cond := isComplexStorageDeleteTarget target

  sol_rule storagePushValueUnfoldLeftFstReceiver from storagePushValue_unfold_leftFstReceiver :
    <[ nsp.push(e) ]> ⇝ <[ T storage sp = nsp; sp.push(e) ]>

  sol_rule storagePushUnfoldLeftFstReceiver from storagePush_unfold_leftFstReceiver :
    <[ nsp.push() ]> ⇝ <[ T storage sp = nsp; sp.push() ]>

  sol_rule storagePopUnfoldLeftFstReceiver from storagePop_unfold_leftFstReceiver :
    <[ nsp.pop() ]> ⇝ <[ T storage sp = nsp; sp.pop() ]>

  sol_rule storageLocalRootPushUnfoldLeftFstReceiver from storageLocalRootPush_unfold_leftFstReceiver :
    <[ lhs = nsp.push() ]> ⇝
      -- Unlike `storagePushLhsToPushValue`, `nsp` here comes out of a
      -- `WrappedExpr`, and `WrappedExpr.pushPlace` carries no assignability
      -- invariant, so there is no witness to appeal to: `asPlace?` really can
      -- return `none`, which is why `…_sound` has to assume `hasgn`.  The
      -- `none` arm is a real guard, not a dead one.
      ⟦ match asPlace? nsp with
        | some _ =>
            [ captureStoragePath nsp,
              Stmt.assign lhs
                (WrappedExpr.pushPlace
                  (aliasExpr Kind.storage nsp.ty storagePathAliasName)) ]
        | none => [] ⟧
    where ¬ (lhs.kind = Kind.memory ∧ isComplex lhs)

  /-!
  `unfold_leftSnd`.  The calculus's `Ref` instance is
  merged: Lean's rule does not split on a reference source.
  -/

  sol_rule storageIndexWriteUnfoldLeftSndIndex from storageIndexWriteNonSimpleIndexCapture, storageIndexWriteRootRhsNonSimpleIndexCapture :
    <[ sp1[nse] = s ]> ⇝ <[ T rv ?= s; T storage sp = sp1; T idx ?= nse; sp[idx] = rv ]>
    where ¬ isMemory s

  /-!
  ### Step 3: generating an update

  Declarations.  the calculus states the rule once
  for storage and names its value instances here too, so the value pair sits
  beside the storage pair.
  -/

  sol_rule storageLocalDeclInitDrop from storageLocalDeclInitDrop :
    <[ T storage lsv = path ]> ⇝ <[ T storage lsv; lsv = path ]>

  sol_rule storageLocalDeclSkip from storageLocalDeclSkip :
    <[ T storage lsv ]> ⇝ <[ ]>

  /-!
  Value-variable declarations (KeY `localValueDeclInitDrop`/`valueDeclSkip`)
  and simple local assignment (KeY `localValueAssign`).
  -/

  sol_rule localValueDeclInitDrop from localValueDeclInitDrop :
    <[ T v = e ]> ⇝ <[ T v; v = e ]>

  sol_rule valueDeclSkip from valueDeclSkip :
    <[ T v ]> ⇝ { v := default(T) } <[ ]>

  /-!
  Simple targets.  The calculus's `storageRootDelete`,
  `storageFieldDelete` and `storageIndexDelete` are one Lean rule over all three
  simple target shapes.
  -/

  sol_rule storageFieldWriteSave from storageFieldWriteSave :
    <[ sp.fld = se ]> ⇝ { storage := save(sp.fld, se) } <[ ]>

  sol_rule storageFieldWriteCopySource from storageFieldWriteCopySource :
    <[ sp1.fld = sp2 ]> ⇝ { storage := copy(sp1.fld, sp2) } <[ ]>

  sol_rule storageRootWriteStore from storageRootWriteStore :
    <[ gsp = se ]> ⇝ { storage := save(gsp, se) } <[ ]>

  sol_rule storageRootWriteCopySource from storageRootWriteCopySource :
    <[ gsp = sp ]> ⇝ { storage := copy(gsp, sp) } <[ ]>

  sol_rule storageLocalRootRebind from storageLocalRootRebind :
    <[ lsv = sp ]> ⇝ { lsv := path(sp) } <[ ]>

  sol_rule storageFieldReadFind from storageFieldReadFind :
    <[ v = sp.fld ]> ⇝ { v := sp.fld } <[ ]>

  sol_rule storageRootReadSelect from storageRootReadSelect :
    <[ v = sp ]> ⇝ { v := sp } <[ ]>

  sol_rule storageFieldReadBindLocalRoot from storageFieldReadBindLocalRoot :
    <[ lsv = sp.fr ]> ⇝ { lsv := path(sp.fr) } <[ ]>

  sol_rule storageFieldReadStoreRoot from storageFieldReadStoreRoot :
    <[ gsp = sp.fr ]> ⇝ { storage := copy(gsp, sp.fr) } <[ ]>
    where isSimple gsp

  sol_rule storageDeleteSimpleTarget from storageRootDelete, storageFieldDelete, storageIndexDelete :
    <[ delete(target) ]> ⇝ { storage := clear(target) } <[ ]>
    where cond := isSimpleStorageDeleteTarget target

  /-!
  Mapping targets.  Mapping selectors generate no
  bounds branch: mappings have no length.
  -/

  sol_rule storageIndexWriteMappingSave from storageIndexWriteMappingSave :
    <[ map[i] = se ]> ⇝ { storage := save(map[i], se) } <[ ]>

  sol_rule storageIndexWriteMappingCopySource from storageIndexWriteMappingCopySource :
    <[ map[i] = sp ]> ⇝ { storage := copy(map[i], sp) } <[ ]>

  sol_rule storageIndexReadMappingFind from storageIndexReadMappingFind :
    <[ v = map[i] ]> ⇝ { v := map[i] } <[ ]>

  sol_rule storageIndexReadMappingBindLocalRoot from storageIndexReadMappingBindLocalRoot :
    <[ lsv = map[i] ]> ⇝ { lsv := path(map[i]) } <[ ]>

  sol_rule storageIndexReadMappingStoreRoot from storageIndexReadMappingStoreRoot :
    <[ gsp = map[i] ]> ⇝ { storage := copy(gsp, map[i]) } <[ ]>
    where isSimple gsp

  /-!
  Array targets.  The calculus stacks the bounds check
  as two sequents; Lean splits each rule into a box/diamond twin pair.  **The box
  twin is listed first**, here and in `ruleNames` — see the `Box`/`Diamond`
  note in the module docstring.
  -/

  sol_rule storageIndexWriteArraySave twins from storageIndexWriteArraySave :
    <[ arr[i] = se ]> ⇝
      | inBounds(arr[i]) ⟹ { storage := save(arr[i], se) } <[ ]>
      | else             ⟹ revert()
    after read(se), resolve(arr[i])

  sol_rule storageIndexWriteArrayCopySource twins from storageIndexWriteArrayCopySource :
    <[ arr[i] = sp ]> ⇝
      | inBounds(arr[i]) ⟹ { storage := copy(arr[i], sp) } <[ ]>
      | else             ⟹ revert()
    after image(sp), resolve(arr[i])

  sol_rule storageIndexReadArrayFind twins from storageIndexReadArrayFind :
    <[ v = arr[i] ]> ⇝
      | inBounds(arr[i]) ⟹ { v := arr[i] } <[ ]>
      | else             ⟹ revert()
    after resolve(arr[i])

  sol_rule storageIndexReadArrayBindLocalRoot twins from storageIndexReadArrayBindLocalRoot :
    <[ lsv = arr[i] ]> ⇝
      | inBounds(arr[i]) ⟹ { lsv := path(arr[i]) } <[ ]>
      | else             ⟹ revert()
    after resolve(arr[i])

  sol_rule storageIndexReadArrayStoreRoot twins from storageIndexReadArrayStoreRoot :
    <[ gsp = arr[i] ]> ⇝
      | inBounds(arr[i]) ⟹ { storage := copy(gsp, arr[i]) } <[ ]>
      | else             ⟹ revert()
    after resolve(arr[i])
    where isSimple gsp

  /-!
  Push and pop.  The calculus's `sizeNotNegative`
  is a first-order side condition, not a rewrite rule; its
  Lean counterpart is `WellFormedConsumers.lean`.
  -/

  sol_rule storagePushValueSave from storagePushValueSave :
    <[ sp.push(se) ]> ⇝ { storage := push(sp, se) } <[ ]>

  sol_rule storagePushValueCopySource from storagePushValueCopySource :
    <[ sp1.push(sp2) ]> ⇝ { storage := push(sp1, sp2) } <[ ]>

  sol_rule storagePushLengthSave from storagePushLengthSave :
    <[ sp.push() ]> ⇝ { storage := push(sp) } <[ ]>

  sol_rule storageLocalRootPushBind from storageLocalRootPushBind :
    <[ lsv = sp.push() ]> ⇝
      { storage := pushSlot(sp.push()) || lsv := slot(sp.push()) } <[ ]>

  sol_rule storagePopSave twins from storagePopSave :
    <[ sp.pop() ]> ⇝
      | nonEmpty(sp) ⟹ { storage := pop(sp) } <[ ]>
      | else         ⟹ revert()
    after resolve(sp)

  /-! ### Require and assert (the calculus, the rule set) -/

  /-!
  Require: KeY `requireConditionCapture` and `requireSimple` (the
  Holds/Reverts split of `requireSimple` lives in the semantic layer:
  the interpreter reverts on false, and `check` routes the revert
  per modality — diamond `c ∧ φ`, box `c → φ`).
  -/

  sol_rule requireConditionCapture from requireConditionCapture :
    <[ require(nse) ]> ⇝ <[ T pv = nse; require(pv) ]>

  /-!
  Assert: KeY `assertConditionCapture` and `assertSimple` (the sequent
  split of `assertSimple` lives in the semantic layer).
  -/

  sol_rule assertConditionCapture from assertConditionCapture :
    <[ assert(nse) ]> ⇝ <[ T pv = nse; assert(pv) ]>

  sol_rule requireSimple from requireSimple :
    <[ require(se) ]> ⇝
      | se   ⟹ <[ ]>
      | else ⟹ revert()
    where cond := isSimple se

  sol_rule assertSimple from assertSimple :
    <[ assert(se) ]> ⇝
      | "Holds"    : se ⟹ <[ ]>
      | "Violated" :    ⟹ se
    where cond := isSimple se

  /-!
  ### Conditional statements (the calculus, the rule set)

  The calculus's `ifElseSplit` is a sequent rule — two goals, so no `BlockStep` —
  and lives in `JudgmentSplit.ite_split`.
  -/

  /-!
  If-then-else (upstream `ifElseUnfold`/`ifElseTrue`/`ifElseFalse`/
  `ifElseNegated`, the rule set): condition-directed rewrites per
  plan D3(b).  All four now carry solkey's own program-rule names, which lift
  the term-level `ifthenelse_true`/`ifthenelse_false`/`ifthenelse_negated`
  to statements.  `ifElseUnfold` covers KeY's `ifUnfold` *and* `ifElseUnfold`,
  because `Stmt.ite` always carries both branches; the calculus's `ifElseSplit`
  is a sequent rule and lives in `JudgmentSplit.ite_split`.
  -/

  sol_rule ifElseUnfold from ifUnfold, ifElseUnfold :
    <[ if (nse) thn else els ]> ⇝ <[ T pv = nse; if (pv) thn else els ]>
    where ∀ inner, nse = WrappedExpr.unop UnOp.not inner -> isComplex inner

  sol_rule ifElseTrue :
    <[ if (true) thn else els ]> ⇝ <[ thn ]>

  sol_rule ifElseFalse :
    <[ if (false) thn else els ]> ⇝ <[ els ]>

  sol_rule ifElseNegated :
    <[ if (!s) thn else els ]> ⇝ <[ if (s) els else thn ]>

  /-!
  ### Abrupt termination (the calculus, the rule set)

  the rule set prints the diamond rule first; here the box twin leads, as it must
  everywhere (module docstring, `Box`/`Diamond`).
  -/

  /-!
  Modality rules: KeY `revertBox`/`revertDiamond` consume a `revert();`
  (the truth value of the enclosing modality lives in the semantic layer).
  -/

  sol_rule «revert» twins :
    <[ revert() ]> ⇝
      | "box"     : box     : ⟹ ⊤
      | "diamond" : diamond : ⟹ ⊥

  /-!
  ## Payment Rules

  The calculus splits the terminal
  transfer rule into a box and a diamond rule; Lean's `transferNoCallback` is
  modality-generic and carries both.
  -/

  /-!
  Payments: KeY `transfer_unfold_leftFstReceiver`,
  `transfer_unfold_rightSndArgument`, `transferNoCallback`.
  -/

  sol_rule transferUnfoldLeftFstReceiver from transfer_unfold_leftFstReceiver :
    <[ nadr.transfer(e) ]> ⇝ <[ T pv = nadr; pv.transfer(e) ]>

  sol_rule transferUnfoldRightSndArgument from transfer_unfold_rightSndArgument :
    <[ sadr.transfer(nse) ]> ⇝ <[ T pv = nse; sadr.transfer(pv) ]>

  sol_rule transferNoCallback from transferNoCallbackBox, transferNoCallbackDiamond :
    <[ sadr.transfer(se) ]> ⇝
      | funded(se) ⟹ { transfer(sadr, se) } <[ ]>
      | else       ⟹ revert()
    after read(net(sadr))
    where cond := isSimple sadr ∧ isSimple se

  /-!
  KeY option `transferSemantics:withCallback`: the re-entrancy-aware
  transfer. Same syntactic condition and (empty) residual as
  `transferNoCallback` — KeY makes the two a *choice*, not coexisting
  rules — so it lives in the alternative rule list
  `ruleNamesWithCallback`, never in `ruleNames`. Its semantic
  content (the contract-invariant / havoc branch split) is
  `CallbackSemantics.holdsC_transfer_split`.
  -/

  sol_rule transferWithCallback alternative from transferWithCallbackBox, transferWithCallbackDiamond :
    <[ sadr.transfer(s) ]> ⇝
      | "invariant on exit"     :      ⟹ { transfer(sadr, s) } CInv
      | "resume after callback" : CInv ⟹ { havoc } <[ ]>

  /- ## Memory Rules

  The same three steps.
  -/

  /- ### Step 1: unfolding the right-hand side -/

  /-!
  ## Memory Rules

  The same three steps.
  -/

  /-! ### Step 1: unfolding the right-hand side -/

  sol_rule memoryFieldReadUnfoldRightFst from memoryFieldRead_unfold_rightFst :
    <[ lhs = nmp.fld ]> ⇝ <[ T memory mv = nmp; lhs = mv.fld ]>
    where ¬ isStorage lhs

  sol_rule memoryIndexReadUnfoldRightFst from memoryIndexRead_unfold_rightFst :
    <[ lhs = nmp[e] ]> ⇝ <[ T memory mv = nmp; lhs = mv[e] ]>
    where ¬ isStorage lhs

  sol_rule memoryIndexReadUnfoldRightSndIndex from memoryIndexRead_unfold_rightSndIndex :
    <[ lhs = mv[nse] ]> ⇝ <[ T idx = nse; lhs = mv[idx] ]>
    where ¬ isStorage lhs

  sol_rule memoryWriteUnfoldRightSndResult from memoryIndexWriteMemRefRhsCapture :
    <[ nmp = nse ]> ⇝ <[ _ pv = nse; nmp = pv ]>
    where cond :=
      nmp.kind = Kind.memory ∧ isComplex nmp ∧ isComplex nse ∧
        match nse with
        | WrappedExpr.field Kind.memory .. => False
        | WrappedExpr.index Kind.memory .. => False
        | _ => True

  sol_rule memoryFieldReadUnfoldRightSndResult from memoryFieldRead_unfold_rightSndResult :
    <[ nmp = mv.fld ]> ⇝ <[ _ pv = mv.fld; nmp = pv ]>

  sol_rule memoryIndexReadUnfoldRightSndResult from memoryIndexRead_unfold_rightSndResult :
    <[ nmp = mv[i] ]> ⇝ <[ _ pv = mv[i]; nmp = pv ]>

  /-!
  ### Step 2: unfolding the left-hand side

  As in storage, the two delete unfolds are merged into one rule.
  -/

  sol_rule memoryFieldWriteUnfoldLeftFst from memoryFieldWrite_unfold_leftFst :
    <[ nmp.fld = e ]> ⇝ <[ T rv ?= e; T memory mv = nmp; mv.fld = rv ]>
    where isSimple e

  sol_rule memoryIndexWriteUnfoldLeftFst from memoryIndexWrite_unfold_leftFst :
    <[ nmp[e1] = e2 ]> ⇝ <[ T rv ?= e2; T memory mv = nmp; T idx ?= e1; mv[idx] = rv ]>
    where isSimple e2

  sol_rule memoryDeleteComplexTarget from memoryFieldDelete_unfold_leftFst, memoryIndexDelete_unfold_leftFst, memoryIndexDeleteNonSimpleIndexCapture :
    <[ delete(target) ]> ⇝ ⟦ memoryDeleteComplexTargetBlock (target : WrappedExpr) h ⟧
    where cond := isComplexMemoryDeleteTarget target

  sol_rule memoryIndexWriteUnfoldLeftSndIndex from memoryIndexWriteNonSimpleIndexCapture :
    <[ mv1[nse] = s ]> ⇝ <[ T rv ?= s; T memory mv = mv1; T idx ?= nse; mv[idx] = rv ]>

  /-!
  ### Step 3: generating an update

  Declarations; `memoryArrayFreshAlloc` is merged into
  `memoryDeclFreshAlloc`.
  -/

  sol_rule memoryLocalDeclInitDrop from memoryLocalDeclInitDrop :
    <[ T memory mv = mpath ]> ⇝ <[ mv = mpath ]>

  sol_rule memoryDeclFreshAlloc from memoryReferenceDeclFreshAlloc, memoryArrayFreshAlloc :
    <[ T memory mv ]> ⇝ { mv := alloc() } <[ ]>

  /- Simple targets.  The calculus's five delete rules —
  root fresh-rebind, f primitive/reference, index primitive/reference — are
  one Lean rule.
  -/

  /-!
  Simple targets.  The calculus's five delete rules —
  root fresh-rebind, field primitive/reference, index primitive/reference — are
  one Lean rule.
  -/

  sol_rule memoryFieldWriteStore from memoryFieldWrite :
    <[ mv.fld = se ]> ⇝ { memory := write(mv.fld, se) } <[ ]>

  sol_rule memoryRootAlias from memoryRootRebind :
    <[ mv1 = mv2 ]> ⇝ { mv1 := ref(mv2) } <[ ]>

  sol_rule memoryFieldReadHeap from memoryFieldRead :
    <[ v = mv.fld ]> ⇝ { v := mv.fld } <[ ]>

  sol_rule memoryFieldReadAliasRoot from memoryFieldRead :
    <[ mv1 = mv2.fr ]> ⇝ { mv1 := ref(mv2.fr) } <[ ]>

  sol_rule memoryDeleteSimpleTarget from memoryRootDeleteFreshRebind, memoryFieldDeletePrimitive, memoryFieldDeleteReference, memoryIndexDeletePrimitive, memoryIndexDeleteReference :
    <[ delete(target) ]> ⇝ { clear(target) } <[ ]>
    where cond := isSimpleMemoryDeleteTarget target

  /-! Array targets, box twin first. -/

  sol_rule memoryIndexWriteStore twins from memoryIndexWriteArray :
    <[ mv[i] = se ]> ⇝
      | inBounds(mv[i]) ⟹ { memory := write(mv[i], se) } <[ ]>
      | else            ⟹ revert()
    after read(se), resolve(mv[i])

  sol_rule memoryIndexReadHeap twins from memoryIndexReadArrayValue :
    <[ v = mv[i] ]> ⇝
      | inBounds(mv[i]) ⟹ { v := mv[i] } <[ ]>
      | else            ⟹ revert()
    after resolve(mv[i])

  sol_rule memoryIndexReadAliasRoot twins from memoryIndexReadArrayMemory :
    <[ mv1 = mv2[i] ]> ⇝
      | inBounds(mv2[i]) ⟹ { mv1 := ref(mv2[i]) } <[ ]>
      | else             ⟹ revert()
    after resolve(mv2[i])

  /- ## Storage to Memory Rules

  the calculus, the rule set: a deep copy through a memory root.
  `memoryStorageCopy` is the simple-mv2 form (`mv = sp;`, fresh identity plus
  `copySt`); `memoryStorageCopyUnfold` captures a complex storage mv2 into a
  storage alias first.  Both were once silently absorbed by `memoryRootAlias`,
  whose condition did not restrict the right-hand side's kind.
  -/

  /-!
  ## Storage to Memory Rules

  A deep copy through a memory root.  `memoryStorageCopy` is the simple-path
  form (`mv = sp;`, fresh identity plus `copySt`); `memoryStorageCopyUnfold`
  captures a complex storage path into a storage alias first.
  -/

  sol_rule memoryStorageCopyUnfold from memoryStorageCopyUnfold :
    <[ mv = path ]> ⇝ <[ T storage sp = path; mv = sp ]>
    where cond :=
      mv.kind = Kind.memory ∧ isSimple mv ∧
        match path with
        | WrappedExpr.field Kind.storage _ base _ => isSimple base
        | WrappedExpr.index Kind.storage _ base i =>
            isSimple base ∧ isSimple i
        | _ => False

  sol_rule memoryStorageCopy from memoryStorageCopy :
    <[ mv = sp ]> ⇝ { mv := alloc(sp) } <[ ]>

  /-!
  ## Memory to Storage Rules

  The calculus's
  `memoryToStorageFieldCopyField` is merged into `memoryToStorageFieldCopyRoot`
  plus the unfolds; the array index rule is a box/diamond twin pair.
  -/

  sol_rule memoryToStorageUnfoldLeftFstTarget :
    <[ nsp.fld = mv ]> ⇝ <[ T rv ?= mv; T storage sp = nsp; sp.fld = rv ]>

  sol_rule memoryToStorageUnfoldLeftSndTargetIndex :
    <[ sp1[nse] = mv ]> ⇝ <[ T rv ?= mv; T storage sp = sp1; T idx ?= nse; sp[idx] = rv ]>

  sol_rule memoryToStorageFieldCopyRoot from memoryToStorageFieldCopyRoot, memoryToStorageFieldCopyField :
    <[ sp.fld = mv ]> ⇝ { storage := copyMem(sp.fld, mv) } <[ ]>

  sol_rule memoryToStorageIndexMappingCopyRoot from memoryToStorageIndexMappingCopyRoot :
    <[ map[i] = mv ]> ⇝ { storage := copyMem(map[i], mv) } <[ ]>

  sol_rule memoryToStorageIndexArrayCopyRoot twins from memoryToStorageIndexArrayCopyRoot :
    <[ arr[i] = mv ]> ⇝
      | inBounds(arr[i]) ⟹ { storage := copyMem(arr[i], mv) } <[ ]>
      | else             ⟹ revert()
    after image(mv), resolve(arr[i])

  sol_rule memoryToStorageStoreRoot from memoryToStorageStoreRoot :
    <[ sp = mv ]> ⇝ { storage := copyMem(sp, mv) } <[ ]>

  /- ## Arithmetic

  the calculus; the rule set (local and storage targets) and
  the rule set (memory targets).  Each rule of the calculus is schematic in the
  operator or the inc/dec variant, and Lean has one instance per member.  The
  calculus's `unaryMinusAssignment` is `unopAssignment .neg`, listed with the
  operator tier below because its `.not` sibling is not arithmetic.
  -/

  /- Local targets (`localOpAssign`, `localDivAssign`). -/

  /-!
  ## Arithmetic

  the calculus; the rule set (local and storage targets) and
  the rule set (memory targets).  Each rule of the calculus is schematic in the
  operator or the inc/dec variant, and Lean has one instance per member.  The
  calculus's `unaryMinusAssignment` is `unopAssignment .neg`, listed with the
  operator tier below because its `.not` sibling is not arithmetic.
  -/

  /-! Local targets (`localOpAssign`, `localDivAssign`). -/

  /-!
  Local compound assignment, one KeY taclet per op instance
  (`localAddAssign` = `localCompoundAssign .add`, ...): terminal
  `lv ⊕= se;` on a stack variable.
  -/

  sol_rule localCompoundAssign (op : BinOp) from (localCompoundOrigin op) :
    <[ lv ⊕= se ]> ⇝
      | (nonZero(se) when BinOp.needsGuard opS) ⟹ { lv := lv ⊕ se } <[ ]>
      | else                                    ⟹ revert()
    after read(se)

  /-!
  Storage targets: `storageRootOpAssign`, `storageFieldOpAssign`,
  `storageIndexMappingOpAssign` / `storageIndexArrayOpAssign` — merged into one
  Lean rule — and `storageRootIncrement`.
  -/

  /-!
  Storage compound assignments, one KeY taclet per op instance
  (`storageRootAddAssign` = `storageRootCompoundAssign .add`, ...);
  unsatisfiable for ops without a compound form (`**`, comparisons,
  boolean connectives).
  -/

  /-!
  Storage targets (`storageRootOpAssign`, `storageFieldOpAssign`,
  `storageIndex{Mapping,Array}OpAssign` — merged here — and
  `storageRootIncrement`).
  -/

  sol_rule storageRootCompoundAssign (op : BinOp) from (storageRootCompoundOrigin op) :
    <[ gsp ⊕= se ]> ⇝
      | (nonZero(se) when BinOp.needsGuard opS) ⟹ { gsp := gsp ⊕ se } <[ ]>
      | else                                    ⟹ revert()
    after read(se)

  sol_rule storageFieldCompoundAssign (op : BinOp) from (storageFieldCompoundOrigin op) :
    <[ sp.fld ⊕= se ]> ⇝
      | (nonZero(se) when BinOp.needsGuard opS) ⟹ { sp.fld := sp.fld ⊕ se } <[ ]>
      | else                                    ⟹ revert()
    after read(se)

  sol_rule storageIndexCompoundAssign (op : BinOp) from (storageIndexCompoundOrigin op) :
    <[ sp[i] ⊕= se ]> ⇝
      | inBounds(sp[i]) ⟹ { sp[i] := sp[i] ⊕ se } <[ ]>
      | else            ⟹ revert()
    after read(se), resolve(sp[i])

  sol_rule storageFieldCompoundAssignUnfoldLeftFst (op : BinOp) from (storageFieldCompoundUnfoldOrigin op) :
    <[ nsp.fld ⊕= se ]> ⇝ <[ T rv = se; T storage sp = nsp; sp.fld ⊕= rv ]>

  sol_rule storageIndexCompoundAssignUnfoldLeftFst (op : BinOp) from (storageIndexCompoundUnfoldOrigin op) :
    <[ nsp[i] ⊕= se ]> ⇝ <[ T rv = se; T storage sp = nsp; sp[i] ⊕= rv ]>

  /-!
  Increment/decrement statement forms (`++age;`), one KeY taclet per
  `IncDec` instance (`storageRootPreincrement` = `storageRootIncDec
  .preInc`, ...), their complex-path unfolds, the assignment forms
  (`result = ++age;`), and the local-variable assignment form
  (`localAssignPreincrement`, ...; KeY `localDeclPreincrement` is covered
  by `localValueDeclInitDrop` followed by `localAssignIncDec`).
  -/

  sol_rule storageRootIncDec (op : IncDec) from (storageRootIncDecOrigin op) :
    <[ gsp++ ]> ⇝ { bump(gsp++) } <[ ]>

  sol_rule storageFieldIncDec (op : IncDec) from (storageFieldIncDecOrigin op) :
    <[ sp.fld++ ]> ⇝ { bump(sp.fld++) } <[ ]>

  sol_rule storageIndexIncDec (op : IncDec) from (storageIndexIncDecOrigin op) :
    <[ sp[i]++ ]> ⇝
      | inBounds(sp[i]++) ⟹ { bump(sp[i]++) } <[ ]>
      | else              ⟹ revert()
    after resolve(sp[i]++)

  sol_rule storageFieldIncDecUnfoldLeftFst (op : IncDec) from (storageFieldIncDecUnfoldOrigin op) :
    <[ nsp.fld++ ]> ⇝ <[ T storage sp = nsp; sp.fld++ ]>

  sol_rule storageIndexIncDecUnfoldLeftFst (op : IncDec) from (storageIndexIncDecUnfoldOrigin op) :
    <[ nsp[i]++ ]> ⇝ <[ T storage sp = nsp; sp[i]++ ]>

  sol_rule storageRootIncDecAssignment (op : IncDec) from (storageRootIncDecAssignOrigin op) :
    <[ lv = gsp++ ]> ⇝ { bump(gsp++) || lv := gsp++ } <[ ]>

  sol_rule storageFieldIncDecAssignment (op : IncDec) from (storageFieldIncDecAssignOrigin op) :
    <[ lv = sp.fld++ ]> ⇝ { bump(sp.fld++) || lv := sp.fld++ } <[ ]>

  sol_rule storageIndexIncDecAssignment (op : IncDec) from (storageIndexIncDecAssignOrigin op) :
    <[ lv = sp[i]++ ]> ⇝
      | inBounds(sp[i]++) ⟹ { bump(sp[i]++) || lv := sp[i]++ } <[ ]>
      | else              ⟹ revert()
    after resolve(sp[i]++)

  /-!
  Memory targets: `memoryFieldOpAssign`, `memoryFieldDivAssign`,
  `memoryIndexArrayOpAssign`, `memoryFieldIncrement`.
  -/

  /-!
  Memory-target compound assignments, the storage terminals with the
  heap read/write in place of `find`/`save`: the calculus's
  `memoryFieldOpAssign` / `memoryFieldDivAssign` / `memoryIndexArrayOpAssign`
  (the rule set, "Memory-target arithmetic"), solkey's
  `memoryField{Add,Sub,Mul,Div,Mod}Assign` and `memoryIndexArray*Assign`
  plus their `_unfold_leftFst` twins.  **No root form** — a memory root is
  an identity, not a value cell — and **no mapping form**: memory has no
  mappings.
  -/

  /-!
  Memory targets (`memoryFieldOpAssign`, `memoryFieldDivAssign`,
  `memoryIndexArrayOpAssign`, `memoryFieldIncrement`).
  -/

  sol_rule memoryFieldCompoundAssign (op : BinOp) :
    <[ mv.fld ⊕= se ]> ⇝
      | (nonZero(se) when BinOp.needsGuard opS) ⟹ { mv.fld := mv.fld ⊕ se } <[ ]>
      | else                                    ⟹ revert()
    after read(se)

  sol_rule memoryIndexCompoundAssign (op : BinOp) :
    <[ mv[i] ⊕= se ]> ⇝
      | inBounds(mv[i]) ⟹ { mv[i] := mv[i] ⊕ se } <[ ]>
      | else            ⟹ revert()
    after read(se), resolve(mv[i])

  sol_rule memoryFieldCompoundAssignUnfoldLeftFst (op : BinOp) :
    <[ nmp.fld ⊕= se ]> ⇝ <[ T rv = se; T memory mv = nmp; mv.fld ⊕= rv ]>

  sol_rule memoryIndexCompoundAssignUnfoldLeftFst (op : BinOp) :
    <[ nmp[i] ⊕= se ]> ⇝ <[ T rv = se; T memory mv = nmp; mv[i] ⊕= rv ]>

  /-!
  The memory twins of the increment/decrement family: the calculus's
  `memoryFieldIncrement`, solkey's `memoryField{Pre,Post}{in,de}crement`
  and `memoryIndexArray{Pre,Post}{in,de}crement` with their `Assignment`
  and `_unfold_leftFst` forms.  Again no root and no mapping form.
  -/

  sol_rule memoryFieldIncDec (op : IncDec) :
    <[ mv.fld++ ]> ⇝ { bump(mv.fld++) } <[ ]>

  sol_rule memoryIndexIncDec (op : IncDec) :
    <[ mv[i]++ ]> ⇝
      | inBounds(mv[i]++) ⟹ { bump(mv[i]++) } <[ ]>
      | else              ⟹ revert()
    after resolve(mv[i]++)

  sol_rule memoryFieldIncDecUnfoldLeftFst (op : IncDec) :
    <[ nmp.fld++ ]> ⇝ <[ T memory mv = nmp; mv.fld++ ]>

  sol_rule memoryIndexIncDecUnfoldLeftFst (op : IncDec) :
    <[ nmp[i]++ ]> ⇝ <[ T memory mv = nmp; mv[i]++ ]>

  sol_rule memoryFieldIncDecAssignment (op : IncDec) :
    <[ lv = mv.fld++ ]> ⇝ { bump(mv.fld++) || lv := mv.fld++ } <[ ]>

  sol_rule memoryIndexIncDecAssignment (op : IncDec) :
    <[ lv = mv[i]++ ]> ⇝
      | inBounds(mv[i]++) ⟹ { bump(mv[i]++) || lv := mv[i]++ } <[ ]>
      | else              ⟹ revert()
    after resolve(mv[i]++)

  /- ## Rules with no counterpart upstream

  solkey's finer tiers and the Lean-only rules.  Nothing checks this
  direction: a Lean rule is deliberately allowed to be finer than the
  presentation upstream, and requiring an upstream name for each would be a
  claim nobody makes.
  -/

  /- solkey's expression-operator tier. -/

  /-!
  ## Rules with no counterpart upstream

  solkey's finer tiers and the Lean-only rules.  Nothing checks this
  direction: a Lean rule is deliberately allowed to be finer than the
  presentation upstream, and requiring an upstream name for each would be a
  claim nobody makes.
  -/

  /-! solkey's expression-operator tier. -/

  /-!
  Binary-operator families, one KeY taclet per `op` instance:
  `binopUnfoldLeft op` = `<op>_unfold_left` / `<op>CaptureLhs`,
  `binopUnfoldRight op` = `<op>_unfold_right` / `<op>CaptureRhs`
  (unsatisfiable for the short-circuiting `&&`/`||`),
  `binopUnfoldResult op` = `<op>_unfold_result` (arithmetic ops only),
  `binopAssignment op` = `<op>Assignment`.
  -/

  sol_rule binopUnfoldLeft (op : BinOp) from (binopUnfoldLeftOrigin op) :
    <[ lv = nse ⊕ e ]> ⇝ <[ T pv = nse; lv = pv ⊕ e ]>

  sol_rule binopUnfoldRight (op : BinOp | op.shortCircuits = false) from (binopUnfoldRightOrigin op) :
    <[ lv = s ⊕ nse ]> ⇝ <[ T pv = nse; lv = s ⊕ pv ]>

  sol_rule binopUnfoldResult (op : BinOp | op.isArith = true) :
    <[ x = s1 ⊕ s2 ]> ⇝ <[ T pv = s1 ⊕ s2; x = pv ]>
    where ¬ isStackVar x, ¬ (x.kind = Kind.memory ∧ isComplex x)

  sol_rule binopAssignment (op : BinOp) from (binopAssignmentOrigin op) :
    <[ lv = s1 ⊕ s2 ]> ⇝
      | (rhsNonZero(s1 ⊕ s2) when BinOp.needsGuard op) ⟹ { lv := s1 ⊕ s2 } <[ ]>
      | else                                           ⟹ revert()

  /-!
  Short-circuit RHS: KeY `logicalAndShortCircuitRhs` /
  `logicalOrShortCircuitRhs`. KeY rewrites `v = se && nse;` into the
  ternary `v = se ? nse : false;`; Lean keeps the statement-level `if`
  residual (same meaning, and it predates `mkTernary`). The interpreter
  itself short-circuits, so the rewrite is exact.
  -/

  sol_rule logicalAndShortCircuitRhs from logicalAndShortCircuitRhs :
    <[ lv = s && nse ]> ⇝ <[ if (s) { lv = nse } else { lv = false } ]>

  sol_rule logicalOrShortCircuitRhs from logicalOrShortCircuitRhs :
    <[ lv = s || nse ]> ⇝ <[ if (s) { lv = true } else { lv = nse } ]>

  /-!
  Ternary `v = c ? e1 : e2;`: KeY `ternaryCaptureCond` hoists a
  nonsimple condition into `pv`; `ternaryToIf` lowers to the statement
  `if` for a stack target; `ternaryToIfStorage` is the twin for a
  storage-path target (which is not a KeY `Variable`).
  -/

  sol_rule ternaryCaptureCond from ternaryCaptureCond :
    <[ lhs = nse ? e1 : e2 ]> ⇝ <[ T pv = nse; lhs = pv ? e1 : e2 ]>
    -- the memory-complex-lhs dispatch branch claims the whole right-hand side
    -- first (`memoryWriteUnfoldRightSndResult`)
    where ¬ (lhs.kind = Kind.memory ∧ isComplex lhs)

  sol_rule ternaryToIf from ternaryToIf :
    <[ x = s ? e1 : e2 ]> ⇝ <[ if (s) { x = e1 } else { x = e2 } ]>
    where isStackVar x

  sol_rule ternaryToIfStorage from ternaryToIfStorage :
    <[ path = s ? e1 : e2 ]> ⇝ <[ if (s) { path = e1 } else { path = e2 } ]>
    where isStorage path

  /-!
  Unary operators: KeY `logicalNotCapture`/`logicalNotAssignment` and
  `unaryMinusCapture`/`unaryMinusAssignment`.
  -/

  sol_rule unopCapture (op : UnOp) from (unopCaptureOrigin op) :
    <[ lv = ⊖nse ]> ⇝ <[ T pv = nse; lv = ⊖pv ]>

  sol_rule unopAssignment (op : UnOp) from (unopAssignmentOrigin op) :
    <[ lv = ⊖s ]> ⇝ { lv := ⊖s } <[ ]>

  /-! solkey's capture partition: the location-neutral value hoists. -/

  /-!
  Evaluation-order RHS captures: KeY `storageRootWriteValueRhsCapture`,
  `fieldWriteValueRhsCapture`, `indexWriteValueRhsCapture` — hoist a
  nonsimple primitive RHS into `pv` before the storage write resolves
  its target (RHS-before-LHS evaluation order). The Lean conditions
  exclude the cells other rules already cover: arithmetic operators over
  simple operands go to `binopUnfoldResult`, and the stack-lhs operator
  families keep their own rules.
  -/

  sol_rule storageRootWriteValueRhsCapture from storageRootWriteValueRhsCapture :
    <[ gsp = e ]> ⇝ <[ T pv = e; gsp = pv ]>
    where valueRhsCaptureRhs e

  sol_rule fieldWriteValueRhsCapture from fieldWriteValueRhsCapture :
    <[ path.fld = e ]> ⇝ <[ T pv = e; path.fld = pv ]>
    where valueRhsCaptureRhs e

  sol_rule indexWriteValueRhsCapture from indexWriteValueRhsCapture :
    <[ path[x] = e ]> ⇝ <[ T pv = e; path[x] = pv ]>
    where valueRhsCaptureRhs e

  /-!
  Compound-assignment RHS capture: KeY
  `{add,sub,mul,div,mod}AssignValueRhsCapture` — location-neutral hoist
  of a nonsimple compound-assign RHS into `pv` before the target rules
  fire (RHS-before-LHS evaluation order, like the `*ValueRhsCapture`
  trio for plain assignment).
  -/

  sol_rule compoundAssignValueRhsCapture (op : BinOp) from (compoundRhsCaptureOrigin op) :
    <[ lhs ⊕= e ]> ⇝ <[ T pv = e; lhs ⊕= pv ]>
    where ¬ (isSe e)

  /-! Stack locals: solkey `localValueAssign`, `localAssign*crement` and
  `local*crement`. -/

  sol_rule localValueAssign from localValueAssign :
    <[ lv = se ]> ⇝ { lv := se } <[ ]>

  sol_rule localAssignIncDec (op : IncDec) from (localAssignIncDecOrigin op) :
    <[ lv = se++ ]> ⇝ { bump(se++) || lv := se++ } <[ ]>

  /-!
  Bare increment/decrement of a stack local as a statement of its own:
  KeY `localPreincrement`, `localPostincrement`, `localPredecrement`,
  `localPostdecrement` (`localIncDec .preInc`, ...).
  -/

  sol_rule localIncDec (op : IncDec) from (localIncDecOrigin op) :
    <[ se++ ]> ⇝ { bump(se++) } <[ ]>

  /-! Function calls. -/

  /-!
  Function calls: `functionBodyExpand` is KeY's inlining taclet
  (`ExpandFunctionBody`); `functionCallArgCapture` hoists the leftmost
  complex argument first — `unfoldArgument` on solkey's own backlog
  (`~/projects/solkey/docs/net.md` §5.1), so Lean goes beyond solkey here.
  The name is solkey's, not the calculus's: the rule set declares no rule
  called `unfoldArgument`, which is why nothing upstream names
  it and `functionCallArgCapture` is one of the Lean-only rules.
  -/

  sol_rule functionCallArgCapture :
    <[ res = fn(args) ]> ⇝
      ⟦ have h' : (captureFirstComplexArg args).isSome = true := h
        match captureFirstComplexArg args, h' with
        | some (c, args'), _ =>
            [ captureStackValue c, Stmt.callStmt res fn args' ] ⟧
    where cond := (captureFirstComplexArg args).isSome = true

  sol_rule functionBodyExpand from functionBodyExpand :
    <[ res = fn(args) ]> ⇝ ⟦ (SoliditySyntax.expandCall res fn args).getD [] ⟧
    where cond :=
      args.all (·.simple) = true ∧
        (SoliditySyntax.expandCall res fn args).isSome = true

  /-! Lean-only rules: front-end normalisations and scratch bindings with no
  taclet of their own. -/

  sol_rule storagePlaceAlias :
    <[ T alias sp = e ]> ⇝ { sp := path(e) } <[ ]>

  /-!
  Lean-only coverage rules.  `exprStmtCapture` parks a bare non-incDec
  expression statement in the scratch value alias: the residual `pv = e;`
  declaration performs the same evaluation (same reverts, same
  incDec/push side effects) and differs only in the scratch binding —
  sound modulo `RuleSoundness.aliasNames` (`exprStmtCapture_sound`).
  `pushAssignLower`/`pushFieldAssignLower` rewrite the push-assignment
  sugar to the very `Stmt.assign` form `Semantics.execStmt` delegates
  to, so original and residual execute definitionally alike
  (`pushAssignLower_sound`, `pushFieldAssignLower_sound`).
  -/

  sol_rule exprStmtCapture :
    <[ e ]> ⇝ <[ T pv = e ]>
    where cond :=
      match e with
      | WrappedExpr.incDec _ _ => False
      | _ => True

  sol_rule pushAssignLower :
    <[ pushAssign(target, value) ]> ⇝ <[ target.push() = value ]>

  sol_rule pushFieldAssignLower :
    <[ pushFieldAssign(target, fld, value) ]> ⇝ <[ target.push().fld = value ]>

  sol_rule storagePushLhsToPushValue :
    <[ path.push() = s ]> ⇝ <[ path.push(s) ]>

  sol_rule storageToMemoryDeclUnfoldRightFst :
    <[ T memory mv = nsp.fld ]> ⇝ <[ T storage sp = nsp; T memory mv = sp.fld ]>

  sol_rule storageToMemoryDeclCopyField :
    <[ T memory mv = sp.fld ]> ⇝ { mv := alloc(sp.fld) } <[ ]>

  sol_rule storageToMemoryDeclCopyRoot :
    <[ T memory mv = sp ]> ⇝ { mv := alloc(sp) } <[ ]>

  sol_rule memoryToStorageUnfoldRightFstSource :
    <[ path = nmp ]> ⇝ <[ _ pv = nmp; path = pv ]>
    where cond := path.kind = Kind.storage ∧ isNmp nmp

  sol_rule memoryFieldWriteCopy from memoryFieldWriteCaptureSrc :
    <[ mv1.fld = mv2 ]> ⇝ { memory := writeRef(mv1.fld, mv2) } <[ ]>

  sol_rule memoryIndexWriteCopy twins from memoryIndexWriteArray :
    <[ mv1[i] = mv2 ]> ⇝
      | inBounds(mv1[i]) ⟹ { memory := writeRef(mv1[i], mv2) } <[ ]>
      | else             ⟹ revert()
    after image(mv2), resolve(mv1[i])

  sol_assemble_rules

  end Rules

  /-- A rule of the calculus paired with its effect.  Outside `Rules` so
  that it keeps the name every consumer spells, `Solidity.StepCase`. -/
  structure StepCase where
  rule : RuleName
  effect : StepEffect

  namespace Rules


/-- KeY `transferSemantics:withCallback`: the alternative rule set in
which `transferNoCallback` is replaced by `transferWithCallback`. The
two lists are otherwise identical, mirroring KeY's `\choice`. -/
def ruleNamesWithCallback : List RuleName :=
  (ruleNames.erase .transferNoCallback) ++ [.transferWithCallback]

/-- The two transfer rules fire on exactly the same statements, in the same
modalities.  Their *goals* differ, and that is the whole content of KeY's
`transferSemantics` choice: `transferNoCallback` books the payment and
continues, `transferWithCallback` owes the contract invariant on exit and
resumes under a havoc (`CallbackSemantics.ExecC`).  Before the goals carried
the updates, the two effects were literally equal and this was one `rfl`; the
pair below is what survives, and it is all the coverage argument ever used. -/
theorem transferWithCallback_cond_eq :
    (ruleEffect .transferWithCallback).cond =
      (ruleEffect .transferNoCallback).cond := rfl

theorem transferWithCallback_mode_eq :
    (ruleEffect .transferWithCallback).mode =
      (ruleEffect .transferNoCallback).mode := rfl

def ruleApplies (mode : Modality) (stmt : Stmt) : Prop :=
  ∃ rule, rule ∈ ruleNames ∧
    ((ruleEffect rule).mode stmt).applies mode = true ∧
      (ruleEffect rule).cond stmt

/-- Coverage is unchanged by the `transferSemantics` choice: a statement
has an applicable rule in the withCallback set iff it has one in the
default set. -/
theorem ruleApplies_withCallback_iff (mode : Modality) (stmt : Stmt) :
    (∃ rule, rule ∈ ruleNamesWithCallback ∧
      ((ruleEffect rule).mode stmt).applies mode = true ∧
        (ruleEffect rule).cond stmt) ↔ ruleApplies mode stmt := by
  constructor
  · rintro ⟨rule, hmem, hmode, hcond⟩
    rw [ruleNamesWithCallback, List.mem_append] at hmem
    cases hmem with
    | inl h =>
        exact ⟨rule, List.mem_of_mem_erase h, hmode, hcond⟩
    | inr h =>
        simp only [List.mem_singleton] at h
        subst h
        rw [transferWithCallback_mode_eq] at hmode
        rw [transferWithCallback_cond_eq] at hcond
        exact ⟨.transferNoCallback, by decide, hmode, hcond⟩
  · rintro ⟨rule, hmem, hmode, hcond⟩
    by_cases hr : rule = .transferNoCallback
    · subst hr
      refine ⟨.transferWithCallback, ?_, ?_, ?_⟩
      · rw [ruleNamesWithCallback, List.mem_append]
        exact Or.inr (List.mem_singleton.mpr rfl)
      · rw [transferWithCallback_mode_eq]; exact hmode
      · rw [transferWithCallback_cond_eq]; exact hcond
    · refine ⟨rule, ?_, hmode, hcond⟩
      rw [ruleNamesWithCallback, List.mem_append]
      exact Or.inl ((List.mem_erase_of_ne hr).mpr hmem)

/-- The step case of a rule: its name paired with its effect.  The calculus
has *only* these rules — there is no catch-all tier.  A statement no rule
covers is stuck in the rewrite calculus (see
`Coverage.ResidueShape` for the exact list of such shapes and
`Progress.lean` for the refutation of totality); it is the judgment
layer, not a rewrite rule, that splits a symbolic `if`. -/
def stepCase (rule : RuleName) : StepCase :=
  { rule, effect := ruleEffect rule }

def ruleCases : List StepCase :=
  ruleNames.map stepCase

/-- The generated rule set is exactly the rules of the calculus. -/
def rules : List StepCase :=
  ruleCases

@[simp] theorem stepCase_rule (rule : RuleName) : (stepCase rule).rule = rule := rfl

theorem rules_ruleNames :
    rules.map (fun r => r.rule) = ruleNames := by
  simp only [rules, ruleCases, List.map_map, Function.comp_def, stepCase_rule,
    List.map_id']

end Rules

/-- Which rules a block modality may use.  `.both` admits every case mode:
a rule sound for box and sound for diamond is sound for their conjunction,
and the box/diamond twin rules are effect-identical (their `_cond_eq`
bridges are `rfl`), so under `.both` any applicable twin is as good as the
other.  The previous strict `.both`-only gate made every statement covered
solely by box/diamond twins (pop, index read/write, revert) stuck under
`.both`. -/
def SolidityModality.appliesCaseMode : SolidityModality -> CaseMode -> Bool
  | .box, cm => cm.applies Modality.box
  | .diamond, cm => cm.applies Modality.diamond
  | .both, _ => true

def SolidityModality.ofModality : Modality -> SolidityModality
  | .box => .box
  | .diamond => .diamond

end Solidity
