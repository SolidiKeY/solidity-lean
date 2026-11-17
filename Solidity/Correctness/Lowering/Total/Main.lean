import Solidity.Correctness.Lowering.Total.Production
import Solidity.Correctness.Lowering.Loops.Correct
import Solidity.Source.Infer
import Solidity.Source.Unique
import Solidity.Source.Agreement.Primitive

/-!
# Loop lowering: what the contract still asks (e2b-loops-producer)

`Total.LowerLoopsCorrectContract b i decode` composed with the two theorems that
exist: the production theorem `universalProducerCorrect` (e2d) and the family
theorem `lowerLoopsFamily_correct` (e1). Both hold at every boundary, so:

* `contract_iff_coverage`: the contract is exactly its coverage conjunct.
* `contract_iff`: the interpretation `i` adds nothing beyond `Faithful b i`
  (its four agreement fields); what remains is `Residual b decode`, stated
  against the boundary's own reference interpretation.
* `normalCompatibility_iff`, `returnCompatibility_iff`: the e1 endpoints are
  theorems, so the two compatibility fields say only that `relates` holds of
  every family pair.
* `production_correct`: the consumer whose only premise on the request is its
  successful pipeline; admission comes from `FullDomain b` (the boundary
  admits every request whose pipeline succeeds). The raw `LowersTo` conjunct
  is for top-level requests only: nothing is stated of the `lowerLoops` run
  inside `calleeBody`.
* `Residual.of_empty`: a boundary admitting nothing, whose `relates` holds of
  the e1 families, satisfies the residual. So the contract alone does not rule
  out input exclusion, and `FullDomain` is a separate obligation.

The concrete boundary is begun below, not finished:

* `Decode.decode` is the raw-to-Source decoder (stage 1): canonical Source
  spelling, then the existing Source inference and resolution. It is defined
  on top-level requests outside `unchecked`/`checked` scopes, over primitive
  full-width locals and state variables: expressions, simple statements,
  branches, blocks, `unchecked` and the loops. Elsewhere it is `none`, a
  coverage gap. Its spellings are choices; none is proved to agree with the
  model elaborator.
* `loopEntry` admits every request whose lowering, elaboration and placement
  all succeed. A request whose lowering succeeds but whose elaboration or
  placement fails is not admitted: at top level it still has `LowersTo`
  (`Request.lowers`), as a callee nothing is stated of it.
* `loopAssociated` is `Spells` (H1024): an inductive spelling relation and
  Source typing derivations, not the decoder. `decode_spells` proves the
  decoder sound for it and `Spells.decode` complete if Source inference is
  complete (`InferComplete`, not proved in the Source front end). `Spells`
  shares the decoder's small tables, so those rest on review.
* `loopBoundary_fullDomain` and `loopResidual_iff` state what is left once
  admission and association are fixed.
* `Observe.source`/`Observe.target` are the observation policies (H1021): no
  events, the kind of the outcome at the first completing horizon.
* `Simulation.Simulates rel` is `relates` (H1022): one general simulation,
  which the e1 endpoints imply (`of_endpoint`, `of_retEndpoint`).
  It is relative to a state relation `rel`.
* `Allocation.trace` is the allocation trace (H1023): one scope per run.
* `loopBoundaryAt rel` assembles them with `rel` unbound. For a `rel` that
  reflects Booleans and relates `false` to `false`, `loopResidualAt_iff` gives
  the four obligations left and the two family obligations follow. No such
  `rel` is required to be non-degenerate by these two hypotheses.
* `loopRel` is the stage-1 state relation (Q-9 answer): primitive values,
  primitive state variables of the running account, `msg.value` and the
  timestamp; the rest of the state is unrelated. `loopBoundaryStage1` is the
  boundary at it, a closed term, with `loopResidualStage1_iff`.

Each of the three choices has known defects, listed at its section: the
policies observe the outcome kind only and allow every environment, the
simulation can hold vacuously, and the allocation trace is incomplete. The
boundary is therefore not ready to carry the goal.

Not proved, and partly not provable yet: the fields `allocation` and `pipeline`
take as hypothesis a successful run of `elabStmtsP` and, for a callee, of
`calleeBody`, which runs `renameStmts`, `lowerReturns` and `wrapMods`. All four
are `partial`, so opaque to the kernel: the hypothesis says nothing about the
elaborated program, and no request's `Request.Succeeds` can be derived (it can
be refuted where top-level lowering, which is total, fails). So the decoder's
coverage obligation cannot be proved today; once the elaborator is total it
fails on the first successful request in a listed gap. Also not proved:
`InferComplete`, and that `loopRel` has any related pair. `Solidity.Goals.lowerLoopsCorrect`
stays unstated until the boundary is complete.
-/
namespace Solidity.Correctness.Lowering.Total

open Solidity.Roadmap.G49Final

/-- `relates` holds of every pair of the e1 normal-outcome family. -/
def RelatesNormalFamily (b : SemanticBoundary) : Prop :=
  ∀ k {E srcΓ returns M l u C Γ} (m : Lowering.V07.ContextMap srcΓ Γ) (pair : Loops.Pair m)
    (extra : Loops.Shape.Extra E returns M u srcΓ C Γ k) names,
    b.relates (SourceProgram.ofStmt (Loops.Shape.source (l := l) k pair extra))
      (k.lowered pair extra names)

/-- `relates` holds of every pair of the e1 return family. -/
def RelatesReturnFamily (b : SemanticBoundary) : Prop :=
  ∀ k {E srcΓ M l u C Γ} (m : Lowering.V07.ContextMap srcΓ Γ) (pair : Loops.Pair m)
    (extra : Loops.RetShape.Extra E srcΓ C Γ k) names,
    b.relates (SourceProgram.ofStmt (Loops.RetShape.source (M := M) (l := l) (u := u) k pair extra))
      ⟨_, k.program pair extra names⟩

/-- The e1 normal endpoint is a theorem, so compatibility is membership. -/
theorem normalCompatibility_iff (b : SemanticBoundary) :
    NormalCompatibility b ↔ RelatesNormalFamily b := by
  constructor
  · intro h k E srcΓ returns M l u C Γ m pair extra names
    exact (h k m pair extra names).mpr (normalFamily_correct k m pair extra names _ rfl)
  · intro h k E srcΓ returns M l u C Γ m pair extra names
    exact ⟨fun _ => normalFamily_correct k m pair extra names _ rfl,
      fun _ => h k m pair extra names⟩

/-- The e1 return endpoint is a theorem, so compatibility is membership. -/
theorem returnCompatibility_iff (b : SemanticBoundary) :
    ReturnCompatibility b ↔ RelatesReturnFamily b := by
  constructor
  · intro h k E srcΓ M l u C Γ m pair extra names
    exact (h k m pair extra names).mpr (returnFamily_correct k m pair extra names)
  · intro h k E srcΓ M l u C Γ m pair extra names
    exact ⟨fun _ => returnFamily_correct k m pair extra names, fun _ => h k m pair extra names⟩

/-- The production and family conjuncts hold at every boundary. -/
theorem contract_iff_coverage (b : SemanticBoundary) (i : RawSourceInterpretation)
    (decode : Request → Option SourceProgram) :
    LowerLoopsCorrectContract b i decode ↔ CoverageObligations b i decode :=
  ⟨fun h => h.2.1, fun h => ⟨universalProducerCorrect, h, lowerLoopsFamily_correct⟩⟩

/-- The interpretation agrees with the boundary's reference. -/
structure Faithful (b : SemanticBoundary) (i : RawSourceInterpretation) : Prop where
  admitted : ∀ r, i.entry r ↔ b.reference.entry r
  association : ∀ r s, i.associated r s ↔ b.reference.associated r s
  source : ∀ s, (i.source s).behaviour = (b.reference.source s).behaviour
  target : ∀ {C Γ} (p : Blk C Γ), (i.target p).behaviour = (b.reference.target p).behaviour

theorem Faithful.refl (b : SemanticBoundary) : Faithful b b.reference :=
  ⟨fun _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => rfl, fun _ => rfl⟩

/-- What the contract asks of a boundary and a decoder, with no interpretation
left: every admitted request decodes, to its one associated Source program;
every successful pipeline of an admitted request has a safe allocation trace,
is related to that program and refines it; and the e1 families are related. -/
structure Residual (b : SemanticBoundary) (decode : Request → Option SourceProgram) : Prop where
  total : ∀ r, b.reference.entry r → ∃ s, decode r = some s
  decoder : ∀ r s, b.reference.entry r → (decode r = some s ↔ b.reference.associated r s)
  allocation : ∀ r o after parts program, b.reference.entry r →
    r.pipeline o after parts program →
    ∃ scopes, b.allocations r o after parts program scopes ∧
      ∀ scope ∈ scopes, SafeSpellings r.input.names scope.protectedNames scope.generated
  pipeline : ∀ r o after parts program s, b.reference.entry r → decode r = some s →
    r.pipeline o after parts program →
    b.relates s program ∧
      Nonempty (PassCorrect (b.reference.source s).behaviour (b.reference.target program).behaviour)
  normal : RelatesNormalFamily b
  returns : RelatesReturnFamily b

/-- Coverage is faithfulness of the interpretation together with the residual. -/
theorem coverage_iff (b : SemanticBoundary) (i : RawSourceInterpretation)
    (decode : Request → Option SourceProgram) :
    CoverageObligations b i decode ↔ Faithful b i ∧ Residual b decode := by
  constructor
  · intro h
    refine ⟨⟨h.admitted, h.association, h.sourceFaithful, h.targetFaithful⟩, ?_, ?_, ?_, ?_,
      (normalCompatibility_iff b).mp h.normal, (returnCompatibility_iff b).mp h.returns⟩
    · intro r e
      obtain ⟨s, a⟩ := h.source r ((h.admitted r).mpr e)
      exact ⟨s, (h.decoder r s ((h.admitted r).mpr e)).mpr a⟩
    · intro r s e
      exact (h.decoder r s ((h.admitted r).mpr e)).trans (h.association r s)
    · intro r o after parts program e run
      exact h.allocation r o after parts program ((h.admitted r).mpr e) run
    · intro r o after parts program s e d run
      have p : b.relates s program ∧
          Nonempty (PassCorrect (i.source s).behaviour (i.target program).behaviour) :=
        h.pipeline r o after parts program s ((h.admitted r).mpr e) d run
      exact ⟨p.1, h.sourceFaithful s ▸ h.targetFaithful program ▸ p.2⟩
  · intro ⟨f, h⟩
    refine ⟨f.admitted, f.association, f.source, f.target, ?_, ?_, ?_, ?_,
      (normalCompatibility_iff b).mpr h.normal, (returnCompatibility_iff b).mpr h.returns⟩
    · intro r o after parts program e run
      exact h.allocation r o after parts program ((f.admitted r).mp e) run
    · intro r e
      obtain ⟨s, d⟩ := h.total r ((f.admitted r).mp e)
      exact ⟨s, (f.association r s).mpr ((h.decoder r s ((f.admitted r).mp e)).mp d)⟩
    · intro r s e
      exact (h.decoder r s ((f.admitted r).mp e)).trans (f.association r s).symm
    · intro r o after parts program s e d run
      have p : b.relates s program ∧ Nonempty (PassCorrect (b.reference.source s).behaviour
          (b.reference.target program).behaviour) :=
        h.pipeline r o after parts program s ((f.admitted r).mp e) d run
      exact ⟨p.1, (f.source s).symm ▸ (f.target program).symm ▸ p.2⟩

/-- **The contract, composed with e2d and e1**: at every boundary,
interpretation and decoder it is faithfulness and the residual. -/
theorem contract_iff (b : SemanticBoundary) (i : RawSourceInterpretation)
    (decode : Request → Option SourceProgram) :
    LowerLoopsCorrectContract b i decode ↔ Faithful b i ∧ Residual b decode :=
  (contract_iff_coverage b i decode).trans (coverage_iff b i decode)

/-- At the reference interpretation the contract is the residual. -/
theorem contract_reference_iff (b : SemanticBoundary) (decode : Request → Option SourceProgram) :
    LowerLoopsCorrectContract b b.reference decode ↔ Residual b decode :=
  (contract_iff b b.reference decode).trans ⟨fun h => h.2, fun h => ⟨Faithful.refl b, h⟩⟩

/-- An admitted request has one associated Source program: the decoded one. -/
theorem Residual.associated_unique {b : SemanticBoundary}
    {decode : Request → Option SourceProgram} (h : Residual b decode) {r : Request}
    {s s' : SourceProgram} (e : b.reference.entry r) (a : b.reference.associated r s)
    (a' : b.reference.associated r s') : s = s' :=
  Option.some.inj (((h.decoder r s e).mpr a).symm.trans ((h.decoder r s' e).mpr a'))

/-- The request's whole pipeline succeeds: lowering (for a callee, the callee
body pass) and then intrinsic elaboration and placement. -/
def Request.Succeeds (r : Request) : Prop :=
  ∃ o after parts program, r.pipeline o after parts program

/-- Every request whose whole pipeline succeeds is admitted. A lowering whose
elaboration or placement then fails is outside this statement. -/
def FullDomain (b : SemanticBoundary) : Prop :=
  ∀ r, r.Succeeds → b.reference.entry r

/-- A successful top-level run is in the relation; no admission is used. -/
theorem Request.lowers (r : Request) (o : ProductionOutput) (top : r.callee = none)
    (run : r.success o) :
    @LowersTo r.input.names r.input.returnSlots r.input.raw o.raw r.input.scope r.input.before
      o.after := by
  obtain ⟨C, input, callee⟩ := r
  cases top
  exact universalProducerCorrect input o run

/-- **Production correctness from the residual and `FullDomain`**: the only
premise on the request is its own successful pipeline. The `LowersTo` conjunct
is for top-level requests; for a callee only the semantic conjuncts are stated.
The pipeline premise runs the `partial` elaborator, so this cannot yet be
applied to a concrete run. -/
theorem production_correct {b : SemanticBoundary} {decode : Request → Option SourceProgram}
    (h : Residual b decode) (full : FullDomain b) (r : Request) (o : ProductionOutput)
    (after : Checker.Snapshot) (parts : SProg r.contract) (program : Blk r.contract r.context.ctx)
    (run : r.pipeline o after parts program) :
    (r.callee = none →
      @LowersTo r.input.names r.input.returnSlots r.input.raw o.raw r.input.scope r.input.before
        o.after) ∧
    (∃ scopes, b.allocations r o after parts program scopes ∧
      ∀ scope ∈ scopes, SafeSpellings r.input.names scope.protectedNames scope.generated) ∧
    ∃ s, decode r = some s ∧ b.reference.associated r s ∧ b.relates s program ∧
      Nonempty (PassCorrect (b.reference.source s).behaviour
        (b.reference.target program).behaviour) := by
  have e : b.reference.entry r := full r ⟨o, after, parts, program, run⟩
  obtain ⟨s, d⟩ := h.total r e
  exact ⟨fun top => r.lowers o top run.1, h.allocation r o after parts program e run,
    s, d, (h.decoder r s e).mp d, h.pipeline r o after parts program s e d run⟩

/-- Negative control: a boundary that admits nothing satisfies the residual at
every decoder once `relates` holds of the families. So the contract does not
exclude an empty admission by itself; `FullDomain` is a separate obligation. -/
theorem Residual.of_empty (b : SemanticBoundary) (decode : Request → Option SourceProgram)
    (empty : ∀ r, ¬ b.reference.entry r) (normal : RelatesNormalFamily b)
    (returns : RelatesReturnFamily b) : Residual b decode :=
  ⟨fun r e => absurd e (empty r), fun r _ e => absurd e (empty r),
    fun r _ _ _ _ e => absurd e (empty r), fun r _ _ _ _ _ e => absurd e (empty r),
    normal, returns⟩

/-! ## The concrete raw-to-Source decoder (stage 1)

`decode` reads a request's raw input as Source: a chosen Source syntax tree
for the raw statements (`Spelling`), typed by the existing Source inference
(`Source.ItemsD.infer`) and resolved by `ItemsD.toR`, in the Source unit whose
one contract declares the model contract's primitive state variables. Nothing
is checked against the lowered output: the decoder sees only the request.

A `none` is a coverage gap, not an exclusion: admission is fixed separately
(`loopEntry`), so a successful request in a gap leaves the coverage obligation
of `loopResidual_iff` open. The main gaps are listed at each definition; the
lists are not exhaustive (a cast written as a call, `msg.sender` used as a
`uint`, a braced single declaration read unbraced, nested `unchecked`, a `for`
with several initializers or updates are further ones). Each
`some` is a chosen spelling; that it agrees with the model's reading of the
same raw construct is part of the `pipeline` obligation, not shown here. -/
namespace Decode

open Source (Syn SCtx STy)

/-- The contract name of the canonical unit (the model contract has none). -/
def contractName : String := "C"

/-- A decimal literal with no fraction and no exponent. -/
def num (n : Nat) : Syn .expr := .lit (.num (.dec n 0 0))

def uintElem : Source.Elem := .int false 256 (by decide)
def intElem : Source.Elem := .int true 256 (by decide)

/-- Binary operators. The wrapping forms (`addW` …) have no Source operator:
Source wraps by an enclosing `unchecked` block. Model `>>` is spelled `sar`. -/
def binop : BinOp → Option (Syn .expr → Syn .expr → Syn .expr)
  | .add => some (.addSub .add) | .sub => some (.addSub .sub)
  | .mul => some (.mulDivMod .mul) | .div => some (.mulDivMod .div)
  | .mod => some (.mulDivMod .mod) | .pow => some .exp
  | .lt => some (.order .lt) | .gt => some (.order .gt)
  | .le => some (.order .le) | .ge => some (.order .ge)
  | .eqB => some (.equality .eq) | .neB => some (.equality .ne)
  | .and => some .and | .or => some .or
  | .band => some .bitAnd | .bor => some .bitOr | .bxor => some .bitXor
  | .shl => some (.shift .shl) | .shr => some (.shift .sar)
  | .addW | .subW | .mulW | .powW => none

/-- Compound assignment operators (`x op= e`). -/
def assignOp : BinOp → Option Source.AssignOp
  | .add => some .add | .sub => some .sub | .mul => some .mul | .div => some .div
  | .mod => some .mod | .band => some .bitAnd | .bor => some .bitOr | .bxor => some .bitXor
  | .shl => some .shl | .shr => some .sar
  | _ => none

/-- Environment reads. `msg.sender`, `address(this)` and its balance are gaps:
the model has erased the address type and the state relation does not relate
them. -/
def env : EnvKey → Option (Syn .expr)
  | .msgValue => some (.member (.ident "msg") "value")
  | .timestamp => some (.member (.ident "block") "timestamp")
  | .msgSender | .selfBalance | .selfAddress => none

mutual
/-- Expressions. Gaps: `newArr`, `named`, the wrapping operators, a tuple of
fewer than two components, `address(this)`. -/
def expr : RawExpr → Option (Syn .expr)
  | .num n => some (num n)
  | .name x => some (.ident x)
  | .bool b => some (.lit (.bool b))
  | .field e f => (expr e).map (.member · f)
  | .index e k => do pure (.index (← expr e) (.some (← expr k)))
  | .binop op a b => do pure ((← binop op) (← expr a) (← expr b))
  | .unop .neg a => (expr a).map (.unaryPrefix .neg)
  | .unop .not a => (expr a).map (.unaryPrefix .not)
  | .unop .bnot a => (expr a).map (.unaryPrefix .bitNot)
  | .unop .toInt a => (expr a).map fun a =>
      .call (.elemType intElem (by decide)) (.positional (.cons a .nil))
  | .unop .toUint a => (expr a).map fun a =>
      .call (.elemType uintElem (by decide)) (.positional (.cons a .nil))
  | .ternary c a b => do pure (.cond (← expr c) (← expr a) (← expr b))
  | .incDec .preInc e => (expr e).map (.unaryPrefix .inc)
  | .incDec .preDec e => (expr e).map (.unaryPrefix .dec)
  | .incDec .postInc e => (expr e).map (.unarySuffix .inc)
  | .incDec .postDec e => (expr e).map (.unarySuffix .dec)
  | .call f args => (exprs args).map fun args => .call (.ident f) (.positional args)
  | .modular op a b k => do
      pure (.call (.ident op.toStr)
        (.positional (.cons (← expr a) (.cons (← expr b) (.cons (← expr k) .nil)))))
  | .env k => env k
  | .tuple (a :: b :: rest) => do
      pure (.tuple (.some (← expr a)) (.cons (.some (← expr b)) (← components rest)))
  | .assign l r => do pure (.assign .assign (← expr l) (← expr r))
  | .opAssign op l r => do pure (.assign (← assignOp op) (← expr l) (← expr r))
  | _ => none
/-- Argument lists, in order. -/
def exprs : List RawExpr → Option (Syn (.list .expr))
  | [] => some .nil
  | e :: es => do pure (.cons (← expr e) (← exprs es))
/-- The remaining components of a tuple; none is left out. -/
def components : List RawExpr → Option (Syn (.list (.opt .expr)))
  | [] => some .nil
  | e :: es => do pure (.cons (.some (← expr e)) (← components es))
end

/-- Local declaration types: the three primitive types by their canonical
names. Narrow integers, `address`, references and user types are gaps. -/
def typeName : RawTy → Option (Syn .typeName)
  | .named "bool" => some (.elem .bool)
  | .named "uint" | .named "uint256" => some (.elem uintElem)
  | .named "int" | .named "int256" => some (.elem intElem)
  | _ => none

/-- Simple statements: a declaration, an assignment, an update, a builtin
call. `require`, `assert` and `revert()` are spelled as calls of the Source
builtins. The modifier hole is a gap: the context is never a modifier's. -/
def simple : RawStmt → Option (Syn .simple)
  | .assign l r => do pure (.exprStmt (.assign .assign (← expr l) (← expr r)))
  | .decl T x none => (typeName T).map fun T => .declVar (.varDecl T none x) .none
  | .decl T x (some e) => do pure (.declVar (.varDecl (← typeName T) none x) (.some (← expr e)))
  | .opAssign op l r => do pure (.exprStmt (.assign (← assignOp op) (← expr l) (← expr r)))
  | .incDec op l => (expr (.incDec op l)).map .exprStmt
  | .require c => (expr c).map fun c =>
      .exprStmt (.call (.ident "require") (.positional (.cons c .nil)))
  | .assert c => (expr c).map fun c =>
      .exprStmt (.call (.ident "assert") (.positional (.cons c .nil)))
  | .revert => some (.exprStmt (.call (.ident "revert") (.positional .nil)))
  | _ => none

/-- A `for` update: one expression statement. -/
def update : List RawStmt → Option (Syn (.opt .expr))
  | [] => some .none
  | [.assign l r] => do pure (.some (.assign .assign (← expr l) (← expr r)))
  | [.opAssign op l r] => do pure (.some (.assign (← assignOp op) (← expr l) (← expr r)))
  | [.incDec op l] => (expr (.incDec op l)).map .some
  | _ => none

/-- A `for` initializer: one simple statement. -/
def initializer : List RawStmt → Option (Syn (.opt .simple))
  | [] => some .none
  | [s] => (simple s).map .some
  | _ => none

/-- `break` and `continue` exist only inside a loop. -/
def jump (brk : Bool) : (k : SCtx) → Option (Syn (.stmt k))
  | ⟨true, _⟩ => some (if brk then .breakStmt else .continueStmt)
  | ⟨false, _⟩ => none

/-- An `unchecked` block is an item of a checked block only. -/
def uncheckedItem : (k : SCtx) → Syn (.list (.item ⟨k.loop, true⟩)) → Option (Syn (.item k))
  | ⟨_, false⟩, b => some (.uncheckedItem (.block b))
  | ⟨_, true⟩, _ => none

/-- A loop body or a branch from its items. The raw syntax does not record
braces: exactly one statement is read unbraced, anything else as a block. -/
def unbrace {k : SCtx} : Syn (.list (.item k)) → Syn (.stmt k)
  | .cons (.stmtItem s) .nil => s
  | b => .blockStmt (.block b)

mutual
/-- Statements in control context `k`. Bodies and branches are read by
`unbrace`; an empty `else` is read as absent. Loop specifications are
annotations with no Source syntax and are not read. A lowered `loop` is
spelled as a `while`. Gaps: every statement not listed here or in
`simple` (storage and memory declarations, `delete`, pushes, calls as
statements, tuples, `try`, sends, reverts with data, `eval`, `checked`,
`assumeFalse`). -/
def stmt (k : SCtx) : RawStmt → Option (Syn (.stmt k))
  | .ite c thn els => do
      let c ← expr c
      let thn ← items k thn
      match els with
      | [] => pure (.ifStmt c (unbrace thn) .none)
      | e :: els => pure (.ifStmt c (unbrace thn) (.some (unbrace (← items k (e :: els)))))
  | .ret none => some (.returnStmt .none)
  | .ret (some e) => (expr e).map fun e => .returnStmt (.some e)
  | .block b => (items k b).map fun b => .blockStmt (.block b)
  | .whileLoop _ c b | .loop _ c b => do
      pure (.whileStmt (← expr c) (unbrace (← items ⟨true, k.unchecked⟩ b)))
  | .doWhile _ b c => do
      pure (.doWhile (unbrace (← items ⟨true, k.unchecked⟩ b)) (← expr c))
  | .forLoop _ init c upd b => do
      let init ← initializer init
      let c ← match c with
        | none => pure .none
        | some c => (expr c).map Syn.some
      pure (.forStmt init c (← update upd) (unbrace (← items ⟨true, k.unchecked⟩ b)))
  | .brk => jump true k
  | .cont => jump false k
  | s => (simple s).map .simpleStmt
/-- The items of a block. -/
def items (k : SCtx) : List RawStmt → Option (Syn (.list (.item k)))
  | [] => some .nil
  | .unchecked b :: rest => do
      pure (.cons (← uncheckedItem k (← items ⟨k.loop, true⟩ b)) (← items k rest))
  | s :: rest => do pure (.cons (.stmtItem (← stmt k s)) (← items k rest))
end

/-- Source type of a model local: a full-width primitive with no shape rows.
Narrow locals, locals carrying a shape (the marker of an erased `address`,
`bytes32`, enum or function type), references and formula locals are gaps. -/
def localTy : LocalTy → Option STy
  | .val p 256 [] => some (Source.Agreement.sourceTy p)
  | _ => none

/-- The Source locals of a model context, innermost first, by name. -/
def locals : ECtx → Option (List (String × STy))
  | [] => some []
  | (x, t) :: Γ => do pure ((x, ← localTy t) :: (← locals Γ))

/-- State variable types: primitive only (references are gaps). A model `uint`
is spelled `uint256` even where the original declared `address` or an enum:
the model has erased that, and `relates` must absorb it. -/
def stateTy : Ty → Option (Syn .typeName)
  | .prim .bool => some (.elem .bool)
  | .prim .uint => some (.elem uintElem)
  | .prim .int => some (.elem intElem)
  | _ => none

/-- The state variables, in declaration order. Transient roots are gaps. -/
def stateVars : List (Name × Ty) → Option (Syn (.list (.part false)))
  | [] => some .nil
  | (x, T) :: rest => do
      pure (.cons (.stateVar (← stateTy T) none none none false x .none) (← stateVars rest))

/-- The canonical Source unit of a model contract: one contract with its
state variables. Functions, enums, the constructor, initializers and narrow
widths are not spelled, so a request that calls a function, or whose contract
has any of them, is a gap. -/
def unit (C : Contract) : Option (Syn .unit) :=
  if C.transientRoots.isEmpty && C.funs.isEmpty && C.enums.isEmpty && C.ctor.isNone &&
      C.widths.isEmpty && C.inits.isEmpty then
    (stateVars C.vars).map fun parts =>
      .unit (.cons (.contract false contractName .none .nil parts) .nil)
  else none

/-- The request parts the decoder cannot read yet. It reads the contract,
the raw input and the caller's locals only, so a request whose meaning depends
on anything else is a gap, never a guess: a callee body (renaming, modifiers,
constructor initializers, self frame, declared returns), return slots, and a
scope inside `unchecked`, `checked` or `ignoringOverflow`. -/
def plain (r : Request) : Bool :=
  r.callee.isNone && r.input.returnSlots.isNone && !r.input.scope.unchecked &&
    r.input.scope.overflow.isNone

/-- The Source typing context of a request, with no locals yet: the canonical
unit, inside its contract, in a function that returns nothing. -/
def context (r : Request) : Option Source.Ctx :=
  (unit r.contract).map fun u =>
    { env := u.env, scope := some contractName, locals := [], rets := [] }

/-- **The decoder (stage 1).** A plain request's raw input in its canonical
Source spelling, typed and resolved by the Source front end against the
caller's locals. The result is the decoder's choice of Source program: that it
means what the model elaborator gives the same raw input is not proved here;
it is the `pipeline` obligation, once `relates` and the policies are fixed. -/
def decode (r : Request) : Option SourceProgram :=
  if plain r then do
    let C ← context r
    let L ← locals r.input.before.locals.1
    let b ← items .body r.input.raw
    let ⟨L', d⟩ ← Source.ItemsD.infer C L b
    pure ⟨C.env, C.rets, C.inModifier, .body, Source.tysOf L, Source.tysOf L', d.toR⟩
  else none

end Decode

/-! ## The spelling relation (H1024)

An inductive relation between raw and Source syntax, written without the
decoder's functions, and `Spells` on requests, written with Source typing
derivations instead of the inference function. The decoder is proved sound for
it (`decode_spells`) and, if Source inference is complete, complete
(`Spells.decode`). It shares the decoder's operator, type and environment
tables, its `unbrace`, its `plain` test and its reading of the request's unit
and locals, and its constructors repeat the decoder's spelling choices. So it
is an independent check of the recursion and of inference, not of the choices. -/
namespace Spells
open Source (Syn SCtx STy)
open Decode (num uintElem intElem unbrace)

mutual
inductive Expr : RawExpr → Syn .expr → Prop where
  | num (n : Nat) : Expr (.num n) (num n)
  | name (x : String) : Expr (.name x) (.ident x)
  | bool (b : Bool) : Expr (.bool b) (.lit (.bool b))
  | field {e e'} (f : String) : Expr e e' → Expr (.field e f) (.member e' f)
  | index {e e' k k'} : Expr e e' → Expr k k' → Expr (.index e k) (.index e' (.some k'))
  | binop {op f a a' b b' t} : Decode.binop op = some f → Expr a a' → Expr b b' →
      t = f a' b' → Expr (.binop op a b) t
  | neg {a a'} : Expr a a' → Expr (.unop .neg a) (.unaryPrefix .neg a')
  | not {a a'} : Expr a a' → Expr (.unop .not a) (.unaryPrefix .not a')
  | bnot {a a'} : Expr a a' → Expr (.unop .bnot a) (.unaryPrefix .bitNot a')
  | toInt {a a'} : Expr a a' → Expr (.unop .toInt a)
      (.call (.elemType intElem (by decide)) (.positional (.cons a' .nil)))
  | toUint {a a'} : Expr a a' → Expr (.unop .toUint a)
      (.call (.elemType uintElem (by decide)) (.positional (.cons a' .nil)))
  | ternary {c c' a a' b b'} : Expr c c' → Expr a a' → Expr b b' →
      Expr (.ternary c a b) (.cond c' a' b')
  | preInc {e e'} : Expr e e' → Expr (.incDec .preInc e) (.unaryPrefix .inc e')
  | preDec {e e'} : Expr e e' → Expr (.incDec .preDec e) (.unaryPrefix .dec e')
  | postInc {e e'} : Expr e e' → Expr (.incDec .postInc e) (.unarySuffix .inc e')
  | postDec {e e'} : Expr e e' → Expr (.incDec .postDec e) (.unarySuffix .dec e')
  | call {args args'} (f : String) : Exprs args args' →
      Expr (.call f args) (.call (.ident f) (.positional args'))
  | modular {a a' b b' k k'} (op : ModOp) : Expr a a' → Expr b b' → Expr k k' →
      Expr (.modular op a b k)
        (.call (.ident op.toStr) (.positional (.cons a' (.cons b' (.cons k' .nil)))))
  | env {k t} : Decode.env k = some t → Expr (.env k) t
  | tuple {a a' b b' rest rest'} : Expr a a' → Expr b b' → Components rest rest' →
      Expr (.tuple (a :: b :: rest)) (.tuple (.some a') (.cons (.some b') rest'))
  | assign {l l' r r'} : Expr l l' → Expr r r' → Expr (.assign l r) (.assign .assign l' r')
  | opAssign {op o l l' r r'} : Decode.assignOp op = some o → Expr l l' → Expr r r' →
      Expr (.opAssign op l r) (.assign o l' r')
inductive Exprs : List RawExpr → Syn (.list .expr) → Prop where
  | nil : Exprs [] .nil
  | cons {e e' es es'} : Expr e e' → Exprs es es' → Exprs (e :: es) (.cons e' es')
inductive Components : List RawExpr → Syn (.list (.opt .expr)) → Prop where
  | nil : Components [] .nil
  | cons {e e' es es'} : Expr e e' → Components es es' →
      Components (e :: es) (.cons (.some e') es')
end

mutual
theorem Expr.decode : ∀ {e t}, Expr e t → Decode.expr e = some t
  | _, _, .num _ | _, _, .name _ | _, _, .bool _ => by simp [Decode.expr]
  | _, _, .field _ h => by simp [Decode.expr, h.decode]
  | _, _, .index h k => by simp [Decode.expr, h.decode, k.decode]
  | _, _, .binop o h k e => by simp [Decode.expr, o, h.decode, k.decode, e]
  | _, _, .neg h | _, _, .not h | _, _, .bnot h | _, _, .toInt h | _, _, .toUint h
  | _, _, .preInc h | _, _, .preDec h | _, _, .postInc h | _, _, .postDec h => by
      simp [Decode.expr, h.decode]
  | _, _, .ternary c a b => by simp [Decode.expr, c.decode, a.decode, b.decode]
  | _, _, .call _ h => by simp [Decode.expr, h.decode]
  | _, _, .modular _ a b k => by simp [Decode.expr, a.decode, b.decode, k.decode]
  | _, _, .env h => by simp [Decode.expr, h]
  | _, _, .tuple a b r => by simp [Decode.expr, a.decode, b.decode, r.decode]
  | _, _, .assign l r => by simp [Decode.expr, l.decode, r.decode]
  | _, _, .opAssign o l r => by simp [Decode.expr, o, l.decode, r.decode]
theorem Exprs.decode : ∀ {es t}, Exprs es t → Decode.exprs es = some t
  | _, _, .nil => by simp [Decode.exprs]
  | _, _, .cons h k => by simp [Decode.exprs, h.decode, k.decode]
theorem Components.decode : ∀ {es t}, Components es t → Decode.components es = some t
  | _, _, .nil => by simp [Decode.components]
  | _, _, .cons h k => by simp [Decode.components, h.decode, k.decode]
end


/-- Split the binds of a decoder equation. -/
local macro "bind_simp" " at " h:ident : tactic =>
  `(tactic| simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, Option.some.injEq, reduceCtorEq, exists_const, false_and,
      exists_false] at $h:ident)

/-- Unfold one decoder equation and split its binds. -/
local macro "spell_simp " f:ident " at " h:ident : tactic =>
  `(tactic| simp only [$f:ident, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, Option.some.injEq, reduceCtorEq, exists_const, false_and,
      exists_false] at $h:ident)

mutual
theorem expr_spells : (e : RawExpr) → (t : Syn .expr) → Decode.expr e = some t → Expr e t
  | .num n, t, h => by spell_simp Decode.expr at h; subst h; exact .num n
  | .name x, t, h => by spell_simp Decode.expr at h; subst h; exact .name x
  | .bool b, t, h => by spell_simp Decode.expr at h; subst h; exact .bool b
  | .field e f, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a, ha, rfl⟩ := h; exact .field f (expr_spells _ _ ha)
  | .index e k, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact .index (expr_spells _ _ ha) (expr_spells _ _ hb)
  | .binop op a b, t, h => by
      spell_simp Decode.expr at h; obtain ⟨f, hf, a', ha, b', hb, rfl⟩ := h
      exact .binop hf (expr_spells _ _ ha) (expr_spells _ _ hb) rfl
  | .unop .neg a, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .neg (expr_spells _ _ ha)
  | .unop .not a, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .not (expr_spells _ _ ha)
  | .unop .bnot a, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .bnot (expr_spells _ _ ha)
  | .unop .toInt a, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .toInt (expr_spells _ _ ha)
  | .unop .toUint a, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .toUint (expr_spells _ _ ha)
  | .ternary c a b, t, h => by
      spell_simp Decode.expr at h; obtain ⟨c', hc, a', ha, b', hb, rfl⟩ := h
      exact .ternary (expr_spells _ _ hc) (expr_spells _ _ ha) (expr_spells _ _ hb)
  | .incDec .preInc e, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .preInc (expr_spells _ _ ha)
  | .incDec .preDec e, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .preDec (expr_spells _ _ ha)
  | .incDec .postInc e, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .postInc (expr_spells _ _ ha)
  | .incDec .postDec e, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .postDec (expr_spells _ _ ha)
  | .call f args, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .call f (exprs_spells _ _ ha)
  | .modular op a b k, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, b', hb, k', hk, rfl⟩ := h
      exact .modular op (expr_spells _ _ ha) (expr_spells _ _ hb) (expr_spells _ _ hk)
  | .env k, t, h => by spell_simp Decode.expr at h; exact .env h
  | .tuple (a :: b :: rest), t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, b', hb, r', hr, rfl⟩ := h
      exact .tuple (expr_spells _ _ ha) (expr_spells _ _ hb) (components_spells _ _ hr)
  | .assign l r, t, h => by
      spell_simp Decode.expr at h; obtain ⟨l', hl, r', hr, rfl⟩ := h
      exact .assign (expr_spells _ _ hl) (expr_spells _ _ hr)
  | .opAssign op l r, t, h => by
      spell_simp Decode.expr at h; obtain ⟨o, ho, l', hl, r', hr, rfl⟩ := h
      exact .opAssign ho (expr_spells _ _ hl) (expr_spells _ _ hr)
  | .newArr .., _, h | .named .., _, h | .tuple [], _, h | .tuple [_], _, h => by
      spell_simp Decode.expr at h
theorem exprs_spells : (es : List RawExpr) → (t : Syn (.list .expr)) →
    Decode.exprs es = some t → Exprs es t
  | [], t, h => by spell_simp Decode.exprs at h; subst h; exact .nil
  | e :: es, t, h => by
      spell_simp Decode.exprs at h; obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact .cons (expr_spells _ _ ha) (exprs_spells _ _ hb)
theorem components_spells : (es : List RawExpr) → (t : Syn (.list (.opt .expr))) →
    Decode.components es = some t → Components es t
  | [], t, h => by spell_simp Decode.components at h; subst h; exact .nil
  | e :: es, t, h => by
      spell_simp Decode.components at h; obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact .cons (expr_spells _ _ ha) (components_spells _ _ hb)
end

/-- Simple statements. -/
inductive Simple : RawStmt → Syn .simple → Prop where
  | assign {l l' r r'} : Expr l l' → Expr r r' →
      Simple (.assign l r) (.exprStmt (.assign .assign l' r'))
  | declNone {T T'} (x : String) : Decode.typeName T = some T' →
      Simple (.decl T x none) (.declVar (.varDecl T' none x) .none)
  | declSome {T T' e e'} (x : String) : Decode.typeName T = some T' → Expr e e' →
      Simple (.decl T x (some e)) (.declVar (.varDecl T' none x) (.some e'))
  | opAssign {op o l l' r r'} : Decode.assignOp op = some o → Expr l l' → Expr r r' →
      Simple (.opAssign op l r) (.exprStmt (.assign o l' r'))
  | incDec {op l t} : Expr (.incDec op l) t → Simple (.incDec op l) (.exprStmt t)
  | require {c c'} : Expr c c' →
      Simple (.require c) (.exprStmt (.call (.ident "require") (.positional (.cons c' .nil))))
  | assert {c c'} : Expr c c' →
      Simple (.assert c) (.exprStmt (.call (.ident "assert") (.positional (.cons c' .nil))))
  | revert : Simple .revert (.exprStmt (.call (.ident "revert") (.positional .nil)))

theorem Simple.decode {s t} (h : Simple s t) : Decode.simple s = some t := by
  cases h with
  | assign l r => simp [Decode.simple, l.decode, r.decode]
  | declNone x T => simp [Decode.simple, T]
  | declSome x T e => simp [Decode.simple, T, e.decode]
  | opAssign o l r => simp [Decode.simple, o, l.decode, r.decode]
  | incDec e => simp [Decode.simple, e.decode]
  | require c => simp [Decode.simple, c.decode]
  | assert c => simp [Decode.simple, c.decode]
  | revert => simp [Decode.simple]

theorem simple_spells (s : RawStmt) (t : Syn .simple) (h : Decode.simple s = some t) :
    Simple s t := by
  cases s with
  | assign l r =>
      spell_simp Decode.simple at h; obtain ⟨l', hl, r', hr, rfl⟩ := h
      exact .assign (expr_spells _ _ hl) (expr_spells _ _ hr)
  | decl T x init =>
      cases init with
      | none => spell_simp Decode.simple at h; obtain ⟨T', hT, rfl⟩ := h; exact .declNone x hT
      | some e =>
        spell_simp Decode.simple at h; obtain ⟨T', hT, e', he, rfl⟩ := h
        exact .declSome x hT (expr_spells _ _ he)
  | opAssign op l r =>
      spell_simp Decode.simple at h; obtain ⟨o, ho, l', hl, r', hr, rfl⟩ := h
      exact .opAssign ho (expr_spells _ _ hl) (expr_spells _ _ hr)
  | incDec op l =>
      spell_simp Decode.simple at h; obtain ⟨a, ha, rfl⟩ := h; exact .incDec (expr_spells _ _ ha)
  | require c =>
      spell_simp Decode.simple at h; obtain ⟨a, ha, rfl⟩ := h; exact .require (expr_spells _ _ ha)
  | assert c =>
      spell_simp Decode.simple at h; obtain ⟨a, ha, rfl⟩ := h; exact .assert (expr_spells _ _ ha)
  | revert => spell_simp Decode.simple at h; subst h; exact .revert
  | _ => simp [Decode.simple] at h

/-- A `for` initializer: none, or one simple statement. -/
inductive Init : List RawStmt → Syn (.opt .simple) → Prop where
  | absent : Init [] .none
  | one {s t} : Simple s t → Init [s] (.some t)

/-- A `for` update: none, or one assignment or update expression. -/
inductive Upd : List RawStmt → Syn (.opt .expr) → Prop where
  | absent : Upd [] .none
  | assign {l l' r r'} : Expr l l' → Expr r r' → Upd [.assign l r] (.some (.assign .assign l' r'))
  | opAssign {op o l l' r r'} : Decode.assignOp op = some o → Expr l l' → Expr r r' →
      Upd [.opAssign op l r] (.some (.assign o l' r'))
  | incDec {op l t} : Expr (.incDec op l) t → Upd [.incDec op l] (.some t)

/-- A `for` condition, absent or present. -/
inductive Cond : Option RawExpr → Syn (.opt .expr) → Prop where
  | absent : Cond none .none
  | present {c c'} : Expr c c' → Cond (some c) (.some c')

mutual
/-- Statements in a control context. -/
inductive Stmt : (k : SCtx) → RawStmt → Syn (.stmt k) → Prop where
  | ite {k c c' thn thn'} : Expr c c' → Items k thn thn' →
      Stmt k (.ite c thn []) (.ifStmt c' (unbrace thn') .none)
  | iteElse {k c c' thn thn' e els els'} : Expr c c' → Items k thn thn' →
      Items k (e :: els) els' →
      Stmt k (.ite c thn (e :: els)) (.ifStmt c' (unbrace thn') (.some (unbrace els')))
  | retNone {k} : Stmt k (.ret none) (.returnStmt .none)
  | retSome {k e e'} : Expr e e' → Stmt k (.ret (some e)) (.returnStmt (.some e'))
  | block {k b b'} : Items k b b' → Stmt k (.block b) (.blockStmt (.block b'))
  | whileLoop {l u c c' b b'} (spec : RawLoopSpec) : Expr c c' → Items ⟨true, u⟩ b b' →
      Stmt ⟨l, u⟩ (.whileLoop spec c b) (.whileStmt c' (unbrace b'))
  | loop {l u c c' b b'} (spec : RawLoopSpec) : Expr c c' → Items ⟨true, u⟩ b b' →
      Stmt ⟨l, u⟩ (.loop spec c b) (.whileStmt c' (unbrace b'))
  | doWhile {l u c c' b b'} (spec : RawLoopSpec) : Items ⟨true, u⟩ b b' → Expr c c' →
      Stmt ⟨l, u⟩ (.doWhile spec b c) (.doWhile (unbrace b') c')
  | forLoop {l u init init' c c' upd upd' b b'} (spec : RawLoopSpec) : Init init init' →
      Cond c c' → Upd upd upd' → Items ⟨true, u⟩ b b' →
      Stmt ⟨l, u⟩ (.forLoop spec init c upd b) (.forStmt init' c' upd' (unbrace b'))
  | brk {u} : Stmt ⟨true, u⟩ .brk .breakStmt
  | cont {u} : Stmt ⟨true, u⟩ .cont .continueStmt
  | simple {k s t} : Simple s t → Stmt k s (.simpleStmt t)
/-- The items of a block; an `unchecked` block only in a checked context. -/
inductive Items : (k : SCtx) → List RawStmt → Syn (.list (.item k)) → Prop where
  | nil {k} : Items k [] .nil
  | unchecked {l b b' rest rest'} : Items ⟨l, true⟩ b b' → Items ⟨l, false⟩ rest rest' →
      Items ⟨l, false⟩ (.unchecked b :: rest) (.cons (.uncheckedItem (.block b')) rest')
  | stmt {k s s' rest rest'} : Stmt k s s' → Items k rest rest' →
      Items k (s :: rest) (.cons (.stmtItem s') rest')
end

theorem Init.decode {b t} (h : Init b t) : Decode.initializer b = some t := by
  cases h with
  | absent => rfl
  | one s => simp [Decode.initializer, s.decode]

theorem init_spells (b : List RawStmt) (t : Syn (.opt .simple))
    (h : Decode.initializer b = some t) : Init b t := by
  match b, h with
  | [], h => spell_simp Decode.initializer at h; subst h; exact .absent
  | [s], h =>
    spell_simp Decode.initializer at h; obtain ⟨a, ha, rfl⟩ := h; exact .one (simple_spells _ _ ha)
  | _ :: _ :: _, h => simp [Decode.initializer] at h

theorem Upd.decode {b t} (h : Upd b t) : Decode.update b = some t := by
  cases h with
  | absent => rfl
  | assign l r => simp [Decode.update, l.decode, r.decode]
  | opAssign o l r => simp [Decode.update, o, l.decode, r.decode]
  | incDec e => simp [Decode.update, e.decode]

theorem upd_spells (b : List RawStmt) (t : Syn (.opt .expr)) (h : Decode.update b = some t) :
    Upd b t := by
  unfold Decode.update at h
  split at h
  · cases h; exact .absent
  · bind_simp at h; obtain ⟨l', hl, r', hr, rfl⟩ := h
    exact .assign (expr_spells _ _ hl) (expr_spells _ _ hr)
  · bind_simp at h; obtain ⟨o, ho, l', hl, r', hr, rfl⟩ := h
    exact .opAssign ho (expr_spells _ _ hl) (expr_spells _ _ hr)
  · bind_simp at h; obtain ⟨a, ha, rfl⟩ := h; exact .incDec (expr_spells _ _ ha)
  · cases h

mutual
theorem Stmt.decode : ∀ {k s t}, Stmt k s t → Decode.stmt k s = some t
  | _, _, _, .ite c thn => by simp [Decode.stmt, c.decode, thn.decode]
  | _, _, _, .iteElse c thn els => by simp [Decode.stmt, c.decode, thn.decode, els.decode]
  | _, _, _, .retNone => by simp [Decode.stmt]
  | _, _, _, .retSome e => by simp [Decode.stmt, e.decode]
  | _, _, _, .block b => by simp [Decode.stmt, b.decode]
  | _, _, _, .whileLoop _ c b | _, _, _, .loop _ c b => by
      simp [Decode.stmt, c.decode, b.decode]
  | _, _, _, .doWhile _ b c => by simp [Decode.stmt, c.decode, b.decode]
  | _, _, _, .forLoop _ i c u b => by
      cases c with
      | absent => simp [Decode.stmt, i.decode, u.decode, b.decode]
      | present c => simp [Decode.stmt, i.decode, u.decode, b.decode, c.decode]
  | _, _, _, .brk | _, _, _, .cont => by simp [Decode.stmt, Decode.jump]
  | _, _, _, .simple h => by
      have e := h.decode
      cases h <;> simp [Decode.stmt, e]
theorem Items.decode : ∀ {k b t}, Items k b t → Decode.items k b = some t
  | _, _, _, .nil => by simp [Decode.items]
  | _, _, _, .unchecked b rest => by
      simp [Decode.items, b.decode, rest.decode, Decode.uncheckedItem]
  | _, _, _, .stmt s rest => by
      have e := s.decode
      have e' := rest.decode
      cases s <;> first | simp [Decode.items, e, e'] | (rename_i h; cases h <;> simp [Decode.items, e, e'])
end

mutual
theorem stmt_spells : (k : SCtx) → (s : RawStmt) → (t : Syn (.stmt k)) →
    Decode.stmt k s = some t → Stmt k s t
  | k, .ite c thn [], t, h => by
      spell_simp Decode.stmt at h; obtain ⟨c', hc, thn', ht, rfl⟩ := h
      exact .ite (expr_spells _ _ hc) (items_spells _ _ _ ht)
  | k, .ite c thn (e :: els), t, h => by
      spell_simp Decode.stmt at h; obtain ⟨c', hc, thn', ht, els', he, rfl⟩ := h
      exact .iteElse (expr_spells _ _ hc) (items_spells _ _ _ ht) (items_spells _ _ _ he)
  | k, .ret none, t, h => by spell_simp Decode.stmt at h; subst h; exact .retNone
  | k, .ret (some e), t, h => by
      spell_simp Decode.stmt at h; obtain ⟨e', he, rfl⟩ := h; exact .retSome (expr_spells _ _ he)
  | k, .block b, t, h => by
      spell_simp Decode.stmt at h; obtain ⟨b', hb, rfl⟩ := h; exact .block (items_spells _ _ _ hb)
  | ⟨l, u⟩, .whileLoop spec c b, t, h => by
      spell_simp Decode.stmt at h; obtain ⟨c', hc, b', hb, rfl⟩ := h
      exact .whileLoop spec (expr_spells _ _ hc) (items_spells _ _ _ hb)
  | ⟨l, u⟩, .loop spec c b, t, h => by
      spell_simp Decode.stmt at h; obtain ⟨c', hc, b', hb, rfl⟩ := h
      exact .loop spec (expr_spells _ _ hc) (items_spells _ _ _ hb)
  | ⟨l, u⟩, .doWhile spec b c, t, h => by
      spell_simp Decode.stmt at h; obtain ⟨b', hb, c', hc, rfl⟩ := h
      exact .doWhile spec (items_spells _ _ _ hb) (expr_spells _ _ hc)
  | ⟨l, u⟩, .forLoop spec init none upd b, t, h => by
      spell_simp Decode.stmt at h; obtain ⟨i', hi, _, rfl, u', hu, b', hb, rfl⟩ := h
      exact .forLoop spec (init_spells _ _ hi) .absent (upd_spells _ _ hu) (items_spells _ _ _ hb)
  | ⟨l, u⟩, .forLoop spec init (some c) upd b, t, h => by
      spell_simp Decode.stmt at h; obtain ⟨i', hi, _, ⟨c', hc, rfl⟩, u', hu, b', hb, rfl⟩ := h
      exact .forLoop spec (init_spells _ _ hi) (.present (expr_spells _ _ hc)) (upd_spells _ _ hu)
        (items_spells _ _ _ hb)
  | ⟨true, u⟩, .brk, t, h => by simp [Decode.stmt, Decode.jump] at h; subst h; exact .brk
  | ⟨false, u⟩, .brk, t, h => by simp [Decode.stmt, Decode.jump] at h
  | ⟨true, u⟩, .cont, t, h => by simp [Decode.stmt, Decode.jump] at h; subst h; exact .cont
  | ⟨false, u⟩, .cont, t, h => by simp [Decode.stmt, Decode.jump] at h
  | k, s@(.assign ..), t, h | k, s@(.decl ..), t, h | k, s@(.declStorage ..), t, h
  | k, s@(.declMemory ..), t, h | k, s@(.delete ..), t, h | k, s@(.opAssign ..), t, h
  | k, s@(.incDec ..), t, h | k, s@(.pushOpAssign ..), t, h | k, s@(.pushIncDec ..), t, h
  | k, s@(.call ..), t, h | k, s@(.assignIncDec ..), t, h | k, s@(.assignPush ..), t, h
  | k, s@(.declStoragePush ..), t, h | k, s@(.declPush ..), t, h | k, s@(.require ..), t, h
  | k, s@(.assert ..), t, h | k, s@.revert, t, h | k, s@(.revertMsg ..), t, h
  | k, s@(.requireMsg ..), t, h | k, s@(.revertReason ..), t, h | k, s@(.requireReason ..), t, h
  | k, s@(.revertRaw ..), t, h | k, s@(.revertErr ..), t, h | k, s@(.requireErr ..), t, h
  | k, s@.assumeFalse, t, h | k, s@(.eval ..), t, h | k, s@(.unchecked ..), t, h
  | k, s@(.checked ..), t, h | k, s@(.tryCall ..), t, h | k, s@(.send ..), t, h
  | k, s@(.tupleDecl ..), t, h | k, s@(.tupleAssign ..), t, h | k, s@.hole, t, h => by
      spell_simp Decode.stmt at h; obtain ⟨a, ha, rfl⟩ := h; exact .simple (simple_spells _ _ ha)
theorem items_spells : (k : SCtx) → (b : List RawStmt) → (t : Syn (.list (.item k))) →
    Decode.items k b = some t → Items k b t
  | k, [], t, h => by spell_simp Decode.items at h; subst h; exact .nil
  | ⟨l, false⟩, .unchecked b :: rest, t, h => by
      simp only [Decode.items, Decode.uncheckedItem] at h
      bind_simp at h
      obtain ⟨b', hb, _, rfl, r', hr, rfl⟩ := h
      exact .unchecked (items_spells _ _ _ hb) (items_spells _ _ _ hr)
  | ⟨l, true⟩, .unchecked b :: rest, t, h => by
      simp only [Decode.items, Decode.uncheckedItem] at h
      bind_simp at h
      obtain ⟨_, _, h⟩ := h
      exact h.elim
  | k, s@(.assign ..) :: rest, t, h | k, s@(.decl ..) :: rest, t, h
  | k, s@(.declStorage ..) :: rest, t, h | k, s@(.declMemory ..) :: rest, t, h
  | k, s@(.delete ..) :: rest, t, h | k, s@(.opAssign ..) :: rest, t, h
  | k, s@(.incDec ..) :: rest, t, h | k, s@(.pushOpAssign ..) :: rest, t, h
  | k, s@(.pushIncDec ..) :: rest, t, h | k, s@(.call ..) :: rest, t, h
  | k, s@(.assignIncDec ..) :: rest, t, h | k, s@(.assignPush ..) :: rest, t, h
  | k, s@(.declStoragePush ..) :: rest, t, h | k, s@(.declPush ..) :: rest, t, h
  | k, s@(.ite ..) :: rest, t, h | k, s@(.require ..) :: rest, t, h
  | k, s@(.assert ..) :: rest, t, h | k, s@.revert :: rest, t, h
  | k, s@(.revertMsg ..) :: rest, t, h | k, s@(.requireMsg ..) :: rest, t, h
  | k, s@(.revertReason ..) :: rest, t, h | k, s@(.requireReason ..) :: rest, t, h
  | k, s@(.revertRaw ..) :: rest, t, h | k, s@(.revertErr ..) :: rest, t, h
  | k, s@(.requireErr ..) :: rest, t, h | k, s@.assumeFalse :: rest, t, h
  | k, s@(.ret ..) :: rest, t, h | k, s@(.eval ..) :: rest, t, h
  | k, s@(.checked ..) :: rest, t, h | k, s@(.tryCall ..) :: rest, t, h
  | k, s@(.send ..) :: rest, t, h | k, s@(.tupleDecl ..) :: rest, t, h
  | k, s@(.tupleAssign ..) :: rest, t, h | k, s@(.block ..) :: rest, t, h
  | k, s@(.whileLoop ..) :: rest, t, h | k, s@(.forLoop ..) :: rest, t, h
  | k, s@(.doWhile ..) :: rest, t, h | k, s@.brk :: rest, t, h | k, s@.cont :: rest, t, h
  | k, s@(.loop ..) :: rest, t, h | k, s@.hole :: rest, t, h => by
      spell_simp Decode.items at h; obtain ⟨s', hs, r', hr, rfl⟩ := h
      exact .stmt (stmt_spells _ _ _ hs) (items_spells _ _ _ hr)
end
end Spells

/-- **The spelling relation.** A plain request spells a Source program when
its raw input spells a block that has a Source typing derivation from the
caller's locals in the canonical unit, and the program is that derivation's
resolution. No inference function is mentioned. -/
def Spells (r : Request) (s : SourceProgram) : Prop :=
  Decode.plain r = true ∧
  ∃ (C : Source.Ctx) (L : List (String × Source.STy)) (b : Source.Syn (.list (.item .body)))
    (L' : List (String × Source.STy)) (d : Source.ItemsD C L b L'),
    Decode.context r = some C ∧ Decode.locals r.input.before.locals.1 = some L ∧
    Spells.Items .body r.input.raw b ∧
    s = ⟨C.env, C.rets, C.inModifier, .body, Source.tysOf L, Source.tysOf L', d.toR⟩

/-- Source inference finds a derivation whenever one exists, on the decoder's
image only: a request's canonical context and a block its raw input spells.
Not proved in the Source front end, whose inference is documented as possibly
incomplete in general; the decoder is complete for `Spells` under it. -/
def InferComplete : Prop :=
  ∀ (r : Request) (C : Source.Ctx) (L : List (String × Source.STy))
    (b : Source.Syn (.list (.item .body))) (L' : List (String × Source.STy)),
    Decode.context r = some C → Spells.Items .body r.input.raw b → Source.ItemsD C L b L' →
    (Source.ItemsD.infer C L b).isSome = true

/-- The decoder is sound for the relation: what it returns is spelled. -/
theorem decode_spells {r : Request} {s : SourceProgram} (h : Decode.decode r = some s) :
    Spells r s := by
  unfold Decode.decode at h
  split at h
  · rename_i p
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨C, hC, L, hL, b, hb, ⟨L', d⟩, _, rfl⟩ := h
    exact ⟨p, C, L, b, L', d, hC, hL, Spells.items_spells _ _ _ hb, rfl⟩
  · cases h

/-- A request spells at most one program. -/
theorem Spells.unique {r : Request} {s s' : SourceProgram} (h : Spells r s) (h' : Spells r s') :
    s = s' := by
  obtain ⟨_, C, L, b, L', d, hC, hL, hb, rfl⟩ := h
  obtain ⟨_, C', L₀, b', L'', d', hC', hL', hb', rfl⟩ := h'
  cases hC.symm.trans hC'
  cases hL.symm.trans hL'
  cases hb.decode.symm.trans hb'.decode
  obtain ⟨rfl, same⟩ := Source.ItemsD.unique d d'
  rw [eq_of_heq same]

/-- The decoder is complete for the relation if Source inference is. -/
theorem Spells.decode (complete : InferComplete) {r : Request} {s : SourceProgram}
    (h : Spells r s) : Decode.decode r = some s := by
  have h₀ := h
  obtain ⟨p, C, L, b, L', d, hC, hL, hb, _⟩ := h₀
  obtain ⟨⟨L'', d'⟩, found⟩ := Option.isSome_iff_exists.mp (complete r C L b L' hC hb d)
  have decoded : Decode.decode r =
      some ⟨C.env, C.rets, C.inModifier, .body, Source.tysOf L, Source.tysOf L'', d'.toR⟩ := by
    simp [Decode.decode, p, hC, hL, hb.decode, found]
  exact decoded.trans (congrArg some (Spells.unique (decode_spells decoded) h))

/-! ## The observation policies (H1021)

No events; the outcome at the first horizon that completes. Only the kind of an
outcome is observed (success or failure): no data, no events, no journal, no
state. Panic data cannot be compared (the intrinsic halt keeps no code); other
revert data is compared only in `Simulation.Final`. Event and journal
faithfulness is stated by no proposition in this file: it is dropped by these
policies, not yet exposed as an obligation.

Known defects of this choice, open: every environment is allowed, including
Source executions with a failure plan, while the simulation speaks of the
default plan only; a stuck Source run observes like a diverging model run; an
escaping `break` or `continue` observes as success; and `PassCorrect` at these
policies needs a surjection from model states onto Source executions that is
tied to no state relation, so it may be false for reasons unrelated to
lowering, or say very little. -/
namespace Observe

open Solidity.Roadmap

/-- A Source result's outcome. A timeout has not completed; a stuck run (a
run-time type mismatch) never counts as completed. -/
def sourceOutcome {α : Type} : Source.R α → Option Outcome
  | .ok _ => some (.success [])
  | .error (.revert _) => some (.revert [])
  | .error (.stuck _) | .error .timeout => none

/-- A target result's outcome. Divergence and exhaustion do not complete. -/
def targetOutcome {α : Type} : TRes α → Option Outcome
  | .ok _ => some (.success [])
  | .error .revert | .error .panic | .error (.revertWith _) => some (.revert [])
  | .error .diverge | .error .exhausted => none

/-- The outcome at the first completing horizon up to `n`. -/
def first (f : Nat → Option Outcome) : Nat → Option Outcome
  | 0 => f 0
  | n + 1 => match first f n with
    | some o => some o
    | none => f (n + 1)

theorem first_succ_of_some {f : Nat → Option Outcome} {n : Nat} {o : Outcome}
    (e : first f n = some o) : first f (n + 1) = some o := by
  simp only [first, e]

theorem first_mono {f : Nat → Option Outcome} {n n' : Nat} {o : Outcome} (h : n ≤ n')
    (e : first f n = some o) : first f n' = some o := by
  induction h with
  | refl => exact e
  | step _ ih => exact first_succ_of_some ih

/-- A prefix with no events. -/
def silent (o : Option Outcome) : Prefix Event Outcome := ⟨[], o⟩

/-- First-completion observation is consistent with no fact about the
evaluator: once an outcome is seen it is kept. -/
theorem first_consistent (f : Nat → Option Outcome) :
    Prefixes.Consistent (fun n => silent (first f n)) := by
  intro n n' h
  refine ⟨List.prefix_refl _, ?_⟩
  cases e : first f n with
  | none => exact .inl (by simp only [silent, e])
  | some o => exact .inr (by simp only [silent, e, first_mono h e])

/-- The Source policy: the first completing horizon of the actual run. -/
def source (s : SourceProgram) :
    ObservationPolicy (fun e n => @SourceExecution.result s e n) where
  allowed _ := True
  admissible _ := True
  forward _ _ := True
  guard _ _ := True
  observe _ n run := silent (first (fun m => sourceOutcome (run m).1) n)
  consistent _ := first_consistent _

/-- The target policy: the model run has no horizon, so every bound observes
its one result. -/
def target {C : Contract} {Γ : Ctx} (p : Blk C Γ) :
    ObservationPolicy (fun (e : State C Γ) (_ : Nat) => p.2.run e) where
  allowed _ := True
  admissible _ := True
  forward _ _ := True
  guard _ _ := True
  observe _ n run := silent (targetOutcome (run n))
  consistent _ := fun _ _ _ => Prefix.Le.refl _

end Observe

/-! ## The allocation trace (H1023)

One scope per request: the names listed by `protectedNames`, and as generated
the fresh-shaped spellings of the run whose index lies in the run's
fresh-counter interval. Callee-local rebinding and memo reuse get no scope of
their own. The trace is not complete, and both lists under-approximate:

* protected: binders the raw input declares but never reads, quantified
  invariant binders, a callee's parameters and modifiers unless in its
  locals, recursion and memo entries are missing;
* generated: only names read in the lowered output or live after elaboration
  are seen, so a temporary declared and never read, one that occurs only in
  the intrinsic program, and a memo-reused callee name below the interval
  are missing; with a `FreshNames` whose `parse` never succeeds the list is
  empty and the obligation trivial. No round-trip law on `FreshNames` is
  assumed or stated. -/
namespace Allocation

/-- Names in scope of the request: caller and callee locals, return slots,
state variables, enums, functions, a callee's renaming, names the scope marks
as user-supplied, and the names the raw input reads. -/
def protectedNames (r : Request) : List String :=
  r.input.before.locals.1.map Prod.fst ++
    (r.callee.map fun c => c.locals.map Prod.fst ++ c.names.map Prod.fst ++
      c.names.map Prod.snd ++ c.scope.map Prod.fst).getD [] ++
    r.input.returnSlots.getD [] ++
    r.contract.vars.map Prod.fst ++ r.contract.enums.map Prod.fst ++
    r.contract.funs.map Prod.fst ++
    r.input.scope.funs.map Prod.fst ++ r.input.scope.mutableFreshNames ++
    r.input.raw.flatMap RawStmt.names

/-- The fresh identifiers among `spellings` with index in `[lo, hi)`. -/
def generated (names : FreshNames) (lo hi : Nat) (spellings : List String) :
    List (String × Nat) :=
  spellings.filterMap fun s =>
    (names.parse s).filter fun id => decide (lo ≤ id.2) && decide (id.2 < hi)

/-- The one scope of a run, from the counter before lowering to the counter
after elaboration. -/
def scope (r : Request) (o : ProductionOutput) (after : Checker.Snapshot) : AllocationScope :=
  ⟨protectedNames r, generated r.input.names r.input.before.locals.2 after.locals.2
    (o.raw.flatMap RawStmt.names ++ after.locals.1.map Prod.fst)⟩

/-- The trace of a run is its one scope. -/
def trace (r : Request) (o : ProductionOutput) (after : Checker.Snapshot)
    (_ : SProg r.contract) (_ : Blk r.contract r.context.ctx)
    (scopes : List AllocationScope) : Prop :=
  scopes = [scope r o after]

end Allocation

/-! ## The general simulation (H1022)

One relation for every decoded program and its elaborated block, in place of
the e1 endpoints by cases. The e1 endpoints imply it (`of_endpoint`,
`of_retEndpoint`); they are stronger and are not recovered from it. It is
relative to a state relation `rel` (values and globals; `loopRel` below is the
stage-1 one). It speaks of
runs with no failure plan and known calldata only.

Known defects, open. `Simulates` can hold vacuously: its context maps are
chosen existentially and are tied to no names, so a map between unrelatable
types makes the premise unsatisfiable; and nothing asks `rel` to be non-empty
or total (a `glob` that is never true satisfies it). Unlike the diagram of
`Goals/Shrink.lean` it has no total initial matching, no integer reflection
and no freshness clause. The return witness of the e1 return endpoint is not
kept: a Source `return` and a normal completion match the same model results. -/
namespace Simulation

/-- A Source/model state relation: values at each heap typing, and the
globals (the model state without its locals). -/
structure StateRelation (E : Source.Env) (C : Contract) where
  val : (H : HTy) → (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C H → Prop
  glob : Source.Glob E → Source.Fr → Source.St E → State C [] → Prop

/-- Final matching of a Source result and a model result. Normal completion
relates the final locals through `m'`; a `return` relates the entry locals
through the block's context extension; both relate the globals. A revert keeps
its data, a panic only its kind (the intrinsic halt has no code). A Source
timeout matches model divergence. Nothing else matches: an escaping `break` or
`continue`, a stuck Source run, model exhaustion. -/
def Final {s : SourceProgram} {C : Contract} {Γ Δ : Ctx} {H : HTy}
    (rel : StateRelation s.env C) (m : Lowering.V07.ContextMap s.before Γ)
    (m' : Lowering.V07.ContextMap s.after Δ) (emb : Thin Γ Δ) (G : Source.Glob s.env)
    (F : Source.Fr) (src : SourceResult s) (tgt : TRes (Out C H Δ)) : Prop :=
  match src.1, tgt with
  | .ok (.normal ls), .ok o =>
    m'.Related (rel.val o.st.H) ls o.st.env ∧ rel.glob G F src.2.2 o.st.glob
  | .ok (.ret ls), .ok o =>
    (m.wk emb).Related (rel.val o.st.H) ls o.st.env ∧ rel.glob G F src.2.2 o.st.glob
  | .error (.revert d), .error h => h = THalt.ofData d ∨ (h = .panic ∧ ∃ c, d = Source.panicData c)
  | .error .timeout, .error .diverge => True
  | _, _ => False

/-- **The simulation.** From related states, at every horizon from some point
on, the Source result matches the model's one result. A Source run that times
out at every horizon is matched only by a diverging model run, so this is both
directions on related pairs only; it is not the backward half of `PassCorrect`.
Since model exhaustion, a stuck Source run and an escaping jump match nothing,
proving it means proving they do not occur from related states. -/
def Simulates (rel : (E : Source.Env) → (C : Contract) → StateRelation E C)
    (s : SourceProgram) {C : Contract} {Γ : Ctx} (p : Blk C Γ) : Prop :=
  ∃ (m : Lowering.V07.ContextMap s.before Γ) (m' : Lowering.V07.ContextMap s.after p.1)
    (emb : Thin Γ p.1),
    ∀ (e : SourceExecution s) (tgt : State C Γ), e.plan = none → e.calldataKnown = true →
      m.Related ((rel s.env C).val tgt.H) e.initial.1 tgt.env →
      (rel s.env C).glob e.glob e.frame e.initial.2 tgt.glob →
      ∃ N, ∀ n,
        Final (rel s.env C) m m' emb e.glob e.frame (e.result (n + N)) (p.2.run tgt)

/-- A block of one statement runs as the statement, one horizon later. -/
theorem execItems_single {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (ph : Option (Source.Ph E)) {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    {Γ Γ' : Source.RCtx} (s : Source.RStmt E R M k Γ Γ') (l : Source.Locals E.layout Γ)
    (σ σ' : Source.Locals E.layout [] × Source.St E) (o : Source.Out E.layout Γ Γ')
    (h : (Source.execS G F n nps ph s l).run σ = (.ok o, σ')) :
    (Source.execItems G F (n + 1) nps ph (.stmt s .nil) l).run σ = (.ok o, σ') := by
  cases n with
  | zero => simp [Source.execS, Source.EM.halt] at h; cases h
  | succ n =>
    rw [Source.execItems]
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.run, StateT.bind, ExceptT.bindCont] at h ⊢
    rw [h]
    cases o <;> rfl

variable {rel : (E : Source.Env) → (C : Contract) → StateRelation E C}

/-- The e1 normal endpoint implies the simulation, for every state
relation that reflects Booleans and relates `false` to `false`. -/
theorem of_endpoint
    (reflect : ∀ E C H (v : Source.Val E.layout .bool) (b : Bool),
      (rel E C).val H .bool (.val .bool) v b → v = .bool b)
    (falseRel : ∀ E C H, (rel E C).val H .bool (.val .bool) (.bool false) false)
    {E : Source.Env} {srcΓ : Source.RCtx} {returns : List Source.STy} {M : Bool}
    {k : Source.SCtx} {C : Contract} {Γ Δ : Ctx}
    {statement : Source.RStmt E returns M k srcΓ srcΓ} {offset : Nat}
    {m : Lowering.V07.ContextMap srcΓ Γ} {program : Prog C Γ Δ} {emb : Thin Γ Δ}
    (h : Loops.Endpoint statement offset m program emb) :
    Simulates rel (SourceProgram.ofStmt statement) (⟨Δ, program⟩ : Blk C Γ) := by
  refine ⟨m, m.wk emb, emb, fun e tgt plan known related glob => ⟨offset + 1, fun n => ?_⟩⟩
  obtain ⟨G, F, nps, ph, initial, plan', known'⟩ := e
  cases plan
  cases known
  obtain ⟨ls, out, run, target, post, same⟩ :=
    h G F n nps ph initial tgt (rel E C).val related (reflect E C) (falseRel E C)
  have step := execItems_single G F (n + offset) nps ph statement initial.1 _ _ _ run
  simp only [Final, SourceExecution.result, SourceProgram.ofStmt]
  rw [show n + (offset + 1) = n + offset + 1 from rfl, step, target]
  exact ⟨post, same ▸ glob⟩

/-- The e1 return endpoint implies the simulation as well. The returned flag
selects which matching case applies; its link to the model witness is dropped. -/
theorem of_retEndpoint
    (reflect : ∀ E C H (v : Source.Val E.layout .bool) (b : Bool),
      (rel E C).val H .bool (.val .bool) v b → v = .bool b)
    (falseRel : ∀ E C H, (rel E C).val H .bool (.val .bool) (.bool false) false)
    {E : Source.Env} {srcΓ : Source.RCtx} {M : Bool} {k : Source.SCtx} {C : Contract}
    {Γ Δ : Ctx} {statement : Source.RStmt E [] M k srcΓ srcΓ} {offset : Nat}
    {m : Lowering.V07.ContextMap srcΓ Γ} {program : Prog C Γ Δ} {emb : Thin Γ Δ}
    {witness : Idx Δ (.val .bool)}
    (h : Loops.RetEndpoint statement offset m program emb witness) :
    Simulates rel (SourceProgram.ofStmt statement) (⟨Δ, program⟩ : Blk C Γ) := by
  refine ⟨m, m.wk emb, emb, fun e tgt plan known related glob => ⟨offset + 1, fun n => ?_⟩⟩
  obtain ⟨G, F, nps, ph, initial, plan', known'⟩ := e
  cases plan
  cases known
  obtain ⟨ls, returned, out, run, target, _, post, same⟩ :=
    h G F n nps ph initial tgt (rel E C).val related (reflect E C) (falseRel E C)
  have step := execItems_single G F (n + offset) nps ph statement initial.1 _ _ _ run
  simp only [Final, SourceExecution.result, SourceProgram.ofStmt]
  rw [show n + (offset + 1) = n + offset + 1 from rfl, step, target]
  cases returned <;> exact ⟨post, same ▸ glob⟩

/-- Negative control: a state relation whose globals are never related makes
every pair with some context maps simulate. So `Simulates` alone does not rule
out a degenerate `rel`; non-emptiness is a separate obligation, not yet stated. -/
theorem vacuous (empty : ∀ E C G F st σ, ¬ (rel E C).glob G F st σ) {s : SourceProgram}
    {C : Contract} {Γ : Ctx} (p : Blk C Γ) (m : Lowering.V07.ContextMap s.before Γ)
    (m' : Lowering.V07.ContextMap s.after p.1) (emb : Thin Γ p.1) : Simulates rel s p :=
  ⟨m, m', emb, fun _ _ _ _ _ glob => absurd glob (empty _ _ _ _ _ _)⟩

end Simulation

/-! ## The concrete state relation (stage 1)

The state relation of the fragment the stage-1 decoder covers. Values: a
primitive model value and the Source value of the corresponding type, by
`Source.Agreement.PrimitiveRel`; no other pair of types is related. Globals:
each primitive state variable holds related values in the model storage and
in the storage of the running Source account, at the canonical unit's path;
`msg.value` and the block timestamp agree; the Source frame is not static and
checks arithmetic. A contract with a state variable of any other type has no
related globals, as the decoder has no unit for it.

Not related, so unconstrained: memory heaps; the ledger, balances and
`selfBalance`; the caller and own address; external-call results (`tx.ext`);
transient storage; other accounts; the Source journal, events, logs, function
locals and resource metadata; the frame's contract, depth and calldata; and
all of the Source globals but the timestamp. No related pair is exhibited and
no total initial matching is proved: that the cell type at each path equals
the declared type, and that every Source state of a decoded program has a
related model state, are obligations not yet stated. -/
namespace Relation

open Source.Agreement (sourceTy PrimitiveRel)

/-- Values: primitives at corresponding types. -/
def val (E : Source.Env) (C : Contract) (H : HTy) (τ : Source.STy) :
    (u : LTy) → Source.Val E.layout τ → u.TDenote C H → Prop
  | .val p, v, x => ∃ h : τ = sourceTy p, PrimitiveRel E.layout p (h ▸ v) x
  | _, _, _ => False

/-- One state variable: a primitive holds related values at its path. -/
def field {D : Source.Layout} (read : Source.SPath → Option ((τ : Source.STy) × Source.Val D τ))
    (x : Name) : {T : Ty} → SVal T → Prop
  | _, .prim (p := p) w =>
    ∃ v, read ⟨⟨some Decode.contractName, x⟩, []⟩ = some ⟨sourceTy p, v⟩ ∧ PrimitiveRel D p v w
  | _, _ => False

/-- Every state variable, in declaration order. -/
def fields {D : Source.Layout} (read : Source.SPath → Option ((τ : Source.STy) × Source.Val D τ)) :
    {fs : List (Name × Ty)} → SFields fs → Prop
  | _, .nil => True
  | _, .cons (f := x) v rest => field read x v ∧ fields read rest

/-- Globals: storage of the running account, `msg.value`, the timestamp, and a
Source frame that may write and checks arithmetic, as the model always does. -/
def glob (E : Source.Env) (C : Contract) (G : Source.Glob E) (F : Source.Fr) (st : Source.St E)
    (σ : State C []) : Prop :=
  fields (fun p => ((st.ex.world.accounts F.this).storage.read p).map fun v => ⟨_, v⟩) σ.storage ∧
  σ.tx.msgValue.1 = (F.value.val : Int) ∧ σ.tx.timestamp.1 = (G.timestamp.val : Int) ∧
  F.static = false ∧ F.checked = true

end Relation

/-- The value relation is total on primitives: every model primitive has a
related Source value. (Nothing of the kind is proved for globals.) -/
theorem Relation.val_total (E : Source.Env) (C : Contract) (H : HTy) (p : PrimTy)
    (x : p.Denote) :
    ∃ v, Relation.val E C H (Source.Agreement.sourceTy p) (.val p) v x :=
  ⟨Source.Agreement.ofModel E.layout p x, rfl, Source.Agreement.ofModel_related E.layout p x⟩

/-- The stage-1 state relation. -/
def loopRel (E : Source.Env) (C : Contract) : Simulation.StateRelation E C :=
  ⟨Relation.val E C, Relation.glob E C⟩

/-- It reflects Booleans. -/
theorem loopRel_reflect (E : Source.Env) (C : Contract) (H : HTy)
    (v : Source.Val E.layout .bool) (b : Bool)
    (h : (loopRel E C).val H .bool (.val .bool) v b) : v = .bool b := by
  obtain ⟨_, r⟩ := h
  cases r
  rfl

/-- It relates `false` to `false`. -/
theorem loopRel_false (E : Source.Env) (C : Contract) (H : HTy) :
    (loopRel E C).val H .bool (.val .bool) (.bool false) false :=
  ⟨rfl, .bool false⟩

/-! ## The concrete boundary, as far as the decoder fixes it

Admission and association are fixed here: every request whose whole pipeline
succeeds is admitted (`loopEntry`), and a request is associated with the
programs it spells (`Spells`), so the `decoder` field is a real obligation:
soundness is `decode_spells`, completeness is left. `loopBoundary` takes the
policies, `relates` and the allocation trace as arguments, and
`loopResidual_iff` lists what is left for any choice of them. -/

/-- Admission: every request whose whole pipeline succeeds. -/
def loopEntry (r : Request) : Prop := r.Succeeds

/-- Association: the request spells the program (`Spells`, not the decoder). -/
def loopAssociated (r : Request) (s : SourceProgram) : Prop := Spells r s

/-- The reference interpretation at given observation policies. -/
def loopReference
    (source : (s : SourceProgram) → ObservationPolicy (fun e n => @SourceExecution.result s e n))
    (target : {C : Contract} → {Γ : Ctx} → (p : Blk C Γ) →
      ObservationPolicy (fun (e : State C Γ) (_ : Nat) => p.2.run e)) :
    RawSourceInterpretation :=
  ⟨loopAssociated, loopEntry, source, target⟩

/-- The boundary at given policies, state relation and allocation trace. -/
def loopBoundary
    (source : (s : SourceProgram) → ObservationPolicy (fun e n => @SourceExecution.result s e n))
    (target : {C : Contract} → {Γ : Ctx} → (p : Blk C Γ) →
      ObservationPolicy (fun (e : State C Γ) (_ : Nat) => p.2.run e))
    (relates : SourceProgram → {C : Contract} → {Γ : Ctx} → Blk C Γ → Prop)
    (allocations : (r : Request) → ProductionOutput → Checker.Snapshot → SProg r.contract →
      Blk r.contract r.context.ctx → List AllocationScope → Prop) : SemanticBoundary :=
  ⟨loopReference source target, relates, allocations⟩

/-- The boundary admits every request whose whole pipeline succeeds. -/
theorem loopBoundary_fullDomain {source target relates allocations} :
    FullDomain (loopBoundary source target relates allocations) := fun _ h => h

/-- **What is left at the concrete admission and association.** Decoder
soundness is a theorem, so the `decoder` field is its completeness on admitted
requests. Left: the decoder is defined on every successful request (not
provable for stage 1, which has gaps) and complete for `Spells` there; each
successful pipeline has a safe allocation trace, is related to its decoded
program and refines it; and `relates` holds of the e1 families. -/
theorem loopResidual_iff {source target relates allocations} :
    Residual (loopBoundary source target relates allocations) Decode.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → Spells r s → Decode.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        ∃ scopes, allocations r o after parts program scopes ∧
          ∀ scope ∈ scopes, SafeSpellings r.input.names scope.protectedNames scope.generated) ∧
      (∀ (r : Request) o after parts program s, Decode.decode r = some s →
        r.pipeline o after parts program →
        relates s program ∧
          Nonempty (PassCorrect (source s).behaviour (target program).behaviour)) ∧
      RelatesNormalFamily (loopBoundary source target relates allocations) ∧
      RelatesReturnFamily (loopBoundary source target relates allocations) := by
  constructor
  · intro h
    exact ⟨h.total, fun r s e spelled => (h.decoder r s e).mpr spelled,
      fun r o after parts program run =>
        h.allocation r o after parts program ⟨o, after, parts, program, run⟩ run,
      fun r o after parts program s d run =>
        h.pipeline r o after parts program s ⟨o, after, parts, program, run⟩ d run,
      h.normal, h.returns⟩
  · intro ⟨covered, complete, allocation, pipeline, normal, returns⟩
    exact ⟨covered, fun r s e => ⟨decode_spells, complete r s e⟩,
      fun r o after parts program _ run => allocation r o after parts program run,
      fun r o after parts program s _ d run => pipeline r o after parts program s d run,
      normal, returns⟩

/-! ## The boundary at a state relation

The policies (H1021), the simulation (H1022) and the allocation trace (H1023)
as chosen above, each with its listed defects; the state relation `rel` is
still an argument, so this is not yet a concrete boundary. -/

/-- The boundary with the state relation unbound. -/
def loopBoundaryAt (rel : (E : Source.Env) → (C : Contract) → Simulation.StateRelation E C) :
    SemanticBoundary :=
  loopBoundary Observe.source (fun p => Observe.target p)
    (fun s _ _ p => Simulation.Simulates rel s p) Allocation.trace

variable {rel : (E : Source.Env) → (C : Contract) → Simulation.StateRelation E C}

/-- The e1 normal family is related: derived from its endpoint theorem. -/
theorem loopBoundaryAt_normal
    (reflect : ∀ E C H (v : Source.Val E.layout .bool) (b : Bool),
      (rel E C).val H .bool (.val .bool) v b → v = .bool b)
    (falseRel : ∀ E C H, (rel E C).val H .bool (.val .bool) (.bool false) false) :
    RelatesNormalFamily (loopBoundaryAt rel) := by
  intro k E srcΓ returns M l u C Γ m pair extra names
  obtain ⟨embedding, endpoint⟩ := normalFamily_correct k (returns := returns) (M := M)
    (l := l) (u := u) m pair extra names (k.lowered pair extra names) rfl
  exact Simulation.of_endpoint reflect falseRel endpoint

/-- The e1 return family is related: derived from its endpoint theorem. -/
theorem loopBoundaryAt_returns
    (reflect : ∀ E C H (v : Source.Val E.layout .bool) (b : Bool),
      (rel E C).val H .bool (.val .bool) v b → v = .bool b)
    (falseRel : ∀ E C H, (rel E C).val H .bool (.val .bool) (.bool false) false) :
    RelatesReturnFamily (loopBoundaryAt rel) := by
  intro k E srcΓ M l u C Γ m pair extra names
  exact Simulation.of_retEndpoint reflect falseRel
    (returnFamily_correct k (M := M) (l := l) (u := u) m pair extra names)

/-- **What is left at the boundary**, for a state relation that reflects
Booleans and relates `false` to `false`: the decoder is defined on every
successful request and complete for `Spells` there; the run's one allocation
scope is safe; and each successful pipeline simulates its decoded program and
refines it under the policies. The two family obligations follow from the two
hypotheses on `rel` (`loopRel` has both). -/
theorem loopResidualAt_iff
    (reflect : ∀ E C H (v : Source.Val E.layout .bool) (b : Bool),
      (rel E C).val H .bool (.val .bool) v b → v = .bool b)
    (falseRel : ∀ E C H, (rel E C).val H .bool (.val .bool) (.bool false) false) :
    Residual (loopBoundaryAt rel) Decode.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → Spells r s → Decode.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, Decode.decode r = some s →
        r.pipeline o after parts program →
        Simulation.Simulates rel s program ∧
          Nonempty (PassCorrect (Observe.source s).behaviour
            (Observe.target program).behaviour)) := by
  refine loopResidual_iff.trans ⟨fun ⟨covered, complete, allocation, pipeline, _, _⟩ =>
    ⟨covered, complete, fun r o after parts program run => ?_, pipeline⟩,
    fun ⟨covered, complete, allocation, pipeline⟩ =>
      ⟨covered, complete, fun r o after parts program run =>
        ⟨_, rfl, fun scope member => ?_⟩, pipeline,
        loopBoundaryAt_normal reflect falseRel, loopBoundaryAt_returns reflect falseRel⟩⟩
  · obtain ⟨scopes, trace, safe⟩ := allocation r o after parts program run
    cases trace
    exact safe _ (List.mem_singleton.mpr rfl)
  · cases List.mem_singleton.mp member
    exact allocation r o after parts program run

/-! ## The boundary at the stage-1 state relation

Every part is now a closed term. It is still not fit to carry the goal: the
defects listed at the policies, the simulation and the allocation trace
stand, the state relation leaves most of the state unrelated, and the decoder
has gaps. -/

/-- The stage-1 boundary. -/
def loopBoundaryStage1 : SemanticBoundary := loopBoundaryAt loopRel

/-- At the stage-1 boundary both family obligations are theorems, and four
obligations are left. -/
theorem loopResidualStage1_iff :
    Residual loopBoundaryStage1 Decode.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → Spells r s → Decode.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, Decode.decode r = some s →
        r.pipeline o after parts program →
        Simulation.Simulates loopRel s program ∧
          Nonempty (PassCorrect (Observe.source s).behaviour
            (Observe.target program).behaviour)) :=
  loopResidualAt_iff loopRel_reflect loopRel_false

end Solidity.Correctness.Lowering.Total
