import Solidity.Correctness.Lowering.Total.Production
import Solidity.Correctness.Lowering.Loops.Correct
import Solidity.Source.Infer
import Solidity.Source.Agreement.PrimitiveTypes

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
  spelling, then the existing Source inference and resolution. It covers
  primitive full-width locals and state variables, expressions, simple
  statements, branches, blocks, `unchecked` and the loops; every other input
  decodes to `none`, which is a coverage gap and never an exclusion.
* `loopEntry` admits every request whose pipeline succeeds, and
  `loopAssociated` is the decoder's graph. `loopBoundary_fullDomain` and
  `loopResidual_iff` state what is left once these two are fixed.
* The observation policies, `relates` and the allocation trace are arguments
  of `loopBoundary`: no concrete one is chosen here.

Not proved, and partly not provable yet: the fields `allocation` and `pipeline`
take as hypothesis a successful run of `elabStmtsP` and, for a callee, of
`calleeBody`, which runs `renameStmts`, `lowerReturns` and `wrapMods`. All four
are `partial`, so opaque to the kernel: the hypothesis says nothing about the
elaborated program, and no request's `Request.Succeeds` can be derived or
refuted. The decoder's coverage obligation is false as soon as one successful
request uses a construct in a listed gap. `Solidity.Goals.lowerLoopsCorrect`
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

/-- No input exclusion: every request whose pipeline succeeds is admitted. -/
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

`decode` reads a request's raw input as Source: the canonical Source spelling
of the raw statements (`Spelling`), typed by the existing Source inference
(`Source.ItemsD.infer`) and resolved by `ItemsD.toR`, in the Source unit whose
one contract declares the model contract's primitive state variables. Nothing
is checked against the lowered output: the decoder sees only the request.

Every `none` is a coverage gap, not an exclusion: with admission fixed to every
successful request (`loopEntry`), a gap on a successful request refutes the
`total` obligation. The gaps are listed at each definition. -/
namespace Decode

open Source (Syn SCtx STy)

/-- The contract name of the canonical unit (the model contract has none). -/
def contractName : String := "C"

/-- A decimal literal with no fraction and no exponent. -/
def num (n : Nat) : Syn .expr := .lit (.num (.dec n 0 0))

def uintElem : Source.Elem := .int false 256 (by decide)
def intElem : Source.Elem := .int true 256 (by decide)

/-- Binary operators. The wrapping forms (`addW` …) have no Source operator:
Source wraps by an enclosing `unchecked` block. Model `>>` is Source `sar`. -/
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

/-- Environment reads. `address(this)` and its balance are gaps. -/
def env : EnvKey → Option (Syn .expr)
  | .msgSender => some (.member (.ident "msg") "sender")
  | .msgValue => some (.member (.ident "msg") "value")
  | .timestamp => some (.member (.ident "block") "timestamp")
  | .selfBalance | .selfAddress => none

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
call. `require`, `assert` and `revert()` are calls of the Source builtins. -/
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
  | .hole => some (.exprStmt (.ident "_"))
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
spelled as the `while` it is. Gaps: every statement not listed here or in
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

/-- Source type of a model local: a full-width primitive. Narrow locals,
references and formula locals are gaps. -/
def localTy : LocalTy → Option STy
  | .val p 256 _ => some (Source.Agreement.sourceTy p)
  | _ => none

/-- The Source locals of a model context, innermost first, by name. -/
def locals : ECtx → Option (List (String × STy))
  | [] => some []
  | (x, t) :: Γ => do pure ((x, ← localTy t) :: (← locals Γ))

/-- State variable types: primitive only (references are gaps). -/
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
state variables. Functions, enums and the constructor are not declared, so a
request that calls a function, or whose contract has any of them, is a gap. -/
def unit (C : Contract) : Option (Syn .unit) :=
  if C.transientRoots.isEmpty && C.funs.isEmpty && C.enums.isEmpty && C.ctor.isNone then
    (stateVars C.vars).map fun parts =>
      .unit (.cons (.contract false contractName .none .nil parts) .nil)
  else none

/-- Return types of the enclosing function: a callee's declared primitive
returns; none at top level. -/
def returns : Option CalleeRequest → Option (List STy)
  | none => some []
  | some c => c.declaration.rets.mapM fun (_, T) =>
      match T with
      | .prim p => some (Source.Agreement.sourceTy p)
      | _ => none

/-- The Source typing context of a request, with no locals yet. -/
def context (r : Request) : Option Source.Ctx := do
  let u ← unit r.contract
  let rets ← returns r.callee
  pure { env := u.env, scope := some contractName, locals := [], rets := rets }

/-- **The decoder.** The request's raw input in its canonical Source
spelling, typed and resolved by the Source front end in the request's own
context: the callee's locals for a callee body, the caller's otherwise. -/
def decode (r : Request) : Option SourceProgram := do
  let C ← context r
  let L ← locals (r.callee.map (·.locals) |>.getD r.input.before.locals.1)
  let b ← items .body r.input.raw
  let ⟨L', d⟩ ← Source.ItemsD.infer C L b
  pure ⟨C.env, C.rets, C.inModifier, .body, Source.tysOf L, Source.tysOf L', d.toR⟩

end Decode

/-! ## The concrete boundary, as far as the decoder fixes it

Admission and association are fixed here: every request whose pipeline
succeeds is admitted (`loopEntry`: no input is excluded), and a request is
associated with exactly its decoded program. The observation policies, the
state relation `relates` and the allocation trace are not chosen here: each is
a separate semantic choice that needs its own decision, so `loopBoundary` takes
them as arguments and `loopResidual_iff` lists what is then left to prove. -/

/-- Admission: every request whose whole pipeline succeeds. -/
def loopEntry (r : Request) : Prop := r.Succeeds

/-- Association: the request decodes to the program. -/
def loopAssociated (r : Request) (s : SourceProgram) : Prop := Decode.decode r = some s

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

/-- The boundary excludes no successful request, whatever its other parts. -/
theorem loopBoundary_fullDomain {source target relates allocations} :
    FullDomain (loopBoundary source target relates allocations) := fun _ h => h

/-- **What is left at the concrete admission and decoder.** The `decoder`
field holds by definition. Left: the decoder covers every successful request
(`covered`); each successful pipeline has a safe allocation trace, is related
to its decoded program and refines it; and `relates` holds of the e1 families. -/
theorem loopResidual_iff {source target relates allocations} :
    Residual (loopBoundary source target relates allocations) Decode.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.decode r = some s) ∧
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
    exact ⟨h.total, fun r o after parts program run =>
        h.allocation r o after parts program ⟨o, after, parts, program, run⟩ run,
      fun r o after parts program s d run =>
        h.pipeline r o after parts program s ⟨o, after, parts, program, run⟩ d run,
      h.normal, h.returns⟩
  · intro ⟨covered, allocation, pipeline, normal, returns⟩
    exact ⟨covered, fun _ _ _ => Iff.rfl,
      fun r o after parts program _ run => allocation r o after parts program run,
      fun r o after parts program s _ d run => pipeline r o after parts program s d run,
      normal, returns⟩

end Solidity.Correctness.Lowering.Total
