import Solidity.Frontend.SolcJson.TryPanicSourcePlan

/-! Whole original c() structural derivation, not source-to-TRun realization.
Return94 is associated to its real caller return/binder declarations. No new
operational early-return token, execution certificate or admission hook is added. -/
namespace Solidity.Frontend.TryPanicSourceCaller
open Lean (Json)
open Evm.TryByteImage Evm.TryPanicProducer Evm.TryPanicSourcePlan Evm.TryPanicSourceFrame
open TryPanicSourcePlan
variable {C : Contract}

abbrev CallerCtx : Ctx := [.val .uint]

def cMetadata : SourceFunction :=
  { declaration := some 105, name := "c", signature := some "c()"
    mutability := .nonpayable
    callable := .abi .publicFn .selected (some ⟨0xc3da42b8,by decide⟩) }

def clauseStatement (clause : Json) (i : Nat) : Json :=
  (memberAt (nodeField clause "block") "statements" i).getD .null

/-- The complete actual assert expression, including its builtin declaration. -/
structure AssertNode (statement : Json) (value : Bool) : Prop where
  statementKind : J.kind statement = "ExpressionStatement"
  expressionKind : J.kind (expression statement) = "FunctionCall"
  functionKind : J.kind (nodeField (expression statement) "expression") = "Identifier"
  functionName : J.str? (nodeField (expression statement) "expression") "name" = some "assert"
  builtin : J.ref? (nodeField (expression statement) "expression") = some (-3)
  arguments : J.arr? (expression statement) "arguments" = some #[TryPanicSourcePlan.operand statement 0]
  literalKind : J.kind (TryPanicSourcePlan.operand statement 0) = "Literal"
  boolKind : J.str? (TryPanicSourcePlan.operand statement 0) "kind" = some "bool"
  literal : J.str? (TryPanicSourcePlan.operand statement 0) "value" = some (if value then "true" else "false")

/-- Whole c declaration under the SAME source unit/owner as resolved f. All
source clauses and exact block lists are consumed, including actual Return94. -/
structure ResolvedC {p : Pipeline} {input unit owner decl : Json}
    (f : ResolvedF p input unit owner decl) (caller : Json) : Prop where
  fullCaller : caller = TryPanicSourceData.callerNode
  callerMember : memberAt owner "nodes" 3 = some caller
  scope : intField caller "scope" = some 140
  metadata : sourceFunction (J.arrD owner "nodes").toList caller .selected false = .ok cMetadata
  parameters : J.arr? (nodeField caller "parameters") "parameters" = some #[]
  returnList : J.arr? (nodeField caller "returnParameters") "parameters" =
    some #[TryPanicSourceData.returnSlotNode]
  returnParameters : J.id? (nodeField caller "returnParameters") = some 75
  modifiers : J.arr? caller "modifiers" = some #[]
  bodyKind : J.kind (nodeField caller "body") = "Block"
  body : J.arr? (nodeField caller "body") "statements" = some #[TryPanicSourceData.tryNode]
  tryKind : J.kind TryPanicSourceData.tryNode = "TryStatement"
  tryId : J.id? TryPanicSourceData.tryNode = some 103
  externalCall : J.opt TryPanicSourceData.tryNode "externalCall" = some TryPanicSourceData.callNode
  clauses : J.arr? TryPanicSourceData.tryNode "clauses" =
    some #[TryPanicSourceData.successNode,TryPanicSourceData.panicNode,TryPanicSourceData.catchallNode]
  callKind : J.kind TryPanicSourceData.callNode = "FunctionCall"
  callId : J.id? TryPanicSourceData.callNode = some 79
  isTry : boolField TryPanicSourceData.callNode "tryCall" = some true
  callMember : J.opt TryPanicSourceData.callNode "expression" = some TryPanicSourceData.memberNode
  callArguments : J.arr? TryPanicSourceData.callNode "arguments" = some #[TryPanicSourceData.argumentNode]
  argumentId : J.id? TryPanicSourceData.argumentNode = some 78
  memberKind : J.kind TryPanicSourceData.memberNode = "MemberAccess"
  memberId : J.id? TryPanicSourceData.memberNode = some 77
  memberName : J.str? TryPanicSourceData.memberNode "memberName" = some "f"
  memberDeclaration : J.ref? TryPanicSourceData.memberNode = J.id? decl
  memberReceiver : J.opt TryPanicSourceData.memberNode "expression" = some TryPanicSourceData.receiverNode
  receiverId : J.id? TryPanicSourceData.receiverNode = some 76
  receiverKind : J.kind TryPanicSourceData.receiverNode = "Identifier"
  receiverName : J.str? TryPanicSourceData.receiverNode "name" = some "this"
  receiverBuiltin : J.ref? TryPanicSourceData.receiverNode = some (-28)
  receiverOwner : J.tyId TryPanicSourceData.receiverNode = "t_contract$_C_$140"
  successName : J.str? TryPanicSourceData.successNode "errorName" = some ""
  successParameters : J.opt TryPanicSourceData.successNode "parameters" = none
  successBlock : J.arr? (nodeField TryPanicSourceData.successNode "block") "statements" =
    some #[clauseStatement TryPanicSourceData.successNode 0]
  successAssert : AssertNode (clauseStatement TryPanicSourceData.successNode 0) false
  panicName : J.str? TryPanicSourceData.panicNode "errorName" = some "Panic"
  panicId : J.id? TryPanicSourceData.panicNode = some 96
  panicParameters : J.arr? (nodeField TryPanicSourceData.panicNode "parameters") "parameters" =
    some #[TryPanicSourceData.binderNode]
  panicBlock : J.arr? (nodeField TryPanicSourceData.panicNode "block") "statements" =
    some #[clauseStatement TryPanicSourceData.panicNode 0,TryPanicSourceData.returnNode]
  panicAssert : AssertNode (clauseStatement TryPanicSourceData.panicNode 0) true
  catchName : J.str? TryPanicSourceData.catchallNode "errorName" = some ""
  catchParameters : J.opt TryPanicSourceData.catchallNode "parameters" = none
  catchBlock : J.arr? (nodeField TryPanicSourceData.catchallNode "block") "statements" =
    some #[clauseStatement TryPanicSourceData.catchallNode 0]
  catchAssert : AssertNode (clauseStatement TryPanicSourceData.catchallNode 0) false
  returnSlot : J.id? TryPanicSourceData.returnSlotNode = some 74
  returnSlotScope : intField TryPanicSourceData.returnSlotNode "scope" = some 105
  returnSlotType : J.tyId TryPanicSourceData.returnSlotNode = "t_uint256"
  binder : J.id? TryPanicSourceData.binderNode = some 87
  binderScope : intField TryPanicSourceData.binderNode "scope" = some 96
  binderType : J.tyId TryPanicSourceData.binderNode = "t_uint256"
  returnKind : J.kind TryPanicSourceData.returnNode = "Return"
  returnId : J.id? TryPanicSourceData.returnNode = some 94
  returnTarget : intField TryPanicSourceData.returnNode "functionReturnParameters" = some 75
  returnExpression : J.opt TryPanicSourceData.returnNode "expression" = some TryPanicSourceData.returnExpression
  returnRead : J.ref? TryPanicSourceData.returnExpression = J.id? TryPanicSourceData.binderNode
  returnType : J.tyId TryPanicSourceData.returnExpression = "t_uint256"

/-- Checked full-callsite/return association in BOTH original bundles. -/
theorem resolve_original_c (p : Pipeline) :
    ResolvedC (resolve_original p) TryPanicSourceData.callerNode := by
  constructor <;> first | rfl | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Intrinsic source associations, not runtime success, a lowered body, or an
untyped source environment. Return slot74 and binder87 have different positions. -/
structure CallerOperands (C : Contract) where
  args : Args C CallerCtx Input
  call : ExtCall C CallerCtx
  slot74 : Idx CallerCtx (.val .uint)
  binder87 : Idx (.val .uint :: CallerCtx) (.val .uint)
  target74 : Idx (.val .uint :: CallerCtx) (.val .uint)

def argument? (node : Json) : Option U256 := do
  guard (J.kind node = "Literal")
  guard (J.str? node "kind" = some "number")
  let spelling ← J.str? node "value"
  let value ← unsignedText? spelling
  if h : value < 2^256 then some ⟨(value : Int),PrimTy.inRange_uint_of_lt h⟩ else none

/-- The constructor consumes whole-source resolution and computes operands from
the actual argument. No source outcome/callee realization field is accepted. -/
inductive DerivesWholeC36 {p : Pipeline} {input unit owner decl caller : Json}
    {f : ResolvedF p input unit owner decl} (c : ResolvedC f caller) : CallerOperands C → Prop where
  | call (n : U256) (literal : argument? TryPanicSourceData.argumentNode = some n) :
      DerivesWholeC36 c
        { args := .snoc .nil .uint (.user "size") (.simple (.lit n.val n.property))
          call := ⟨.env .selfAddress rfl,"f",[⟨.uint,.lit n.val n.property⟩]⟩
          slot74 := .here, binder87 := .here, target74 := .there .here }

def originalCallerOps : CallerOperands C :=
  { args := Evm.TryPanicCarrier.args36, call := Evm.TryPanicCarrier.selfCall
    slot74 := .here, binder87 := .here, target74 := .there .here }

private theorem argument36 : argument? TryPanicSourceData.argumentNode = some size36 := rfl

theorem derive_original_c (p : Pipeline) :
    DerivesWholeC36 (C := C) (resolve_original_c p) originalCallerOps := .call size36 argument36

/-- Local36 is DERIVED from the real literal, never imposed on generic f. -/
theorem deriveWholeC_operands_sound {p : Pipeline} {input unit owner decl caller : Json}
    {f : ResolvedF p input unit owner decl} {c : ResolvedC f caller}
    {ops : CallerOperands C} (d : DerivesWholeC36 c ops) : ops = originalCallerOps := by
  cases d with
  | call n literal =>
    have value : size36 = n := Option.some.inj (argument36.symm.trans literal)
    cases value
    rfl

/-- This is the actual intrinsic literal evaluation equation, with arbitrary
caller state and its retained heap; it is not a claim that the source ran. -/
theorem source_args36 {p : Pipeline} {input unit owner decl caller : Json}
    {f : ResolvedF p input unit owner decl} {c : ResolvedC f caller}
    {ops : CallerOperands C} (d : DerivesWholeC36 c ops) (σ : State C CallerCtx) :
    Args.evalT σ ops.args = .ok (size36,()) := by
  rw [deriveWholeC_operands_sound d]
  exact Evm.TryPanicCarrier.args36_eval σ

/-- Source c literal evaluation and empty callee-return entry are connected to
the generic f derivation at the SAME conditional finite frame. This does not
prove installed code, actual entry/prologue/resources, source-to-TRun, or Return
control-flow realization. No source/execution success is a premise. -/
theorem source_c36_completed {p : Pipeline} {input unit owner decl caller : Json}
    {f : ResolvedF p input unit owner decl} {c : ResolvedC f caller}
    {fops : ThreeOp C Input} {cops : CallerOperands C}
    (df : DerivesWholeF f fops) (dc : DerivesWholeC36 c cops)
    (σ : State C CallerCtx) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) (μ : FrameMem C Input)
    (init : FiniteEntry (σ.withEnv (Δ := Input) (size36,())) key K aligned large μ) :
    Args.evalT σ cops.args = .ok (size36,()) ∧
    CallRet.enterT (CallRet.rets (Γ := CallerCtx) .nil)
        (σ.withEnv (Δ := Input) (size36,())) =
      ⟨σ.withEnv (Δ := Input) (size36,()),List.prefix_refl _⟩ ∧
    ∃ final : FrameMem C Input, BodyCompletedAt fops μ final computed36 ∧
      final.st = σ.withEnv (Δ := Input) (size36,()) ∧
      final.key = key ∧ final.capacity = K := by
  refine ⟨source_args36 dc σ,Evm.TryPanicCarrier.empty_entry σ,?_⟩
  exact wholeF_completed36_reduce df _ key K aligned large μ init rfl

/-- Compare the RESULT of any same-entry completed model derivation with the
closed carrier halt. This never substitutes carrier36 for generic source f or
asserts a normal Out equality across caller/callee contexts. -/
theorem source_c36_result_carrier {p : Pipeline} {input unit owner decl caller : Json}
    {f : ResolvedF p input unit owner decl} {c : ResolvedC f caller}
    {fops : ThreeOp C Input} {cops : CallerOperands C}
    (df : DerivesWholeF f fops) (dc : DerivesWholeC36 c cops)
    (σ : State C CallerCtx) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) {μ final : FrameMem C Input}
    {bytes : List UInt8}
    (init : FiniteEntry (σ.withEnv (Δ := Input) (size36,())) key K aligned large μ)
    (completed : BodyCompletedAt fops μ final bytes) :
    Args.evalT σ cops.args = .ok (size36,()) ∧
    ∃ bound : bytes.length < 2^256,
      final = imageK (σ.withEnv (Δ := Input) (size36,())) key K aligned large ∧
      bytes = computed36 ∧
      bytesHalt bytes bound μ.st = .error (THalt.ofData computed36) ∧
      Prog.run (σ.withEnv (Δ := Input) (size36,())) Evm.TryPanicCarrier.carrier36 =
        .error (THalt.ofData computed36) := by
  rw [deriveWholeF_operands_sound df] at completed
  have exactResult : final = imageK (σ.withEnv (Δ := Input) (size36,())) key K aligned large ∧
      bytes = computed36 :=
    Evm.TryPanicSourceDeterminism.initialized36_exact _ key K aligned large init rfl completed
  refine ⟨source_args36 dc σ,Evm.TryPanicSourceDeterminism.completed_bytes_bound completed,
    exactResult.1,exactResult.2,?_,Evm.TryPanicCarrier.carrier36_halt _⟩
  exact Evm.TryPanicSourceDeterminism.initialized36_materialized _ key K aligned large init rfl completed

end Solidity.Frontend.TryPanicSourceCaller
