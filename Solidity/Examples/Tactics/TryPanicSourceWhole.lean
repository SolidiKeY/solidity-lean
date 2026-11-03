import Solidity.Frontend.SolcJson.TryPanicSourceCaller

/-! Complete-node mutation and inhabited original-source/model clients.
Refusal means no structural certificate, never an operational source/EVM verdict.
The original quoted inputs remain immutable; only separate controls are changed. -/
namespace Solidity.Examples.Tactics.TryPanicSourceWhole
open Lean (Json toJson)
open Evm.TryByteImage Evm.TryPanicProducer Evm.TryPanicSourcePlan Evm.TryPanicSourceFrame
open Frontend Frontend.TryPanicSourcePlan Frontend.TryPanicSourceCaller
variable {C : Contract}

def extraBody : Json := TryPanicSourceData.calleeNode.setObjVal! "body"
  ((nodeField TryPanicSourceData.calleeNode "body").setObjVal! "statements"
    (.arr #[TryPanicSourceData.assemblyNode,TryPanicSourceData.assemblyNode]))
def bodyArity (node : Json) : Nat := (J.arrD (nodeField node "body") "statements").size

/-- Whole body checking rejects an extra suffix, not only a wrong node ID. -/
theorem extra_body_refused (p : Pipeline) (input unit owner : Json) :
    ¬ ResolvedF p input unit owner extraBody := by
  intro r
  have bad : bodyArity extraBody = bodyArity TryPanicSourceData.calleeNode :=
    congrArg bodyArity r.fullDeclaration
  change (2 : Nat) = 1 at bad
  cases bad

def reversedAssembly : Json := TryPanicSourceData.assemblyNode.setObjVal! "AST"
  (TryPanicSourceData.yulBlock.setObjVal! "statements"
    (.arr #[TryPanicSourceData.store4Node,TryPanicSourceData.store0Node,TryPanicSourceData.terminalNode]))
def reversedBody : Json := TryPanicSourceData.calleeNode.setObjVal! "body"
  ((nodeField TryPanicSourceData.calleeNode "body").setObjVal! "statements" (.arr #[reversedAssembly]))
def firstAddress (node : Json) : Option Nat := do
  let assembly ← memberAt (nodeField node "body") "statements" 0
  let statement ← memberAt (nodeField assembly "AST") "statements" 0
  let n ← literal? (TryPanicSourcePlan.operand statement 0)
  pure n.val.toNat

/-- Raw source order is checked even though original overlap bytes can agree. -/
theorem reversed_body_refused (p : Pipeline) (input unit owner : Json) :
    ¬ ResolvedF p input unit owner reversedBody := by
  intro r
  have bad : firstAddress reversedBody = firstAddress TryPanicSourceData.calleeNode :=
    congrArg firstAddress r.fullDeclaration
  change (some 4 : Option Nat) = some 0 at bad
  cases bad

def wrongParameter : Json := TryPanicSourceData.parameterNode.setObjVal! "scope" (toJson (8 : Int))
def wrongScopeBody : Json := TryPanicSourceData.calleeNode.setObjVal! "parameters"
  ((nodeField TryPanicSourceData.calleeNode "parameters").setObjVal! "parameters" (.arr #[wrongParameter]))
def parameterScope (node : Json) : Option Int :=
  (memberAt (nodeField node "parameters") "parameters" 0).bind fun p => intField p "scope"

/-- Same name/type at another declaration scope cannot resolve parameter2. -/
theorem wrong_scope_refused (p : Pipeline) (input unit owner : Json) :
    ¬ ResolvedF p input unit owner wrongScopeBody := by
  intro r
  have bad : parameterScope wrongScopeBody = parameterScope TryPanicSourceData.calleeNode :=
    congrArg parameterScope r.fullDeclaration
  change (some 8 : Option Int) = some 7 at bad
  have impossible : (8 : Int) = 7 := Option.some.inj bad
  omega

/-- Identical AST values do not authorize swapping distinct compiler inputs. -/
theorem wrong_pipeline_input :
    ¬ ResolvedF .legacy (TryPanicSourceData.standardInput .viaIR)
      (TryPanicSourceData.wholeUnit .legacy) TryPanicSourceData.ownerNode TryPanicSourceData.calleeNode := by
  intro r
  have bad : boolField (nodeField (TryPanicSourceData.standardInput .viaIR) "settings") "viaIR" =
      boolField (nodeField (TryPanicSourceData.standardInput .legacy) "settings") "viaIR" :=
    congrArg (fun j => boolField (nodeField j "settings") "viaIR") r.fullInput
  change (some true : Option Bool) = some false at bad
  cases bad

/-- Full unit identity includes its actual source path, not IDs alone. -/
theorem wrong_unit_refused (p : Pipeline) :
    ¬ ResolvedF p (TryPanicSourceData.standardInput p)
      ((TryPanicSourceData.wholeUnit p).setObjVal! "absolutePath" (.str "other.sol"))
      TryPanicSourceData.ownerNode TryPanicSourceData.calleeNode := by
  cases p <;> intro r <;>
    have bad : (some "other.sol" : Option String) = some "original.sol" := r.unitPath <;>
    exact (by decide : (some "other.sol" : Option String) ≠ some "original.sol") bad

/-- Typed return slot74 and handler binder87 are different positions. -/
theorem binder_not_return :
    (originalCallerOps (C := C)).binder87 ≠ (originalCallerOps (C := C)).target74 := by
  intro bad
  cases bad

/-- Static mutation helper, never a source execution/lowering operation. -/
def callerWithReturn (statement : Json) : Json :=
  let block := (nodeField TryPanicSourceData.panicNode "block").setObjVal! "statements"
    (.arr #[clauseStatement TryPanicSourceData.panicNode 0,statement])
  let panicClause := TryPanicSourceData.panicNode.setObjVal! "block" block
  let sourceTry := TryPanicSourceData.tryNode.setObjVal! "clauses"
    (.arr #[TryPanicSourceData.successNode,panicClause,TryPanicSourceData.catchallNode])
  TryPanicSourceData.callerNode.setObjVal! "body"
    ((nodeField TryPanicSourceData.callerNode "body").setObjVal! "statements" (.arr #[sourceTry]))

def actualReturn (caller : Json) : Json :=
  let sourceTry := (memberAt (nodeField caller "body") "statements" 0).getD .null
  let panicClause := (memberAt sourceTry "clauses" 1).getD .null
  (memberAt (nodeField panicClause "block") "statements" 1).getD .null

def wrongReturnParameters : Json := callerWithReturn
  (TryPanicSourceData.returnNode.setObjVal! "functionReturnParameters" (toJson (74 : Int)))

/-- Return references the parameter-list75, not variable declaration74. -/
theorem wrong_return_parameters_refused {p : Pipeline} {input unit owner decl : Json}
    (f : ResolvedF p input unit owner decl) : ¬ ResolvedC f wrongReturnParameters := by
  intro c
  have bad : intField (actualReturn wrongReturnParameters) "functionReturnParameters" =
      intField (actualReturn TryPanicSourceData.callerNode) "functionReturnParameters" :=
    congrArg (fun node => intField (actualReturn node) "functionReturnParameters") c.fullCaller
  change (some 74 : Option Int) = some 75 at bad
  have impossible : (74 : Int) = 75 := Option.some.inj bad
  omega

def wrongBinderRead : Json := callerWithReturn
  (TryPanicSourceData.returnNode.setObjVal! "expression"
    (TryPanicSourceData.returnExpression.setObjVal! "referencedDeclaration" (toJson (74 : Int))))

/-- A same-typed scalar return slot does not replace the handler binder87. -/
theorem wrong_binder_refused {p : Pipeline} {input unit owner decl : Json}
    (f : ResolvedF p input unit owner decl) : ¬ ResolvedC f wrongBinderRead := by
  intro c
  have bad : J.ref? (nodeField (actualReturn wrongBinderRead) "expression") =
      J.ref? (nodeField (actualReturn TryPanicSourceData.callerNode) "expression") :=
    congrArg (fun node => J.ref? (nodeField (actualReturn node) "expression")) c.fullCaller
  change (some 74 : Option Int) = some 87 at bad
  have impossible : (74 : Int) = 87 := Option.some.inj bad
  omega

def callerWithCall (call : Json) : Json :=
  TryPanicSourceData.callerNode.setObjVal! "body"
    ((nodeField TryPanicSourceData.callerNode "body").setObjVal! "statements"
      (.arr #[TryPanicSourceData.tryNode.setObjVal! "externalCall" call]))
def actualCall (caller : Json) : Json :=
  nodeField ((memberAt (nodeField caller "body") "statements" 0).getD .null) "externalCall"
def actualArgument (caller : Json) : Option Nat := do
  let arg ← memberAt (actualCall caller) "arguments" 0
  let n ← argument? arg
  pure n.val.toNat

def wrongArgument : Json := callerWithCall
  (TryPanicSourceData.callNode.setObjVal! "arguments"
    (.arr #[TryPanicSourceData.argumentNode.setObjVal! "value" (.str "0x25")]))

/-- Changed literal78 cannot retain the unchanged whole-c certificate. -/
theorem wrong_argument_refused {p : Pipeline} {input unit owner decl : Json}
    (f : ResolvedF p input unit owner decl) : ¬ ResolvedC f wrongArgument := by
  intro c
  have bad : actualArgument wrongArgument = actualArgument TryPanicSourceData.callerNode :=
    congrArg actualArgument c.fullCaller
  change (some 37 : Option Nat) = some 36 at bad
  cases bad

def wrongMember : Json := callerWithCall
  (TryPanicSourceData.callNode.setObjVal! "expression"
    (TryPanicSourceData.memberNode.setObjVal! "referencedDeclaration" (toJson (8 : Int))))

/-- Name f alone is insufficient when member77 refers to another declaration. -/
theorem wrong_member_refused {p : Pipeline} {input unit owner decl : Json}
    (f : ResolvedF p input unit owner decl) : ¬ ResolvedC f wrongMember := by
  intro c
  have bad : J.ref? (nodeField (actualCall wrongMember) "expression") =
      J.ref? (nodeField (actualCall TryPanicSourceData.callerNode) "expression") :=
    congrArg (fun n => J.ref? (nodeField (actualCall n) "expression")) c.fullCaller
  change (some 8 : Option Int) = some 7 at bad
  have impossible : (8 : Int) = 7 := Option.some.inj bad
  omega

def wrongReceiver : Json := callerWithCall
  (TryPanicSourceData.callNode.setObjVal! "expression"
    (TryPanicSourceData.memberNode.setObjVal! "expression"
      (TryPanicSourceData.receiverNode.setObjVal! "referencedDeclaration" (toJson (-29 : Int)))))

theorem wrong_receiver_refused {p : Pipeline} {input unit owner decl : Json}
    (f : ResolvedF p input unit owner decl) : ¬ ResolvedC f wrongReceiver := by
  intro c
  have bad : J.ref? (nodeField (nodeField (actualCall wrongReceiver) "expression") "expression") =
      J.ref? (nodeField (nodeField (actualCall TryPanicSourceData.callerNode) "expression") "expression") :=
    congrArg (fun n => J.ref? (nodeField (nodeField (actualCall n) "expression") "expression")) c.fullCaller
  change (some (-29) : Option Int) = some (-28) at bad
  have impossible : (-29 : Int) = -28 := Option.some.inj bad
  omega

def constantTerminalOps : ThreeOp C Input :=
  { originalOps with terminal := ⟨zero,.simple (.lit 36 rfl)⟩ }

/-- Observing the36 case cannot replace the source's generic terminal local. -/
theorem constant_terminal_refused {p : Pipeline} {input unit owner decl : Json}
    (r : ResolvedF p input unit owner decl) :
    ¬ DerivesWholeF (C := C) r constantTerminalOps := by
  intro d
  have same : constantTerminalOps (C := C) = originalOps := deriveWholeF_operands_sound d
  have bad : (constantTerminalOps (C := C)).terminal.length =
      (originalOps (C := C)).terminal.length :=
    congrArg (fun ops : ThreeOp C Input => ops.terminal.length) same
  cases bad

/-- Source original f and c derivations are BOTH constructed before conditional
model reduction; no whole-source certificate is supplied by this client. -/
theorem original_model_client (p : Pipeline) (σ : State C CallerCtx) (key : FrameKey) :
    Args.evalT σ (originalCallerOps (C := C)).args = .ok (size36,()) ∧
    CallRet.enterT (CallRet.rets (Γ := CallerCtx) .nil)
        (σ.withEnv (Δ := Input) (size36,())) =
      ⟨σ.withEnv (Δ := Input) (size36,()),List.prefix_refl _⟩ ∧
    ∃ final : FrameMem C Input,
      BodyCompletedAt originalOps
        (entryK (σ.withEnv (Δ := Input) (size36,())) key 256 ⟨8,rfl⟩ (by decide))
        final computed36 ∧ final.st = σ.withEnv (Δ := Input) (size36,()) ∧
        final.key = key ∧ final.capacity = 256 :=
  source_c36_completed (derive_original p) (derive_original_c p) σ key 256 ⟨8,rfl⟩ (by decide) _ rfl

/-- The SAME resolved f declaration has an inhabited generic6 model branch.
The comparison call is explicitly the separate constructed constant carrier,
not an original-source execution or a whole-function substitution theorem. -/
theorem original_six_vs_constant (p : Pipeline) (σ : State C CallerCtx) (key : FrameKey) :
    let τ := σ.withEnv (Δ := Input) ((⟨6,rfl⟩ : U256),())
    ∃ final bytes,
      BodyCompletedAt originalOps (entryK τ key 256 ⟨8,rfl⟩ (by decide)) final bytes ∧
      bytes.length = 6 ∧
      TRun.call (Evm.TryPanicCarrier.argsAt (⟨6,rfl⟩ : U256)) (.rets .nil) .refl
        Evm.TryPanicCarrier.carrier36.runR σ = .error (THalt.ofData computed36) := by
  let τ : State C Input := σ.withEnv (Δ := Input) ((⟨6,rfl⟩ : U256),())
  have fits : (TEnv.get sizeSlot τ.env).val.toNat ≤ 256 := by change 6 ≤ 256; decide
  refine ⟨imageK τ key 256 ⟨8,rfl⟩ (by decide),dataK τ key 256 ⟨8,rfl⟩ (by decide) fits,
    ?_,data_length _ _ _ _ _ _,Evm.TryPanicCarrier.call_at_halt _ σ⟩
  exact wholeF_completed (derive_original p) _ (by change 36 ≤ 256; decide) fits

end Solidity.Examples.Tactics.TryPanicSourceWhole
