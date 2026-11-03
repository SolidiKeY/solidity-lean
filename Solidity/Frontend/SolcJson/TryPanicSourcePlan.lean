import Solidity.Frontend.SolcJson.Getters
import Solidity.Frontend.SolcJson.TryPanicSourceData
import Solidity.Evm.TryPanicSourceDeterminism

/-! H8 structural source derivation only. Raw JSON is immutable provenance,
never a runtime environment. This module is not imported by admission/lowering.
No source-to-Prog, compiler, deployment or target-resource adequacy is claimed. -/
namespace Solidity.Frontend.TryPanicSourcePlan
open Lean (Json)
open Evm.TryByteImage Evm.TryPanicProducer Evm.TryPanicSourcePlan
open Evm.TryPanicSourceFrame Evm.TryPanicSourceDeterminism
variable {C : Contract}

def nodeField (j : Json) (key : String) : Json := (J.opt j key).getD .null
def intField (j : Json) (key : String) : Option Int := (j.getObjValAs? Int key).toOption
def boolField (j : Json) (key : String) : Option Bool := (j.getObjValAs? Bool key).toOption
def memberAt (j : Json) (key : String) (i : Nat) : Option Json :=
  (J.arr? j key).bind fun ns => ns[i]?

def fMetadata : SourceFunction :=
  { declaration := some 7, name := "f", signature := some "f(uint256)"
    mutability := .pureFn
    callable := .abi .publicFn .selected (some ⟨0xb3de648b,by decide⟩) }

/-- Full immutable input/unit/declaration identity plus actual parent lookup and
existing compiler-lane metadata. Equality is over complete raw values, not hashes.
The body list, return list and modifiers admit no skipped statement or suffix. -/
structure ResolvedF (p : Pipeline) (input unit owner declaration : Json) : Prop where
  fullInput : input = TryPanicSourceData.standardInput p
  fullUnit : unit = TryPanicSourceData.wholeUnit p
  fullOwner : owner = TryPanicSourceData.ownerNode
  fullDeclaration : declaration = TryPanicSourceData.calleeNode
  source : J.str? (nodeField (nodeField input "sources") "original.sol") "content" =
    some (TryPanicSourceData.bundleKey p).source
  unitKind : J.kind unit = "SourceUnit"
  unitPath : J.str? unit "absolutePath" = some "original.sol"
  unitId : J.id? unit = some 141
  ownerMember : memberAt unit "nodes" 0 = some owner
  ownerKind : J.kind owner = "ContractDefinition"
  ownerId : J.id? owner = some 140
  ownerScope : intField owner "scope" = some 141
  declarationMember : memberAt owner "nodes" 0 = some declaration
  declarationScope : intField declaration "scope" = some 140
  metadata : sourceFunction (J.arrD owner "nodes").toList declaration .selected false = .ok fMetadata
  parameters : J.arr? (nodeField declaration "parameters") "parameters" = some #[TryPanicSourceData.parameterNode]
  returns : J.arr? (nodeField declaration "returnParameters") "parameters" = some #[]
  modifiers : J.arr? declaration "modifiers" = some #[]
  implemented : boolField declaration "implemented" = some true
  bodyKind : J.kind (nodeField declaration "body") = "Block"
  body : J.arr? (nodeField declaration "body") "statements" = some #[TryPanicSourceData.assemblyNode]
  assemblyKind : J.kind TryPanicSourceData.assemblyNode = "InlineAssembly"
  yulKind : J.kind (nodeField TryPanicSourceData.assemblyNode "AST") = "YulBlock"
  yulStatements : J.arr? (nodeField TryPanicSourceData.assemblyNode "AST") "statements" =
    some #[TryPanicSourceData.store0Node,TryPanicSourceData.store4Node,TryPanicSourceData.terminalNode]

/-- Construct actual full-source membership and metadata evidence for EACH
pinned pipeline. Equal AST values do not identify distinct bundle keys. -/
theorem resolve_original (p : Pipeline) :
    ResolvedF p (TryPanicSourceData.standardInput p) (TryPanicSourceData.wholeUnit p) TryPanicSourceData.ownerNode TryPanicSourceData.calleeNode := by
  cases p <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Narrow proof-side adapter for these immutable literals: the standard decimal
Nat formula over a structural character list, or the EXISTING width-checked hex reader. No general source
elaborator is changed. Odd-width/other spellings are not admitted by this helper. -/
def unsignedText? (text : String) : Option Nat :=
  match text.toList with
  | '0' :: 'x' :: digits | '0' :: 'X' :: digits => do
    guard (digits.length > 0 ∧ digits.length % 2 = 0)
    let node := Json.mkObj [("digits", .str (String.mk digits))]
    let value ← (declarationSelector node "digits" (digits.length / 2)).toOption
    pure value.val
  | _ => do
    let digits := text.toList
    guard (!digits.isEmpty && digits.all Char.isDigit)
    pure (digits.foldl (fun n c => n*10 + (c.toNat - '0'.toNat)) 0)

/-- Literal value and uint bound are computed, never supplied as a claimed
source result. The general parseRational kernel probe exceeded the unchanged
heartbeat limit; this adapter reuses the already checked narrow reader above. -/
def literal? (node : Json) : Option U256 := do
  guard (J.kind node = "YulLiteral")
  guard (J.str? node "kind" = some "number")
  let spelling ← J.str? node "value"
  let value ← unsignedText? spelling
  if h : value < 2^256 then some ⟨(value : Int),PrimTy.inRange_uint_of_lt h⟩ else none

def expression (node : Json) : Json := nodeField node "expression"
def operand (node : Json) (i : Nat) : Json :=
  ((J.arr? (expression node) "arguments").bind fun ns => ns[i]?).getD .null

/-- Exactly two actual operands; missing or extra arguments cannot be ignored. -/
structure YulCall (node : Json) (calleeName : String) : Prop where
  statement : J.kind node = "YulExpressionStatement"
  call : J.kind (expression node) = "YulFunctionCall"
  function : J.kind (nodeField (expression node) "functionName") = "YulIdentifier"
  name : J.str? (nodeField (expression node) "functionName") "name" = some calleeName
  arguments : J.arr? (expression node) "arguments" = some #[operand node 0,operand node 1]

/-- The sole local rule ties the typed position to parameter2/scope7 and its
complete source declaration, then to the one assembly external reference. -/
inductive ResolvedLocal {p : Pipeline} {input unit owner decl : Json}
    (r : ResolvedF p input unit owner decl) (identifier : Json) :
    Idx Input (.val .uint) → Prop where
  | parameter
      (parameterId : J.id? TryPanicSourceData.parameterNode = some 2)
      (scope : intField TryPanicSourceData.parameterNode "scope" = some 7)
      (uint : J.tyId TryPanicSourceData.parameterNode = "t_uint256")
      (references : J.arr? TryPanicSourceData.assemblyNode "externalReferences" = some #[TryPanicSourceData.referenceNode])
      (declaration : intField TryPanicSourceData.referenceNode "declaration" = some 2)
      (width : intField TryPanicSourceData.referenceNode "valueSize" = some 1)
      (slot : boolField TryPanicSourceData.referenceNode "isSlot" = some false)
      (offset : boolField TryPanicSourceData.referenceNode "isOffset" = some false)
      (source : J.str? TryPanicSourceData.referenceNode "src" = J.str? identifier "src")
      (name : J.str? identifier "name" = J.str? TryPanicSourceData.parameterNode "name")
      (kind : J.kind identifier = "YulIdentifier") : ResolvedLocal r identifier sizeSlot

inductive DerivesStore (node : Json) : WordStore C Input → Prop where
  | mstore (a v : U256) (shape : YulCall node "mstore")
      (address : literal? (operand node 0) = some a)
      (value : literal? (operand node 1) = some v) :
      DerivesStore node ⟨a,.simple (.lit v.val v.property)⟩

inductive DerivesTerminal {p : Pipeline} {input unit owner decl : Json}
    (r : ResolvedF p input unit owner decl) (node : Json) : Terminal C Input → Prop where
  | revert (a : U256) (i : Idx Input (.val .uint)) (shape : YulCall node "revert")
      (address : literal? (operand node 0) = some a)
      (localRead : ResolvedLocal r (operand node 1) i) :
      DerivesTerminal r node ⟨a,.simple (.local i)⟩

/-- The checked whole body supplies the exact ordered three statements. The
result is assembled from their typed derivations, never an assumed plan/outcome. -/
inductive DerivesWholeF {p : Pipeline} {input unit owner decl : Json}
    (r : ResolvedF p input unit owner decl) : ThreeOp C Input → Prop where
  | body (first second : WordStore C Input) (terminal : Terminal C Input)
      (s0 : DerivesStore TryPanicSourceData.store0Node first)
      (s4 : DerivesStore TryPanicSourceData.store4Node second)
      (stop : DerivesTerminal r TryPanicSourceData.terminalNode terminal) :
      DerivesWholeF r ⟨first,second,terminal⟩

private theorem store0_shape : YulCall TryPanicSourceData.store0Node "mstore" :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩
private theorem store4_shape : YulCall TryPanicSourceData.store4Node "mstore" :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩
private theorem terminal_shape : YulCall TryPanicSourceData.terminalNode "revert" :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩
private theorem address0 : literal? (operand TryPanicSourceData.store0Node 0) = some zero := rfl
private theorem selector_literal :
    literal? (operand TryPanicSourceData.store0Node 1) = some selectorWord := rfl
private theorem address4 : literal? (operand TryPanicSourceData.store4Node 0) = some ⟨4,rfl⟩ := rfl
private theorem code_literal :
    literal? (operand TryPanicSourceData.store4Node 1) = some codeWord := rfl
private theorem terminal_address :
    literal? (operand TryPanicSourceData.terminalNode 0) = some zero := rfl

/-- Actual assembly external-reference resolution constructs the intrinsic
parameter position; no size value, source reply or body result is assumed. -/
theorem resolve_parameter {p : Pipeline} {input unit owner decl : Json}
    (r : ResolvedF p input unit owner decl) :
    ResolvedLocal r (operand TryPanicSourceData.terminalNode 1) sizeSlot :=
  .parameter rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- These witnesses consume the COMPLETE actual declaration under each full
pinned source unit. They are constructed, not certificate hypotheses. -/
theorem derive_original (p : Pipeline) :
    DerivesWholeF (C := C) (resolve_original p) originalOps := by
  apply DerivesWholeF.body originalOps.first originalOps.second originalOps.terminal
  · exact .mstore zero selectorWord store0_shape address0 selector_literal
  · exact .mstore ⟨4,rfl⟩ codeWord store4_shape address4 code_literal
  · exact .revert zero sizeSlot terminal_shape terminal_address (resolve_parameter _)

private theorem store0_sound {store : WordStore C Input}
    (d : DerivesStore TryPanicSourceData.store0Node store) : store = originalOps.first := by
  cases d with
  | mstore a v shape ha hv =>
    have addressEq : zero = a := Option.some.inj (address0.symm.trans ha)
    have valueEq : selectorWord = v := Option.some.inj (selector_literal.symm.trans hv)
    cases addressEq
    cases valueEq
    rfl

private theorem store4_sound {store : WordStore C Input}
    (d : DerivesStore TryPanicSourceData.store4Node store) : store = originalOps.second := by
  cases d with
  | mstore a v shape ha hv =>
    have addressEq : (⟨4,rfl⟩ : U256) = a := Option.some.inj (address4.symm.trans ha)
    have valueEq : codeWord = v := Option.some.inj (code_literal.symm.trans hv)
    cases addressEq
    cases valueEq
    rfl

private theorem terminal_sound {p : Pipeline} {input unit owner decl : Json}
    {r : ResolvedF p input unit owner decl} {terminal : Terminal C Input}
    (d : DerivesTerminal r TryPanicSourceData.terminalNode terminal) :
    terminal = originalOps.terminal := by
  cases d with
  | revert a i shape ha localRead =>
    have addressEq : zero = a := Option.some.inj (terminal_address.symm.trans ha)
    cases addressEq
    cases localRead
    rfl

/-- Inversion reconstructs the exact source operations and generic parameter
read. No compiled execution, source-to-Prog realization or hcall is a premise. -/
theorem deriveWholeF_operands_sound {p : Pipeline} {input unit owner decl : Json}
    {r : ResolvedF p input unit owner decl} {ops : ThreeOp C Input}
    (d : DerivesWholeF r ops) : ops = originalOps := by
  cases d with
  | body first second terminal s0 s4 stop =>
    have h0 : first = originalOps.first := store0_sound s0
    have h4 : second = originalOps.second := store4_sound s4
    have ht : terminal = originalOps.terminal := terminal_sound stop
    cases h0
    cases h4
    cases ht
    rfl

/-- The source-linked interpretation stays generic in the ACTUAL local uint.
Bounds describe only this finite completed model branch, not source admission. -/
theorem wholeF_completed {p : Pipeline} {input unit owner decl : Json}
    {r : ResolvedF p input unit owner decl} {ops : ThreeOp C Input}
    (d : DerivesWholeF r ops) (μ : FrameMem C Input) (space : 36 ≤ μ.capacity)
    (fits : (TEnv.get sizeSlot μ.st.env).val.toNat ≤ μ.capacity) :
    BodyCompletedAt ops μ (originalImage μ space)
      (snapshot (originalImage μ space) (actualRange μ fits)) := by
  rw [deriveWholeF_operands_sound d]
  exact original_completed μ space fits

/-- Source-structural derivation plus a conditional finite-entry witness yields
the completed36 model. It does not manufacture that entry or runtime resources. -/
theorem wholeF_completed36_reduce {p : Pipeline} {input unit owner decl : Json}
    {r : ResolvedF p input unit owner decl} {ops : ThreeOp C Input}
    (d : DerivesWholeF r ops) (σ : State C Input) (key : FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K) (μ : FrameMem C Input)
    (init : FiniteEntry σ key K aligned large μ)
    (size : TEnv.get sizeSlot σ.env = size36) :
    ∃ final : FrameMem C Input, BodyCompletedAt ops μ final computed36 ∧
      final.st = σ ∧ final.key = key ∧ final.capacity = K := by
  rw [deriveWholeF_operands_sound d]
  exact finite_entry36 σ key K aligned large μ init size

/-- A changed order cannot furnish this whole-source typed derivation, even
when these specific overlapping constants happen to give equal short bytes. -/
def swappedOps : ThreeOp C Input :=
  { first := originalOps.second, second := originalOps.first, terminal := originalOps.terminal }

theorem reversed_refused {p : Pipeline} {input unit owner decl : Json}
    (r : ResolvedF p input unit owner decl) : ¬ DerivesWholeF (C := C) r swappedOps := by
  intro d
  have same : swappedOps (C := C) = originalOps := deriveWholeF_operands_sound d
  have address : (swappedOps (C := C)).first.offset.val.toNat =
      (originalOps (C := C)).first.offset.val.toNat :=
    congrArg (fun ops : ThreeOp C Input => ops.first.offset.val.toNat) same
  change (4 : Nat) = 0 at address
  cases address

end Solidity.Frontend.TryPanicSourcePlan
