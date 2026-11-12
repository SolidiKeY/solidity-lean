import Solidity.Goals.Plan

/-! Environment-bound goal-pin specification, additive to `GoalPinSpec` v1.
The reference observations below describe a finite traversal graph; they are not
an installed pin checker, command, pin table, workflow, or proof of the goal. -/
namespace Solidity.Goals
namespace GoalPinSpecV2

open Lean
open GoalPinSpec

/-- Failures are values. Resource exhaustion never means a successful comparison. -/
inductive Error where
  | definition (reason : DefinitionError)
  | notProposition | invalidUniverse | freeVariable | metavariable | illScoped | illTyped | unsupported
  | resource | recursion | interrupted
  | coverage (reason : CoverageError)
  | duplicatePin | malformedPin | malformedManifest | unknownGoal
  | missingPin | missingDecision | decisionMismatch | digestMismatch
  deriving DecidableEq

/-- The local telescope is innermost first; its types use the preceding outer
context. It is distinct from the declaration's universe-parameter context. -/
inductive Pointwise {A B : Type} (R : A → B → Prop) : List A → List B → Prop where
  | nil : Pointwise R [] []
  | cons : R a b → Pointwise R as bs → Pointwise R (a :: as) (b :: bs)

structure Local where
  type : Expr
  info : BinderInfo

structure Task where
  params : List Lean.Name
  locals : List Local
  active : List Lean.Name
  expression : Expr

/-- Erase only binder spelling and metadata, before inspecting application
spines. All identities, universe expressions, binder annotations and arguments
remain. In particular, metadata cannot hide the head of a matcher application. -/
def erase : Expr → Expr
  | .app f a => .app (erase f) (erase a)
  | .lam _ t b bi => .lam .anonymous (erase t) (erase b) bi
  | .forallE _ t b bi => .forallE .anonymous (erase t) (erase b) bi
  | .letE _ t v b nd => .letE .anonymous (erase t) (erase v) (erase b) nd
  | .mdata _ e => erase e
  | .proj n i e => .proj n i (erase e)
  | e => e

def close : List Local → Expr → Expr
  | [], e => e
  | l :: ls, e => close ls (.lam .anonymous l.type e l.info)

def universesValid (params : List Lean.Name) : Canonical → Bool
  | .sort level => validLevel params level
  | .const _ levels => levels.all (validLevel params)
  | .app f a => universesValid params f && universesValid params a
  | .lam ty body _ | .forallE ty body _ => universesValid params ty && universesValid params body
  | .letE ty value body _ => universesValid params ty && universesValid params value && universesValid params body
  | .proj _ _ target => universesValid params target
  | .unfolded .. => false
  | _ => true

def raw (params : List Lean.Name) (depth : Nat) (e : Expr) : Except Error Canonical := do
  if e.hasFVar then throw .freeVariable
  if e.hasMVar then throw .metavariable
  let some c := reify e | throw (.definition .malformed)
  if !universesValid params c then throw .invalidUniverse
  if !c.sourceScoped params depth then throw .illScoped
  pure c

def kernelFailure (fallback : Error) : Kernel.Exception → Error
  | .deterministicTimeout | .excessiveMemory => .resource
  | .deepRecursion => .recursion
  | .interrupted => .interrupted
  | _ => fallback

/-- Check the closed telescope with the existing kernel inspector. No supplied
inference or inspection callback participates in the reference graph. -/
def inferred (env : Environment) (t : Task) : Except Error Expr :=
  match Kernel.check env {} (close t.locals (erase t.expression)) with
  | .ok ty => .ok ty
  | .error err => .error (kernelFailure .illTyped err)

/-- Observe the eventual result of the *instantiated application*, including
partial applications. Kernel head conversion is used only for classification;
it does not put computational definition bodies into the canonical input. -/
def propResult (env : Environment) : Nat → Expr → Except Error Bool
  | 0, _ => .error .resource
  | fuel + 1, ty =>
    match Kernel.whnf env {} ty with
    | .error err => .error (kernelFailure .unsupported err)
    | .ok (.forallE _ _ body _) => propResult env fuel body
    | .ok (.sort .zero) => .ok true
    | .ok _ => .ok false

/-- A v2 label carries raw v1 rawSyntax plus framed declaration/signature records.
Tags: 0 rawSyntax, 1 folded constant, 2 definition expansion, 3 Prop signatures,
4 active recursive reference. Lists are ordered, never treated as sets. -/
structure Label where
  tag : Nat
  names : List Lean.Name
  numbers : List Nat
  rawSyntax : List Canonical

inductive Tree where
  | node (label : Label) (children : List Tree)

/-- The original occurrence is always retained, including its complete spine. -/
def label (t : Task) (tag : Nat) (names : List Lean.Name := [])
    (numbers : List Nat := []) (rawSyntax : List Canonical := []) : Except Error Label := do
  let source ← raw t.params t.locals.length (erase t.expression)
  pure ⟨tag, t.params ++ names, t.params.length :: t.locals.length :: numbers, source :: rawSyntax⟩

def template (t : Task) (ci : ConstantInfo) (e : Expr) : Task :=
  ⟨ci.levelParams, [], ci.name :: t.active, e⟩

/-- Fold bodies, but retain and traverse their actual signatures. This covers
constructor owners and named projection owners even when their proof arguments
are opaque. Active names prevent cycling through signature references. -/
def folded (t : Task) (ci : ConstantInfo) (args : List Task) : Except Error (Label × List Task) := do
  let ty ← raw ci.levelParams 0 ci.type
  let next := if t.active.contains ci.name then [] else [template t ci ci.type]
  pure (← label t 1 (ci.name :: ci.levelParams) [ci.levelParams.length] [ty], args ++ next)

def peel : Nat → Expr → Except Error Expr
  | 0, ty => .ok ty
  | k + 1, .forallE _ _ body _ => peel k body
  | _, _ => .error .illTyped

structure Signature where
  params : List Lean.Name
  source : Canonical
  original : Task
  instantiated : Task
  requestedIndices : List Canonical

def child (t : Task) (e : Expr) : Task := { t with expression := e }

def argumentTasks (t : Task) (e : Expr) : List Task :=
  e.getAppArgs.toList.map (child t)

/-- Capture-avoiding parameter substitution in a signature telescope. Indices
remain bound by that signature; the occurrence's actual indices are separately
retained in its source spine and argument children. -/
def instantiateParameters : Expr → List Expr → Expr
  | .forallE _ _ body _, a :: args => instantiateParameters (body.instantiate1 a) args
  | ty, _ => ty

/-- Checked indexed signature representation. Universe and owner parameters
are instantiated in both kinds. Projection indices are instantiated too.
Constructor result indices remain expressions under the constructor's own field
binders; they are paired with the supplied occurrence-index tuple, not solved or
used to filter constructors. Thus every constructor is inspected, including ones
whose result indices differ from the current occurrence. The two scopes are
retained separately by original/instantiated tasks and requestedIndices.
Implementation bodies, proofs and recursor implementations are absent. -/
def signature (env : Environment) (t : Task) (owner : InductiveVal)
    (levels : List Level) (args : List Expr) (n : Lean.Name) : Except Error Signature := do
  let some ci := env.toKernelEnv.find? n | throw (.definition .missing)
  if ci.isUnsafe then throw (.definition .unsafeDefinition)
  if ci.levelParams.length != levels.length then throw .invalidUniverse
  let source ← raw ci.levelParams 0 ci.type
  let constructor := ci matches .ctorInfo _
  let count := if constructor then owner.numParams else owner.numParams + owner.numIndices
  let instantiated := instantiateParameters
    (ci.type.instantiateLevelParams ci.levelParams levels) (args.take count)
  let indices ← ((args.drop owner.numParams).take owner.numIndices).mapM
    (raw t.params t.locals.length)
  pure ⟨ci.levelParams, source, template t ci ci.type,
    { t with expression := instantiated }, indices⟩

/-- Constructor order comes from ConstantInfo; field order comes from the actual
StructureInfo, not alphabetical order or erased binder names. -/
def signatureNames (env : Environment) (d : InductiveVal) : Except Error (List Lean.Name × List Lean.Name) := do
  let mut fields := []
  if let some si := getStructureInfo? env d.name then
    for field in si.fieldNames.toList do
      let some fi := si.fieldInfo.toList.find? (fun f => f.fieldName == field)
        | throw .unsupported
      fields := fields ++ [field, fi.projFn]
  pure (d.ctors, fields)

/-- One independent graph observation. Full spines are classified before their
head is traversed. In particular the generated Input matcher is classified
with its actual motive/universes, while compile/run/data bodies stay folded.
Active names terminate recursive/mutual Prop expansion; references retain the
actual source application, and the first expansion retains its declaration. -/
def step (env : Environment) (fuel : Nat) (t : Task) : Except Error (Label × List Task) := do
  let e := erase t.expression
  let _ ← raw t.params t.locals.length e
  let ty ← inferred env t
  let family ← propResult env fuel ty
  if let .const n levels := e.getAppFn then
    let some ci := env.toKernelEnv.find? n | throw (.definition .missing)
    if ci.levelParams.length != levels.length then throw .invalidUniverse
    if ci.isUnsafe then throw (.definition .unsafeDefinition)
    let args := argumentTasks t e
    match ci with
    | .defnInfo d =>
      if family && (`Solidity).isPrefixOf n && (env.getProjectionFnInfo? n).isNone then
        let dt ← raw d.levelParams 0 d.type
        let dv ← raw d.levelParams 0 d.value
        if t.active.contains n then
          return (← label t 4 (n :: d.levelParams) [d.levelParams.length] [dt, dv], args)
        let body := Expr.beta (d.value.instantiateLevelParams d.levelParams levels) e.getAppArgs
        let next := { t with active := n :: t.active, expression := body }
        return (← label t 2 (n :: d.levelParams) [d.levelParams.length] [dt, dv], args ++ [template next ci d.type, template next ci d.value, next])
      else
        return ← folded t ci args
    | .inductInfo d =>
      if family then
        let dt ← raw d.levelParams 0 d.type
        if t.active.contains n then
          return (← label t 4 (n :: d.levelParams) [d.numParams, d.numIndices] [dt], args)
        let (ctors, fields) ← signatureNames env d
        let projections := fields.zipIdx.filterMap fun (name, i) => if i % 2 == 1 then some name else none
        let names := ctors ++ projections
        let next := { t with active := n :: t.active }
        let sigs ← names.mapM (signature env next d levels e.getAppArgs.toList)
        return (← label t 3 (n :: d.levelParams ++ d.all ++ ctors ++ fields ++ sigs.flatMap (·.params))
          ([d.levelParams.length, d.all.length, ctors.length, fields.length,
           d.numParams, d.numIndices] ++ sigs.map (·.params.length) ++
            sigs.map (·.requestedIndices.length))
          (dt :: sigs.map (·.source) ++ sigs.flatMap (·.requestedIndices)),
          args ++ [template next ci d.type] ++ sigs.flatMap (fun s => [s.original, s.instantiated]))
      else
        return ← folded t ci args
    | _ => return ← folded t ci args
  else
    let children ← match e with
      | .app f a => pure [child t f, child t a]
      | .lam _ ty body bi | .forallE _ ty body bi =>
        pure [child t ty, { t with locals := ⟨ty, bi⟩ :: t.locals, expression := body }]
      | .letE _ ty value body _ =>
        pure [child t ty, child t value, child t (body.instantiate1 value)]
      | .proj _ _ target => do
        let targetType ← inferred env (child t target)
        let openType ← peel t.locals.length targetType
        pure [child t target, child t openType]
      | _ => pure []
    return (← label t 0, children)

/-- Child errors propagate in left-to-right preorder. -/
def collect : List (Except Error Tree) → Except Error (List Tree)
  | [] => .ok []
  | .error e :: _ => .error e
  | .ok tree :: rest => (collect rest).map (tree :: ·)

mutual
/-- Finite independent evaluation graph, not an implementation callback.
Fuel bounds both graph depth and classification telescope traversal. -/
inductive Derives (env : Environment) : Nat → Task → Except Error Tree → Prop where
  | exhausted : Derives env 0 t (.error .resource)
  | failed (h : step env fuel t = .error err) :
      Derives env (fuel + 1) t (.error err)
  | node (h : step env fuel t = .ok (lab, tasks))
      (children : DerivesList env fuel tasks results)
      (output : collect results = .ok trees) :
      Derives env (fuel + 1) t (.ok (.node lab trees))
  | childFailed (h : step env fuel t = .ok (lab, tasks))
      (children : DerivesList env fuel tasks results)
      (output : collect results = .error err) :
      Derives env (fuel + 1) t (.error err)

inductive DerivesList (env : Environment) : Nat → List Task → List (Except Error Tree) → Prop where
  | nil : DerivesList env fuel [] []
  | cons : Derives env fuel task result → DerivesList env fuel tasks results →
      DerivesList env fuel (task :: tasks) (result :: results)
end

/-- Root inspection is v1's unchanged actual-kernel-environment inspection.
A goal must itself be a checked safe definition of Prop. -/
def root (env : Environment) (n : Lean.Name) : Except Error (Label × Task) := do
  let d ← (inspectIn env n).mapError Error.definition
  let some (.defnInfo info) := env.toKernelEnv.find? n | throw (.definition .notDefinition)
  if info.type != .sort .zero then throw .notProposition
  let source := Canonical.const n (d.levelParams.map Level.param)
  let lab : Label := ⟨5, n :: d.levelParams, [d.levelParams.length, 0], [source, d.type, d.value]⟩
  pure (lab, ⟨d.levelParams, [], [n], info.value⟩)

/-- Root capture is unconditional on namespace: every registered goal is bound
 to its actual definition. Only *transitive* definition unfolding is restricted
 to Solidity Prop families. -/
def RootGraph (env : Environment) (fuel : Nat) (n : Lean.Name) (out : Except Error Tree) : Prop :=
  match root env n with
  | .error err => out = .error err
  | .ok (lab, t) => ∃ body : Except Error Tree,
      Derives env fuel t body ∧ out = body.map (fun tree => .node lab [tree])

/-- Fixed reference support requires finite successful environment observations,
not a caller predicate or success of the future implementation. Downstream
integration must exhibit this for *every* required current name; unsupported
names must be rejected, never omitted from the required coverage. -/
def Supported (env : Environment) (n : Lean.Name) : Prop :=
  ∃ fuel tree, RootGraph env fuel n (.ok tree)

namespace EncodingV2

def listOf (encode : A → Option (List Nat)) : List A → Option (List Nat)
  | [] => some [0]
  | a :: rest => do
    let bytes ← encode a
    pure ([1] ++ Encoding.number bytes.length ++ bytes ++ (← listOf encode rest))

def labelBytes (lab : Label) : Option (List Nat) := do
  let names ← listOf (fun n => some (Encoding.name n)) lab.names
  let numbers ← listOf (fun n => some (Encoding.number n)) lab.numbers
  let terms ← listOf (Encoding.term ((lab.numbers[1]?).getD 0)) lab.rawSyntax
  pure (Encoding.number lab.tag ++ names ++ numbers ++ terms)

mutual
  def treeBytes : Tree → Option (List Nat)
    | .node lab children => do
      let bytes ← labelBytes lab
      pure (Encoding.number bytes.length ++ bytes ++ (← forestBytes children))
  def forestBytes : List Tree → Option (List Nat)
    | [] => some [0]
    | tree :: rest => do
      let bytes ← treeBytes tree
      pure ([1] ++ Encoding.number bytes.length ++ bytes ++ (← forestBytes rest))
end

/-- The v2 version prefix is disjoint from unchanged v1. Nodes, fields,
constructors, arguments and children retain reference traversal order. -/
def encode (tree : Tree) : Option (List Nat) :=
  (treeBytes tree).map ([71, 80, 2, 0] ++ ·)

end EncodingV2

/-- Independently authenticated by downstream CI before use. A row binds an
exact triple to a canonical H-number in a specified historical source document;
it is not an authorization oracle. Pure laws check syntax and exact agreement,
not whether a person really approved the historical record. -/
structure Authorization where
  pin : Pin
  recordId : String
  sourceDocument : String

structure Manifest where
  sourceRevision : String
  records : List Authorization

def Manifest.WellFormed (m : Manifest) : Prop :=
  m.sourceRevision ≠ "" ∧ (m.records.map (·.pin.goal)).Nodup ∧
  ∀ a ∈ m.records, a.pin.WellFormed ∧ a.recordId = a.pin.decisionId ∧ a.sourceDocument ≠ ""

/-- Agreement is with an independent manifest, never an entry compared with
itself. H0 is neither specially excluded nor treated as authenticated history. -/
def AuthorizedTriples (m : Manifest) (pins : List Pin) : Prop :=
  ∀ p ∈ pins, ∃ a ∈ m.records, a.pin = p

/-- Required names are observations of v1.required; there is no list-valued
coverage argument on the current-environment entry point. -/
structure Snapshot where
  env : Environment
  requiredNames : List Lean.Name

def registryNames (s : Snapshot) : List Lean.Name :=
  (Solidity.Goal.goalExt.getState s.env).toList.map (·.decl)

/-- Read the actual imported environment and unchanged roadmap classifier.
All duplicate/finish-shape/dependency/status errors from v1 are preserved.
This action cannot establish that every goal module has been imported. -/
def readSnapshot : MetaM (Except Error Snapshot) := do
  let env ← getEnv
  let names ← withEnv env GoalPinSpec.required
  pure (names.mapError Error.coverage |>.map fun ns => ⟨env, ns⟩)

/-- An actual execution of the fixed capture route, from the same environment.
No caller-supplied inspection action or coverage list is quantified here. -/
def ObservedSnapshot (s : Snapshot) : Prop :=
  ∃ (mc : Lean.Meta.Context) (ms : Lean.Meta.State)
    (cc : Lean.Core.Context) (cs post : Lean.Core.State)
    (world nextWorld : IO.RealWorld),
    cs.env = s.env ∧
    ((readSnapshot.run' mc ms).run cc cs) world =
      EStateM.Result.ok (.ok s, post) nextWorld


/-- Fixed precedence for independent structural/triple failures. The source
checker must reject identical repeats as duplicates too. -/
def issues (s : Snapshot) (m : Manifest) (pins : List Pin) : List (Error × Prop) :=
  [(.duplicatePin, ¬ Unique pins),
   (.malformedPin, ∃ p ∈ pins, ¬ p.WellFormed),
   (.malformedManifest, ¬ m.WellFormed),
   (.unknownGoal, ∃ p ∈ pins, p.goal ∉ registryNames s),
   (.missingPin, ¬ Covers s.requiredNames pins),
   (.missingDecision, ∃ p ∈ pins, ¬ ∃ a ∈ m.records, a.pin.goal = p.goal),
   (.decisionMismatch, ¬ AuthorizedTriples m pins)]

inductive FirstIssue : List (Error × Prop) → Error → Prop where
  | here : condition → FirstIssue ((err, condition) :: rest) err
  | later : ¬ condition → FirstIssue rest err → FirstIssue ((other, condition) :: rest) err

def Clean (s : Snapshot) (m : Manifest) (pins : List Pin) : Prop :=
  ∀ issue ∈ issues s m pins, ¬ issue.2

def Encodable (trees : List Tree) : Prop :=
  ∀ tree ∈ trees, ∃ bytes, EncodingV2.encode tree = some bytes

/-- SHA-256 is the existing hash, not an injectivity axiom. Neither logical
 equivalence nor an equal hash by itself identifies canonical input syntax. -/
def Matches : List Pin → List Tree → Prop :=
  Pointwise fun pin tree => ∃ bytes,
    EncodingV2.encode tree = some bytes ∧ pin.digest = Solidity.Hashes.sha256 bytes

/-- Checking recomputes every committed entry; Covers makes this include every
required name, without silently dropping unsupported finish/components/proved
goals. Optional registered open goals can be pinned without being proved. -/
inductive CheckGraph (s : Snapshot) (m : Manifest) (pins : List Pin)
    (fuel : Nat) : Except Error Unit → Prop where
  | structural : FirstIssue (issues s m pins) err → CheckGraph s m pins fuel (.error err)
  | computation : Clean s m pins →
      Pointwise (fun p => RootGraph s.env fuel p.goal) pins outputs →
      collect outputs = .error err → CheckGraph s m pins fuel (.error err)
  | encoding : Clean s m pins →
      Pointwise (fun p => RootGraph s.env fuel p.goal) pins outputs →
      collect outputs = .ok trees → ¬ Encodable trees →
      CheckGraph s m pins fuel (.error .unsupported)
  | mismatch : Clean s m pins →
      Pointwise (fun p => RootGraph s.env fuel p.goal) pins outputs →
      collect outputs = .ok trees → Encodable trees → ¬ Matches pins trees →
      CheckGraph s m pins fuel (.error .digestMismatch)
  | success : Clean s m pins →
      Pointwise (fun p => RootGraph s.env fuel p.goal) pins outputs →
      collect outputs = .ok trees → Matches pins trees →
      CheckGraph s m pins fuel (.ok ())

/-- Correct pins are characterized by independent actual-environment graphs,
encoding and manifest agreement, not by the candidate checker's answers. -/
def CorrectPins (s : Snapshot) (m : Manifest) (pins : List Pin) : Prop :=
  Clean s m pins ∧ ∀ p ∈ pins, ∃ fuel tree bytes,
    RootGraph s.env fuel p.goal (.ok tree) ∧ EncodingV2.encode tree = some bytes ∧
    p.digest = Solidity.Hashes.sha256 bytes

/-- Parsed source rows retain the decision identifier spelling. The scripts'
byte/file parser must produce these exact rows or reject malformed file syntax;
that external parser cannot silently repair a digest or decision identifier. -/
structure RawPin where
  goal : Lean.Name
  digest : List Nat
  decisionId : String

def RowOf (row : RawPin) (pin : Pin) : Prop :=
  row.goal = pin.goal ∧ row.digest = pin.digest ∧ row.decisionId = pin.decisionId ∧ pin.WellFormed

/-- A canonical H<n> string and 32-byte digest are required; any other spelling
or byte range is rejected. Duplicates are retained for CheckGraph to reject. -/
inductive DecodeGraph (rows : List RawPin) : Except Error (List Pin) → Prop where
  | success : Pointwise RowOf rows pins → DecodeGraph rows (.ok pins)
  | malformed : (∃ row ∈ rows, ¬ ∃ pin, RowOf row pin) →
      DecodeGraph rows (.error .malformedPin)

/-- Required implementation signatures. The future implementation has a direct
executable refinement route: recurse on fuel and the finite task list using
step/collect; implement finite manifest/pin comparisons; bind current to the
fixed readSnapshot action. No classical selection of a sound callback suffices.
No implementation or proof is supplied in this prerequisite. -/
structure Operations where
  decode : List RawPin → Except Error (List Pin)
  rawCurrent : Nat → Manifest → List RawPin → MetaM (Except Error Unit)
  recompute : Environment → Nat → Lean.Name → Except Error Tree
  check : Snapshot → Nat → Manifest → List Pin → Except Error Unit
  current : Nat → Manifest → List Pin → MetaM (Except Error Unit)

/-- The entire success and error graphs are fixed independently. In particular,
reject-all, ignoring committed pins, or accepting a pin's own decision as its
authorization cannot satisfy the positive refinement/completeness laws. -/
structure Laws (ops : Operations) : Prop where
  decode_exact : ∀ rows output, ops.decode rows = output ↔ DecodeGraph rows output
  raw_current_route : ∀ fuel manifest rows, ops.rawCurrent fuel manifest rows = (do
    match ops.decode rows with
    | .error err => pure (.error err)
    | .ok pins => ops.current fuel manifest pins)
  recompute_exact : ∀ env fuel name output,
    ops.recompute env fuel name = output ↔ RootGraph env fuel name output
  check_exact : ∀ snapshot fuel manifest pins output, ObservedSnapshot snapshot →
    ops.check snapshot fuel manifest pins = output ↔ CheckGraph snapshot manifest pins fuel output
  current_route : ∀ fuel manifest pins, ops.current fuel manifest pins = (do
    let snapshot ← readSnapshot
    match snapshot with
    | .error err => pure (.error err)
    | .ok s => pure (ops.check s fuel manifest pins))
  graph_deterministic : ∀ env fuel name a b,
    RootGraph env fuel name a → RootGraph env fuel name b → a = b
  check_deterministic : ∀ s m pins fuel a b,
    CheckGraph s m pins fuel a → CheckGraph s m pins fuel b → a = b
  budget_adequate : ∀ env name fuel tree,
    RootGraph env fuel name (.ok tree) → ∀ larger, fuel ≤ larger →
      RootGraph env larger name (.ok tree)
  supported_complete : ∀ env name, Supported env name →
    ∃ bound tree, ∀ fuel, bound ≤ fuel → ops.recompute env fuel name = .ok tree
  correct_pins_complete : ∀ s m pins, ObservedSnapshot s → CorrectPins s m pins →
    ∃ bound, ∀ fuel, bound ≤ fuel → ops.check s fuel m pins = .ok ()
  success_encodes : ∀ env fuel name tree,
    RootGraph env fuel name (.ok tree) → ∃ bytes, EncodingV2.encode tree = some bytes
  collision_boundary : ∀ a b bytesA bytesB,
    EncodingV2.encode a = some bytesA → EncodingV2.encode b = some bytesB →
    CollisionFreeOn bytesA bytesB →
    Solidity.Hashes.sha256 bytesA = Solidity.Hashes.sha256 bytesB → bytesA = bytesB

inductive Subtree : Tree → Tree → Prop where
  | root : Subtree tree tree
  | descend {inner sub : Tree} {children : List Tree} {lab : Label} :
      inner ∈ children → Subtree sub inner → Subtree sub (.node lab children)

/-- A signature/expansion record for this exact declaration identity. -/
def HasRecord (tree : Tree) (tag : Nat) (name : Lean.Name) : Prop :=
  ∃ lab children, Subtree (.node lab children) tree ∧ lab.tag = tag ∧
    lab.names[(lab.numbers[0]?).getD 0]? = some name

/-- A mandatory *positive* downstream integration gate, separate from universal
pure laws. The runner must obtain s from readSnapshot, load the complete registry
outward, and exhibit successful reference support for every required identity.
This is required acceptance evidence, not a support assumption used to prove
Laws or a claim that current support has already been checked here. -/
def IntegrationAcceptance (ops : Operations) (s : Snapshot) (m : Manifest)
    (pins : List Pin) (fuel : Nat) : Prop :=
  ObservedSnapshot s ∧
  s.env.header.moduleNames.contains `Solidity.Goals = true ∧
  s.env.header.moduleNames.contains `Solidity.Goals.Pins = true ∧
  `Solidity.Goals.projectFinished ∈ s.requiredNames ∧
  (∀ name ∈ s.requiredNames, Supported s.env name) ∧
  CorrectPins s m pins ∧ ops.check s fuel m pins = .ok () ∧
  ∃ tree, RootGraph s.env fuel `Solidity.Goals.compilerEndpointCorrect (.ok tree) ∧
    HasRecord tree 2 `Solidity.Evm.Compiler.Compilation.Input ∧
    HasRecord tree 3 `Solidity.Evm.Memory.Objects.StateRepr ∧
    ¬ HasRecord tree 2 `Solidity.Evm.Compiler.compile ∧
    ¬ HasRecord tree 2 `Solidity.Evm.run ∧
    ¬ HasRecord tree 3 `Solidity.Evm.Compiler.Compilation

/-! Mandatory future operational acceptance (not facts established by Laws).

* The downstream integration runner must use Operations.current/readSnapshot,
  import the complete generated Goals registry and completed Goals.Pins outward,
  and produce IntegrationAcceptance on correct committed pins. No required name,
  including projectFinished, may be dropped for being open, Unstated, expensive,
  recursive or a Prop structure. A finite recursive reference is success syntax;
  genuine resource/query failures are explicit rejections. A larger adequate
  budget must succeed on supported inputs; unexplained failure is not adequate.
* Stale or mismatched committed triples must fail elaboration. An isolated
  CompilerEndpointWith premise weakening must be rejected in a temporary fixture
  without modifying production declarations. H706/H710 requires constructor and
  field-signature changes of reachable Prop structures to affect canonical input.
* Under H664 a new compiling Compilation branch can pass the extension control
  only if canonical Input encoding is unchanged and all other pin checks pass.
  Otherwise reject until a recorded decision authorizes the changed triple and
  committed pins are updated. No unconditional backend-extension stability law
  is asserted. Data-inductive bodies and compile/run implementations stay folded.
* Before accepting Manifest, CI must authenticate sourceRevision/sourceDocument
  against the actual immutable decision history, verify the human approval and
  its exact goal/digest/H-number binding, and validate the exact Goal-Change: H<n>
  trailer on each pin-changing commit against those records. Manifest syntax or
  an arbitrary Nat is not historical authorization. Forged/unapproved records,
  missing/mismatched trailers and manifest-to-entry disagreement must fail CI.
* A hash match only compares SHA-256 results. Any inference to encoded-input
  equality requires CollisionFreeOn for that pair. Logical equivalence neither
  implies canonical equality nor independently authorizes a pin change.

The future Tools.GoalPins imports this specification and realizes Operations.
Goals.Pins imports both and proves Solidity.GoalPins.correct by constructing that
realizer and Laws; Examples.Goals.Pins performs the outward integration gates.
Neither this specification nor Tools.GoalPins imports the generated Goals root
or Goals.Pins. Implementations, proofs and the operational gates remain future
work; this prerequisite's separate example deliberately keeps the goal open.
-/

end GoalPinSpecV2

open Solidity.Goal

/-- Environment-bound statement-pin recomputation and exact committed checking.
The witness must refine the independent graphs with positive completeness;
operational acceptance additionally requires the integration gates above. -/
@[goal Solidity.GoalPins.correct "gp-goal-pins"]
def goalPinsCorrect : Prop := ∃ ops : GoalPinSpecV2.Operations, GoalPinSpecV2.Laws ops

end Solidity.Goals
