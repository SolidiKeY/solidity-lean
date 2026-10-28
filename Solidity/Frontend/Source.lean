import Lean
import Solidity.Language.Features

/-!
# The compiler boundary of imported source

This records the selected SHA-pinned compiler and settings of the source
helper. It is provenance of an external validation step, not a theorem of
compiler correctness or authentication of an arbitrary hand-written fixture.
Historical fixtures retain an explicit legacy boundary.
-/

namespace Solidity.Frontend.Source
open Lean (Json)
open Solidity.Language

inductive Compiler where
  | solkey0834 | catalog0838
  deriving Repr, DecidableEq, Inhabited

deriving instance Lean.ToExpr for Compiler

def Compiler.version : Compiler → String
  | .solkey0834 => "0.8.34+commit.80d5c536.Emscripten.clang"
  | .catalog0838 => "0.8.38+commit.1835d247.Emscripten.clang"

def Compiler.file : Compiler → String
  | .solkey0834 => "soljson-v0.8.34+commit.80d5c536.js"
  | .catalog0838 => "soljson-v0.8.38+commit.1835d247.js"

def Compiler.sha256 : Compiler → String
  | .solkey0834 => "c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8"
  | .catalog0838 => "6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390"

inductive AbiCoder where
  | v1 | v2
  deriving Repr, DecidableEq, Inhabited

deriving instance Lean.ToExpr for AbiCoder

inductive Pipeline where
  | legacy | viaIR
  deriving Repr, DecidableEq, Inhabited

deriving instance Lean.ToExpr for Pipeline

inductive Gate where
  | version (tokens : List String)
  | abiCoder (coder : AbiCoder)
  | encoderV2
  | smtChecker
  deriving Repr, DecidableEq, Inhabited

deriving instance Lean.ToExpr for Gate

structure Pragmas where
  requestedCoder : AbiCoder := .v2
  gates : List Gate := []
  deriving Repr, Inhabited

/-- Only compiler-accepted modes are known here. Repeated/conflicting coder
directives fail independently rather than acquiring last-wins semantics. -/
def readPragmas (ast : Json) : Except String Pragmas := do
  let nodes ← ast.getObjValAs? (Array Json) "nodes"
  let mut result : Pragmas := {}
  let mut explicit : Option AbiCoder := none
  let mut experimental := false
  let mut smt := false
  for node in nodes do
    if (node.getObjValAs? String "nodeType").toOption != some "PragmaDirective" then continue
    let tokens ← node.getObjValAs? (Array String) "literals"
    match tokens.toList with
    | "solidity" :: constraints =>
      if constraints.isEmpty then throw "empty compiler version pragma"
      result := { result with gates := result.gates ++ [.version constraints] }
    | ["abicoder", mode] =>
      let coder ← match mode with
        | "v1" => pure AbiCoder.v1
        | "v2" => pure AbiCoder.v2
        | _ => throw "unknown ABI coder pragma"
      if explicit.isSome || experimental then throw "repeated or conflicting ABI coder pragmas"
      explicit := some coder
      result := { requestedCoder := coder, gates := result.gates ++ [.abiCoder coder] }
    | ["experimental", "ABIEncoderV2"] =>
      if experimental || explicit == some .v1 then throw "repeated or conflicting ABI encoder pragmas"
      experimental := true
      result := { requestedCoder := .v2, gates := result.gates ++ [.encoderV2] }
    | ["experimental", "SMTChecker"] =>
      if smt then throw "repeated SMTChecker pragma"
      smt := true
      result := { result with gates := result.gates ++ [.smtChecker] }
    | _ => throw "unknown enabled compiler language mode"
  return result

/-- Historical fixtures have no recorded settings. An analysed fixture has
one selected pipeline and its validated settings text. The effective coder
is an observation of this mode and the requested coder, never separate state. -/
inductive Compilation where
  | historical
  | analysed (pipeline : Pipeline) (settings : String)
  deriving Repr, Inhabited

deriving instance Lean.ToExpr for Compilation

/-- One original solc source unit, retaining its own language modes and digest. -/
structure SourceFile where
  name : String
  sourceId : Nat
  declarationId : Nat
  sourceSha256 : String
  requestedCoder : AbiCoder
  gates : List Gate
  deriving Repr, Inhabited

deriving instance Lean.ToExpr for SourceFile

structure Provenance where
  compiler : Compiler
  solkeyCommit : String
  source : String
  sourceSha256 : String
  compilation : Compilation
  requestedCoder : AbiCoder
  gates : List Gate
  /-- Empty for the historical/single-source schemas; complete for a compilation unit. -/
  sources : List SourceFile := []
  deriving Repr, Inhabited

deriving instance Lean.ToExpr for Provenance

def Provenance.legacyFixture (provenance : Provenance) : Bool :=
  match provenance.compilation with
  | .historical => true
  | .analysed _ _ => false

def Provenance.pipeline (provenance : Provenance) : Option Pipeline :=
  match provenance.compilation with
  | .historical => none
  | .analysed pipeline _ => some pipeline

def Provenance.settings (provenance : Provenance) : String :=
  match provenance.compilation with
  | .historical => ""
  | .analysed _ settings => settings

/-- via-IR uses v2 regardless of the requested pragma. Historical v1 fixtures
do not establish an effective coder; historical v2 retains the known default. -/
def Provenance.effectiveCoder (provenance : Provenance) : Option AbiCoder :=
  match provenance.compilation with
  | .analysed .viaIR _ => some .v2
  | .analysed .legacy _ => some provenance.requestedCoder
  | .historical => if provenance.requestedCoder == .v2 then some .v2 else none

def parseCompiler (version : String) : Except String Compiler :=
  if version == Compiler.solkey0834.version then pure .solkey0834
  else if version == Compiler.catalog0838.version then pure .catalog0838
  else throw "compiler version is not one of the two supported exact pins"

private def digest (s : String) : Bool :=
  s.length == 64 && s.toList.all fun c =>
    ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')


private def onlyKeys (j : Json) (allowed : List String) : Bool :=
  match j with
  | .obj fields => fields.toList.all fun (key, _) => allowed.contains key
  | _ => false

private def validateSettings (settings : Json) (compilationUnit : Bool) : Except String Bool := do
  unless onlyKeys settings ["viaIR", "evmVersion", "optimizer", "libraries", "remappings", "outputSelection"] do
    throw "unknown compiler setting"
  let viaIR ← settings.getObjValAs? Bool "viaIR"
  let evm ← settings.getObjValAs? String "evmVersion"
  unless ["homestead", "tangerineWhistle", "spuriousDragon", "byzantium",
      "constantinople", "petersburg", "istanbul", "berlin", "london", "paris",
      "shanghai", "cancun", "prague", "osaka"].contains evm do
    throw "unknown EVM target"
  let optimizer ← settings.getObjVal? "optimizer"
  unless onlyKeys optimizer ["enabled", "runs"] do throw "unknown optimizer setting"
  let _ ← optimizer.getObjValAs? Bool "enabled"
  let _ ← optimizer.getObjValAs? Nat "runs"
  let libraries ← settings.getObjVal? "libraries"
  unless onlyKeys libraries [] do throw "library linking is not in this source boundary"
  let remappings ← settings.getObjValAs? (Array String) "remappings"
  unless compilationUnit || remappings.isEmpty do
    throw "import remappings need compilation-unit provenance"
  for remapping in remappings do
    match remapping.splitOn "=" with
    | fromPath :: _target :: _ =>
      unless !fromPath.isEmpty &&
          !(fromPath.splitOn ":").getLast!.isEmpty do throw "malformed import remapping"
    | _ => throw "malformed import remapping"
  let output ← settings.getObjVal? "outputSelection"
  unless onlyKeys output ["*"] do throw "unknown output selection"
  let unit ← output.getObjVal? "*"
  unless onlyKeys unit [""] &&
      (← unit.getObjValAs? (Array String) "") == #["ast"] do
    throw "source provenance records AST analysis only"
  return viaIR

/-- Validate the schema against the selected binary and AST pragmas.
The helper's successful solc analysis checks version constraints and types. -/
def read (fixture ast : Json) (compilationUnit : Bool := false) : Except String Provenance := do
  unless (← ast.getObjValAs? String "nodeType") == "SourceUnit" do
    throw "source provenance requires a SourceUnit AST"
  let header ← fixture.getObjVal? "header"
  let solkeyCommit ← header.getObjValAs? String "solkeyCommit"
  let compiler ← parseCompiler (← header.getObjValAs? String "solcVersion")
  let source ← header.getObjValAs? String "source"
  let sourceSha256 ← header.getObjValAs? String "sourceSha256"
  unless !source.isEmpty && digest sourceSha256 do throw "malformed source provenance"
  let pragmas ← readPragmas ast
  match (header.getObjVal? "provenanceVersion").toOption with
  | none =>
    unless onlyKeys header ["solcVersion", "sourceSha256", "solkeyCommit", "source"] do
      throw "incomplete modern provenance cannot become a legacy fixture"
    return {
      compiler, solkeyCommit, source, sourceSha256
      requestedCoder := pragmas.requestedCoder
      gates := pragmas.gates, compilation := .historical }
  | some schema =>
    unless onlyKeys header ["solcVersion", "sourceSha256", "solkeyCommit", "source",
        "provenanceVersion", "compilerFile", "compilerSha256", "validationStage",
        "settings", "acceptedPragmas"] do throw "unknown source provenance field"
    unless schema.getNat?.toOption == some 1 do throw "unknown source provenance schema"
    unless (← header.getObjValAs? String "compilerFile") == compiler.file &&
        (← header.getObjValAs? String "compilerSha256") == compiler.sha256 do
      throw "compiler binary provenance does not match its exact pin"
    unless (← header.getObjValAs? String "validationStage") == "analysis" do
      throw "unknown source validation stage"
    let settings ← header.getObjVal? "settings"
    let viaIR ← validateSettings settings compilationUnit
    let pipeline := if viaIR then Pipeline.viaIR else .legacy
    let recorded ← header.getObjValAs? (Array (Array String)) "acceptedPragmas"
    let actual ← (← ast.getObjValAs? (Array Json) "nodes").toList.filterMapM fun node => do
      if (node.getObjValAs? String "nodeType").toOption == some "PragmaDirective" then
        return some (← node.getObjValAs? (Array String) "literals")
      else return none
    unless recorded.toList == actual do throw "recorded pragmas disagree with the source AST"
    return {
      compiler, solkeyCommit, source, sourceSha256
      requestedCoder := pragmas.requestedCoder
      gates := pragmas.gates, compilation := .analysed pipeline settings.compress }


/-- Distinguish profile policy, upstream limitations and implementation gaps. -/
inductive DiagnosticKind where
  | excluded | upstream | unknownNode | unresolvedReference | compilerMode
  | missingImplementation | invalidAst
  deriving Repr, DecidableEq, Inhabited

structure Diagnostic where
  kind : DiagnosticKind
  name : Lean.Name
  reason : String
  line : Nat := 0
  feature : Option Feature := none
  deriving Repr, Inhabited

deriving instance Lean.ToExpr for Solidity.Language.Feature
deriving instance Lean.ToExpr for DiagnosticKind
deriving instance Lean.ToExpr for Diagnostic

structure Use where
  feature : Feature
  line : Nat := 0
  deriving Repr, Inhabited

/-- Only the extracted feature list is certified. This is not a proof of
extractor completeness, source lowering or compiler equivalence. -/
inductive ScopeScan where
  | admitted (features : List Feature) (within : WithinProfile features)
  | rejected (features : List Feature) (diagnostic : Diagnostic)

instance : Inhabited ScopeScan :=
  ⟨.admitted [] (fun _ member => nomatch member)⟩

def ScopeScan.features : ScopeScan → List Feature
  | .admitted fs _ | .rejected fs _ => fs

def ScopeScan.diagnostic? : ScopeScan → Option Diagnostic
  | .admitted .. => none
  | .rejected _ d => some d

/-- Historical AST-analysis-only inputs cannot gain code-generation observations
from a profile change. Exact static bytes must be present as validated inputs. -/
def ScopeScan.requireCompilerCode (available : Bool) : ScopeScan → ScopeScan
  | scan@(.rejected ..) => scan
  | scan@(.admitted features _) =>
    if !available && (features.contains .creationCode || features.contains .runtimeCode) then
      let feature := if features.contains .creationCode then Language.Feature.creationCode else .runtimeCode
      .rejected features {
        kind := .excluded, name := .str (.str .anonymous "solidity") feature.id,
        feature := some feature,
        reason := "This AST-analysis input has no validated static compiler-code artifacts." }
    else scan

/-- A successful scan certifies exactly its reported feature list. -/
theorem ScopeScan.within : (scan : ScopeScan) → scan.diagnostic? = none →
    WithinProfile scan.features
  | .admitted _ within, _ => within
  | .rejected _ _, impossible => nomatch impossible

private def outsideDiagnostic (use : Use) : Diagnostic :=
  match use.feature.unmodelled? with
  | some outside => {
      kind := .excluded, name := outside.errorName, reason := outside.reason
      line := use.line, feature := some use.feature }
  | none => {
      kind := .upstream, name := .str (.str .anonymous "solidity") use.feature.id
      reason := use.feature.info.requirement, line := use.line, feature := some use.feature }

def ScopeScan.certify : List Use → ScopeScan
  | [] => default
  | use :: rest =>
    if allowed : use.feature.info.scope = .model ∨ use.feature.info.scope = .abstract then
      match certify rest with
      | .admitted fs within => .admitted (use.feature :: fs) (by
          intro f member
          rcases List.mem_cons.mp member with head | member
          · subst f; exact allowed
          · exact within f member)
      | .rejected fs d => .rejected (use.feature :: fs) d
    else .rejected ((use :: rest).map Use.feature) (outsideDiagnostic use)

def ScopeScan.append (a b : ScopeScan) : ScopeScan :=
  match a, b with
  | .admitted xs hx, .admitted ys hy =>
    .admitted (xs ++ ys) (fun f member => (List.mem_append.mp member).elim (hx f) (hy f))
  | .rejected xs d, b => .rejected (xs ++ b.features) d
  | .admitted xs _, .rejected ys d => .rejected (xs ++ ys) d

def ScopeScan.normalize : ScopeScan → ScopeScan
  | .admitted fs _ => .certify (fs.eraseDups.map fun f => ⟨f, 0⟩)
  | .rejected fs d => .rejected fs.eraseDups d

/-- JSON is the untyped external compiler format. Only resolved execution
roots execute: declaration headers and constants are followed separately.
The intrinsic model remains indexed by its contract and local context. -/
structure AdmissionRequest where
  entry : Json
  evaluatedRoots : List Json
  declarationRoots : List Json := []
  constantIds : List Int := []
  specifications : List (List String × String) := []
  modelBindings : List String := []
  unresolvedDispatch : List Json := []
  diagnostics : List Diagnostic := []
  deriving Inhabited

end Solidity.Frontend.Source


namespace Solidity.Frontend.Source

open Lean (Json)

/-- Optional exact static compiler artifacts. These are compiler-output inputs,
not observations of deployed accounts or immutable-substituted runtime state. -/
def readCompilerCode (fixture ast : Json) (provenance : Provenance) :
    Except String (List (Int × (String × String))) := do
  let some code := (fixture.getObjVal? "compilerCode").toOption | return []
  if provenance.legacyFixture then throw "static compiler code requires modern provenance"
  unless onlyKeys code ["compilerSha256", "sourceSha256", "settings", "contracts"] do
    throw "unknown static compiler-code field"
  unless (← code.getObjValAs? String "compilerSha256") == provenance.compiler.sha256 &&
      (← code.getObjValAs? String "sourceSha256") == provenance.sourceSha256 do
    throw "static compiler-code provenance mismatch"
  let base ← Json.parse provenance.settings
  let settings ← code.getObjVal? "settings"
  unless onlyKeys settings ["viaIR", "evmVersion", "optimizer", "libraries", "remappings", "outputSelection"] do
    throw "unknown static compiler-code setting"
  for key in ["viaIR", "evmVersion", "optimizer", "libraries", "remappings"] do
    unless (← settings.getObjVal? key) == (← base.getObjVal? key) do
      throw s!"static compiler-code setting mismatch: {key}"
  let declarations ← ast.getObjValAs? (Array Json) "nodes"
  let contracts ← code.getObjValAs? (Array Json) "contracts"
  let mut seen : List Int := []
  let mut names : List String := []
  let mut result := []
  for contract in contracts do
    unless onlyKeys contract ["id", "name", "creationCode", "runtimeCode"] do
      throw "unknown static compiler-code contract field"
    let id ← contract.getObjValAs? Int "id"
    let name ← contract.getObjValAs? String "name"
    unless id ≥ 0 && !name.isEmpty do throw "malformed static compiler-code identity"
    if seen.contains id || names.contains name then throw "duplicate static compiler-code identity"
    unless declarations.any (fun d =>
      (d.getObjValAs? String "nodeType").toOption == some "ContractDefinition" &&
      (d.getObjValAs? Int "id").toOption == some id &&
      (d.getObjValAs? String "name").toOption == some name) do
      throw "static compiler-code declaration identity mismatch"
    let hex (key : String) : Except String String := do
      let text ← contract.getObjValAs? String key
      unless text.length % 2 == 0 && text.length ≤ 262144 &&
          text.toList.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')) do
        throw "static compiler code is unlinked, malformed or exceeds its materialization bound"
      return text
    result := result ++ [(id, (← hex "creationCode", ← hex "runtimeCode"))]
    seen := id :: seen
    names := name :: names
  let output ← settings.getObjVal? "outputSelection"
  let .obj units := output | throw "invalid static code output selection"
  let [(unitName, unit)] := units.toList | throw "static code needs a single compilation unit"
  let expected ← ast.getObjValAs? String "absolutePath"
  unless unitName == expected do throw "static compiler-code source unit mismatch"
  unless onlyKeys unit names do throw "unknown static code output contract"
  for name in names do
    unless (← unit.getObjValAs? (Array String) name) ==
        #["evm.bytecode.object", "evm.deployedBytecode.object"] do
      throw "static compiler-code output selection mismatch"
  return result

end Solidity.Frontend.Source
