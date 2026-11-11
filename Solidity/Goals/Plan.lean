import Solidity.Tools.Goal
import Solidity.Yul.OpcodeSpec
import Solidity.Yul.Compilation.Artifact
import Solidity.Yul.Compilation.ProducerStatements
import Solidity.Yul.Compilation.WordMachine
import Solidity.Roadmap.Contracts
import Solidity.Semantics.Callback
import Solidity.Semantics.TransientWorld
import Solidity.Lowering.V08.EnvironmentProjection

/-! Plan steps outside the finish line: each goal names the theorem expected to close
it; all await vocabulary. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Main.trusted_surface_closed "va1-trust-surface"]
def trustedSurfaceClosed : Prop := Unstated

@[goal Solidity.Validation.differential_agreement "va3-semantic-validation"]
def differentialAgreement : Prop := Unstated

@[goal Solidity.Bench.budgets_met "vu1-benchmarks"]
def benchmarkBudgetsMet : Prop := Unstated

@[goal Solidity.Automation.fast_mode_agrees "vu2-fast-mode"]
def fastModeAgrees : Prop := Unstated

@[goal Solidity.Automation.Certificate.check_sound "vu3-certificates"]
def certificateCheckSound : Prop := Unstated

@[goal Solidity.Automation.Summary.call_summary_sound "vu4-modular"]
def callSummarySound : Prop := Unstated

@[goal Solidity.Yul.Views.generic_views_preserve "t1-yul-views-generic"]
def genericYulViewsPreserve : Prop := Unstated

@[goal Solidity.Controls.off_critical_path "t2-controls-off-path"]
def controlsOffCriticalPath : Prop := Unstated

@[goal Solidity.Dedup.statements_preserved "t3-dedup-rollout"]
def dedupStatementsPreserved : Prop := Unstated

@[goal Solidity.Docs.lint_clean "g2-doc-lint"]
def docLintClean : Prop := Unstated

@[goal Solidity.Docs.history_purged "g3-history-purge-docs"]
def docHistoryPurged : Prop := Unstated

@[goal Solidity.Docs.comments_as_code "g4-comments-to-code"]
def commentsAsCode : Prop := Unstated

/-! Arithmetic vocabulary for the universal opcode contract: wrappers of the
pure statements in `Solidity.Yul.OpcodeSpec`, which proofs in the core use
without importing goal tooling. -/
namespace OpcodeSpec

/-- Word modulus, independent of evaluation. -/
def modulus : Nat := Solidity.Yul.OpcodeSpec.modulus

/-- Canonical residue of a signed integer, including negative results. -/
def residue (z : Int) : Nat := Solidity.Yul.OpcodeSpec.residue z

/-- CLZ shared by Arithmetic and Bytes (`Solidity.Yul.OpcodeSpec.clz`). -/
def clz : Prop := Solidity.Yul.OpcodeSpec.clz

end OpcodeSpec

/-- SHL, SHR and SAR over every input (`Solidity.Yul.OpcodeSpec.shifts`). -/
def opcodeShifts : Prop := Solidity.Yul.OpcodeSpec.shifts

/-- The twenty arithmetic, comparison and bitwise opcodes over every input
(`Solidity.Yul.OpcodeSpec.arithmetic`). -/
def opcodeArithmetic : Prop := Solidity.Yul.OpcodeSpec.arithmetic

/-- BYTE, SIGNEXTEND, CLZ and EXP over every input
(`Solidity.Yul.OpcodeSpec.bytesPowers`). -/
def opcodeBytesPowers : Prop := Solidity.Yul.OpcodeSpec.bytesPowers

/-- Universal arithmetic agreement for the 26 distinct opcodes in the finite
Checks families. CLZ has two memberships with one identical specification.
The three family obligations are independently usable by Checks-only proofs. -/
@[goal Solidity.Yul.opcode_eval_universal "v1-yul-checks-universal"]
def opcodeEvalUniversal : Prop :=
  opcodeShifts ∧ opcodeArithmetic ∧ opcodeBytesPowers

/-! Declaration-reachability inventory for the seven Lean areas (plan step
k1-lean-inventory). The vocabulary is abstract and dependency-free: modules `M`,
declarations `D`, consumers `C` and families `F` are any types.

* `World` is what is actually true of the repository: areas, the directory or
  X/XControls/XPins grouping, declaration owners, every use between declarations
  (explicit, elaborator-generated, instance, macro or otherwise implicit), including
  uses through declarations outside the seven areas, and every consumer's uses and
  kind. `D` is the census's declaration identity: auxiliary constants may be folded
  into their parent, provided uses are folded the same way.
* `Census` is the explicit extracted input: listed modules, declarations, consumers,
  root uses, use edges and the unresolved gaps, plus the grouping and metadata.
* `Certificate` is the claimed classification with a witness per declaration.

`Adequate` holds the input-adequacy assumptions; `Census.Valid` holds only locally
checkable structural obligations (paths, closed sets, records); `Sound` is what must
be derived. Module imports appear nowhere: imports alone establish neither keep nor
orphan.

Boundary: proving `leanInventorySound` certifies only this finite abstract
reasoning. It does not certify the Python extraction, the completeness of the real
census, any wall-clock measurement, Git recovery or deletion safety; the real census
still owes its evidence and the accounting of every unresolved gap. `Adequate` for
the real repository is not established by any proof here: discharging a gap needs
the resolved edges from the elaborated environment (constants used by every compiled
declaration, auxiliary and instance constants included) or a separately verified
bridge from it; reporting a gap does not prove completeness. `unresolved` is the
conservative verdict: it is never forced into orphan, and it is precise only as far
as the listed gaps are.

The expected proof `Solidity.LeanInventory.inventory_sound` belongs to a standalone
file under `scripts/lean-inventory/` that imports this module, so no library root,
statement or guard changes; that file can pin its own `#roadmap_goal` line. -/
namespace Inventory

/-- The seven audited directories under `Solidity/`. -/
inductive Area where
  | backend | yul | lowering | frontend | solcValidation | source | optimizer
deriving DecidableEq

def Area.all : List Area :=
  [.backend, .yul, .lowering, .frontend, .solcValidation, .source, .optimizer]

/-- A module's place in its family: an ordinary member `X`, or the family's own
`XControls` / `XPins`. -/
inductive Role where
  | member | controls | pins
deriving DecidableEq

/-- A consumer. Only the first four are independent roots; `blanket` (a root importing
everything, or a whole-tree scan) is secondary coverage, and `ownControls` (such as a
runner of every Controls/Pins file) demands each used declaration for that
declaration's own family only. A consumer's kind is a fact of `World`, so a runner of
Controls labelled `test` violates `Adequate`. -/
inductive ConsumerKind (F : Type) where
  | goalProof | test | runner | cli | blanket | ownControls
deriving DecidableEq

def ConsumerKind.primary {F : Type} : ConsumerKind F → Bool
  | .goalProof | .test | .runner | .cli => true
  | .blanket | .ownControls => false

/-- Every kind except `blanket` can demand a declaration. -/
def ConsumerKind.demands {F : Type} : ConsumerKind F → Bool
  | .blanket => false
  | _ => true

/-- The source end of an unresolved dependency: a use from declaration `src`, or a
root use by `consumer`; `none` means the source itself is unknown. -/
inductive GapSource (D C : Type) where
  | use (src : Option D)
  | root (consumer : Option C)
deriving DecidableEq

/-- A documented unresolved edge or root; `target = none` means any declaration. -/
structure Gap (D C : Type) where
  source : GapSource D C
  target : Option D
  reason : String
deriving DecidableEq

/-- How one check time was obtained. -/
structure Provenance where
  source : String
  toolchain : String
  command : String
  context : String
  outcome : String

/-- A measured check time, or an explicit unavailable value with its reason. -/
inductive Measured where
  | measured (millis : Nat) (how : Provenance)
  | unavailable (reason : String)

def Measured.Recorded : Measured → Prop
  | .measured _ h => h.source ≠ "" ∧ h.toolchain ≠ "" ∧ h.command ≠ "" ∧
      h.context ≠ "" ∧ h.outcome ≠ ""
  | .unavailable r => r ≠ ""

def Measured.isMeasured : Measured → Bool
  | .measured .. => true
  | .unavailable _ => false

/-- A recoverable source identity for a family: a revision and the modules it pins. -/
structure Pin (M : Type) where
  revision : String
  modules : List M

/-- The repository as it is. -/
structure World (M D C F : Type) where
  area : M → Option Area
  family : M → F
  role : M → Role
  moduleOf : D → M
  uses : D → D → Prop
  rootUse : C → D → Prop
  kind : C → ConsumerKind F

/-- The explicit census input. -/
structure Census (M D C F : Type) where
  modules : List M
  area : M → Area
  family : M → F
  role : M → Role
  families : List F
  decls : List D
  declModule : D → M
  consumers : List C
  kind : C → ConsumerKind F
  roots : List (C × D)
  edges : List (D × D)
  gaps : List (Gap D C)
  lineBasis : String
  lines : M → Nat
  checkTime : M → Measured
  pin : F → Pin M

inductive Verdict where
  | keep | ownerNeeded | orphan | unresolved
deriving DecidableEq

/-- A classification with its witness. `keep`: a root use and a path. `ownerNeeded`:
a Controls/Pins seed of `owner` (a Controls/Pins declaration, which is thus its own
seed, or the root of an `ownControls` consumer `via`), a path, and a set refuting independent
reachability; `owner` is normally the declaration's own family, and names the other
family when only that family's Controls/Pins demand it. `orphan`: a set refuting all
demand. `unresolved`: a gap that can reach the declaration, and a set refuting
recorded keep. -/
inductive Evidence (D C F : Type) where
  | keep (consumer : C) (root : D) (path : List D)
  | ownerNeeded (owner : F) (via : Option C) (seed : D) (path : List D) (indep : List D)
  | orphan (live : List D)
  | unresolved (gap : Gap D C) (lead : D × List D) (path : List D) (recorded : List D)

def Evidence.verdict {D C F : Type} : Evidence D C F → Verdict
  | .keep .. => .keep
  | .ownerNeeded .. => .ownerNeeded
  | .orphan .. => .orphan
  | .unresolved .. => .unresolved

/-- The owner family of an `ownerNeeded` witness. -/
def Evidence.owner {D C F : Type} : Evidence D C F → Option F
  | .ownerNeeded f .. => some f
  | _ => none

/-- `unresolved` also names the live source of its gap: unknown, a demanding consumer,
or a declaration reached by `lead` (a demand seed and a recorded path to it). -/
structure Row (D C F : Type) where
  evidence : Evidence D C F
  reason : String

structure Certificate (D C F : Type) where
  entry : D → Row D C F
  family : F → Verdict

/-- Reflexive-transitive closure. -/
inductive Reach {D : Type} (R : D → D → Prop) : D → D → Prop where
  | refl (a : D) : Reach R a a
  | step {a b c : D} : R a b → Reach R b c → Reach R a c

/-- `Chain R a path b`: the listed path steps from `a` to `b` along `R`. -/
def Chain {D : Type} (R : D → D → Prop) : D → List D → D → Prop
  | a, [], b => a = b
  | a, x :: xs, b => R a x ∧ Chain R x xs b

variable {M D C F : Type}

def World.InScope (W : World M D C F) (m : M) : Prop := W.area m ≠ none

/-- Independent reachability: from a primary consumer's actual use. -/
def World.IndepReach (W : World M D C F) (d : D) : Prop :=
  ∃ c e, (W.kind c).primary ∧ W.rootUse c e ∧ Reach W.uses e d

/-- A seed of family `f`'s own demand: a declaration of an in-scope Controls/Pins
module of `f`, or an in-scope declaration of `f` used by an `ownControls` consumer. -/
def World.ControlSeed (W : World M D C F) (f : F) (s : D) : Prop :=
  W.InScope (W.moduleOf s) ∧ W.family (W.moduleOf s) = f ∧
    (W.role (W.moduleOf s) ≠ .member ∨ ∃ c, W.kind c = .ownControls ∧ W.rootUse c s)

def World.DemandBy (W : World M D C F) (f : F) (d : D) : Prop :=
  ∃ s, W.ControlSeed f s ∧ Reach W.uses s d

def World.ControlDemand (W : World M D C F) (d : D) : Prop :=
  ∃ f, W.DemandBy f d

/-- `d` is an in-scope declaration of family `f`. -/
def World.Member (W : World M D C F) (f : F) (d : D) : Prop :=
  W.InScope (W.moduleOf d) ∧ W.family (W.moduleOf d) = f

def Census.Edge (K : Census M D C F) (x y : D) : Prop := (x, y) ∈ K.edges

def Census.CoversUse (g : Gap D C) (x y : D) : Prop :=
  (g.source = .use none ∨ g.source = .use (some x)) ∧ (g.target = none ∨ g.target = some y)

def Census.CoversRoot (g : Gap D C) (c : C) (y : D) : Prop :=
  (g.source = .root none ∨ g.source = .root (some c)) ∧ (g.target = none ∨ g.target = some y)

/-- A recorded edge, or a use some gap may stand for. -/
def Census.PossStep (K : Census M D C F) (x y : D) : Prop :=
  K.Edge x y ∨ ∃ g ∈ K.gaps, Census.CoversUse g x y

/-- Keep from recorded data alone. -/
def Census.RecordedKeep (K : Census M D C F) (d : D) : Prop :=
  ∃ c e, c ∈ K.consumers ∧ (K.kind c).primary ∧ (c, e) ∈ K.roots ∧ Reach K.Edge e d

/-- `S` holds every recorded root of a consumer satisfying `p` and is closed under
recorded edges. -/
def Census.RecClosed (K : Census M D C F) (p : ConsumerKind F → Bool) (S : List D) : Prop :=
  (∀ r ∈ K.roots, p (K.kind r.1) → r.2 ∈ S) ∧ ∀ e ∈ K.edges, e.1 ∈ S → e.2 ∈ S

/-- A gap whose source may be live for `S`: an unknown source, a source in `S`, or a
consumer that might satisfy `p`. -/
def Census.GapLive (K : Census M D C F) (p : ConsumerKind F → Bool) (S : List D)
    (g : Gap D C) : Prop :=
  match g.source with
  | .use none => True
  | .use (some x) => x ∈ S
  | .root none => True
  | .root (some c) => p (K.kind c) = true

/-- `RecClosed`, and also closed under every gap: a live gap must have a known target
inside `S`. An untargeted live gap therefore blocks every absence conclusion. -/
def Census.Closed (K : Census M D C F) (p : ConsumerKind F → Bool) (S : List D) : Prop :=
  K.RecClosed p S ∧ ∀ g ∈ K.gaps, K.GapLive p S g → ∃ y, g.target = some y ∧ y ∈ S

def Census.Seed (K : Census M D C F) (f : F) (via : Option C) (s : D) : Prop :=
  match via with
  | none => s ∈ K.decls ∧ K.family (K.declModule s) = f ∧ K.role (K.declModule s) ≠ .member
  | some c => s ∈ K.decls ∧ K.family (K.declModule s) = f ∧
      c ∈ K.consumers ∧ K.kind c = .ownControls ∧ (c, s) ∈ K.roots

/-- A demand seed in the census: a listed Controls/Pins declaration, or a root of a
demanding (non-blanket) consumer. -/
def Census.DemandSeed (K : Census M D C F) (s : D) : Prop :=
  (s ∈ K.decls ∧ K.role (K.declModule s) ≠ .member) ∨
  ∃ r ∈ K.roots, r.2 = s ∧ (K.kind r.1).demands

/-- The gap's source could be live: unknown, a demanding consumer, or a declaration
reached from a demand seed `lead.1` along the recorded path `lead.2`. -/
def Census.GapSourceLive (K : Census M D C F) (g : Gap D C) (lead : D × List D) : Prop :=
  match g.source with
  | .use none | .root none => True
  | .root (some c) => (K.kind c).demands
  | .use (some x) => K.DemandSeed lead.1 ∧ Chain K.Edge lead.1 lead.2 x

/-- The local check of one witness for declaration `d`. -/
def Census.EvidenceOk (K : Census M D C F) (d : D) : Evidence D C F → Prop
  | .keep c e path =>
      c ∈ K.consumers ∧ (K.kind c).primary ∧ (c, e) ∈ K.roots ∧ Chain K.Edge e path d
  | .ownerNeeded f via s path S =>
      K.Seed f via s ∧ Chain K.Edge s path d ∧ K.Closed ConsumerKind.primary S ∧ d ∉ S
  | .orphan S =>
      K.Closed ConsumerKind.demands S ∧
      (∀ s ∈ K.decls, K.role (K.declModule s) ≠ .member → s ∈ S) ∧ d ∉ S
  | .unresolved g lead path S =>
      g ∈ K.gaps ∧ K.GapSourceLive g lead ∧
      (g.target = none ∨ ∃ y, g.target = some y ∧ Chain K.PossStep y path d) ∧
      K.RecClosed ConsumerKind.primary S ∧ d ∉ S

/-- A listed declaration of family `f` whose certified verdict is `v`. -/
def Certificate.Has (X : Certificate D C F) (K : Census M D C F) (f : F) (v : Verdict) :
    Prop :=
  ∃ d ∈ K.decls, K.family (K.declModule d) = f ∧ (X.entry d).evidence.verdict = v

/-- A family's verdict is determined by its members' verdicts, so member-level evidence
is never replaced: any keep member makes it keep; otherwise an unresolved member, or no
declarations at all, makes it unresolved. -/
def Census.FamilyOk (K : Census M D C F) (X : Certificate D C F) (f : F) : Verdict → Prop
  | .keep => X.Has K f .keep
  | .unresolved => ¬ X.Has K f .keep ∧
      (X.Has K f .unresolved ∨ ¬ ∃ d ∈ K.decls, K.family (K.declModule d) = f)
  | .ownerNeeded => ¬ X.Has K f .keep ∧ ¬ X.Has K f .unresolved ∧ X.Has K f .ownerNeeded
  | .orphan => (∃ d ∈ K.decls, K.family (K.declModule d) = f) ∧
      ∀ d ∈ K.decls, K.family (K.declModule d) = f → (X.entry d).evidence.verdict = .orphan

/-- Locally checkable obligations of a census and certificate. -/
def Census.Valid (K : Census M D C F) (X : Certificate D C F) : Prop :=
  (∀ m ∈ K.modules, K.family m ∈ K.families) ∧
  (∀ f ∈ K.families, ∃ m ∈ K.modules, K.family m = f) ∧
  (∀ m ∈ K.modules, ∀ m' ∈ K.modules, K.family m = K.family m' → K.area m = K.area m') ∧
  (∀ d ∈ K.decls, K.declModule d ∈ K.modules) ∧
  (∀ r ∈ K.roots, r.1 ∈ K.consumers) ∧
  (∀ g ∈ K.gaps, g.reason ≠ "" ∧
    match g.source with | .root (some c) => c ∈ K.consumers | _ => True) ∧
  (∀ d ∈ K.decls, (X.entry d).reason ≠ "" ∧ K.EvidenceOk d (X.entry d).evidence) ∧
  (∀ f ∈ K.families, K.FamilyOk X f (X.family f)) ∧
  K.lineBasis ≠ "" ∧
  (∀ m ∈ K.modules, (K.checkTime m).Recorded) ∧
  ∀ f ∈ K.families, (K.pin f).revision ≠ "" ∧
    ∀ m ∈ K.modules, K.family m = f → m ∈ (K.pin f).modules

/-- Input adequacy, assumed rather than proved: module and declaration coverage,
consumer kinds, root coverage and dependency-edge adequacy, where every unrecorded
actual use or non-blanket root must be covered by a listed gap. -/
def Adequate (W : World M D C F) (K : Census M D C F) : Prop :=
  (∀ m, W.InScope m ↔ m ∈ K.modules) ∧
  (∀ m ∈ K.modules, W.area m = some (K.area m) ∧ W.family m = K.family m ∧
    W.role m = K.role m) ∧
  (∀ d, W.InScope (W.moduleOf d) → d ∈ K.decls) ∧
  (∀ d ∈ K.decls, K.declModule d = W.moduleOf d) ∧
  (∀ c ∈ K.consumers, K.kind c = W.kind c) ∧
  (∀ c d, (c, d) ∈ K.roots → W.rootUse c d) ∧
  (∀ c d, W.rootUse c d → W.kind c ≠ .blanket →
    (c ∈ K.consumers ∧ (c, d) ∈ K.roots) ∨ ∃ g ∈ K.gaps, Census.CoversRoot g c d) ∧
  (∀ x y, K.Edge x y → W.uses x y) ∧
  ∀ x y, W.uses x y → K.Edge x y ∨ ∃ g ∈ K.gaps, Census.CoversUse g x y

/-- What a certified declaration means in the world. -/
def Meaning (W : World M D C F) (K : Census M D C F) (d : D) : Evidence D C F → Prop
  | .keep .. => W.IndepReach d
  | .ownerNeeded f .. => ¬ W.IndepReach d ∧ W.DemandBy f d
  | .orphan .. => ¬ W.IndepReach d ∧ ¬ W.ControlDemand d
  | .unresolved g lead .. => g ∈ K.gaps ∧ K.GapSourceLive g lead ∧ ¬ K.RecordedKeep d

/-- The conclusions: per-declaration meaning, no unresolved verdict without a gap,
family verdicts that cannot hide an independently reachable member, and complete
metadata records for every in-scope module. -/
def Sound (W : World M D C F) (K : Census M D C F) (X : Certificate D C F) : Prop :=
  (∀ d, W.InScope (W.moduleOf d) → Meaning W K d (X.entry d).evidence) ∧
  (K.gaps = [] → ∀ d, W.InScope (W.moduleOf d) →
    (X.entry d).evidence.verdict ≠ .unresolved) ∧
  (∀ f ∈ K.families,
    (X.family f = .keep → ∃ d, W.Member f d ∧ W.IndepReach d) ∧
    (X.family f = .ownerNeeded →
      (∀ d, W.Member f d → ¬ W.IndepReach d) ∧
      ∃ d, W.Member f d ∧ W.ControlDemand d) ∧
    (X.family f = .orphan → (∃ d, W.Member f d) ∧
      ∀ d, W.Member f d → ¬ W.IndepReach d ∧ ¬ W.ControlDemand d) ∧
    (X.family f = .unresolved → K.gaps ≠ [] ∨ ¬ ∃ d, W.Member f d) ∧
    ∀ d, W.Member f d → W.IndepReach d →
      X.family f = .keep ∨ X.family f = .unresolved) ∧
  ∀ m, W.InScope m → m ∈ K.modules ∧ K.family m ∈ K.families ∧ K.lineBasis ≠ "" ∧
    (K.checkTime m).Recorded ∧ m ∈ (K.pin (K.family m)).modules

/-- Boundary cases a satisfying instance must show at once: all seven areas, a keep
member in a family with a non-keep member, an own-controls cycle whose family stays
owner-needed and is also used by an `ownControls` consumer, an orphan family with a
cycle reached by a blanket consumer, an unresolved declaration behind a gap, and
both a measured and an unavailable check time. -/
def Exhibits (K : Census M D C F) (X : Certificate D C F) : Prop :=
  (∀ a ∈ Area.all, ∃ m ∈ K.modules, K.area m = a) ∧
  (∃ d ∈ K.decls, ∃ d' ∈ K.decls, K.family (K.declModule d) = K.family (K.declModule d') ∧
    (X.entry d).evidence.verdict = .keep ∧ (X.entry d').evidence.verdict ≠ .keep) ∧
  (∃ x ∈ K.decls, ∃ y ∈ K.decls, K.family (K.declModule x) = K.family (K.declModule y) ∧
    K.role (K.declModule x) = .member ∧ K.role (K.declModule y) ≠ .member ∧
    K.Edge x y ∧ K.Edge y x ∧ (X.entry x).evidence.owner = some (K.family (K.declModule x)) ∧
    X.family (K.family (K.declModule x)) = .ownerNeeded ∧
    ∃ r ∈ K.roots, K.kind r.1 = .ownControls ∧
      K.family (K.declModule r.2) = K.family (K.declModule x)) ∧
  (∃ x ∈ K.decls, ∃ y ∈ K.decls, x ≠ y ∧ K.Edge x y ∧ K.Edge y x ∧
    (X.entry x).evidence.verdict = .orphan ∧ (X.entry y).evidence.verdict = .orphan ∧
    X.family (K.family (K.declModule x)) = .orphan ∧
    ∃ c ∈ K.consumers, K.kind c = .blanket ∧ (c, x) ∈ K.roots) ∧
  (∃ d ∈ K.decls, (X.entry d).evidence.verdict = .unresolved) ∧
  (∃ m ∈ K.modules, (K.checkTime m).isMeasured) ∧
  ∃ m ∈ K.modules, !(K.checkTime m).isMeasured

end Inventory

/-- The inventory contract: every valid certificate over adequate inputs is sound,
and the obligations are jointly satisfiable with every verdict and boundary case. -/
@[goal Solidity.LeanInventory.inventory_sound "k1-lean-inventory"]
def leanInventorySound : Prop :=
  (∀ (M D C F : Type) (W : Inventory.World M D C F) (K : Inventory.Census M D C F)
      (X : Inventory.Certificate D C F),
    Inventory.Adequate W K → K.Valid X → Inventory.Sound W K X) ∧
  ∃ (M D C F : Type) (W : Inventory.World M D C F) (K : Inventory.Census M D C F)
      (X : Inventory.Certificate D C F),
    Inventory.Adequate W K ∧ K.Valid X ∧ Inventory.Exhibits K X

/-! Accepted Yul language for the producer Artifact obligation (plan step
y1-yul-artifact-producers). Three separate layers:

* `YulArtifact.Accepted`: syntax only. Closed statements (`Stmt [] []`, any
  control `c`, any local count `n`) built from `skip`, `seq` and single-target
  assignment whose right side is built from literals, locals and
  `add`/`sub`/`mul`. Nesting and composition are arbitrary. These are exactly the
  constructors `ProducerStatements.compile` and `ProducerExpressions.compile`
  visit; any other constructor (`discard`, `let`, `zero`, `if`, `switch`, `for`,
  multi-target assignment, other builtins, early control, function groups) is
  outside this language, not a certificate failure. Calls and externals cannot
  occur in a closed statement.
* `YulArtifact.Fits depth`: the representation limit of the emitted code. Local
  reads use DUP and writes use SWAP, whose Backend index is `Fin 16`; a read at
  stack height `h` above the locals (counting the `depth` newer words) needs `h + i < 16`, and a
  write needs `depth + i < 16` (`lowerLocal`, `lowerAssign`, `lowerBinary`).
  Syntactic: computed from the program and the depth, never from success.
* The goal: the producer must succeed on every accepted program, its emission at
  every fitting depth must select into `Evm.Instr` through the existing word
  selector (stack, `ADD`, `SUB`, `MUL` and more), and exactly that code must
  carry an `Artifact` for the same statement, with both directions as defined. -/
namespace YulArtifact

open Solidity.Yul

/-- The binary operators the expression producer visits. -/
def Binary (op : Yul.Pure 2) : Prop := op = .add ∨ op = .sub ∨ op = .mul

/-- Accepted right-hand sides: literals, locals and arbitrarily nested binaries. -/
inductive AcceptedExpr {n : Nat} : Yul.Expr [] [] n 1 → Prop
  | literal (w : Yul.Word) : AcceptedExpr (.literal w)
  | «local» (i : Fin n) : AcceptedExpr (.local i)
  | binary {op : Yul.Pure 2} {args : Fin 2 → Yul.Expr [] [] n 1} (selected : Binary op)
      (left : AcceptedExpr (args 0)) (right : AcceptedExpr (args 1)) :
      AcceptedExpr (.builtin (.pure op) args)

/-- Accepted statements. In a closed program every target is a local. -/
inductive Accepted {c : Yul.Control} {n : Nat} : Yul.Stmt [] [] c n → Prop
  | skip : Accepted .skip
  | seq {a b : Yul.Stmt [] [] c n} (first : Accepted a) (second : Accepted b) :
      Accepted (.seq a b)
  | assign (targets : Fin 1 → Yul.Target [] n) {expr : Yul.Expr [] [] n 1}
      (value : AcceptedExpr expr) : Accepted (.assign targets expr)

/-- DUP reach of an expression evaluated `height` words above the locals. The
right operand runs first; the left one runs one word deeper. -/
inductive ExprFits {n : Nat} : Nat → Yul.Expr [] [] n 1 → Prop
  | literal (height : Nat) (w : Yul.Word) : ExprFits height (.literal w)
  | «local» {height : Nat} (i : Fin n) (reach : height + i.val < 16) :
      ExprFits height (.local i)
  | builtin {height : Nat} {b : Yul.Builtin 2 1} {args : Fin 2 → Yul.Expr [] [] n 1}
      (right : ExprFits height (args 1)) (left : ExprFits (1 + height) (args 0)) :
      ExprFits height (.builtin b args)

/-- DUP/SWAP reach of a statement run under `depth` newer words. -/
inductive Fits {c : Yul.Control} {n : Nat} : Nat → Yul.Stmt [] [] c n → Prop
  | skip (depth : Nat) : Fits depth .skip
  | seq {depth : Nat} {a b : Yul.Stmt [] [] c n} (first : Fits depth a) (second : Fits depth b) :
      Fits depth (.seq a b)
  | assign {depth : Nat} (targets : Fin 1 → Yul.Target [] n) {expr : Yul.Expr [] [] n 1}
      (reach : ∀ i : Fin n, targets 0 = .local i → depth + i.val < 16)
      (value : ExprFits depth expr) : Fits depth (.assign targets expr)

end YulArtifact

/-- Every accepted program compiles: the producer succeeds at some fuel. For every
successful compilation and every fitting newer-prefix depth, the lowered program
is emitted, the word selector translates it, and an `Artifact` for the same
statement has exactly that code. The `Artifact` fields keep every source horizon
forward, an existential horizon backward, arbitrary machine and caller frames,
the newer prefix and exact final machine and skip observations. -/
@[goal Solidity.Yul.accepted_compiles_with_artifact "y1-yul-artifact-producers"]
def yulAcceptedCompilesWithArtifact : Prop :=
  ∀ {c : Yul.Control} {n : Nat} (stmt : Yul.Stmt [] [] c n), YulArtifact.Accepted stmt →
    (∃ fuel, (Yul.Compilation.ProducerStatements.compile fuel stmt).isSome) ∧
    ∀ (fuel : Nat) (compiled : Yul.Compilation.ProducerStatements.Compiled fuel stmt),
      Yul.Compilation.ProducerStatements.compile fuel stmt = some compiled →
      ∀ depth : Nat, YulArtifact.Fits depth stmt →
      ∃ (p : Backend.Program) (code : List Evm.Instr),
        compiled.lowered.code depth = some p ∧
        Yul.Compilation.WordMachine.selectCode p = some code ∧
        ∃ artifact : Yul.Compilation.Artifact depth stmt, artifact.code = code

/-! Concrete intrinsic session semantics (plan step is0-intrinsic-session). The
obligation is a concrete `Roadmap.IntrinsicSpec` whose worlds are read as actual
typed contract worlds (`ContractWorld.World` over a catalog of `Contract`s, with
the `Prog`s it runs) and whose sessions are tied, boundary by boundary, to the
existing frame semantics:

* `View.Boundary x en h n t`: the session of world `x` in `en` stands at a
  transaction boundary after exactly the history `h`, with `n` actions issued, in
  the typed world `t`. Boundaries are observed at bounds without resource failure,
  and every listed world is one;
* at a boundary, a deployment or transaction whose body never leaves its contract
  (`Prog.callsBack true = false`, and no response table changes its result) is
  exactly `World.transact` of `World.create` / `World.call`: the logical
  `Prog.run`, with no fuel in the statement. Exhaustion and divergence yield no
  event at a bound without resource failure (`ContractWorld.catchable`), and a
  completed run is observed at some such bound;
* dropped requests (`Funded`, the reading of `Lang.Affordable` at the boundary's
  history), credits, the end of the session, the callee strategy's moves,
  `Forward`, `Guard` and the environment maps are those of `Roadmap/Contracts.lean`.

Not determined by the typed definitions this reads, and therefore not chosen
here: how the strategy's answers reach a body that leaves its contract (`TTx.ext`
is a table, a strategy reads the history) and every event of such a body past the
move after a call; the revert data of a `THalt.panic` (it carries no code); the
data of a successful deployment; what follows a reverted deployment or a credit
whose sum is not a word; deployments and requests the code does not resolve;
a request or deployment whose value the sender's funds in the world do not cover
(the frame reverts there, the ledger may call it affordable); the final
observation of a session without outcomes; whether the world after a deployment
or a credit is listed; bounds with resource failures, beyond an upper bound on
the outcome a determined first step shows there (its own, or a revert with empty
data: no failing bound is required to exist); environments that are not allowed;
and the preimages a run hashes and the slot preimages of the keys a typed
storage holds (`View.stored` is only required to be accounted for, so this goal
does not pin `Forward` and `Guard` beyond their definitions). Within a determined
step the frame's own accounting is the typed world's: global funds, debited from
the sender on success. `Lang.Affordable` over a whole history is not required:
`Fixed.ledger` is an arbitrary function and the history of a transaction includes
its inner events. -/
namespace IntrinsicSession

open Solidity.Roadmap
open Solidity.Lowering.V08.EnvironmentProjection
  (liftWord lowerWord liftAddress lowerAddress requestContext)

/-- The code of a compilation: its contracts by position (as `Artifact.contracts`
and `Event.create` number them), the selected one, their roles, and the programs a
deployment or a request runs. `ctor` and `entry` resolve constructor arguments and
calldata to actual typed programs; an entry's `result` gives its return data. -/
structure Code where
  contracts : List Contract
  main : Nat
  roles : Fin contracts.length → ContractWorld.Role
  ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] [])
  entry : (k : Fin contracts.length) → Bytes → Option (ContractWorld.Entry contracts[k] Bytes)

/-- The catalog `ContractWorld` indexes instances by. -/
abbrev Code.catalog (c : Code) (k : Fin c.contracts.length) : Contract := c.contracts[k]

/-- An actual typed contract world together with its code. -/
structure TypedWorld where
  code : Code
  world : ContractWorld.World code.catalog

/-- Session opening balances as a world's global funds. -/
def funds (b : Address → Roadmap.Word) : ContractWorld.Address → ContractWorld.Word :=
  fun a => liftWord (b (lowerAddress a))

/-- Two worlds agree at a transaction boundary: instances and storage up to the
transaction-local cells, funds and roles. The timestamp is each request's own. -/
def Same {K : Type} {contracts : K → Contract} (a b : ContractWorld.World contracts) : Prop :=
  a.resetTransient.accounts = b.resetTransient.accounts ∧ a.funds = b.funds ∧ a.roles = b.roles

/-- `t` is the world `w` of `code`, at a transaction boundary. -/
def TypedWorld.Shows (t : TypedWorld) (code : Code) (w : ContractWorld.World code.catalog) :
    Prop :=
  ∃ w' : ContractWorld.World code.catalog, t = ⟨code, w'⟩ ∧ Same w' w

/-- `b` is `a` with the funds of `target` set to `sum`, and nothing else changed. -/
def Credited {K : Type} {contracts : K → Contract} (a : ContractWorld.World contracts)
    (target : ContractWorld.Address) (sum : ContractWorld.Word)
    (b : ContractWorld.World contracts) : Prop :=
  a.resetTransient.accounts = b.resetTransient.accounts ∧ a.roles = b.roles ∧
  (∀ x, x ≠ target → b.funds x = a.funds x) ∧ b.funds target = sum

/-- The request is affordable after the history `h` (`Lang.Affordable`, on the
ledger over the opening balances); otherwise it is dropped. -/
def Funded (F : Fixed) (e : SessionEnv) (h : List Event) (q : Request) : Prop :=
  q.value.val ≤ (F.ledger e.balance h q.sender).val

/-- A frame result that completed: a return, or a failure a caller can observe.
Divergence and exhaustion are not completions. -/
def Ends {α : Type} : TRes α → Prop
  | .ok _ => True
  | .error h => ContractWorld.catchable h = true

/-- A completed failure as an outcome: a revert with the halt's data. A panic's
data is not read off `THalt.panic`, which carries no code. -/
def RevertMatches (h : THalt) (out : Outcome) : Prop :=
  ContractWorld.catchable h = true ∧ ∃ d, out = .revert d ∧ (h ≠ .panic → d = h.data)

/-- A transaction's frame result as its outcome. -/
def Matches : TRes Bytes → Outcome → Prop
  | .ok d, out => out = .success d
  | .error h, out => RevertMatches h out

/-- The outcomes of the completed deployments and transactions of a history. -/
def outcomes (h : List Event) : List Outcome :=
  h.filterMap fun
    | .deploy _ _ _ o _ => some o
    | .tx _ _ _ _ _ o => some o
    | _ => none

/-- A completed transaction. -/
def IsTx : Event → Prop
  | .tx .. => True
  | _ => False

/-- The event a move of the callee strategy shows. -/
def Moved : Move → Event → Prop
  | .answer o, x => ∃ created, x = .answer o created
  | .reenter t s v i st, x => x = .reenter t s v i st
  | .credit t v, x => x = .credit t v

/-- How a candidate's worlds are typed worlds: the typed world of each world, the
world a compilation starts from (nothing deployed), the world resumed at a typed
world, the slot preimages of the keys a typed world stores, and the transaction
boundaries of a session (history, actions issued, typed world). -/
structure View (I : IntrinsicSpec) where
  typed : I.World → TypedWorld
  initial : Code → I.World
  resume : TypedWorld → I.World
  stored : TypedWorld → List Bytes
  Boundary : I.World → I.lang.Env → List Event → Nat → TypedWorld → Prop

/-- A bound the laws speak of: admissible and without resource failure. -/
def Good (I : IntrinsicSpec) (r : I.lang.Res) : Prop := I.lang.Admissible r ∧ I.NoFail r

/-- The history is observed at some bound without resource failure. -/
def Observed (I : IntrinsicSpec) (p : I.lang.Prog) (en : I.lang.Env) (h : List Event) : Prop :=
  ∃ r, Good I r ∧ h <+: (I.lang.sem p en r).events

/-- The laws of the concrete intrinsic session semantics `I`, read through `V`,
over the fixed parameters `F`. -/
structure Laws (F : Fixed) (I : IntrinsicSpec) (V : View I) : Prop where
  /-- The fixed parameters are the given ones. -/
  fixed : I.fixed = F
  /-- The shared readings of every layer's events. -/
  precompiles : I.lang.PrecompilesFixed
  this : I.lang.ThisFromDeployment F I.session
  /-- Bounds without resource failure have common upper bounds, so the
  consistency of the prefixes relates any two of them. -/
  directed : ∀ r r', Good I r → Good I r' →
    ∃ r'', Good I r'' ∧ I.lang.resLE.le r r'' ∧ I.lang.resLE.le r' r''
  /-- Larger bounds extend the listed worlds and the preimages. -/
  worlds_consistent : ∀ p e r r', I.lang.resLE.le r r' → I.worlds p e r <+: I.worlds p e r'
  hashed_consistent : ∀ p e r r', I.lang.resLE.le r r' → I.hashed p e r <+: I.hashed p e r'
  slotHashed_sub : ∀ p e r b, b ∈ I.slotHashed p e r → b ∈ I.hashed p e r
  /-- A final observation is the last completed outcome. -/
  final_last : ∀ p e r o, (I.lang.sem p e r).final = some o →
    outcomes (I.lang.sem p e r).events = [] ∨
      (outcomes (I.lang.sem p e r).events).getLast? = some o
  /-- The event after a call to the environment is the strategy's move there. -/
  answered : ∀ p en r h callee value input static x, I.lang.Allowed en → Good I r →
    h ++ [Event.call callee value input static, x] <+: (I.lang.sem p en r).events →
    Moved ((I.session en).callee (h ++ [Event.call callee value input static])) x
  /-- Worlds keep their code. -/
  typed_resume : ∀ t, V.typed (V.resume t) = t
  initial_code : ∀ c, (V.typed (V.initial c)).code = c
  worlds_code : ∀ x e r, ∀ ω ∈ I.worlds (I.ofWorld x) e r,
    (V.typed ω).code = (V.typed x).code
  /-- A listed world runs as the world resumed at its typed world. -/
  listed_resumes : ∀ x e r, ∀ ω ∈ I.worlds (I.ofWorld x) e r,
    let p := I.ofWorld ω
    let p' := I.ofWorld (V.resume (V.typed ω))
    I.lang.sem p = I.lang.sem p' ∧ I.worlds p = I.worlds p' ∧ I.hashed p = I.hashed p' ∧
      I.slotHashed p = I.slotHashed p'
  /-- A run resumed from a world accounts for the keys the world stores. -/
  stored_hashed : ∀ t e r, ∀ b ∈ V.stored t, b ∈ I.slotHashed (I.ofWorld (V.resume t)) e r
  /-- A session resumed at a typed world starts at that world. -/
  starts : ∀ (t : TypedWorld) (en : I.lang.Env), I.lang.Allowed en →
    V.Boundary (V.resume t) en [] 0 t
  /-- A boundary's history is observed, and its world has the session's code. -/
  boundary_observed : ∀ x en h n t, V.Boundary x en h n t → Observed I (I.ofWorld x) en h
  boundary_code : ∀ x en h n t, V.Boundary x en h n t → t.code = (V.typed x).code
  /-- Every listed world is the world of a boundary the prefix has reached. -/
  listed_boundary : ∀ x en r, Good I r → ∀ ω ∈ I.worlds (I.ofWorld x) en r,
    ∃ h n, V.Boundary x en h n (V.typed ω) ∧ h <+: (I.lang.sem (I.ofWorld x) en r).events
  /-- No further action: the history is complete, and the session completes once
  it has an outcome. -/
  idle : ∀ x en h n t, I.lang.Allowed en → V.Boundary x en h n t →
    (I.session en).requests h n = none →
    (∀ r, Good I r → h <+: (I.lang.sem (I.ofWorld x) en r).events →
      (I.lang.sem (I.ofWorld x) en r).events = h) ∧
    (outcomes h ≠ [] → ∃ r, Good I r ∧ (I.lang.sem (I.ofWorld x) en r).events = h ∧
      (I.lang.sem (I.ofWorld x) en r).final ≠ none)
  /-- An unaffordable request is dropped: the next action, same history and world. -/
  dropped : ∀ x en h n t (q : Request), I.lang.Allowed en → V.Boundary x en h n t →
    (I.session en).requests h n = some (.request q) → ¬ Funded F (I.session en) h q →
    V.Boundary x en h (n + 1) t
  /-- A credit is the next event; when the sum is a word, the boundary after it
  has the target's global funds raised and nothing else changed. -/
  credited : ∀ x en h n (code : Code) (cw : ContractWorld.World code.catalog)
      (target : Address) (value : Roadmap.Word),
    I.lang.Allowed en → V.Boundary x en h n ⟨code, cw⟩ →
    (I.session en).requests h n = some (.credit target value) →
    let p := I.ofWorld x
    let done := Event.credit target value
    Observed I p en (h ++ [done]) ∧
    (∀ r, Good I r → h <+: (I.lang.sem p en r).events →
      (I.lang.sem p en r).events = h ∨ h ++ [done] <+: (I.lang.sem p en r).events) ∧
    ∀ sum, PrimTy.ofInt? .uint ((cw.funds (liftAddress target)).1 + (liftWord value).1) =
        some sum →
      ∃ cw' : ContractWorld.World code.catalog, Credited cw (liftAddress target) sum cw' ∧
        V.Boundary x en (h ++ [done]) (n + 1) ⟨code, cw'⟩
  /-- **A transaction that never leaves its contract is the actual frame**: at a
  boundary, an affordable request, covered by its sender's funds in the world, to an
  instance whose code resolves its input to a body without external interaction,
  whose result no response table changes, is
  the next event exactly when `World.transact` of the actual `World.call`
  completes, with that outcome; the world it reaches is listed and is the next
  boundary. As the first event of a session, at any admissible bound (resource
  failures included), its outcome if shown is that one or a revert with empty
  data; past the first step a failing bound may have reached another world. -/
  transacts : ∀ x en h n (code : Code) (cw : ContractWorld.World code.catalog)
      (q : Request) (k : Fin code.contracts.length) (st : Storage (code.catalog k))
      (entry : ContractWorld.Entry (code.catalog k) Bytes),
    I.lang.Allowed en → V.Boundary x en h n ⟨code, cw⟩ →
    (I.session en).requests h n = some (.request q) → Funded F (I.session en) h q →
    cw.accounts (liftAddress q.target) = some ⟨k, st⟩ → code.entry k q.input = some entry →
    Prog.callsBack true entry.body = false →
    (liftWord q.value).1 ≤ (cw.funds (liftAddress q.sender)).1 →
    let p := I.ofWorld x
    let frame := fun ext => (cw.atTime (liftWord q.timestamp)).transact fun w =>
      w.call (⟨liftAddress q.target⟩ : ContractWorld.Handle k) entry (requestContext q ext)
    let res := frame []
    (∀ ext, frame ext = res) →
    (Ends res.2 → ∃ out, Observed I p en
      (h ++ [Event.tx q.sender q.target q.value q.timestamp q.input out])) ∧
    (∀ r, Good I r → h <+: (I.lang.sem p en r).events →
      (I.lang.sem p en r).events = h ∨ ∃ out,
        let done := Event.tx q.sender q.target q.value q.timestamp q.input out
        h ++ [done] <+: (I.lang.sem p en r).events ∧ Matches res.2 out ∧
        ∃ ω ∈ I.worlds p en r, (V.typed ω).Shows code res.1 ∧
          V.Boundary x en (h ++ [done]) (n + 1) (V.typed ω)) ∧
    ∀ r, I.lang.Admissible r → h = [] → ∀ out,
      [Event.tx q.sender q.target q.value q.timestamp q.input out] <+:
        (I.lang.sem p en r).events →
      Matches res.2 out ∨ out = .revert []
  /-- Every completed transaction of an affordable request, whatever its body
  does, is that request's, and reaches a listed world that is the next boundary. -/
  resumes : ∀ x en h n t (q : Request), I.lang.Allowed en → V.Boundary x en h n t →
    (I.session en).requests h n = some (.request q) → Funded F (I.session en) h q →
    let p := I.ofWorld x
    ∀ r, Good I r → ∀ (seg : List Event) (ev : Event), IsTx ev →
      (∀ y ∈ seg, ¬ IsTx y) → h ++ seg ++ [ev] <+: (I.lang.sem p en r).events →
      (∃ out, ev = Event.tx q.sender q.target q.value q.timestamp q.input out) ∧
      ∃ ω ∈ I.worlds p en r, V.Boundary x en (h ++ seg ++ [ev]) (n + 1) (V.typed ω)
  /-- **A deployment that never leaves its contract is the actual creation**: from
  the initial world of a compilation, funded by the opening balances, the selected
  contract's constructor, under the same conditions and with the deployment value
  covered by a deployer other than the new address, runs as `World.transact` of
  the actual `World.create` at the address `Fixed.createAddress` gives; it is the
  first event exactly when that completes, and on success the world it installs is
  the first boundary. At any admissible bound (resource failures included) its
  outcome if shown is that one or a revert with empty data and no address. -/
  deploys : ∀ (code : Code) (en : I.lang.Env) (k : Fin code.contracts.length)
      (body : Prog (code.catalog k) [] []),
    I.lang.Allowed en → k.val = code.main →
    code.ctor k (I.session en).deployArgs = some body → Prog.callsBack true body = false →
    let e := I.session en
    let p := I.ofWorld (V.initial code)
    let this := F.createAddress e.deployer e.deployNonce
    e.deployValue.val ≤ (e.balance e.deployer).val → this ≠ e.deployer →
    let frame := fun ext =>
      (ContractWorld.World.empty code.catalog (funds e.balance) code.roles).transact fun w =>
        w.create k (liftAddress this) body
          { sender := liftAddress e.deployer, mode := .ordinary (liftWord e.deployValue),
            ext := ext }
    let res := frame []
    (∀ ext, frame ext = res) →
    (Ends res.2 → ∃ out address, Observed I p en
      [Event.deploy e.deployer e.deployValue e.deployArgs out address]) ∧
    (∀ r, Good I r → (I.lang.sem p en r).events ≠ [] → ∃ out address,
      let done := Event.deploy e.deployer e.deployValue e.deployArgs out address
      [done] <+: (I.lang.sem p en r).events ∧
      match res.2 with
      | .ok _ => (∃ d, out = .success d) ∧ address = some this ∧
        ∃ t', t'.Shows code res.1 ∧ V.Boundary (V.initial code) en [done] 0 t'
      | .error h => RevertMatches h out ∧ address = none) ∧
    ∀ r, I.lang.Admissible r → ∀ out address,
      [Event.deploy e.deployer e.deployValue e.deployArgs out address] <+:
        (I.lang.sem p en r).events →
      (out = .revert [] ∧ address = none) ∨
      match res.2 with
      | .ok _ => (∃ d, out = .success d) ∧ address = some this
      | .error h => RevertMatches h out ∧ address = none

end IntrinsicSession

/-- For every fixed parameters there is a concrete intrinsic session semantics: an
`IntrinsicSpec` (exact session environment, pinned `Forward` and `Guard`, consistent
prefixes, by its type) whose worlds are actual typed contract worlds and whose
sessions satisfy `IntrinsicSession.Laws`. -/
@[goal Solidity.Semantics.IntrinsicSession.session_semantics_correct "is0-intrinsic-session"]
def intrinsicSessionSemantics : Prop :=
  ∀ F : Solidity.Roadmap.Fixed, ∃ (I : Solidity.Roadmap.IntrinsicSpec)
    (V : IntrinsicSession.View I), IntrinsicSession.Laws F I V

/-! Code-relative prose ratchet (plan step pb2-prose-ratio-rule). Each area `a` and
prose category `k` may carry at most `r * C + m` prose lines (process-id tokens),
where `C` counts the
area's eligible code lines and the allowance `(r, m)` comes from a frozen policy.

* `Scope` and `Entries` form the trusted policy, frozen before the candidate is
  measured: the area mapping, the generated-file list, the per-path kind and the
  ratio and margin per area and category. `Tree` is the measured candidate. `accepts`
  takes both separately, so nothing in the tree (a policy file included) can supply
  or raise the policy; a candidate's proposed entries enter only through `shrink`.
* A ratio is `num / den` with `0 < den`, compared by value through cross
  multiplication; the margin counts whole lines. `Allowance.lines` rounds the ratio
  part down, and `accepts` decides the cross-multiplied form without division.
* Eligible code is lexical: a Lean line counts once when some code segment outside
  comments holds a non-blank character. Comments, docstrings and process ids are
  prose categories and never make a line code. Docs files contribute their lines as
  `docs` prose and no code. Generated files, `docs/audits` (until
  r1-regen-out-of-git, through its own `Exclusion` constructor) and `outside` paths
  contribute neither. A docs area holds no code, so its bound is its margin alone.
* A missing entry is the zero allowance, never an unbounded one.

Boundary: a proof of `proseRatioRuleSound` certifies only this arithmetic over
classified lines. The lexer producing `Segment`s, the Python checker, Git
provenance of the frozen policy (its generated list and path kinds included), the
check that generated files equal their generator's output, the process-id exemption
for registered module names, Unicode blankness in the lexer, the history-calibrated
ratios and margins, and CI on the merged head remain separate obligations. A line
count says nothing about the usefulness of added code, and splitting existing code
over more lines raises `C`. -/
namespace ProseRatio

/-- A repository path by components, e.g. `["docs", "audits", "x.md"]`. -/
abbrev Path := List String

/-- The four existing prose metrics of `scripts/check-prose-budget`; as there, a
docstring line is also a comment line. -/
inductive Category where
  | docs | comment | docstring | processId
deriving DecidableEq

def Category.all : List Category := [.docs, .comment, .docstring, .processId]

/-- A lexical piece of a Lean line; comment and docstring delimiters belong to their
segment, and a process-id token is split out wherever it occurs. -/
inductive Segment where
  | code (text : String)
  | comment (text : String)
  | docstring (text : String)
  | processId (token : String)

abbrev Line := List Segment

def nonblank (s : String) : Bool := s.toList.any fun c => !c.isWhitespace

def Segment.isCode : Segment → Bool
  | .code s => nonblank s
  | _ => false

def Segment.isComment : Segment → Bool
  | .comment _ => true
  | _ => false

def Segment.isDocstring : Segment → Bool
  | .docstring _ => true
  | _ => false

def Segment.isProcessId : Segment → Bool
  | .processId _ => true
  | _ => false

/-- Eligible code: some non-blank code outside comments. Blank, comment-only,
docstring-only and process-id-only lines are not code. -/
def Line.hasCode (l : Line) : Bool := l.any Segment.isCode

def Line.code (l : Line) : Nat := if l.hasCode then 1 else 0

/-- Prose a Lean line carries in category `k`; a mixed line counts as code and as
prose. -/
def Line.prose (l : Line) : Category → Nat
  | .docs => 0
  | .comment => if l.any fun s => s.isComment || s.isDocstring then 1 else 0
  | .docstring => if l.any Segment.isDocstring then 1 else 0
  | .processId => (l.filter Segment.isProcessId).length

/-- Why a path contributes nothing. `auditsUntilRegen` is temporary: removing the
`docs/audits` exclusion deletes this constructor and so visibly changes this goal. -/
inductive Exclusion where
  | generated | auditsUntilRegen
deriving DecidableEq

/-- How the frozen policy reads a path that is neither generated nor under
`docs/audits`. -/
inductive Kind where
  | source | docs | outside
deriving DecidableEq

inductive Treatment where
  | source | docs | outside | excluded (why : Exclusion)
deriving DecidableEq

def Treatment.counted : Treatment → Bool
  | .source | .docs => true
  | _ => false

def InAudits (p : Path) : Bool := p.take 2 == ["docs", "audits"]

/-- The frozen classification half of the policy. -/
structure Scope (A : Type) where
  area : Path → A
  generated : List Path
  kind : Path → Kind

def Scope.treat {A : Type} (s : Scope A) (p : Path) : Treatment :=
  if p ∈ s.generated then .excluded .generated
  else if InAudits p then .excluded .auditsUntilRegen
  else match s.kind p with
    | .source => .source
    | .docs => .docs
    | .outside => .outside

/-- A nonnegative rational ratio `num / den`. -/
structure Ratio where
  num : Nat
  den : Nat
  den_pos : 0 < den

/-- By value, not by numerator. -/
def Ratio.le (r s : Ratio) : Prop := r.num * s.den ≤ s.num * r.den

instance (r s : Ratio) : Decidable (r.le s) := inferInstanceAs (Decidable (_ ≤ _))

def Ratio.min (r s : Ratio) : Ratio := if r.le s then r else s

structure Allowance where
  ratio : Ratio
  margin : Nat

def Allowance.zero : Allowance := ⟨⟨0, 1, Nat.one_pos⟩, 0⟩

def Allowance.le (w v : Allowance) : Prop := w.ratio.le v.ratio ∧ w.margin ≤ v.margin

def Allowance.Equiv (w v : Allowance) : Prop := w.le v ∧ v.le w

def Allowance.min (w v : Allowance) : Allowance := ⟨w.ratio.min v.ratio, Nat.min w.margin v.margin⟩

/-- Whole prose lines allowed beside `C` code lines: `⌊num * C / den⌋ + margin`. -/
def Allowance.lines (w : Allowance) (C : Nat) : Nat := w.ratio.num * C / w.ratio.den + w.margin

/-- The cross-multiplied test the checker decides. -/
def Allowance.fits (w : Allowance) (P C : Nat) : Bool :=
  decide (P * w.ratio.den ≤ w.ratio.num * C + w.margin * w.ratio.den)

/-- Ratios and margins per area and category; the first entry for a key wins. -/
abbrev Entries (A : Type) := List ((A × Category) × Allowance)

def Entries.allowance {A : Type} [DecidableEq A] (es : Entries A) (key : A × Category) :
    Allowance :=
  match es.find? (fun e => decide (e.1 = key)) with
  | some e => e.2
  | none => .zero

structure Policy (A : Type) where
  scope : Scope A
  entries : Entries A

def Policy.allowance {A : Type} [DecidableEq A] (pol : Policy A) (key : A × Category) :
    Allowance :=
  pol.entries.allowance key

/-- Shrink-only update: every frozen entry keeps its key and drops to the value
minimum with the proposal (a key the proposal omits drops to zero); the scope and the
entry list's keys stay those of the frozen policy. -/
def Policy.shrink {A : Type} [DecidableEq A] (frozen : Policy A) (proposed : Entries A) :
    Policy A :=
  { frozen with entries := frozen.entries.map fun e => (e.1, e.2.min (proposed.allowance e.1)) }

/-- One measured file: its path and its lexically classified lines. -/
structure File where
  path : Path
  lines : List Line

abbrev Tree := List File

def fileProse {A : Type} (s : Scope A) (f : File) (k : Category) : Nat :=
  match s.treat f.path with
  | .source => (f.lines.map (Line.prose · k)).sum
  | .docs => if k = .docs then f.lines.length else 0
  | _ => 0

def fileCode {A : Type} (s : Scope A) (f : File) : Nat :=
  match s.treat f.path with
  | .source => (f.lines.map Line.code).sum
  | _ => 0

variable {A : Type} [DecidableEq A]

def prose (s : Scope A) (t : Tree) (a : A) (k : Category) : Nat :=
  ((t.filter fun f => decide (s.area f.path = a)).map (fileProse s · k)).sum

def code (s : Scope A) (t : Tree) (a : A) : Nat :=
  ((t.filter fun f => decide (s.area f.path = a)).map (fileCode s)).sum

/-- Areas of counted files in the tree, newly encountered ones included. -/
def checkedAreas (s : Scope A) (t : Tree) : List A :=
  (t.filter fun f => (s.treat f.path).counted).map (s.area ·.path)

/-- The decision model: every checked area and category fits its frozen allowance. -/
def accepts (pol : Policy A) (t : Tree) : Bool :=
  (checkedAreas pol.scope t).all fun a => Category.all.all fun k =>
    (pol.allowance (a, k)).fits (prose pol.scope t a k) (code pol.scope t a)

def Within (pol : Policy A) (t : Tree) (a : A) (k : Category) : Prop :=
  prose pol.scope t a k ≤ (pol.allowance (a, k)).lines (code pol.scope t a)

/-- The specification, over every area of the type, listed or not. -/
def WithinAllowance (pol : Policy A) (t : Tree) : Prop := ∀ a k, Within pol t a k

/-- Obligations of the code-relative ratchet. -/
structure Laws (A : Type) [DecidableEq A] : Prop where
  /-- Acceptance is exactly the per-area bound: equality passes, one line over fails. -/
  decides : ∀ (pol : Policy A) t, accepts pol t = true ↔ WithinAllowance pol t
  rejects : ∀ (pol : Policy A) t a k, ¬ Within pol t a k → accepts pol t = false
  /-- The rounding convention: floor of the ratio part, exactly the cross product. -/
  rounding : ∀ (w : Allowance) P C,
    P ≤ w.lines C ↔ P * w.ratio.den ≤ w.ratio.num * C + w.margin * w.ratio.den
  /-- Value-equal ratios and margins allow the same prose. -/
  byValue : ∀ (w v : Allowance), w.Equiv v → ∀ C, w.lines C = v.lines C
  zeroCode : ∀ (pol : Policy A) t a k, code pol.scope t a = 0 →
    (Within pol t a k ↔ prose pol.scope t a k ≤ (pol.allowance (a, k)).margin)
  /-- A missing entry, also for a new area, allows no prose at all. -/
  unlisted : ∀ (pol : Policy A) t a k, (∀ w, ((a, k), w) ∉ pol.entries) →
    accepts pol t = true → prose pol.scope t a k = 0
  /-- Prose added with its own code at the frozen ratio stays accepted. -/
  growth : ∀ (pol : Policy A) t (f : File), pol.scope.treat f.path = .source →
    (∀ k, let w := pol.allowance (pol.scope.area f.path, k)
      (f.lines.map (Line.prose · k)).sum * w.ratio.den ≤
        w.ratio.num * (f.lines.map Line.code).sum) →
    accepts pol t = true → accepts pol (t ++ [f]) = true
  /-- Uncounted files (generated, audits, outside) change nothing. -/
  uncounted : ∀ (pol : Policy A) t (f : File), (pol.scope.treat f.path).counted = false →
    accepts pol (t ++ [f]) = accepts pol t
  generatedPadding : ∀ (pol : Policy A) t (f : File), f.path ∈ pol.scope.generated →
    accepts pol (t ++ [f]) = accepts pol t
  auditsPadding : ∀ (pol : Policy A) t (f : File), InAudits f.path = true →
    accepts pol (t ++ [f]) = accepts pol t
  /-- Blank, comment, docstring and process-id lines add no code and cannot turn a
  rejection into acceptance. -/
  codeFreePadding : ∀ (pol : Policy A) t (f : File), (∀ l ∈ f.lines, l.hasCode = false) →
    (∀ a, code pol.scope (t ++ [f]) a = code pol.scope t a) ∧
    (accepts pol t = false → accepts pol (t ++ [f]) = false)
  /-- A non-code segment never changes whether its line is code. -/
  segmentInert : ∀ (l : Line) (s : Segment), s.isCode = false →
    Line.hasCode (l ++ [s]) = l.hasCode ∧ Line.hasCode (s :: l) = l.hasCode
  shrinkFrozen : ∀ (pol : Policy A) p key, ((pol.shrink p).allowance key).le (pol.allowance key)
  shrinkProposed : ∀ (pol : Policy A) p key,
    ((pol.shrink p).allowance key).le (p.allowance key)
  /-- A proposal below the frozen policy is taken, up to value. -/
  shrinkExact : ∀ (pol : Policy A) p, (∀ key, (p.allowance key).le (pol.allowance key)) →
    ∀ key, ((pol.shrink p).allowance key).Equiv (p.allowance key)
  /-- No reset: the scope and every entry key survive. -/
  shrinkKeeps : ∀ (pol : Policy A) p,
    (pol.shrink p).scope = pol.scope ∧ (pol.shrink p).entries.map (·.1) = pol.entries.map (·.1)
  /-- A pointwise smaller policy over the same scope accepts less. -/
  tighten : ∀ (pol q : Policy A) t, q.scope = pol.scope →
    (∀ key, (q.allowance key).le (pol.allowance key)) → accepts q t = true → accepts pol t = true
  /-- Candidate policy bytes never authorize what the frozen policy rejects. -/
  noReplacement : ∀ (pol : Policy A) p t, accepts (pol.shrink p) t = true → accepts pol t = true

end ProseRatio

/-- The code-relative prose ratchet's laws for every area type. Open until pb2 proves
them; the policy values, checker and CI are not part of this statement. -/
@[goal Solidity.Docs.prose_ratio_rule_sound "pb2-prose-ratio-rule"]
def proseRatioRuleSound : Prop := ∀ (A : Type) [DecidableEq A], ProseRatio.Laws A

end Solidity.Goals
