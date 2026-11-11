import Solidity.Tools.Goal
import Solidity.Yul.Words

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

/-! Arithmetic vocabulary for the universal opcode contract. Inputs are already
words, so quantifying over `Fin a → Word` covers the entire word domain.
All result equalities expose canonical natural residues modulo 2^256. -/
namespace OpcodeSpec

open Solidity.Yul

/-- Word modulus, independent of evaluation. -/
def modulus : Nat := 2 ^ 256

/-- Canonical residue of a signed integer, including negative results. -/
def residue (z : Int) : Nat := (z % (2 ^ 256)).toNat

/-- CLZ shared by Arithmetic and Bytes: zero has 256 leading zeros; for
nonzero words log2 is the position of the highest set bit. -/
def clz : Prop := ∀ xs : Fin 1 → Word,
  (Pure.eval .«clz» xs).val =
    (if (xs 0).val = 0 then 256 else 255 - (xs 0).val.log2) % modulus

end OpcodeSpec

open Solidity.Yul

/-- Source operand 0 is the shift amount; operand 1 is the value.
SAR divides the signed two's-complement integer with floor rounding, including
negative odd values. Amounts at least 256 give zero or the complete sign fill. -/
def opcodeShifts : Prop :=
  (∀ xs : Fin 2 → Word, (Pure.eval .«shl» xs).val =
    (if (xs 0).val ≥ 256 then 0 else (xs 1).val * 2 ^ (xs 0).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«shr» xs).val =
    (if (xs 0).val ≥ 256 then 0 else (xs 1).val / 2 ^ (xs 0).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«sar» xs).val =
    OpcodeSpec.residue (if (xs 0).val ≥ 256 then
      (if signed (xs 1) < 0 then -1 else 0)
      else signed (xs 1) / (2 ^ (xs 0).val : Int)))

/-- Source operands 0,1 are left,right; operand 2 is ADDMOD/MULMOD's
modulus. Natural intermediates are unbounded, with subtraction wrapping by
adding 2^256 first. Signed operands use `signed`'s two's-complement meaning;
`tdiv` truncates toward zero and `tmod` retains the dividend's sign. Residue
normalization includes minimum-signed / -1 overflow. Every zero divisor or
modulus gives zero. Comparisons return complete words 0 or 1, and bitwise
operations cover all 256 bits. No operand is excluded. -/
def opcodeArithmetic : Prop :=
  (∀ xs : Fin 2 → Word, (Pure.eval .«add» xs).val =
    ((xs 0).val + (xs 1).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«sub» xs).val =
    ((xs 0).val + OpcodeSpec.modulus - (xs 1).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«mul» xs).val =
    ((xs 0).val * (xs 1).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«div» xs).val =
    (if (xs 1).val = 0 then 0 else (xs 0).val / (xs 1).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«mod» xs).val =
    (if (xs 1).val = 0 then 0 else (xs 0).val % (xs 1).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«sdiv» xs).val =
    OpcodeSpec.residue (if (xs 1).val = 0 then 0 else (signed (xs 0)).tdiv (signed (xs 1)))) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«smod» xs).val =
    OpcodeSpec.residue (if (xs 1).val = 0 then 0 else (signed (xs 0)).tmod (signed (xs 1)))) ∧
  (∀ xs : Fin 3 → Word, (Pure.eval .«addmod» xs).val =
    (if (xs 2).val = 0 then 0 else ((xs 0).val + (xs 1).val) % (xs 2).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 3 → Word, (Pure.eval .«mulmod» xs).val =
    (if (xs 2).val = 0 then 0 else ((xs 0).val * (xs 1).val) % (xs 2).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«lt» xs).val =
    (if (xs 0).val < (xs 1).val then 1 else 0) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«gt» xs).val =
    (if (xs 1).val < (xs 0).val then 1 else 0) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«slt» xs).val =
    (if signed (xs 0) < signed (xs 1) then 1 else 0) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«sgt» xs).val =
    (if signed (xs 1) < signed (xs 0) then 1 else 0) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«eq» xs).val =
    (if (xs 0).val = (xs 1).val then 1 else 0) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 1 → Word, (Pure.eval .«iszero» xs).val =
    (if (xs 0).val = 0 then 1 else 0) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 1 → Word, (Pure.eval .«not» xs).val =
    (OpcodeSpec.modulus - 1 - (xs 0).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«and» xs).val =
    ((xs 0).val &&& (xs 1).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«or» xs).val =
    ((xs 0).val ||| (xs 1).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«xor» xs).val =
    ((xs 0).val ^^^ (xs 1).val) % OpcodeSpec.modulus) ∧
  OpcodeSpec.clz

/-- BYTE uses operand 0 as a big-endian byte index (0 is most significant),
with zero at every index ≥32. SIGNEXTEND uses operand 0 as a byte index,
tests bit 8*i+7, and is identity at every index ≥31. EXP uses operand 0 as
base and operand 1 as exponent: mathematical power includes exponent zero
(and 0^0 = 1), independently of the square-and-multiply implementation. -/
def opcodeBytesPowers : Prop :=
  (∀ xs : Fin 2 → Word, (Pure.eval .«byte» xs).val =
    (if (xs 0).val ≥ 32 then 0 else
      ((xs 1).val / 2 ^ (8 * (31 - (xs 0).val))) % 256) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«signextend» xs).val =
    (if (xs 0).val ≥ 31 then (xs 1).val else
      let bits := 8 * ((xs 0).val + 1)
      let low := (xs 1).val % (2 ^ bits)
      if low < 2 ^ (bits - 1) then low
      else low + OpcodeSpec.modulus - 2 ^ bits) % OpcodeSpec.modulus) ∧
  OpcodeSpec.clz ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«exp» xs).val =
    (xs 0).val ^ (xs 1).val % OpcodeSpec.modulus)

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

end Solidity.Goals
