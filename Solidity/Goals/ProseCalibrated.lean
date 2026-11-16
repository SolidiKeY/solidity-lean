import Solidity.Goals.Plan

/-!
Inactive calibrated contract (H659/H666/H671), separate from `ProseRatio`.
References refreshed at f2f915369596117bd9386cbbb51b539c5f7ad27a:
`Plan.lean:870-1143`; `scripts/prose-backtest/README.md:65-138,234-247`;
`backtest.py:812-830` (`v2_test`, `v2_allowance`); calibration-additive.json
specification.policy/selection/classifier/denominator_mapping/enforcement_exclusions.
The old whole-number-margin and path-list contracts are deliberately not reused.

Boundary: generator reproduction is unverified (published verified list empty),
envelope-margin policy unapproved, no held-out evidence, residual failures in
Goals/Correctness/Lowering/Yul unresolved, inherited pb1 provenance UNVERIFIABLE.
In-sample success and post-hoc Scratch coverage are not independent validation.
This authorizes no allowance decision, margin raise, regeneration or activation.
Arithmetic, actual checker correspondence, historical authenticity, policy approval,
generator reproduction and merged CI success are distinct obligations. Lexical
padding laws say nothing about useless nonblank code or source-line splitting.
-/
namespace Solidity.Goals
namespace ProseCalibrated

open ProseRatio (Category Segment Line Ratio)

abbrev RepoPath := ProseRatio.Path

/-- Exact nonnegative rationals, with positive representation denominators. -/
abbrev Rational := Ratio

def Rational.zero : Rational := ⟨0, 1, by decide⟩
def Rational.ofNat (n : Nat) : Rational := ⟨n, 1, by decide⟩
def Rational.equiv (x y : Rational) : Prop := x.le y ∧ y.le x

def Rational.add (x y : Rational) : Rational :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den,
    Nat.mul_pos x.den_pos y.den_pos⟩
def Rational.scale (x : Rational) (d : Nat) : Rational := ⟨x.num * d, x.den, x.den_pos⟩

structure Allowance where
  ratio : Rational
  margin : Rational

def Allowance.zero : Allowance := ⟨.zero, .zero⟩
def Allowance.value (w : Allowance) (d : Nat) : Rational := w.ratio.scale d |>.add w.margin
/-- Declarative order on exact rational values; no rounding. -/
def Allowance.Within (w : Allowance) (n d : Nat) : Prop :=
  (Rational.ofNat n).le (w.value d)
/-- Independent executable cross-product decision, as in v2_test. -/
def Allowance.fits (w : Allowance) (n d : Nat) : Bool :=
  decide (n * w.ratio.den * w.margin.den ≤
    w.ratio.num * d * w.margin.den + w.margin.num * w.ratio.den)
def Allowance.lines (w : Allowance) (d : Nat) : Nat :=
  (w.value d).num / (w.value d).den

def Allowance.le (w v : Allowance) : Prop := w.ratio.le v.ratio ∧ w.margin.le v.margin
def Allowance.equiv (w v : Allowance) : Prop := w.le v ∧ v.le w
def Allowance.min (w v : Allowance) : Allowance :=
  ⟨w.ratio.min v.ratio, w.margin.min v.margin⟩

/-- Nonnegative residual, computed before taking the historical maximum. -/
def residual (r : Rational) (n d : Nat) : Rational :=
  ⟨n * r.den - r.num * d, r.den, r.den_pos⟩
def historicalMargin (r : Rational) (history : List (Nat × Nat)) : Rational :=
  history.foldl (fun m nd => let x := residual r nd.1 nd.2; if m.le x then x else m) .zero
/-- History is supplied separately, never from the candidate. Selection by frozen
first-parent existence/timestamps and authenticity are external binding obligations. -/
def calibrate (anchorN anchorD : Nat) (history : List (Nat × Nat)) : Allowance :=
  let r : Rational := if h : 0 < anchorD then ⟨anchorN, anchorD, h⟩ else .zero
  ⟨r, historicalMargin r history⟩

/-- Reproduction evidence must be checked externally; a string is not a proof.
Matching binds the output path/blob and generator path/blob at the measured commit. -/
structure GeneratedEntry where
  path : RepoPath
  outputBlob : String
  generatorPath : RepoPath
  generatorBlob : String
  reproductionReceipt : String

structure File where
  path : RepoPath
  outputBlob : String
  generatorPath : RepoPath
  generatorBlob : String
  generationHeader : Bool
  lines : List Line
abbrev Tree := List File

inductive Denominator where
  | self | repositorySolidity
  deriving DecidableEq

/-- No discretionary exclusion list: audits alone are temporarily unenforced.
`kind` and `area` are frozen classifications, not candidate-supplied headers. -/
structure Scope where
  /-- Exempt individual segment occurrences, not entire lines.
  External binding validates canonical header syntax and registry membership. -/
  registeredImport : RepoPath → Nat → Nat → Bool
  verified : List GeneratedEntry
  provenance : String
  selection : String

/-- Canonical area mapping, including root files. `File` denotes a regular blob;
raw symlinks/nonblobs must not be decoded as files by the binding. -/
def Scope.area (_ : Scope) (p : RepoPath) : RepoPath :=
  match p with
  | root :: area :: _ :: _ => [root, area]
  | root :: _ :: [] => [root, "_root"]
  | _ => p

def Scope.kind (_ : Scope) (p : RepoPath) : ProseRatio.Kind :=
  if p.length < 2 then .outside
  else if p.head? == some "docs" then .docs
  else if p.head? == some "Solidity" && (p.getLast!).endsWith ".lean" then .source
  else .outside

def Scope.denominator (_ : Scope) (a : RepoPath) : Denominator :=
  if a.head? == some "Solidity" then .self else .repositorySolidity

/-- An exemption cannot erase H tokens or other segments. The occurrence index
must identify an actual G token in the canonical import's module-name span. -/
def processCount (s : Scope) (f : File) (line : Nat) (l : Line) : Nat :=
  (l.zipIdx.map fun (seg, occurrence) => match seg with
    | .processId token => if token.startsWith "G" && s.registeredImport f.path line occurrence then 0 else 1
    | _ => 0).sum

def entryMatches (e : GeneratedEntry) (f : File) : Bool :=
  e.path == f.path && e.outputBlob == f.outputBlob &&
  e.generatorPath == f.generatorPath && e.generatorBlob == f.generatorBlob

def verified (s : Scope) (f : File) : Bool := s.verified.any (entryMatches · f)
def eligible (s : Scope) (f : File) : Bool :=
  s.kind f.path != .outside && !verified s f

def codeFile (s : Scope) (f : File) : Nat :=
  if eligible s f && s.kind f.path == .source then (f.lines.map Line.code).sum else 0

def proseFile (s : Scope) (f : File) (k : Category) : Nat :=
  if !eligible s f then 0
  else match s.kind f.path with
    | .source => (f.lines.zipIdx |>.map fun (l, i) =>
        if k == .processId then processCount s f i l else l.prose k).sum
    | .docs => if k == .docs then f.lines.length else 0
    | .outside => 0

def numerator (s : Scope) (t : Tree) (a : RepoPath) (k : Category) : Nat :=
  (t.filter (fun f => s.area f.path == a) |>.map (proseFile s · k)).sum

def denominator (s : Scope) (t : Tree) (a : RepoPath) : Nat :=
  (t.filter (fun f => match s.denominator a with
    | .self => s.area f.path == a
    | .repositorySolidity => f.path.head? == some "Solidity") |>.map (codeFile s)).sum

abbrev Entries := List ((RepoPath × Category) × Allowance)
def lookup (es : Entries) (key : RepoPath × Category) : Allowance :=
  match es.find? (fun e => e.1 == key) with
  | some e => e.2
  | none => .zero

structure Policy where
  scope : Scope
  entries : Entries

def Policy.shrink (p : Policy) (proposal : Entries) : Policy :=
  { p with entries := p.entries.map fun e => (e.1, e.2.min (lookup proposal e.1)) }

/-- Audits remain measured/reported; only enforcement is temporarily skipped. -/
def enforced (a : RepoPath) : Bool := !ProseRatio.InAudits a

def areas (p : Policy) (t : Tree) : List RepoPath :=
  p.entries.map (·.1.1) ++ t.map (p.scope.area ·.path)

def accepts (p : Policy) (t : Tree) : Bool :=
  (areas p t).all fun a => !enforced a || Category.all.all fun k =>
    (lookup p.entries (a, k)).fits (numerator p.scope t a k) (denominator p.scope t a)

/-- Unavailable measurements fail closed; absence of files is an available empty tree. -/
def decision (p : Policy) (measurement : Option Tree) : Bool :=
  match measurement with | none => false | some t => accepts p t

def Within (p : Policy) (t : Tree) : Prop := ∀ a k, enforced a = true →
  (lookup p.entries (a, k)).Within (numerator p.scope t a k) (denominator p.scope t a)

/-- Laws to prove downstream, universally quantified rather than fixture claims. -/
structure Laws : Prop where
  exact : ∀ (w : Allowance) (n d : Nat), w.fits n d = true ↔ Allowance.Within w n d
  floorSum : ∀ (w : Allowance) (n d : Nat), n ≤ Allowance.lines w d ↔ w.Within n d
  boundary : ∀ (w : Allowance) (d : Nat), w.fits (w.lines d) d = true ∧ w.fits (w.lines d + 1) d = false
  byValue : ∀ (w v : Allowance), w.equiv v → ∀ n d, w.fits n d = v.fits n d
  decides : ∀ (p : Policy) (t : Tree), accepts p t = true ↔ Within p t
  rejects : ∀ (p : Policy) (t : Tree) (a : RepoPath) (k : Category), enforced a = true →
    ¬(lookup p.entries (a,k)).Within (numerator p.scope t a k) (denominator p.scope t a) →
    accepts p t = false
  zeroEvaluation : ∀ (w : Allowance) (n : Nat), w.Within n 0 ↔ (Rational.ofNat n).le w.margin
  zeroAnchor : ∀ (n : Nat) (h : List (Nat × Nat)), (calibrate n 0 h).ratio.equiv .zero ∧
    (calibrate n 0 h).margin.equiv (Rational.ofNat ((h.map (·.1)).foldl Nat.max 0))
  zeroNumerator : ∀ (d : Nat) (h : List (Nat × Nat)), (calibrate 0 d h).ratio.equiv .zero ∧
    (calibrate 0 d h).margin.equiv (Rational.ofNat ((h.map (·.1)).foldl Nat.max 0))
  unseen : ∀ (p : Policy) (t : Tree) (a : RepoPath) (k : Category), (∀ w, ((a,k),w) ∉ p.entries) → enforced a = true →
    accepts p t = true → numerator p.scope t a k = 0
  unavailable : ∀ (p : Policy), decision p none = false
  shrinkValues : ∀ (p : Policy) (q : Entries) (key : RepoPath × Category), (lookup (p.shrink q).entries key).le (lookup p.entries key) ∧
    (lookup (p.shrink q).entries key).le (lookup q key)
  shrinkFrozen : ∀ (p : Policy) (q : Entries), (p.shrink q).scope = p.scope ∧
    (p.shrink q).entries.map (·.1) = p.entries.map (·.1)
  shrinkExact : ∀ (p : Policy) (q : Entries), (∀ key, (lookup q key).le (lookup p.entries key)) →
    ∀ key, (lookup (p.shrink q).entries key).equiv (lookup q key)
  tighten : ∀ (p q : Policy) (t : Tree), q.scope = p.scope →
    (∀ key, (lookup q.entries key).le (lookup p.entries key)) →
    accepts q t = true → accepts p t = true
  noReplacement : ∀ (p : Policy) (q : Entries) (t : Tree), accepts (p.shrink q) t = true → accepts p t = true
  codeFreePadding : ∀ (p : Policy) (t : Tree) (f : File), (∀ l ∈ f.lines, l.hasCode = false) →
    (∀ a, denominator p.scope (t ++ [f]) a = denominator p.scope t a) ∧
    (accepts p t = false → accepts p (t ++ [f]) = false)
  /-- Fixed policy and measured identities: append does not edit existing output
  or generator blobs. No invariance is asserted across changed verification identities. -/
  generatedPadding : ∀ (p : Policy) (t : Tree) (f : File), verified p.scope f = true →
    accepts p (t ++ [f]) = accepts p t
  symmetricExclusion : ∀ (s : Scope) (f : File), verified s f = true →
    codeFile s f = 0 ∧ ∀ k, proseFile s f k = 0
  headerInert : ∀ (s : Scope) (f : File) (b : Bool), eligible s { f with generationHeader := b } = eligible s f
  unverifiedCounted : ∀ (s : Scope) (f : File), verified s f = false → s.kind f.path ≠ .outside →
    eligible s f = true
  identityMismatch : ∀ (e : GeneratedEntry) (f : File), (e.path ≠ f.path ∨ e.outputBlob ≠ f.outputBlob ∨
    e.generatorPath ≠ f.generatorPath ∨ e.generatorBlob ≠ f.generatorBlob) → entryMatches e f = false
  docstringSubset : ∀ (s : Scope) (f : File), proseFile s f .docstring ≤ proseFile s f .comment
  sourceLocal : ∀ (s : Scope) (t : Tree) (a : RepoPath) (f : File), s.denominator a = .self → s.area f.path ≠ a →
    denominator s (t ++ [f]) a = denominator s t a
  docsRepository : ∀ (s : Scope) (t : Tree) (a : RepoPath), s.denominator a = .repositorySolidity →
    denominator s t a = (t.filter (fun f => f.path.head? == some "Solidity") |>.map (codeFile s)).sum

/-!
Correspondence is deliberately an unproved companion contract, not a premise
of `Laws.decides`. Future pb2 must instantiate it with the actual checker execution
semantics and independent raw-input binding relations; it cannot supply arbitrary
relations or a provenance token as historical authenticity. Those relations must
bind measured commit/path/blob identities, reach and area mapping, lexer/category
counts (Unicode whitespace, comment spans, docstring subset, occurrence counts),
registered-root process-ID imports, self/repository denominators, frozen policy
parsing and historical selection/provenance, and externally reproduced generation.
They must not mention acceptance or assume the equality being proved.
-/
structure CheckerInterface (Raw : Type) where
  /-- Actual execution of the specifically identified checker artifact. -/
  runs : Raw → Bool → Prop
  /-- Independent raw decoding; unavailable inputs use none. -/
  decode : Raw → Policy → Option Tree → Prop
  measuredReach : Raw → Policy → Option Tree → Prop
  lexerCounts : Raw → Policy → Option Tree → Prop
  registryOccurrences : Raw → Policy → Option Tree → Prop
  denominatorMapping : Raw → Policy → Option Tree → Prop
  frozenPolicyParsing : Raw → Policy → Option Tree → Prop
  historicalProvenance : Raw → Policy → Option Tree → Prop
  generatedReproduction : Raw → Policy → Option Tree → Prop
  /-- Actual artifact identity, not supplied or rewritten by the candidate. -/
  artifact : String

/-- Separate binding obligations: none is an assumption about checker acceptance.
Instantiation must define these from actual bytes/commits/registry and reproduction
semantics; arbitrary predicates or tokens do not establish authenticity. -/
def CheckerInterface.Bound {Raw : Type} (i : CheckerInterface Raw)
    (raw : Raw) (p : Policy) (t : Option Tree) : Prop :=
  i.decode raw p t ∧ i.measuredReach raw p t ∧ i.lexerCounts raw p t ∧
  i.registryOccurrences raw p t ∧ i.denominatorMapping raw p t ∧
  i.frozenPolicyParsing raw p t ∧ i.historicalProvenance raw p t ∧
  i.generatedReproduction raw p t

/-- Required future implementation-to-model theorem type. No implementation,
execution semantics, binding proof or instance is supplied in this prerequisite. -/
def ImplementationCorrespondence {Raw : Type} (i : CheckerInterface Raw) : Prop :=
  (∀ raw, ∃ p t, i.Bound raw p t) ∧
  (∀ raw p t actual, i.Bound raw p t → i.runs raw actual → actual = decision p t) ∧
  (∀ raw, ∃ actual, i.runs raw actual)

end ProseCalibrated

/-- Open calibrated arithmetic/classification laws. The companion
`ProseCalibrated.ImplementationCorrespondence` must additionally be discharged for
actual pb2 tooling under separate H659 path authorization. Closing this goal alone
does not establish implementation soundness; arithmetic cannot imply
that Python parses, measures or verifies correctly. -/
@[goal Solidity.Docs.prose_calibrated_ratio_rule_sound "pb2-prose-ratio-rule"]
def proseCalibratedRatioRuleSound : Prop := ProseCalibrated.Laws

end Solidity.Goals
