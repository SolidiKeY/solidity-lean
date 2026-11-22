import Solidity.Tools.Goal

/-! The plan goal `proseRatioRuleSound` (`x.md`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

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
