import Solidity.Goals.Plan
import Solidity.Semantics.IntrinsicStorage.Layout

namespace Solidity.Goals

/--
info: unstated Solidity.Goals.trustedSurfaceClosed ← Solidity.Main.trusted_surface_closed plan va1-trust-surface
-/
#guard_msgs in
#roadmap_goal trustedSurfaceClosed

/--
info: unstated Solidity.Goals.differentialAgreement ← Solidity.Validation.differential_agreement plan va3-semantic-validation
-/
#guard_msgs in
#roadmap_goal differentialAgreement

/--
info: unstated Solidity.Goals.benchmarkBudgetsMet ← Solidity.Bench.budgets_met plan vu1-benchmarks
-/
#guard_msgs in
#roadmap_goal benchmarkBudgetsMet

/--
info: unstated Solidity.Goals.fastModeAgrees ← Solidity.Automation.fast_mode_agrees plan vu2-fast-mode
-/
#guard_msgs in
#roadmap_goal fastModeAgrees

/--
info: unstated Solidity.Goals.certificateCheckSound ← Solidity.Automation.Certificate.check_sound plan vu3-certificates
-/
#guard_msgs in
#roadmap_goal certificateCheckSound

/--
info: unstated Solidity.Goals.callSummarySound ← Solidity.Automation.Summary.call_summary_sound plan vu4-modular
-/
#guard_msgs in
#roadmap_goal callSummarySound

/--
info: unstated Solidity.Goals.genericYulViewsPreserve ← Solidity.Yul.Views.generic_views_preserve plan t1-yul-views-generic
-/
#guard_msgs in
#roadmap_goal genericYulViewsPreserve

/--
info: unstated Solidity.Goals.controlsOffCriticalPath ← Solidity.Controls.off_critical_path plan t2-controls-off-path
-/
#guard_msgs in
#roadmap_goal controlsOffCriticalPath

/--
info: unstated Solidity.Goals.dedupStatementsPreserved ← Solidity.Dedup.statements_preserved plan t3-dedup-rollout
-/
#guard_msgs in
#roadmap_goal dedupStatementsPreserved

/--
info: unstated Solidity.Goals.docLintClean ← Solidity.Docs.lint_clean plan g2-doc-lint
-/
#guard_msgs in
#roadmap_goal docLintClean

/--
info: unstated Solidity.Goals.docHistoryPurged ← Solidity.Docs.history_purged plan g3-history-purge-docs
-/
#guard_msgs in
#roadmap_goal docHistoryPurged

/--
info: unstated Solidity.Goals.commentsAsCode ← Solidity.Docs.comments_as_code plan g4-comments-to-code
-/
#guard_msgs in
#roadmap_goal commentsAsCode

/--
info: open Solidity.Goals.opcodeEvalUniversal ← Solidity.Yul.opcode_eval_universal plan v1-yul-checks-universal
-/
#guard_msgs in
#roadmap_goal opcodeEvalUniversal

/--
info: open Solidity.Goals.leanInventorySound ← Solidity.LeanInventory.inventory_sound plan k1-lean-inventory
-/
#guard_msgs in
#roadmap_goal leanInventorySound

/--
info: open Solidity.Goals.yulAcceptedCompilesWithArtifact ← Solidity.Yul.accepted_compiles_with_artifact plan y1-yul-artifact-producers
-/
#guard_msgs in
#roadmap_goal yulAcceptedCompilesWithArtifact

/--
info: open Solidity.Goals.intrinsicSessionSemantics ← Solidity.Semantics.IntrinsicSession.session_semantics_correct plan is0-intrinsic-session
-/
#guard_msgs in
#roadmap_goal intrinsicSessionSemantics

/-! Layout controls for the storage prerequisite; the session goal above stays OPEN. -/
namespace IntrinsicStorageLayoutControls
open Solidity.Storage Solidity.Semantics Solidity.Semantics.IntrinsicStorage

private def ledgerKey (k : PrimTy.uint.Denote) : Path (.ref (.struct "LedgerUse")) .uint :=
  .field (f := "ledger") (T := .ref (.struct "Ledger")) (by decide)
    (.field (f := "balances") (T := .ref (.mapping .uint .uint)) (by decide) (.key k .nil))

-- The nested ledger's nonce occupies slot zero, so its mapping starts at one.
example (k : PrimTy.uint.Denote) :
    locate (ledgerKey k) (.root 0) = .hash (keyWord k) (.root 1) 0 := by rfl

private def personAge (i : PrimTy.uint.Denote) :
    Path (.ref (.array (.ref (.struct "Person")))) .uint :=
  .at i (.field (f := "age") (T := .uint) (by decide) .nil)

-- Person has three slots; age follows the two-slot Account member.
example (i : PrimTy.uint.Denote) :
    locate (personAge i) (.root 7) = .data (.root 7) (i.val.toNat * 3 + 2) := by rfl

-- A mapping to Person arrays composes its key and array/member path.
example (k i : PrimTy.uint.Denote) :
    locate ((Path.key k .nil).append (personAge i)) (.root 7) =
      .data (.hash (keyWord k) (.root 7) 0) (i.val.toNat * 3 + 2) := by
  rw [locate_append]
  rfl

-- Descending into an array member retains the enclosing mapping's hash input.
example (k i : PrimTy.uint.Denote) :
    ancestry (.hash (keyWord k) (.root 7) 0) <+:
      ancestry (locate (personAge i) (.hash (keyWord k) (.root 7) 0)) :=
  ancestry_locate (personAge i) _

-- Field boundaries and fixed-array strides agree with the dependent struct layout.
example {s f : Name} {T : Ty} (h : lookupBy f (structDef s) = some T) :
    offset s f + size T ≤ size (.ref (.struct s)) := by
  rw [size_struct]
  exact offsetIn_bound h

example (n : Nat) : size (.ref (.fixed (.ref (.struct "Person")) n)) = n * 3 := by
  rw [size_fixed, size_struct]
  rfl

-- Equal encoded inputs reached by actual typed references decode to equal preimages.
-- This neither assumes nor concludes injectivity of keccak.
example {C : Contract} {T : Ty} (r : SRef C T) {p q : Pre}
    (hp : p ∈ ancestry (reference r)) (hq : q ∈ ancestry (reference r))
    (h : encoded p = encoded q) : p = q :=
  encoded_inj (ancestry_words _ (reference_bounded r) _ hp)
    (ancestry_words _ (reference_bounded r) _ hq) h

-- Array data and mapping entry encodings cannot be confused, even at the same word.
example : encoded (.data 7) ≠ encoded (.entry 7 0) := by
  intro h
  have e := encoded_inj (p := .data 7) (q := .entry 7 0)
    (by unfold Pre.Words; decide) (by unfold Pre.Words; decide) h
  cases e

end IntrinsicStorageLayoutControls

/-! The Lean policy specification only: not the checker's proof, the calibrated
policy, the Python integration or CI on the merged head. -/
/--
info: open Solidity.Goals.proseRatioRuleSound ← Solidity.Docs.prose_ratio_rule_sound plan pb2-prose-ratio-rule
-/
#guard_msgs in
#roadmap_goal proseRatioRuleSound

/-! The accepted Yul language is inhabited at every local count and control, is
closed under arbitrarily deep composition and arithmetic nesting, admits
nonzero newer-prefix depths, and refuses constructors the producer does not
visit. -/
namespace YulArtifact

/-- Two operands for a binary builtin, left first. -/
def operands {n : Nat} (left right : Yul.Expr [] [] n 1) : Fin 2 → Yul.Expr [] [] n 1 :=
  fun k => if k.val = 0 then left else right

/-- `x := (x + w) * (y - x)`, then `y := x`. -/
def sample {c : Yul.Control} {n : Nat} (x y : Fin n) (w : Yul.Word) : Yul.Stmt [] [] c n :=
  .seq
    (.assign (fun _ => .local x) (.builtin (.pure .mul) (operands
      (.builtin (.pure .add) (operands (.local x) (.literal w)))
      (.builtin (.pure .sub) (operands (.local y) (.local x))))))
    (.assign (fun _ => .local y) (.local x))

example {c : Yul.Control} {n : Nat} (x y : Fin n) (w : Yul.Word) :
    Accepted (sample (c := c) x y w) :=
  .seq (.assign _ (.binary (.inr (.inr rfl))
      (.binary (.inl rfl) (.local x) (.literal w))
      (.binary (.inr (.inl rfl)) (.local y) (.local x))))
    (.assign _ (.local x))

/-- Composition of `k + 1` copies of a statement. -/
def iterate {c : Yul.Control} {n : Nat} (s : Yul.Stmt [] [] c n) : Nat → Yul.Stmt [] [] c n
  | 0 => s
  | k + 1 => .seq s (iterate s k)

example {c : Yul.Control} {n : Nat} (s : Yul.Stmt [] [] c n) (accepted : Accepted s)
    (k : Nat) : Accepted (iterate s k) := by
  induction k with
  | zero => exact accepted
  | succ k ih => exact .seq accepted ih

/-- With locals `0` and `1`, `sample` fits under three newer words. -/
example {c : Yul.Control} (w : Yul.Word) :
    Fits 3 (sample (c := c) (0 : Fin 2) 1 w) :=
  .seq (.assign _ (fun i same => by cases same; decide)
      (.builtin
        (.builtin (.local (height := 3) (0 : Fin 2) (by decide))
          (.local (height := 4) (1 : Fin 2) (by decide)))
        (.builtin (.literal _ _) (.local (height := 5) (0 : Fin 2) (by decide)))))
    (.assign _ (fun i same => by cases same; decide)
      (.local (height := 3) (0 : Fin 2) (by decide)))

/-- `Fits` is a real limit: a write to local 0 under sixteen newer words has no
SWAP reach. -/
example {c : Yul.Control} (w : Yul.Word) :
    ¬ Fits 16 (.assign (c := c) (fun _ => .local (0 : Fin 1)) (.literal w)) := by
  intro fits
  cases fits with
  | assign _ reach _ => exact absurd (reach 0 rfl) (by decide)

example {c : Yul.Control} {n : Nat} (test : Yul.Expr [] [] n 1) (body : Yul.Stmt [] [] c n) :
    ¬ Accepted (.if_ test body) := nofun

end YulArtifact

/-! The intrinsic session laws refuse a candidate that never observes an event:
a resumed session whose first action is a credit must show it. -/
namespace IntrinsicSession

open Solidity.Roadmap

/-- The code of an empty compilation. -/
def noCode : Code where
  contracts := []
  main := 0
  roles := fun k => k.elim0
  ctor := fun k => k.elim0
  entry := fun k => k.elim0

/-- An allowed environment whose every action is a credit. -/
def crediting : SessionEnv where
  deployer := Address.zero
  deployNonce := ⟨0, by decide⟩
  deployValue := ⟨0, by decide⟩
  deployArgs := []
  balance := fun _ => ⟨0, by decide⟩
  hasCode := fun _ _ => false
  requests := fun _ _ => some (.credit Address.zero ⟨1, by decide⟩)
  callee := fun _ => .answer (.success [])

example : crediting.Allowed := ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- A candidate without events is refused, whatever its view. -/
example (F : Fixed) (I : IntrinsicSpec) (V : View I)
    (silent : ∀ p e r, (I.lang.sem p e r).events = []) : ¬ Laws F I V := by
  intro laws
  have allowed : I.lang.Allowed (I.ofSession crediting) := by
    rw [I.allowed_iff, I.session_of]
    exact ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  let start : TypedWorld :=
    ⟨noCode, ContractWorld.World.empty noCode.catalog (funds crediting.balance) noCode.roles⟩
  obtain ⟨r, _, shown⟩ := (laws.credited (V.resume start) (I.ofSession crediting) [] 0
    noCode start.world Address.zero ⟨1, by decide⟩ allowed (laws.starts start _ allowed)
    (by rw [I.session_of]; rfl)).1
  rw [silent] at shown
  exact absurd (List.prefix_nil.mp shown) (by simp)

/-- A resource-failure classification that admits no bound is refused. -/
example (F : Fixed) (I : IntrinsicSpec) (V : View I) (never : ∀ r, ¬ I.NoFail r) :
    ¬ Laws F I V := by
  intro laws
  have allowed : I.lang.Allowed (I.ofSession crediting) := by
    rw [I.allowed_iff, I.session_of]
    exact ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  let start : TypedWorld :=
    ⟨noCode, ContractWorld.World.empty noCode.catalog (funds crediting.balance) noCode.roles⟩
  obtain ⟨r, good, _⟩ := laws.boundary_observed _ _ _ _ _ (laws.starts start _ allowed)
  exact never r good.2

end IntrinsicSession

/-! The decision model at its boundaries: equality passes and one line over fails,
mixed lines count as code, audits padding and value-equal or raised proposals change
nothing, and an unlisted area allows no prose. -/
namespace ProseRatio

def scope : Scope String where
  area p := p.headD ""
  generated := [["Solidity.lean"]]
  kind p := if p.headD "" = "Solidity" then .source
    else if p.headD "" = "docs" then .docs else .outside

/-- Comments in `Solidity`: half a line per code line, plus one. -/
def half : Allowance := ⟨⟨1, 2, by decide⟩, 1⟩

def pol : Policy String := ⟨scope, [(("Solidity", .comment), half)]⟩

def lean (code comments : Nat) : File :=
  ⟨["Solidity", "A.lean"], List.replicate code [.code "x"] ++
    List.replicate comments [.code " ", .comment "-- c"]⟩

example : accepts pol [lean 4 3] = true := by decide
example : accepts pol [lean 4 4] = false := by decide
example : accepts pol [lean 0 1] = true := by decide
example : accepts pol [⟨["Solidity", "B.lean"], [[.code "x ", .comment "-- c"],
    [.code "y", .comment "-- d"]]⟩] = true := by decide
example : accepts pol [lean 4 3, ⟨["docs", "audits", "a.md"], [[], []]⟩] = true := by decide
example : accepts pol [lean 4 3, ⟨["docs", "a.md"], [[]]⟩] = false := by decide
example : accepts pol [lean 4 3, ⟨["Solidity", "C.lean"], [[.comment "-- e"]]⟩] = false := by decide
example : accepts pol [lean 4 3, ⟨["Solidity", "C.lean"], [[.code "z"], [.code "w"]]⟩] =
    true := by decide
example : accepts (pol.shrink [(("Solidity", .comment), ⟨⟨1, 1, by decide⟩, 9⟩)])
    [lean 4 4] = false := by decide
example : accepts ((⟨scope, [(("Solidity", .comment), ⟨⟨2, 4, by decide⟩, 1⟩)]⟩ :
    Policy String).shrink [(("Solidity", .comment), half)]) [lean 4 3] = true := by decide
example : accepts (pol.shrink []) [lean 4 1] = false := by decide

end ProseRatio

end Solidity.Goals
