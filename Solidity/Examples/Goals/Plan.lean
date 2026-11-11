import Solidity.Goals.Plan

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

/-! The intrinsic session vocabulary: a resumed environment stays allowed, a
world funded by opening balances shows them again, and a candidate that never
observes an event satisfies the laws for no view. -/
namespace IntrinsicSession

open Solidity.Roadmap
open Solidity.Lowering.V08.EnvironmentProjection

example (e : SessionEnv) (allowed : e.Allowed) (h : List Event) (n : Nat)
    (balance : Address → Roadmap.Word) : (after e h n balance).Allowed :=
  ⟨fun h' => allowed.1 (h ++ h'), fun h' a pre => allowed.2.1 (h ++ h') a pre,
    fun h' a v i s code => by
      show e.callee (h ++ (h' ++ [.call a v i s])) = .answer (.success [])
      rw [← List.append_assoc]
      exact allowed.2.2 (h ++ h') a v i s code⟩

theorem balances_funds {K : Type} {contracts : K → Contract} (b : Address → Roadmap.Word)
    (roles : K → ContractWorld.Role) :
    balances (ContractWorld.World.empty contracts (funds b) roles) = b := by
  funext a
  show lowerWord (liftWord (b (lowerAddress (liftAddress a)))) = b a
  rw [lower_lift_address, lower_lift_word]

/-- The code of an empty compilation. -/
def noCode : Code where
  contracts := []
  main := 0
  roles := fun k => k.elim0
  ctor := fun k => k.elim0
  entry := fun k => k.elim0

/-- An allowed environment whose first action is a credit. -/
def crediting : SessionEnv where
  deployer := Address.zero
  deployNonce := ⟨0, by decide⟩
  deployValue := ⟨0, by decide⟩
  deployArgs := []
  balance := fun _ => ⟨0, by decide⟩
  hasCode := fun _ _ => false
  requests := fun _ _ => some (.credit Address.zero ⟨1, by decide⟩)
  callee := fun _ => .answer (.success [])

/-- A candidate without events is refused: the credit must be observed. -/
example (F : Fixed) (I : IntrinsicSpec) (V : View I)
    (silent : ∀ p e r, (I.lang.sem p e r).events = []) : ¬ Laws F I V := by
  intro laws
  have allowed : I.lang.Allowed (I.ofSession crediting) := by
    rw [I.allowed_iff, I.session_of]
    exact ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  have observed := (laws.credited noCode
    (ContractWorld.World.empty noCode.catalog (funds crediting.balance) noCode.roles)
    (I.ofSession crediting) Address.zero ⟨1, by decide⟩ allowed
    (by rw [I.session_of, balances_funds]) (by rw [I.session_of]; rfl)).1
  obtain ⟨r, _, events⟩ := observed
  exact events (silent _ _ r)

end IntrinsicSession

end Solidity.Goals
