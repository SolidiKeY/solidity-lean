import Solidity.Correctness.IntrinsicSession.Laws.Common

/-!
# The intrinsic session: the boundary laws

Seven fields of `Solidity.Goals.IntrinsicSession.Laws F (spec F) (view F)` (step
`is0p-session-laws`, lane boundary), each a theorem `Laws.<field>` whose statement is that field:
`starts`, `boundary_observed`, `boundary_code`, `listed_boundary`, `idle`, `dropped`, `credited`.
-/

namespace Solidity.Semantics.IntrinsicSession

open Solidity.Roadmap
open Solidity.Goals.IntrinsicSession (Code TypedWorld Good Observed Funded Credited outcomes)
open Solidity.ContractWorld (World)
open Solidity.Lowering.V08.EnvironmentProjection (liftWord liftAddress)

/-- The outcomes the laws read are those `lastOutcome` reads. -/
theorem outcomes_eq (h : List Event) : outcomes h = h.filterMap outcomeIn :=
  congrArg (h.filterMap ·) (funext fun ev => by cases ev <;> rfl)

/-- A credit whose sum is a word leaves the world `Credited`. -/
theorem credit_credited {contracts : List Contract} (w : World (catalog contracts))
    (target : Address) (value : Roadmap.Word) {sum : ContractWorld.Word}
    (word : PrimTy.ofInt? .uint ((w.funds (liftAddress target)).1 + (liftWord value).1) =
      some sum) :
    Credited w (liftAddress target) sum (credit w target value).world := by
  simp only [credit, word]
  exact ⟨rfl, rfl, fun _ ne => if_neg ne, if_pos rfl⟩

namespace Laws

variable (F : Fixed)

/-- **A session resumed at a typed world starts at that world.** -/
theorem starts : ∀ (t : TypedWorld) (en : (spec F).lang.Env), (spec F).lang.Allowed en →
    (view F).Boundary ((view F).resume t) en [] 0 t :=
  fun t en _ => Boundary.resume F t en

/-- **A boundary's history is observed.** -/
theorem boundary_observed : ∀ x en h n t, (view F).Boundary x en h n t →
    Observed (spec F) ((spec F).ofWorld x) en h :=
  fun _ _ _ _ _ b => Boundary.observed b

/-- **A boundary's world has the session's code.** -/
theorem boundary_code : ∀ x en h n t, (view F).Boundary x en h n t →
    t.code = ((view F).typed x).code :=
  fun _ _ _ _ _ b => Boundary.code b

/-- **Every listed world is the world of a boundary the prefix has reached.** -/
theorem listed_boundary : ∀ x en r, Good (spec F) r →
    ∀ ω ∈ (spec F).worlds ((spec F).ofWorld x) en r,
      ∃ h n, (view F).Boundary x en h n ((view F).typed ω) ∧
        h <+: ((spec F).lang.sem ((spec F).ofWorld x) en r).events :=
  fun _ _ _ good _ mem => IntrinsicSession.listed_boundary good mem

/-- **No further action**: the history is complete, and the session completes
once it has an outcome. -/
theorem idle : ∀ x en h n t, (spec F).lang.Allowed en → (view F).Boundary x en h n t →
    ((spec F).session en).requests h n = none →
    (∀ r, Good (spec F) r → h <+: ((spec F).lang.sem ((spec F).ofWorld x) en r).events →
      ((spec F).lang.sem ((spec F).ofWorld x) en r).events = h) ∧
    (outcomes h ≠ [] → ∃ r, Good (spec F) r ∧
      ((spec F).lang.sem ((spec F).ofWorld x) en r).events = h ∧
      ((spec F).lang.sem ((spec F).ofWorld x) en r).final ≠ none) := by
  rintro x en h n t - b ended
  have below := b
  obtain ⟨w, rfl, st⟩ := b
  have b : (view F).Boundary x en h n ⟨x.code, w⟩ := ⟨w, rfl, st⟩
  refine ⟨fun r good pre => ?_, fun has => ?_⟩
  · by_cases le : n ≤ r.horizon
    · exact (Boundary.idle b ended good le).1
    · have short := Boundary.below below good (by omega)
      exact short.eq_of_length (Nat.le_antisymm short.length_le pre.length_le)
  · obtain ⟨events, final⟩ := Boundary.idle b ended (good_upto F (n + 1)) (Nat.le_succ n)
    refine ⟨_, good_upto F (n + 1), events, ?_⟩
    show ((spec F).lang.sem x en (Bound.upto (n + 1))).final ≠ none
    rw [final (Nat.lt_succ_self n), lastOutcome, ← outcomes_eq]
    cases eq : outcomes h with
    | nil => exact absurd eq has
    | cons o os => simp [List.getLast?_cons]

/-- **An unaffordable request is dropped**: the next action, same history and world. -/
theorem dropped : ∀ x en h n t (q : Request), (spec F).lang.Allowed en →
    (view F).Boundary x en h n t →
    ((spec F).session en).requests h n = some (.request q) →
    ¬ Funded F ((spec F).session en) h q → (view F).Boundary x en h (n + 1) t := by
  rintro x en h n t q - ⟨w, rfl, st⟩ next unfunded
  exact Boundary.dropped (F := F) ⟨w, rfl, st⟩ next unfunded

/-- **A credit is the next event**; when the sum is a word, the boundary after it
has the target's global funds raised and nothing else changed. -/
theorem credited : ∀ x en h n (code : Code) (cw : ContractWorld.World code.catalog)
      (target : Address) (value : Roadmap.Word),
    (spec F).lang.Allowed en → (view F).Boundary x en h n ⟨code, cw⟩ →
    ((spec F).session en).requests h n = some (.credit target value) →
    let p := (spec F).ofWorld x
    let done := Event.credit target value
    Observed (spec F) p en (h ++ [done]) ∧
    (∀ r, Good (spec F) r → h <+: ((spec F).lang.sem p en r).events →
      ((spec F).lang.sem p en r).events = h ∨
        h ++ [done] <+: ((spec F).lang.sem p en r).events) ∧
    ∀ sum, PrimTy.ofInt? .uint ((cw.funds (liftAddress target)).1 + (liftWord value).1) =
        some sum →
      ∃ cw' : ContractWorld.World code.catalog, Credited cw (liftAddress target) sum cw' ∧
        (view F).Boundary x en (h ++ [done]) (n + 1) ⟨code, cw'⟩ := by
  rintro x en h n code cw target value - ⟨w, eq, st⟩ next
  cases eq
  have b : (view F).Boundary x en h n ⟨x.code, w⟩ := ⟨w, rfl, st⟩
  exact ⟨Boundary.observed (Boundary.credited b next),
    fun r good pre => Boundary.events_cases b next rfl good pre,
    fun sum word => ⟨_, credit_credited w target value word, Boundary.credited b next⟩⟩

end Laws

end Solidity.Semantics.IntrinsicSession
