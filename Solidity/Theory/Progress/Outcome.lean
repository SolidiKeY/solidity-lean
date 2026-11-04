import Solidity.Source.ExprProgress
import Solidity.Semantics.RunFuel

/-!
# How a well-typed run ends (S4.1)

Type soundness as progress: a run that is never stuck **returns, reverts,
panics, or runs out of fuel or resources**. The repository has two
semantics, and the statement has a different weight in each: for the core
every well-typed program progresses, for the source interpreter the
theorems of `Theory/Progress/Program.lean` cover a fragment.

* **The core run** (`Prog.run`, `Prog.runF`, `Solidity/Semantics/Run.lean`)
  is intrinsically typed: a program is a `Prog C Γ Γ'`, so every inhabitant
  is well typed, and the run is a total function into `TRes`, whose halts
  (`THalt`) are `revert`, `revertWith`, `panic`, `diverge` and `exhausted`;
  there is no `stuck` constructor. Progress holds by construction:
  `Prog.run_ends`, `Prog.runF_ends` state it as the classification
  `CoreEnds`.
* **The source interpreter** (`Solidity/Source/Eval.lean`) has a
  `Halt.stuck` for run-time type mismatches. `Ends r` is the classification
  of a result without `stuck` — returned, panicked (`panicData c`), reverted
  with other data, or out of fuel (`timeout`) — and `NS m` (never `stuck`,
  `Solidity/Source/ExprProgress.lean`) is exactly `∀ x, Ends (m.run x).1`
  (`ns_iff_ends`). The fragment theorems of `Theory/Progress/Fragment.lean`
  and `Theory/Progress/Program.lean` prove `NS`, so they are read through
  this module as progress. The interpreter also uses `stuck` for
  features it does not model (dynamic ABI decoding, `new` of some types,
  some getters, `Source/Eval.lean`), so well-typedness alone does not give
  progress there: the fragment's predicates exclude those nodes.

Gas: neither semantics models gas today (D2 is lane X03's), so no run
ends by running out of gas; the resource ends are the fuel horizon
(`timeout`), `diverge` and `exhausted`.
-/

namespace Solidity.Theory.Progress

open Solidity.Source

/-! ## The source interpreter -/

/-- **How a source run may end**: every result but `stuck`. A revert whose
data is a `Panic(uint256)` encoding of a `PanicCode` is a panic; any other
revert data (`Error(string)`, a custom error, empty) is a revert. The split
reads the data only, as a caller does: user code can produce panic data
(a rethrown `bytes` value, a user-declared `error Panic(uint256)`). -/
inductive Ends {α : Type} : Except Halt α → Prop where
  | returns (a : α) : Ends (.ok a)
  | panics (c : PanicCode) : Ends (.error (.revert (panicData c)))
  | reverts (d : Roadmap.Bytes) (hd : ∀ c, d ≠ panicData c) : Ends (.error (.revert d))
  | outOfFuel : Ends (.error .timeout)

/-- A result that is not `stuck` ends in one of the four ways. -/
theorem ends_of_notStuck {α : Type} (r : Except Halt α) (h : ∀ w, r ≠ .error (.stuck w)) : Ends r := by
  cases r with
  | ok a => exact .returns a
  | error e =>
    cases e with
    | revert d =>
      by_cases hp : ∃ c, d = panicData c
      · obtain ⟨c, rfl⟩ := hp
        exact .panics c
      · exact .reverts d fun c hc => hp ⟨c, hc⟩
    | stuck w => exact absurd rfl (h w)
    | timeout => exact .outOfFuel

/-- An ending is never `stuck`. -/
theorem Ends.notStuck {α : Type} {r : Except Halt α} (h : Ends r) : ∀ w, r ≠ .error (.stuck w) := by
  intro w hw
  cases h <;> cases hw

/-- **Never `stuck` is progress**: from every state, the run ends in one of
the four ways. -/
theorem ns_iff_ends {E : Env} {Γ : RCtx} {α : Type} (m : EM E Γ α) :
    NS m ↔ ∀ x, Ends (m.run x).1 :=
  ⟨fun h x => ends_of_notStuck _ (h x), fun h x w => (h x).notStuck w⟩

/-- The direction the fragment theorems are read through. -/
theorem NS.ends {E : Env} {Γ : RCtx} {α : Type} {m : EM E Γ α} (h : NS m) (x : Locals E.layout Γ × St E) :
    Ends (m.run x).1 :=
  (ns_iff_ends m).1 h x

/-- A stuck result does not end (the negative control of `Ends`). -/
theorem not_ends_stuck {α : Type} (w : String) : ¬ Ends (.error (.stuck w) : Except Halt α) :=
  fun h => h.notStuck w rfl

/-! ## The core run -/

/-- **How a core run may end**: returned, reverted (with or without data),
panicked, diverged (`diverge`: the loop bound of `Prog.runF` reached, or a
loop `Prog.run` never leaves) or out of resources (`exhausted`). -/
inductive CoreEnds {α : Type} : TRes α → Prop where
  | returns (a : α) : CoreEnds (.ok a)
  | reverts : CoreEnds (.error .revert)
  | revertsWith (d : List UInt8) : CoreEnds (.error (.revertWith d))
  | panics : CoreEnds (.error .panic)
  | diverges : CoreEnds (.error .diverge)
  | exhausted : CoreEnds (.error .exhausted)

/-- Every core result ends: `THalt` has no `stuck`. -/
theorem coreEnds {α : Type} : (r : TRes α) → CoreEnds r
  | .ok a => .returns a
  | .error .revert => .reverts
  | .error (.revertWith d) => .revertsWith d
  | .error .panic => .panics
  | .error .diverge => .diverges
  | .error .exhausted => .exhausted

/-- **Progress of the core run**: a (necessarily well-typed) program run
from any state ends. -/
theorem Prog.run_ends {C : Contract} {Γ Γ' : Ctx} (σ : State C Γ) (P : Prog C Γ Γ') :
    CoreEnds (Prog.run σ P) :=
  coreEnds _

/-- **Progress of the core run with fuel.** -/
theorem Prog.runF_ends {C : Contract} {Γ Γ' : Ctx} (n : Nat) (P : Prog C Γ Γ') (σ : State C Γ) :
    CoreEnds (Prog.runF n P σ) :=
  coreEnds _

/-- **Progress of one core statement with fuel.** -/
theorem Stmt.runF_ends {C : Contract} {Γ Γ' : Ctx} (n : Nat) (s : Stmt C Γ Γ') (σ : State C Γ) :
    CoreEnds (Stmt.runF n s σ) :=
  coreEnds _

end Solidity.Theory.Progress
