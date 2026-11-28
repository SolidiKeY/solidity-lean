import Solidity.Source.ExprProgress
import Solidity.Semantics.RunFuel


namespace Solidity.Theory.Progress

open Solidity.Source


inductive Ends {α : Type} : Except Halt α → Prop where
  | returns (a : α) : Ends (.ok a)
  | panics (c : PanicCode) : Ends (.error (.revert (panicData c)))
  | reverts (d : Roadmap.Bytes) (hd : ∀ c, d ≠ panicData c) : Ends (.error (.revert d))
  | outOfFuel : Ends (.error .timeout)

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

theorem Ends.notStuck {α : Type} {r : Except Halt α} (h : Ends r) : ∀ w, r ≠ .error (.stuck w) := by
  intro w hw
  cases h <;> cases hw

theorem ns_iff_ends {E : Env} {Γ : RCtx} {α : Type} (m : EM E Γ α) :
    NS m ↔ ∀ x, Ends (m.run x).1 :=
  ⟨fun h x => ends_of_notStuck _ (h x), fun h x w => (h x).notStuck w⟩

theorem NS.ends {E : Env} {Γ : RCtx} {α : Type} {m : EM E Γ α} (h : NS m) (x : Locals E.layout Γ × St E) :
    Ends (m.run x).1 :=
  (ns_iff_ends m).1 h x

theorem not_ends_stuck {α : Type} (w : String) : ¬ Ends (.error (.stuck w) : Except Halt α) :=
  fun h => h.notStuck w rfl


inductive CoreEnds {α : Type} : TRes α → Prop where
  | returns (a : α) : CoreEnds (.ok a)
  | reverts : CoreEnds (.error .revert)
  | revertsWith (d : List UInt8) : CoreEnds (.error (.revertWith d))
  | panics : CoreEnds (.error .panic)
  | diverges : CoreEnds (.error .diverge)
  | exhausted : CoreEnds (.error .exhausted)

theorem coreEnds {α : Type} : (r : TRes α) → CoreEnds r
  | .ok a => .returns a
  | .error .revert => .reverts
  | .error (.revertWith d) => .revertsWith d
  | .error .panic => .panics
  | .error .diverge => .diverges
  | .error .exhausted => .exhausted

theorem Prog.run_ends {C : Contract} {Γ Γ' : Ctx} (σ : State C Γ) (P : Prog C Γ Γ') :
    CoreEnds (Prog.run σ P) :=
  coreEnds _

theorem Prog.runF_ends {C : Contract} {Γ Γ' : Ctx} (n : Nat) (P : Prog C Γ Γ') (σ : State C Γ) :
    CoreEnds (Prog.runF n P σ) :=
  coreEnds _

theorem Stmt.runF_ends {C : Contract} {Γ Γ' : Ctx} (n : Nat) (s : Stmt C Γ Γ') (σ : State C Γ) :
    CoreEnds (Stmt.runF n s σ) :=
  coreEnds _

end Solidity.Theory.Progress
