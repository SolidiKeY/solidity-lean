import Solidity.Yul.LocalBlock

/-! Lean-only modal composition for the actual pure LOCAL Source runner.
The formula explicitly captures the initial Source state; it is not a uniform
Source/G51 normalization or general Source statement/session theorem. -/
namespace Solidity.Yul.LocalBlockLogic

theorem completed_unique {ctx control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (state : LocalState ctx.env ctx.tys) {left right first second}
    (one : runLocalBlock ctx code policy left state = some first)
    (two : runLocalBlock ctx code policy right state = some second) : first = second := by
  have a := runLocalBlock_stable ctx code policy state (Nat.le_max_left left right) one
  have b := runLocalBlock_stable ctx code policy state (Nat.le_max_right left right) two
  exact Option.some.inj (a.symm.trans b)

def holds {ctx control} (mode : Solidity.Modality)
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (post : LocalBlockOutcome ctx control → Prop) (state : LocalState ctx.env ctx.tys) : Prop :=
  match mode with
  | .box => ∀ fuel result, runLocalBlock ctx code policy fuel state = some result → post result
  | .diamond => ∃ fuel result, runLocalBlock ctx code policy fuel state = some result ∧ post result

theorem holds_iff_raw {ctx control} (mode : Solidity.Modality)
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (post : LocalBlockOutcome ctx control → Prop) (state : LocalState ctx.env ctx.tys) :
    holds mode code policy post state ↔
      WordAdapter.rawHolds mode code policy (fun result => post (LocalBlockOutcome.ofWord state result))
        ⟨Fin.elim0,localWordCells ctx state.1⟩ := by
  cases mode with
  | box =>
      constructor
      · intro valid fuel raw done
        apply valid fuel (LocalBlockOutcome.ofWord state raw)
        unfold runLocalBlock
        rw [done]
        rfl
      · intro valid fuel result done
        unfold runLocalBlock at done
        cases actual : WordAdapter.run code policy fuel ⟨Fin.elim0,localWordCells ctx state.1⟩ with
        | none => rw [actual] at done; cases done
        | some raw =>
            rw [actual] at done
            cases done
            exact valid fuel raw actual
  | diamond =>
      constructor
      · rintro ⟨fuel,result,done,valid⟩
        unfold runLocalBlock at done
        cases actual : WordAdapter.run code policy fuel ⟨Fin.elim0,localWordCells ctx state.1⟩ with
        | none => rw [actual] at done; cases done
        | some raw =>
            rw [actual] at done
            cases done
            exact ⟨fuel,raw,actual,valid⟩
      · rintro ⟨fuel,raw,done,valid⟩
        refine ⟨fuel,LocalBlockOutcome.ofWord state raw,?_,valid⟩
        unfold runLocalBlock
        rw [done]
        rfl

def formula {ctx control} (mode : Solidity.Modality)
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (post : LocalBlockOutcome ctx control → Prop) (state : LocalState ctx.env ctx.tys) :
    Logic.Fml (0 + wordCellCount (localExternalTypes ctx)) :=
  WordAdapter.formula mode code policy (fun result => post (LocalBlockOutcome.ofWord state result))

theorem formula_iff {ctx control} (mode : Solidity.Modality)
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (post : LocalBlockOutcome ctx control → Prop) (state : LocalState ctx.env ctx.tys) :
    (formula mode code policy post state).holds
      (WordState.pack (n := 0) ⟨Fin.elim0,localWordCells ctx state.1⟩) ↔
        holds mode code policy post state :=
  (WordAdapter.formula_iff mode code policy _ _).trans
    (holds_iff_raw mode code policy post state).symm

theorem rule_exists {ctx control} (mode : Solidity.Modality)
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (post : LocalBlockOutcome ctx control → Prop) (state : LocalState ctx.env ctx.tys) :
    ∃ premise, Nonempty (Logic.Rule (formula mode code policy post state) premise) :=
  WordAdapter.rule_exists mode code policy _

/-- Concrete one-step word rule soundness for this actual initial Source state.
The initial-state parameter and completion modalities are explicit. -/
theorem rule_sound {ctx control} (mode : Solidity.Modality)
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (post : LocalBlockOutcome ctx control → Prop) (state : LocalState ctx.env ctx.tys) :
    ∃ premise : Logic.Fml (0 + wordCellCount (localExternalTypes ctx)),
      holds mode code policy post state ↔
        premise.holds (WordState.pack (n := 0) ⟨Fin.elim0,localWordCells ctx state.1⟩) := by
  obtain ⟨premise,sound⟩ := WordAdapter.rule_sound mode code policy
    (fun result => post (LocalBlockOutcome.ofWord state result))
  exact ⟨premise,(holds_iff_raw mode code policy post state).trans (sound _)⟩

/-- A supplied ACTUAL completion reduces both modalities to the full
outcome postcondition. No termination assumption is hidden in the rule. -/
theorem completion_iff {ctx control} (mode : Solidity.Modality)
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (post : LocalBlockOutcome ctx control → Prop) (state : LocalState ctx.env ctx.tys)
    {fuel : Nat} {result : LocalBlockOutcome ctx control}
    (done : runLocalBlock ctx code policy fuel state = some result) :
    holds mode code policy post state ↔ post result := by
  cases mode with
  | box =>
      constructor
      · intro valid
        exact valid fuel result done
      · intro valid otherFuel other finished
        have same : other = result := completed_unique code policy state finished done
        cases same
        exact valid
  | diamond =>
      constructor
      · rintro ⟨otherFuel, other, finished, valid⟩
        have same : other = result := completed_unique code policy state finished done
        cases same
        exact valid
      · intro valid
        exact ⟨fuel, result, done, valid⟩

theorem formula_completion_iff {ctx control} (mode : Solidity.Modality)
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (post : LocalBlockOutcome ctx control → Prop) (state : LocalState ctx.env ctx.tys)
    {fuel : Nat} {result : LocalBlockOutcome ctx control}
    (done : runLocalBlock ctx code policy fuel state = some result) :
    (formula mode code policy post state).holds
      (WordState.pack (n := 0) ⟨Fin.elim0, localWordCells ctx state.1⟩) ↔ post result :=
  (formula_iff mode code policy post state).trans
    (completion_iff mode code policy post state done)

/-- The actual existing Lean-only rule and its premise at the explicitly
captured initial state; valid only under the concrete completion equation. -/
theorem rule_completion {ctx control} (mode : Solidity.Modality)
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (post : LocalBlockOutcome ctx control → Prop) (state : LocalState ctx.env ctx.tys)
    {fuel : Nat} {result : LocalBlockOutcome ctx control}
    (done : runLocalBlock ctx code policy fuel state = some result) :
    ∃ premise : Logic.Fml (0 + wordCellCount (localExternalTypes ctx)),
    ∃ _rule : Logic.Rule (formula mode code policy post state) premise,
      premise.holds (WordState.pack (n := 0) ⟨Fin.elim0, localWordCells ctx state.1⟩) ↔
        post result := by
  obtain ⟨premise, ⟨rule⟩⟩ := rule_exists mode code policy post state
  exact ⟨premise, rule, (rule.sound _).symm.trans
    (formula_completion_iff mode code policy post state done)⟩

end Solidity.Yul.LocalBlockLogic
