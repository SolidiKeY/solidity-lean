import Solidity.Yul.Views.RetainedForIteration

/-! Actual Source for initialization composes with an explicit iteration
observer. Initializer scope captures survive the iteration and restoration.
Unexpected control outcomes keep the owner's existing stuck errors unchanged. -/
namespace Solidity.Yul.Views

def observeForLoop {E Γ Γ₁ Γ₂ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (init : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.ROptBool E Γ₁) (post : Source.ROptExpr E Γ₁) (body : Source.RStmt E R M ⟨true,u⟩ Γ₁ Γ₂)
    (initializer : StatementObserver G F n nps ph init) (iteration : ForIterationObserver G F n nps ph condition post body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  let first := initializer.observe prior l s
  match first.1.1 with
  | .error error => ((.error error,first.1.2),first.2)
  | .ok (.normal l1) =>
    let step := iteration.observe first.2 l1 first.1.2
    let result := match step.1.1 with
      | .error error => (.error error,step.1.2)
      | .ok (.normal l2) => ((do let restored ← Source.EM.lift (l2.restore Γ); pure (.normal restored)) :
          Source.EM E [] (Source.Out E.layout Γ Γ)).run step.1.2
      | .ok (.ret l2) => ((do let restored ← Source.EM.lift (l2.restore Γ); pure (.ret restored)) :
          Source.EM E [] (Source.Out E.layout Γ Γ)).run step.1.2
      | .ok (.brk _) | .ok (.cont _) => (.error (.stuck "for loop"),step.1.2)
    (result,step.2)
  | .ok (.brk _) | .ok (.cont _) | .ok (.ret _) => ((.error (.stuck "for initializer"),first.1.2),first.2)

theorem observeForLoop_source {E Γ Γ₁ Γ₂ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (init : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.ROptBool E Γ₁) (post : Source.ROptExpr E Γ₁) (body : Source.RStmt E R M ⟨true,u⟩ Γ₁ Γ₂)
    (initializer : StatementObserver G F n nps ph init) (iteration : ForIterationObserver G F n nps ph condition post body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (observeForLoop G F n nps ph init condition post body initializer iteration prior l s).1=
      (Source.execS G F (n+1) nps ph (.forLoop (l:=lp) init condition post body) l).run s := by
  unfold observeForLoop
  dsimp only
  rw [Source.execS,Source.Hoare.run_bind,← initializer.source]
  cases first : (initializer.observe prior l s).1 with
  | mk result after =>
    cases result with
    | error error => rfl
    | ok out =>
      cases out with
      | normal l1 =>
        dsimp only
        rw [Source.Hoare.run_bind,← iteration.source]
        cases step : (iteration.observe (initializer.observe prior l s).2 l1 after).1 with
        | mk result finalState =>
          cases result with
          | error error => rfl
          | ok out => cases out <;> rfl
      | brk l1 => rfl
      | cont l1 => rfl
      | ret l1 => rfl

/-- Captured initializer scopes survive all iteration and restoration outcomes. -/
theorem observeForLoop_init_scopes {E Γ Γ₁ Γ₂ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (init : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.ROptBool E Γ₁) (post : Source.ROptExpr E Γ₁) (body : Source.RStmt E R M ⟨true,u⟩ Γ₁ Γ₂)
    (initializer : StatementObserver G F n nps ph init) (iteration : ForIterationObserver G F n nps ph condition post body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (scope) (member : scope∈(initializer.observe prior l s).2) :
    scope∈(observeForLoop G F n nps ph init condition post body initializer iteration prior l s).2 := by
  unfold observeForLoop
  dsimp only
  cases first : (initializer.observe prior l s).1.1 with
  | error error => exact member
  | ok out =>
    cases out with
    | normal l1 => exact iteration.prior _ l1 _ scope member
    | brk l1 => exact member
    | cont l1 => exact member
    | ret l1 => exact member

/-- After normal initialization, the complete iteration inventory survives
loop-scope restoration, even if restoration fails. -/
theorem observeForLoop_iteration_scopes {E Γ Γ₁ Γ₂ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (init : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.ROptBool E Γ₁) (post : Source.ROptExpr E Γ₁) (body : Source.RStmt E R M ⟨true,u⟩ Γ₁ Γ₂)
    (initializer : StatementObserver G F n nps ph init) (iteration : ForIterationObserver G F n nps ph condition post body)
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (l1 : Source.Locals E.layout Γ₁)
    (s after : Source.EMState E []) (run : (initializer.observe prior l s).1=(.ok (.normal l1),after)) :
    (observeForLoop G F n nps ph init condition post body initializer iteration prior l s).2=
      (iteration.observe (initializer.observe prior l s).2 l1 after).2 := by
  simp only [observeForLoop,run]

/-- An exact conditional composition, not a general iteration producer. -/
def forLoopStatementObserver {E Γ Γ₁ Γ₂ R M} {lp u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (init : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁)
    (condition : Source.ROptBool E Γ₁) (post : Source.ROptExpr E Γ₁) (body : Source.RStmt E R M ⟨true,u⟩ Γ₁ Γ₂)
    (initializer : StatementObserver G F n nps ph init) (iteration : ForIterationObserver G F n nps ph condition post body) :
    StatementObserver G F (n+1) nps ph (.forLoop (l:=lp) init condition post body) where
  observe := observeForLoop G F n nps ph init condition post body initializer iteration
  source := observeForLoop_source G F n nps ph init condition post body initializer iteration (lp:=lp)
  prior := fun prior l s scope member => observeForLoop_init_scopes G F n nps ph init condition post body initializer iteration
    prior l s scope (initializer.prior prior l s scope member)

end Solidity.Yul.Views
