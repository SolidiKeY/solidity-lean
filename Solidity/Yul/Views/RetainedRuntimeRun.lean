import Solidity.Yul.Views.RetainedRuntimePaths

namespace Solidity.Yul.Views

/-- Observe actual raw runtime values BEFORE any getV conversion. -/
def captureRuntimeRun {E Γ σ} (F : Source.Fr) (prior : List (EntryReferenceScope E))
    (m : Source.EM E Γ (Source.RVal E.layout σ)) (s : Source.EMState E Γ) :=
  let result := m.run s
  let returned := match result.1 with | .ok v => [runtimeScope F v] | .error _ => []
  (result,prior++[entryLocalScope F s.1,entryLocalScope F result.2.1]++returned)

def captureRuntimeValuesRun {E Γ types} (F : Source.Fr) (prior : List (EntryReferenceScope E))
    (m : Source.EM E Γ (Source.RVals E.layout types)) (s : Source.EMState E Γ) :=
  let result := m.run s
  let returned := match result.1 with | .ok vs => [runtimeValuesScope F vs] | .error _ => []
  (result,prior++[entryLocalScope F s.1,entryLocalScope F result.2.1]++returned)

theorem captureRuntimeRun_source {E Γ σ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.RVal E.layout σ)) (s : Source.EMState E Γ) :
    (captureRuntimeRun F prior m s).1=m.run s := rfl

theorem captureRuntimeRun_prefix {E Γ σ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.RVal E.layout σ)) (s : Source.EMState E Γ)
    (scope) (member : scope ∈ prior) : scope ∈ (captureRuntimeRun F prior m s).2 :=
  List.mem_append_left _ (List.mem_append_left _ member)

theorem captureRuntimeRun_return {E Γ σ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.RVal E.layout σ)) (s after : Source.EMState E Γ) (value)
    (run : m.run s=(.ok value,after)) : runtimeScope F value ∈ (captureRuntimeRun F prior m s).2 := by
  unfold captureRuntimeRun
  rw [run]
  exact List.mem_append_right _ List.mem_cons_self

theorem captureRuntimeValuesRun_prefix {E Γ types} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.RVals E.layout types)) (s : Source.EMState E Γ)
    (scope) (member : scope ∈ prior) : scope ∈ (captureRuntimeValuesRun F prior m s).2 :=
  List.mem_append_left _ (List.mem_append_left _ member)

/-- Instrument the EXACT owner left-to-right argument producer. Recursion is
on its actual horizon, with both head and tail at n. Scopes retain successful
heads on later halt. No new evaluator/AST/state or imposed resource bound. This
does not instrument intermediates INSIDE an arbitrary head evalE. -/
def captureArgumentsRun {E Γ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (es : Source.RArgs E Γ types) (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :
    (Except Source.Halt (Source.RVals E.layout types) × Source.EMState E Γ) × List (EntryReferenceScope E) :=
  match n with
  | 0 => captureRuntimeValuesRun F prior (Source.evalArgs G F 0 es) s
  | n+1 => by
    cases es with
    | nil => exact captureRuntimeValuesRun F prior (Source.evalArgs G F (n+1) .nil) s
    | cons head tail => exact
      let first := captureRuntimeRun F prior (Source.evalE G F n head) s
      match first.1.1 with
      | .error error => ((.error error,first.1.2),first.2)
      | .ok value =>
        let rest := captureArgumentsRun G F n tail first.2 first.1.2
        ((rest.1.1.map (Source.RVals.cons value),rest.1.2),rest.2)
termination_by structural n

theorem captureArgumentsRun_source {E Γ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (es : Source.RArgs E Γ types) (prior) (s : Source.EMState E Γ) :
    (captureArgumentsRun G F n es prior s).1=(Source.evalArgs G F n es).run s := by
  induction n generalizing types prior s with
  | zero => rfl
  | succ n ih =>
    cases es with
    | nil => rfl
    | cons head tail =>
      change (captureArgumentsRun G F (n+1) (.cons head tail) prior s).1=
        ((Source.evalE G F n head) >>= fun v => do pure (.cons v (← Source.evalArgs G F n tail))).run s
      rw [Source.Hoare.run_bind]
      unfold captureArgumentsRun captureRuntimeRun
      cases first : (Source.evalE G F n head).run s with
      | mk result after =>
        cases result with
        | error error => simp only [first]
        | ok value =>
          simp only [first]
          rw [ih,Source.Hoare.run_bind]
          cases (Source.evalArgs G F n tail).run after with
          | mk result finalState => cases result <;> rfl

theorem captureArgumentsRun_prefix {E Γ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (es : Source.RArgs E Γ types) (prior) (s : Source.EMState E Γ) (scope)
    (member : scope ∈ prior) : scope ∈ (captureArgumentsRun G F n es prior s).2 := by
  induction n generalizing types prior s with
  | zero => exact captureRuntimeValuesRun_prefix F prior _ s scope member
  | succ n ih =>
    cases es with
    | nil => exact captureRuntimeValuesRun_prefix F prior _ s scope member
    | cons head tail =>
      have retained := captureRuntimeRun_prefix F prior (Source.evalE G F n head) s scope member
      unfold captureArgumentsRun
      dsimp only
      split
      · exact retained
      · exact ih _ _ _ retained

theorem captureArgumentsRun_head {E Γ σ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (head : Source.RExpr E Γ σ) (tail : Source.RArgs E Γ types) (prior)
    (s after : Source.EMState E Γ) (value : Source.RVal E.layout σ)
    (run : (Source.evalE G F n head).run s=(.ok value,after)) :
    runtimeScope F value ∈ (captureArgumentsRun G F (n+1) (.cons head tail) prior s).2 := by
  unfold captureArgumentsRun captureRuntimeRun
  simp only [run]
  apply captureArgumentsRun_prefix
  exact List.mem_append_right _ List.mem_cons_self

/-- Every returned constituent is accounted for, including nested tuples.
Premise is the ACTUAL successful owner run, never a supplied coverage law. -/
theorem captureArgumentsRun_covers {E Γ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (es : Source.RArgs E Γ types) (prior) (s after : Source.EMState E Γ)
    (values : Source.RVals E.layout types) (run : (Source.evalArgs G F n es).run s=(.ok values,after))
    (p : Source.SPath) (member : p ∈ runtimeValuesPaths values) :
    ∃ scope ∈ (captureArgumentsRun G F n es prior s).2, scope.account=F.this ∧ p ∈ scope.paths := by
  induction n generalizing types prior s after with
  | zero => cases run
  | succ n ih =>
    cases es with
    | nil => cases run; cases member
    | cons head tail =>
      change ((Source.evalE G F n head) >>= fun v => do pure (Source.RVals.cons v (← Source.evalArgs G F n tail))).run s=(Except.ok values,after) at run
      rw [Source.Hoare.run_bind] at run
      cases first : (Source.evalE G F n head).run s with
      | mk result mid =>
        rw [first] at run
        cases result with
        | error error => cases run
        | ok value =>
          dsimp only at run
          rw [Source.Hoare.run_bind] at run
          cases remaining : (Source.evalArgs G F n tail).run mid with
          | mk result finalState =>
            rw [remaining] at run
            cases result with
            | error error => cases run
            | ok rest =>
              cases run
              rcases (runtime_cons_member value rest p).mp member with here | later
              · exact ⟨runtimeScope F value,captureArgumentsRun_head G F n head tail prior s mid value first,rfl,here⟩
              · have covered := ih tail (captureRuntimeRun F prior (Source.evalE G F n head) s).2 mid after rest remaining later
                unfold captureArgumentsRun
                dsimp only
                unfold captureRuntimeRun
                simp only [captureRuntimeRun,first] at covered ⊢
                exact covered

end Solidity.Yul.Views
