import SolidityBridge.Adversary

/-!
An operational callee induces precisely the policy of its reachable returns.
This checks a fixed adversary, rather than relying only on the maximally
nondeterministic callee as the witness for universal quantification.
-/
namespace Solidity.Bridge.Adversary

variable {C : Contract} {Γ : Ctx} {σ : State C Γ} {J : StateInv C}
  {r a : Val C Γ .uint}

def reachablePolicy (M : Callee σ) : Policy σ := fun o st nt sb =>
  ∃ q₀ q es, M.initial o q₀ ∧ M.system.MTr q₀ es q ∧ M.returns q st nt sb

/-- Lift every internal callee step into the composed LTS, retaining labels. -/
theorem lift_callee_trace {M : Callee σ} {q q' : M.Control} {es : List M.Label}
    (o : Out C σ.H Γ) (ht : M.system.MTr q es q') :
    (callLts J σ r a M).MTr (.active o q) (es.map CallEvent.callee) (.active o q') := by
  induction ht with
  | refl => exact .refl
  | stepL hs _ ih => exact .stepL (.callee hs) ih

private def reachableMeaning (M : Callee σ) : CallCfg σ M → Prop
  | .entry => True
  | .active o q => TRun.transfer r a σ = .ok o ∧ J.at o.st ∧
      ∃ q₀ es, M.initial o q₀ ∧ M.system.MTr q₀ es q
  | .finished out => ∃ es, (lts J σ r a (reachablePolicy M)).MTr .entry es (.finished out)

theorem call_trace_policy {M : Callee σ} {es : List (CallEvent M)}
    {out : COut C σ.H Γ} (ht : (callLts J σ r a M).MTr .entry es (.finished out)) :
    ∃ es', (lts J σ r a (reachablePolicy M)).MTr .entry es' (.finished out) := by
  have step : ∀ {s t : CallCfg σ M} {e : CallEvent M},
      (callLts J σ r a M).Tr s e t →
      reachableMeaning (J := J) (r := r) (a := a) M s →
      reachableMeaning (J := J) (r := r) (a := a) M t := by
    intro s t e hs hm
    cases hs with
    | enter hr hi hstart => exact ⟨hr, hi, _, [], hstart, .refl⟩
    | halt hr => exact ⟨[.halt], .stepL (.halt hr) .refl⟩
    | violation hr hi =>
      exact ⟨[.yield, .violation], .stepL (.enter hr) (.stepL (.violation hi) .refl)⟩
    | callee hs =>
      obtain ⟨hr, hi, q₀, es, hstart, ht⟩ := hm
      exact ⟨hr, hi, q₀, es ++ [_], hstart, LTS.MTr.stepR M.system ht hs⟩
    | resume hret hi =>
      obtain ⟨hr, hexit, q₀, es, hstart, ht⟩ := hm
      exact ⟨[.yield, .resume], .stepL (.enter hr)
        (.stepL (.resume hexit hi ⟨q₀, _, es, hstart, ht, hret⟩) .refl)⟩
  have walk : ∀ {s t : CallCfg σ M} {es : List (CallEvent M)},
      (callLts J σ r a M).MTr s es t →
      reachableMeaning (J := J) (r := r) (a := a) M s →
      reachableMeaning (J := J) (r := r) (a := a) M t := by
    intro s t es hs
    induction hs with
    | refl => exact id
    | stepL hs _ ih => exact fun hm => ih (step hs hm)
  exact walk ht trivial

theorem policy_trace_call {M : Callee σ} {es : List Event} {out : COut C σ.H Γ}
    (ht : (lts J σ r a (reachablePolicy M)).MTr .entry es (.finished out)) :
    ∃ es', (callLts J σ r a M).MTr .entry es' (.finished out) := by
  have step : ∀ {s t : Cfg σ} {e : Event},
      (lts J σ r a (reachablePolicy M)).Tr s e t →
      (match s with
        | .entry => True
        | .waiting o => TRun.transfer r a σ = .ok o
        | .finished out => ∃ es', (callLts J σ r a M).MTr .entry es' (.finished out)) →
      (match t with
        | .entry => True
        | .waiting o => TRun.transfer r a σ = .ok o
        | .finished out => ∃ es', (callLts J σ r a M).MTr .entry es' (.finished out)) := by
    intro s t e hs hm
    cases hs with
    | enter hr => exact hr
    | halt hr => exact ⟨[.halt], .stepL (.halt hr) .refl⟩
    | violation hi => exact ⟨[.violation], .stepL (.violation hm hi) .refl⟩
    | @resume o st nt sb hexit hback choice =>
      obtain ⟨q₀, q, es, hstart, hcallee, hret⟩ := choice
      have hc : (callLts J σ r a M).MTr (.active o q₀)
          (es.map CallEvent.callee) (.active o q) := lift_callee_trace o hcallee
      have hr : (callLts J σ r a M).Tr (.active o q) .resume
          (.finished (.ok ⟨o.st.havoc st nt sb, o.ext⟩)) :=
        CallTr.resume (o := o) hret hback
      exact ⟨.yield :: (es.map CallEvent.callee ++ [.resume]),
        .stepL (.enter hm hexit hstart)
          (LTS.MTr.comp (callLts J σ r a M) hc (.stepL hr .refl))⟩
  have walk : ∀ {s t : Cfg σ} {es : List Event},
      (lts J σ r a (reachablePolicy M)).MTr s es t →
      (match s with
        | .entry => True
        | .waiting o => TRun.transfer r a σ = .ok o
        | .finished out => ∃ es', (callLts J σ r a M).MTr .entry es' (.finished out)) →
      (match t with
        | .entry => True
        | .waiting o => TRun.transfer r a σ = .ok o
        | .finished out => ∃ es', (callLts J σ r a M).MTr .entry es' (.finished out)) := by
    intro s t es hs
    induction hs with
    | refl => exact id
    | stepL hs _ ih => exact fun hm => ih (step hs hm)
  exact walk ht trivial

/-- For each fixed operational adversary, policy abstraction preserves and
reflects completed outcomes. Internal callee labels remain in `callLts`. -/
theorem callSafe_iff_reachablePolicy (M : Callee σ) (m : Modality)
    (post : State C Γ → Prop) :
    CallSafe J σ r a M m post ↔ Safe J σ r a (reachablePolicy M) m post := by
  constructor
  · intro h es out ht
    obtain ⟨es', hc⟩ := policy_trace_call ht
    exact h es' out hc
  · intro h es out ht
    obtain ⟨es', hp⟩ := call_trace_policy ht
    exact h es' out hp

end Solidity.Bridge.Adversary

/-- info: 'Solidity.Bridge.Adversary.callSafe_iff_reachablePolicy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Adversary.callSafe_iff_reachablePolicy
