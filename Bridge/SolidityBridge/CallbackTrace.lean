import SolidityBridge.Adversary
import Cslib.Foundations.Semantics.LTS.Bisimulation

/-!
Observable callback traces and CSLib trace equivalence. Completed outcomes
are labels, so equal traces preserve arbitrary postconditions on returned
storage, ledger and balance. Internal callee labels are hidden, but their
transitions remain in the trace. Infinite computations are not completed
outcomes; invariant-preserving returns are still the callback assumption.
-/
namespace Solidity.Bridge.Adversary

variable {C : Contract} {Γ : Ctx}

inductive Observation (σ : State C Γ) where
  | internal
  | result (out : COut C σ.H Γ)

instance : HasTau (Observation σ) := ⟨.internal⟩

inductive ObservedCfg (σ : State C Γ) where
  | running (M : Callee σ) (q : CallCfg σ M)
  | stopped

inductive ObservedTr (J : StateInv C) (σ : State C Γ) (r a : Val C Γ .uint) :
    ObservedCfg σ → Observation σ → ObservedCfg σ → Prop where
  | internal {M : Callee σ} {q q' : CallCfg σ M} {e : CallEvent M}
      (h : (callLts J σ r a M).Tr q e q') :
      ObservedTr J σ r a (.running M q) .internal (.running M q')
  | result {M : Callee σ} {out : COut C σ.H Γ} :
      ObservedTr J σ r a (.running M (.finished out)) (.result out) .stopped

def observedLts (J : StateInv C) (σ : State C Γ) (r a : Val C Γ .uint) :
    LTS (ObservedCfg σ) (Observation σ) := ⟨ObservedTr J σ r a⟩

variable {J : StateInv C} {σ : State C Γ} {r a : Val C Γ .uint}

def TraceSafe (start : ObservedCfg σ) (Q : COut C σ.H Γ → Prop) : Prop :=
  ∀ labels ∈ (observedLts J σ r a).traces start,
    ∀ out, Observation.result out ∈ labels → Q out

private def FutureSafe (Q : COut C σ.H Γ → Prop) : ObservedCfg σ → Prop
  | .running M q => ∀ es out, (callLts J σ r a M).MTr q es (.finished out) → Q out
  | .stopped => True

private theorem observed_step_safe {Q : COut C σ.H Γ → Prop}
    {s t : ObservedCfg σ} {e : Observation σ}
    (h : (observedLts J σ r a).Tr s e t)
    (hs : FutureSafe (J := J) (r := r) (a := a) Q s) :
    FutureSafe (J := J) (r := r) (a := a) Q t ∧
      ∀ out, e = .result out → Q out := by
  cases h with
  | internal h =>
    exact ⟨fun es out ht => hs (_ :: es) out (.stepL h ht), fun _ he => nomatch he⟩
  | result =>
    exact ⟨trivial, fun out he => by cases he; exact hs [] _ .refl⟩

theorem observed_trace_safe {Q : COut C σ.H Γ → Prop}
    {s t : ObservedCfg σ} {labels : List (Observation σ)}
    (ht : (observedLts J σ r a).MTr s labels t)
    (hs : FutureSafe (J := J) (r := r) (a := a) Q s) :
    ∀ out, Observation.result out ∈ labels → Q out := by
  induction ht with
  | refl => intro out h; cases h
  | stepL h _ ih =>
    obtain ⟨hnext, hevent⟩ := observed_step_safe h hs
    intro out hmem
    rcases List.mem_cons.mp hmem with he | htail
    · exact hevent out he.symm
    · exact ih hnext out htail

theorem lift_observed_trace {M : Callee σ} {q q' : CallCfg σ M}
    {es : List (CallEvent M)} (ht : (callLts J σ r a M).MTr q es q') :
    (observedLts J σ r a).MTr (.running M q)
      (List.replicate es.length .internal) (.running M q') := by
  induction ht with
  | refl => exact .refl
  | stepL h _ ih => exact .stepL (.internal h) ih

theorem callSafe_iff_traceSafe (M : Callee σ) (m : Modality)
    (post : State C Γ → Prop) :
    CallSafe J σ r a M m post ↔
      TraceSafe (J := J) (r := r) (a := a) (.running M .entry) (fun out => out.after m post) := by
  constructor
  · intro h labels hlabels out hmem
    obtain ⟨q, ht⟩ := hlabels
    exact observed_trace_safe ht h out hmem
  · intro h es out ht
    have path : (observedLts J σ r a).MTr (.running M .entry)
        (List.replicate es.length .internal ++ [.result out]) .stopped :=
      LTS.MTr.stepR _ (lift_observed_trace ht) ObservedTr.result
    exact h _ ⟨_, path⟩ out (List.mem_append_right _ (by simp only [List.mem_singleton]))

/-- CSLib trace equivalence preserves callback safety, including every
postcondition on the observed returned state. -/
theorem traceEq_callSafe {M N : Callee σ}
    (h : TraceEq (observedLts J σ r a) (.running M .entry) (.running N .entry))
    (m : Modality) (post : State C Γ → Prop) :
    CallSafe J σ r a M m post ↔ CallSafe J σ r a N m post := by
  rw [callSafe_iff_traceSafe, callSafe_iff_traceSafe]
  unfold TraceSafe
  rw [show (observedLts J σ r a).traces (.running M .entry) =
    (observedLts J σ r a).traces (.running N .entry) from h]

theorem bisim_callSafe {M N : Callee σ} {R : ObservedCfg σ → ObservedCfg σ → Prop}
    (hR : (observedLts J σ r a).IsBisimulation R)
    (h : R (.running M .entry) (.running N .entry))
    (m : Modality) (post : State C Γ → Prop) :
    CallSafe J σ r a M m post ↔ CallSafe J σ r a N m post :=
  traceEq_callSafe (hR.traceEq h) m post

theorem holdsC_iff_observable_traces (I : Fml C []) (σ : State C Γ)
    (r a : Val C Γ .uint) (m : Modality) (φ : Fml C Γ) :
    holdsC I true σ (.modal m (.cons (.transfer r a) .nil) .nil φ) ↔
      ∀ M : Callee σ, TraceSafe (J := I.stateInv true) (r := r) (a := a)
        (.running M .entry) (fun out => out.after m (holdsC I true · φ)) := by
  rw [holdsC_iff_all_callees]
  exact forall_congr' fun M => callSafe_iff_traceSafe M m _

/-- An implementation trace-equivalent to the universal callee can replace
it when checking the calculus's callback modality. -/
theorem holdsC_iff_traceEquivalent_callee (I : Fml C []) (σ : State C Γ)
    (r a : Val C Γ .uint) (M : Callee σ)
    (h : TraceEq (observedLts (I.stateInv true) σ r a)
      (.running (universalCallee σ) .entry) (.running M .entry))
    (m : Modality) (φ : Fml C Γ) :
    holdsC I true σ (.modal m (.cons (.transfer r a) .nil) .nil φ) ↔
      CallSafe (I.stateInv true) σ r a M m (holdsC I true · φ) := by
  rw [← traceEq_callSafe h]
  rw [holdsC_single]
  constructor
  · intro h es out ht
    exact h out (call_trace_sound rfl ht)
  · intro h out ho
    obtain ⟨es, ht⟩ := exec_call_trace rfl ho
    exact h es out ht

/-! Saturation treats internal work as silent, independently of its length. -/

def WeakTraceSafe (start : ObservedCfg σ) (Q : COut C σ.H Γ → Prop) : Prop :=
  ∀ labels ∈ (observedLts J σ r a).saturate.traces start,
    ∀ out, Observation.result out ∈ labels → Q out

private theorem saturated_step_safe {Q : COut C σ.H Γ → Prop}
    {s t : ObservedCfg σ} {e : Observation σ}
    (h : (observedLts J σ r a).STr s e t)
    (hs : FutureSafe (J := J) (r := r) (a := a) Q s) :
    FutureSafe (J := J) (r := r) (a := a) Q t ∧
      ∀ out, e = .result out → Q out := by
  induction h with
  | refl => exact ⟨hs, fun _ he => nomatch he⟩
  | tr _ h _ ihpre ihpost =>
    obtain ⟨hpre, _⟩ := ihpre hs
    obtain ⟨hstep, hevent⟩ := observed_step_safe h hpre
    exact ⟨(ihpost hstep).1, hevent⟩

private theorem saturated_trace_safe {Q : COut C σ.H Γ → Prop}
    {s t : ObservedCfg σ} {labels : List (Observation σ)}
    (ht : (observedLts J σ r a).saturate.MTr s labels t)
    (hs : FutureSafe (J := J) (r := r) (a := a) Q s) :
    ∀ out, Observation.result out ∈ labels → Q out := by
  induction ht with
  | refl => intro out h; cases h
  | stepL h _ ih =>
    obtain ⟨hnext, hevent⟩ := saturated_step_safe h hs
    intro out hmem
    rcases List.mem_cons.mp hmem with he | htail
    · exact hevent out he.symm
    · exact ih hnext out htail

private theorem lift_saturated {s t : ObservedCfg σ} {es : List (Observation σ)}
    (ht : (observedLts J σ r a).MTr s es t) :
    (observedLts J σ r a).saturate.MTr s es t := by
  induction ht with
  | refl => exact .refl
  | stepL h _ ih => exact .stepL (LTS.STr.single _ h) ih

theorem callSafe_iff_weakTraceSafe (M : Callee σ) (m : Modality)
    (post : State C Γ → Prop) :
    CallSafe J σ r a M m post ↔
      WeakTraceSafe (J := J) (r := r) (a := a) (.running M .entry)
        (fun out => out.after m post) := by
  constructor
  · intro h labels hlabels out hmem
    obtain ⟨q, ht⟩ := hlabels
    exact saturated_trace_safe ht h out hmem
  · intro h
    apply (callSafe_iff_traceSafe M m post).mpr
    intro labels hlabels out hmem
    obtain ⟨q, ht⟩ := hlabels
    exact h labels ⟨q, lift_saturated ht⟩ out hmem

theorem weakTraceEq_callSafe {M N : Callee σ}
    (h : TraceEq (observedLts J σ r a).saturate
      (.running M .entry) (.running N .entry))
    (m : Modality) (post : State C Γ → Prop) :
    CallSafe J σ r a M m post ↔ CallSafe J σ r a N m post := by
  rw [callSafe_iff_weakTraceSafe, callSafe_iff_weakTraceSafe]
  unfold WeakTraceSafe
  rw [show (observedLts J σ r a).saturate.traces (.running M .entry) =
    (observedLts J σ r a).saturate.traces (.running N .entry) from h]

/-- Unlike strong trace equality, weak bisimulation permits a callee to
perform additional internal work before producing the same outcome. -/
theorem weakBisim_callSafe {M N : Callee σ} {R : ObservedCfg σ → ObservedCfg σ → Prop}
    (hR : (observedLts J σ r a).IsWeakBisimulation R)
    (h : R (.running M .entry) (.running N .entry))
    (m : Modality) (post : State C Γ → Prop) :
    CallSafe J σ r a M m post ↔ CallSafe J σ r a N m post :=
  weakTraceEq_callSafe (hR.traceEq h) m post

theorem holdsC_iff_weakObservable_traces (I : Fml C []) (σ : State C Γ)
    (r a : Val C Γ .uint) (m : Modality) (φ : Fml C Γ) :
    holdsC I true σ (.modal m (.cons (.transfer r a) .nil) .nil φ) ↔
      ∀ M : Callee σ, WeakTraceSafe (J := I.stateInv true) (r := r) (a := a)
        (.running M .entry) (fun out => out.after m (holdsC I true · φ)) := by
  rw [holdsC_iff_all_callees]
  exact forall_congr' fun M => callSafe_iff_weakTraceSafe M m _

theorem holdsC_iff_weakTraceEquivalent_callee (I : Fml C []) (σ : State C Γ)
    (r a : Val C Γ .uint) (M : Callee σ)
    (h : TraceEq (observedLts (I.stateInv true) σ r a).saturate
      (.running (universalCallee σ) .entry) (.running M .entry))
    (m : Modality) (φ : Fml C Γ) :
    holdsC I true σ (.modal m (.cons (.transfer r a) .nil) .nil φ) ↔
      CallSafe (I.stateInv true) σ r a M m (holdsC I true · φ) := by
  rw [← weakTraceEq_callSafe h]
  rw [holdsC_single]
  constructor
  · intro h es out ht
    exact h out (call_trace_sound rfl ht)
  · intro h out ho
    obtain ⟨es, ht⟩ := exec_call_trace rfl ho
    exact h es out ht

end Solidity.Bridge.Adversary

/-- info: 'Solidity.Bridge.Adversary.holdsC_iff_weakObservable_traces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Adversary.holdsC_iff_weakObservable_traces

/-- info: 'Solidity.Bridge.Adversary.weakBisim_callSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Adversary.weakBisim_callSafe
