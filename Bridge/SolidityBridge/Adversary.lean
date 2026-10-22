import Solidity.Calculus.CallbackHolds
import Cslib.Foundations.Semantics.LTS.Basic

/-!
# An explicit adversary at a payment boundary

This operational LTS is defined independently of `ExecS`: the payment runs,
the contract yields, and an arbitrary callee chooses the storage, ledger and
balance on resumption. An invariant broken on exit is an observable failure.
Every adversary policy restricts the resume transitions; the universal
policy permits every invariant-preserving choice.

`exec_iff_trace` proves exact agreement with the existing transfer reading,
including halts and invariant violations. `safe_iff_all_policies` quantifies
over all policies. These are finite completed interaction traces, not a
liveness claim about a callee that never returns. The boundary models
arbitrarily many internal reentrant actions by their final global state;
it does not claim a correspondence for `try`, sends, or whole EVM accounts.
The operational `Callee`/`CallTr` layer below also runs every transition of
an arbitrary callee LTS before it returns. Returns are restricted to states
preserving the assumed invariant, as in `ExecS`; a violating return cannot
resume. This assumption is not a proof that every hostile callee preserves it.
-/

namespace Solidity.Bridge.Adversary

variable {C : Contract} {Γ : Ctx}

inductive Cfg (σ : State C Γ) where
  | entry
  | waiting (o : Out C σ.H Γ)
  | finished (o : COut C σ.H Γ)

inductive Event where
  | yield | resume | halt | violation
  deriving DecidableEq, Repr

/-- A callee policy may depend on the state at the yield. -/
abbrev Policy (σ : State C Γ) :=
  Out C σ.H Γ → Storage C → Ledger → PrimTy.uint.Denote → Prop

def anyPolicy (σ : State C Γ) : Policy σ := fun _ _ _ _ => True

inductive Tr (J : StateInv C) (σ : State C Γ) (r a : Val C Γ .uint) (A : Policy σ) :
    Cfg σ → Event → Cfg σ → Prop where
  | enter {o : Out C σ.H Γ} (h : TRun.transfer r a σ = .ok o) :
      Tr J σ r a A .entry .yield (.waiting o)
  | halt {e : THalt} (h : TRun.transfer r a σ = .error e) :
      Tr J σ r a A .entry .halt (.finished (.halt e))
  | violation {o : Out C σ.H Γ} (h : ¬ J.at o.st) :
      Tr J σ r a A (.waiting o) .violation (.finished .violated)
  | resume {o : Out C σ.H Γ} {st : Storage C} {nt : Ledger} {sb : PrimTy.uint.Denote}
      (exit : J.at o.st) (back : J.at (o.st.havoc st nt sb)) (choice : A o st nt sb) :
      Tr J σ r a A (.waiting o) .resume (.finished (.ok ⟨o.st.havoc st nt sb, o.ext⟩))

def lts (J : StateInv C) (σ : State C Γ) (r a : Val C Γ .uint) (A : Policy σ) :
    LTS (Cfg σ) Event := ⟨Tr J σ r a A⟩

variable {J : StateInv C} {σ : State C Γ} {r a : Val C Γ .uint}

/-- Meaning of each control phase, used only in the correspondence proof. -/
def Meaning : Cfg σ → Prop
  | .entry => True
  | .waiting o => TRun.transfer r a σ = .ok o
  | .finished o => ExecS J σ (.transfer r a) o

theorem step_sound (hp : J.pay = true) {A : Policy σ} {s t : Cfg σ} {e : Event}
    (h : (lts J σ r a A).Tr s e t) : Meaning (J := J) (r := r) (a := a) s →
      Meaning (J := J) (r := r) (a := a) t := by
  cases h with
  | enter hrun => exact fun _ => hrun
  | halt hrun => exact fun _ => .transferHalt hp hrun
  | violation hbad => exact fun hrun => .transferViolated hp hrun hbad
  | resume hexit hback _ => exact fun hrun => .transferResume hp hrun hexit hback

theorem trace_sound (hp : J.pay = true) {A : Policy σ} {es : List Event}
    {o : COut C σ.H Γ} (h : (lts J σ r a A).MTr .entry es (.finished o)) :
    ExecS J σ (.transfer r a) o := by
  have transport : ∀ {s t : Cfg σ} {es : List Event}, (lts J σ r a A).MTr s es t →
      Meaning (J := J) (r := r) (a := a) s → Meaning (J := J) (r := r) (a := a) t := by
    intro s t es ht
    induction ht with
    | refl => exact id
    | stepL hs _ ih => exact fun hm => ih (step_sound hp hs hm)
  exact transport h trivial

theorem exec_trace (hp : J.pay = true) {o : COut C σ.H Γ}
    (h : ExecS J σ (.transfer r a) o) :
    ∃ es, (lts J σ r a (anyPolicy σ)).MTr .entry es (.finished o) := by
  cases h with
  | det hf => simp only [Stmt.forksIn, hp, Bool.true_eq_false] at hf
  | transferHalt _ hrun => exact ⟨[.halt], .stepL (.halt hrun) .refl⟩
  | transferViolated _ hrun hbad =>
    exact ⟨[.yield, .violation], .stepL (.enter hrun) (.stepL (.violation hbad) .refl)⟩
  | transferResume _ hrun hexit hback =>
    exact ⟨[.yield, .resume], .stepL (.enter hrun) (.stepL (.resume hexit hback trivial) .refl)⟩

/-- Exact terminal outcomes, without dropping failed invariant checks. -/
theorem exec_iff_trace (hp : J.pay = true) (o : COut C σ.H Γ) :
    ExecS J σ (.transfer r a) o ↔
      ∃ es, (lts J σ r a (anyPolicy σ)).MTr .entry es (.finished o) :=
  ⟨exec_trace hp, fun ⟨_, h⟩ => trace_sound hp h⟩

def Safe (J : StateInv C) (σ : State C Γ) (r a : Val C Γ .uint) (A : Policy σ)
    (m : Modality) (post : State C Γ → Prop) : Prop :=
  ∀ es o, (lts J σ r a A).MTr .entry es (.finished o) → o.after m post

/-- Quantification over every possible callee is exactly the existing
universal callback reading at this boundary. -/
theorem safe_iff_all_policies (hp : J.pay = true) (m : Modality) (post : State C Γ → Prop) :
    (∀ o, ExecS J σ (.transfer r a) o → o.after m post) ↔
      ∀ A : Policy σ, Safe J σ r a A m post := by
  constructor
  · intro h A es o ht
    exact h o (trace_sound hp ht)
  · intro h o ho
    obtain ⟨es, ht⟩ := exec_trace hp ho
    exact h (anyPolicy σ) es o ht

/-- A one-statement modality is universal over that statement's outcomes,
with no intervening frames. -/
theorem holdsC_single (I : Fml C []) (pay : Bool) (σ : State C Γ)
    (s : Stmt C Γ Γ) (m : Modality) (φ : Fml C Γ) :
    holdsC I pay σ (.modal m (.cons s .nil) .nil φ) ↔
      ∀ o, ExecS (I.stateInv pay) σ s o → o.after m (holdsC I pay · φ) := by
  constructor
  · intro h o hs
    cases o with
    | ok o =>
      have hp := h (.ok o) (by simpa only [COut.map, Out.cat] using (ExecP.cons hs ExecP.nil))
      exact hp (.ok ⟨o.st, List.prefix_refl _⟩) ExecF.nil
    | halt e => exact h (.halt e) (ExecP.halt hs)
    | violated => exact h .violated (ExecP.violated hs)
  · intro h o hp
    cases hp with
    | cons hs ht =>
      cases ht
      intro out hf
      cases hf
      exact h _ hs
    | halt hs => exact h _ hs
    | violated hs => exact h _ hs

/-- The calculus's callback modality is exactly safety of all completed
interaction traces against every adversary policy at this payment boundary. -/
theorem holdsC_iff_all_policies (I : Fml C []) (σ : State C Γ)
    (r a : Val C Γ .uint) (m : Modality) (φ : Fml C Γ) :
    holdsC I true σ (.modal m (.cons (.transfer r a) .nil) .nil φ) ↔
      ∀ A : Policy σ, Safe (I.stateInv true) σ r a A m (holdsC I true · φ) :=
  (holdsC_single I true σ (.transfer r a) m φ).trans (safe_iff_all_policies rfl m _)

/-! ## Callees with their own operational semantics -/

/-- An arbitrary callee is an LTS. Its control states may contain program
counters, private state, history and a call stack. Input/output relations
allow nondeterministic entry and return. -/
structure Callee (σ : State C Γ) where
  Control : Type
  Label : Type
  system : LTS Control Label
  initial : Out C σ.H Γ → Control → Prop
  returns : Control → Storage C → Ledger → PrimTy.uint.Denote → Prop

inductive CallCfg (σ : State C Γ) (M : Callee σ) where
  | entry
  | active (o : Out C σ.H Γ) (q : M.Control)
  | finished (o : COut C σ.H Γ)

inductive CallEvent (M : Callee σ) where
  | yield | resume | halt | violation
  | callee (label : M.Label)

/-- The composed contract/callee LTS executes each callee transition. It
does not replace an actual callee trace by a single havoc transition. -/
inductive CallTr (J : StateInv C) (σ : State C Γ) (r a : Val C Γ .uint) (M : Callee σ) :
    CallCfg σ M → CallEvent M → CallCfg σ M → Prop where
  | enter {o : Out C σ.H Γ} {q : M.Control} (h : TRun.transfer r a σ = .ok o)
      (hi : J.at o.st) (hstart : M.initial o q) :
      CallTr J σ r a M .entry .yield (.active o q)
  | halt {e : THalt} (h : TRun.transfer r a σ = .error e) :
      CallTr J σ r a M .entry .halt (.finished (.halt e))
  | violation {o : Out C σ.H Γ} (h : TRun.transfer r a σ = .ok o) (hi : ¬J.at o.st) :
      CallTr J σ r a M .entry .violation (.finished .violated)
  | callee {o : Out C σ.H Γ} {q q' : M.Control} {label : M.Label}
      (h : M.system.Tr q label q') :
      CallTr J σ r a M (.active o q) (.callee label) (.active o q')
  | resume {o : Out C σ.H Γ} {q : M.Control} {st : Storage C} {nt : Ledger}
      {sb : PrimTy.uint.Denote} (hret : M.returns q st nt sb) (hi : J.at (o.st.havoc st nt sb)) :
      CallTr J σ r a M (.active o q) .resume (.finished (.ok ⟨o.st.havoc st nt sb, o.ext⟩))

def callLts (J : StateInv C) (σ : State C Γ) (r a : Val C Γ .uint) (M : Callee σ) :
    LTS (CallCfg σ M) (CallEvent M) := ⟨CallTr J σ r a M⟩

def CallMeaning (M : Callee σ) : CallCfg σ M → Prop
  | .entry => True
  | .active o _ => TRun.transfer r a σ = .ok o ∧ J.at o.st
  | .finished o => ExecS J σ (.transfer r a) o

theorem call_step_sound (hp : J.pay = true) {M : Callee σ} {s t : CallCfg σ M}
    {e : CallEvent M} (h : (callLts J σ r a M).Tr s e t) :
    CallMeaning (J := J) (r := r) (a := a) M s →
      CallMeaning (J := J) (r := r) (a := a) M t := by
  cases h with
  | enter hrun hi _ => exact fun _ => ⟨hrun, hi⟩
  | halt hrun => exact fun _ => .transferHalt hp hrun
  | violation hrun hi => exact fun _ => .transferViolated hp hrun hi
  | callee _ => exact id
  | resume _ hi => exact fun h => .transferResume hp h.1 h.2 hi

theorem call_trace_sound (hp : J.pay = true) {M : Callee σ} {es : List (CallEvent M)}
    {o : COut C σ.H Γ} (h : (callLts J σ r a M).MTr .entry es (.finished o)) :
    ExecS J σ (.transfer r a) o := by
  have transport : ∀ {s t : CallCfg σ M} {es : List (CallEvent M)},
      (callLts J σ r a M).MTr s es t →
      CallMeaning (J := J) (r := r) (a := a) M s →
        CallMeaning (J := J) (r := r) (a := a) M t := by
    intro s t es ht
    induction ht with
    | refl => exact id
    | stepL hs _ ih => exact fun hm => ih (call_step_sound hp hs hm)
  exact transport h trivial

def CallSafe (J : StateInv C) (σ : State C Γ) (r a : Val C Γ .uint) (M : Callee σ)
    (m : Modality) (post : State C Γ → Prop) : Prop :=
  ∀ es o, (callLts J σ r a M).MTr .entry es (.finished o) → o.after m post

/-- The maximally nondeterministic callee can return every global state.
It witnesses completeness of quantification over arbitrary callees. -/
def universalCallee (σ : State C Γ) : Callee σ where
  Control := Storage C × Ledger × PrimTy.uint.Denote
  Label := Unit
  system := ⟨fun _ _ _ => False⟩
  initial := fun _ _ => True
  returns := fun q st nt sb => q = (st, nt, sb)

theorem exec_call_trace (hp : J.pay = true) {o : COut C σ.H Γ}
    (h : ExecS J σ (.transfer r a) o) :
    ∃ es, (callLts J σ r a (universalCallee σ)).MTr .entry es (.finished o) := by
  cases h with
  | det hf => simp only [Stmt.forksIn, hp, Bool.true_eq_false] at hf
  | transferHalt _ hrun => exact ⟨[.halt], .stepL (.halt hrun) .refl⟩
  | transferViolated _ hrun hi => exact ⟨[.violation], .stepL (.violation hrun hi) .refl⟩
  | transferResume _ hrun hi hback =>
    exact ⟨[.yield, .resume], .stepL (.enter hrun hi trivial) (.stepL (.resume rfl hback) .refl)⟩

/-- Exact safety against operational callees with invariant-preserving
returns, including arbitrarily long finite computations. Returns violating
the invariant cannot resume in `callLts`; this is an assumption of the
callback reading, not an invariant-preservation theorem about all callees. -/
theorem holdsC_iff_all_callees (I : Fml C []) (σ : State C Γ)
    (r a : Val C Γ .uint) (m : Modality) (φ : Fml C Γ) :
    holdsC I true σ (.modal m (.cons (.transfer r a) .nil) .nil φ) ↔
      ∀ M : Callee σ, CallSafe (I.stateInv true) σ r a M m (holdsC I true · φ) := by
  rw [holdsC_single]
  constructor
  · intro h M es o ht
    exact h o (call_trace_sound rfl ht)
  · intro h o ho
    obtain ⟨es, ht⟩ := exec_call_trace rfl ho
    exact h (universalCallee σ) es o ht

end Solidity.Bridge.Adversary
