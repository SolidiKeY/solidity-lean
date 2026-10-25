import Solidity.Calculus.CallbackHolds
import Cslib.Foundations.Semantics.LTS.Bisimulation

/-!
CSLib trace/bisimulation invariance for every framed callback modality.
Program and frame execution use the existing `ExecP`/`ExecF` relations;
completed states, halts and invariant violations are observable labels.
The independently defined operational callee correspondence is separate
(`CallbackTrace`); this module does not reimplement callback execution.
-/
namespace Solidity.Bridge.CallbackTrace

variable {C : Contract} {Δ : Ctx}

inductive Event (C : Contract) (Δ : Ctx) where
  | internal
  | returned (σ : State C Δ)
  | halted (e : THalt)
  | violated

inductive Config (C : Contract) (Δ : Ctx) where
  | program {Γ Ε : Ctx} (σ : State C Γ) (P : Prog C Γ Ε) (κ : Frames C Ε Δ)
  | frames {Ε : Ctx} (σ : State C Ε) (κ : Frames C Ε Δ)
  | returned (σ : State C Δ)
  | halted (e : THalt)
  | violated
  | stopped

inductive Transition (J : StateInv C) : Config C Δ → Event C Δ → Config C Δ → Prop where
  | programOk {Γ Ε : Ctx} {σ : State C Γ} {P : Prog C Γ Ε} {κ : Frames C Ε Δ}
      {o : Out C σ.H Ε} (h : ExecP J σ P (.ok o)) :
      Transition J (.program σ P κ) .internal (.frames o.st κ)
  | programHalt {Γ Ε : Ctx} {σ : State C Γ} {P : Prog C Γ Ε} {κ : Frames C Ε Δ}
      {e : THalt} (h : ExecP J σ P (.halt e)) :
      Transition J (.program σ P κ) .internal (.halted e)
  | programViolated {Γ Ε : Ctx} {σ : State C Γ} {P : Prog C Γ Ε} {κ : Frames C Ε Δ}
      (h : ExecP J σ P .violated) : Transition J (.program σ P κ) .internal .violated
  | framesOk {Ε : Ctx} {σ : State C Ε} {κ : Frames C Ε Δ}
      {o : Out C σ.H Δ} (h : ExecF J σ κ (.ok o)) :
      Transition J (.frames σ κ) .internal (.returned o.st)
  | framesHalt {Ε : Ctx} {σ : State C Ε} {κ : Frames C Ε Δ}
      {e : THalt} (h : ExecF J σ κ (.halt e)) :
      Transition J (.frames σ κ) .internal (.halted e)
  | framesViolated {Ε : Ctx} {σ : State C Ε} {κ : Frames C Ε Δ}
      (h : ExecF J σ κ .violated) : Transition J (.frames σ κ) .internal .violated
  | returned {σ : State C Δ} : Transition J (.returned σ) (.returned σ) .stopped
  | halted {e : THalt} : Transition J (.halted e) (.halted e) .stopped
  | violated : Transition J .violated .violated .stopped

def system (J : StateInv C) : LTS (Config C Δ) (Event C Δ) := ⟨Transition J⟩

def Accept (m : Modality) (post : State C Δ → Prop) : Event C Δ → Prop
  | .internal => True
  | .returned σ => post σ
  | .halted e => m.onTHalt e ∧ e ≠ .panic
  | .violated => False

def Safe (J : StateInv C) (q : Config C Δ) (m : Modality) (post : State C Δ → Prop) : Prop :=
  ∀ labels ∈ (system J).traces q, ∀ e ∈ labels, Accept m post e

private def Meaning (J : StateInv C) (m : Modality) (post : State C Δ → Prop) :
    Config C Δ → Prop
  | .program σ P κ => ∀ out, ExecP J σ P out → out.thenF J κ m post
  | .frames σ κ => ∀ out, ExecF J σ κ out → out.after m post
  | .returned σ => post σ
  | .halted e => m.onTHalt e ∧ e ≠ .panic
  | .violated => False
  | .stopped => True

private theorem step_sound {J : StateInv C} {m : Modality} {post : State C Δ → Prop}
    {s t : Config C Δ} {e : Event C Δ} (h : (system J).Tr s e t)
    (hs : Meaning J m post s) : Meaning J m post t ∧ Accept m post e := by
  cases h with
  | programOk h => exact ⟨hs _ h, trivial⟩
  | programHalt h => exact ⟨hs _ h, trivial⟩
  | programViolated h => exact ⟨hs _ h, trivial⟩
  | framesOk h => exact ⟨hs _ h, trivial⟩
  | framesHalt h => exact ⟨hs _ h, trivial⟩
  | framesViolated h => exact ⟨hs _ h, trivial⟩
  | returned => exact ⟨trivial, hs⟩
  | halted => exact ⟨trivial, hs⟩
  | violated => exact hs.elim

private theorem trace_sound {J : StateInv C} {m : Modality} {post : State C Δ → Prop}
    {s t : Config C Δ} {es : List (Event C Δ)} (h : (system J).MTr s es t)
    (hs : Meaning J m post s) : ∀ e ∈ es, Accept m post e := by
  induction h with
  | refl => intro e he; cases he
  | stepL h _ ih =>
    obtain ⟨hnext, hevent⟩ := step_sound h hs
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hevent
    · exact ih hnext e he

theorem holdsC_iff_traceSafe (I : Fml C []) (pay : Bool) {Γ Ε : Ctx}
    (σ : State C Γ) (P : Prog C Γ Ε) (κ : Frames C Ε Δ)
    (m : Modality) (φ : Fml C Δ) :
    holdsC I pay σ (.modal m P κ φ) ↔
      Safe (I.stateInv pay) (.program σ P κ) m (holdsC I pay · φ) := by
  constructor
  · intro h es hes e he
    obtain ⟨q, ht⟩ := hes
    exact trace_sound ht h e he
  · intro h out hp
    cases out with
    | halt e =>
      exact h [.internal, .halted e]
        ⟨_, .stepL (.programHalt hp) (.stepL .halted .refl)⟩ (.halted e)
          (by simp only [List.mem_cons, true_or, or_true])
    | violated =>
      exact h [.internal, .violated]
        ⟨_, .stepL (.programViolated hp) (.stepL .violated .refl)⟩ .violated
          (by simp only [List.mem_cons, true_or, or_true])
    | ok o =>
      intro out hf
      cases out with
      | ok o' =>
        exact h [.internal, .internal, .returned o'.st]
          ⟨_, .stepL (.programOk hp) (.stepL (.framesOk hf) (.stepL .returned .refl))⟩
          (.returned o'.st) (by simp only [List.mem_cons, true_or, or_true])
      | halt e =>
        exact h [.internal, .internal, .halted e]
          ⟨_, .stepL (.programOk hp) (.stepL (.framesHalt hf) (.stepL .halted .refl))⟩
          (.halted e) (by simp only [List.mem_cons, true_or, or_true])
      | violated =>
        exact h [.internal, .internal, .violated]
          ⟨_, .stepL (.programOk hp) (.stepL (.framesViolated hf) (.stepL .violated .refl))⟩
          .violated (by simp only [List.mem_cons, true_or, or_true])

theorem traceEq_holdsC (I : Fml C []) (pay : Bool) {Γ Ε Γ' Ε' : Ctx}
    (σ : State C Γ) (P : Prog C Γ Ε) (κ : Frames C Ε Δ)
    (τ : State C Γ') (Q : Prog C Γ' Ε') (κ' : Frames C Ε' Δ)
    (h : TraceEq (system (I.stateInv pay)) (.program σ P κ) (.program τ Q κ'))
    (m : Modality) (φ : Fml C Δ) :
    holdsC I pay σ (.modal m P κ φ) ↔ holdsC I pay τ (.modal m Q κ' φ) := by
  rw [holdsC_iff_traceSafe, holdsC_iff_traceSafe]
  unfold Safe
  rw [show (system (I.stateInv pay)).traces (.program σ P κ) =
    (system (I.stateInv pay)).traces (.program τ Q κ') from h]

theorem bisim_holdsC (I : Fml C []) (pay : Bool) {Γ Ε Γ' Ε' : Ctx}
    (σ : State C Γ) (P : Prog C Γ Ε) (κ : Frames C Ε Δ)
    (τ : State C Γ') (Q : Prog C Γ' Ε') (κ' : Frames C Ε' Δ)
    {R : Config C Δ → Config C Δ → Prop}
    (hR : (system (I.stateInv pay)).IsBisimulation R)
    (h : R (.program σ P κ) (.program τ Q κ')) (m : Modality) (φ : Fml C Δ) :
    holdsC I pay σ (.modal m P κ φ) ↔ holdsC I pay τ (.modal m Q κ' φ) :=
  traceEq_holdsC I pay σ P κ τ Q κ' (hR.traceEq h) m φ

end Solidity.Bridge.CallbackTrace

/-- info: 'Solidity.Bridge.CallbackTrace.holdsC_iff_traceSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.CallbackTrace.holdsC_iff_traceSafe

/-- info: 'Solidity.Bridge.CallbackTrace.bisim_holdsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.CallbackTrace.bisim_holdsC
