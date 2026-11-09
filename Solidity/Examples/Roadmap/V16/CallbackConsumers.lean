import Solidity.Calculus.CallbackHolds

/-!
Scoped consumers of the published callback reading and its actual ExecP/ExecF
runs. No callback rule, transfer option or deterministic/runtime correspondence
is supplied or changed. Halts and invariant violations retain their readings.
-/
namespace Solidity.Roadmap.V16

/-- A modal callback specification supplies its postcondition after actual
successful program and frame executions, with all dependent heap types kept. -/
theorem callback_post {C : Contract} {Γ Δ Ξ : Ctx} {I : Fml C []}
    {pay : Bool} {m : Modality} {σ : State C Γ} {P : Prog C Γ Δ}
    {κ : Frames C Δ Ξ} {φ : Fml C Ξ}
    {o : Out C σ.H Δ} {u : Out C o.st.H Ξ}
    (modal : holdsC I pay σ (.modal m P κ φ))
    (run : ExecP (I.stateInv pay) σ P (.ok o))
    (frames : ExecF (I.stateInv pay) o.st κ (.ok u)) : holdsC I pay u.st φ :=
  modal _ run _ frames

/-- Consume the selected existing transfer semantics and callback precondition;
this does not prove the supplied validity or turn it into runtime validity. -/
theorem callback_valid_post {C : Contract} {Δ Ξ : Ctx} {ts : TransferSem C}
    {σ : State C []} {a : Fml C []} {P : Prog C [] Δ}
    {κ : Frames C Δ Ξ} {φ : Fml C Ξ} {m : Modality}
    {o : Out C σ.H Δ} {u : Out C o.st.H Ξ}
    (valid : ValidT ts (.imp a (.modal m P κ φ)))
    (pre : holdsC ts.inv.fml ts.pay σ a)
    (run : ExecP (ts.inv.fml.stateInv ts.pay) σ P (.ok o))
    (frames : ExecF (ts.inv.fml.stateInv ts.pay) o.st κ (.ok u)) :
    holdsC ts.inv.fml ts.pay u.st φ :=
  callback_post (valid σ pre) run frames

/-- Neither modality may accept an actual invariant-violating program run. -/
theorem callback_no_violation {C : Contract} {Γ Δ Ξ : Ctx} {I : Fml C []}
    {pay : Bool} {m : Modality} {σ : State C Γ} {P : Prog C Γ Δ}
    {κ : Frames C Δ Ξ} {φ : Fml C Ξ}
    (modal : holdsC I pay σ (.modal m P κ φ)) :
    ¬ ExecP (I.stateInv pay) σ P .violated := fun run => modal _ run

/-- A successful prefix cannot hide an invariant violation in its frames. -/
theorem callback_frames_no_violation {C : Contract} {Γ Δ Ξ : Ctx} {I : Fml C []}
    {pay : Bool} {m : Modality} {σ : State C Γ} {P : Prog C Γ Δ}
    {κ : Frames C Δ Ξ} {φ : Fml C Ξ} {o : Out C σ.H Δ}
    (modal : holdsC I pay σ (.modal m P κ φ))
    (run : ExecP (I.stateInv pay) σ P (.ok o)) :
    ¬ ExecF (I.stateInv pay) o.st κ .violated := fun frames => modal _ run _ frames

/-- Retain the actual halt value, the modality's existing halt reading and
panic exclusion; a successful-state postcondition is not inferred at a halt. -/
theorem callback_halt {C : Contract} {Γ Δ Ξ : Ctx} {I : Fml C []}
    {pay : Bool} {m : Modality} {σ : State C Γ} {P : Prog C Γ Δ}
    {κ : Frames C Δ Ξ} {φ : Fml C Ξ} {e : THalt}
    (modal : holdsC I pay σ (.modal m P κ φ))
    (run : ExecP (I.stateInv pay) σ P (.halt e)) : m.onTHalt e ∧ e ≠ .panic :=
  modal _ run

end Solidity.Roadmap.V16
