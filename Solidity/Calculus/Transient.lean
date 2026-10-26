import Solidity.Semantics.Transient
import Solidity.Calculus.Correct

/-!
# Correctness of composed transient effects

The modal halt policy is the existing calculus's `afterRunTR`, including its
panic exclusion and acceptance of exhaustion. Ordinary fragment boxes and
diamonds are exactly their `Spec.sat` reading. This reuses proofs established
by the ordinary calculus; it does not extend `Fml`, `Taclet` or `sol_prove`
with transient syntax. `Program.transact_ok` separately requires a completed
run, so accepting exhaustion in a modality cannot create a transaction commit.
-/

namespace Solidity.Transient

variable {C : Contract} {L : Layout} {α β : Type}

/-- The existing dynamic-logic halt policy, on the composed interpreter. -/
def Holds (m : Modality) (body : Program C L α)
    (post : α → FrameState C L → Prop) (ctx : Context) (s : FrameState C L) : Prop :=
  m.afterRunTR (fun result => post result.1 result.2) (Program.run body ctx s)

/-- Sequence two checked effect derivations. A panic is never discarded. -/
theorem holds_bind {m : Modality} (body : Program C L α) (next : α → Program C L β)
    (post : β → FrameState C L → Prop) {ctx : Context} {s : FrameState C L}
    (premise : Holds m body (fun v t => Holds m (next v) post ctx t) ctx s) :
    Holds m (.bind body next) post ctx s := by
  change m.afterRunTR _ (do
    let (v, t) ← Program.run body ctx s
    Program.run (next v) ctx t)
  cases ran : Program.run body ctx s with
  | error e =>
    change m.afterRunTR _ (Program.run body ctx s) at premise
    rw [ran] at premise
    refine ⟨premise.1, ?_⟩
    intro panic
    exact premise.2 (congrArg
      (fun reason : THalt => (Except.error reason : TRes (α × FrameState C L)))
      (Except.error.inj panic))
  | ok result =>
    obtain ⟨v, t⟩ := result
    change m.afterRunTR _ (Program.run body ctx s) at premise
    rw [ran] at premise
    exact premise.1

/-- A box proved in the ordinary calculus applies unchanged to its ordinary
fragment inside a transient computation. The transient store is kept. -/
theorem ordinary_spec_box (P : Prog C [] []) (within : Prog.within .nonpayable P = true)
    (φ : Spec C []) (s : FrameState C L) (proved : Spec.sat s.base (.box P φ)) :
    Holds .box (.ordinary .nonpayable P within) (fun _ t => Spec.sat t.base φ) {} s := by
  unfold Holds
  rw [Program.run_ordinary]
  cases ran : P.run s.base with
  | error e =>
    simp only [Spec.sat, ran] at proved
    refine ⟨trivial, ?_⟩
    intro panic
    exact proved (Except.error.inj panic)
  | ok out =>
    simp only [Spec.sat, ran] at proved
    exact ⟨proved, by intro panic; cases panic⟩

/-- The diamond bridge retains the ordinary exhaustion policy exactly. -/
theorem ordinary_spec_diamond (P : Prog C [] []) (within : Prog.within .nonpayable P = true)
    (φ : Spec C []) (s : FrameState C L) (proved : Spec.sat s.base (.diamond P φ)) :
    Holds .diamond (.ordinary .nonpayable P within) (fun _ t => Spec.sat t.base φ) {} s := by
  unfold Holds
  rw [Program.run_ordinary]
  cases ran : P.run s.base with
  | error e =>
    simp only [Spec.sat, ran] at proved
    refine ⟨proved, ?_⟩
    cases proved
    intro panic
    cases panic
  | ok out =>
    simp only [Spec.sat, ran] at proved
    exact ⟨proved, by intro panic; cases panic⟩

/-- Modal proofs concern successful results as well as the halt policy. -/
theorem post_of_holds {m : Modality} {body : Program C L α}
    {post : α → FrameState C L → Prop} {ctx : Context} {s t : FrameState C L} {v : α}
    (proved : Holds m body post ctx s) (success : Program.run body ctx s = .ok (v, t)) :
    post v t := by
  unfold Holds at proved
  rw [success] at proved
  exact proved.1

/-- An ordinary public correctness theorem, including one obtained by
`Proves.valid`, is usable for every transient entry store. -/
theorem ordinary_of_valid (P : Prog C [] []) (within : Prog.within .nonpayable P = true)
    (pre post : Spec C []) (proved : Spec.Valid (.imp pre (.box P post)))
    (s : FrameState C L) (entry : Spec.sat s.base pre) :
    Holds .box (.ordinary .nonpayable P within) (fun _ t => Spec.sat t.base post) {} s :=
  ordinary_spec_box P within post s (proved s.base entry)

end Solidity.Transient
