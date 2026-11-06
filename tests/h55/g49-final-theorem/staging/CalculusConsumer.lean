import Solidity.Roadmap.V16.CompilerConsumer
import Solidity.Calculus.CallbackHolds

/-!
# Actual calculus-to-compiler consumers for parallel clients

The input is the existing intrinsic Fml reading, not a new specification
semantics. A checked compiler Input rules out the approved exhausted-diamond
alternative. Payment refusal remains a distinct target alternative; the
nonpaying consumer removes it only with the actual syntactic pays equation.
These consumers compile the body P, with no residual frames. They do not
construct SourceSpec admission/lowering, callback bytecode correspondence or
full-profile compilation. No Fml.inTarget or SolKey rule is changed.
-/
namespace Solidity.Roadmap.V16
open Solidity.Evm

/-- A genuine calculus diamond and an actual checked compiler input produce a
source success. There is no separate source-success/notExhausted premise. -/
theorem calculus_compiler_source {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {φ : Fml C Δ}
    (input : compiled.Input L frame base σ m)
    (diamond : holds σ (.modal .diamond P .nil φ)) :
    ∃ o, P.run σ = .ok o ∧ holds o.st φ := by
  cases source : P.run σ with
  | ok o =>
    exact ⟨o,rfl,(afterRunTR_ok .diamond _ o.st).mp (by
      simpa only [holds,Prog.runFrames,source,Frames.run,Except.bind,
        pure,Except.pure] using diamond)⟩
  | error e =>
    have exhausted : e = .exhausted := by
      have halt := (afterRunTR_error .diamond (holds · φ) e).mp (by
        simpa only [holds,Prog.runFrames,source,Except.bind] using diamond)
      exact halt.1
    subst e
    exact False.elim (compiler_not_exhausted compiled input source)

/-- Exact public compiler alternatives, including real payment refusal.
The success arm keeps PC0, the entire protected stack and branch-specific Rep. -/
theorem calculus_compiler_diamond {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {φ : Fml C Δ}
    (input : compiled.Input L frame base σ m)
    (diamond : holds σ (.modal .diamond P .nil φ)) :
    ∃ o, P.run σ = .ok o ∧ holds o.st φ ∧
      ((∃ m', run compiled.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
        compiled.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m') ∨
       (Evm.Prog.pays P = true ∧ run compiled.code m = .revert ∧
         ∃ candidate, compiled.Rep (L + Evm.Prog.pushes P) frame base σ m o.st candidate)) := by
  obtain ⟨o,source,post⟩ := calculus_compiler_source compiled input diamond
  have spec : Spec.sat σ (.diamond P .tt) := by
    simp only [Spec.sat,source]
  obtain ⟨u,hs,_,target⟩ := compiler_diamond compiled input spec
  have eq : u = o := Except.ok.inj (hs.symm.trans source)
  subst u
  exact ⟨o,source,post,target⟩

/-- Actual nonpayment eliminates payment refusal, not source divergence in the
profile. Success follows from the supplied calculus diamond and checked Input. -/
theorem calculus_compiler_nonpaying {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {φ : Fml C Δ}
    (input : compiled.Input L frame base σ m) (nonpaying : Evm.Prog.pays P = false)
    (diamond : holds σ (.modal .diamond P .nil φ)) :
    ∃ o m', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ compiled.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m' ∧
      holds o.st φ := by
  obtain ⟨o,source,post,result⟩ := calculus_compiler_diamond compiled input diamond
  rcases result with ⟨m',target,stack,rep⟩ | ⟨pays,_⟩
  · exact ⟨o,m',source,target,stack,rep,post⟩
  · rw [nonpaying] at pays; cases pays

/-- A box supplies the actual successful target's source postcondition.
This does not reinterpret a target revert as a source panic or a success. -/
theorem calculus_compiler_box_target {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m m' : Machine} {φ : Fml C Δ}
    (input : compiled.Input L frame base σ m)
    (box : holds σ (.modal .box P .nil φ))
    (target : run compiled.code m = .ok m' 0) :
    ∃ o, P.run σ = .ok o ∧ m'.stack = m.stack ∧
      compiled.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m' ∧ holds o.st φ := by
  have spec : Spec.sat σ (.box P .tt) := by
    cases hs : P.run σ with
    | ok o => simp only [Spec.sat,hs]
    | error e =>
      have halt := (afterRunTR_error .box (holds · φ) e).mp (by
        simpa only [holds,Prog.runFrames,hs,Except.bind] using box)
      simpa only [Spec.sat,hs] using halt.2
  obtain ⟨o,source,stack,rep,_⟩ := compiler_box_target compiled input spec target
  refine ⟨o,source,stack,rep,?_⟩
  exact (afterRunTR_ok .box _ o.st).mp (by
    simpa only [holds,Prog.runFrames,source,Frames.run,Except.bind,
      pure,Except.pure] using box)

/-- Consume the published callback-aware reading without assuming an ExecP or a
desired target run. The postcondition's callback restriction is explicit; no
claim is made that compilation realizes adversarial resumptions. -/
theorem callback_compiler_nonpaying {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    {I : Fml C []} {pay : Bool} {φ : Fml C Δ}
    (input : compiled.Input L frame base σ m) (nonpaying : Evm.Prog.pays P = false)
    (postNoCallback : φ.callsBack pay = false)
    (diamond : holdsC I pay σ (.modal .diamond P .nil φ)) :
    ∃ o m', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ compiled.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m' ∧
      holds o.st φ :=
  calculus_compiler_nonpaying compiled input nonpaying
    (holds_of_holdsC_modal diamond postNoCallback)

/-- Callback-aware boxes are consumed only at an actual successful target run. -/
theorem callback_compiler_box_target {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m m' : Machine}
    {I : Fml C []} {pay : Bool} {φ : Fml C Δ}
    (input : compiled.Input L frame base σ m) (postNoCallback : φ.callsBack pay = false)
    (box : holdsC I pay σ (.modal .box P .nil φ))
    (target : run compiled.code m = .ok m' 0) :
    ∃ o, P.run σ = .ok o ∧ m'.stack = m.stack ∧
      compiled.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m' ∧ holds o.st φ :=
  calculus_compiler_box_target compiled input (holds_of_holdsC_modal box postNoCallback) target
end Solidity.Roadmap.V16
