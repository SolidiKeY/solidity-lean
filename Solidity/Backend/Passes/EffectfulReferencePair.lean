import Solidity.Backend.Passes.MappedTail
import Solidity.Lowering.V07.ReferenceEffects

/-! Actual pipeline-dependent reference assignment/read captures, connected to
accepted compiler output. The selected address/identity relation is independent
of both evaluators. This does not assert global Source heap or world adequacy. -/
namespace Solidity.Backend.Passes.EffectfulReferencePair
open Evm Evm.Compiler Solidity.Lowering.V07

def reached {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline)
    (target : State C Γ) (j : Idx Γ (.mem bytesR)) (old assigned : HRef target.H bytesR) :
    State C (.mem bytesR :: .mem bytesR :: Γ) :=
  ((target.setLocal j (some assigned)).push (t := .mem bytesR)
    (some (if pipeline = .legacy then old else assigned))).push (t := .mem bytesR) (some assigned)

theorem payment_free {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline)
    (j b : Idx Γ (.mem bytesR)) :
    Evm.Prog.pays (memoryAssignReadPrefix (C := C) pipeline j b rfl) = false := by
  first | rfl | decide | omega | (cases pipeline <;> rfl)

theorem execution {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (i a : Source.Idx srcΓ (.bytes .memory)) (j b : Idx Γ (.mem bytesR))
    (oldAddress newAddress : Nat) (old assigned : HRef target.H bytesR)
    (readI : source.1.get i = .memRef rfl oldAddress)
    (readA : source.1.get a = .memRef rfl newAddress)
    (targetI : TEnv.get j target.env = some old) (targetA : TEnv.get b target.env = some assigned)
    (R : Nat → HRef target.H bytesR → Prop) (oldRel : R oldAddress old) (newRel : R newAddress assigned)
    (aliases : oldAddress = newAddress ↔ old = assigned)
    {offset L frame : Nat} {F : Frag Γ}
    (compiled : Compilation offset F (memoryAssignReadPrefix G.pipeline j b rfl))
    {base : Nat → Fin W} {machine : Machine}
    (input : compiled.Input L frame base target machine) :
    (Source.evalPair G SF (fuel+3) (.assign (.local i) (.local a)) (.local i)).run source =
      (.ok (.val (.memRef rfl newAddress),
        .val (.memRef rfl (if G.pipeline = .legacy then oldAddress else newAddress))),
        (source.1.set i (.memRef rfl newAddress),source.2)) ∧
    R (if G.pipeline = .legacy then oldAddress else newAddress)
      (if G.pipeline = .legacy then old else assigned) ∧
    (newAddress = (if G.pipeline = .legacy then oldAddress else newAddress) ↔
      assigned = (if G.pipeline = .legacy then old else assigned)) ∧
    (memoryAssignReadPrefix G.pipeline j b rfl).run target =
      .ok ⟨reached G.pipeline target j old assigned,List.prefix_refl _⟩ ∧
    ∃ (canonical : Machine) (outBase : Nat → Fin W), canonical.stack = [] ∧ ∀ tail,
      compiled.Input L frame base target {machine with stack := tail} ∧
      run compiled.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput compiled (L + Evm.Prog.pushes (memoryAssignReadPrefix (C := C) G.pipeline j b rfl))
        frame base target {machine with stack := tail}
        (reached G.pipeline target j old assigned) {canonical with stack := tail} outBase := by
  first
  | (solve | simp only)
  | (solve | decide)
  | (solve | omega)
  | (solve | rfl)
  |
    have transport := reference_assignment_pair_transport G SF fuel source target i a j b
      oldAddress newAddress old assigned readI readA targetI targetA R oldRel newRel aliases
    obtain ⟨canonical,outBase,_,empty,runs⟩ := compilation_success_shared_mapped compiled input
      (payment_free G.pipeline j b) transport.2.1
    exact ⟨transport.1,transport.2.2.1,transport.2.2.2,transport.2.1,
      canonical,outBase,empty,fun tail => ⟨compilation_input_stack compiled input tail,runs tail⟩⟩

end Solidity.Backend.Passes.EffectfulReferencePair
