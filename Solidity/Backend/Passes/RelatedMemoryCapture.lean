import Solidity.Backend.Passes.MappedTail
import Solidity.Lowering.V07.ReferenceCaptureRelated

/-! Initial independent reference/context alignment, actual alias capture and
selected-map pointer readback. No Source declaration, heap-content or admission
correspondence is inferred from a local value relation. -/
namespace Solidity.Backend.Passes.RelatedMemoryCapture
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07

theorem execution {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (Rel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related Rel source.1 target.env)
    (i : Source.Idx srcΓ (.bytes .memory)) (j : Idx Γ (.mem bytesR))
    (address : Nat) (r : HRef target.H bytesR) (slot : m.slot i = ⟨.mem bytesR,j⟩)
    (sourceRead : source.1.get i = .memRef rfl address) (targetRead : TEnv.get j target.env = some r)
    {offset L frame : Nat} {F : Frag Γ}
    (compiled : CompiledProg offset F (memoryCapture j rfl))
    {base : Nat → Fin W} {machine : Machine}
    (input : (Compilation.memory compiled).Input L frame base target machine) :
    (Source.evalE G SF (fuel+1) (.local i)).run source = (.ok (.val (.memRef rfl address)),source) ∧
    Rel (.bytes .memory) (.mem bytesR) (.memRef rfl address) (some r) ∧
    (m.cons (.bytes .memory) (.mem bytesR)).Related Rel
      (.cons (.memRef rfl address) source.1) (target.push (t := .mem bytesR) (some r)).env ∧
    (m.wk (Thin.drop (t := .mem bytesR) .refl)).Related Rel
      source.1 (target.push (t := .mem bytesR) (some r)).env ∧
    (target.push (t := .mem bytesR) (some r)).drop (.push .refl) = target ∧
    ∃ (canonical : Machine) (selected : Nat → Fin W), canonical.stack = [] ∧ ∀ tail,
      (Compilation.memory compiled).Input L frame base target {machine with stack := tail} ∧
      run compiled.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput (.memory compiled) L frame base target {machine with stack := tail}
        (target.push (t := .mem bytesR) (some r)) {canonical with stack := tail} selected ∧
      selected r.id = base r.id ∧
      run (compiled.code ++ [.mload (cell (offset+Γ.length))]) {machine with stack := tail} =
        .ok ({canonical with stack := tail}.push (.val (selected r.id))) 0 := by
  have facts := related_memory_capture G SF fuel source target m Rel aligned i j address r slot sourceRead targetRead
  obtain ⟨canonical,selected,_,empty,runs⟩ := compilation_success_shared_mapped
    (.memory compiled) input (by rfl) facts.2.1
  refine ⟨facts.1,facts.2.2.2.1,facts.2.2.2.2.1,facts.2.2.2.2.2.1,
    facts.2.2.2.2.2.2,canonical,selected,empty,?_⟩
  intro tail
  have mapped := (runs tail).2
  rw [compiled.cert.pushes_zero,Nat.add_zero] at mapped
  obtain ⟨actualRef,localRead,word⟩ := mapped.1.pointers (.here : Idx (.mem bytesR :: Γ) (.mem bytesR))
  change some r = some actualRef at localRead
  have same : actualRef = r := Option.some.inj localRead.symm
  subst actualRef
  have physicalWord : canonical.mem (cell (offset+Γ.length)) = .val (selected r.id) := by
    simpa only [cellOf,lvl_here] using word
  have load : run [.mload (cell (offset+Γ.length))] {canonical with stack := tail} =
      .ok ({canonical with stack := tail}.push (.val (selected r.id))) 0 := by
    change Evm.Out.ok ({canonical with stack := tail}.push (canonical.mem (cell (offset+Γ.length)))) 0 = _
    rw [physicalWord]
  exact ⟨compilation_input_stack (.memory compiled) input tail,(runs tail).1,mapped,
    mapped.2.1 r,(run_append_ok (c₂ := [.mload (cell (offset+Γ.length))]) (runs tail).1).trans load⟩

end Solidity.Backend.Passes.RelatedMemoryCapture
