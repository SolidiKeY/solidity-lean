import Solidity.Backend.Passes.ClosedValues
import Solidity.Backend.Environment.Metadata

/-! Apply published resolved selector metadata to existing intrinsic literals,
actual compiler value certificates and selected-memory value composition.
Selectors remain LOW numeric uints, distinct from ABI left-aligned bytes4.
Declaration resolution and complete source/world/function lowering stay open. -/
namespace Solidity.Backend.Passes.ResolvedMetadata
open Backend.Environment
variable {C : Contract} {Γ : Ctx}

def expression (s : Fin (2^32)) : Val C Γ .uint :=
  .simple (.lit (selectorWord s).val (selectorWord s).property)

def certificate (σ : State C Γ) (f : Frame) (s : Fin (2^32)) (m : Memory) :
    ValueCertificate σ (expression s) f [selectorCode s] m where
  value := selectorWord s
  memoryOut := m
  source := (selector_intrinsic σ s []).1
  target := fun tail => slice_constant f 4 _ ⟨tail,m⟩

/-- The literal is admitted by the ACTUAL legacy compiler for arbitrary
original fragment. No target semantics replaces source evaluation. -/
def symbolic (b : Nat) (F : Evm.Frag Γ) (s : Fin (2^32)) :
    Evm.Memory.CompiledVal (C := C) b F (expression s) :=
  ⟨Evm.compileVal b (expression s),.core _ rfl⟩

theorem physical {σ : State C Γ} {b L frame : Nat} {F : Evm.Frag Γ}
    {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (input : Evm.Memory.StateRepr L b frame F σ base machine)
    (s : Fin (2^32)) (tail : List Evm.Word) :
    ∃ w : Fin Evm.W, Evm.ReprV .uint (selectorWord s) (.val w) ∧
      Backend.Scalar.encodeValue .uint (selectorWord s) = BitVec.ofNat 256 w.val ∧
      Evm.run (symbolic (C := C) b F s).code {machine with stack := tail} =
        .ok ({machine with stack := tail}.push (.val w)) 0 := by
  obtain ⟨word,hw,ht⟩ := value_success_tail (symbolic (C := C) b F s) input rfl tail
  obtain ⟨w,ew,he⟩ := ClosedValues.represented_word hw
  subst word
  exact ⟨w,hw,he,ht⟩

/-- The metadata suffix consumes the previous certificate's ACTUAL memoryOut.
Capacity is only the final PUSH premise; it asserts no missing prefix adequacy. -/
theorem after_value {σ : State C Γ} {e : Val C Γ .uint} {f : Frame}
    {code : List Backend.Instr} {memory : Memory}
    (head : ValueCertificate σ e f code memory)
    (d : SourceFunction) (s : Fin (2^32)) (resolved : metadataSelector d = some s)
    (tail : List Word)
    (capacity : Backend.Scalar.stackBound [selectorCode s] ((tail.length+1:Nat):Int) = true) :
    declarationCode d = some (selectorCode s) ∧
    evalValues σ [e,expression s] = .ok [head.value,selectorWord s] ∧
    runSlice f (code ++ [selectorCode s]) ⟨tail,memory⟩ =
      some ⟨selectorWord s :: head.value :: tail,head.memoryOut⟩ ∧
    Backend.Scalar.stackBound [selectorCode s] ((tail.length+1:Nat):Int) = true := by
  let selected := certificate σ f s head.memoryOut
  let joined := consCertificate head
    (consCertificate selected (nilCertificate σ f selected.memoryOut))
  refine ⟨(declaration_correct d s resolved []).1,joined.source,?_,capacity⟩
  simpa only [List.append_nil,List.reverse_cons,List.reverse_nil,List.nil_append,
    List.singleton_append,List.cons_append] using joined.target tail

end Solidity.Backend.Passes.ResolvedMetadata
