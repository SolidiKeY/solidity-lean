import Solidity.Backend.Passes.ValueCertificate
import Solidity.Backend.InternalFlow.RuntimeFrameRestoredRepresentation
import Solidity.Backend.PrimitivePackets.UnsignedMul.Selection

/-! Unchecked unsigned multiplication transported from independent Source locals to
actual emitted value code. Width and full physical representation are retained;
this proves selection only for this local expression family, not general Source
heap/world admission or Source-to-intrinsic lowering. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedMul
open Evm Evm.Memory Solidity.Lowering.V07 Backend.Passes
open Solidity.Lowering.V07.UnsignedNarrowing Solidity.Lowering.V07.UnsignedMultiplication

theorem execution {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (a b : ι) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy)
    {offset L frame : Nat} {F : Frag Γ}
    {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F target base machine) :
    let value := integerValue (ty bits valid) ((ty bits valid).wrap (x*y)) ((ty bits valid).wrap_mem (x*y))
    (Source.evalE G {SF with checked := false} (fuel+3)
      (.binary .mul (.local (si a)) (.local (si b)))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (x*y))),source) ∧
    (expression (C := C) bits (ti a) (ti b)).evalT target = .ok value ∧
    IntValueRel (ty bits valid) (Source.intWrap (ty bits valid) (x*y) : Source.Val E.layout (.int (ty bits valid))) value ∧
    Memory.compileVal offset F (expression (C := C) bits (ti a) (ti b)) =
      some (selected (C := C) offset F bits (ti a) (ti b)) ∧
    ∃ word, ReprV .uint value word ∧ ∀ tail,
      run (selected (C := C) offset F bits (ti a) (ti b)).code {machine with stack := tail} = .ok ({machine with stack := tail}.push word) 0 ∧
      StateRepr L offset frame F target base ({machine with stack := tail}.push word) := by

  have transport := UnsignedMultiplication.locals_transport G SF fuel source target bits valid si ti family a b x y hx hy readA readB
  let compiled := selected (C := C) offset F bits (ti a) (ti b)
  obtain ⟨word,repr,_⟩ := value_success_tail compiled represented transport.2.1 []
  refine ⟨transport.1,transport.2.1,transport.2.2,selection offset F bits (ti a) (ti b),word,repr,?_⟩
  intro tail
  obtain ⟨actual,actualRep,run⟩ := value_success_tail compiled represented transport.2.1 tail
  have same : actual = word := Backend.InternalFlow.RuntimeFrame.Restored.value_unique actualRep repr
  rw [same] at run
  exact ⟨run, represented.stack (word :: tail)⟩

end Solidity.Backend.PrimitivePackets.UnsignedMul
