import Solidity.Backend.Passes.MappedTail
import Solidity.Backend.Passes.CapturedValueStability
import Solidity.Lowering.V07.UnsignedAddition
import Solidity.Backend.Passes.AssignmentSubtractionPass

/-! Effectful unchecked addition with actual captured operand order. Published
Source assignment transport, original compiler Input and exact selected maps
are retained; no arithmetic/compiler producer is assumed from a desired run. -/
namespace Solidity.Backend.Passes.AssignmentAdditionPass
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open UnsignedNarrowing

def value {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline) (bits : Nat) :
    Val C (.val .uint :: .val .uint :: Γ) .uint :=
  match pipeline with
  | .legacy => UnsignedAddition.addValue bits
      (.simple (.local .here)) (.simple (.local (.there .here)))
  | .viaIR => UnsignedAddition.addValue bits
      (.simple (.local (.there .here))) (.simple (.local .here))

abbrev reached := @AssignmentSubtractionPass.reached

theorem reached_value {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline) (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (i : Idx Γ (.val .uint)) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) :
    (value (C := C) (Γ := Γ) pipeline bits).evalT
      (reached pipeline target (ty bits valid) i x y hx hy) =
      .ok (integerValue (ty bits valid)
        ((ty bits valid).wrap (x+(if pipeline = .legacy then y else x)))
        ((ty bits valid).wrap_mem _)) := by
  cases pipeline with
  | legacy =>
    simpa only [value,reached,AssignmentSubtractionPass.reached,if_true] using
      UnsignedAddition.add_value_run
        (reached .legacy target (ty bits valid) i x y hx hy) bits valid
        (.simple (.local .here)) (.simple (.local (.there .here))) x y hx hy rfl rfl
  | viaIR =>
    simpa only [value,reached,AssignmentSubtractionPass.reached,reduceCtorEq,if_false] using
      UnsignedAddition.add_value_run
        (reached .viaIR target (ty bits valid) i x y hx hy) bits valid
        (.simple (.local (.there .here))) (.simple (.local .here)) x x hx hx rfl rfl

theorem execution {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (i a : ι) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (sourceA : source.1.get (si a) = .int x hx) (sourceI : source.1.get (si i) = .int y hy)
    {offset L frame : Nat} {F : Frag Γ}
    (programCode : CompiledProg offset F (assignReadPrefix G.pipeline (ti i) (ti a)))
    (operand : CompiledVal offset programCode.frag (value (C := C) (Γ := Γ) G.pipeline bits))
    {base : Nat → Fin W} {machine : Machine}
    (input : (Compilation.memory programCode).Input L frame base target machine) :
    (Source.evalE G {SF with checked := false} (fuel+4) (.binary .add (.assign (.local (si i)) (.local (si a))) (.local (si i)))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (x+(if G.pipeline = .legacy then y else x)))),
        (source.1.set (si i) (.int x hx),source.2)) ∧
    IntValueRel (ty bits valid)
      (Source.intWrap (ty bits valid) (x+(if G.pipeline = .legacy then y else x)) :
        Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) ((ty bits valid).wrap (x+(if G.pipeline = .legacy then y else x)))
        ((ty bits valid).wrap_mem _)) ∧
    IntegerLocalFamily (ty bits valid) si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue (ty bits valid) x hx) target.env) ∧
    ∃ (canonical : Machine) (addresses : Nat → Fin W) (word : Word),
      ReprV .uint (integerValue (ty bits valid) ((ty bits valid).wrap (x+(if G.pipeline = .legacy then y else x))) ((ty bits valid).wrap_mem _)) word ∧
      canonical.stack = [] ∧ ∀ tail,
        run programCode.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
        MappedOutput (.memory programCode) (L+Evm.Prog.pushes (assignReadPrefix (C := C) G.pipeline (ti i) (ti a)))
          frame base target {machine with stack := tail}
          (reached G.pipeline target (ty bits valid) (ti i) x y hx hy) {canonical with stack := tail} addresses ∧
        run operand.code {canonical with stack := tail} = .ok ({canonical with stack := tail}.push word) 0 ∧
        run (programCode.code ++ operand.code) {machine with stack := tail} =
          .ok ({canonical with stack := tail}.push word) 0 := by
  have sourceRun := UnsignedAddition.assignment_transport G SF fuel source target bits valid si ti family
    i a x y hx hy sourceA sourceI
  have prefixRun := assign_read_prefix_run G.pipeline target (ti i) (ti a) _ _
    (family.read a x hx sourceA) (family.read i y hy sourceI)
  have noPay : Evm.Prog.pays (assignReadPrefix (C := C) G.pipeline (ti i) (ti a)) = false := by cases G.pipeline <;> rfl
  obtain ⟨canonical,addresses,_,empty,runs⟩ := compilation_success_shared_mapped (.memory programCode) input noPay prefixRun
  have represented := (runs []).2.1
  obtain ⟨word,repr,values⟩ := CapturedValueStability.value_shared _ operand represented _
    (reached_value G.pipeline target bits valid (ti i) x y hx hy)
  refine ⟨sourceRun.1,sourceRun.2.2.1,sourceRun.2.2.2,canonical,addresses,word,repr,empty,?_⟩
  intro tail
  have vr := values tail
  refine ⟨(runs tail).1,(runs tail).2,vr,?_⟩
  exact (run_append_ok (c₂ := operand.code) (runs tail).1).trans vr

end Solidity.Backend.Passes.AssignmentAdditionPass
