import tests.h62.item4.«generic-passes».Generic
import Solidity.Backend.Passes.AssignmentAdditionPass
import Solidity.Backend.Passes.AssignmentSubtractionPass
import Solidity.Backend.Passes.AssignmentMultiplicationPass

namespace Solidity.Backend.Passes.H62Instances
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open UnsignedNarrowing

section
open AssignmentAdditionPass
theorem execution_addition {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
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
  have noPay : Evm.Prog.pays (assignReadPrefix (C := C) G.pipeline (ti i) (ti a)) = false := by
    cases G.pipeline <;> rfl
  refine ⟨sourceRun.1, sourceRun.2.2.1, sourceRun.2.2.2, ?_⟩
  exact H62Generic.prefix_value programCode _ operand input noPay _ prefixRun _
    (reached_value G.pipeline target bits valid (ti i) x y hx hy)

theorem exact_addition_type : type_of% @AssignmentAdditionPass.execution :=
  @execution_addition
end

section
open AssignmentSubtractionPass
theorem execution_subtraction {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (t : Source.IntTy)
    (i a : Source.Idx srcΓ (.int t)) (j b : Idx Γ (.val (integerPrim t)))
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (sourceA : source.1.get a = .int x hx) (sourceI : source.1.get i = .int y hy)
    (targetA : TEnv.get b target.env = integerValue t x hx)
    (targetI : TEnv.get j target.env = integerValue t y hy)
    (hz : t.lo ≤ x-(if G.pipeline = .legacy then y else x) ∧
      x-(if G.pipeline = .legacy then y else x) ≤ t.hi)
    {offset L frame : Nat} {F : Frag Γ}
    (programCode : CompiledProg offset F (assignReadPrefix G.pipeline j b))
    (operand : CompiledVal offset programCode.frag (value (C := C) (Γ := Γ) G.pipeline t))
    {base : Nat → Fin W} {machine : Machine}
    (input : (Compilation.memory programCode).Input L frame base target machine) :
    (Source.evalE G SF (fuel+4) (.binary .sub (.assign (.local i) (.local a)) (.local i))).run source =
      (.ok (.val (.int (x-(if G.pipeline = .legacy then y else x)) hz)),
        (source.1.set i (.int x hx),source.2)) ∧
    IntValueRel t (.int (x-(if G.pipeline = .legacy then y else x)) hz : Source.Val E.layout (.int t))
      (integerValue t (x-(if G.pipeline = .legacy then y else x)) hz) ∧
    ∃ (canonical : Machine) (addresses : Nat → Fin W) (word : Word),
      ReprV (integerPrim t) (integerValue t (x-(if G.pipeline = .legacy then y else x)) hz) word ∧
      canonical.stack = [] ∧ ∀ tail,
        run programCode.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
        MappedOutput (.memory programCode) (L+Evm.Prog.pushes (assignReadPrefix (C := C) G.pipeline j b))
          frame base target {machine with stack := tail}
          (reached G.pipeline target t j x y hx hy) {canonical with stack := tail} addresses ∧
        run operand.code {canonical with stack := tail} = .ok ({canonical with stack := tail}.push word) 0 ∧
        run (programCode.code ++ operand.code) {machine with stack := tail} =
          .ok ({canonical with stack := tail}.push word) 0 := by
  have sourceRun := assignment_subtraction_transport G SF fuel source target t i a j b x y hx hy
    sourceA sourceI targetA targetI hz
  have prefixRun := assign_read_prefix_run G.pipeline target j b _ _ targetA targetI
  have noPay : Evm.Prog.pays (assignReadPrefix (C := C) G.pipeline j b) = false := by
    cases G.pipeline <;> rfl
  refine ⟨sourceRun.1, sourceRun.2.2, ?_⟩
  exact H62Generic.prefix_value programCode _ operand input noPay _ prefixRun _
    (reached_value G.pipeline target t j x y hx hy hz)

theorem exact_subtraction_type : type_of% @AssignmentSubtractionPass.execution :=
  @execution_subtraction
end

section
open AssignmentMultiplicationPass
theorem execution_multiplication {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
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
    (Source.evalE G {SF with checked := false} (fuel+4) (.binary .mul (.assign (.local (si i)) (.local (si a))) (.local (si i)))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (x*(if G.pipeline = .legacy then y else x)))),
        (source.1.set (si i) (.int x hx),source.2)) ∧
    IntValueRel (ty bits valid)
      (Source.intWrap (ty bits valid) (x*(if G.pipeline = .legacy then y else x)) :
        Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) ((ty bits valid).wrap (x*(if G.pipeline = .legacy then y else x)))
        ((ty bits valid).wrap_mem _)) ∧
    IntegerLocalFamily (ty bits valid) si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue (ty bits valid) x hx) target.env) ∧
    ∃ (canonical : Machine) (addresses : Nat → Fin W) (word : Word),
      ReprV .uint (integerValue (ty bits valid) ((ty bits valid).wrap (x*(if G.pipeline = .legacy then y else x))) ((ty bits valid).wrap_mem _)) word ∧
      canonical.stack = [] ∧ ∀ tail,
        run programCode.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
        MappedOutput (.memory programCode) (L+Evm.Prog.pushes (assignReadPrefix (C := C) G.pipeline (ti i) (ti a)))
          frame base target {machine with stack := tail}
          (reached G.pipeline target (ty bits valid) (ti i) x y hx hy) {canonical with stack := tail} addresses ∧
        run operand.code {canonical with stack := tail} = .ok ({canonical with stack := tail}.push word) 0 ∧
        run (programCode.code ++ operand.code) {machine with stack := tail} =
          .ok ({canonical with stack := tail}.push word) 0 := by
  have sourceRun := UnsignedMultiplication.assignment_transport G SF fuel source target bits valid si ti family
    i a x y hx hy sourceA sourceI
  have prefixRun := assign_read_prefix_run G.pipeline target (ti i) (ti a) _ _
    (family.read a x hx sourceA) (family.read i y hy sourceI)
  have noPay : Evm.Prog.pays (assignReadPrefix (C := C) G.pipeline (ti i) (ti a)) = false := by
    cases G.pipeline <;> rfl
  refine ⟨sourceRun.1, sourceRun.2.2.1, sourceRun.2.2.2, ?_⟩
  exact H62Generic.prefix_value programCode _ operand input noPay _ prefixRun _
    (reached_value G.pipeline target bits valid (ti i) x y hx hy)

theorem exact_multiplication_type : type_of% @AssignmentMultiplicationPass.execution :=
  @execution_multiplication
end

end Solidity.Backend.Passes.H62Instances
