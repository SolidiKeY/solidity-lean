import Solidity.Backend.Passes.MappedTail
import Solidity.Backend.Passes.CapturedValueStability
import Solidity.Lowering.V07.AssignmentSubtraction

/-! Independent Source assignment/subtraction connected to actual emitted
capture-programCode and value code. Only the producer's original local/range facts
are used; no P8 Producer or whole Source/world correspondence is assumed. -/
namespace Solidity.Backend.Passes.AssignmentSubtractionPass
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07

def value {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline) (t : Source.IntTy) :
    Val C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) (integerPrim t) :=
  match pipeline with
  | .legacy => .binop .sub (integer_sub_accepts t) rfl
      (.simple (.local .here)) (.simple (.local (.there .here)))
  | .viaIR => .binop .sub (integer_sub_accepts t) rfl
      (.simple (.local (.there .here))) (.simple (.local .here))

def reached {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline) (target : State C Γ)
    (t : Source.IntTy) (i : Idx Γ (.val (integerPrim t))) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    State C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) :=
  ((target.setLocal i (integerValue t x hx)).push (t := .val (integerPrim t))
    (if pipeline = .legacy then integerValue t y hy else integerValue t x hx)).push (t := .val (integerPrim t)) (integerValue t x hx)

theorem reached_value {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline) (target : State C Γ)
    (t : Source.IntTy) (i : Idx Γ (.val (integerPrim t))) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (hz : t.lo ≤ x-(if pipeline = .legacy then y else x) ∧
      x-(if pipeline = .legacy then y else x) ≤ t.hi) :
    (value (C := C) (Γ := Γ) pipeline t).evalT (reached pipeline target t i x y hx hy) =
      .ok (integerValue t (x-(if pipeline = .legacy then y else x)) hz) := by
  first
  | (solve | simp only)
  | (solve | decide)
  | (solve | omega)
  | (solve | rfl)
  | cases pipeline with
    | legacy =>
      simpa only [value,reached,if_true] using intrinsic_sub_run
        (reached .legacy target t i x y hx hy) t
        (.simple (.local .here)) (.simple (.local (.there .here))) x y hx hy hz rfl rfl
    | viaIR =>
      simpa only [value,reached,reduceCtorEq,if_false] using intrinsic_sub_run
        (reached .viaIR target t i x y hx hy) t
        (.simple (.local (.there .here))) (.simple (.local .here)) x x hx hx hz rfl rfl

theorem execution {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
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
  first
  | (solve | simp only)
  | (solve | decide)
  | (solve | omega)
  | (solve | rfl)
  | have sourceRun := assignment_subtraction_transport G SF fuel source target t i a j b x y hx hy
      sourceA sourceI targetA targetI hz
    have prefixRun := assign_read_prefix_run G.pipeline target j b _ _ targetA targetI
    have noPay : Evm.Prog.pays (assignReadPrefix (C := C) G.pipeline j b) = false := by cases G.pipeline <;> rfl
    obtain ⟨canonical,addresses,_,empty,runs⟩ := compilation_success_shared_mapped (.memory programCode) input noPay prefixRun
    have represented := (runs []).2.1
    obtain ⟨word,repr,values⟩ := CapturedValueStability.value_shared _ operand represented _
      (reached_value G.pipeline target t j x y hx hy hz)
    refine ⟨sourceRun.1,sourceRun.2.2,canonical,addresses,word,repr,empty,?_⟩
    intro tail
    have vr := values tail
    refine ⟨(runs tail).1,(runs tail).2,vr,?_⟩
    exact (run_append_ok (c₂ := operand.code) (runs tail).1).trans vr

end Solidity.Backend.Passes.AssignmentSubtractionPass
