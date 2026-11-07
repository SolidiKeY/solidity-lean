import Solidity.Backend.PrimitivePackets.Constants.Agreement
import Solidity.Evm.MemoryCompileExamples

/-! Regression: a typed integer literal must produce the canonical word while
preserving populated caller memory and arbitrary saved stacks. Out-of-range
Source constants/conversions are refused, not reclassified as target executions.
All legal widths/signs remain quantified. This does not repair frozen-file
fidelity or prove heap/world/session/gas/fetched-EVM adequacy. -/
namespace H62.PrimitivePackets.ConstantCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory Solidity.Lowering.V07
open Solidity.Backend.PrimitivePackets.Constants

def code (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) :=
  (selected (C := CompileExamples.C) 0 (Frag.init CompileExamples.Γ) t z h).code

theorem joint {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat) (source : Source.EMState E Δ)
    (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) (saved : List Word) :
    compileVal 0 (Frag.init CompileExamples.Γ) (value (C := CompileExamples.C) t z h) =
      some (selected 0 (Frag.init CompileExamples.Γ) t z h) ∧
    (Source.evalE G fr (fuel+2)
      (.conv (.const (Source.Q.ofInt z)) (.inl (IntegerConstants.allowed E t z h)))).run source =
      (.ok (.val (.int z h)),source) ∧
    IntValueRel t (.int z h : Source.Val E.layout (.int t)) (integerValue t z h) ∧
    run (code t z h) {CompileExamples.machine with stack := saved} =
      .ok ({CompileExamples.machine with stack := saved}.push (.val (sword z))) 0 ∧
    StateRepr 1 0 4 (Frag.init CompileExamples.Γ) CompileExamples.σ CompileExamples.base
      ({CompileExamples.machine with stack := saved}.push (.val (sword z))) := by
  have packet := success (C := CompileExamples.C) G fr fuel source 0 (Frag.init CompileExamples.Γ)
    t z h CompileExamples.machine saved
  exact ⟨packet.1,packet.2.1,packet.2.2.1,packet.2.2.2.2.2,
    (CompileExamples.fixture_repr.stack saved).push _⟩

theorem below_refused (E : Source.Env) (t : Source.IntTy) :
    Source.constVal (Source.Q.ofInt (t.lo-1)) (.int t) =
      (.error (.stuck "integer out of range") : Source.R (Source.Val E.layout (.int t))) ∧
    (Source.STy.rational (Source.Q.ofInt (t.lo-1))).implicit E.isBase E.mapFree (.int t) = false := by
  have outside : ¬ (t.lo ≤ t.lo-1 ∧ t.lo-1 ≤ t.hi) := by omega
  exact ⟨source_refused t (t.lo-1) outside,conversion_refused E t (t.lo-1) outside⟩

theorem above_refused (E : Source.Env) (t : Source.IntTy) :
    Source.constVal (Source.Q.ofInt (t.hi+1)) (.int t) =
      (.error (.stuck "integer out of range") : Source.R (Source.Val E.layout (.int t))) ∧
    (Source.STy.rational (Source.Q.ofInt (t.hi+1))).implicit E.isBase E.mapFree (.int t) = false := by
  have outside : ¬ (t.lo ≤ t.hi+1 ∧ t.hi+1 ≤ t.hi) := by omega
  exact ⟨source_refused t (t.hi+1) outside,conversion_refused E t (t.hi+1) outside⟩

theorem reject_all_refuted (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi)
    (saved : List Word) : run (code t z h) {CompileExamples.machine with stack := saved} ≠ .revert := by
  have ran := target_success (C := CompileExamples.C) 0 (Frag.init CompileExamples.Γ)
    t z h CompileExamples.machine saved
  unfold code
  rw [ran]
  intro same
  cases same

theorem low_fuel {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (source : Source.EMState E Δ)
    (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) :
    (Source.evalE G fr 0
      (.conv (.const (Source.Q.ofInt z)) (.inl (IntegerConstants.allowed E t z h)))).run source =
      (.error .timeout,source) := rfl

#print axioms joint
#print axioms below_refused
#print axioms above_refused
#print axioms reject_all_refuted
#print axioms low_fuel
end H62.PrimitivePackets.ConstantCorrespondence
