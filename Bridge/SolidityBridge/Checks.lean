import SolidityBridge.ExternalEvm.StorageSlotExamples
import SolidityBridge.Arith
import SolidityBridge.WeakestPre
import SolidityBridge.LoomRules
import SolidityBridge.LoomExamples
import SolidityBridge.ExternalEvm
import SolidityBridge.Adversary
import SolidityBridge.Loop
import SolidityBridge.ModelTheory
import SolidityBridge.ProofTheory

/-! Boundary regressions and headline axiom audits for the optional package. -/

namespace Solidity.Bridge.Checks

private def umax : PrimTy.uint.Denote := ⟨115792089237316195423570985008687907853269984665640564039457584007913129639935, by decide⟩
private def one : PrimTy.uint.Denote := ⟨1, by decide⟩

/-- Checked overflow fails while the wrapping evaluator returns zero. -/
example : BinOp.add.evalT rfl umax one = none := by decide +kernel
example : (BinOp.addW.evalT rfl umax one).map Subtype.val = some 0 := by decide +kernel

/-- Panic and exhaustion refute unconditional modal duality. -/
example : Modality.diamond.afterRunTR (fun _ : Unit => False) (.error .exhausted) := by simp only [Modality.afterRunTR, Modality.onTHalt, ne_eq, Except.error.injEq, reduceCtorEq, not_false_eq_true, and_self]
example : Modality.box.afterRunTR (fun _ : Unit => True) (.error .exhausted) := by simp only [Modality.afterRunTR, Modality.onTHalt, ne_eq, Except.error.injEq, reduceCtorEq, not_false_eq_true, and_self]
example : ¬ Modality.box.afterRunTR (fun _ : Unit => True) (.error .panic) := by simp only [Modality.afterRunTR, Modality.onTHalt, ne_eq, not_true_eq_false, and_false, not_false_eq_true]
example : ¬ Modality.diamond.afterRunTR (fun _ : Unit => True) (.error .panic) := by simp only [Modality.afterRunTR, Modality.onTHalt, reduceCtorEq, ne_eq, not_true_eq_false, and_self, not_false_eq_true]

/-- The external interpreter uses top-of-stack first for noncommutative SUB. -/
example : (EvmYul.UInt256.sub (.ofNat 3) (.ofNat 5)).toNat = Evm.W - 2 := by decide +kernel
example : (EvmYul.UInt256.div (.ofNat 7) (.ofNat 0)).toNat = 0 := by decide +kernel
example : (EvmYul.UInt256.mod (.ofNat 7) (.ofNat 0)).toNat = 0 := by decide +kernel

/-- A hole under heap growth is part of the congruence API too. -/
example {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    (FCtx.grow FCtx.hole).fill φ = Fml.grow φ := rfl

private def delayedCallee {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (st : Storage C) (nt : Ledger) (sb : PrimTy.uint.Denote) : Adversary.Callee σ where
  Control := Nat
  Label := Unit
  system := ⟨fun n _ n' => n' = n + 1⟩
  initial := fun _ n => n = 0
  returns := fun n st' nt' sb' => n = 2 ∧ st' = st ∧ nt' = nt ∧ sb' = sb

/-- A real callee computation has internal transitions between yield and return. -/
example {C : Contract} {Γ : Ctx} (J : StateInv C) (σ : State C Γ)
    (r a : Val C Γ .uint) (o : Out C σ.H Γ)
    (st : Storage C) (nt : Ledger) (sb : PrimTy.uint.Denote)
    (hrun : TRun.transfer r a σ = .ok o) (hi : J.at o.st)
    (hback : J.at (o.st.havoc st nt sb)) :
    (Adversary.callLts J σ r a (delayedCallee σ st nt sb)).MTr .entry
      [.yield, .callee (), .callee (), .resume]
      (.finished (.ok ⟨o.st.havoc st nt sb, o.ext⟩)) :=
  .stepL (.enter hrun hi (show 0 = 0 from rfl))
    (.stepL (.callee (show 1 = 0 + 1 from rfl))
      (.stepL (.callee (show 2 = 1 + 1 from rfl))
        (.stepL (.resume ⟨rfl, rfl, rfl, rfl⟩ hback) .refl)))

end Solidity.Bridge.Checks

/-- info: 'Solidity.Bridge.Arith.uint_addW_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Arith.uint_addW_bitvec
/-- info: 'Solidity.Bridge.Arith.uint_subW_zmod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Arith.uint_subW_zmod
/-- info: 'Solidity.Bridge.wp_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.wp_dual
/-- info: 'Solidity.TLoop.run_correct_of_variant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.TLoop.run_correct_of_variant
/-- info: 'Solidity.Evm.External.simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.simulation
/-- info: 'Solidity.Evm.External.upstream_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.upstream_step
/-- info: 'Solidity.Bridge.Adversary.holdsC_iff_all_callees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Adversary.holdsC_iff_all_callees
/-- info: 'Solidity.FO.finite_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.FO.finite_support
