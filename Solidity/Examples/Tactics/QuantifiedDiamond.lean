import Solidity.Solkey.QuantifiedDiamond
import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Semantics.RevertMemory
import Solidity.Tools.Counterexample
import Solidity.Examples.Termination

/-!
# Quantified invariants under ordinary scalar diamonds

The same imported source is retained in both solc pipelines. The nested
and mapping-prefix automation attempts are recorded as blocked in docs/loops.md.
Modal proofs
check the declared scalar variant; separate successful-run certificates
exclude the calculus's exhaustion alternative for the concrete countdown.
-/

namespace Solidity.Examples.Tactics.QuantifiedDiamond
open scoped Solidity.Scoped

/-- Every source function is retained and elaborated in this pipeline. -/
example : Solc.QuantifiedDiamond.report.all (·.status == .elaborated) = true := by decide +kernel

/-- The imported while loop checks its quantified invariant and scalar decrease. -/
theorem count : ⊨ᶠ Solc.QuantifiedDiamond.count.problem := by
  sol_symex
  sol_close

/-- Continue still executes the update of the imported for loop. -/
theorem forCount : ⊨ᶠ Solc.QuantifiedDiamond.forCount.problem := by
  sol_symex
  sol_close

/-- A nonempty quantified postcondition of the actual imported return. -/
theorem quantified_post : ⊨ᶠ dl[Solc.QuantifiedDiamond]{ ⟨ uint r = count(); ⟩ (∀ uint q; q < 3 → q < r) } := by
  sol_symex
  sol_close

/-- The nearby false quantified post has the concrete witness q = 2. -/
theorem quantified_post_false : ¬ (⊨ᶠ dl[Solc.QuantifiedDiamond]{ ⟨ uint r = count(); ⟩ (∀ uint q; q < 3 → q < r - 1) }) := by
  sol_refute

private def initial : State Solc.QuantifiedDiamond [] := State.init Solc.QuantifiedDiamond

/-- A concrete kernel execution witness for the imported countdown. -/
theorem count_fuel : (Solc.QuantifiedDiamond.count.runF 4 initial).toOption.isSome = true := by
  decide +kernel

/-- Successful unbounded execution excludes both exhaustion and divergence. -/
theorem count_success : (Prog.run initial Solc.QuantifiedDiamond.count).toOption.isSome = true :=
  (Prog.runF_approx 4 _ initial).returned count_fuel

/-- A concrete kernel execution witness for the mapping-fill example. -/
theorem fill_fuel : (Solc.QuantifiedDiamond.fill.runF 4 initial).toOption.isSome = true := by
  decide +kernel

/-- The mapping-fill example also has a successful unbounded run. -/
theorem fill_success : (Prog.run initial Solc.QuantifiedDiamond.fill).toOption.isSome = true :=
  (Prog.runF_approx 4 _ initial).returned fill_fuel

/-- The false scalar control has an actual panic, not an unclosed proof alone. -/
theorem falsePost_fuel : (Solc.QuantifiedDiamond.falsePost.runF 4 initial).halt? = some .panic := by
  decide +kernel

theorem falsePost_panics : (Prog.run initial Solc.QuantifiedDiamond.falsePost).halt? = some .panic :=
  Prog.run_halt_of_runF _ initial 4 (by decide) falsePost_fuel

/-- The actual imported infinite loop diverges, whatever its annotations. -/
theorem nonterminating_diverges (σ : State Solc.QuantifiedDiamond []) :
    Prog.run σ Solc.QuantifiedDiamond.nonterminating = .error .diverge := by
  change TRun.seq (TRun.loop (.simple (.bool true)) .refl TRun.nil) TRun.nil σ = _
  have hloop : TRun.loop (C := Solc.QuantifiedDiamond) (Γ := [])
      (.simple (.bool true)) .refl TRun.nil σ = .error .diverge := by
    change TLoop.run (fun o : Out Solc.QuantifiedDiamond σ.H [] => .ok o)
      (fun _ => .ok true) ⟨σ, List.prefix_refl _⟩ = _
    exact Solidity.Examples.Termination.spin_diverges _
  unfold TRun.seq
  rw [hloop]

/-- Every source function is retained and elaborated in this pipeline. -/
example : SolcIR.QuantifiedDiamond.report.all (·.status == .elaborated) = true := by decide +kernel

/-- The imported while loop checks its quantified invariant and scalar decrease. -/
theorem countIR : ⊨ᶠ SolcIR.QuantifiedDiamond.count.problem := by
  sol_symex
  sol_close

/-- Continue still executes the update of the imported for loop. -/
theorem forCountIR : ⊨ᶠ SolcIR.QuantifiedDiamond.forCount.problem := by
  sol_symex
  sol_close

/-- A nonempty quantified postcondition of the actual imported return. -/
theorem quantified_postIR : ⊨ᶠ dl[SolcIR.QuantifiedDiamond]{ ⟨ uint r = count(); ⟩ (∀ uint q; q < 3 → q < r) } := by
  sol_symex
  sol_close

/-- The nearby false quantified post has the concrete witness q = 2. -/
theorem quantified_post_falseIR : ¬ (⊨ᶠ dl[SolcIR.QuantifiedDiamond]{ ⟨ uint r = count(); ⟩ (∀ uint q; q < 3 → q < r - 1) }) := by
  sol_refute

private def initialIR : State SolcIR.QuantifiedDiamond [] := State.init SolcIR.QuantifiedDiamond

/-- A concrete kernel execution witness for the imported countdown. -/
theorem count_fuelIR : (SolcIR.QuantifiedDiamond.count.runF 4 initialIR).toOption.isSome = true := by
  decide +kernel

/-- Successful unbounded execution excludes both exhaustion and divergence. -/
theorem count_successIR : (Prog.run initialIR SolcIR.QuantifiedDiamond.count).toOption.isSome = true :=
  (Prog.runF_approx 4 _ initialIR).returned count_fuelIR

/-- A concrete kernel execution witness for the mapping-fill example. -/
theorem fill_fuelIR : (SolcIR.QuantifiedDiamond.fill.runF 4 initialIR).toOption.isSome = true := by
  decide +kernel

/-- The mapping-fill example also has a successful unbounded run. -/
theorem fill_successIR : (Prog.run initialIR SolcIR.QuantifiedDiamond.fill).toOption.isSome = true :=
  (Prog.runF_approx 4 _ initialIR).returned fill_fuelIR

/-- The false scalar control has an actual panic, not an unclosed proof alone. -/
theorem falsePost_fuelIR : (SolcIR.QuantifiedDiamond.falsePost.runF 4 initialIR).halt? = some .panic := by
  decide +kernel

theorem falsePost_panicsIR : (Prog.run initialIR SolcIR.QuantifiedDiamond.falsePost).halt? = some .panic :=
  Prog.run_halt_of_runF _ initialIR 4 (by decide) falsePost_fuelIR

/-- The actual imported infinite loop diverges, whatever its annotations. -/
theorem nonterminating_divergesIR (σ : State SolcIR.QuantifiedDiamond []) :
    Prog.run σ SolcIR.QuantifiedDiamond.nonterminating = .error .diverge := by
  change TRun.seq (TRun.loop (.simple (.bool true)) .refl TRun.nil) TRun.nil σ = _
  have hloop : TRun.loop (C := SolcIR.QuantifiedDiamond) (Γ := [])
      (.simple (.bool true)) .refl TRun.nil σ = .error .diverge := by
    change TLoop.run (fun o : Out SolcIR.QuantifiedDiamond σ.H [] => .ok o)
      (fun _ => .ok true) ⟨σ, List.prefix_refl _⟩ = _
    exact Solidity.Examples.Termination.spin_diverges _
  unfold TRun.seq
  rw [hloop]

#print axioms count
#print axioms quantified_post
#print axioms quantified_post_false
#print axioms quantified_postIR
#print axioms quantified_post_falseIR
#print axioms count_successIR
#print axioms fill_successIR
#print axioms count_success
#print axioms fill_success
#print axioms nonterminating_diverges
#print axioms Premise.sound_whileInvDiamond
#print axioms invFml_up_holds
end Solidity.Examples.Tactics.QuantifiedDiamond
