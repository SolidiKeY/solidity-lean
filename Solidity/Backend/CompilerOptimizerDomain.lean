import Solidity.Backend.CompilerOptimizerDomain.StmtFold
import Solidity.Backend.CompilerOptimizerDomain.DeadCode
import Solidity.Backend.CompilerOptimizerDomain.DeadStore
import Solidity.Backend.CompilerOptimizerDomain.LICM
import Solidity.Backend.CompilerOptimizerDomain.Simplify
import Solidity.Backend.CompilerOptimizerDomain.Inline
import Solidity.Backend.CompilerOptimizerDomain.CSE
import Solidity.Backend.CompilerOptimizerDomain.Propagate
import Solidity.Backend.CompilerOptimizerDomain.UnusedVar
import Solidity.Backend.CompilerOptimizerDomain.Loads
import Solidity.Optimizer.Pipeline

/-! The unchanged public compiler domain is closed under every optimizer iteration.
This prerequisite does not change the optimized compiler's fallback or endpoint. -/
namespace Solidity.Backend.CompilerOptimizerDomain
open Solidity Solidity.Optimizer Solidity.Optimizer.ConstFold
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract} {Γ Δ : Ctx} {K : Kinds}

/-- Every actual optimizer stage preserves the original accepted domain. -/
theorem stage_ok (pass : Lowering.Pass C Γ Δ) (hm : pass ∈ stages Γ Δ)
    {P : Solidity.Prog C Γ Δ} (hP : ProgOk K P) : ProgOk K (pass P) := by
  simp only [stages, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prog_inl_ok hP
  · exact prog_cprop_ok hP facts_empty_ok
  · exact prog_simplify_ok hP
  · exact prog_cfold_ok hP
  · exact prog_dce_ok hP
  · exact prog_dse_ok hP
  · exact prog_cse_ok hP []
  · exact prog_rle_ok hP loads_nil_ok
  · exact prog_dstore_ok hP
  · exact prog_licm_ok hP
  · exact prog_uve_ok hP

/-- Use the generic pipeline relation with implication between domain predicates. -/
theorem round_ok {P : Solidity.Prog C Γ Δ} (hP : ProgOk K P) :
    ProgOk K (round Γ Δ P) :=
  Preserves.pipeline (Related := fun P Q => ProgOk K P → ProgOk K Q)
    (fun _ h => h) (fun a b h => b (a h)) (stages Γ Δ)
    (fun pass hm _ h => stage_ok pass hm h) P hP

/-- No bound or additional premise on the iteration count or accepted input. -/
theorem optimize_ok (n : Nat) {P : Solidity.Prog C Γ Δ} (hP : ProgOk K P) :
    ProgOk K (P.optimize n) := by
  apply Preserves.pipeline (Related := fun P Q => ProgOk K P → ProgOk K Q)
    (fun _ h => h) (fun a b h => b (a h)) (List.replicate n (round Γ Δ)) _ P hP
  intro pass hm Q hQ
  rw [List.eq_of_mem_replicate hm]
  exact round_ok hQ

/-- Reusable optimizer resource invariant for the unchanged public domain. -/
theorem optimize_pushes (n : Nat) {P : Solidity.Prog C Γ Δ} (hP : ProgOk [] P) :
    Evm.Prog.pushes (P.optimize n) = 0 := (optimize_ok n hP).quiet.1

/-- Reusable fresh-frame fragment acceptance for the unchanged public domain. -/
theorem optimize_frag (n : Nat) {P : Solidity.Prog C Γ Δ} (hP : ProgOk [] P) :
    ∃ G, Evm.inFragP (Evm.Frag.init Γ) (P.optimize n) = some G := by
  obtain ⟨G, h, _⟩ := (optimize_ok n hP).frag (Evm.Frag.init Γ) (Matches.init Γ)
  exact ⟨G, h⟩

end Solidity.Backend.CompilerOptimizerDomain
