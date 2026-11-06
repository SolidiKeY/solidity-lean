import Solidity.Optimizer.Laws
import Solidity.Optimizer.Simplify
import Solidity.Optimizer.UnusedVar
import Solidity.Optimizer.CSE
import Solidity.Optimizer.Inline
import Solidity.Optimizer.DeadCode
import Solidity.Optimizer.Loads
import Solidity.Optimizer.DeadStore
import Solidity.Optimizer.LICM

/-!
# The O02/O03 optimizer pipeline over lowering programs

One round inlines covered internal calls, propagates constants and copies,
simplifies and folds expressions (removing dead branches), removes code after a
halting statement in blocks, branches and loop bodies and dead local stores,
eliminates common subexpressions, redundant storage and memory loads
(`Prog.rle`), dead storage and memory stores (`Prog.dstore`), hoists
loop-invariant assignments under their loop's guard (`Prog.licm`) and
eliminates unused declarations, in that order (`round`); `Prog.optimize n` runs `n` rounds. Each stage is a proved pass of the O01 interface
(`Preserves SameRun`), so the pipeline is one by `Preserves.pipeline`
(`round_preserves`, `optimize_preserves`): the optimized program's typed run
equals the original's in every state (`Prog.optimize_runC`).
-/
namespace Solidity.Optimizer.ConstFold
open Solidity

variable {C : Contract}

/-- The stages of one round, in order. -/
def stages (Γ Γ' : Ctx) : List (Lowering.Pass C Γ Γ') :=
  [Prog.inl, Prog.cprop Facts.empty, Prog.simplify, Prog.cfold, Prog.dce, Prog.dse,
    Prog.cse [], Prog.rle [], Prog.dstore, Prog.licm, Prog.uve]

/-- One optimizer round. -/
def round (Γ Γ' : Ctx) : Lowering.Pass C Γ Γ' := Pass.pipeline (stages Γ Γ')

/-- One round preserves `SameRun`: each stage does (`Preserves.pipeline`). -/
theorem round_preserves (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ')) (round Γ Γ') :=
  Preserves.pipeline (Related := SameRun) (fun _ => rfl)
    (fun a b => show SameRun _ _ from Eq.trans a b) _ fun pass mem => by
    simp only [stages, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact inl_preserves Γ Γ'
    · exact cprop_preserves Γ Γ'
    · exact vopt_preserves simpFoldPass Γ Γ'
    · exact cfold_preserves Γ Γ'
    · exact dce_preserves Γ Γ'
    · exact dse_preserves Γ Γ'
    · exact cse_preserves Γ Γ'
    · exact rle_preserves Γ Γ'
    · exact dstore_preserves Γ Γ'
    · exact licm_preserves Γ Γ'
    · exact uve_preserves Γ Γ'

/-- `n` optimizer rounds. -/
def _root_.Solidity.Prog.optimize (n : Nat) {Γ Γ' : Ctx} (P : Prog C Γ Γ') : Prog C Γ Γ' :=
  Pass.pipeline (List.replicate n (round Γ Γ')) P

/-- `n` rounds preserve `SameRun`. -/
theorem optimize_preserves (n : Nat) (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ')) (Prog.optimize n) :=
  Preserves.pipeline (Related := SameRun) (fun _ => rfl)
    (fun a b => show SameRun _ _ from Eq.trans a b) _ fun pass mem => by
    rw [(List.eq_of_mem_replicate mem)]
    exact round_preserves Γ Γ'

/-- **The optimized program runs as the original, in every typed state.** -/
theorem _root_.Solidity.Prog.optimize_runC (n : Nat) {Γ Γ' : Ctx} (P : Prog C Γ Γ') :
    Prog.runC (Prog.optimize n P) = Prog.runC P :=
  (optimize_preserves n Γ Γ' P).symm

end Solidity.Optimizer.ConstFold
