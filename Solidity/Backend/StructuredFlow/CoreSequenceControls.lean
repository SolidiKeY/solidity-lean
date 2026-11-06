import Solidity.Backend.StructuredFlow.CoreSequence

/-! A populated local is updated under a branch, then read by its continuation.
All whole-machine outcomes retain caller stack77 and exact memory cells. -/
namespace Solidity.Backend.StructuredFlow.CoreSequenceControls
open Solidity.Evm
private def C : Solidity.Contract := default
private def initial := freshT C 0 W_pos ⟨0,W_pos⟩
private def machine := {Machine.init (fun _ => 0) ⟨0,W_pos⟩ with stack := [w[77]]}
private def caller := initial.push (t := .val .uint) (uintT 41 (by decide))
private def loaded := {machine with mem := upd machine.mem 0 w[41]}
private def left : Solidity.Prog C [.val .uint] [.val .uint] :=
  .cons (.assignLocal .here (.simple (.lit 7 rfl))) .nil
private def right : Solidity.Prog C [.val .uint] [.val .uint] := .cons .revert .nil
private def tail : Solidity.Prog C [.val .uint] [.val .uint,.val .uint] :=
  .cons (.declLocal .uint (.fresh "copied-local" 0) (some (.simple (.local .here)))) .nil
private def branch (flag : Bool) : Solidity.Stmt C [.val .uint] [.val .uint] :=
  .ite (.simple (.bool flag)) left right
private def rest (flag : Bool) : Solidity.Prog C [.val .uint] [.val .uint,.val .uint] :=
  .cons (branch flag) tail
private def emitted (flag : Bool) := CoreSequence.emit 0 (.simple (.bool flag)) left right tail

-- This is an actual inhabited populated context, not a Sim assumption.
theorem represented : Sim C 1 0 (Frag.init [.val .uint]) caller loaded := by
  exact Sim.pushVal ((Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl).stack [w[77]])
    (p := .uint) (v := uintT 41 (by decide)) (w := w[41]) ⟨⟨41,by decide⟩,rfl,rfl⟩

theorem branch_admitted (flag : Bool) :
    inFrag (Frag.init [.val .uint]) (branch flag) = some (Frag.init [.val .uint]) := rfl

theorem tail_admitted : inFragP (Frag.init [.val .uint]) tail =
    some (Frag.init [.val .uint,.val .uint]) := rfl

theorem target_true : run (emitted true) loaded =
    .ok {loaded with mem := upd (upd loaded.mem 0 w[7]) 1 w[7]} 0 := by rfl

theorem target_false : run (emitted false) loaded = .revert := by rfl

theorem checked (flag : Bool) :
    StmtOut C (1 + Prog.pushes (rest flag)) 0 (Frag.init [.val .uint,.val .uint])
      (Prog.shrinks (rest flag)) (Prog.pays (rest flag))
      (Prog.asserts (rest flag)) (Solidity.Prog.run caller (rest flag))
      (run (emitted flag) loaded) loaded := by
  apply CoreSequence.admitted _ left right tail represented (branch_admitted flag) tail_admitted
  change 1 + 0 ≤ Lmax
  unfold Lmax
  decide

theorem source_true : Solidity.Prog.run caller (rest true) =
    .ok ⟨(initial.push (t := .val .uint) (uintT 7 (by decide))).push
      (t := .val .uint) (uintT 7 (by decide)),List.prefix_refl _⟩ := by
  change Solidity.Prog.runR (rest true) caller = _
  simp only [Solidity.Prog.runR_eq]
  rfl

theorem source_false : Solidity.Prog.run caller (rest false) = .error .revert := by
  change Solidity.Prog.runR (rest false) caller = _
  simp only [Solidity.Prog.runR_eq]
  rfl

theorem refusal_short_circuits : run (emitted false) loaded ≠
    .ok {loaded with mem := upd loaded.mem 1 w[41]} 0 := by
  rw [target_false]
  intro impossible
  cases impossible

theorem wrong_copy_refused : run (emitted true) loaded ≠
    .ok {loaded with mem := upd (upd loaded.mem 0 w[7]) 1 w[41]} 0 := by
  rw [target_true]
  intro impossible
  have value : (w[7] : Word) = w[41] := congrArg
    (fun outcome => match outcome with | .ok state _ => state.mem 1 | _ => w[0]) impossible
  exact (by decide : (w[7] : Word) ≠ w[41]) value
end Solidity.Backend.StructuredFlow.CoreSequenceControls
