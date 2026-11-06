import Solidity.Backend.LabelExec.LoopExit

/-! A whole zero-literal loop control with an unsupported body. The loop
passes it without fetching it, then reaches EOF; EOF refusal is not a halt,
EVM error, source fixture or a native execution result. -/
namespace Solidity.Backend.LabelExec.LoopExitControls

def block : Block := .loop [.push 0 #v[]] (.code [.op .STOP])

/-- STOP is outside the supported numeric/control step slice. -/
theorem unsupported_stop (tail : Scalar.Stack) :
    step [Op.STOP.code] ⟨0,tail⟩ = none := by rfl

/-- Actual assembly exists although the body has an unsupported instruction. -/
theorem assembly_exists : ∃ out, assemble 0 emptyLink (block.expand 0).1 = some out := by
  have hb : ∀ l ∈ refs (block.expand 0).1,
      0 + tagOffset (fun _ => (32 : Fin 33)) (block.expand 0).1 l < 256^32 := by
    intro l hl
    have hr : refs (block.expand 0).1 = [1,0] := rfl
    rw [hr] at hl
    have hm : l = 1 ∨ l = 0 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hl
    rcases hm with rfl | rfl <;> decide
  exact Option.isSome_iff_exists.mp (Block.expand_assemble_isSome block 0 0 emptyLink hb)

/-- The same actual assembly executes six steps past the unfetched STOP body
and exit marker, reaching EOF. Its seventh step refuses, rather than halting. -/
theorem skips_unsupported_body (tail : Scalar.Stack) :
    ∃ out, assemble 0 emptyLink (block.expand 0).1 = some out ∧
      advance 6 (encode out.code) ⟨0,tail⟩ = some ⟨size out.code,tail⟩ ∧
      advance 7 (encode out.code) ⟨0,tail⟩ = none := by
  obtain ⟨out,ho⟩ := assembly_exists
  have he : offset out.code ((block.expand 0).1.length-1)+1 = size out.code :=
    (Block.expand_loop_layout [.push 0 #v[]] (.code [.op .STOP]) 0 0 emptyLink ho).2.2.2.2
  have hh : advance 6 (encode out.code) ⟨0,tail⟩ = some ⟨size out.code,tail⟩ := by
    rw [← he]
    simpa only [emitPrefix, List.map_nil, size, List.sum_nil, List.length_nil,
      Nat.zero_add] using
      zero_loop_complete [] [] (.code [.op .STOP]) 0 out ho tail
  have hr : advance 7 (encode out.code) ⟨0,tail⟩ = none := by
    have hc : advance 7 (encode out.code) ⟨0,tail⟩ =
        (advance 6 (encode out.code) ⟨0,tail⟩).bind (step (encode out.code)) := by
      simp only [advance, Option.bind_assoc, Option.bind_fun_some]
    rw [hc, hh, Option.bind_some, step_at_end]
  exact ⟨out,ho,hh,hr⟩

end Solidity.Backend.LabelExec.LoopExitControls
