import Solidity.Backend.LabelExec.Boundaries
import Solidity.Backend.LabelExec.LiteralLoops

/-! Consume a resolved exit label after the actual zero-literal loop header.
The endpoint is immediately after the loop, not a halt or EVM result. -/
namespace Solidity.Backend.LabelExec

/-- The last loop item executes its actual JUMPDEST even when embedded. -/
theorem loop_exit_step (before after : List (Item Nat Empty)) (cond : List Instr)
    (body : Block) (n : Nat) (out : Assembled Empty)
    (h : assemble 0 emptyLink (placedItems before after cond body n) = some out)
    (tail : Scalar.Stack) :
    let k := before.length + ((Block.loop cond body).expand n).1.length-1
    step (encode out.code) ⟨offset out.code k,tail⟩ =
      some ⟨offset out.code k+1,tail⟩ := by
  have hn : (tags (before ++ ((Block.loop cond body).expand n).1 ++ after)).Nodup := by
    have ho : layoutOk 0 (placedItems before after cond body n)
        (asmWidths 0 (placedItems before after cond body n)) = true := (assemble_eq h).1
    simp only [layoutOk, Bool.and_eq_true, decide_eq_true_eq] at ho
    exact ho.1.1
  exact assembled_tag_step _ (n+1) _ out h
    (Block.loop_tagIndex cond body n before after hn).2 tail

/-- A zero-literal loop executes through its exit label. The body is never
fetched; no run premise, body termination, or reached-test state is supplied. -/
theorem zero_loop_complete (before after : List (Item Nat Empty))
    (body : Block) (n : Nat) (out : Assembled Empty)
    (h : assemble 0 emptyLink (placedItems before after [.push 0 #v[]] body n) = some out)
    (tail : Scalar.Stack) :
    advance 6 (encode out.code)
      ⟨size (emitPrefix (placedItems before after [.push 0 #v[]] body n) before),tail⟩ =
      some ⟨offset out.code
        (before.length + ((Block.loop [.push 0 #v[]] body).expand n).1.length-1)+1,tail⟩ := by
  let s : State :=
    ⟨size (emitPrefix (placedItems before after [.push 0 #v[]] body n) before),tail⟩
  have hz : (Scalar.immediate ([] : List UInt8) == 0) = true := rfl
  have hh : advance 5 (encode out.code) s =
      some ⟨offset out.code
        (before.length + ((Block.loop [.push 0 #v[]] body).expand n).1.length-1),tail⟩ := by
    simpa only [Vector.toList_mk, Array.toList_empty, hz, if_pos rfl] using
      literal_loop_header_at before after 0 #v[] body n out h tail
  have hc : advance 6 (encode out.code) s =
      (advance 5 (encode out.code) s).bind (step (encode out.code)) := by
    simp only [advance, Option.bind_assoc, Option.bind_fun_some]
  rw [hc, hh, Option.bind_some]
  exact loop_exit_step before after [.push 0 #v[]] body n out h tail

end Solidity.Backend.LabelExec
