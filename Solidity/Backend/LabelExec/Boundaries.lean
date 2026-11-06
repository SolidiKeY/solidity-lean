import Solidity.Backend.LabelExec.Placement

/-! Fetch and step at actual encoded instruction indices. An item index is
converted through offset; it is never treated as a byte PC. This reuses the
published fetch policy and does not assert validity at arbitrary byte offsets. -/
namespace Solidity.Backend.LabelExec

/-- Actual instruction selection supplies both fetched instruction and suffix. -/
theorem fetch_at (p : Program) (k : Nat) (i : Instr) (h : p[k]? = some i) :
    Creation.fetch ((encode p).drop (offset p k)) = some (i,encode (p.drop (k+1))) := by
  obtain ⟨hk,hi⟩ := List.getElem?_eq_some_iff.mp h
  have hd : p.drop k = i :: p.drop (k+1) := by
    rw [List.drop_eq_getElem_cons hk, hi]
  have he : p = p.take k ++ (i :: p.drop (k+1)) :=
    (List.take_append_drop k p).symm.trans (congrArg (p.take k ++ ·) hd)
  have hc : encode p = encode (p.take k) ++ (i.encode ++ encode (p.drop (k+1))) := by
    calc
      encode p = encode (p.take k ++ (i :: p.drop (k+1))) := congrArg encode he
      _ = _ := by rw [encode_append, encode_cons]
  rw [hc]
  change Creation.fetch ((encode (p.take k) ++ (i.encode ++ encode (p.drop (k+1)))).drop
    (size (p.take k))) = _
  rw [← length_encode (p.take k)]
  exact fetch_prefix _ _ _

/-- Preserve the exact operation-specific effect, including its real refusal. -/
theorem step_at (p : Program) (k : Nat) (i : Instr) (h : p[k]? = some i)
    (stack : Scalar.Stack) :
    step (encode p) ⟨offset p k,stack⟩ = effect (encode p) i ⟨offset p k,stack⟩ := by
  simp only [step, fetch_at p k i h, Option.bind_some]

/-- A resolved tag really executes JUMPDEST at its emitted byte offset. -/
theorem assembled_tag_step (items : List (Item Nat Empty)) (label k : Nat)
    (out : Assembled Empty) (h : assemble 0 emptyLink items = some out)
    (hk : tagIndex items label = some k) (tail : Scalar.Stack) :
    step (encode out.code) ⟨offset out.code k,tail⟩ =
      some ⟨offset out.code k+1,tail⟩ := by
  have hi : items[k]? = some (.tag label) := tagIndex_get hk
  have hc : out.code[k]? = some (.op .JUMPDEST) := by
    rw [(assemble_eq h).2.1, List.getElem?_map, hi]
    rfl
  rw [step_at out.code k (.op .JUMPDEST) hc]
  rfl

/-- End of this byte slice has no fetched instruction; it is not an EVM halt. -/
theorem step_at_end (p : Program) (stack : Scalar.Stack) :
    step (encode p) ⟨size p,stack⟩ = none := by
  simp only [step, ← length_encode p, List.drop_length, Creation.fetch, Option.bind_none]

end Solidity.Backend.LabelExec
