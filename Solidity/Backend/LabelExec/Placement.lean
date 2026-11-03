import Solidity.Backend.LabelExec.Loops

/-! A loop may be embedded after/before arbitrary assembler items in a full
runtime assembled at base zero. Byte offsets come from actual emitted code,
not item counts. This is local packet execution, not loop-entry reachability
or arbitrary external section relocation. -/
namespace Solidity.Backend.LabelExec

def placedItems (before after : List (Item Nat Empty)) (cond : List Instr)
    (body : Block) (n : Nat) : List (Item Nat Empty) :=
  before ++ ((Block.loop cond body).expand n).1 ++ after

/-- A loop's actual backedge reaches its emitted head after arbitrary items,
not byte zero or the number of preceding items. Whole-runtime base remains zero. -/
theorem loop_backedge_at (before after : List (Item Nat Empty)) (cond : List Instr)
    (body : Block) (n : Nat) (out : Assembled Empty)
    (h : assemble 0 emptyLink (placedItems before after cond body n) = some out)
    (tail : Scalar.Stack) :
    advance 2 (encode out.code)
      ⟨size (emitPrefix (placedItems before after cond body n)
        (before ++ backPrefix cond body n)),tail⟩ =
      some ⟨offset out.code before.length,tail⟩ := by
  have hp : assemble 0 emptyLink ((before ++ backPrefix cond body n) ++
      (.pushTag n :: .instr (.op .JUMP) :: .tag (n+1) :: after)) = some out := by
    simpa only [placedItems, Block.expand, backPrefix, List.append_assoc,
      List.cons_append, List.nil_append] using h
  obtain ⟨j,hj,hr⟩ := assembled_jump (before ++ backPrefix cond body n)
    (.tag (n+1) :: after) n out hp tail
  have hn : (tags (before ++ ((Block.loop cond body).expand n).1 ++ after)).Nodup := by
    have ho : layoutOk 0 (placedItems before after cond body n)
        (asmWidths 0 (placedItems before after cond body n)) = true := (assemble_eq h).1
    simp only [layoutOk, Bool.and_eq_true, decide_eq_true_eq] at ho
    exact ho.1.1
  have hh : tagIndex (placedItems before after cond body n) n = some before.length :=
    (Block.loop_tagIndex cond body n before after hn).1
  have hj' : tagIndex (placedItems before after cond body n) n = some j := by
    simpa only [placedItems, Block.expand, backPrefix, List.append_assoc,
      List.cons_append, List.nil_append] using hj
  have hz : j = before.length := Option.some.inj (hj'.symm.trans hh)
  subst j
  simpa only [placedItems, Block.expand, backPrefix, List.append_assoc,
    List.cons_append, List.nil_append] using hr

/-- Both raw condition arms at the actual emitted test of an embedded loop. -/
theorem loop_header_at (before after : List (Item Nat Empty)) (cond : List Instr)
    (body : Block) (n : Nat) (out : Assembled Empty)
    (h : assemble 0 emptyLink (placedItems before after cond body n) = some out)
    (condition : Scalar.Word) (tail : Scalar.Stack) :
    advance 3 (encode out.code)
      ⟨size (emitPrefix (placedItems before after cond body n)
        (before ++ checkPrefix cond n)),condition :: tail⟩ =
      if condition == 0 then
        some ⟨offset out.code (before.length + ((Block.loop cond body).expand n).1.length-1),tail⟩
      else some ⟨size (emitPrefix (placedItems before after cond body n)
        (before ++ checkPrefix cond n)) + 1 +
        (Instr.push (asmWidths 0 (placedItems before after cond body n) (n+1))
          (labelImm (placedItems before after cond body n) (n+1))).size + 1,tail⟩ := by
  have hi : testItems (before ++ checkPrefix cond n) (loopPost body n ++ after) (n+1) =
      placedItems before after cond body n := by
    simp only [placedItems, testItems, checkPrefix, loopPost, Block.expand,
      List.append_assoc, List.cons_append, List.nil_append]
  have hp : assemble 0 emptyLink
      (testItems (before ++ checkPrefix cond n) (loopPost body n ++ after) (n+1)) = some out := by
    rw [hi]
    exact h
  obtain ⟨j,hj,hr⟩ := assembled_test (before ++ checkPrefix cond n)
    (loopPost body n ++ after) (n+1) out hp condition tail
  rw [hi] at hj hr
  have hn : (tags (before ++ ((Block.loop cond body).expand n).1 ++ after)).Nodup := by
    have ho : layoutOk 0 (placedItems before after cond body n)
        (asmWidths 0 (placedItems before after cond body n)) = true := (assemble_eq h).1
    simp only [layoutOk, Bool.and_eq_true, decide_eq_true_eq] at ho
    exact ho.1.1
  have hh : tagIndex (placedItems before after cond body n) (n+1) =
      some (before.length + ((Block.loop cond body).expand n).1.length-1) :=
    (Block.loop_tagIndex cond body n before after hn).2
  have hj' : j = before.length + ((Block.loop cond body).expand n).1.length-1 :=
    Option.some.inj (hj.symm.trans hh)
  subst j
  exact hr

end Solidity.Backend.LabelExec
