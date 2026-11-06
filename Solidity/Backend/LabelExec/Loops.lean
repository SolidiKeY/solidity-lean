import Solidity.Backend.LabelExec.Assembly

/-! Concrete control edges of the published structured loop expansion.
The body/condition may contain unsupported raw instructions: no reachability
or body termination follows merely from these byte-addressed edge laws. -/
namespace Solidity.Backend.LabelExec

/-- The actual items before the loop's backedge packet. -/
def backPrefix (cond : List Instr) (body : Block) (n : Nat) : List (Item Nat Empty) :=
  [.tag n] ++ cond.map .instr ++
    [.instr (.op .ISZERO), .pushTag (n+1), .instr (.op .JUMPI)] ++
    (body.expand (n+2)).1

/-- The expanded loop backedge of a top-level loop at base 0 (`emptyLink`)
executes to its head at byte zero.
This consumes actual assembly; it does not assume a successful jump step. -/
theorem loop_backedge (cond : List Instr) (body : Block) (n : Nat)
    (out : Assembled Empty)
    (h : assemble 0 emptyLink ((Block.loop cond body).expand n).1 = some out)
    (tail : Scalar.Stack) :
    advance 2 (encode out.code)
      ⟨size (emitPrefix ((Block.loop cond body).expand n).1 (backPrefix cond body n)),tail⟩ =
      some ⟨0,tail⟩ := by
  have hp : assemble 0 emptyLink
      (backPrefix cond body n ++ (.pushTag n :: .instr (.op .JUMP) :: [.tag (n+1)])) = some out := by
    simpa only [Block.expand, backPrefix, List.append_assoc] using h
  obtain ⟨j, hj, hr⟩ := assembled_jump (backPrefix cond body n) [.tag (n+1)] n out hp tail
  have hn : (tags ([] ++ ((Block.loop cond body).expand n).1 ++ [])).Nodup := by
    simpa only [List.nil_append, List.append_nil] using Block.tags_nodup (.loop cond body) n
  have hh : tagIndex ((Block.loop cond body).expand n).1 n = some 0 := by
    simpa only [List.nil_append, List.append_nil, List.length_nil] using
      (Block.loop_tagIndex cond body n [] [] hn).1
  have hj' : tagIndex ((Block.loop cond body).expand n).1 n = some j := by
    simpa only [Block.expand, backPrefix, List.append_assoc] using hj
  have hz : j = 0 := Option.some.inj (hj'.symm.trans hh)
  subst j
  have hoff : offset out.code 0 = 0 := rfl
  simpa only [Block.expand, backPrefix, List.append_assoc, hoff] using hr

/-- Items before the loop's emitted ISZERO test. -/
def checkPrefix (cond : List Instr) (n : Nat) : List (Item Nat Empty) :=
  [.tag n] ++ cond.map .instr

/-- Items after the conditional transfer: body, backedge, exit label. -/
def loopPost (body : Block) (n : Nat) : List (Item Nat Empty) :=
  (body.expand (n+2)).1 ++ [.pushTag n, .instr (.op .JUMP), .tag (n+1)]

/-- For a top-level loop at base 0, the expanded loop test goes to its last
(exit) label on zero,
otherwise to the body byte boundary after the emitted conditional transfer. -/
theorem loop_header (cond : List Instr) (body : Block) (n : Nat)
    (out : Assembled Empty)
    (h : assemble 0 emptyLink ((Block.loop cond body).expand n).1 = some out)
    (condition : Scalar.Word) (tail : Scalar.Stack) :
    advance 3 (encode out.code)
      ⟨size (emitPrefix ((Block.loop cond body).expand n).1 (checkPrefix cond n)),condition :: tail⟩ =
      if condition == 0 then
        some ⟨offset out.code (((Block.loop cond body).expand n).1.length-1),tail⟩
      else some ⟨size (emitPrefix ((Block.loop cond body).expand n).1 (checkPrefix cond n)) + 1 +
        (Instr.push (asmWidths 0 ((Block.loop cond body).expand n).1 (n+1))
          (labelImm ((Block.loop cond body).expand n).1 (n+1))).size + 1,tail⟩ := by
  have hi : testItems (checkPrefix cond n) (loopPost body n) (n+1) =
      ((Block.loop cond body).expand n).1 := by
    simp only [testItems, checkPrefix, loopPost, Block.expand, List.append_assoc,
      List.cons_append, List.nil_append]
  have hp : assemble 0 emptyLink
      (testItems (checkPrefix cond n) (loopPost body n) (n+1)) = some out := by
    rw [hi]
    exact h
  obtain ⟨j, hj, hr⟩ := assembled_test (checkPrefix cond n) (loopPost body n)
    (n+1) out hp condition tail
  rw [hi] at hj hr
  have hn : (tags ([] ++ ((Block.loop cond body).expand n).1 ++ [])).Nodup := by
    simpa only [List.nil_append, List.append_nil] using Block.tags_nodup (.loop cond body) n
  have hh : tagIndex ((Block.loop cond body).expand n).1 (n+1) =
      some (((Block.loop cond body).expand n).1.length-1) := by
    simpa only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] using
      (Block.loop_tagIndex cond body n [] [] hn).2
  have hj' : j = ((Block.loop cond body).expand n).1.length-1 :=
    Option.some.inj (hj.symm.trans hh)
  subst j
  exact hr

end Solidity.Backend.LabelExec
