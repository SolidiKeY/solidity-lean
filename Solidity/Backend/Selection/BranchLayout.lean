import Solidity.Backend.Selection.ControlPackets

/-! Prefix views of the existing conditional expansion. The small placement
lemmas keep layout normalization outside whole-execution proof budgets. -/
namespace Solidity.Backend.Selection.ExecutionTrace.BranchLayout

theorem index_of_split (items before after : List (Item Nat Empty)) (label : Nat)
    (out : Assembled Empty) (assembly : assemble 0 LabelExec.emptyLink items = some out)
    (split : items = before ++ .tag label :: after) : tagIndex items label = some before.length := by
  have checked : layoutOk 0 items (asmWidths 0 items) = true := (assemble_eq assembly).1
  simp only [layoutOk, Bool.and_eq_true, decide_eq_true_eq] at checked
  apply tagIndex_unique checked.1.1
  rw [split]
  simp only [List.getElem?_append_right (Nat.le_refl before.length), Nat.sub_self,
    List.getElem?_cons_zero]

theorem offset_of_split (items before after : List (Item Nat Empty)) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink items = some out)
    (split : items = before ++ after) :
    offset out.code before.length = size (LabelExec.emitPrefix items before) := by
  have taken : items.take before.length = before := by rw [split, List.take_left]
  rw [(assemble_eq assembly).2.1]
  simp only [offset, ← List.map_take, taken, LabelExec.emitPrefix]

/-- Re-express an existing realization in a fixed whole assembled item list. -/
theorem realize_items {block : Block} {n m : Nat} (certificate : ControlCertificate block n m)
    (items before after : List (Item Nat Empty)) (label : Nat) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink items = some out)
    (split : before ++ (block.expand label).1 ++ after = items)
    (input output : Scalar.Stack) (height : input.length = n)
    (actual : StructuredExec block input output) :
    ∃ count, Safe (encode out.code) count
      ⟨size (LabelExec.emitPrefix items before),input⟩
      ⟨size (LabelExec.emitPrefix items (before ++ (block.expand label).1)),output⟩ := by
  have placed : assemble 0 LabelExec.emptyLink (before ++ (block.expand label).1 ++ after) = some out := by
    rw [split]; exact assembly
  obtain ⟨count,run,bounds⟩ := certificate.realize before after label out placed input output height actual
  rw [split] at run bounds
  exact ⟨count,run,bounds⟩

theorem scalar_items (items before after : List (Item Nat Empty)) (code : Program)
    (out : Assembled Empty) (assembly : assemble 0 LabelExec.emptyLink items = some out)
    (split : before ++ code.map Item.instr ++ after = items)
    (input output : Scalar.Stack) (actual : Scalar.run code input = some output)
    (capacity : Scalar.stackBound code (input.length : Int) = true) :
    Safe (encode out.code) code.length
      ⟨size (LabelExec.emitPrefix items before),input⟩
      ⟨size (LabelExec.emitPrefix items (before ++ code.map Item.instr)),output⟩ := by
  have placed : assemble 0 LabelExec.emptyLink (before ++ code.map Item.instr ++ after) = some out := by
    rw [split]; exact assembly
  have trace : Safe (encode out.code) code.length
      ⟨size (LabelExec.emitPrefix (before ++ code.map Item.instr ++ after) before),input⟩
      ⟨size (LabelExec.emitPrefix (before ++ code.map Item.instr ++ after)
        (before ++ code.map Item.instr)),output⟩ :=
    placed_scalar before after code out placed input output actual capacity
  rw [split] at trace
  exact trace

theorem test_items (items before after : List (Item Nat Empty)) (label : Nat)
    (out : Assembled Empty) (assembly : assemble 0 LabelExec.emptyLink items = some out)
    (split : LabelExec.testItems before after label = items)
    (word : Scalar.Word) (tail : Scalar.Stack) (room : tail.length + 2 ≤ 1024) :
    ∃ target, tagIndex items label = some target ∧ Safe (encode out.code) 3
      ⟨size (LabelExec.emitPrefix items before),word :: tail⟩
      ⟨if word == 0 then offset out.code target else size (LabelExec.emitPrefix items
        (before ++ [.instr (.op .ISZERO), .pushTag label, .instr (.op .JUMPI)])),tail⟩ := by
  have placed : assemble 0 LabelExec.emptyLink (LabelExec.testItems before after label) = some out := by
    rw [split]; exact assembly
  obtain ⟨target,found,trace⟩ := test before after label out placed word tail room
  rw [split] at found trace
  exact ⟨target,found,trace⟩

theorem jump_items (items before after : List (Item Nat Empty)) (label : Nat)
    (out : Assembled Empty) (assembly : assemble 0 LabelExec.emptyLink items = some out)
    (split : before ++ .pushTag label :: .instr (.op .JUMP) :: after = items)
    (tail : Scalar.Stack) (room : tail.length + 1 ≤ 1024) :
    ∃ target, tagIndex items label = some target ∧ Safe (encode out.code) 2
      ⟨size (LabelExec.emitPrefix items before),tail⟩ ⟨offset out.code target,tail⟩ := by
  have placed : assemble 0 LabelExec.emptyLink
      (before ++ .pushTag label :: .instr (.op .JUMP) :: after) = some out := by
    rw [split]; exact assembly
  obtain ⟨target,found,trace⟩ := jump before after label out placed tail room
  rw [split] at found trace
  exact ⟨target,found,trace⟩

theorem tag_items (items before after : List (Item Nat Empty)) (label : Nat)
    (out : Assembled Empty) (assembly : assemble 0 LabelExec.emptyLink items = some out)
    (split : items = before ++ .tag label :: after)
    (tail : Scalar.Stack) (room : tail.length ≤ 1024) : Safe (encode out.code) 1
      ⟨size (LabelExec.emitPrefix items before),tail⟩
      ⟨size (LabelExec.emitPrefix items (before ++ [.tag label])),tail⟩ := by
  have placed : assemble 0 LabelExec.emptyLink (before ++ .tag label :: after) = some out := by
    rw [← split]; exact assembly
  have trace : Safe (encode out.code) 1
      ⟨size (LabelExec.emitPrefix (before ++ .tag label :: after) before),tail⟩
      ⟨size (LabelExec.emitPrefix (before ++ .tag label :: after) (before ++ [.tag label])),tail⟩ :=
    tag before after label out placed tail room
  rw [← split] at trace
  exact trace

/-- Static coordinates for an existing Block.ite, not a new block language. -/
structure Placement where
  before : List (Item Nat Empty)
  after : List (Item Nat Empty)
  condition : Program
  yes : Block
  no : Block
  label : Nat

namespace Placement

def yesItems (p : Placement) : List (Item Nat Empty) := (p.yes.expand (p.label + 2)).1
def noLabel (p : Placement) : Nat := (p.yes.expand (p.label + 2)).2
def noItems (p : Placement) : List (Item Nat Empty) := (p.no.expand p.noLabel).1
def header (p : Placement) : List (Item Nat Empty) :=
  [.instr (.op .ISZERO), .pushTag p.label, .instr (.op .JUMPI)]
def join (p : Placement) : List (Item Nat Empty) := [.pushTag (p.label + 1), .instr (.op .JUMP)]
def checked (p : Placement) : List (Item Nat Empty) := p.before ++ p.condition.map Item.instr
def yesPre (p : Placement) : List (Item Nat Empty) := p.checked ++ p.header
def falsePre (p : Placement) : List (Item Nat Empty) := p.yesPre ++ p.yesItems ++ p.join
def noPre (p : Placement) : List (Item Nat Empty) := p.falsePre ++ [.tag p.label]
def endPre (p : Placement) : List (Item Nat Empty) := p.noPre ++ p.noItems
def items (p : Placement) : List (Item Nat Empty) := p.endPre ++ [.tag (p.label + 1)] ++ p.after
def pc (p : Placement) (pre : List (Item Nat Empty)) : Nat := size (LabelExec.emitPrefix p.items pre)

/-- These prefix views are exactly the published expansion. -/
theorem items_eq (p : Placement) :
    p.before ++ ((Block.ite p.condition p.yes p.no).expand p.label).1 ++ p.after = p.items := by
  simp only [items, endPre, noPre, falsePre, yesPre, checked, header, join,
    yesItems, noItems, noLabel, Block.expand, List.append_assoc, List.cons_append, List.nil_append]

theorem condition_split (p : Placement) :
    p.before ++ p.condition.map Item.instr ++
      (p.header ++ p.yesItems ++ p.join ++ [.tag p.label] ++ p.noItems ++ [.tag (p.label + 1)] ++ p.after) = p.items := by
  simp only [items, endPre, noPre, falsePre, yesPre, checked, List.append_assoc]

theorem header_split (p : Placement) : LabelExec.testItems p.checked
    (p.yesItems ++ p.join ++ [.tag p.label] ++ p.noItems ++ [.tag (p.label + 1)] ++ p.after) p.label = p.items := by
  simp only [LabelExec.testItems, items, endPre, noPre, falsePre, yesPre, header,
    List.append_assoc, List.cons_append, List.nil_append]

theorem yes_split (p : Placement) : p.yesPre ++ p.yesItems ++
    (p.join ++ [.tag p.label] ++ p.noItems ++ [.tag (p.label + 1)] ++ p.after) = p.items := by
  simp only [items, endPre, noPre, falsePre, List.append_assoc]

theorem no_split (p : Placement) : p.noPre ++ p.noItems ++ ([.tag (p.label + 1)] ++ p.after) = p.items := by
  simp only [items, endPre, List.append_assoc]

theorem join_split (p : Placement) : (p.yesPre ++ p.yesItems) ++
    .pushTag (p.label + 1) :: .instr (.op .JUMP) :: .tag p.label ::
      (p.noItems ++ [.tag (p.label + 1)] ++ p.after) = p.items := by
  simp only [items, endPre, noPre, falsePre, join, List.append_assoc, List.cons_append, List.nil_append]

theorem false_split (p : Placement) : p.items =
    p.falsePre ++ .tag p.label :: (p.noItems ++ [.tag (p.label + 1)] ++ p.after) := by
  simp only [items, endPre, noPre, List.append_assoc, List.cons_append, List.nil_append]

theorem end_split (p : Placement) : p.items = p.endPre ++ .tag (p.label + 1) :: p.after := by
  simp only [items, List.append_assoc, List.cons_append, List.nil_append]

theorem block_prefix (p : Placement) :
    p.before ++ ((Block.ite p.condition p.yes p.no).expand p.label).1 =
      p.endPre ++ [.tag (p.label + 1)] := by
  simp only [endPre, noPre, falsePre, yesPre, checked, header, join,
    yesItems, noItems, noLabel, Block.expand, List.append_assoc, List.cons_append, List.nil_append]

theorem false_index (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out) :
    tagIndex p.items p.label = some p.falsePre.length := by
  exact index_of_split p.items p.falsePre (p.noItems ++ [.tag (p.label + 1)] ++ p.after)
    p.label out assembly p.false_split

theorem end_index (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out) :
    tagIndex p.items (p.label + 1) = some p.endPre.length := by
  exact index_of_split p.items p.endPre p.after (p.label + 1) out assembly p.end_split

theorem false_pc (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out) :
    offset out.code p.falsePre.length = p.pc p.falsePre := by
  exact offset_of_split p.items p.falsePre
    (.tag p.label :: (p.noItems ++ [.tag (p.label + 1)] ++ p.after)) out assembly p.false_split

theorem end_pc (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out) :
    offset out.code p.endPre.length = p.pc p.endPre := by
  exact offset_of_split p.items p.endPre (.tag (p.label + 1) :: p.after) out assembly p.end_split

#print axioms index_of_split
#print axioms offset_of_split
#print axioms realize_items
#print axioms scalar_items
#print axioms test_items
#print axioms jump_items
#print axioms tag_items

#print axioms items_eq
#print axioms false_index
#print axioms end_index
#print axioms false_pc
#print axioms end_pc

end Placement
end Solidity.Backend.Selection.ExecutionTrace.BranchLayout
