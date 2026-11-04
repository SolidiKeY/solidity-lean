import Solidity.Backend.Selection.BranchLayout

/-! Static prefix views of the existing loop expansion, reusing fixed-items
adapters rather than introducing a second compilation or execution framework. -/
namespace Solidity.Backend.Selection.ExecutionTrace.LoopLayout

structure Placement where
  before : List (Item Nat Empty)
  after : List (Item Nat Empty)
  condition : Program
  body : Block
  label : Nat

namespace Placement

def bodyItems (p : Placement) : List (Item Nat Empty) := (p.body.expand (p.label + 2)).1
def header (p : Placement) : List (Item Nat Empty) :=
  [.instr (.op .ISZERO), .pushTag (p.label + 1), .instr (.op .JUMPI)]
def back (p : Placement) : List (Item Nat Empty) := [.pushTag p.label, .instr (.op .JUMP)]
def conditionPre (p : Placement) : List (Item Nat Empty) := p.before ++ [.tag p.label]
def checked (p : Placement) : List (Item Nat Empty) := p.conditionPre ++ p.condition.map Item.instr
def bodyPre (p : Placement) : List (Item Nat Empty) := p.checked ++ p.header
def backPre (p : Placement) : List (Item Nat Empty) := p.bodyPre ++ p.bodyItems
def endPre (p : Placement) : List (Item Nat Empty) := p.backPre ++ p.back
def items (p : Placement) : List (Item Nat Empty) := p.endPre ++ [.tag (p.label + 1)] ++ p.after
def pc (p : Placement) (pre : List (Item Nat Empty)) : Nat := size (LabelExec.emitPrefix p.items pre)

theorem items_eq (p : Placement) :
    p.before ++ ((Block.loop p.condition p.body).expand p.label).1 ++ p.after = p.items := by
  simp only [items, endPre, backPre, bodyPre, checked, conditionPre, header, back,
    bodyItems, Block.expand, List.append_assoc, List.cons_append, List.nil_append]

theorem block_prefix (p : Placement) :
    p.before ++ ((Block.loop p.condition p.body).expand p.label).1 = p.endPre ++ [.tag (p.label + 1)] := by
  simp only [endPre, backPre, bodyPre, checked, conditionPre, header, back,
    bodyItems, Block.expand, List.append_assoc, List.cons_append, List.nil_append]

theorem head_split (p : Placement) : p.items = p.before ++ .tag p.label ::
    (p.condition.map Item.instr ++ p.header ++ p.bodyItems ++ p.back ++ [.tag (p.label + 1)] ++ p.after) := by
  simp only [items, endPre, backPre, bodyPre, checked, conditionPre,
    List.append_assoc, List.cons_append, List.nil_append]

theorem condition_split (p : Placement) : p.conditionPre ++ p.condition.map Item.instr ++
    (p.header ++ p.bodyItems ++ p.back ++ [.tag (p.label + 1)] ++ p.after) = p.items := by
  simp only [items, endPre, backPre, bodyPre, checked, List.append_assoc]

theorem header_split (p : Placement) : LabelExec.testItems p.checked
    (p.bodyItems ++ p.back ++ [.tag (p.label + 1)] ++ p.after) (p.label + 1) = p.items := by
  simp only [LabelExec.testItems, items, endPre, backPre, bodyPre, header,
    List.append_assoc, List.cons_append, List.nil_append]

theorem body_split (p : Placement) : p.bodyPre ++ p.bodyItems ++
    (p.back ++ [.tag (p.label + 1)] ++ p.after) = p.items := by
  simp only [items, endPre, backPre, List.append_assoc]

theorem back_split (p : Placement) : p.backPre ++ .pushTag p.label ::
    .instr (.op .JUMP) :: .tag (p.label + 1) :: p.after = p.items := by
  simp only [items, endPre, back, List.append_assoc, List.cons_append, List.nil_append]

theorem end_split (p : Placement) : p.items = p.endPre ++ .tag (p.label + 1) :: p.after := by
  simp only [items, List.append_assoc, List.cons_append, List.nil_append]

theorem head_index (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out) :
    tagIndex p.items p.label = some p.before.length :=
  BranchLayout.index_of_split p.items p.before
    (p.condition.map Item.instr ++ p.header ++ p.bodyItems ++ p.back ++ [.tag (p.label + 1)] ++ p.after)
    p.label out assembly p.head_split

theorem end_index (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out) :
    tagIndex p.items (p.label + 1) = some p.endPre.length :=
  BranchLayout.index_of_split p.items p.endPre p.after (p.label + 1) out assembly p.end_split

theorem head_pc (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out) :
    offset out.code p.before.length = p.pc p.before :=
  BranchLayout.offset_of_split p.items p.before
    (.tag p.label :: (p.condition.map Item.instr ++ p.header ++ p.bodyItems ++ p.back ++ [.tag (p.label + 1)] ++ p.after))
    out assembly p.head_split

theorem end_pc (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out) :
    offset out.code p.endPre.length = p.pc p.endPre :=
  BranchLayout.offset_of_split p.items p.endPre (.tag (p.label + 1) :: p.after) out assembly p.end_split

#print axioms items_eq
#print axioms block_prefix
#print axioms head_index
#print axioms end_index
#print axioms head_pc
#print axioms end_pc

end Placement
end Solidity.Backend.Selection.ExecutionTrace.LoopLayout
