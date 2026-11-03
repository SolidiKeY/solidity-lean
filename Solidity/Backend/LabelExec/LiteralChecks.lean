import Solidity.Backend.LabelExec.LiteralLoops
import Solidity.Backend.LabelExec.Checks

/-! Two actually assembled loop entries differing only in their literal
condition. These are kernel controls for local gasless execution, not native
fixtures, a source witness, body termination or EVM fuel behavior. -/
namespace Solidity.Backend.LabelExec.LiteralChecks

/-- A nonzero literal, rather than an independently supplied test-stack word. -/
def nonzeroCondition : List Instr := [.push 1 #v[1]]
def nonzeroBlock : Block := .seq (.code [Scalar.pushByte 0x5b, .op .POP])
  (.seq (.loop nonzeroCondition (.code [])) (.code [.op .STOP]))
def nonzeroItems : List (Item Nat Empty) :=
  placedItems Checks.before Checks.after nonzeroCondition (.code []) 0

/-- The changed condition still has real successful assembly. -/
theorem nonzero_assembly_exists : ∃ out, assemble 0 emptyLink nonzeroItems = some out := by
  have hbound : ∀ l ∈ refs (nonzeroBlock.expand 0).1,
      0 + tagOffset (fun _ => (32 : Fin 33)) (nonzeroBlock.expand 0).1 l < 256^32 := by
    intro l hl
    have hrefs : refs (nonzeroBlock.expand 0).1 = [1,0] := rfl
    rw [hrefs] at hl
    have hm : l = 1 ∨ l = 0 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hl
    rcases hm with rfl | rfl <;> decide
  have hex : (assemble 0 emptyLink (nonzeroBlock.expand 0).1).isSome :=
    Block.expand_assemble_isSome nonzeroBlock 0 0 emptyLink hbound
  have he : (nonzeroBlock.expand 0).1 = nonzeroItems := rfl
  rw [he] at hex
  exact Option.isSome_iff_exists.mp hex

/-- The zero literal executes from its actual emitted head to the exit label,
not from an assumed reached condition state. Original physical tail survives. -/
theorem zero_entry (tail : Scalar.Stack) :
    ∃ out, assemble 0 emptyLink Checks.items = some out ∧
      advance 5 (encode out.code)
        ⟨size (emitPrefix Checks.items Checks.before),tail⟩ =
        some ⟨offset out.code
          (Checks.before.length + ((Block.loop Checks.condition (.code [])).expand 0).1.length-1),tail⟩ := by
  obtain ⟨out,ho⟩ := Checks.assembly_exists
  refine ⟨out,ho,?_⟩
  have hz : (Scalar.immediate ([] : List UInt8) == 0) = true := rfl
  simpa only [Checks.items, Checks.condition, Vector.toList_mk, Array.toList_empty,
    hz, if_pos rfl] using
    literal_loop_header_at Checks.before Checks.after 0 #v[] (.code []) 0 out ho tail

/-- The nonzero literal enters the body-side byte boundary rather than taking
the zero exit. This proves the computed branch; it does not execute the body. -/
theorem nonzero_entry (tail : Scalar.Stack) :
    ∃ out, assemble 0 emptyLink nonzeroItems = some out ∧
      advance 5 (encode out.code)
        ⟨size (emitPrefix nonzeroItems Checks.before),tail⟩ =
        some ⟨size (emitPrefix nonzeroItems
            (Checks.before ++ checkPrefix nonzeroCondition 0)) + 1 +
          (Instr.push (asmWidths 0 nonzeroItems 1) (labelImm nonzeroItems 1)).size + 1,tail⟩ := by
  obtain ⟨out,ho⟩ := nonzero_assembly_exists
  refine ⟨out,ho,?_⟩
  have hn : (Scalar.immediate ([1] : List UInt8) == 0) = false := rfl
  simpa only [nonzeroItems, nonzeroCondition, Vector.toList_mk, List.toList_toArray,
    hn, Bool.false_eq_true, if_false] using
    literal_loop_header_at Checks.before Checks.after 1 #v[1] (.code []) 0 out ho tail

end Solidity.Backend.LabelExec.LiteralChecks
