import Solidity.Backend.LabelExec.Placement
import Solidity.Backend.LabelExec.FragmentControls

/-! Standalone kernel controls. The packet negatives are retained from the
prior owned Controls module, without its unmerged Executable dependencies.
The assembled loop witness uses only published Block/assembler interfaces.
These are gasless local cuts, not source execution or loop reachability. -/
namespace Solidity.Backend.LabelExec.Checks

def before : List (Item Nat Empty) :=
  [.instr (Scalar.pushByte 0x5b), .instr (.op .POP)]
def after : List (Item Nat Empty) := [.instr (.op .STOP)]
def condition : List Instr := [.push 0 #v[]]
def block : Block := .seq (.code [Scalar.pushByte 0x5b, .op .POP])
  (.seq (.loop condition (.code [])) (.code [.op .STOP]))
def items : List (Item Nat Empty) := placedItems before after condition (.code []) 0

/-- Actual assembly exists; no successful jump or selected output is a premise. -/
theorem assembly_exists : ∃ out, assemble 0 emptyLink items = some out := by
  have hbound : ∀ l ∈ refs (block.expand 0).1,
      0 + tagOffset (fun _ => (32 : Fin 33)) (block.expand 0).1 l < 256^32 := by
    intro l hl
    have hrefs : refs (block.expand 0).1 = [1,0] := rfl
    rw [hrefs] at hl
    have hm : l = 1 ∨ l = 0 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hl
    rcases hm with rfl | rfl <;> decide
  have hex : (assemble 0 emptyLink (block.expand 0).1).isSome :=
    Block.expand_assemble_isSome block 0 0 emptyLink hbound
  have he : (block.expand 0).1 = items := rfl
  rw [he] at hex
  exact Option.isSome_iff_exists.mp hex

/-- The preceding two items occupy THREE bytes, including PUSH payload. -/
theorem head_offset (out : Assembled Empty)
    (h : assemble 0 emptyLink items = some out) : offset out.code before.length = 3 := by
  rw [(assemble_layout h).2.1]
  rfl

/-- A nonvacuous assembled local backedge after a nonempty prefix. -/
theorem assembled_loop (tail : Scalar.Stack) :
    ∃ out, assemble 0 emptyLink items = some out ∧
      advance 2 (encode out.code)
        ⟨size (emitPrefix items (before ++ backPrefix condition (.code []) 0)),tail⟩ =
        some ⟨3,tail⟩ := by
  obtain ⟨out,ho⟩ := assembly_exists
  refine ⟨out,ho,?_⟩
  have hr : advance 2 (encode out.code)
      ⟨size (emitPrefix items (before ++ backPrefix condition (.code []) 0)),tail⟩ =
      some ⟨offset out.code before.length,tail⟩ :=
    loop_backedge_at before after condition (.code []) 0 out ho tail
  rw [head_offset out ho] at hr
  exact hr

/-- Offset zero holds PUSH0, so it cannot be a JUMPDEST. -/
theorem push0_not_destination : validJumpdest [0x5f,0x57] 0 = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hn : ([0x5f,0x57] : List UInt8)[0]? ≠ some Op.JUMPDEST.code := by decide
  exact hn ((validJumpdest_iff _ _).mp h).1

/-- A real zero condition bypasses the invalid-target check. -/
theorem untaken_invalid : advance 2 [0x5f,0x57] ⟨0,[0,7]⟩ = some ⟨2,[7]⟩ := by
  have hz : ((0 : Scalar.Word) == 0) = true := rfl
  simpa only [hz, if_pos rfl] using jumpi_packet [] 0 #v[] [] 0 [7]

/-- Changing only that condition makes the same invalid target reject. -/
theorem taken_invalid : advance 2 [0x5f,0x57] ⟨0,[1,7]⟩ = none := by
  have hp : advance 2 [0x5f,0x57] ⟨0,[1,7]⟩ =
      if ((1 : Scalar.Word) == 0) then some ⟨2,[7]⟩
      else if validJumpdest [0x5f,0x57] (Scalar.immediate []).toNat then
        some ⟨(Scalar.immediate []).toNat,[7]⟩ else none :=
    jumpi_packet [] 0 #v[] [] 1 [7]
  have ho : ((1 : Scalar.Word) == 0) = false := rfl
  have hi : (Scalar.immediate []).toNat = 0 := immediate_fit 0 0 (by decide)
  simpa only [ho, Bool.false_eq_true, if_false, hi, push0_not_destination] using hp

/-- JUMPI needs both destination and condition in the actual physical stack. -/
theorem underflow_jumpi : step [0x57] ⟨0,[0]⟩ = none :=
  step_prefix [] (.op .JUMPI) [] [0]

/-- The reused fetch slice refuses truncated PUSH data (not full EVM padding). -/
theorem truncated_push : step [0x60] ⟨0,[]⟩ = none := by rfl

/-- A JUMPDEST byte inside PUSH data is not an admissible destination. -/
theorem pushdata_not_destination : validJumpdest [0x60,0x5b,0x60,0x01,0x56] 1 = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hd : InPushData [0x60,0x5b,0x60,0x01,0x56] 1 := by
    refine ⟨0, ?_, 0x60, rfl, by decide, by decide⟩
    rw [starts_cons]
    exact List.mem_cons_self
  exact ((validJumpdest_iff _ _).mp h).2 hd


end Solidity.Backend.LabelExec.Checks
