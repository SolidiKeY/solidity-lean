import Solidity.Backend.Control
import Solidity.Backend.Scalar.Checked
import Solidity.Backend.Failure.Emit

/-! Concrete checked-add branch artifact using the published control assembler.
Assembly and relocation are proved; branch execution is not supplied by G45.03. -/
namespace Solidity.Backend.AbiWorld.CheckedAddArtifact

def failure (address : Nat) : Block :=
 .code (Failure.emit address (.panic ⟨17,by decide +kernel⟩))

def block (address : Nat) : Block :=
 .ite Scalar.checkedUintAdd.test (failure address) (.code Scalar.checkedUintAdd.body)

def items (address label : Nat) : List (Item Nat Empty) := (block address |>.expand label).1

def link : Empty → Option (Vector UInt8 20) := fun e => nomatch e

def compile (address base label : Nat) : Option (Assembled Empty) :=
 assemble base link (items address label)

theorem expanded (address label : Nat) :
 items address label = Scalar.checkedUintAdd.test.map Item.instr ++
 [.instr (.op .ISZERO),.pushTag label,.instr (.op .JUMPI)] ++
 (Failure.emit address (.panic ⟨17,by decide +kernel⟩)).map Item.instr ++
 [.pushTag (label+1),.instr (.op .JUMP),.tag label] ++
 Scalar.checkedUintAdd.body.map Item.instr ++ [.tag (label+1)] := by rfl

/-- Explicit widest-layout bound from the existing assembler, not execution. -/
theorem compiles (address base label : Nat)
 (fits : ∀ l ∈ refs (items address label),
  base+tagOffset (fun _ => (32 : Fin 33)) (items address label) l<256^32) :
 (compile address base label).isSome :=
 Block.expand_assemble_isSome (block address) label base link fits

theorem item_bound {L Lib : Type} (widths : Widths L) (item : Item L Lib) :
 item.size widths≤33 := by
 cases item with
 | instr instruction => cases instruction <;> simp only [Item.size,Instr.size] <;> omega
 | tag => simp only [Item.size]; omega
 | pushTag l => simp only [Item.size]; have h := (widths l).isLt; omega
 | pushTagRel l => simp only [Item.size]; have h := (widths l).isLt; omega
 | pushLibraryAddress => simp only [Item.size]; omega

theorem offset_bound {L Lib : Type} (widths : Widths L) (list : List (Item L Lib)) (k : Nat) :
 itemOffset widths list k≤33*list.length := by
 induction list generalizing k with
 | nil => simp only [itemOffset,List.take_nil,List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,Nat.le_refl]
 | cons item list ih =>
  cases k with
  | zero => simp only [itemOffset,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_le]
  | succ k =>
   have tail := ih k
   have head := item_bound widths item
   simp only [itemOffset,List.take_succ_cons,List.map_cons,List.sum_cons]
   simp only [itemOffset] at tail
   simp only [List.length_cons]
   omega

theorem tag_bound {L Lib : Type} [DecidableEq L] (widths : Widths L)
 (list : List (Item L Lib)) (label : L) : tagOffset widths list label≤33*list.length := by
 unfold tagOffset
 split
 · exact offset_bound widths list _
 · exact Nat.zero_le _

theorem item_count (address label : Nat) : (items address label).length=124 := by
 rw [expanded]
 simp only [List.length_append,List.length_map,Failure.emit_length,Failure.panic_length,
  Scalar.checkedUintAdd,Scalar.unsignedAddTest,List.length_cons,List.length_nil]

theorem compiles_bounded (address base label : Nat) (bound : base+4092<256^32) :
 (compile address base label).isSome := by
 apply compiles
 intro l _
 have span := tag_bound (fun _ => (32 : Fin 33)) (items address label) l
 rw [item_count] at span
 omega

theorem condition_ref (address label : Nat) : (items address label)[6]?=some (.pushTag label) := by
 rw [expanded]
 simp only [List.append_assoc,Scalar.checkedUintAdd,Scalar.unsignedAddTest,List.map_cons,
  List.map_nil,List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero]

/-- The zero flag jumps to success; overflow falls through to Panic.
This proves relocation of the actual emitted conditional jump only. -/
theorem conditional_target (address base label : Nat) {out : Assembled Empty}
 (assembled : compile address base label=some out) :
 ∃ j imm, tagIndex (items address label) label=some j ∧
 out.code[j]?=some (.op .JUMPDEST) ∧
 out.code[6]?=some (.push (asmWidths base (items address label) label) imm) ∧
 ofBytesBE imm.toList=base+offset out.code j := by
 obtain ⟨j,imm,hj,hd,hp,hv,_,_⟩ := assemble_pushTag assembled (condition_ref address label)
 exact ⟨j,imm,hj,hd,hp,hv⟩
end Solidity.Backend.AbiWorld.CheckedAddArtifact
