import SolidityBridge.Yul.StructuredForControls
import Solidity.Backend.LabelExec.Fragment

/-! Physical numeric/expansion preparation for the actual branch-bearing FOR
compiler output. No whole-byte realization/native/Source-G24 claim. -/
namespace SolidityBridge.Yul.ForShape
open Solidity Backend Scalar Selection LabelExec

def flagCode : Program := [.op (.DUP 4)]
def testCode : Program := [.op (.DUP 2)]
def preCode : Program := [pushWord 2,.op (.SWAP 2),.op .POP]
def bodyCode : Program := [pushWord 1,.op (.DUP 3),.op .SUB,.op (.SWAP 2),.op .POP]
def postCode : Program := [pushWord 1,.op (.DUP 4),.op .ADD,.op (.SWAP 3),.op .POP]
def branch (test arm : Program) : Backend.Block := .ite test (.code arm) (.code [])
def layout : Backend.Block := .seq (branch flagCode preCode)
  (.loop testCode (.seq (branch flagCode bodyCode) (branch testCode postCode)))

theorem actual_layout : StructuredFor.Controls.target = layout := by rfl

theorem pre_trace (h : Int) : heightTrace preCode h = [h,h+1,h+1,h] := by
  change [h,h+1,(h+1)+0,((h+1)+0)+(-1)] = _
  simp only [Int.add_assoc,Int.reduceAdd,Int.add_zero]

theorem body_trace (h : Int) : heightTrace bodyCode h = [h,h+1,h+2,h+1,h+1,h] := by
  change [h,h+1,(h+1)+1,((h+1)+1)+(-1),(((h+1)+1)+(-1))+0,
    ((((h+1)+1)+(-1))+0)+(-1)] = _
  simp only [Int.add_assoc,Int.reduceAdd,Int.add_zero]

theorem post_trace (h : Int) : heightTrace postCode h = [h,h+1,h+2,h+1,h+1,h] := by
  change [h,h+1,(h+1)+1,((h+1)+1)+(-1),(((h+1)+1)+(-1))+0,
    ((((h+1)+1)+(-1))+0)+(-1)] = _
  simp only [Int.add_assoc,Int.reduceAdd,Int.add_zero]

theorem pre_capacity (h : Int) : stackBound preCode h = true ↔ 0 ≤ h ∧ h+1 ≤ 1024 := by
  simp only [stackBound,pre_trace,List.all_cons,List.all_nil,Bool.and_true,
    Bool.and_eq_true,safeHeight,decide_eq_true_eq]
  omega

theorem body_capacity (h : Int) : stackBound bodyCode h = true ↔ 0 ≤ h ∧ h+2 ≤ 1024 := by
  simp only [stackBound,body_trace,List.all_cons,List.all_nil,Bool.and_true,
    Bool.and_eq_true,safeHeight,decide_eq_true_eq]
  omega

theorem post_capacity (h : Int) : stackBound postCode h = true ↔ 0 ≤ h ∧ h+2 ≤ 1024 := by
  simp only [stackBound,post_trace,List.all_cons,List.all_nil,Bool.and_true,
    Bool.and_eq_true,safeHeight,decide_eq_true_eq]
  omega

private theorem pre_shape (h : Nat) (enough : 5 ≤ h) : CodeShape preCode h h := by
  refine .cons (m := h+1) (.mk 0 1 h rfl (by omega) (by omega)) ?_
  refine .cons (m := h+1) (.mk 4 4 (h-3) rfl (by omega) (by omega)) ?_
  exact .cons (.mk 1 0 h rfl (by omega) (by omega)) (.nil h)

private theorem body_shape (h : Nat) (enough : 5 ≤ h) : CodeShape bodyCode h h := by
  refine .cons (m := h+1) (.mk 0 1 h rfl (by omega) (by omega)) ?_
  refine .cons (m := h+2) (.mk 4 5 (h-3) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+1) (.mk 2 1 h rfl (by omega) (by omega)) ?_
  refine .cons (m := h+1) (.mk 4 4 (h-3) rfl (by omega) (by omega)) ?_
  exact .cons (.mk 1 0 h rfl (by omega) (by omega)) (.nil h)

private theorem post_shape (h : Nat) (enough : 5 ≤ h) : CodeShape postCode h h := by
  refine .cons (m := h+1) (.mk 0 1 h rfl (by omega) (by omega)) ?_
  refine .cons (m := h+2) (.mk 5 6 (h-4) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+1) (.mk 2 1 h rfl (by omega) (by omega)) ?_
  refine .cons (m := h+1) (.mk 5 5 (h-4) rfl (by omega) (by omega)) ?_
  exact .cons (.mk 1 0 h rfl (by omega) (by omega)) (.nil h)

private def duplicateFragment (i : Fin 16) (h : Nat) (operands : i.val+1 ≤ h)
    (room : h+2 ≤ 1024) : Code h (h+1) where
  instructions := [.op (.DUP i)]
  shape := .cons (.mk (i.val+1) (i.val+2) (h-(i.val+1)) rfl (by omega) (by omega)) (.nil (h+1))
  capacity := by
    change ([((h : Int)),(h : Int)+1].all safeHeight) = true
    simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,safeHeight,decide_eq_true_eq]
    omega

private def emptyFragment (h : Nat) (room : h+2 ≤ 1024) : Code h h where
  instructions := []
  shape := .nil h
  capacity := by
    change (safeHeight (h : Int) && true) = true
    simp only [Bool.and_true,safeHeight,decide_eq_true_eq]
    omega

private theorem branch_shape (i : Fin 16) (code : Program) (h : Nat)
    (operands : i.val+1 ≤ h) (room : h+2 ≤ 1024)
    (shape : CodeShape code h h) (capacity : stackBound code (h : Int) = true) :
    BlockShape (branch [.op (.DUP i)] code) h h :=
  .ite (cond := duplicateFragment i h operands room)
    (.code ⟨code,shape,capacity⟩) (.code (emptyFragment h room)) room

private theorem pre_branch (h : Nat) (enough : 5 ≤ h) (room : h+2 ≤ 1024) :
    BlockShape (branch flagCode preCode) h h :=
  branch_shape 4 preCode h (by omega) room (pre_shape h enough)
    ((pre_capacity h).mpr ⟨by omega,by omega⟩)

private theorem body_branch (h : Nat) (enough : 5 ≤ h) (room : h+2 ≤ 1024) :
    BlockShape (branch flagCode bodyCode) h h :=
  branch_shape 4 bodyCode h (by omega) room (body_shape h enough)
    ((body_capacity h).mpr ⟨by omega,by omega⟩)

private theorem post_branch (h : Nat) (enough : 5 ≤ h) (room : h+2 ≤ 1024) :
    BlockShape (branch testCode postCode) h h :=
  branch_shape 2 postCode h (by omega) room (post_shape h enough)
    ((post_capacity h).mpr ⟨by omega,by omega⟩)

private theorem loop_shape (h : Nat) (enough : 5 ≤ h) (room : h+2 ≤ 1024) :
    BlockShape (.loop testCode (.seq (branch flagCode bodyCode) (branch testCode postCode))) h h :=
  .loop (cond := duplicateFragment 2 h (by omega) room)
    (.seq (body_branch h enough room) (post_branch h enough room)) room

/-- The actual emitted block has intrinsic operands/height and every scalar
prefix bound, plus the separate structured test's two-word allowance. -/
theorem shape (h : Nat) (enough : 5 ≤ h) (room : h+2 ≤ 1024) :
    BlockShape StructuredFor.Controls.target h h := by
  rw [actual_layout]
  exact .seq (pre_branch h enough room) (loop_shape h enough room)

private theorem branch_room (block : Backend.Block) (input output : Nat)
    (checked : BlockShape block input output) :
    ∀ (test : Program) (yes no : Backend.Block), block = .ite test yes no → input+2 ≤ 1024 := by
  cases checked with
  | code leaf => intro test yes no same; cases same
  | seq first second => intro test yes no same; cases same
  | ite left right room => intro test yes no same; exact room
  | loop body room => intro test yes no same; cases same

/-- Necessity comes from the actual emitted prelude branch's test contract. -/
theorem requires_room {h : Nat} (checked : BlockShape StructuredFor.Controls.target h h) :
    h+2 ≤ 1024 := by
  rw [actual_layout] at checked
  cases checked with
  | seq first rest =>
    exact branch_room _ _ _ first flagCode (.code preCode) (.code []) rfl

theorem shape_iff (h : Nat) (enough : 5 ≤ h) :
    BlockShape StructuredFor.Controls.target h h ↔ h+2 ≤ 1024 :=
  ⟨requires_room,shape h enough⟩

/-- Additional join-jump room is proved separately; no whole realization field
or native instruction-step execution is asserted. -/
theorem expansion_room (h : Nat) (enough : 5 ≤ h) (room : h+2 ≤ 1024) :
    ExpansionRoom StructuredFor.Controls.target h h := by
  change ∃ mid, BlockShape (branch flagCode preCode) h mid ∧
    BlockShape (.loop testCode (.seq (branch flagCode bodyCode) (branch testCode postCode))) mid h ∧
    ExpansionRoom (branch flagCode preCode) h mid ∧
    ExpansionRoom (.loop testCode (.seq (branch flagCode bodyCode) (branch testCode postCode))) mid h
  refine ⟨h,pre_branch h enough room,loop_shape h enough room,?_,?_⟩
  · exact ⟨True.intro,True.intro,by omega⟩
  · exact ⟨h,body_branch h enough room,post_branch h enough room,
      ⟨True.intro,True.intro,by omega⟩,⟨True.intro,True.intro,by omega⟩⟩

/-- info: 'SolidityBridge.Yul.ForShape.actual_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms actual_layout
/-- info: 'SolidityBridge.Yul.ForShape.pre_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pre_trace
/-- info: 'SolidityBridge.Yul.ForShape.body_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms body_trace
/-- info: 'SolidityBridge.Yul.ForShape.post_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms post_trace
/-- info: 'SolidityBridge.Yul.ForShape.pre_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pre_capacity
/-- info: 'SolidityBridge.Yul.ForShape.body_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms body_capacity
/-- info: 'SolidityBridge.Yul.ForShape.post_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_capacity
/-- info: 'SolidityBridge.Yul.ForShape.shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shape
/-- info: 'SolidityBridge.Yul.ForShape.requires_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms requires_room
/-- info: 'SolidityBridge.Yul.ForShape.shape_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shape_iff
/-- info: 'SolidityBridge.Yul.ForShape.expansion_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expansion_room
end SolidityBridge.Yul.ForShape
