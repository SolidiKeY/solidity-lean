import Solidity.Yul.Views.SharedZeroRead

/-! Identity-retaining shared-zero slot preparation and actual Source writeback.
The existing typed slot supplies provenance; raw pointer96 never selects an
ID. Checks concern physical pointer/header only. Actual empty-object lookup is
additionally required for read agreement, not inferred from these checks.
None is preparation failure, not Source/Yul refusal or an execution no-op. -/
namespace Solidity.Yul.Views.SharedZeroLocalWriteback
open SharedZeroRead

/-- No fresh reference is synthesized: the retained typed value is returned. -/
def prepare {D : Source.Layout} {element : Source.STy}
    (retained : Source.Val D (.array .memory element none)) (raw : Roadmap.Word) (memory : ByteView) :
    Option (Source.Val D (.array .memory element none)) :=
  if raw=pointer ∧ mload memory pointer.val=0 then some retained else none

def writeback {E : Source.Env} {Γ : Source.RCtx} {element : Source.STy}
    (s : Source.EMState E Γ) (frame : Source.Fr) (fuel : Nat)
    (slot : Source.Idx Γ (.array .memory element none)) (raw : Roadmap.Word) (memory : ByteView) :
    Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  (prepare (s.1.get slot) raw memory).map (fun value=>(Source.writeLoc frame fuel (.local slot) value).run s)

/-- Intrinsic slot replacement by its retrieved value is exact, including all
other locals. This proof changes no Source definition or execution judgment. -/
theorem locals_set_get {D : Source.Layout} {Γ : Source.RCtx} {τ : Source.STy}
    (values : Source.Locals D Γ) (i : Source.Idx Γ τ) : values.set i (values.get i)=values := by
  first | (simp only;done) | decide | omega | rfl | skip
  induction i with
  | here => cases values;rfl
  | there i ih =>
    cases values with
    | cons head tail =>
      change Source.Locals.cons head (tail.set i (tail.get i))=Source.Locals.cons head tail
      rw [ih tail]

theorem source_write_same {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (s : Source.EMState E Γ) (frame : Source.Fr) (fuel : Nat) (i : Source.Idx Γ τ) :
    (Source.writeLoc frame fuel (.local i) (s.1.get i)).run s=(.ok (),s) := by
  first | (simp only;done) | decide | omega | rfl | skip
  change ((Except.ok () : Except Source.Halt Unit), (s.1.set i (s.1.get i),s.2))=((Except.ok () : Except Source.Halt Unit),s)
  rw [locals_set_get]

theorem prepared {D : Source.Layout} {element : Source.STy}
    (retained : Source.Val D (.array .memory element none)) (memory : ByteView) (free : Roadmap.Word)
    (reserved : ReservedOK memory free) : prepare retained pointer memory=some retained := by
  first | (simp only;done) | decide | omega | rfl | skip
  simp only [prepare,header memory free reserved,and_self,↓reduceIte]

/-- Complete Source administrative identity is derived through actual writeLoc.
This says nothing about validity of arbitrary supplied retained references. -/
theorem unchanged {E : Source.Env} {Γ : Source.RCtx} {element : Source.STy}
    (s : Source.EMState E Γ) (frame : Source.Fr) (fuel : Nat)
    (slot : Source.Idx Γ (.array .memory element none)) (memory : ByteView) (free : Roadmap.Word)
    (reserved : ReservedOK memory free) : writeback s frame fuel slot pointer memory=some (.ok (),s) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [writeback,prepared _ memory free reserved]
  simp only [Option.map_some,source_write_same]

/-- Actual entry binding and actual empty heap lookup supply observational
agreement. They are not replaced by the physical preparation checks. -/
theorem read_agreement {E : Source.Env} {Γ : Source.RCtx} {element : Source.STy}
    (s : Source.EMState E Γ) (frame : Source.Fr) (fuel root : Nat)
    (slot : Source.Idx Γ (.array .memory element none))
    (binding : s.1.get slot=.memRef rfl root)
    (found : s.2.heap.get root=some ⟨.array .memory element none,emptyArray E.layout element⟩)
    (memory : ByteView) (free : Roadmap.Word) (reserved : ReservedOK memory free) :
    writeback s frame fuel slot pointer memory=some (.ok (),s) ∧
    (Source.readLoc frame (.local slot)).run s=(.ok (.memRef rfl root),s) ∧
    (Source.lengthOf frame (s.1.get slot)).run s=(.ok 0,s) ∧ mload memory pointer.val=0 := by
  first | omega | decide | skip
  refine ⟨unchanged s frame fuel slot memory free reserved,?_,?_,header memory free reserved⟩
  · change ((Except.ok (s.1.get slot) : Except Source.Halt _),s)=((Except.ok (.memRef rfl root) : Except Source.Halt _),s)
    rw [binding]
  · rw [binding]
    exact length s frame root element found

theorem rejected {D : Source.Layout} {element : Source.STy}
    (retained : Source.Val D (.array .memory element none)) (raw : Roadmap.Word) (memory : ByteView)
    (wrong : raw≠pointer ∨ mload memory pointer.val≠0) : prepare retained raw memory=none := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply if_neg
  intro both
  rcases wrong with wrong | wrong
  · exact wrong both.1
  · exact wrong both.2
end Solidity.Yul.Views.SharedZeroLocalWriteback
