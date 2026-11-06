import Solidity.Backend.CalldataPackets.RawInt.Execution
namespace Solidity.Backend.CalldataPackets.RawInt.Controls

def int8 : Source.IntTy := ⟨true,8,by decide⟩
def frame (bytes : List UInt8) : Source.Fr :=
  { this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨0,by decide⟩,
    static := false,contract := "RawInt",cd := bytes }

theorem negative_one : (Source.Val.int (D := Source.Env.layout ⟨[]⟩) (t := int8) (-1) (by decide)).word.bind (Source.readInt int8)=some (-1) := by
  exact Source.Val.word_int (D := Source.Env.layout ⟨[]⟩) (t := int8) (-1) (by decide)
theorem positive_max : Source.readInt int8 (Source.toWord 127)=some 127 := by decide
theorem negative_min : (Source.Val.int (D := Source.Env.layout ⟨[]⟩) (t := int8) (-128) (by decide)).word.bind (Source.readInt int8)=some (-128) := by
  exact Source.Val.word_int (D := Source.Env.layout ⟨[]⟩) (t := int8) (-128) (by decide)
theorem dirty_positive : Source.readInt int8 (Source.toWord 128)=none := by decide
theorem dirty_negative : Source.readInt int8 (Source.toWord 255)=none := by decide

theorem dirty_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame (Source.natBytes 32 255)) (ArrayTy int8) 0 1).run y=
      (.error (.revert []),y) := by
  rw [copy_run]
  rfl

theorem positive_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame (Source.natBytes 32 127)) (ArrayTy int8) 0 1).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc
          ⟨ArrayTy int8,memory [Source.Val.int 127 (by decide)]⟩).1})) := by
  rw [copy_run]
  rfl

theorem late_dirty_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame (Source.natBytes 32 127++Source.natBytes 32 255))
      (ArrayTy int8) 0 2).run y=(.error (.revert []),y) := by
  rw [copy_run]
  rfl

theorem empty_copy {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr)
    (off : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F (ArrayTy int8) off 0).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy int8,memory []⟩).1})) := by
  rw [copy_run]
  rfl

theorem eof_padding {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame []) (ArrayTy int8) 123 1).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc
          ⟨ArrayTy int8,memory [Source.Val.int 0 (by decide)]⟩).1})) := by
  rw [copy_run]
  rfl

theorem zero_horizon {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E)
    (F : Source.Fr) (t : Source.IntTy) (i : Source.Idx Γ (.array .calldata (.int t) none))
    (y : Source.EMState E Γ) :
    (Source.evalE G F 0 (copyExpr t i)).run y=(.error .timeout,y) := rfl

theorem one_horizon {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E)
    (F : Source.Fr) (t : Source.IntTy) (i : Source.Idx Γ (.array .calldata (.int t) none))
    (y : Source.EMState E Γ) :
    (Source.evalE G F 1 (copyExpr t i)).run y=(.error .timeout,y) := rfl

end Solidity.Backend.CalldataPackets.RawInt.Controls
