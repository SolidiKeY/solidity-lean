import Solidity.Backend.MemoryOps.SourceRawBoolCopy
import Solidity.Source.Semantics

/-! Raw-byte controls for actual Source validation/allocation, not an ABI entry
or native writer theorem. cdToMem itself has no pipeline or horizon argument. -/
namespace Solidity.Backend.MemoryOps.RawBoolCopyControls
private def E0 : Source.Env := ⟨[]⟩
private abbrev A : Source.STy := .array .memory .bool none
private abbrev Γ : Source.RCtx := [A,A]
private def zero : Source.EMState E0 [] := (.nil,Source.St.init E0)
private def old := ((Source.allocRef (sourceBoolMemory [true,false])).run zero).2
private def objects := ((Source.allocRef (sourceBoolMemory [false,true,true])).run old).2
private def initial : Source.EMState E0 Γ := (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil),objects.2)
private def frame (data : List UInt8) : Source.Fr :=
  {this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨17,by decide⟩,
    static := false,contract := "RawBool",cd := data}
private def good := frame ([171,205,239]++Source.natBytes 32 0++Source.natBytes 32 1)
private def bad := frame ([171,205,239]++Source.natBytes 32 0++Source.natBytes 32 2++Source.natBytes 32 1)
private def final : Source.EMState E0 Γ :=
  (initial.1,{initial.2 with heap := (initial.2.heap.alloc ⟨A,sourceBoolMemory [false,true]⟩).1})
private theorem canonical : ∀ j,j<2 → Source.cdWordAt good (3+32*j)=0 ∨ Source.cdWordAt good (3+32*j)=1 := by
  intro j hj
  have casesJ : j=0 ∨ j=1 := by omega
  rcases casesJ with rfl|rfl <;> decide

/-- Nonempty old objects and two retained aliases survive a fresh allocation.
The complete ordered object table and decoded payload are derived from bytes. -/
theorem populated :
    (Source.cdToMem good A 3 2).run initial=(.ok (.val (.memRef rfl 2)),final) ∧
    [initial.2.heap.get 0,initial.2.heap.get 1,initial.2.heap.get 2]=
      [some ⟨A,sourceBoolMemory [true,false]⟩,some ⟨A,sourceBoolMemory [false,true,true]⟩,none] ∧
    [final.2.heap.get 0,final.2.heap.get 1,final.2.heap.get 2]=
      [some ⟨A,sourceBoolMemory [true,false]⟩,some ⟨A,sourceBoolMemory [false,true,true]⟩,
        some ⟨A,sourceBoolMemory [false,true]⟩] ∧
    initial.2.heap.next=2 ∧ final.2.heap.next=3 ∧ final.1=initial.1 ∧
    {final.2 with heap := initial.2.heap}=initial.2 ∧
    rawBoolPayload good 3 2=[false,true] ∧
    rawBoolPayload good 3 2≠[true,false] ∧
    (∀ a,a≠2 → final.2.heap.get a=initial.2.heap.get a) := by
  first
  | solve | simp only [] | omega
  | have run := source_raw_bool_copy good 3 2 initial canonical
    have values : rawBoolPayload good 3 2=[false,true] := by decide
    rw [values] at run
    have frames := source_raw_bool_copy_frames good 3 2 initial canonical
    have keep := frames.2.2.1
    rw [run] at keep
    change ∀ a,a≠2 → final.2.heap.get a=initial.2.heap.get a at keep
    exact ⟨run,rfl,rfl,rfl,rfl,rfl,rfl,values,by decide,keep⟩

/-- An actually decoded false prefix precedes a noncanonical two; validation
fails before any allocation. The malformed suffix is never fabricated as data. -/
theorem late_invalid :
    ([0].mapM (fun j => Source.EM.lift (E := E0) (Γ := Γ)
      (Source.decodeWord E0.layout (Source.cdWordAt bad (3+32*j)) .bool))).run initial=
      (.ok [Source.Val.bool false],initial) ∧
    (Source.EM.lift (E := E0) (Γ := Γ) (Source.decodeWord E0.layout (Source.cdWordAt bad 35) .bool)).run initial=
      (.error (.revert []),initial) ∧
    (Source.cdToMem bad A 3 3).run initial=(.error (.revert []),initial) ∧
    initial.2.heap.next=2 ∧ initial.2.heap.get 2=none ∧
    bad.cd≠good.cd := by
  first
  | solve | simp only [] | omega
  | have error := source_raw_bool_copy_first_error bad 3 3 initial [0] [2] 1 rfl
        (by intro j hj;simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;subst j;decide) (by decide)
    exact ⟨error.1,error.2.1,error.2.2,rfl,rfl,by decide⟩

/-- Missing standalone-copy bytes are zero padded by the actual Source reader;
this is success, not a fabricated truncated-entry refusal. Empty length also
allocates an actual fresh empty object. cdTail remains a separate entry guard. -/
theorem padding_and_empty :
    (Source.cdToMem (frame []) A 7 2).run initial=
      (.ok (.val (.memRef rfl 2)),(initial.1,{initial.2 with heap :=
        (initial.2.heap.alloc ⟨A,sourceBoolMemory [false,false]⟩).1})) ∧
    (Source.cdToMem bad A 3 0).run initial=
      (.ok (.val (.memRef rfl 2)),(initial.1,{initial.2 with heap :=
        (initial.2.heap.alloc ⟨A,sourceBoolMemory []⟩).1})) := by
  first
  | solve | simp only [] | omega
  | have padded := source_cd_bool_empty_run (frame []) rfl 7 2 initial
    have empty := source_raw_bool_copy bad 3 0 initial (by intro j hj;omega)
    exact ⟨padded,empty⟩

/-- info: 'Solidity.Backend.MemoryOps.RawBoolCopyControls.populated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms populated
/-- info: 'Solidity.Backend.MemoryOps.RawBoolCopyControls.late_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms late_invalid
/-- info: 'Solidity.Backend.MemoryOps.RawBoolCopyControls.padding_and_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padding_and_empty
end Solidity.Backend.MemoryOps.RawBoolCopyControls
