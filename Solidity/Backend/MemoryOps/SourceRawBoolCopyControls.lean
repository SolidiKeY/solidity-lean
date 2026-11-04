import Solidity.Backend.MemoryOps.SourceRawBoolEntry
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
private def selectorBytes : List UInt8 := [222,173,190,239]
private def args : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++Source.natBytes 32 0++Source.natBytes 32 1
private def badArgs : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++Source.natBytes 32 0++Source.natBytes 32 2
private def shortArgs : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++Source.natBytes 32 0
private def emptyArgs : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 0
private def entryFrame (data : List UInt8) := frame (selectorBytes++data)
private theorem entry_guard (data : List UInt8) (k : Nat)
    (head : Source.wordAt data 0=32) (len : Source.wordAt (data.drop 32) 0=k)
    (bytes : data.length=64+32*k) (small : k<2^64) : Source.cdTail data 0 32=.ok (68,k) := by
  rw [Source.cdTail,head,if_neg (by omega),len,if_neg (by omega),if_pos (by omega)]
  rfl
private theorem entry_canonical : ∀ j,j<Source.wordAt (args.drop (Source.wordAt args 0)) 0 →
    let w := Source.beValue (Source.fitBytes 32 (args.drop (Source.wordAt args 0+32+32*j)))
    w=0 ∨ w=1 := by
  intro j hj
  have len : Source.wordAt (args.drop (Source.wordAt args 0)) 0=2 := by decide
  rw [len] at hj
  have casesJ : j=0 ∨ j=1 := by omega
  rcases casesJ with rfl|rfl <;> decide

/-- Actual entry guard plus copy under the selector/frame binding. Existing
complete populated object tables and retained aliases are the same final state. -/
theorem entry_success :
    Source.cdTail args 0 32=.ok (68,2) ∧
    ((Source.EM.lift (Source.cdTail args 0 32)) >>= fun p =>
      Source.cdToMem (entryFrame args) A p.1 p.2).run initial=(.ok (.val (.memRef rfl 2)),final) ∧
    [final.2.heap.get 0,final.2.heap.get 1,final.2.heap.get 2]=
      [some ⟨A,sourceBoolMemory [true,false]⟩,some ⟨A,sourceBoolMemory [false,true,true]⟩,some ⟨A,sourceBoolMemory [false,true]⟩] ∧
    final.1=initial.1 ∧ {final.2 with heap := initial.2.heap}=initial.2 := by
  first
  | solve | simp only [] | omega
  | have header : Source.wordAt args 0=32 := by decide
    have lenWord : Source.wordAt (args.drop 32) 0=2 := by decide
    have bytes : args.length=128 := by simp only [args,Source.natBytes,List.length_append,Source.beBytes_length]
    have guarded := entry_guard args 2 header lenWord bytes (by decide)
    have run := source_raw_bool_entry_success (entryFrame args) selectorBytes args rfl rfl 0 initial
        (by rw [header,bytes];decide) (by rw [header,lenWord];decide)
        (by rw [header,lenWord,bytes];decide) entry_canonical
    have off : 4+Source.wordAt args 0+32=68 := by decide
    have len : Source.wordAt (args.drop (Source.wordAt args 0)) 0=2 := by decide
    rw [off,len] at run
    dsimp only at run
    have values : rawBoolPayload (entryFrame args) 68 2=[false,true] := by decide
    rw [values] at run
    exact ⟨guarded,run,rfl,rfl,rfl⟩

/-- The span guard passes but the second raw Boolean word fails validation.
The actual accepted false prefix and unchanged heap distinguish these phases. -/
theorem entry_invalid :
    Source.cdTail badArgs 0 32=.ok (68,2) ∧
    ([0].mapM (fun j => Source.EM.lift (E := E0) (Γ := Γ)
      (Source.decodeWord E0.layout (Source.cdWordAt (entryFrame badArgs) (68+32*j)) .bool))).run initial=
      (.ok [Source.Val.bool false],initial) ∧
    ((Source.EM.lift (Source.cdTail badArgs 0 32)) >>= fun p =>
      Source.cdToMem (entryFrame badArgs) A p.1 p.2).run initial=(.error (.revert []),initial) := by
  first
  | solve | simp only [] | omega
  | have guard : Source.cdTail badArgs 0 32=.ok (68,2) :=
      entry_guard badArgs 2 (by decide) (by decide)
        (by simp only [badArgs,Source.natBytes,List.length_append,Source.beBytes_length]) (by decide)
    have copied := source_raw_bool_copy_first_error (entryFrame badArgs) 68 2 initial [0] [] 1 rfl
        (by intro j hj;simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;subst j;decide) (by decide)
    refine ⟨guard,copied.1,?_⟩
    rw [source_raw_bool_guarded_run,guard]
    exact copied.2.2

/-- Truncated dynamic elements reject at entry. The SAME bytes instead pad
successfully under standalone copy; neither branch invents a failed final heap. -/
theorem entry_truncated :
    Source.cdTail shortArgs 0 32=.error (.revert []) ∧
    ((Source.EM.lift (Source.cdTail shortArgs 0 32)) >>= fun p =>
      Source.cdToMem (entryFrame shortArgs) A p.1 p.2).run initial=(.error (.revert []),initial) ∧
    (Source.cdToMem (entryFrame shortArgs) A 68 2).run initial=
      (.ok (.val (.memRef rfl 2)),(initial.1,{initial.2 with heap :=
        (initial.2.heap.alloc ⟨A,sourceBoolMemory [false,false]⟩).1})) := by
  first
  | solve | simp only [] | omega
  | obtain ⟨guard,run⟩ := source_raw_bool_entry_refused (entryFrame shortArgs) shortArgs 0 initial
        (Or.inr (Or.inr (by decide)))
    have canon : ∀ j,j<2 → Source.cdWordAt (entryFrame shortArgs) (68+32*j)=0 ∨ Source.cdWordAt (entryFrame shortArgs) (68+32*j)=1 := by
      intro j hj
      have casesJ : j=0 ∨ j=1 := by omega
      rcases casesJ with rfl|rfl <;> decide
    have padded := source_raw_bool_copy (entryFrame shortArgs) 68 2 initial canon
    have values : rawBoolPayload (entryFrame shortArgs) 68 2=[false,false] := by decide
    rw [values] at padded
    exact ⟨guard,run,padded⟩

/-- Exact-end zero-length entry succeeds and allocates the empty dynamic object. -/
theorem entry_empty :
    Source.cdTail emptyArgs 0 32=.ok (68,0) ∧
    ((Source.EM.lift (Source.cdTail emptyArgs 0 32)) >>= fun p =>
      Source.cdToMem (entryFrame emptyArgs) A p.1 p.2).run initial=
      (.ok (.val (.memRef rfl 2)),(initial.1,{initial.2 with heap :=
        (initial.2.heap.alloc ⟨A,sourceBoolMemory []⟩).1})) := by
  first
  | solve | simp only [] | omega
  | have guard : Source.cdTail emptyArgs 0 32=.ok (68,0) :=
      entry_guard emptyArgs 0 (by decide) (by decide)
        (by simp only [emptyArgs,Source.natBytes,List.length_append,Source.beBytes_length]) (by decide)
    refine ⟨guard,?_⟩
    rw [source_raw_bool_guarded_run,guard]
    exact source_raw_bool_copy (entryFrame emptyArgs) 68 0 initial (by intro j hj;omega)

/-- info: 'Solidity.Backend.MemoryOps.RawBoolCopyControls.entry_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entry_success
/-- info: 'Solidity.Backend.MemoryOps.RawBoolCopyControls.entry_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entry_invalid
/-- info: 'Solidity.Backend.MemoryOps.RawBoolCopyControls.entry_truncated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entry_truncated
/-- info: 'Solidity.Backend.MemoryOps.RawBoolCopyControls.entry_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entry_empty
end Solidity.Backend.MemoryOps.RawBoolCopyControls
