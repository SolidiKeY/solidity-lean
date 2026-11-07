import Solidity.Backend.MemoryOps.PhysicalReferenceSequence
import Solidity.Backend.MemoryOps.PhysicalPointerWorldUnwind
import Solidity.Backend.MemoryOps.PhysicalWorldUnwindControls

/-! Inhabited parent redirection/dynamic child-write controls. These word/byte
programs do not assert a Source path compiler or external EVM execution. -/
namespace Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls
open Semantics Evm Evm.Memory
private abbrev B : RefTy := .array (.prim .bool)
private abbrev P : RefTy := .array (.ref B)
private abbrev N : RefTy := .array (.prim .uint)
private abbrev H : HTy := [P,B,B,N]
private def root : HRef H P := ⟨0,rfl⟩
private def left : HRef H B := ⟨1,rfl⟩
private def right : HRef H B := ⟨2,rfl⟩
private def neighbor : HRef H N := ⟨3,rfl⟩
private def u (n : Nat) : PrimTy.uint.Denote := indexValue (wmod n)
private def hp : Heap H := (⟨[left,left],by decide⟩,⟨[true,false],by decide⟩,⟨[false],by decide⟩,⟨[u 8,u 9],by decide⟩,())
private def base (id : Nat) : Fin W := if id=0 then wmod 16 else if id=1 then wmod 1 else if id=2 then wmod 8 else wmod 24
private def machine : Machine := {Machine.init with stack := [.val (wmod 77),.val (wmod 88)],mem := (fun c => if c=0 then .val (wmod 32) else if c=1 ∨ c=16 ∨ c=24 then .val (wmod 2) else if c=2 ∨ c=8 ∨ c=17 ∨ c=18 then .val (wmod 1) else if c=25 then .val (wmod 8) else if c=26 then .val (wmod 9) else .val (wmod 0))}
private def image : List (Nat×Nat) := [(0,1024),(1,2),(2,1),(3,0),(8,1),(9,0),(16,2),(17,32),(18,32),(24,2),(25,8),(26,9)]
private def bytes : Environment.Memory := image.foldl
  (fun memory cell => Environment.writeBytes memory (32*cell.1) (Semantics.wordBytes cell.2)) (fun _ => 0)
private def middle : Heap H := hp.set root (MObj.setElem .dyn (hp.get root) 0 right)
private def final : Heap H := middle.set right (MObj.setElem .dyn (middle.get right) 0 true)
private def middleWord : Machine := writeMachine machine 17 (.val (wmod 8))
private def middleBytes := Environment.writeBytes bytes 544 (Semantics.wordBytes 256)
private def finalWord : Machine := writeMachine middleWord 9 (.val (wmod 1))
private def finalBytes := Environment.writeBytes middleBytes 288 (Semantics.wordBytes 1)
private def pathCode (j : Fin W) : List Evm.Instr :=
  [.push (.val (wmod 1)),.push (.val (wmod 0))] ++
    (readArrayCode (wmod 16) ++ ([.push (.val j)] ++ writeArrayStackCode))
private def program (j : Fin W) : List Evm.Instr := writeArrayCode (wmod 16) ++ pathCode j
private def initialStack := (machine.push (.val (wmod 8))).push (.val (wmod 0))
private def cells : List Nat := [0,1,2,3,8,9,16,17,18,24,25,26]
private def wordVector (m : Machine) := cells.map m.mem
private def byteVector (m : Environment.Memory) := cells.map fun c => Environment.readMemory m (32*c) 32

private theorem parentLength : hp.len root .dyn=2 := by
  simp only [Heap.len,MObj.elems_dyn]
  rfl
private theorem rightLength : hp.len right .dyn=1 := by
  simp only [Heap.len,MObj.elems_dyn]
  rfl
private theorem parentElements : MObj.elems .dyn (hp.get root)=[left,left] := by
  simp only [MObj.elems_dyn]
  rfl
private theorem written_read (memory : Environment.Memory) (a value : Nat) :
    Environment.readMemory (Environment.writeBytes memory a (Semantics.wordBytes value)) a 32=Semantics.wordBytes value := by
  simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes value) a memory
private theorem image_read (c value : Nat) (hit : (c,value)∈image) :
    Environment.readMemory bytes (32*c) 32=Semantics.wordBytes value := by
  simp only [image,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hit
  rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    simp only [bytes,image,List.foldl_cons,List.foldl_nil]
    repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length];omega)
    exact written_read _ _ _
private theorem parentAt : ReferenceArrayAt hp root base machine bytes := by
  constructor
  · constructor
    · rw [parentLength]
      decide
    · rw [parentLength]
      rfl
    · intro i child hit
      rw [parentElements] at hit
      cases i with
      | zero => cases hit;rfl
      | succ i => cases i with
        | zero => cases hit;rfl
        | succ i => cases hit
  · decide
  · exact ⟨wmod 2,rfl,image_read 16 2 (by decide)⟩
  · constructor
    · intro c hc
      obtain ⟨i,hi,eq⟩ := hc
      rw [parentLength] at hi
      change c=16+1+i at eq
      omega
    · intro c hc
      obtain ⟨i,hi,eq⟩ := hc
      rw [parentLength] at hi
      change c=16+1+i at eq
      have which : i=0 ∨ i=1 := by omega
      rcases which with rfl | rfl
      · subst c
        exact ⟨wmod 1,rfl,by decide,image_read 17 32 (by decide)⟩
      · subst c
        exact ⟨wmod 1,rfl,by decide,image_read 18 32 (by decide)⟩
private theorem rightWords : ArrayRepr hp right (base right.id) machine := by
  constructor
  · rw [rightLength]
    decide
  · rw [rightLength]
    rfl
  · intro i value hit
    simp only [MObj.elems_dyn] at hit
    cases i with
    | zero => cases hit;rfl
    | succ i => cases hit
private theorem rightBytes : WordFrame machine bytes (fun c => (base right.id).val≤c ∧ c<(base right.id).val+1+hp.len right .dyn) := by
  constructor
  · intro c hc
    rw [rightLength] at hc
    change 8≤c ∧ c<10 at hc
    omega
  · intro c hc
    rw [rightLength] at hc
    change 8≤c ∧ c<10 at hc
    have which : c=8 ∨ c=9 := by omega
    rcases which with rfl | rfl
    · exact ⟨wmod 1,rfl,image_read 8 1 (by decide)⟩
    · exact ⟨wmod 0,rfl,image_read 9 0 (by decide)⟩

/-- A real repeated-alias parent is redirected to RIGHT; dynamic pointer load
then materially changes RIGHT false→true while LEFT and neighbor remain. -/
theorem redirect_write_client :
    ReferenceArrayAt hp root base machine bytes ∧
    hp.writeAddr (.index root .dyn (indexValue (wmod 0))) right=some middle ∧
    middle.index root .dyn (indexValue (wmod 0))=some right ∧
    middle.writeAddr (.index right .dyn (indexValue (wmod 0))) true=some final ∧
    Evm.run (writeArrayCode (wmod 16)) initialStack=.ok middleWord 0 ∧
    Evm.run (pathCode (wmod 0)) middleWord=.ok finalWord 0 ∧
    Evm.run (program (wmod 0)) initialStack=.ok finalWord 0 ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 544 (by decide)::lenU 256 (by decide)::[lenU 11 (by decide),lenU 22 (by decide)],bytes⟩=
        some ⟨[lenU 11 (by decide),lenU 22 (by decide)],middleBytes⟩ ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 288 (by decide)::lenU 1 (by decide)::[lenU 11 (by decide),lenU 22 (by decide)],middleBytes⟩=
        some ⟨[lenU 11 (by decide),lenU 22 (by decide)],finalBytes⟩ ∧
    ReferenceArrayAt final root base finalWord finalBytes ∧
    ArrayRepr final right (base right.id) finalWord ∧
    WordFrame finalWord finalBytes (fun c => (base right.id).val≤c ∧ c<(base right.id).val+1+final.len right .dyn) ∧
    Evm.run (readArrayCode (wmod 16)) (finalWord.push (.val (wmod 0)))=.ok (finalWord.push (.val (wmod 8))) 0 ∧
    Environment.readMemory finalBytes 544 32=Semantics.wordBytes 256 ∧
    final.get left=hp.get left ∧ final.get neighbor=hp.get neighbor ∧
    finalWord.mem 0=machine.mem 0 ∧ finalWord.stack=machine.stack := by
  have numbers : ∀ c,(base right.id).val≤c ∧ c<(base right.id).val+1+hp.len right .dyn → c≠(base root.id).val+1+(wmod 0).val := by
    intro c hc
    rw [rightLength] at hc
    change 8≤c ∧ c<10 at hc
    change c≠17
    omega
  have slots : ∀ c,ReferenceSlots hp root base c → c≠(base right.id).val+1+(wmod 0).val := by
    intro c hc
    obtain ⟨k,hk,eq⟩ := hc
    rw [parentLength] at hk
    change c=16+1+k at eq
    change c≠9
    omega
  obtain ⟨out,h1,sel,w1,b1,wm,h2,w2,whole,dynamic,b2,parentF,wordsF,physicalF,parentGet,selectedF,read,pointer,frame,free,exterior,stack⟩ :=
    parentAt.redirect_primitive right rightWords rightBytes (wmod 0) (wmod 0) (wmod 1) true
      (by rw [parentLength];decide) (by rw [rightLength];decide) rfl (by decide) numbers (by decide) slots
  have bound : (wmod 0).val<(MObj.elems .dyn (middle.get right)).length := by
    simp only [middle,Heap.get_set_ne hp root right (by decide),MObj.elems_dyn]
    decide
  have actual : middle.writeAddr (.index right .dyn (indexValue (wmod 0))) true=some final := by
    simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast,bound,↓reduceIte]
    rfl
  have same : out=final := Option.some.inj (h2.symm.trans actual)
  subst out
  have pathRun := dynamic
  rw [Evm.run_append_ok w1] at pathRun
  obtain ⟨off1,hoff1,store1⟩ := b1
  have eq1 : off1=⟨544,by decide⟩ := Fin.ext hoff1
  subst off1
  obtain ⟨off2,hoff2,store2⟩ := b2
  have eq2 : off2=⟨288,by decide⟩ := Fin.ext hoff2
  subst off2
  exact ⟨parentAt,h1,sel,h2,w1,pathRun,dynamic,store1 _,store2 _,parentF,wordsF,physicalF,read,pointer,
    frame _ left (by decide) (by decide),frame _ neighbor (by decide) (by decide),free,stack⟩


private theorem middle_written_read : Environment.readMemory middleBytes 544 32=Semantics.wordBytes 256 :=
  written_read bytes 544 256
private theorem final_written_read : Environment.readMemory finalBytes 288 32=Semantics.wordBytes 1 :=
  written_read middleBytes 288 1
private theorem middle_other_read (c value : Nat) (hit : (c,value)∈image) (different : c≠17) :
    Environment.readMemory middleBytes (32*c) 32=Semantics.wordBytes value := by
  unfold middleBytes
  rw [readMemory_write_frame]
  · exact image_read c value hit
  · simp only [Environment.wordBytes_length]
    omega
private theorem final_other_read (c value : Nat) (hit : (c,value)∈image) (notPointer : c≠17) (notValue : c≠9) :
    Environment.readMemory finalBytes (32*c) 32=Semantics.wordBytes value := by
  unfold finalBytes
  rw [readMemory_write_frame]
  · exact middle_other_read c value hit notPointer
  · simp only [Environment.wordBytes_length]
    omega
private theorem final_pointer_read : Environment.readMemory finalBytes 544 32=Semantics.wordBytes 256 := by
  unfold finalBytes
  rw [readMemory_write_frame]
  · exact written_read bytes 544 256
  · simp only [Environment.wordBytes_length]
    omega
private theorem leftLength : hp.len left .dyn=2 := by
  simp only [Heap.len,MObj.elems_dyn]
  rfl
private theorem leftWords : ArrayRepr hp left (base left.id) machine := by
  constructor
  · rw [leftLength]
    decide
  · rw [leftLength]
    rfl
  · intro i value hit
    simp only [MObj.elems_dyn] at hit
    cases i with
    | zero => cases hit;rfl
    | succ i => cases i with
      | zero => cases hit;rfl
      | succ i => cases hit
private theorem leftMiddleWords : ArrayRepr middle left (base left.id) middleWord := by
  apply primitive_words_after_reference root right left base machine 0 leftWords
  intro c hc
  rw [leftLength] at hc
  change 1≤c ∧ c<4 at hc
  change c≠17
  omega
private theorem rightMiddleWords : ArrayRepr middle right (base right.id) middleWord := by
  apply primitive_words_after_reference root right right base machine 0 rightWords
  intro c hc
  rw [rightLength] at hc
  change 8≤c ∧ c<10 at hc
  change c≠17
  omega
private theorem selectedMiddle : middle.index root .dyn (indexValue (wmod 0))=some right :=
  redirect_write_client.2.2.1
private theorem selectedWithValue : Evm.run (readArrayCode (wmod 16))
    ((middleWord.push (.val (wmod 1))).push (.val (wmod 0)))=
      .ok ((middleWord.push (.val (wmod 1))).push (.val (wmod 8))) 0 := by
  have parentMid := parentAt.set 0 (by rw [parentLength];decide) right (by decide)
  have represented : RefArrayRepr middle root base middleWord := parentMid.word
  have read := (represented.stack (middleWord.push (.val (wmod 1))).stack).read (wmod 0)
  simp only [RefOut,selectedMiddle,TRes.ofOpt,Except.ok.injEq,reduceCtorEq,false_and,or_false] at read
  obtain ⟨actual,equal,run⟩ := read
  cases equal
  simpa only [middleWord,Machine.push] using run
private theorem endpointNative : middle.writeAddr (.index right .dyn (indexValue (wmod 1))) true=none := by
  simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast,middle,
    Heap.get_set_ne hp root right (by decide),MObj.elems_dyn]
  rfl
private theorem leftSame : middle.writeAddr (.index left .dyn (indexValue (wmod 0))) true=some middle := by
  have bound : (wmod 0).val<(MObj.elems .dyn (middle.get left)).length := by
    simp only [middle,Heap.get_set_ne hp root left (by decide),MObj.elems_dyn]
    decide
  simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast,bound,↓reduceIte]
  have unchanged : MObj.setElem .dyn (middle.get left) 0 true=middle.get left := by
    have elements : MObj.elems .dyn (MObj.setElem .dyn (middle.get left) 0 true)=
        MObj.elems .dyn (middle.get left) := by
      rw [MObj.elems_setElem]
      simp only [middle,Heap.get_set_ne hp root left (by decide),MObj.elems_dyn]
      rfl
    apply Subtype.ext
    simpa only [MObj.elems_dyn] using elements
  rw [show (wmod 0).val=0 from by decide,unchanged]
  rfl

/-- All parent identities, both complete child values and the neighbor survive
at their actual initial/middle/final stages, including the retained LEFT entry. -/
theorem typed_vectors :
    [(MObj.elems .dyn (hp.get root)).map HRef.id,(MObj.elems .dyn (middle.get root)).map HRef.id,
      (MObj.elems .dyn (final.get root)).map HRef.id]=[[1,1],[2,1],[2,1]] ∧
    [MObj.elems .dyn (hp.get left),MObj.elems .dyn (hp.get right),
      MObj.elems .dyn (middle.get left),MObj.elems .dyn (middle.get right),
      MObj.elems .dyn (final.get left),MObj.elems .dyn (final.get right)]=
        [[true,false],[false],[true,false],[false],[true,false],[true]] ∧
    [MObj.elems .dyn (hp.get neighbor),MObj.elems .dyn (middle.get neighbor),MObj.elems .dyn (final.get neighbor)]=
      [[u 8,u 9],[u 8,u 9],[u 8,u 9]] ∧
    [hp.index left .dyn (u 0),middle.index right .dyn (u 0),final.index right .dyn (u 0)]=[some true,some false,some true] ∧
    [root.id,left.id,right.id,neighbor.id]=[0,1,2,3] := by
  simp only [final,middle,Heap.index,Heap.get_set_same,
    Heap.get_set_ne (hp.set root (MObj.setElem .dyn (hp.get root) 0 right)) right root (by decide),
    Heap.get_set_ne (hp.set root (MObj.setElem .dyn (hp.get root) 0 right)) right left (by decide),
    Heap.get_set_ne (hp.set root (MObj.setElem .dyn (hp.get root) 0 right)) right neighbor (by decide),
    Heap.get_set_ne hp root left (by decide),Heap.get_set_ne hp root right (by decide),
    Heap.get_set_ne hp root neighbor (by decide),MObj.elems_setElem,MObj.elems_dyn]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem word_vectors :
    [wordVector machine,wordVector middleWord,wordVector finalWord]=
      [[32,2,1,0,1,0,2,1,1,2,8,9].map (fun n => Evm.Word.val (wmod n)),
       [32,2,1,0,1,0,2,8,1,2,8,9].map (fun n => Evm.Word.val (wmod n)),
       [32,2,1,0,1,1,2,8,1,2,8,9].map (fun n => Evm.Word.val (wmod n))] ∧
    finalWord.stack=[.val (wmod 77),.val (wmod 88)] := by
  exact ⟨rfl,rfl⟩

theorem initial_byte_vector : byteVector bytes=[1024,2,1,0,1,0,2,32,32,2,8,9].map Semantics.wordBytes := by
  simp only [byteVector,cells,List.map_cons,List.map_nil]
  rw [image_read 0 1024 (by decide),
    image_read 1 2 (by decide),
    image_read 2 1 (by decide),
    image_read 3 0 (by decide),
    image_read 8 1 (by decide),
    image_read 9 0 (by decide),
    image_read 16 2 (by decide),
    image_read 17 32 (by decide),
    image_read 18 32 (by decide),
    image_read 24 2 (by decide),
    image_read 25 8 (by decide),
    image_read 26 9 (by decide)]

theorem middle_byte_vector : byteVector middleBytes=[1024,2,1,0,1,0,2,256,32,2,8,9].map Semantics.wordBytes := by
  simp only [byteVector,cells,List.map_cons,List.map_nil]
  rw [middle_other_read 0 1024 (by decide) (by decide),
    middle_other_read 1 2 (by decide) (by decide),
    middle_other_read 2 1 (by decide) (by decide),
    middle_other_read 3 0 (by decide) (by decide),
    middle_other_read 8 1 (by decide) (by decide),
    middle_other_read 9 0 (by decide) (by decide),
    middle_other_read 16 2 (by decide) (by decide),
    middle_written_read,
    middle_other_read 18 32 (by decide) (by decide),
    middle_other_read 24 2 (by decide) (by decide),
    middle_other_read 25 8 (by decide) (by decide),
    middle_other_read 26 9 (by decide) (by decide)]

theorem final_byte_vector : byteVector finalBytes=[1024,2,1,0,1,1,2,256,32,2,8,9].map Semantics.wordBytes := by
  simp only [byteVector,cells,List.map_cons,List.map_nil]
  rw [final_other_read 0 1024 (by decide) (by decide) (by decide),
    final_other_read 1 2 (by decide) (by decide) (by decide),
    final_other_read 2 1 (by decide) (by decide) (by decide),
    final_other_read 3 0 (by decide) (by decide) (by decide),
    final_other_read 8 1 (by decide) (by decide) (by decide),
    final_written_read,
    final_other_read 16 2 (by decide) (by decide) (by decide),
    final_pointer_read,
    final_other_read 18 32 (by decide) (by decide) (by decide),
    final_other_read 24 2 (by decide) (by decide) (by decide),
    final_other_read 25 8 (by decide) (by decide) (by decide),
    final_other_read 26 9 (by decide) (by decide) (by decide)]

/-- Actual valid redirection prefix before the selected length1 endpoint1
rejects. Revert has no suffix machine or claimed transaction rollback. -/
theorem late_endpoint_reject :
    Evm.run (writeArrayCode (wmod 16)) initialStack=.ok middleWord 0 ∧
    middle.writeAddr (.index right .dyn (indexValue (wmod 1))) true=none ∧
    Evm.run (pathCode (wmod 1)) middleWord=.revert ∧
    Evm.run (program (wmod 1)) initialStack=.revert ∧
    middle.index root .dyn (indexValue (wmod 0))=some right ∧
    middle.get right=hp.get right := by
  have failed : Evm.run (writeArrayCode (base right.id))
      ((middleWord.push (.val (wmod 1))).push (.val (wmod 1)))=.revert := by
    rcases writeArray_correct rightMiddleWords (wmod 1) true (.val (wmod 1)) rfl with
      ⟨out,native,run,represented⟩ | ⟨native,run⟩
    · rw [endpointNative] at native
      cases native
    · exact run
  have stackFailed : Evm.run writeArrayStackCode
      ((((middleWord.push (.val (wmod 1))).push (.val (wmod 8))).push (.val (wmod 1))))=.revert := by
    rw [writeArrayStackCode,arrayStack_append_eq (middleWord.push (.val (wmod 1))) (wmod 8) (wmod 1)
      (middle.len right .dyn) (middle.len_dyn_lt right) rightMiddleWords.length]
    exact failed
  have pathFailed : Evm.run (pathCode (wmod 1)) middleWord=.revert := by
    rw [pathCode,Evm.run_append_ok (show Evm.run [.push (.val (wmod 1)),.push (.val (wmod 0))] middleWord=
      .ok ((middleWord.push (.val (wmod 1))).push (.val (wmod 0))) 0 from rfl),
      Evm.run_append_ok selectedWithValue,
      Evm.run_append_ok (show Evm.run [.push (.val (wmod 1))] ((middleWord.push (.val (wmod 1))).push (.val (wmod 8)))=
        .ok (((middleWord.push (.val (wmod 1))).push (.val (wmod 8))).push (.val (wmod 1))) 0 from rfl)]
    exact stackFailed
  have firstRun := redirect_write_client.2.2.2.2.1
  refine ⟨firstRun,endpointNative,pathFailed,?_,selectedMiddle,Heap.get_set_ne hp root right (by decide) _⟩
  rw [program,Evm.run_append_ok firstRun]
  exact pathFailed

private def staleWord : Machine := writeMachine middleWord 2 (.val (wmod 1))
private def staleBytes := Environment.writeBytes middleBytes 64 (Semantics.wordBytes 1)
/-- Using the stale initial LEFT base after real redirection leaves selected
RIGHT false, contrasting the dynamic path's true and physical numeric1. -/
theorem stale_base_negative :
    Evm.run (writeArrayCode (wmod 16) ++
      ([.push (.val (wmod 1)),.push (.val (wmod 0))] ++ writeArrayCode (wmod 1))) initialStack=.ok staleWord 0 ∧
    middle.writeAddr (.index left .dyn (indexValue (wmod 0))) true=some middle ∧
    [staleWord.mem 17,staleWord.mem 18,staleWord.mem 9,finalWord.mem 9]=
      [.val (wmod 8),.val (wmod 1),.val (wmod 0),.val (wmod 1)] ∧
    Environment.readMemory staleBytes 288 32=Semantics.wordBytes 0 ∧
    Semantics.wordBytes 0≠Semantics.wordBytes 1 := by
  have staleRun : Evm.run (writeArrayCode (base left.id))
      ((middleWord.push (.val (wmod 1))).push (.val (wmod 0)))=.ok staleWord 0 := by
    rcases writeArray_correct leftMiddleWords (wmod 0) true (.val (wmod 1)) rfl with
      ⟨out,native,run,represented⟩ | ⟨native,run⟩
    · exact run
    · rw [leftSame] at native
      cases native
  refine ⟨?_,leftSame,rfl,?_,by decide⟩
  · rw [Evm.run_append_ok redirect_write_client.2.2.2.2.1,
      Evm.run_append_ok (show Evm.run [.push (.val (wmod 1)),.push (.val (wmod 0))] middleWord=
        .ok ((middleWord.push (.val (wmod 1))).push (.val (wmod 0))) 0 from rfl)]
    exact staleRun
  · unfold staleBytes
    rw [readMemory_write_frame]
    · exact middle_other_read 9 0 (by decide) (by decide)
    · simp only [Environment.wordBytes_length]
      omega

/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.redirect_write_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms redirect_write_client
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.typed_vectors' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms typed_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.word_vectors' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms word_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.initial_byte_vector' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initial_byte_vector
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.middle_byte_vector' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms middle_byte_vector
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.final_byte_vector' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms final_byte_vector
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.late_endpoint_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms late_endpoint_reject
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.stale_base_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stale_base_negative
private def payloadBytes : List UInt8 := [7,0,255]
private def byteAfter := Environment.writeBytes bytes 384 payloadBytes
private theorem byte_vectors_framed : byteVector byteAfter=byteVector bytes := by
  first
  | solve | simp only [] | omega
  | apply List.map_congr_left
    intro c hc
    apply readMemory_congr
    intro j hj
    apply Environment.writeBytes_frame
    simp only [payloadBytes,List.length_cons,List.length_nil]
    simp only [cells,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

/-- Actual checked byte emission retains the typed repeated parent, numeric
child, complete old byte vector (including free pointer/neighbour), and caller
stack whenever the published guard returns a machine. No graph closure claim. -/
theorem materialize_mixed_frames (caller : List Roadmap.Word) (suffix : Backend.Program) :
    Failure.Slice.checkedRun (Environment.materialize 384 payloadBytes++(.op .REVERT::suffix))
      ⟨⟨384,by decide⟩::⟨3,by decide⟩::caller,bytes⟩=
      (if caller.length+4≤1024 then some (⟨caller,byteAfter⟩,some (.revert payloadBytes)) else none) ∧
    (∀ out,Failure.Slice.checkedRun (Environment.materialize 384 payloadBytes++(.op .REVERT::suffix))
      ⟨⟨384,by decide⟩::⟨3,by decide⟩::caller,bytes⟩=some out →
      ReferenceArrayAt hp root base machine out.1.memory ∧
      WordFrame machine out.1.memory (fun c => (base right.id).val≤c ∧ c<(base right.id).val+1+hp.len right .dyn) ∧
      out.1.stack=caller ∧ out.2=some (.revert payloadBytes) ∧
      byteVector out.1.memory=[1024,2,1,0,1,0,2,32,32,2,8,9].map Semantics.wordBytes ∧
      Environment.readMemory out.1.memory 384 3=payloadBytes ∧
      Environment.readMemory out.1.memory 544 32=Environment.readMemory out.1.memory 576 32) := by
  first
  | solve | simp only [] | omega
  | have header : 384+payloadBytes.length≤32*(base root.id).val ∨ 32*(base root.id).val+32≤384 := by decide
    have ptrs : ∀ c,ReferenceSlots hp root base c → 384+payloadBytes.length≤32*c ∨ 32*c+32≤384 := by
      intro c hc
      obtain ⟨i,hi,eq⟩ := hc
      rw [parentLength] at hi
      change c=16+1+i at eq
      subst c
      change 387≤32*(16+1+i) ∨ 32*(16+1+i)+32≤384
      omega
    have nums : ∀ c,(base right.id).val≤c ∧ c<(base right.id).val+1+hp.len right .dyn →
        384+payloadBytes.length≤32*c ∨ 32*c+32≤384 := by
      intro c hc
      rw [rightLength] at hc
      change 8≤c ∧ c<10 at hc
      change 387≤32*c ∨ 32*c+32≤384
      omega
    have linked := parentAt.materialize_checked_revert _ rightBytes 7 [0,255] ⟨384,by decide⟩ ⟨3,by decide⟩ caller suffix
        rfl (by decide) header ptrs nums
    refine ⟨linked.1,?_⟩
    intro out returned
    obtain ⟨parent,numeric,stack,halt⟩ := linked.2 out returned
    have run := linked.1
    change Failure.Slice.checkedRun (Environment.materialize 384 payloadBytes++(.op .REVERT::suffix))
      ⟨⟨384,by decide⟩::⟨3,by decide⟩::caller,bytes⟩=
      (if caller.length+4≤1024 then some (⟨caller,byteAfter⟩,some (.revert payloadBytes)) else none) at run
    rw [run] at returned
    by_cases room : caller.length+4≤1024
    · rw [if_pos room] at returned
      have resultEq := (Option.some.inj returned).symm
      refine ⟨parent,numeric,stack,halt,?_,?_,?_⟩
      · rw [resultEq]
        exact byte_vectors_framed.trans initial_byte_vector
      · rw [resultEq]
        exact Environment.read_written payloadBytes 384 bytes
      · have left0 : (MObj.elems .dyn (hp.get root))[0]?=some left := by rw [parentElements];rfl
        have left1 : (MObj.elems .dyn (hp.get root))[1]?=some left := by rw [parentElements];rfl
        exact (parent.child_bytes 0 left left0).2.trans (parent.child_bytes 1 left left1).2.symm
    · rw [if_neg room] at returned
      cases returned

/-- A real overlapping one-byte emission changes the low pointer byte32 to7.
The exposed byte-slice halt machine exists, but its initial typed parent
representation is false. This does not assert every overlap is invalid. -/
theorem materialize_pointer_overlap :
    Failure.Slice.checkedRun (Environment.materialize 575 [7]++[.op .REVERT])
      ⟨[⟨575,by decide⟩,⟨1,by decide⟩],bytes⟩=
      some (⟨[],Environment.writeBytes bytes 575 [7]⟩,some (.revert [7])) ∧
    ¬ReferenceArrayAt hp root base machine (Environment.writeBytes bytes 575 [7]) := by
  first
  | solve | simp only [] | omega
  | refine ⟨(materialize_checked_revert [7] ⟨575,by decide⟩ ⟨1,by decide⟩ [] bytes [] rfl (by decide) (by decide)).2,?_⟩
    intro wrong
    have selected : (MObj.elems .dyn (hp.get root))[0]?=some left := by rw [parentElements];rfl
    have read := (wrong.child_bytes 0 left selected).2
    change Environment.readMemory (Environment.writeBytes bytes 575 [7]) 544 32=Semantics.wordBytes 32 at read
    have asBytes : Failure.Slice.getBytes (Environment.writeBytes bytes 575 [7]) 544 32=Semantics.wordBytes 32 :=
      (readMemory_eq_getBytes _ 544 32).symm.trans read
    have found : (Failure.Slice.getBytes (Environment.writeBytes bytes 575 [7]) 544 32)[31]?=some (7 : UInt8) := by
      rw [List.getElem?_eq_getElem (by rw [getBytes_length];decide),
        getBytes_at (Environment.writeBytes bytes 575 [7]) 544 32 31 (by decide)]
      rfl
    have low := congrArg (fun xs : List UInt8 => xs[31]?) asBytes
    change (Failure.Slice.getBytes (Environment.writeBytes bytes 575 [7]) 544 32)[31]?=(Semantics.wordBytes 32)[31]? at low
    rw [found,show (Semantics.wordBytes 32)[31]?=some (32 : UInt8) by decide] at low
    exact (by decide : (some (7 : UInt8))≠some 32) low

/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.materialize_mixed_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materialize_mixed_frames
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.materialize_pointer_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materialize_pointer_overlap
private abbrev WE := Lowering.V08.SourceEnvironmentControls.E
private def originalWorld := Lowering.V08.SourceEnvironmentControls.populated
private def beforeWorld : Source.St WE := {originalWorld with ex := originalWorld.ex.run WorldControls.ops}
private def dirtyOps : List (Source.Op WE.layout WE.lay WE.lay) :=
  [.account Lowering.V08.SourceEnvironmentControls.sender (fun account => {account with balance:=66}),
   .account Lowering.V08.SourceEnvironmentControls.self (fun account => {account with storage := account.storage.write Lowering.V08.SourceEnvironmentControls.saved (.bool true)}),
   .transient Lowering.V08.SourceEnvironmentControls.self (fun store => store.write Lowering.V08.SourceEnvironmentControls.scratch (.bool true))]
private def dirtyWorld : Source.St WE := {beforeWorld with ex := beforeWorld.ex.run dirtyOps}
private def savedBytePrefix : Failure.Slice.Machine := ⟨[⟨77,by decide⟩,⟨88,by decide⟩],byteAfter⟩
private def emittedBytes := Failure.Slice.putBytes byteAfter 544 (Source.errorData WorldControls.reason)

/-- Complete existing Source observation projection across actual journal ops.
The intermediate checkpoint materially differs from both initial and dirty. -/
theorem checkpoint_world_vectors :
    [WorldControls.view originalWorld,WorldControls.view beforeWorld,WorldControls.view dirtyWorld]=
      [(93,7,some (.bool true),some (.bool true),3,1,
        some ⟨.bytes .memory,.bytes [0,255]⟩,
        [.call Lowering.V08.SourceEnvironmentControls.self ⟨7,by decide⟩ [0,255] false],
        [(Lowering.V08.SourceEnvironmentControls.self,[171,0,255])],⟨[.bool],.cons (.bool true) .nil⟩),
       (88,7,some (.bool false),some (.bool false),6,1,
        some ⟨.bytes .memory,.bytes [0,255]⟩,
        [.call Lowering.V08.SourceEnvironmentControls.self ⟨7,by decide⟩ [0,255] false],
        [(Lowering.V08.SourceEnvironmentControls.self,[171,0,255])],⟨[.bool],.cons (.bool true) .nil⟩),
       (66,7,some (.bool true),some (.bool true),9,1,
        some ⟨.bytes .memory,.bytes [0,255]⟩,
        [.call Lowering.V08.SourceEnvironmentControls.self ⟨7,by decide⟩ [0,255] false],
        [(Lowering.V08.SourceEnvironmentControls.self,[171,0,255])],⟨[.bool],.cons (.bool true) .nil⟩)] := by
  first | rfl | simp only [] | decide | omega

/-- Actual byte prefix supplies the saved mixed frame. Actual Source remains
at the dirty reason-error state; separate journal restore returns AFTER prefix.
This pairs component executions, not a compiler/world-heap codec. -/
theorem materialize_world_checkpoint (pipeline : Roadmap.Pipeline) (horizon : Nat) (suffix : Backend.Program) :
    (Source.evalE (Lowering.V08.SourceEnvironmentControls.global pipeline) Lowering.V08.SourceEnvironmentControls.frame (horizon+5)
      (Lowering.V08.SourceFailures.reason WorldControls.reason)).run (Lowering.V08.SourceEnvironmentControls.locals,dirtyWorld)=
        (.error (.revert (Source.errorData WorldControls.reason)),(Lowering.V08.SourceEnvironmentControls.locals,dirtyWorld)) ∧
    Failure.Slice.checkedRun (Environment.materialize 384 payloadBytes) ⟨savedBytePrefix.stack,bytes⟩=some (savedBytePrefix,none) ∧
    (beforeWorld.ex.enter Lowering.V08.SourceEnvironmentControls.frame.this Lowering.V08.SourceEnvironmentControls.frame.sender
      Lowering.V08.SourceEnvironmentControls.frame.value Lowering.V08.SourceEnvironmentControls.frame.cd
      Lowering.V08.SourceEnvironmentControls.frame.static).rollback dirtyWorld.ex=beforeWorld.ex ∧
    Failure.Slice.checkedRun (Failure.emit 544 (.reason WorldControls.reason)++suffix) savedBytePrefix=
      some ({savedBytePrefix with memory := emittedBytes},some (.revert (Source.errorData WorldControls.reason))) ∧
    ∃ output,Failure.Local.execute (Failure.Local.save (worldJournal beforeWorld.ex savedBytePrefix)) 544 (.reason WorldControls.reason)
        (worldJournal dirtyWorld.ex savedBytePrefix)=some (output,.revert (Source.errorData WorldControls.reason)) ∧
      ReferenceArrayAt hp root base machine output.machine.memory ∧
      WordFrame machine output.machine.memory (fun c => (base right.id).val≤c ∧ c<(base right.id).val+1+hp.len right .dyn) ∧
      output.machine=savedBytePrefix ∧ output.persistent=beforeWorld.ex.world ∧ output.transient=beforeWorld.ex.transient ∧
      byteVector output.machine.memory=[1024,2,1,0,1,0,2,32,32,2,8,9].map Semantics.wordBytes ∧
      Environment.readMemory output.machine.memory 384 3=payloadBytes ∧
      Environment.readMemory emittedBytes 544 (Source.errorData WorldControls.reason).length=Source.errorData WorldControls.reason := by
  first
  | solve | simp only [] | omega
  | have header : 384+payloadBytes.length≤32*(base root.id).val ∨ 32*(base root.id).val+32≤384 := by decide
    have ptrs : ∀ c,ReferenceSlots hp root base c → 384+payloadBytes.length≤32*c ∨ 32*c+32≤384 := by
      intro c hc
      obtain ⟨i,hi,eq⟩ := hc
      rw [parentLength] at hi
      change c=16+1+i at eq
      subst c
      change 387≤32*(16+1+i) ∨ 32*(16+1+i)+32≤384
      omega
    have nums : ∀ c,(base right.id).val≤c ∧ c<(base right.id).val+1+hp.len right .dyn →
        384+payloadBytes.length≤32*c ∨ 32*c+32≤384 := by
      intro c hc
      rw [rightLength] at hc
      change 8≤c ∧ c<10 at hc
      change 387≤32*c ∨ 32*c+32≤384
      omega
    obtain ⟨firstRun,rollback,emission,output,execute,parent,numeric,restored,persistent,transient⟩ :=
      parentAt.materialize_world_unwind _ rightBytes originalWorld.ex WorldControls.ops dirtyOps
        Lowering.V08.SourceEnvironmentControls.frame.this Lowering.V08.SourceEnvironmentControls.frame.sender
        Lowering.V08.SourceEnvironmentControls.frame.value Lowering.V08.SourceEnvironmentControls.frame.cd
        Lowering.V08.SourceEnvironmentControls.frame.static 7 [0,255] 384 savedBytePrefix.stack
        (by decide) (by decide) header ptrs nums 544 WorldControls.reason suffix (by unfold Failure.Fits;decide)
    refine ⟨Lowering.V08.SourceFailures.eval_reason _ _ horizon WorldControls.reason _ _,firstRun,rollback,emission,
      output,execute,parent,numeric,restored,persistent,transient,?_,?_,?_⟩
    · rw [restored]
      exact byte_vectors_framed.trans initial_byte_vector
    · rw [restored]
      exact Environment.read_written payloadBytes 384 bytes
    · rw [readMemory_eq_getBytes]
      exact Failure.Slice.getBytes_putBytes byteAfter 544 (Source.errorData WorldControls.reason)

/-- Saving the original instead would erase the real prefix. Both checkpoint
executions are proved; their different returned worlds expose stale saving. -/
theorem wrong_initial_checkpoint :
    Failure.Local.execute (Failure.Local.save (worldJournal originalWorld.ex ⟨savedBytePrefix.stack,bytes⟩))
      544 (.reason WorldControls.reason) (worldJournal dirtyWorld.ex savedBytePrefix)=
      some (worldJournal originalWorld.ex ⟨savedBytePrefix.stack,bytes⟩,.revert (Source.errorData WorldControls.reason)) ∧
    originalWorld.ex.world≠beforeWorld.ex.world ∧ bytes≠byteAfter := by
  first
  | solve | simp only [] | omega
  | refine ⟨?_,?_,?_⟩
    · rw [Lowering.V08.errorData_transport_total]
      exact Failure.Local.execute_failure _ 544 (Semantics.encodeError WorldControls.reason) _
        (by unfold Failure.Fits;decide) (by decide)
    · intro same
      have balances := congrArg (fun world => (world.accounts Lowering.V08.SourceEnvironmentControls.sender).balance) same
      change 93=88 at balances
      exact absurd balances (by decide)
    · intro same
      have observed := congrArg (fun memory => Environment.readMemory memory 384 3) same
      have old : Environment.readMemory bytes 384 3=[0,0,0] := by
        apply (readMemory_congr 384 3 bytes (fun _ => 0) ?_).trans
        · rfl
        · intro j hj
          simp only [bytes,image,List.foldl_cons,List.foldl_nil]
          repeat (rw [Environment.writeBytes_frame]; case outside => simp only [Environment.wordBytes_length];omega)
      have new : Environment.readMemory byteAfter 384 3=payloadBytes := Environment.read_written payloadBytes 384 bytes
      change Environment.readMemory bytes 384 3=Environment.readMemory byteAfter 384 3 at observed
      rw [old,new] at observed
      exact (by decide : ([0,0,0] : List UInt8)≠payloadBytes) observed

/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.checkpoint_world_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkpoint_world_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.materialize_world_checkpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materialize_world_checkpoint
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.wrong_initial_checkpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_initial_checkpoint
private def dirtyPointerBytes := Environment.writeBytes byteAfter 575 [7]
private def dirtyPointerMachine : Failure.Slice.Machine := ⟨savedBytePrefix.stack,dirtyPointerBytes⟩

/-- The actual second materializer corrupts a typed pointer after saving the
reached prefix. The whole append emits from dirty memory; explicit restore
recovers the saved mixed frame. Source failure independently retains dirty state. -/
theorem dirty_pointer_checkpoint (pipeline : Roadmap.Pipeline) (horizon : Nat) (suffix : Backend.Program) :
    (Source.evalE (Lowering.V08.SourceEnvironmentControls.global pipeline) Lowering.V08.SourceEnvironmentControls.frame (horizon+5)
      (Lowering.V08.SourceFailures.reason WorldControls.reason)).run (Lowering.V08.SourceEnvironmentControls.locals,dirtyWorld)=
        (.error (.revert (Source.errorData WorldControls.reason)),(Lowering.V08.SourceEnvironmentControls.locals,dirtyWorld)) ∧
    Failure.Slice.checkedRun (Environment.materialize 384 payloadBytes++
      (Environment.materialize 575 [7]++(Failure.emit 544 (.reason WorldControls.reason)++suffix))) ⟨savedBytePrefix.stack,bytes⟩=
      some ({dirtyPointerMachine with memory := Failure.Slice.putBytes dirtyPointerBytes 544 (Source.errorData WorldControls.reason)},
        some (.revert (Source.errorData WorldControls.reason))) ∧
    Failure.Local.execute (Failure.Local.save (worldJournal beforeWorld.ex savedBytePrefix)) 544 (.reason WorldControls.reason)
      (worldJournal dirtyWorld.ex dirtyPointerMachine)=some (worldJournal beforeWorld.ex savedBytePrefix,.revert (Source.errorData WorldControls.reason)) ∧
    ReferenceArrayAt hp root base machine savedBytePrefix.memory ∧
    WordFrame machine savedBytePrefix.memory (fun c => (base right.id).val≤c ∧ c<(base right.id).val+1+hp.len right .dyn) ∧
    byteVector savedBytePrefix.memory=[1024,2,1,0,1,0,2,32,32,2,8,9].map Semantics.wordBytes ∧
    ¬ReferenceArrayAt hp root base machine dirtyPointerBytes := by
  first
  | solve | simp only [] | omega
  | have header : 384+payloadBytes.length≤32*(base root.id).val ∨ 32*(base root.id).val+32≤384 := by decide
    have ptrs : ∀ c,ReferenceSlots hp root base c → 384+payloadBytes.length≤32*c ∨ 32*c+32≤384 := by
      intro c hc
      obtain ⟨i,hi,eq⟩ := hc
      rw [parentLength] at hi
      change c=16+1+i at eq
      subst c
      change 387≤32*(16+1+i) ∨ 32*(16+1+i)+32≤384
      omega
    have nums : ∀ c,(base right.id).val≤c ∧ c<(base right.id).val+1+hp.len right .dyn →
        384+payloadBytes.length≤32*c ∨ 32*c+32≤384 := by
      intro c hc
      rw [rightLength] at hc
      change 8≤c ∧ c<10 at hc
      change 387≤32*c ∨ 32*c+32≤384
      omega
    obtain ⟨firstRun,dirtyRun,linked,rollback,execute,parent,numeric⟩ :=
      parentAt.materialize_dirty_world_unwind _ rightBytes originalWorld.ex WorldControls.ops dirtyOps
        Lowering.V08.SourceEnvironmentControls.frame.this Lowering.V08.SourceEnvironmentControls.frame.sender
        Lowering.V08.SourceEnvironmentControls.frame.value Lowering.V08.SourceEnvironmentControls.frame.cd
        Lowering.V08.SourceEnvironmentControls.frame.static 7 [0,255] 384 7 [] 575 savedBytePrefix.stack
        (by decide) (by decide) (by decide) header ptrs nums 544 WorldControls.reason suffix (by unfold Failure.Fits;decide)
    refine ⟨Lowering.V08.SourceFailures.eval_reason _ _ horizon WorldControls.reason _ _,linked,execute,parent,numeric,
      byte_vectors_framed.trans initial_byte_vector,?_⟩
    intro wrong
    have selected : (MObj.elems .dyn (hp.get root))[0]?=some left := by rw [parentElements];rfl
    have read := (wrong.child_bytes 0 left selected).2
    change Environment.readMemory dirtyPointerBytes 544 32=Semantics.wordBytes 32 at read
    have asBytes : Failure.Slice.getBytes dirtyPointerBytes 544 32=Semantics.wordBytes 32 :=
      (readMemory_eq_getBytes _ 544 32).symm.trans read
    have found : (Failure.Slice.getBytes dirtyPointerBytes 544 32)[31]?=some (7 : UInt8) := by
      rw [List.getElem?_eq_getElem (by rw [getBytes_length];decide),getBytes_at dirtyPointerBytes 544 32 31 (by decide)]
      rfl
    have low := congrArg (fun xs : List UInt8 => xs[31]?) asBytes
    change (Failure.Slice.getBytes dirtyPointerBytes 544 32)[31]?=(Semantics.wordBytes 32)[31]? at low
    rw [found,show (Semantics.wordBytes 32)[31]?=some (32 : UInt8) by decide] at low
    exact (by decide : (some (7 : UInt8))≠some 32) low

/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.dirty_pointer_checkpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_pointer_checkpoint

private theorem prefix_image_read (c v : Nat) (hit : (c,v)∈image) :
    Environment.readMemory byteAfter (32*c) 32=Semantics.wordBytes v := by
  have sep : 32*c+32≤384 ∨ 384+payloadBytes.length≤32*c := by
    simp only [image,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hit
    rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  exact (readMemory_write_frame bytes (32*c) 32 384 payloadBytes sep).trans (image_read c v hit)

private theorem dirty_image_vector :
    byteVector dirtyPointerBytes=image.map (fun cv =>
      if cv.1=17 then (Semantics.wordBytes cv.2).set 31 7 else Semantics.wordBytes cv.2) := by
  change image.map (fun cv => Environment.readMemory dirtyPointerBytes (32*cv.1) 32)=_
  apply List.map_congr_left
  intro cv hit
  rcases cv with ⟨c,v⟩
  by_cases selected : c=17
  · subst c
    rw [if_pos rfl]
    exact (readMemory_writeByte_at byteAfter 544 32 31 7).trans
      (congrArg (fun bs : List UInt8 => bs.set 31 7) (prefix_image_read 17 v hit))
  · rw [if_neg selected]
    have sep : 32*c+32≤575 ∨ 575+([7] : List UInt8).length≤32*c := by
      change 32*c+32≤575 ∨ 576≤32*c
      simp only [image,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hit
      rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega
    exact (readMemory_write_frame byteAfter (32*c) 32 575 [7] sep).trans (prefix_image_read c v hit)

/-- Complete twelve-word observations in actual initial/saved/dirty/restored
order. Only byte31 of the first repeated pointer changes in the dirty table;
all other bytes, child objects, neighbour and allocator word remain explicit. -/
theorem dirty_pointer_complete_tables :
    [byteVector bytes,byteVector byteAfter,byteVector dirtyPointerBytes,byteVector savedBytePrefix.memory]=
      [[1024,2,1,0,1,0,2,32,32,2,8,9].map Semantics.wordBytes,
       [1024,2,1,0,1,0,2,32,32,2,8,9].map Semantics.wordBytes,
       ([1024,2,1,0,1,0,2,32,32,2,8,9].map Semantics.wordBytes).set 7 ((Semantics.wordBytes 32).set 31 7),
       [1024,2,1,0,1,0,2,32,32,2,8,9].map Semantics.wordBytes] := by
  first
  | solve | simp only [] | omega
  | rw [initial_byte_vector,byte_vectors_framed,initial_byte_vector,dirty_image_vector]
    simp only [image,List.map_cons,List.map_nil,List.set_cons_zero,List.set_cons_succ,Nat.reduceEqDiff,if_true,if_false,savedBytePrefix]
    rw [byte_vectors_framed,initial_byte_vector]
    simp only [List.map_cons,List.map_nil]

/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.dirty_pointer_complete_tables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_pointer_complete_tables

/-- The complete dirty table cannot be replaced by the stale saved table.
The observed last byte of the first pointer is7 rather than32. -/
theorem dirty_pointer_table_not_saved : byteVector dirtyPointerBytes≠byteVector byteAfter := by
  first
  | solve | simp only [] | omega
  | intro same
    have dirty : ((byteVector dirtyPointerBytes)[7]?).bind (fun word => word[31]?)=some (7 : UInt8) := by
      rw [dirty_image_vector]
      decide
    have saved : ((byteVector byteAfter)[7]?).bind (fun word => word[31]?)=some (32 : UInt8) := by
      rw [byte_vectors_framed,initial_byte_vector]
      decide
    rw [same,saved] at dirty
    exact (by decide : (some (32 : UInt8))≠some 7) dirty

/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls.dirty_pointer_table_not_saved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_pointer_table_not_saved

end Solidity.Backend.MemoryOps.Physical.ReferenceSequenceControls
