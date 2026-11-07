import Solidity.Backend.MemoryOps.PhysicalFixedChildProgram
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples
import Solidity.Backend.MemoryOps.SourceUintFixedDeclaration

/-! Inhabited fixed-child controls. Repeated parent slots alias the same fixed
child; no Source parent-to-intrinsic observer or general byte compiler is assumed. -/
namespace Solidity.Backend.MemoryOps.Physical.FixedChildControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 F0 s0)
private abbrev A : RefTy := .fixed (.prim .uint) 3
private abbrev P : RefTy := .array (.ref A)
private abbrev N : RefTy := .fixed (.prim .uint) 2
private abbrev H : HTy := [P,A,N]
private def root : HRef H P := ⟨0,rfl⟩
private def child : HRef H A := ⟨1,rfl⟩
private def neighbor : HRef H N := ⟨2,rfl⟩
private def u (n : Nat) : PrimTy.uint.Denote := indexValue (wmod n)
private def hp : Heap H := (⟨[child,child],by decide⟩,⟨[u 7,u 0,u (W-1)],rfl⟩,⟨[u 8,u 9],rfl⟩,())
private def base (id : Nat) : Fin W := if id=0 then wmod 16 else if id=1 then wmod 8 else wmod 24
private def machine : Machine := {Machine.init with stack := [w[77],w[88]],mem := fun c =>
  if c=0 then w[32] else if c=16 then w[2] else if c=17 ∨ c=18 then w[8]
  else if c=8 then w[7] else if c=10 then (Word.val (wmod (W-1))) else if c=24 then w[8] else if c=25 then w[9] else w[0]}
private def image : List (Nat×Nat) := [(0,1024),(8,7),(9,0),(10,W-1),(16,2),(17,256),(18,256),(24,8),(25,9)]
private def bytes : Environment.Memory := image.foldl
  (fun memory cell => Environment.writeBytes memory (32*cell.1) (Semantics.wordBytes cell.2)) (fun _ => 0)
private def sourceHeap : Source.Heap E0.layout :=
  (((s0 (E := E0)).heap.alloc ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get child)⟩).1.alloc
    ⟨.array .memory (.int .u256) (some 2),sourceUintFixedObject (hp.get neighbor)⟩).1
private def y : Source.EMState E0 [] := (.nil,{s0 with heap := sourceHeap})
private theorem sourceAt : SourceUintFixedAt y 0 hp child := by rfl
private theorem sourceNeighbor : y.2.heap.get 1=some ⟨.array .memory (.int .u256) (some 2),sourceUintFixedObject (hp.get neighbor)⟩ := by rfl
private theorem image_read (c value : Nat) (hit : (c,value)∈image) :
    Environment.readMemory bytes (32*c) 32=Semantics.wordBytes value := by
  simp only [image,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hit
  rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    simp only [bytes,image,List.foldl_cons,List.foldl_nil]
    repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length];omega)
    simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes _) _ _
private theorem parentLength : hp.len root .dyn=2 := by
  simp only [Heap.len,MObj.elems_dyn]
  rfl
private theorem parentElements : MObj.elems .dyn (hp.get root)=[child,child] := by
  simp only [MObj.elems_dyn]
  rfl
private theorem parentAt : ReferenceArrayAt hp root base machine bytes := by
  constructor
  · constructor
    · rw [parentLength];decide
    · rw [parentLength];rfl
    · intro i q hit
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
      rcases which with rfl|rfl
      · subst c
        exact ⟨wmod 8,rfl,by decide,image_read 17 256 (by decide)⟩
      · subst c
        exact ⟨wmod 8,rfl,by decide,image_read 18 256 (by decide)⟩

/-- Actual source/intrinsic success uses cell9, not a dynamic header offset10.
The repeated typed parent, old neighbour and all other Source addresses frame. -/
theorem headerless_write (fuel : Nat) :
    ∃ (out : Heap H) (z : Source.EMState E0 []) (logical offset : Fin W),
      logical.val=9 ∧ offset.val=288 ∧
      hp.writeAddr (.index child .fixed (indexValue (wmod 1))) (u 42)=some out ∧
      (Source.writeLoc (E := E0) (Γ := []) F0 fuel (.mem 0 1) (sourceUint (u 42))).run y=(.ok (),z) ∧
      Evm.run [.mstoreAt] ((machine.push w[42]).push (.val logical))=.ok (writeMachine machine 9 w[42]) 0 ∧
      ReferenceArrayAt out root base (writeMachine machine 9 w[42])
        (Environment.writeBytes bytes 288 (Semantics.wordBytes 42)) ∧
      SourceUintFixedAt z 0 out child ∧ out.get neighbor=hp.get neighbor ∧
      z.2.heap.get 1=some ⟨.array .memory (.int .u256) (some 2),sourceUintFixedObject (hp.get neighbor)⟩ ∧
      (∀ a,a≠0 → z.2.heap.get a=y.2.heap.get a) ∧ z.1=y.1 ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | have slots : ∀ c,ReferenceSlots hp root base c → c≠9 := by
      intro c hc
      obtain ⟨i,hi,eq⟩ := hc
      change c=16+1+i at eq
      omega
    obtain ⟨out,z,logical,offset,loc,off,typed,run,word,byte,parent,source,locals,objects,addresses,world,events,logs,fnLocals,frame⟩ :=
      parentAt.write_fixed_uint sourceAt F0 fuel (wmod 1) (wmod 42) (by decide) (by decide) (by decide) slots
    exact ⟨out,z,logical,offset,loc,off,typed,run,word,parent,source,objects neighbor (by decide),(addresses 1 (by decide)).trans sourceNeighbor,addresses,locals,world,events,logs,fnLocals⟩

/-- Real fixed endpoint rejection returns Source panic bytes and no typed heap.
Terminal MSTORE has no array guard; no target revert is claimed by this law. -/
theorem endpoint_rejected (fuel : Nat) :
    (Source.writeLoc (E := E0) (Γ := []) F0 fuel (.mem 0 3) (sourceUint (u 42))).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    hp.writeAddr (.index child .fixed (indexValue (wmod 3))) (u 42)=none := by
  exact sourceAt.write_bounds F0 fuel (indexValue (wmod 3)) (u 42) (by decide)

/-- Skipping the headerless rule changes a different cell and misses the write. -/
theorem wrong_dynamic_offset :
    writeMachine machine 10 w[42]≠writeMachine machine 9 w[42] := by
  first
  | solve | simp only [] | omega
  | intro same
    have cell := congrArg (fun m : Machine => m.mem 9) same
    change w[0]=w[42] at cell
    exact (by decide : (w[0] : Evm.Word)≠w[42]) cell

private def words (m : Machine) := image.map fun cv => m.mem cv.1
private def physical (memory : Environment.Memory) := image.map fun cv => Environment.readMemory memory (32*cv.1) 32

/-- Complete ordered represented-word observations include the free pointer,
all fixed child cells (including max), both shared slots and the neighbour. -/
theorem complete_vectors :
    words machine=[w[32],w[7],w[0],Word.val (wmod (W-1)),w[2],w[8],w[8],w[8],w[9]] ∧
    words (writeMachine machine 9 w[42])=[w[32],w[7],w[42],Word.val (wmod (W-1)),w[2],w[8],w[8],w[8],w[9]] ∧
    physical bytes=image.map (fun cv => Semantics.wordBytes cv.2) ∧
    physical (Environment.writeBytes bytes 288 (Semantics.wordBytes 42))=
      image.map (fun cv => Semantics.wordBytes (if cv.1=9 then 42 else cv.2)) := by
  first
  | solve | simp only [] | omega
  | refine ⟨rfl,rfl,?_,?_⟩
    · apply List.map_congr_left
      intro cv hit
      exact image_read cv.1 cv.2 hit
    · apply List.map_congr_left
      intro cv hit
      rcases cv with ⟨c,v⟩
      by_cases selected : c=9
      · subst c
        rw [if_pos rfl]
        simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes 42) 288 bytes
      · rw [if_neg selected]
        have sep : 32*c+32≤288 ∨ 288+(Semantics.wordBytes 42).length≤32*c := by
          simp only [Environment.wordBytes_length]
          simp only [image,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hit
          rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega
        exact (readMemory_write_frame bytes (32*c) 32 288 (Semantics.wordBytes 42) sep).trans (image_read c v hit)

/-- info: 'Solidity.Backend.MemoryOps.Physical.FixedChildControls.complete_vectors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.FixedChildControls.headerless_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms headerless_write
/-- info: 'Solidity.Backend.MemoryOps.Physical.FixedChildControls.endpoint_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms endpoint_rejected
/-- info: 'Solidity.Backend.MemoryOps.Physical.FixedChildControls.wrong_dynamic_offset' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms wrong_dynamic_offset
private abbrev SA : Source.STy := .array .memory (.int .u256) (some 3)
private abbrev ΓR : Source.RCtx := [.int .u256,.int .u256,SA]
private abbrev SH := (Source.Heap.empty (D := E0.layout)).ty
private def si : Source.Idx ΓR (.int .u256) := .here
private def sv : Source.Idx ΓR (.int .u256) := .there .here
private def sr : Source.Idx ΓR SA := .there (.there .here)
private def yr (k : Nat) : Source.EMState E0 ΓR :=
  (.cons (sourceUint (u k)) (.cons (sourceUint (u 42)) (.cons (.memRef rfl 0) .nil)),y.2)
private def yFirst : Source.EMState E0 [] :=
  ((Source.allocRef (sourceUintFixedObject (hp.get child))).run (.nil,s0)).2
private theorem sourceR (k : Nat) : SourceUintFixedAt (yr k) 0 hp child := sourceAt
private theorem memOKR (k : Nat) : Source.MemOK E0 SH (yr k) := by
  have h0 : Source.MemOK E0 SH ((.nil,s0) : Source.EMState E0 []) :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have h1 := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (hp.get child) (.nil,s0) h0
  change Source.MemOK E0 SH yFirst ∧ _ at h1
  have h2 := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (hp.get neighbor) yFirst h1.1
  change Source.MemOK E0 SH y ∧ _ at h2
  exact ⟨⟨h2.1.1.1,⟨trivial,⟨trivial,⟨⟨SA,rfl,rfl⟩,trivial⟩⟩⟩⟩,h2.1.2⟩

/-- In both original pipelines, the actual resolved assignment and expression
statement use the SAME derived store output. Parameter count remains explicit. -/
theorem resolved_assignment (pipeline : Roadmap.Pipeline) (horizon nps : Nat) :
    ∃ (out : Heap H) (z : Source.EMState E0 ΓR) (logical offset : Fin W),
      logical.val=9 ∧ offset.val=288 ∧
      hp.writeAddr (.index child .fixed (indexValue (wmod 1))) (u 42)=some out ∧
      (Source.evalE (Source.SemanticsExamples.G0 pipeline) F0 (horizon+3)
        (sourceUintFixedIndexedAssign sr si sv)).run (yr 1)=(.ok (.val (sourceUint (u 42))),z) ∧
      (Source.execS (Source.SemanticsExamples.G0 pipeline) F0 (horizon+4) nps none
        (.expr (sourceUintFixedIndexedAssign sr si sv) : Source.RStmt E0 [] false .body ΓR ΓR) (yr 1).1).run (.nil,(yr 1).2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Evm.run [.mstoreAt] ((machine.push w[42]).push (.val logical))=.ok (writeMachine machine 9 w[42]) 0 ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset.val offset.isLt::lenU 42 (by decide)::tail,bytes⟩=
          some ⟨tail,Environment.writeBytes bytes 288 (Semantics.wordBytes 42)⟩) ∧
      ReferenceArrayAt out root base (writeMachine machine 9 w[42])
        (Environment.writeBytes bytes 288 (Semantics.wordBytes 42)) ∧
      SourceUintFixedAt z 0 out child ∧ Source.MemOK E0 SH z ∧ z.1=(yr 1).1 ∧
      z.2.ex=(yr 1).2.ex ∧ z.2.events=(yr 1).2.events ∧ z.2.logs=(yr 1).2.logs ∧ z.2.fnLocals=(yr 1).2.fnLocals ∧
      out.get neighbor=hp.get neighbor ∧
      z.2.heap.get 1=some ⟨.array .memory (.int .u256) (some 2),sourceUintFixedObject (hp.get neighbor)⟩ := by
  first
  | solve | simp only [] | omega
  | have slots : ∀ c,ReferenceSlots hp root base c → c≠9 := by
      intro c hc
      obtain ⟨i,hi,eq⟩ := hc
      change c=16+1+i at eq
      omega
    obtain ⟨out,z,logical,offset,loc,off,typed,run,expr,stmt,word,byte,parent,source,memOK,locals,objects,addresses,world,events,logs,fnLocals,frame⟩ :=
      parentAt.resolved_fixed_uint (sourceR 1) (Source.SemanticsExamples.G0 pipeline) F0 horizon nps
        sr si sv (wmod 1) (wmod 42) rfl rfl rfl (by decide) (by decide) (by decide) slots SH (memOKR 1)
    exact ⟨out,z,logical,offset,loc,off,typed,expr,stmt,word,byte,parent,source,memOK,locals,
      world,events,logs,fnLocals,objects neighbor (by decide),(addresses 1 (by decide)).trans sourceNeighbor⟩

/-- Swapping the operand locals really indexes42 and rejects before the write.
Zero evaluator horizon is a distinct timeout with its actual initial state. -/
theorem resolved_refusals (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.evalE (Source.SemanticsExamples.G0 pipeline) F0 (horizon+3)
      (sourceUintFixedIndexedAssign sr sv si)).run (yr 1)=
        (.error (.revert (Source.panicData .index)),yr 1) ∧
    (Source.evalE (Source.SemanticsExamples.G0 pipeline) F0 0
      (sourceUintFixedIndexedAssign sr si sv)).run (yr 1)=(.error .timeout,yr 1) := by
  first
  | solve | simp only [] | omega
  | exact ⟨(sourceR 1).eval_assign_bounds (Source.SemanticsExamples.G0 pipeline) F0 horizon sr sv si
      (u 42) (u 1) rfl rfl rfl (by decide),rfl⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.FixedChildControls.resolved_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_assignment
/-- info: 'Solidity.Backend.MemoryOps.Physical.FixedChildControls.resolved_refusals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_refusals

private def CArgs : Contract := {vars := []}
private abbrev ΔArgs : Ctx := [.val .uint,.val .uint,.mem A]
private def stateArgs : State CArgs ΔArgs := {storage := Storage.init CArgs,H := H,heap := hp,env := (u 1,u 42,some child,())}
private def mArgs : Machine := {machine with mem := fun a =>
  if a=1 then w[8] else if a=2 then w[42] else if a=3 then w[1] else machine.mem a}
private theorem refs {Q : RefTy} (q : HRef H Q) :
    (Q=P ∧ HEq q root) ∨ (Q=A ∧ HEq q child) ∨ (Q=N ∧ HEq q neighbor) := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi;exact .inl ⟨rfl,HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi;exact .inr (.inl ⟨rfl,HEq.rfl⟩)
    | succ i => cases i with
      | zero => cases hi;exact .inr (.inr ⟨rfl,HEq.rfl⟩)
      | succ i => cases hi
private theorem heapArgs : Objects.HeapRepr hp base 4 mArgs := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro Q q
    rcases refs q with ⟨rfl,hq⟩ | ⟨rfl,hq⟩ | ⟨rfl,hq⟩ <;> cases hq <;> decide
  · intro Q q
    rcases refs q with ⟨rfl,hq⟩ | ⟨rfl,hq⟩ | ⟨rfl,hq⟩ <;> cases hq
    all_goals simp only [Objects.cells,parentLength];decide
  · intro Q V q r hn
    rcases refs q with ⟨rfl,hq⟩ | ⟨rfl,hq⟩ | ⟨rfl,hq⟩ <;> cases hq
      <;> rcases refs r with ⟨rfl,hr⟩ | ⟨rfl,hr⟩ | ⟨rfl,hr⟩ <;> cases hr
      <;> first | exact (hn rfl).elim | (simp only [Objects.cells,parentLength];decide)
  · intro Q V a r
    rcases refs r with ⟨rfl,hr⟩ | ⟨rfl,hr⟩ | ⟨rfl,hr⟩ <;> cases hr <;> cases a
    all_goals
      refine ⟨?_,?_,?_⟩
      · simp only [Objects.cells,parentLength];decide
      · intro hh
        first | cases (by simpa only [Objects.header] using hh : (0 : Nat)=1)
              | (rw [parentLength];rfl)
      · intro i v hit
        first
        | rw [parentElements] at hit
          cases i with
          | zero => cases hit;rfl
          | succ i => cases i with
            | zero => cases hit;rfl
            | succ i => cases hit
        | rw [MObj.elems_fixed] at hit
          cases i with
          | zero => cases hit;exact ReprV.uint_of rfl
          | succ i => cases i with
            | zero => cases hit;exact ReprV.uint_of rfl
            | succ i => cases i with
              | zero => first | (cases hit;exact ReprV.uint_of rfl) | cases hit
              | succ i => cases hit
  · intro s r
    rcases refs r with ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ <;> cases eq
  · intro s f Q r hf
    rcases refs r with ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ <;> cases eq
private theorem reprArgs : Objects.StateRepr 1 1 4 (Frag.init ΔArgs) stateArgs base mArgs := by
  have hc := Sim.init CArgs 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,heapArgs,?_,by decide⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    · intro p i
      cases i with
      | here => exact ReprV.uint_of rfl
      | there i => cases i with
        | here => exact ReprV.uint_of rfl
        | there i => cases i with | there i => nomatch i
    · intro Q i hi
      cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro Q i hi
      cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · intro Q i
    cases i with | there i => cases i with | there i => cases i with
      | here => exact ⟨child,rfl,rfl⟩
      | there i => nomatch i
private theorem allocatorArgs : Objects.AllocatorRepr hp base 4 ⟨32,by decide⟩ mArgs := by
  refine ⟨heapArgs,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro a ha
    change 32≤a at ha
    simp only [mArgs,machine,if_neg (show a≠0 by omega),if_neg (show a≠1 by omega),
      if_neg (show a≠2 by omega),if_neg (show a≠3 by omega),if_neg (show a≠8 by omega),
      if_neg (show a≠10 by omega),if_neg (show a≠16 by omega),if_neg (show ¬(a=17 ∨ a=18) by omega),
      if_neg (show a≠24 by omega),if_neg (show a≠25 by omega)]
  · intro Q q
    rcases refs q with ⟨rfl,hq⟩ | ⟨rfl,hq⟩ | ⟨rfl,hq⟩ <;> cases hq
    all_goals simp only [Objects.cells,parentLength];decide
private theorem parentArgs : ReferenceArrayAt hp root base mArgs bytes := by
  refine ⟨(heapArgs.arrays .dyn root).reference,parentAt.headerFits,?_,parentAt.pointers.fits,?_⟩
  · exact ⟨wmod 2,rfl,image_read 16 2 (by decide)⟩
  · intro c hc
    obtain ⟨i,hi,eq⟩ := hc
    change c=16+1+i at eq
    have big : 17≤c := by omega
    obtain ⟨v,stored,fit,read⟩ := parentAt.pointers.cells c ⟨i,hi,eq⟩
    refine ⟨v,?_,fit,read⟩
    simp only [mArgs,if_neg (show c≠1 by omega),if_neg (show c≠2 by omega),if_neg (show c≠3 by omega)]
    exact stored

/-- A nonempty, shared-child strong input, including the actual allocator. -/
theorem strong_initial : Objects.StateRepr 1 1 4 (Frag.init ΔArgs) stateArgs base mArgs ∧
    Objects.AllocatorRepr hp base 4 ⟨32,by decide⟩ mArgs ∧
    ReferenceArrayAt hp root base mArgs bytes ∧ Source.MemOK E0 SH (yr 1) :=
  ⟨reprArgs,allocatorArgs,parentArgs,memOKR 1⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.FixedChildControls.strong_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms strong_initial

private def tri : Idx ΔArgs (.mem A) := .there (.there .here)
private def tii : Idx ΔArgs (.val .uint) := .here
private def tvi : Idx ΔArgs (.val .uint) := .there .here
private def assignCode : List Evm.Instr := compileVal 1 (.simple (.local tvi) : Val CArgs ΔArgs .uint) ++
  [.mload (cellOf 1 tri)] ++ compileVal 1 (.simple (.local tii) : Val CArgs ΔArgs .uint) ++
  Objects.writeCode (.fixed : ArrTy A (.prim .uint))

/-- Actual complete local-load/index/write word program, from inhabited strong
inputs. The terminal byte store is joined to its reached word parent/value. -/
theorem whole_word_write (pipeline : Roadmap.Pipeline) (horizon nps : Nat) :
    ∃ (out : Heap H) (z : Source.EMState E0 ΓR) (target : Machine) (offset : Fin W),
      offset.val=288 ∧
      (Source.evalE (Source.SemanticsExamples.G0 pipeline) F0 (horizon+3)
        (sourceUintFixedIndexedAssign sr si sv)).run (yr 1)=(.ok (.val (sourceUint (u 42))),z) ∧
      (Source.execS (Source.SemanticsExamples.G0 pipeline) F0 (horizon+4) nps none
        (.expr (sourceUintFixedIndexedAssign sr si sv) : Source.RStmt E0 [] false .body ΓR ΓR) (yr 1).1).run (.nil,(yr 1).2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run stateArgs (.assignMem (.index .fixed (.var tri rfl) (.simple (.local tii))) (.val (.simple (.local tvi))))=
        .ok ⟨stateArgs.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run assignCode mArgs=.ok target 0 ∧
      Objects.StateRepr 1 1 4 (Frag.init ΔArgs) (stateArgs.withHeap out) base target ∧
      Objects.AllocatorRepr out base 4 ⟨32,by decide⟩ target ∧
      ReferenceArrayAt out root base target (Environment.writeBytes bytes 288 (Semantics.wordBytes 42)) ∧
      CellAt target (Environment.writeBytes bytes 288 (Semantics.wordBytes 42)) 9 ∧
      SourceUintFixedAt z 0 out child ∧ Source.MemOK E0 SH z ∧ z.1=(yr 1).1 ∧ target.stack=[w[77],w[88]] ∧
      target.mem 0=w[32] ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset.val offset.isLt::lenU 42 (by decide)::tail,bytes⟩=
          some ⟨tail,Environment.writeBytes bytes 288 (Semantics.wordBytes 42)⟩) ∧
      out.get neighbor=hp.get neighbor ∧
      z.2.heap.get 1=some ⟨.array .memory (.int .u256) (some 2),sourceUintFixedObject (hp.get neighbor)⟩ ∧
      z.2.ex=(yr 1).2.ex ∧ z.2.events=(yr 1).2.events ∧ z.2.logs=(yr 1).2.logs ∧ z.2.fnLocals=(yr 1).2.fnLocals := by
  first
  | solve | simp only [] | omega
  | obtain ⟨out,z,target,offset,off,typed,expr,stmt,intrinsic,word,strong,allocator,parent,cell,source,memOK,locals,stack,byte,objects,addresses,world,events,logs,fnLocals⟩ :=
      resolved_fixed_parent_word (Source.SemanticsExamples.G0 pipeline) F0 horizon nps stateArgs child root
        (sourceR 1) sr si sv tri tii tvi (wmod 1) (wmod 42) rfl rfl rfl rfl rfl rfl (by decide)
        reprArgs bytes parentArgs (by decide) SH (memOKR 1) ⟨32,by decide⟩ (by decide) allocatorArgs
    exact ⟨out,z,target,offset,off,expr,stmt,intrinsic,word,strong,allocator,parent,cell,source,memOK,locals,stack,
      allocator.free.cell,byte,objects neighbor (by decide),(addresses 1 (by decide)).trans sourceNeighbor,world,events,logs,fnLocals⟩

private def badState := stateArgs.setLocal tii (u 3)
private def badMachine := writeMachine mArgs (cellOf 1 tii) w[3]
private theorem badRepr : Objects.StateRepr 1 1 4 (Frag.init ΔArgs) badState base badMachine :=
  reprArgs.setVal tii (u 3) w[3] (ReprV.uint_of rfl)

/-- Endpoint failure uses the real whole word guard, unlike terminal MSTORE.
Source exposes index panic/state; Evm.Out.revert exposes no suffix machine. -/
theorem whole_word_bounds (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.evalE (Source.SemanticsExamples.G0 pipeline) F0 (horizon+3)
      (sourceUintFixedIndexedAssign sr si sv)).run (yr 3)=
        (.error (.revert (Source.panicData .index)),yr 3) ∧
    Evm.run assignCode badMachine=.revert := by
  first
  | solve | simp only [] | omega
  | exact resolved_uint_fixed_assign_word_bounds (Source.SemanticsExamples.G0 pipeline) F0 horizon
      badState child (sourceR 3) sr si sv tri tii tvi (u 3) (u 42) rfl rfl rfl rfl rfl rfl (by decide) badRepr

/-- info: 'Solidity.Backend.MemoryOps.Physical.FixedChildControls.whole_word_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_word_write
/-- info: 'Solidity.Backend.MemoryOps.Physical.FixedChildControls.whole_word_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_word_bounds

end Solidity.Backend.MemoryOps.Physical.FixedChildControls
