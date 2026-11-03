import Solidity.Backend.MemoryOps.PhysicalArrayReframe
import Solidity.Backend.MemoryOps.PhysicalReferenceChild
import Solidity.Backend.MemoryOps.PhysicalMemoryControls

/-! Physical-memory assembly contracts and their proved clients. Each original
proposition is retained with its exact initial premises and complete ordered
observations. The companion proofs consume actual producer executions; none
assumes a contract as an oracle. These remain local symbolic-word/byte relations,
not whole Source transaction or external compiler/EVM adequacy. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- Observer glue target: retain the initial independent Source and
byte observations, replacing only the word machine by a derived representation
of the SAME reached object. Whole machine equality is intentionally absent. -/
def UintArrayReframeGoal {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (address : Nat) (hp : Heap H)
    (r : HRef H (.array (.prim .uint))) (base : Fin Evm.W)
    (left right : Evm.Machine) (bytes : Environment.Memory) : Prop :=
  UintArrayAt y address hp r base left bytes →
  Evm.Memory.ArrayRepr hp r base right →
  UintArrayAt y address hp r base right bytes

/-- Two real representations of the same typed object derive the reached
physical observation frame, without whole-machine equality. -/
theorem uint_array_reframe {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (address : Nat) (hp : Heap H)
    (r : HRef H (.array (.prim .uint))) (base : Fin Evm.W)
    (left right : Evm.Machine) (bytes : Environment.Memory) :
    UintArrayReframeGoal y address hp r base left right bytes := by
  intro initial words
  refine ⟨initial.source,words,initial.physical.fits,?_⟩
  intro c hc
  obtain ⟨w,hw,hb⟩ := initial.physical.cells c hc
  exact ⟨w,(uint_array_cells_eq words initial.words c hc).trans hw,hb⟩

/-- Assembly target, using only INITIAL local alignment, whole
published word-state/MemOK premises, and physical input representation. The
actual complete word delete program and reached byte relation are conclusions;
no successful output, target-machine equality or final agreement is assumed. -/
def ResolvedDeletePhysicalGoal {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (y : Source.EMState E Γ) (address : Nat) (G : Source.Glob E) (Fsrc : Source.Fr)
    (fuel nps : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none))
    (sindex : Source.Idx Γ (.int .u256))
    (troot : Idx Δ (.mem (.array (.prim .uint)))) (tindex : Idx Δ (.val .uint))
    (i : Fin Evm.W) (L b frame : Nat) (F : Evm.Frag Δ)
    (base : Nat → Fin Evm.W) (m : Evm.Machine) (bytes : Environment.Memory)
    (SH : Source.HeapTy) : Prop :=
  UintArrayAt y address σ.heap r (base r.id) m bytes →
  y.1.get sroot=.memRef rfl address →
  y.1.get sindex=sourceUint (Evm.Memory.indexValue i) →
  TEnv.get troot σ.env=some r →
  TEnv.get tindex σ.env=Evm.Memory.indexValue i →
  i.val<σ.heap.len r .dyn →
  Evm.Memory.StateRepr L b frame F σ base m →
  Source.MemOK E SH y →
  let byteNext := Environment.writeBytes bytes (32*((base r.id).val+1+i.val))
    (List.replicate 32 (0 : UInt8))
  ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
    (Source.evalE G Fsrc (fuel+3) (sourceUintIndexedDelete sroot sindex)).run y=
      (.ok Source.RVal.unit,z) ∧
    (Source.execS G Fsrc (fuel+4) nps none
      (.expr (sourceUintIndexedDelete sroot sindex) : Source.RStmt E [] false .body Γ Γ) y.1).run
        (.nil,y.2)=(.ok (.normal y.1),(.nil,z.2)) ∧
    Stmt.run σ (.deleteMem (.loc (.index .dyn (.var troot rfl) (.simple (.local tindex)))) rfl)=
      .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
    Evm.run (Evm.Memory.deleteLocalCode b troot
      (Evm.compileVal b (.simple (.local tindex) : Val C Δ .uint))) m=.ok target 0 ∧
    UintArrayAt z address out r (base r.id) target byteNext ∧
    Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
    Source.MemOK E SH z ∧ z.1=y.1 ∧ z.2={y.2 with heap:=z.2.heap} ∧
    target.stack=m.stack ∧
    Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target


/-- Assemble the actual physical and complete compiled-local deletion from the
same initial state. Successful execution identifies their reached heaps and
Source states; cell agreement transports the byte observations to the complete
word program, retaining the caller's original Source parameter count. -/
theorem resolved_delete_physical {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (y : Source.EMState E Γ) (address : Nat) (G : Source.Glob E) (Fsrc : Source.Fr)
    (fuel nps : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none))
    (sindex : Source.Idx Γ (.int .u256))
    (troot : Idx Δ (.mem (.array (.prim .uint)))) (tindex : Idx Δ (.val .uint))
    (i : Fin Evm.W) (L b frame : Nat) (F : Evm.Frag Δ)
    (base : Nat → Fin Evm.W) (m : Evm.Machine) (bytes : Environment.Memory)
    (SH : Source.HeapTy) :
    ResolvedDeletePhysicalGoal y address G Fsrc fuel nps σ r sroot sindex troot tindex
      i L b frame F base m bytes SH := by
  intro initial hsroot hsindex htroot htindex hi hm hmem
  dsimp only
  obtain ⟨out,z,ht,hd,he,hs,hw,hbyte,represented,hl,hstate,hother,hframe⟩ :=
    initial.delete_expression G Fsrc fuel nps sroot sindex i hsroot hsindex hi
  have hk : (Evm.Memory.indexValue i).1.toNat<σ.heap.len r .dyn := by
    simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hi
  obtain ⟨outW,zW,target,htW,hdW,heW,hsW,intrinsic,code,source,words,mem,locals,stack,alloc⟩ :=
    resolved_uint_delete_word G Fsrc fuel σ r initial.source sroot sindex troot tindex
      (Evm.Memory.indexValue i) hsroot hsindex htroot htindex hk hm SH hmem
  have heapEq : outW=out := Option.some.inj (htW.symm.trans ht)
  subst outW
  have sourceEq : zW=z := congrArg Prod.snd (heW.symm.trans he)
  subst zW
  have final : UintArrayAt z address out r (base r.id) target
      (Environment.writeBytes bytes (32*((base r.id).val+1+i.val))
        (List.replicate 32 (0 : UInt8))) :=
    uint_array_reframe z address out r (base r.id) _ target _ represented (words.heap.arrays r)
  exact ⟨out,z,target,he,hs,intrinsic,code,final,words,mem,hl,hstate,stack,alloc⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.resolved_delete_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_delete_physical


private abbrev Leaf : RefTy := .array (.prim .bool)
private abbrev Parent : RefTy := .array (.ref Leaf)
private abbrev HT : HTy := [Parent,Leaf,Leaf]
private def parent : HRef HT Parent := ⟨0,rfl⟩
private def left : HRef HT Leaf := ⟨1,rfl⟩
private def right : HRef HT Leaf := ⟨2,rfl⟩
private def heap : Heap HT :=
  (⟨[left,left],by decide⟩,⟨[true,false],by decide⟩,⟨[false],by decide⟩,())
private def bases (id : Nat) : Fin Evm.W :=
  if id=0 then Evm.wmod 16 else if id=1 then Evm.wmod 1 else Evm.wmod 8
private def machine : Evm.Machine :=
  { Evm.Machine.init with stack:=[.val (Evm.wmod 77),.val (Evm.wmod 88)], mem:=(fun a => if a=16 then .val (Evm.wmod 2) else if a=17 ∨ a=18 then .val (Evm.wmod 1) else if a=1 then .val (Evm.wmod 2) else if a=2 ∨ a=8 then .val (Evm.wmod 1) else .val (Evm.wmod 0)) }
private def bytes : Environment.Memory :=
  [(1,2),(2,1),(3,0),(8,1),(9,0),(16,2),(17,32),(18,32)].foldl
    (fun memory pair => Environment.writeBytes memory (32*pair.1) (Semantics.wordBytes pair.2))
    (fun _ => 0)
private def changed : Evm.Machine := Evm.Memory.writeMachine machine 17 (.val (Evm.wmod 8))
private def changedBytes : Environment.Memory := Environment.writeBytes bytes 544 (Semantics.wordBytes 256)
private def wordVector (m : Evm.Machine) := [1,2,3,8,9,16,17,18].map m.mem
private def byteVector (m : Environment.Memory) :=
  [32,64,96,256,288,512,544,576].map (fun a => Environment.readMemory m a 32)

/-- Client contract. It discriminates selected child
identity2, word address8 and physical byte address256; repeated old aliases and
both child contents remain explicit, with every header/data/pointer span. -/
def ReferenceStoreClientGoal : Prop :=
  ∃ out : Heap HT,
    heap.writeAddr (.index parent .dyn (Evm.Memory.indexValue (Evm.wmod 0))) right=some out ∧
    out.index parent .dyn (Evm.Memory.indexValue (Evm.wmod 0))=some right ∧
    out.index parent .dyn (Evm.Memory.indexValue (Evm.wmod 1))=some left ∧
    [(MObj.elems .dyn (heap.get parent)).map HRef.id,
      (MObj.elems .dyn (out.get parent)).map HRef.id]=[[1,1],[2,1]] ∧
    [MObj.elems .dyn (heap.get left),MObj.elems .dyn (heap.get right),
      MObj.elems .dyn (out.get left),MObj.elems .dyn (out.get right)]=
        [[true,false],[false],[true,false],[false]] ∧
    Evm.run (Evm.Memory.writeArrayCode (Evm.wmod 16))
      ((machine.push (.val (Evm.wmod 8))).push (.val (Evm.wmod 0)))=.ok changed 0 ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 544 (by decide)::lenU 256 (by decide)::[lenU 11 (by decide),lenU 22 (by decide)],bytes⟩=
        some ⟨[lenU 11 (by decide),lenU 22 (by decide)],changedBytes⟩ ∧
    [wordVector machine,wordVector changed]=
      [[.val (Evm.wmod 2),.val (Evm.wmod 1),.val (Evm.wmod 0),.val (Evm.wmod 1),
        .val (Evm.wmod 0),.val (Evm.wmod 2),.val (Evm.wmod 1),.val (Evm.wmod 1)],
       [.val (Evm.wmod 2),.val (Evm.wmod 1),.val (Evm.wmod 0),.val (Evm.wmod 1),
        .val (Evm.wmod 0),.val (Evm.wmod 2),.val (Evm.wmod 8),.val (Evm.wmod 1)]] ∧
    [byteVector bytes,byteVector changedBytes]=
      [[2,1,0,1,0,2,32,32].map Semantics.wordBytes,
       [2,1,0,1,0,2,256,32].map Semantics.wordBytes] ∧
    changed.stack=[.val (Evm.wmod 77),.val (Evm.wmod 88)] ∧
    Semantics.wordBytes 8≠Semantics.wordBytes 256



private theorem parent_length : heap.len parent .dyn=2 := by
  simp only [Heap.len,MObj.elems_dyn]
  rfl

private theorem byte_word_read (memory : Environment.Memory) (a w : Nat) :
    Environment.readMemory (Environment.writeBytes memory a (Semantics.wordBytes w)) a 32=
      Semantics.wordBytes w := by
  simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes w) a memory

/-- Execute the producer on the actual shared-child fixture, with all ordered
initial/reached observations retained by the original target. -/
theorem reference_store_client : ReferenceStoreClientGoal := by
  have hi : (Evm.wmod 0).val<heap.len parent .dyn := by rw [parent_length];decide
  obtain ⟨out,ht,hw,hb,_read,_exterior,_frame⟩ :=
    reference_store heap parent right bases machine bytes (Evm.wmod 0)
      hi (by rw [parent_length];rfl) (by decide) (by decide)
  have concrete : out=heap.set parent (MObj.setElem .dyn (heap.get parent) 0 right) := by
    have actual : heap.writeAddr (.index parent .dyn (Evm.Memory.indexValue (Evm.wmod 0))) right=
        some (heap.set parent (MObj.setElem .dyn (heap.get parent) 0 right)) := by
      change (if (Evm.wmod 0).val<heap.len parent .dyn then some _ else none)=_
      simp only [hi,↓reduceIte,Evm.Memory.indexValue,Int.toNat_natCast]
      rfl
    exact Option.some.inj (ht.symm.trans actual)
  subst out
  refine ⟨_,ht,?_,?_,?_,?_,hw,?_,?_,?_,rfl,pointer_eight_not_numeric⟩
  · simp only [Heap.index,Evm.Memory.indexValue,Int.toNat_natCast,
      Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn]
    rfl
  · simp only [Heap.index,Evm.Memory.indexValue,Int.toNat_natCast,
      Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn]
    rfl
  · simp only [Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn]
    rfl
  · rw [Heap.get_set_ne heap parent left (by decide),
      Heap.get_set_ne heap parent right (by decide)]
    simp only [MObj.elems_dyn]
    rfl
  · obtain ⟨offset,hoff,run⟩ := hb
    have same : offset=(⟨544,by decide⟩ : Fin Evm.W) := Fin.ext hoff
    subst offset
    exact run [lenU 11 (by decide),lenU 22 (by decide)]
  · decide
  · simp only [byteVector,List.map_cons,List.map_nil,List.cons.injEq,and_true]
    repeat' apply And.intro
    all_goals
      simp only [bytes,changedBytes,List.foldl_cons,List.foldl_nil]
      repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length]; omega)
      exact byte_word_read _ _ _

/-- The same actual operation has nonempty initial pointer and numeric
footprints. The full client observations are linked to its SAME typed output
by successful-write uniqueness, not an independent or assumed final relation. -/
theorem reference_store_frames_client :
    ∃ out : Heap HT,
      heap.writeAddr (.index parent .dyn (Evm.Memory.indexValue (Evm.wmod 0))) right=some out ∧
      Evm.run (Evm.Memory.writeArrayCode (Evm.wmod 16))
        ((machine.push (.val (Evm.wmod 8))).push (.val (Evm.wmod 0)))=.ok changed 0 ∧
      (∃ offset : Fin Evm.W,offset.val=544 ∧ ∀ tail : List Environment.Word,
        Environment.cryptoStep (.op .MSTORE)
          ⟨lenU offset.val offset.isLt::lenU 256 (by decide)::tail,bytes⟩=
            some ⟨tail,changedBytes⟩) ∧
      PointerFrame changed changedBytes (fun c => c=17 ∨ c=18) ∧
      WordFrame changed changedBytes (fun c => c=16 ∨ c=9) ∧
      out.get left=heap.get left ∧ out.get right=heap.get right ∧
      ReferenceStoreClientGoal := by
  obtain ⟨observed,observedWrite,observations⟩ := reference_store_client
  have complete : ReferenceStoreClientGoal := ⟨observed,observedWrite,observations⟩
  obtain ⟨_,_,_,_,_,_,_,_,_,vectors,_,_⟩ := complete
  have reads : byteVector bytes=[2,1,0,1,0,2,32,32].map Semantics.wordBytes :=
    (List.cons.inj vectors).1
  have pointers : PointerFrame machine bytes (fun c => c=17 ∨ c=18) := by
    constructor
    · intro c hc
      rcases hc with rfl | rfl <;> decide
    · intro c hc
      rcases hc with rfl | rfl
      · refine ⟨Evm.wmod 1,rfl,by decide,?_⟩
        have he := congrArg (fun xs : List (List UInt8) => xs[6]?) reads
        change some (Environment.readMemory bytes 544 32)=some (Semantics.wordBytes 32) at he
        exact Option.some.inj he
      · refine ⟨Evm.wmod 1,rfl,by decide,?_⟩
        have he := congrArg (fun xs : List (List UInt8) => xs[7]?) reads
        change some (Environment.readMemory bytes 576 32)=some (Semantics.wordBytes 32) at he
        exact Option.some.inj he
  have numbers : WordFrame machine bytes (fun c => c=16 ∨ c=9) := by
    constructor
    · intro c hc
      rcases hc with rfl | rfl <;> decide
    · intro c hc
      rcases hc with rfl | rfl
      · refine ⟨Evm.wmod 2,rfl,?_⟩
        have he := congrArg (fun xs : List (List UInt8) => xs[5]?) reads
        change some (Environment.readMemory bytes 512 32)=some (Semantics.wordBytes 2) at he
        exact Option.some.inj he
      · refine ⟨Evm.wmod 0,rfl,?_⟩
        have he := congrArg (fun xs : List (List UInt8) => xs[4]?) reads
        change some (Environment.readMemory bytes 288 32)=some (Semantics.wordBytes 0) at he
        exact Option.some.inj he
  have hi : (Evm.wmod 0).val<heap.len parent .dyn := by rw [parent_length];decide
  obtain ⟨out,ht,hw,hb,hp,hn,hframe⟩ := reference_store_frames heap parent right bases machine bytes
    (Evm.wmod 0) hi (by rw [parent_length];rfl) (by decide) (by decide)
    (fun c => c=17 ∨ c=18) (fun c => c=16 ∨ c=9) pointers numbers
    (by intro c hc;rcases hc with rfl | rfl <;> decide)
  have same : observed=out := Option.some.inj (observedWrite.symm.trans ht)
  subst observed
  refine ⟨out,ht,hw,hb,?_,hn,hframe left (by decide),hframe right (by decide),out,observedWrite,observations⟩
  exact ⟨fun c hc => hp.fits c (.inl hc),fun c hc => hp.cells c (.inl hc)⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.reference_store_frames_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reference_store_frames_client

/-- info: 'Solidity.Backend.MemoryOps.Physical.reference_store_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reference_store_client

/-- Alias client contract: establish a repeated-pointer footprint
at slots17/18, then redirect17 from logical1 to8. Every selected/retained word
and byte span is explicit; initial arbitrary exterior memory is not zeroed. -/
def PointerFrameAliasClientGoal : Prop :=
  ∀ (m : Evm.Machine) (bytes : Environment.Memory),
  let old := Evm.Memory.writeMachine
    (Evm.Memory.writeMachine m 18 (.val (Evm.wmod 1))) 17 (.val (Evm.wmod 1))
  let oldBytes := Environment.writeBytes
    (Environment.writeBytes bytes 576 (Semantics.wordBytes 32))
    544 (Semantics.wordBytes 32)
  let next := Evm.Memory.writeMachine old 17 (.val (Evm.wmod 8))
  let nextBytes := Environment.writeBytes oldBytes 544 (Semantics.wordBytes 256)
  PointerFrame old oldBytes (fun c => c=17 ∨ c=18) ∧
  PointerFrame next nextBytes (fun c => c=17 ∨ c=18) ∧
  [old.mem 17,old.mem 18,next.mem 17,next.mem 18]=
    [.val (Evm.wmod 1),.val (Evm.wmod 1),.val (Evm.wmod 8),.val (Evm.wmod 1)] ∧
  [Environment.readMemory oldBytes 544 32,Environment.readMemory oldBytes 576 32,
    Environment.readMemory nextBytes 544 32,Environment.readMemory nextBytes 576 32]=
    [Semantics.wordBytes 32,Semantics.wordBytes 32,
      Semantics.wordBytes 256,Semantics.wordBytes 32]



private theorem restrict_pointer_frame {m : Evm.Machine} {data : Environment.Memory}
    {large small : Nat → Prop} (frame : PointerFrame m data large)
    (included : ∀ c, small c → large c) : PointerFrame m data small :=
  ⟨fun c hc => frame.fits c (included c hc),fun c hc => frame.cells c (included c hc)⟩

/-- Actual writes establish and then update nonempty alias footprints for
arbitrary original memory; no initial-zero or final-frame premise is used. -/
theorem pointer_frame_alias_client : PointerFrameAliasClientGoal := by
  intro input data
  dsimp only
  let first := Evm.Memory.writeMachine input 18 (.val (Evm.wmod 1))
  let firstBytes := Environment.writeBytes data 576 (Semantics.wordBytes 32)
  let old := Evm.Memory.writeMachine first 17 (.val (Evm.wmod 1))
  let oldBytes := Environment.writeBytes firstBytes 544 (Semantics.wordBytes 32)
  let next := Evm.Memory.writeMachine old 17 (.val (Evm.wmod 8))
  let nextBytes := Environment.writeBytes oldBytes 544 (Semantics.wordBytes 256)
  have empty : PointerFrame input data (fun _ => False) :=
    ⟨fun _ h => h.elim,fun _ h => h.elim⟩
  have f18 : PointerFrame first firstBytes (fun c => False ∨ c=18) :=
    empty.write 18 (Evm.wmod 1) (by decide) (by decide)
  have f17 : PointerFrame old oldBytes (fun c => (False ∨ c=18) ∨ c=17) :=
    f18.write 17 (Evm.wmod 1) (by decide) (by decide)
  have oldFrame : PointerFrame old oldBytes (fun c => c=17 ∨ c=18) :=
    restrict_pointer_frame f17 (by
      intro c hc
      rcases hc with hc | hc
      · exact .inr hc
      · exact .inl (.inr hc))
  have nextFull : PointerFrame next nextBytes (fun c => (c=17 ∨ c=18) ∨ c=17) :=
    oldFrame.write 17 (Evm.wmod 8) (by decide) (by decide)
  have nextFrame : PointerFrame next nextBytes (fun c => c=17 ∨ c=18) :=
    restrict_pointer_frame nextFull (fun _ hc => .inl hc)
  have old17 : Environment.readMemory oldBytes 544 32=Semantics.wordBytes 32 :=
    byte_word_read firstBytes 544 32
  have old18 : Environment.readMemory oldBytes 576 32=Semantics.wordBytes 32 := by
    rw [readMemory_write_frame firstBytes 576 32 544 _ (Or.inr (by rw [Environment.wordBytes_length];decide))]
    exact byte_word_read data 576 32
  have next17 : Environment.readMemory nextBytes 544 32=Semantics.wordBytes 256 :=
    byte_word_read oldBytes 544 256
  have next18 : Environment.readMemory nextBytes 576 32=Semantics.wordBytes 32 := by
    rw [readMemory_write_frame oldBytes 576 32 544 _ (Or.inr (by rw [Environment.wordBytes_length];decide))]
    exact old18
  refine ⟨oldFrame,nextFrame,?_,?_⟩
  · rfl
  · change [Environment.readMemory oldBytes 544 32,Environment.readMemory oldBytes 576 32,
        Environment.readMemory nextBytes 544 32,Environment.readMemory nextBytes 576 32]=
        [Semantics.wordBytes 32,Semantics.wordBytes 32,Semantics.wordBytes 256,Semantics.wordBytes 32]
    rw [old17,old18,next17,next18]

/-- info: 'Solidity.Backend.MemoryOps.Physical.pointer_frame_alias_client' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pointer_frame_alias_client

/-- Primitive child assembly contract. Derive the actual typed child-write
output from the published primitive certificate, then apply set_primitive; use
INITIAL numeric frame bounds for actual MSTORE. No successful run/output or
reached representation is a premise. The following companion proves this contract. -/
def PrimitiveChildStoreGoal : Prop :=
  ∀ {H : HTy} {R : RefTy} {p : PrimTy} {hp : Heap H}
  {root : HRef H (.array (.ref R))} {base : Nat → Fin Evm.W}
  {m : Evm.Machine} {bytes : Environment.Memory},
  ReferenceArrayAt hp root base m bytes →
  ∀ (child : HRef H (.array (.prim p))),
  Evm.Memory.ArrayRepr hp child (base child.id) m →
  WordFrame m bytes (fun c => (base child.id).val≤c ∧
    c<(base child.id).val+1+hp.len child .dyn) →
  ∀ (i w : Fin Evm.W) (v : p.Denote), i.val<hp.len child .dyn →
  Evm.ReprV p v (.val w) →
  (base root.id).val≠(base child.id).val+1+i.val →
  (∀ c, ReferenceSlots hp root base c → c≠(base child.id).val+1+i.val) →
  let cell := (base child.id).val+1+i.val
  let next := Evm.Memory.writeMachine m cell (.val w)
  let byteNext := Environment.writeBytes bytes (32*cell) (Semantics.wordBytes w.val)
  ∃ out : Heap H,
    hp.writeAddr (.index child .dyn (Evm.Memory.indexValue i)) v=some out ∧
    Evm.run (Evm.Memory.writeArrayCode (base child.id))
      ((m.push (.val w)).push (.val i))=.ok next 0 ∧
    (∃ offset : Fin Evm.W,offset.val=32*cell ∧ ∀ tail : List Environment.Word,
      Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset.val offset.isLt::lenU w.val w.isLt::tail,bytes⟩=
          some ⟨tail,byteNext⟩) ∧
    Evm.Memory.ArrayRepr out child (base child.id) next ∧
    WordFrame next byteNext (fun c => (base child.id).val≤c ∧
      c<(base child.id).val+1+out.len child .dyn) ∧
    ReferenceArrayAt out root base next byteNext ∧
    out.get root=hp.get root



/-- Actual primitive execution and both reached object relations follow
from the original alignment, bounds and separated physical footprints. -/
theorem primitive_child_store : PrimitiveChildStoreGoal := by
  intro H R p hp root base m data hparent child words physical i w v hi hv headerNe slotsNe
  dsimp only
  have actual : hp.writeAddr (.index child .dyn (Evm.Memory.indexValue i)) v=
      some (hp.set child (MObj.setElem .dyn (hp.get child) i.val v)) := by
    have bound : i.val<(MObj.elems .dyn (hp.get child)).length := hi
    simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast,bound,↓reduceIte]
  rcases Evm.Memory.writeArray_correct words i v (.val w) hv with
    ⟨out,ht,hw,represented⟩ | ⟨bad,_⟩
  · have same : out=hp.set child (MObj.setElem .dyn (hp.get child) i.val v) :=
      Option.some.inj (ht.symm.trans actual)
    subst out
    have length : (hp.set child (MObj.setElem .dyn (hp.get child) i.val v)).len child .dyn=
        hp.len child .dyn := by
      simp only [Heap.len,Heap.get_set_same,MObj.elems_setElem,List.length_set]
    let cell := (base child.id).val+1+i.val
    have fits : 32*cell+32≤2^256 := physical.fits cell ⟨by dsimp only [cell];omega,by dsimp only [cell];omega⟩
    have logical : cell<Evm.W := by change cell<2^256;omega
    have reached := physical.write cell w fits
    have final : WordFrame (Evm.Memory.writeMachine m cell (.val w))
        (Environment.writeBytes data (32*cell) (Semantics.wordBytes w.val))
        (fun c => (base child.id).val≤c ∧ c<(base child.id).val+1+
          (hp.set child (MObj.setElem .dyn (hp.get child) i.val v)).len child .dyn) := by
      constructor
      · intro c hc
        exact reached.fits c (.inl (by simpa only [length] using hc))
      · intro c hc
        exact reached.cells c (.inl (by simpa only [length] using hc))
    have distinct : child.id≠root.id := by
      intro same
      cases (HRef.heq_of_id child root same).1
    refine ⟨_,ht,hw,?_,represented,final,
      hparent.set_primitive child i.val v w headerNe slotsNe,
      Heap.get_set_ne hp child root distinct _⟩
    refine ⟨⟨32*cell,by change 32*cell<2^256;omega⟩,rfl,?_⟩
    intro tail
    exact byte_mstore data tail ⟨cell,logical⟩ w fits
  · rw [actual] at bad
    cases bad

/-- info: 'Solidity.Backend.MemoryOps.Physical.primitive_child_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms primitive_child_store

private abbrev ClientLeaf : RefTy := .array (.prim .bool)
private abbrev ClientParent : RefTy := .array (.ref ClientLeaf)
private abbrev ClientHT : HTy := [ClientParent,ClientLeaf,ClientLeaf]
private def clientRoot : HRef ClientHT ClientParent := ⟨0,rfl⟩
private def clientLeft : HRef ClientHT ClientLeaf := ⟨1,rfl⟩
private def clientRight : HRef ClientHT ClientLeaf := ⟨2,rfl⟩
private def clientHeap : Heap ClientHT :=
  (⟨[clientLeft,clientLeft],by decide⟩,⟨[true,false],by decide⟩,⟨[false],by decide⟩,())
private def clientBase (id : Nat) : Fin Evm.W :=
  if id=0 then Evm.wmod 16 else if id=1 then Evm.wmod 1 else Evm.wmod 8
private def clientMachine : Evm.Machine :=
  { Evm.Machine.init with stack:=[.val (Evm.wmod 77)], mem:=(fun a => if a=16 then .val (Evm.wmod 2) else if a=17 ∨ a=18 then .val (Evm.wmod 1) else .val (Evm.wmod 0)) }
private def clientBytes : Environment.Memory :=
  [(16,2),(17,32),(18,32)].foldl
    (fun memory pair => Environment.writeBytes memory (32*pair.1) (Semantics.wordBytes pair.2))
    (fun _ => 0)

/-- Populated reference-array client contract. The initial relation itself must be proved from
the concrete independently typed heap and actual word/byte contents, then the
store law derives the reached parent and typed-child bytes. No client proof or
represented child contents are assumed or claimed by this definition. -/
def ReferenceArrayClientGoal : Prop :=
  ReferenceArrayAt clientHeap clientRoot clientBase clientMachine clientBytes ∧
  ∃ out : Heap ClientHT,
    clientHeap.writeAddr (.index clientRoot .dyn (Evm.Memory.indexValue (Evm.wmod 0))) clientRight=some out ∧
    let next := Evm.Memory.writeMachine clientMachine 17 (.val (Evm.wmod 8))
    let nextBytes := Environment.writeBytes clientBytes 544 (Semantics.wordBytes 256)
    ReferenceArrayAt out clientRoot clientBase next nextBytes ∧
    (MObj.elems .dyn (out.get clientRoot)).map HRef.id=[2,1] ∧
    [MObj.elems .dyn (out.get clientLeft),MObj.elems .dyn (out.get clientRight)]=
      [[true,false],[false]] ∧
    [next.mem 16,next.mem 17,next.mem 18]=
      [.val (Evm.wmod 2),.val (Evm.wmod 8),.val (Evm.wmod 1)] ∧
    [Environment.readMemory nextBytes 512 32,Environment.readMemory nextBytes 544 32,
      Environment.readMemory nextBytes 576 32]=
      [Semantics.wordBytes 2,Semantics.wordBytes 256,Semantics.wordBytes 32] ∧
    next.stack=[.val (Evm.wmod 77)]


private theorem client_parent_elements : MObj.elems .dyn (clientHeap.get clientRoot)=
    [clientLeft,clientLeft] := by
  simp only [MObj.elems_dyn]
  rfl

private theorem client_parent_length : clientHeap.len clientRoot .dyn=2 := by
  simp only [Heap.len,client_parent_elements]
  rfl

private theorem client_initial : ReferenceArrayAt clientHeap clientRoot clientBase clientMachine clientBytes := by
  constructor
  · constructor
    · rw [client_parent_length]
      decide
    · rw [client_parent_length]
      rfl
    · intro i v hv
      rw [client_parent_elements] at hv
      cases i with
      | zero => cases hv;rfl
      | succ i => cases i with
        | zero => cases hv;rfl
        | succ i => cases hv
  · decide
  · refine ⟨Evm.wmod 2,rfl,?_⟩
    change Environment.readMemory clientBytes 512 32=Semantics.wordBytes 2
    simp only [clientBytes,List.foldl_cons,List.foldl_nil]
    repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length]; omega)
    exact byte_word_read _ _ _
  · constructor
    · intro c hc
      obtain ⟨i,hi,he⟩ := hc
      rw [client_parent_length] at hi
      change c=16+1+i at he
      omega
    · intro c hc
      obtain ⟨i,hi,he⟩ := hc
      rw [client_parent_length] at hi
      have which : i=0 ∨ i=1 := by omega
      rcases which with rfl | rfl
      · subst c
        refine ⟨Evm.wmod 1,rfl,by decide,?_⟩
        change Environment.readMemory clientBytes 544 32=Semantics.wordBytes 32
        simp only [clientBytes,List.foldl_cons,List.foldl_nil]
        repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length]; omega)
        exact byte_word_read _ _ _
      · subst c
        refine ⟨Evm.wmod 1,rfl,by decide,?_⟩
        change Environment.readMemory clientBytes 576 32=Semantics.wordBytes 32
        simp only [clientBytes,List.foldl_cons,List.foldl_nil]
        exact byte_word_read _ _ _

/-- Independently establish the actual initial parent, then execute the real
redirection. Typed aliases, children, header, all pointer spans and stack remain
exactly those in the original complete target. -/
theorem reference_array_client : ReferenceArrayClientGoal := by
  have hi : (Evm.wmod 0).val<clientHeap.len clientRoot .dyn := by rw [client_parent_length];decide
  obtain ⟨out,ht,_word,_byte,represented,_frame⟩ :=
    client_initial.store (Evm.wmod 0) hi clientRight (by decide)
  have concrete : out=clientHeap.set clientRoot (MObj.setElem .dyn (clientHeap.get clientRoot) 0 clientRight) := by
    have actual : clientHeap.writeAddr (.index clientRoot .dyn (Evm.Memory.indexValue (Evm.wmod 0))) clientRight=
        some (clientHeap.set clientRoot (MObj.setElem .dyn (clientHeap.get clientRoot) 0 clientRight)) := by
      change (if (Evm.wmod 0).val<clientHeap.len clientRoot .dyn then some _ else none)=_
      simp only [hi,↓reduceIte,Evm.Memory.indexValue,Int.toNat_natCast]
      rfl
    exact Option.some.inj (ht.symm.trans actual)
  subst out
  refine ⟨client_initial,_,ht,represented,?_,?_,?_,?_,rfl⟩
  · simp only [Heap.get_set_same,MObj.elems_setElem,client_parent_elements]
    rfl
  · rw [Heap.get_set_ne clientHeap clientRoot clientLeft (by decide),
      Heap.get_set_ne clientHeap clientRoot clientRight (by decide)]
    simp only [MObj.elems_dyn]
    rfl
  · decide
  · simp only [List.cons.injEq,and_true]
    repeat' apply And.intro
    all_goals
      simp only [clientBytes,List.foldl_cons,List.foldl_nil]
      repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length]; omega)
      exact byte_word_read _ _ _

/-- info: 'Solidity.Backend.MemoryOps.Physical.reference_array_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reference_array_client

private theorem parent_elements : MObj.elems .dyn (heap.get parent)=[left,left] := by
  simp only [MObj.elems_dyn]
  rfl

private theorem populated_parent : ReferenceArrayAt heap parent bases machine bytes := by
  constructor
  · constructor
    · rw [parent_length]
      decide
    · rw [parent_length]
      rfl
    · intro i v hv
      rw [parent_elements] at hv
      cases i with
      | zero => cases hv;rfl
      | succ i => cases i with
        | zero => cases hv;rfl
        | succ i => cases hv
  · decide
  · refine ⟨Evm.wmod 2,rfl,?_⟩
    change Environment.readMemory bytes 512 32=Semantics.wordBytes 2
    simp only [bytes,List.foldl_cons,List.foldl_nil]
    repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length]; omega)
    exact byte_word_read _ _ _
  · constructor
    · intro c hc
      obtain ⟨i,hi,he⟩ := hc
      rw [parent_length] at hi
      change c=16+1+i at he
      omega
    · intro c hc
      obtain ⟨i,hi,he⟩ := hc
      rw [parent_length] at hi
      have which : i=0 ∨ i=1 := by omega
      rcases which with rfl | rfl
      · subst c
        refine ⟨Evm.wmod 1,rfl,by decide,?_⟩
        change Environment.readMemory bytes 544 32=Semantics.wordBytes 32
        simp only [bytes,List.foldl_cons,List.foldl_nil]
        repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length]; omega)
        exact byte_word_read _ _ _
      · subst c
        refine ⟨Evm.wmod 1,rfl,by decide,?_⟩
        change Environment.readMemory bytes 576 32=Semantics.wordBytes 32
        simp only [bytes,List.foldl_cons,List.foldl_nil]
        exact byte_word_read _ _ _

private theorem left_length : heap.len left .dyn=2 := by
  simp only [Heap.len,MObj.elems_dyn]
  rfl

private theorem populated_child : Evm.Memory.ArrayRepr heap left (bases left.id) machine := by
  constructor
  · rw [left_length]
    decide
  · rw [left_length]
    rfl
  · intro i v hv
    simp only [MObj.elems_dyn] at hv
    cases i with
    | zero => cases hv;rfl
    | succ i => cases i with
      | zero => cases hv;rfl
      | succ i => cases hv

private theorem populated_child_bytes : WordFrame machine bytes
    (fun c => (bases left.id).val≤c ∧ c<(bases left.id).val+1+heap.len left .dyn) := by
  constructor
  · intro c hc
    rw [left_length] at hc
    change 1≤c ∧ c<4 at hc
    omega
  · intro c hc
    rw [left_length] at hc
    change 1≤c ∧ c<4 at hc
    have which : c=1 ∨ c=2 ∨ c=3 := by omega
    rcases which with rfl | rfl | rfl
    all_goals
      first | refine ⟨Evm.wmod 2,rfl,?_⟩ | refine ⟨Evm.wmod 1,rfl,?_⟩ | refine ⟨Evm.wmod 0,rfl,?_⟩
      simp only [bytes,List.foldl_cons,List.foldl_nil]
      repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length]; omega)
      exact byte_word_read _ _ _

private def primitiveNext : Evm.Machine := Evm.Memory.writeMachine machine 2 (.val (Evm.wmod 0))
private def primitiveBytes : Environment.Memory := Environment.writeBytes bytes 64 (Semantics.wordBytes 0)

/-- A nonvacuous application of the complete primitive-child contract.
Both parent entries alias the changing child; all initial relations are proved
from the actual objects/word/byte contents, not supplied as premises. The
separate child, every parent pointer, and complete ordered observations remain. -/
theorem primitive_child_store_client :
    ReferenceArrayAt heap parent bases machine bytes ∧
    Evm.Memory.ArrayRepr heap left (bases left.id) machine ∧
    WordFrame machine bytes (fun c => (bases left.id).val≤c ∧
      c<(bases left.id).val+1+heap.len left .dyn) ∧
    ∃ out : Heap HT,
      heap.writeAddr (.index left .dyn (Evm.Memory.indexValue (Evm.wmod 0))) false=some out ∧
      Evm.run (Evm.Memory.writeArrayCode (bases left.id))
        ((machine.push (.val (Evm.wmod 0))).push (.val (Evm.wmod 0)))=.ok primitiveNext 0 ∧
      Environment.cryptoStep (.op .MSTORE)
        ⟨lenU 64 (by decide)::lenU 0 (by decide)::[lenU 11 (by decide),lenU 22 (by decide)],bytes⟩=
          some ⟨[lenU 11 (by decide),lenU 22 (by decide)],primitiveBytes⟩ ∧
      Evm.Memory.ArrayRepr out left (bases left.id) primitiveNext ∧
      WordFrame primitiveNext primitiveBytes (fun c => (bases left.id).val≤c ∧
        c<(bases left.id).val+1+out.len left .dyn) ∧
      ReferenceArrayAt out parent bases primitiveNext primitiveBytes ∧ out.get parent=heap.get parent ∧
      [(MObj.elems .dyn (heap.get parent)).map HRef.id,(MObj.elems .dyn (out.get parent)).map HRef.id]=
        [[1,1],[1,1]] ∧
      [MObj.elems .dyn (heap.get left),MObj.elems .dyn (heap.get right),
        MObj.elems .dyn (out.get left),MObj.elems .dyn (out.get right)]=
          [[true,false],[false],[false,false],[false]] ∧
      [(out.index parent .dyn (Evm.Memory.indexValue (Evm.wmod 0))).bind
          (fun child => out.index child .dyn (Evm.Memory.indexValue (Evm.wmod 0))),
        (out.index parent .dyn (Evm.Memory.indexValue (Evm.wmod 1))).bind
          (fun child => out.index child .dyn (Evm.Memory.indexValue (Evm.wmod 0)))]=
            [some false,some false] ∧
      [wordVector machine,wordVector primitiveNext]=
        [[.val (Evm.wmod 2),.val (Evm.wmod 1),.val (Evm.wmod 0),.val (Evm.wmod 1),
          .val (Evm.wmod 0),.val (Evm.wmod 2),.val (Evm.wmod 1),.val (Evm.wmod 1)],
         [.val (Evm.wmod 2),.val (Evm.wmod 0),.val (Evm.wmod 0),.val (Evm.wmod 1),
          .val (Evm.wmod 0),.val (Evm.wmod 2),.val (Evm.wmod 1),.val (Evm.wmod 1)]] ∧
      [byteVector bytes,byteVector primitiveBytes]=
        [[2,1,0,1,0,2,32,32].map Semantics.wordBytes,
         [2,0,0,1,0,2,32,32].map Semantics.wordBytes] ∧
      primitiveNext.stack=[.val (Evm.wmod 77),.val (Evm.wmod 88)] := by
  have hi : (Evm.wmod 0).val<heap.len left .dyn := by rw [left_length];decide
  have separate : ∀ c,ReferenceSlots heap parent bases c →
      c≠(bases left.id).val+1+(Evm.wmod 0).val := by
    intro c hc
    obtain ⟨j,hj,he⟩ := hc
    rw [parent_length] at hj
    change c=16+1+j at he
    change c≠2
    omega
  obtain ⟨out,ht,hw,hb,words,physical,rootFrame,unchanged⟩ :=
    primitive_child_store populated_parent left populated_child populated_child_bytes
      (Evm.wmod 0) (Evm.wmod 0) false hi rfl (by decide) separate
  have concrete : out=heap.set left (MObj.setElem .dyn (heap.get left) 0 false) := by
    have actual : heap.writeAddr (.index left .dyn (Evm.Memory.indexValue (Evm.wmod 0))) false=
        some (heap.set left (MObj.setElem .dyn (heap.get left) 0 false)) := by
      change (if (Evm.wmod 0).val<heap.len left .dyn then some _ else none)=_
      simp only [hi,↓reduceIte,Evm.Memory.indexValue,Int.toNat_natCast]
      rfl
    exact Option.some.inj (ht.symm.trans actual)
  subst out
  refine ⟨populated_parent,populated_child,populated_child_bytes,_,ht,hw,?_,words,physical,
    rootFrame,unchanged,?_,?_,?_,?_,?_,rfl⟩
  · obtain ⟨offset,hoff,run⟩ := hb
    have same : offset=(⟨64,by decide⟩ : Fin Evm.W) := Fin.ext hoff
    subst offset
    exact run [lenU 11 (by decide),lenU 22 (by decide)]
  · rw [unchanged]
    simp only [MObj.elems_dyn]
    rfl
  · rw [Heap.get_set_same,Heap.get_set_ne heap left right (by decide)]
    simp only [MObj.elems_setElem,MObj.elems_dyn]
    rfl
  · simp only [Heap.index,Evm.Memory.indexValue,Int.toNat_natCast,
      Heap.get_set_ne heap left parent (by decide),parent_elements]
    change [(MObj.elems .dyn ((heap.set left (MObj.setElem .dyn (heap.get left) 0 false)).get left))[0]?,
      (MObj.elems .dyn ((heap.set left (MObj.setElem .dyn (heap.get left) 0 false)).get left))[0]?]=
        [some false,some false]
    simp only [Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn]
    rfl
  · decide
  · simp only [byteVector,List.map_cons,List.map_nil,List.cons.injEq,and_true]
    repeat' apply And.intro
    all_goals
      simp only [bytes,primitiveBytes,List.foldl_cons,List.foldl_nil]
      repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length]; omega)
      exact byte_word_read _ _ _

/-- info: 'Solidity.Backend.MemoryOps.Physical.primitive_child_store_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms primitive_child_store_client

/-- Skipping the real child update retains true through BOTH old aliases;
the complete word image and selected byte span distinguish that stale state. -/
theorem primitive_child_store_negative :
    [(heap.index parent .dyn (Evm.Memory.indexValue (Evm.wmod 0))).bind
        (fun child => heap.index child .dyn (Evm.Memory.indexValue (Evm.wmod 0))),
      (heap.index parent .dyn (Evm.Memory.indexValue (Evm.wmod 1))).bind
        (fun child => heap.index child .dyn (Evm.Memory.indexValue (Evm.wmod 0)))]=
          [some true,some true] ∧
    wordVector primitiveNext≠wordVector machine ∧
    Environment.readMemory primitiveBytes 64 32≠Environment.readMemory bytes 64 32 := by
  refine ⟨?_,by decide,?_⟩
  · simp only [Heap.index,Evm.Memory.indexValue,Int.toNat_natCast,MObj.elems_dyn]
    rfl
  · have old : Environment.readMemory bytes 64 32=Semantics.wordBytes 1 := by
      simp only [bytes,List.foldl_cons,List.foldl_nil]
      repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length]; omega)
      exact byte_word_read _ _ _
    have next : Environment.readMemory primitiveBytes 64 32=Semantics.wordBytes 0 :=
      byte_word_read bytes 64 0
    rw [old,next]
    decide

/-- The endpoint is a real typed None and actual checked word revert. Neither
outcome exposes a post-error machine or establishes rollback/byte panic data. -/
theorem primitive_child_store_endpoint :
    heap.writeAddr (.index left .dyn (Evm.Memory.indexValue (Evm.wmod 2))) false=none ∧
    Evm.run (Evm.Memory.writeArrayCode (bases left.id))
      ((machine.push (.val (Evm.wmod 0))).push (.val (Evm.wmod 2)))=.revert := by
  have bounds : ¬(Evm.Memory.indexValue (Evm.wmod 2)).1.toNat<heap.len left .dyn := by
    rw [left_length]
    decide
  have bad : heap.writeAddr (.index left .dyn (Evm.Memory.indexValue (Evm.wmod 2))) false=none := by
    simp only [Heap.writeAddr,Heap.setIndex,show ¬(Evm.Memory.indexValue (Evm.wmod 2)).1.toNat<
      (MObj.elems .dyn (heap.get left)).length from bounds,↓reduceIte]
  refine ⟨bad,?_⟩
  rcases Evm.Memory.writeArray_correct populated_child (Evm.wmod 2) false
      (.val (Evm.wmod 0)) rfl with ⟨out,ht,_⟩ | ⟨_,run⟩
  · rw [bad] at ht
    cases ht
  · exact run

/-- info: 'Solidity.Backend.MemoryOps.Physical.primitive_child_store_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms primitive_child_store_negative
/-- info: 'Solidity.Backend.MemoryOps.Physical.primitive_child_store_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms primitive_child_store_endpoint

namespace Controls

/-- Stack-frame client contract using the unchanged inhabited control inputs. -/
def ReframeStackClientGoal : Prop :=
  let input := reframeStackClientInput
  let sourceState := input.1
  let hp := input.2.1
  let root := input.2.2.1
  let machine := input.2.2.2.1
  let bytes := input.2.2.2.2
  let next : Evm.Machine := {machine with stack:=[.val (Evm.wmod 11),.val (Evm.wmod 22)]}
  UintArrayAt sourceState 0 hp root (Evm.wmod 1) next bytes ∧
  next.stack=[.val (Evm.wmod 11),.val (Evm.wmod 22)] ∧
  machine.stack=[.val (Evm.wmod 77),.val (Evm.wmod 88)] ∧ next≠machine

/-- The independently inhabited control supplies this target, rather than
assuming it or identifying its two different whole machines. -/
theorem reframe_stack_client_goal : ReframeStackClientGoal := reframe_stack_client

/-- info: 'Solidity.Backend.MemoryOps.Physical.Controls.reframe_stack_client_goal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reframe_stack_client_goal
end Controls

/-- info: 'Solidity.Backend.MemoryOps.Physical.uint_array_reframe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uint_array_reframe
end Solidity.Backend.MemoryOps.Physical
