import Solidity.Backend.MemoryOps.PhysicalArrayReframe
import Solidity.Backend.MemoryOps.PhysicalSourceUint
import Solidity.Backend.MemoryOps.PhysicalUintWrite
import Solidity.Backend.MemoryOps.PhysicalByteJournal
import Solidity.Source.Semantics
import Solidity.Backend.MemoryOps.PhysicalUintDelete
import Solidity.Roadmap.Controls

/-! Inhabited INITIAL source, typed heap and real target word/byte cells. The
complete32-byte word observations retain headers, neighbor and stack tails.
No symbolic pointer encoding, physical allocator or external EVM is asserted. -/
namespace Solidity.Backend.MemoryOps.Physical.Controls
private abbrev U : RefTy := .array (.prim .uint)
private abbrev H : HTy := [U,U]
private def root : HRef H U := ⟨0,rfl⟩
private def neighbor : HRef H U := ⟨1,rfl⟩
private def u (n : Nat) : PrimTy.uint.Denote := Evm.Memory.indexValue (Evm.wmod n)
private def hp : Heap H := (⟨[u 7],by decide⟩,⟨[u 8,u 9],by decide⟩,())
private def machineBase : Evm.Machine := {Evm.Machine.init with stack := [.val (Evm.wmod 77),.val (Evm.wmod 88)]}
private def store (m : Evm.Machine) (a v : Nat) := Evm.Memory.writeMachine m a (.val (Evm.wmod v))
private def machine : Evm.Machine := store (store (store (store (store machineBase 1 1) 2 7) 4 2) 5 8) 6 9
private def put (m : Environment.Memory) (a v : Nat) := Environment.writeBytes m (32*a) (Semantics.wordBytes v)
private def bytes : Environment.Memory := put (put (put (put (put (fun _ => 0) 1 1) 2 7) 4 2) 5 8) 6 9
private def live (c : Nat) : Prop := ((((False ∨ c=1) ∨ c=2) ∨ c=4) ∨ c=5) ∨ c=6

private theorem frame : WordFrame machine bytes live := by
  have h0 : WordFrame machineBase (fun _ => 0) (fun _ => False) := ⟨fun _ h => h.elim,fun _ h => h.elim⟩
  have h1 : WordFrame (store machineBase 1 1) (put (fun _ => 0) 1 1) (fun c => False ∨ c=1) :=
    h0.write 1 (Evm.wmod 1) (by decide)
  have h2 : WordFrame (store (store machineBase 1 1) 2 7)
      (put (put (fun _ => 0) 1 1) 2 7) (fun c => (False ∨ c=1) ∨ c=2) :=
    h1.write 2 (Evm.wmod 7) (by decide)
  have h4 : WordFrame (store (store (store machineBase 1 1) 2 7) 4 2)
      (put (put (put (fun _ => 0) 1 1) 2 7) 4 2) (fun c => ((False ∨ c=1) ∨ c=2) ∨ c=4) :=
    h2.write 4 (Evm.wmod 2) (by decide)
  have h5 : WordFrame (store (store (store (store machineBase 1 1) 2 7) 4 2) 5 8)
      (put (put (put (put (fun _ => 0) 1 1) 2 7) 4 2) 5 8) (fun c => (((False ∨ c=1) ∨ c=2) ∨ c=4) ∨ c=5) :=
    h4.write 5 (Evm.wmod 8) (by decide)
  exact h5.write 6 (Evm.wmod 9) (by decide)

private theorem cell_bytes (c n : Nat) (hc : live c) (hm : machine.mem c=.val (Evm.wmod n)) :
    Environment.readMemory bytes (32*c) 32=Semantics.wordBytes (Evm.wmod n).val := by
  obtain ⟨w,hw,hbytes⟩ := frame.cells c hc
  have heq : w=Evm.wmod n := Evm.Word.val.inj (hw.symm.trans hm)
  simpa only [heq] using hbytes

private def E0 : Source.Env := ⟨[]⟩
private def y0 : Source.EMState E0 [] := (.nil,Source.St.init E0)
private def y1 : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory [u 7])).run y0).2
private def sourceState : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory [u 8,u 9])).run y1).2
private def srcFrame : Source.Fr := {this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "P6"}
private theorem root_length : hp.len root .dyn=1 := by
  simp only [Heap.len,MObj.elems_dyn]
  rfl

private theorem initial : UintArrayAt sourceState 0 hp root (Evm.wmod 1) machine bytes := by
  constructor
  · unfold SourceUintMemoryAt
    simp only [MObj.elems_dyn]
    rfl
  · refine ⟨by rw [root_length];decide,by rw [root_length];rfl,?_⟩
    intro i v hv
    simp only [MObj.elems_dyn] at hv
    cases i with
    | zero => cases hv;exact Evm.ReprV.uint_of rfl
    | succ i => cases i <;> cases hv
  · constructor
    · intro c hc
      have hc' : c=1 ∨ c=2 := by rw [root_length] at hc;change 1≤c ∧ c<1+1+1 at hc;omega
      rcases hc' with rfl | rfl <;> decide
    · intro c hc
      apply frame.cells
      change ((((False ∨ c=1) ∨ c=2) ∨ c=4) ∨ c=5) ∨ c=6
      rw [root_length] at hc
      change 1≤c ∧ c<1+1+1 at hc
      omega

/-- Actual Source allocation supplies the initial relation. The selected
Source read and complete32 physical bytes derive from it, not a payload oracle. -/
theorem source_read_and_neighbor :
    (Source.readLoc (E := E0) (Γ := []) srcFrame (τ := .int .u256) (.mem 0 0)).run sourceState=
      (.ok (sourceUint (u 7)),sourceState) ∧
    [Environment.readMemory bytes 32 32,Environment.readMemory bytes 64 32,
      Environment.readMemory bytes 128 32,Environment.readMemory bytes 160 32,Environment.readMemory bytes 192 32]=
      [Semantics.wordBytes 1,Semantics.wordBytes 7,Semantics.wordBytes 2,Semantics.wordBytes 8,Semantics.wordBytes 9] ∧
    sourceState.2.heap.get 1=some ⟨.array .memory (.int .u256) none,sourceUintMemory [u 8,u 9]⟩ := by
  obtain ⟨v,hv,hs,hb,ht⟩ := initial.read srcFrame (Evm.wmod 0) (by rw [root_length];decide)
  have he : v=u 7 := by
    simp only [MObj.elems_dyn] at hv
    exact (Option.some.inj hv).symm
  subst v
  refine ⟨hs,?_,rfl⟩
  rw [cell_bytes 1 1 (by unfold live;decide) rfl,cell_bytes 2 7 (by unfold live;decide) rfl,cell_bytes 4 2 (by unfold live;decide) rfl,
    cell_bytes 5 8 (by unfold live;decide) rfl,cell_bytes 6 9 (by unfold live;decide) rfl]
  rfl

/-- A genuinely changing store of maximum uint retains every represented
neighbor, both real stack tails and the whole exact word-byte image. -/
theorem changed_store :
    Evm.run [.mstoreAt] ((machine.push (.val Evm.wMax)).push (.val (Evm.wmod 2)))=
      .ok (Evm.Memory.writeMachine machine 2 (.val Evm.wMax)) 0 ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 64 (by decide)::lenU Evm.wMax.val Evm.wMax.isLt::[u 77,u 88],bytes⟩=
      some ⟨[u 77,u 88],Environment.writeBytes bytes 64 (Semantics.wordBytes Evm.wMax.val)⟩ ∧
    Environment.readMemory (Environment.writeBytes bytes 64 (Semantics.wordBytes Evm.wMax.val)) 64 32=
      Semantics.wordBytes Evm.wMax.val ∧
    Environment.readMemory (Environment.writeBytes bytes 64 (Semantics.wordBytes Evm.wMax.val)) 192 32=
      Environment.readMemory bytes 192 32 ∧
    (Evm.Memory.writeMachine machine 2 (.val Evm.wMax)).mem 6=machine.mem 6 ∧
    WordFrame (Evm.Memory.writeMachine machine 2 (.val Evm.wMax))
      (Environment.writeBytes bytes 64 (Semantics.wordBytes Evm.wMax.val)) (fun c => live c ∨ c=2) ∧
    (Evm.Memory.writeMachine machine 2 (.val Evm.wMax)).stack=[.val (Evm.wmod 77),.val (Evm.wmod 88)] ∧
    [Environment.readMemory (Environment.writeBytes bytes 64 (Semantics.wordBytes Evm.wMax.val)) 32 32,
      Environment.readMemory (Environment.writeBytes bytes 64 (Semantics.wordBytes Evm.wMax.val)) 64 32,
      Environment.readMemory (Environment.writeBytes bytes 64 (Semantics.wordBytes Evm.wMax.val)) 128 32,
      Environment.readMemory (Environment.writeBytes bytes 64 (Semantics.wordBytes Evm.wMax.val)) 160 32,
      Environment.readMemory (Environment.writeBytes bytes 64 (Semantics.wordBytes Evm.wMax.val)) 192 32]=
      [Semantics.wordBytes 1,Semantics.wordBytes Evm.wMax.val,Semantics.wordBytes 2,Semantics.wordBytes 8,Semantics.wordBytes 9] := by
  obtain ⟨hw,hb,hf⟩ := frame.mstore (Evm.wmod 2) Evm.wMax [u 77,u 88] (by decide)
  refine ⟨hw,hb,?_,?_,?_,hf,rfl,?_⟩
  · simpa only [word_bytes_length] using Environment.read_written (Semantics.wordBytes Evm.wMax.val) 64 bytes
  · apply readMemory_write_frame
    rw [word_bytes_length]
    omega
  · exact Evm.upd_other machine.mem (.val Evm.wMax) (by decide : (6:Nat)≠2)
  · have outside (c : Nat) (hc : c≠2) :
        Environment.readMemory (Environment.writeBytes bytes 64 (Semantics.wordBytes Evm.wMax.val)) (32*c) 32=
          Environment.readMemory bytes (32*c) 32 := by
      apply readMemory_write_frame
      rw [word_bytes_length]
      omega
    rw [outside 1 (by decide),outside 4 (by decide),outside 5 (by decide),outside 6 (by decide)]
    rw [cell_bytes 1 1 (by unfold live;decide) rfl,cell_bytes 4 2 (by unfold live;decide) rfl,
      cell_bytes 5 8 (by unfold live;decide) rfl,cell_bytes 6 9 (by unfold live;decide) rfl]
    have atWritten : Environment.readMemory (Environment.writeBytes bytes 64 (Semantics.wordBytes Evm.wMax.val)) 64 32=
        Semantics.wordBytes Evm.wMax.val := by
      simpa only [word_bytes_length] using Environment.read_written (Semantics.wordBytes Evm.wMax.val) 64 bytes
    rw [atWritten]
    rfl

/-- Physical offset64 and logical cell2 are observably different. This
negative prevents erasing the explicit scaling boundary from the interface. -/
theorem wrong_unscaled_offset :
    Environment.writeBytes bytes 64 (Semantics.wordBytes 255) 95≠
      Environment.writeBytes bytes 2 (Semantics.wordBytes 255) 95 := by
  rw [show 95=64+31 from rfl,Environment.writeBytes_at _ 64 31 bytes (by rw [word_bytes_length];decide)]
  rw [Environment.writeBytes_frame (Semantics.wordBytes 255) 2 95 bytes (by rw [word_bytes_length];omega)]
  have hb : bytes 95=(Semantics.wordBytes 7)[31] := by
    change Environment.writeBytes (put (put (put (put (fun _ => 0) 1 1) 2 7) 4 2) 5 8) 192 (Semantics.wordBytes 9) 95=_
    simp only [put]
    rw [Environment.writeBytes_frame _ 192 95 _ (Or.inl (by decide))]
    rw [Environment.writeBytes_frame _ 160 95 _ (Or.inl (by decide))]
    rw [Environment.writeBytes_frame _ 128 95 _ (Or.inl (by decide))]
    exact Environment.writeBytes_at _ 64 31 _ (by rw [word_bytes_length];decide)
  rw [hb]
  decide

/-- A real reached word payload precedes the EXISTING explicit local restore.
Persistent/transient and caller-stack restoration are scoped to that checkpoint;
there is no statement about a global Source transaction or post-EVM-revert state. -/
theorem live_payload_then_local_restore :
    let caller : Failure.Local.Journal Nat Bool := ⟨3,true,⟨[⟨77,by decide⟩,⟨88,by decide⟩],bytes⟩⟩
    let reached : Failure.Local.Journal Nat Bool :=
      ⟨9,false,⟨[⟨77,by decide⟩,⟨88,by decide⟩],Environment.writeBytes bytes 64 (Semantics.wordBytes Evm.wMax.val)⟩⟩
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 64 (by decide)::lenU Evm.wMax.val Evm.wMax.isLt::[u 77,u 88],bytes⟩=
      some ⟨[u 77,u 88],reached.machine.memory⟩ ∧
    Failure.Slice.run [.op .REVERT]
      ⟨[⟨64,by decide⟩,⟨32,by decide⟩]++reached.machine.stack,reached.machine.memory⟩=
      some (reached.machine,some (.revert (Semantics.wordBytes Evm.wMax.val))) ∧
    Failure.Local.finish (Failure.Local.save caller) (.revert (Semantics.wordBytes Evm.wMax.val)) reached=caller ∧
    WordFrame machine
      (Failure.Local.finish (Failure.Local.save caller) (.revert (Semantics.wordBytes Evm.wMax.val)) reached).machine.memory live ∧
    reached.persistent=9 ∧ reached.transient=false ∧ caller.persistent=3 ∧ caller.transient=true := by
  dsimp only
  refine ⟨byte_mstore bytes [u 77,u 88] (Evm.wmod 2) Evm.wMax (by decide),
    revert_written_word bytes (Evm.wmod 2) Evm.wMax (by decide) [⟨77,by decide⟩,⟨88,by decide⟩] [],
    rfl,frame,rfl,rfl,rfl,rfl⟩

/-- A changing Source write, intrinsic update and complete actual indexed
word program produce the SAME physical postrelation. The reached Source read,
all source object tables, original neighbor and caller frames derive from it. -/
theorem reached_source_write :
    ∃ (out : Heap H) (z : Source.EMState E0 []),
      hp.writeAddr (.index root .dyn (Evm.Memory.indexValue (Evm.wmod 0)))
        (Evm.Memory.indexValue Evm.wMax)=some out ∧
      (Source.writeLoc (E := E0) (Γ := []) srcFrame 0 (.mem 0 0)
        (sourceUint (Evm.Memory.indexValue Evm.wMax))).run sourceState=(.ok (),z) ∧
      Evm.run (Evm.Memory.writeArrayCode (Evm.wmod 1))
        ((machine.push (.val Evm.wMax)).push (.val (Evm.wmod 0)))=
        .ok (Evm.Memory.writeMachine machine 2 (.val Evm.wMax)) 0 ∧
      (∃ offset : Fin Evm.W,offset.val=64 ∧ ∀ tail : List Environment.Word,
        Environment.cryptoStep (.op .MSTORE)
          ⟨lenU offset.val offset.isLt::lenU Evm.wMax.val Evm.wMax.isLt::tail,bytes⟩=
          some ⟨tail,Environment.writeBytes bytes 64 (Semantics.wordBytes Evm.wMax.val)⟩) ∧
      UintArrayAt z 0 out root (Evm.wmod 1) (Evm.Memory.writeMachine machine 2 (.val Evm.wMax))
        (Environment.writeBytes bytes 64 (Semantics.wordBytes Evm.wMax.val)) ∧
      (Source.readLoc (E := E0) (Γ := []) srcFrame (τ := .int .u256) (.mem 0 0)).run z=
        (.ok (sourceUint (Evm.Memory.indexValue Evm.wMax)),z) ∧
      MObj.elems .dyn (out.get root)=[Evm.Memory.indexValue Evm.wMax] ∧
      out.get neighbor=hp.get neighbor ∧
      [sourceState.2.heap.get 0,sourceState.2.heap.get 1,z.2.heap.get 0,z.2.heap.get 1]=
        [some ⟨.array .memory (.int .u256) none,sourceUintMemory [u 7]⟩,
         some ⟨.array .memory (.int .u256) none,sourceUintMemory [u 8,u 9]⟩,
         some ⟨.array .memory (.int .u256) none,sourceUintMemory [Evm.Memory.indexValue Evm.wMax]⟩,
         some ⟨.array .memory (.int .u256) none,sourceUintMemory [u 8,u 9]⟩] ∧
      z.1=sourceState.1 ∧ z.2={sourceState.2 with heap := z.2.heap} := by
  obtain ⟨out,z,ht,hs,hw,hbyte,hnew,hloc,hworld,hotherS,hotherT,houtside⟩ :=
    initial.write_cell srcFrame 0 (Evm.wmod 0) Evm.wMax (by rw [root_length];decide)
  have hk : hp.writeAddr (.index root .dyn (Evm.Memory.indexValue (Evm.wmod 0)))
      (Evm.Memory.indexValue Evm.wMax)=
      some (hp.set root (MObj.setElem .dyn (hp.get root) 0 (Evm.Memory.indexValue Evm.wMax))) := by
    change (if 0<hp.len root .dyn then some _ else none)=_
    exact if_pos (by rw [root_length];decide)
  have hout : out=hp.set root (MObj.setElem .dyn (hp.get root) 0 (Evm.Memory.indexValue Evm.wMax)) :=
    Option.some.inj (ht.symm.trans hk)
  have elems : MObj.elems .dyn (out.get root)=[Evm.Memory.indexValue Evm.wMax] := by
    rw [hout,Heap.get_set_same,MObj.elems_setElem]
    simp only [MObj.elems_dyn]
    rfl
  have hi : (Evm.wmod 0).val<out.len root .dyn := by
    change (Evm.wmod 0).val<(MObj.elems .dyn (out.get root)).length
    rw [elems]
    decide
  obtain ⟨v,hv,hr,hbytes,hload⟩ := hnew.read srcFrame (Evm.wmod 0) hi
  rw [elems] at hv
  have heq : v=Evm.Memory.indexValue Evm.wMax := (Option.some.inj hv).symm
  subst v
  have table : z.2.heap.get 0=some ⟨.array .memory (.int .u256) none,
      sourceUintMemory [Evm.Memory.indexValue Evm.wMax]⟩ := by
    have rep : SourceUintMemoryAt z 0 out root .dyn := hnew.source
    unfold SourceUintMemoryAt at rep
    rw [elems] at rep
    exact rep
  refine ⟨out,z,ht,hs,hw,hbyte,hnew,hr,elems,hotherT neighbor (by decide),?_,hloc,hworld⟩
  rw [table,hotherS 1 (by decide)]
  rfl

/-- A frozen pre-write Source read cannot be substituted for the reached read
above, even though the physical store already exposes the maximum word. -/
theorem frozen_source_is_wrong :
    (Source.readLoc (E := E0) (Γ := []) srcFrame (τ := .int .u256) (.mem 0 0)).run sourceState≠
      (.ok (sourceUint (Evm.Memory.indexValue Evm.wMax)),sourceState) := by
  intro bad
  have he : sourceUint (D := E0.layout) (u 7)=sourceUint (Evm.Memory.indexValue Evm.wMax) :=
    Except.ok.inj (congrArg Prod.fst (source_read_and_neighbor.1.symm.trans bad))
  have hv : u 7=Evm.Memory.indexValue Evm.wMax := by
    simpa only [calldataUint_sourceUint] using congrArg
      (fun v : Source.Val E0.layout (.int .u256) => calldataUint (.val v)) he
  have hn : (7:Nat)=Evm.wMax.val := congrArg (fun v : PrimTy.uint.Denote => v.val.toNat) hv
  exact (by decide : (7:Nat)≠Evm.wMax.val) hn

/-! The existing initial heap/bytes are reused, with an actual typed root,
index and retained alias in Source locals. Fixed oracle fields are UNUSED by
this deletion syntax; evaluation still uses the independent Source evaluator. -/
private abbrev DelCtx : Source.RCtx :=
  [.array .memory (.int .u256) none,.int .u256,.array .memory (.int .u256) none]
private def delState (i : Nat) : Source.EMState E0 DelCtx :=
  (.cons (.memRef rfl 0) (.cons (sourceUint (u i)) (.cons (.memRef rfl 0) .nil)),sourceState.2)
private def delRoot : Source.Idx DelCtx (.array .memory (.int .u256) none) := .here
private def delIndex : Source.Idx DelCtx (.int .u256) := .there .here
private def delAlias : Source.Idx DelCtx (.array .memory (.int .u256) none) := .there (.there .here)
private def delGlobal (pipeline : Roadmap.Pipeline) : Source.Glob E0 :=
  { prog := {body:=fun _ => none,consts:=fun _ => none,inits:=fun _ => [],
             ctor:=fun _ => none,ctorLocals:=fun _ => [],baseArgs:=fun _ => [],contracts:=[]},
    pipeline:=pipeline,fixed:=Roadmap.Controls.toyFixed,balance0:=fun _ => ⟨0,by decide⟩,
    hasCode:=fun _ _ => false,callee:=fun _ => .answer (.success []),timestamp:=⟨0,by decide⟩ }
private theorem delInitial (i : Nat) : UintArrayAt (delState i) 0 hp root (Evm.wmod 1) machine bytes :=
  ⟨initial.source,initial.words,initial.physical⟩

/-- Both actual Source pipelines execute deletion to the SAME reached object
as the word/byte zero store. All five original header/payload spans, both Source
tables, retained alias, nonheap fields, typed neighbor and target tail remain. -/
theorem physical_delete_program (pipeline : Roadmap.Pipeline) :
    ∃ (out : Heap H) (z : Source.EMState E0 DelCtx),
      (Source.evalE (delGlobal pipeline) srcFrame 3
        (sourceUintIndexedDelete delRoot delIndex)).run (delState 0)=(.ok Source.RVal.unit,z) ∧
      (Source.execS (delGlobal pipeline) srcFrame 4 3 none
        (.expr (sourceUintIndexedDelete delRoot delIndex) : Source.RStmt E0 [] false .body DelCtx DelCtx)
        (delState 0).1).run (.nil,(delState 0).2)=
          (.ok (.normal (delState 0).1),(.nil,z.2)) ∧
      Evm.run (Evm.Memory.writeArrayCode (Evm.wmod 1))
        ((machine.push (.val (Evm.wmod 0))).push (.val (Evm.wmod 0)))=
          .ok (Evm.Memory.writeMachine machine 2 (.val (Evm.wmod 0))) 0 ∧
      (∃ offset : Fin Evm.W,offset.val=64 ∧ ∀ tail : List Environment.Word,
        Environment.cryptoStep (.op .MSTORE)
          ⟨lenU offset.val offset.isLt::lenU 0 (by decide)::tail,bytes⟩=
            some ⟨tail,Environment.writeBytes bytes 64 (List.replicate 32 0)⟩) ∧
      UintArrayAt z 0 out root (Evm.wmod 1) (Evm.Memory.writeMachine machine 2 (.val (Evm.wmod 0)))
        (Environment.writeBytes bytes 64 (List.replicate 32 0)) ∧
      MObj.elems .dyn (out.get root)=[u 0] ∧ out.get neighbor=hp.get neighbor ∧
      [Environment.readMemory (Environment.writeBytes bytes 64 (List.replicate 32 0)) 32 32,
       Environment.readMemory (Environment.writeBytes bytes 64 (List.replicate 32 0)) 64 32,
       Environment.readMemory (Environment.writeBytes bytes 64 (List.replicate 32 0)) 128 32,
       Environment.readMemory (Environment.writeBytes bytes 64 (List.replicate 32 0)) 160 32,
       Environment.readMemory (Environment.writeBytes bytes 64 (List.replicate 32 0)) 192 32]=
        [Semantics.wordBytes 1,Semantics.wordBytes 0,Semantics.wordBytes 2,Semantics.wordBytes 8,Semantics.wordBytes 9] ∧
      [(delState 0).2.heap.get 0,(delState 0).2.heap.get 1,z.2.heap.get 0,z.2.heap.get 1]=
        [some ⟨.array .memory (.int .u256) none,sourceUintMemory [u 7]⟩,
         some ⟨.array .memory (.int .u256) none,sourceUintMemory [u 8,u 9]⟩,
         some ⟨.array .memory (.int .u256) none,sourceUintMemory [u 0]⟩,
         some ⟨.array .memory (.int .u256) none,sourceUintMemory [u 8,u 9]⟩] ∧
      z.1.get delRoot=.memRef rfl 0 ∧ z.1.get delAlias=.memRef rfl 0 ∧
      (Source.evalE (delGlobal pipeline) srcFrame 2
        (.indexArray (.local delAlias) (.local delIndex) rfl)).run z=
          (.ok (.val (sourceUint (u 0))),z) ∧
      z.2={(delState 0).2 with heap:=z.2.heap} ∧
      (Evm.Memory.writeMachine machine 2 (.val (Evm.wmod 0))).stack=
        [.val (Evm.wmod 77),.val (Evm.wmod 88)] := by
  obtain ⟨out,z,ht,hd,he,hstmt,hw,hbyte,hr,hl,hs,hother,hneighbor⟩ :=
    (delInitial 0).delete_expression (delGlobal pipeline) srcFrame 0 3 delRoot delIndex (Evm.wmod 0)
      rfl rfl (by rw [root_length];decide)
  have hk : hp.writeAddr (.index root .dyn (Evm.Memory.indexValue (Evm.wmod 0))) (PrimTy.dflt .uint)=
      some (hp.set root (MObj.setElem .dyn (hp.get root) 0 (u 0))) := by
    change (if 0<hp.len root .dyn then some _ else none)=_
    exact if_pos (by rw [root_length];decide)
  have hout : out=hp.set root (MObj.setElem .dyn (hp.get root) 0 (u 0)) := Option.some.inj (ht.symm.trans hk)
  have elems : MObj.elems .dyn (out.get root)=[u 0] := by
    rw [hout,Heap.get_set_same,MObj.elems_setElem]
    simp only [MObj.elems_dyn]
    rfl
  have table : z.2.heap.get 0=some ⟨.array .memory (.int .u256) none,sourceUintMemory [u 0]⟩ := by
    have rep := hr.source
    unfold SourceUintMemoryAt at rep
    rw [elems] at rep
    exact rep
  have hlen : out.len root .dyn=1 := by
    change (MObj.elems .dyn (out.get root)).length=1
    rw [elems]
    rfl
  have aliasRead := hr.source.eval_index (delGlobal pipeline) srcFrame 0 delAlias delIndex (u 0)
    (by rw [hl];rfl) (by rw [hl];rfl) (by rw [hlen];decide)
  have aliasZero : (Source.evalE (delGlobal pipeline) srcFrame 2
      (.indexArray (.local delAlias) (.local delIndex) rfl)).run z=
        (.ok (.val (sourceUint (u 0))),z) := by
    simpa only [elems,List.getElem_cons_zero] using aliasRead
  have zeroRead := Environment.read_written (Semantics.wordBytes 0) 64 bytes
  rw [word_bytes_length] at zeroRead
  refine ⟨out,z,he,hstmt,hw,hbyte,hr,elems,hneighbor neighbor (by decide),?_,?_,?_,?_,aliasZero,hs,rfl⟩
  · rw [← uint_delete_bytes]
    rw [readMemory_write_frame _ 32 32 64 _ (Or.inl (by decide)),
      zeroRead,
      readMemory_write_frame _ 128 32 64 _ (Or.inr (by decide)),
      readMemory_write_frame _ 160 32 64 _ (Or.inr (by decide)),
      readMemory_write_frame _ 192 32 64 _ (Or.inr (by decide))]
    rw [cell_bytes 1 1 (by unfold live;decide) rfl,cell_bytes 4 2 (by unfold live;decide) rfl,
      cell_bytes 5 8 (by unfold live;decide) rfl,cell_bytes 6 9 (by unfold live;decide) rfl]
    rfl
  · rw [table,hother 1 (by decide)]
    rfl
  · rw [hl]
    rfl
  · rw [hl]
    rfl

/-- Literal endpoint rejection and insufficient evaluator horizon retain the
actual initial state. No target post-revert machine is invented. -/
theorem physical_delete_endpoint_timeout (pipeline : Roadmap.Pipeline) :
    (Source.deleteLoc (E := E0) (Γ := DelCtx) srcFrame 1 (τ := .int .u256) (.mem 0 1)).run (delState 1)=
      (.error (.revert (Source.panicData .index)),delState 1) ∧
    hp.writeAddr (.index root .dyn (u 1)) (PrimTy.dflt .uint)=none ∧
    Evm.run (Evm.Memory.writeArrayCode (Evm.wmod 1))
      ((machine.push (.val (Evm.wmod 0))).push (.val (Evm.wmod 1)))=.revert ∧
    (Source.evalE (delGlobal pipeline) srcFrame 3 (sourceUintIndexedDelete delRoot delIndex)).run (delState 1)=
      (.error (.revert (Source.panicData .index)),delState 1) ∧
    (Source.evalE (delGlobal pipeline) srcFrame 0 (sourceUintIndexedDelete delRoot delIndex)).run (delState 0)=
      (.error .timeout,delState 0) := by
  have hd := (delInitial 1).delete_bounds srcFrame 0 (Evm.wmod 1) (by rw [root_length];decide)
  refine ⟨hd.1,hd.2.1,hd.2.2,?_,rfl⟩
  rw [sourceUintIndexedDelete,Source.evalE,Source.Hoare.run_bind,
    (delInitial 1).source.eval_index_bounds (delGlobal pipeline) srcFrame 0 delRoot delIndex (u 1)
      rfl rfl (by rw [root_length];decide)]

/-- Skipping the real clear leaves a different complete selected word image. -/
theorem physical_delete_skipped_differs :
    Environment.readMemory bytes 64 32≠
      Environment.readMemory (Environment.writeBytes bytes 64 (List.replicate 32 0)) 64 32 := by
  rw [cell_bytes 2 7 (by unfold live;decide) rfl,← uint_delete_bytes]
  have h := Environment.read_written (Semantics.wordBytes 0) 64 bytes
  rw [word_bytes_length] at h
  rw [h]
  decide

private def delContract : Contract := {vars:=[]}
private abbrev DelTyped : Ctx := [.mem U,.val .uint,.mem U]
private def typedDeleteState : State delContract DelTyped :=
  {storage:=Storage.init delContract,H:=H,heap:=hp,env:=(some root,u 0,some root,()),
   selfBalance:=u 13,tx:={msgSender:=u 55,selfAddress:=u 66,timestamp:=u 77}}
private def typedRoot : Idx DelTyped (.mem U) := .here
private def typedIndex : Idx DelTyped (.val .uint) := .there .here

/-- Direct inhabited Source/intrinsic/word/physical client, retaining the whole
intrinsic environment, balance and transaction fields on the actual heap update. -/
theorem physical_delete_typed_program (pipeline : Roadmap.Pipeline) :
    ∃ (out : Heap H) (z : Source.EMState E0 DelCtx),
      (Source.evalE (delGlobal pipeline) srcFrame 3 (sourceUintIndexedDelete delRoot delIndex)).run (delState 0)=
        (.ok Source.RVal.unit,z) ∧
      Stmt.run typedDeleteState
        (.deleteMem (.loc (.index .dyn (.var typedRoot rfl) (.simple (.local typedIndex)))) rfl)=
          .ok ⟨typedDeleteState.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.writeArrayCode (Evm.wmod 1))
        ((machine.push (.val (Evm.wmod 0))).push (.val (Evm.wmod 0)))=
          .ok (Evm.Memory.writeMachine machine 2 (.val (Evm.wmod 0))) 0 ∧
      UintArrayAt z 0 out root (Evm.wmod 1) (Evm.Memory.writeMachine machine 2 (.val (Evm.wmod 0)))
        (Environment.writeBytes bytes 64 (List.replicate 32 0)) ∧
      (typedDeleteState.withHeap out).env=typedDeleteState.env ∧
      (typedDeleteState.withHeap out).selfBalance=u 13 ∧
      (typedDeleteState.withHeap out).tx=typedDeleteState.tx ∧
      z.2={(delState 0).2 with heap:=z.2.heap} := by
  obtain ⟨out,z,he,ht,hw,hr,_,hs⟩ := (delInitial 0).delete_typed typedDeleteState root
    (delGlobal pipeline) srcFrame 0 3 delRoot delIndex typedRoot typedIndex (Evm.wmod 0)
    rfl rfl rfl rfl (by change (Evm.wmod 0).val<hp.len root .dyn;rw [root_length];decide)
  exact ⟨out,z,he,ht,hw,hr,rfl,rfl,rfl,hs⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.Controls.physical_delete_typed_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms physical_delete_typed_program

/-- info: 'Solidity.Backend.MemoryOps.Physical.Controls.physical_delete_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms physical_delete_program
/-- info: 'Solidity.Backend.MemoryOps.Physical.Controls.physical_delete_endpoint_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms physical_delete_endpoint_timeout
/-- info: 'Solidity.Backend.MemoryOps.Physical.Controls.physical_delete_skipped_differs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms physical_delete_skipped_differs

/-- info: 'Solidity.Backend.MemoryOps.Physical.Controls.reached_source_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_source_write
/-- info: 'Solidity.Backend.MemoryOps.Physical.Controls.frozen_source_is_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frozen_source_is_wrong

/-- info: 'Solidity.Backend.MemoryOps.Physical.Controls.source_read_and_neighbor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_read_and_neighbor
/-- info: 'Solidity.Backend.MemoryOps.Physical.Controls.changed_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms changed_store
/-- info: 'Solidity.Backend.MemoryOps.Physical.Controls.wrong_unscaled_offset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_unscaled_offset
/-- info: 'Solidity.Backend.MemoryOps.Physical.Controls.live_payload_then_local_restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms live_payload_then_local_restore
/-- An inhabited client of uint_array_cells_eq: use both actual array
representations to transport complete physical observations to a distinct stack.
The source/heap/neighbor fixture is unchanged; the whole machines differ. -/
theorem reframe_stack_client :
    let next : Evm.Machine := {machine with stack:=[.val (Evm.wmod 11),.val (Evm.wmod 22)]}
    UintArrayAt sourceState 0 hp root (Evm.wmod 1) next bytes ∧
    next.stack=[.val (Evm.wmod 11),.val (Evm.wmod 22)] ∧
    machine.stack=[.val (Evm.wmod 77),.val (Evm.wmod 88)] ∧ next≠machine := by
  dsimp only
  let next : Evm.Machine := {machine with stack:=[.val (Evm.wmod 11),.val (Evm.wmod 22)]}
  have words : Evm.Memory.ArrayRepr hp root (Evm.wmod 1) next := initial.words.stack _
  have cells : ∀ c, (Evm.wmod 1).val≤c ∧ c<(Evm.wmod 1).val+1+hp.len root .dyn →
      next.mem c=machine.mem c := fun c hc => uint_array_cells_eq words initial.words c hc
  have represented : UintArrayAt sourceState 0 hp root (Evm.wmod 1) next bytes := by
    refine ⟨initial.source,words,initial.physical.fits,?_⟩
    intro c hc
    obtain ⟨w,hw,hb⟩ := initial.physical.cells c hc
    exact ⟨w,(cells c hc).trans hw,hb⟩
  refine ⟨represented,rfl,rfl,?_⟩
  intro same
  have distinct : ([.val (Evm.wmod 11),.val (Evm.wmod 22)] : List Evm.Word)≠
      [.val (Evm.wmod 77),.val (Evm.wmod 88)] := by decide
  exact distinct (congrArg Evm.Machine.stack same)

/-- info: 'Solidity.Backend.MemoryOps.Physical.Controls.reframe_stack_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reframe_stack_client

/-- Existing inhabited control inputs, exported only as a fixture tuple so
assembly contracts can live outside the proved-control module. -/
def reframeStackClientInput :
    Source.EMState (⟨[]⟩ : Source.Env) [] ×
    Heap [.array (.prim .uint),.array (.prim .uint)] ×
    HRef [.array (.prim .uint),.array (.prim .uint)] (.array (.prim .uint)) ×
    Evm.Machine × Environment.Memory := (sourceState,hp,root,machine,bytes)

end Solidity.Backend.MemoryOps.Physical.Controls
