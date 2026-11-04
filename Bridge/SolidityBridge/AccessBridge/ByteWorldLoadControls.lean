import SolidityBridge.AccessBridge.ByteWorldNumeric

/-! Inhabited initial images for every numeric word and either pipeline, plus
conditional H26 use with saved tails. The literal MLOAD refusal stays explicit;
no concrete byte-world Producer instance is fabricated. -/
namespace SolidityBridge.AccessBridge.ByteWorldLoadControls
open Solidity Solidity.Backend EvmYul
open Solidity.Evm.TryByteImage
private def C : Contract := {vars := []}
private def frame (pipeline : Pipeline) (value : Fin Evm.W) : FrameMem C [] where
  st := State.init C
  key := ⟨3,1,pipeline,7,lenU 1 (by decide),lenU 2 (by decide),lenU 4 (by decide)⟩
  scalar := by intro R i; cases i
  capacity := 32
  aligned := ⟨1,rfl⟩
  data := fun i => (Semantics.wordBytes value.val)[i.val]'(by
    rw [Environment.wordBytes_length];exact i.isLt)
  highWaterWords := 1
  resident := by decide
  zeroAbove := by intro i high; have bound := i.isLt; omega
private def native (pipeline : Pipeline) (value : Fin Evm.W) : EvmYul.MachineState :=
  MemoryLoad.installed (frame pipeline value) default
private def zeroCell : Fin Evm.W := ⟨0,by decide⟩
private def machine (value : Fin Evm.W) : Evm.Machine :=
  {Evm.Machine.init with mem := fun _ => .val value,stack := [.val ⟨258,by decide⟩,.val ⟨513,by decide⟩]}
private def tail : List Environment.Word := [lenU 258 (by decide),lenU 513 (by decide)]
private def runtime : Environment.Frame :=
  ⟨Environment.account (lenU 1 (by decide)),Environment.account (lenU 2 (by decide)),
    lenU 4 (by decide),lenU 77 (by decide),fun _ => lenU 99 (by decide)⟩

theorem native_image (pipeline : Pipeline) (value : Fin Evm.W) :
    FrameImage (frame pipeline value) (native pipeline value) :=
  MemoryLoad.installed_image _ _ (by change 32<UInt256.size;decide)

theorem word_image (pipeline : Pipeline) (value : Fin Evm.W) :
    MemoryOps.Physical.WordFrame (machine value)
      (MemoryOps.Physical.frameBytes (frame pipeline value)) (fun cell => cell=0) := by
  refine ⟨?_,?_⟩
  · intro cell selected
    subst cell
    decide
  · intro cell selected
    subst cell
    refine ⟨value,rfl,?_⟩
    apply List.ext_getElem
    · simp only [Environment.readMemory,List.length_map,List.length_range,
        Environment.wordBytes_length]
    · intro i hi hj
      have small : i<32 := by
        simpa only [Environment.readMemory,List.length_map,List.length_range] using hi
      simp only [Environment.readMemory,List.getElem_map,List.getElem_range]
      simp only [MemoryOps.Physical.frameBytes,frame,Nat.mul_zero,Nat.zero_add,dif_pos small]

/-- Conditional consumer for every initial word, with two distinct saved tails.
Only the exact published producer field remains a hypothesis. -/
theorem paired_case {code : Nat → Backend.Program}
    (producer : MemoryOps.Physical.ByteWorld.Producer code)
    (pipeline : Pipeline) (value : Fin Evm.W) :
    Environment.runSlice runtime (code 0)
      ⟨tail,MemoryOps.Physical.frameBytes (frame pipeline value)⟩=
      some ⟨lenU value.val value.isLt::tail,MemoryOps.Physical.frameBytes (frame pipeline value)⟩ ∧
    (toBytesBE 32 ((native pipeline value).mload (.ofNat 0)).1.toNat).toList=
      Semantics.wordBytes value.val ∧
    ((native pipeline value).mload (.ofNat 0)).2.memory=(native pipeline value).memory ∧
    Evm.run [.mloadAt] ((machine value).push (.val zeroCell))=
      .ok ((machine value).push (.val value)) 0 := by
  obtain ⟨chosen,word,intrinsic,byteRun,read,serialized,memory,post⟩ :=
    ByteWorldLoad.paired_load producer (frame pipeline value) (native pipeline value)
      (native_image pipeline value) (machine value) (fun cell => cell=0)
      (word_image pipeline value) runtime zeroCell (.ofNat 0) rfl rfl tail (by decide)
  change Evm.Word.val value=Evm.Word.val chosen at word
  have same : chosen=value := (Evm.Word.val.inj word).symm
  subst chosen
  exact ⟨byteRun,serialized,memory,intrinsic⟩

theorem numeric_case {code : Nat → Backend.Program}
    (producer : MemoryOps.Physical.ByteWorld.Producer code)
    (pipeline : Pipeline) (value : Fin Evm.W) :
    Environment.runSlice runtime (code 0)
      ⟨tail,MemoryOps.Physical.frameBytes (frame pipeline value)⟩=
      some ⟨lenU value.val value.isLt::tail,MemoryOps.Physical.frameBytes (frame pipeline value)⟩ ∧
    ((native pipeline value).mload (.ofNat 0)).1.toNat=value.val ∧
    ((native pipeline value).mload (.ofNat 0)).2.memory=(native pipeline value).memory ∧
    Evm.run [.mloadAt] ((machine value).push (.val zeroCell))=
      .ok ((machine value).push (.val value)) 0 := by
  obtain ⟨chosen,word,intrinsic,byteRun,read,memory,post⟩ :=
    ByteWorldNumeric.paired_numeric producer (frame pipeline value) (native pipeline value)
      (native_image pipeline value) (machine value) (fun cell => cell=0)
      (word_image pipeline value) runtime zeroCell (.ofNat 0) rfl rfl tail (by decide)
  change Evm.Word.val value=Evm.Word.val chosen at word
  have same : chosen=value := (Evm.Word.val.inj word).symm
  subst chosen
  exact ⟨byteRun,read,memory,intrinsic⟩

theorem literal_mload_refused (input : Environment.Slice) :
    Environment.runSlice runtime [.op .MLOAD] input=none := by
  simp only [Environment.runSlice,MemoryOps.Physical.ByteWorld.current_mload_boundary,
    Option.bind_none]

theorem bad_active_refused (pipeline : Pipeline) (value : Fin Evm.W) :
    ¬FrameImage (frame pipeline value) {(native pipeline value) with activeWords := .ofNat 0} := by
  intro image
  have wrong : 0=1 := image.active
  exact (by decide : (0 : Nat)≠1) wrong

theorem byte_overflow_domain : ¬(List.replicate 1024 (lenU 0 (by decide))).length+1≤1024 := by
  simp only [List.length_replicate]
  decide

/-- info: 'SolidityBridge.AccessBridge.ByteWorldLoadControls.native_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms native_image
/-- info: 'SolidityBridge.AccessBridge.ByteWorldLoadControls.word_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_image
/-- info: 'SolidityBridge.AccessBridge.ByteWorldLoadControls.paired_case' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms paired_case
/-- info: 'SolidityBridge.AccessBridge.ByteWorldLoadControls.literal_mload_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms literal_mload_refused
/-- info: 'SolidityBridge.AccessBridge.ByteWorldLoadControls.bad_active_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bad_active_refused
/-- info: 'SolidityBridge.AccessBridge.ByteWorldLoadControls.byte_overflow_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms byte_overflow_domain
/-- info: 'SolidityBridge.AccessBridge.ByteWorldLoadControls.numeric_case' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms numeric_case
end SolidityBridge.AccessBridge.ByteWorldLoadControls
