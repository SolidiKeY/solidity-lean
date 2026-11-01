import Solidity.Backend.AbiWorld.WordArrayPacket
import Solidity.Backend.AbiWorld.ReturnedBytesPrefix
import Solidity.Backend.AbiWorld.EnumControls

/-! Inhabited actual compiled call applications of the full-word observer.
The packet is a post-execution literal emission, not runtime memory-encoder
code or a Source declaration/signature lowering theorem. -/
namespace Solidity.Backend.AbiWorld.WordArrayControls
open Evm Evm.Memory ReturnedBytesControls

private def body (escape : Bool) : Prog C [.mem bytesR,.mem bytesR]
    [.val .bool,.mem bytesR,.mem bytesR] :=
  .cons (.rebindMem .here (if escape then .newArr (.lit 3 rfl) rfl
    else .alias (.var (.there .here) rfl)))
  (.cons (.assignMem (litLoc 1 (by decide +kernel)) (.val (u 300)))
  (.cons (.declLocal .bool (.user "private") (some (.simple (.bool true)))) .nil))

def stage (escape : Bool) : Prog C Entry Output :=
  .cons (.declMem bytesR (.user "argument") (some (.newArr (.lit 3 rfl) rfl)) rfl rfl)
  (.cons (litWrite 2 (by decide +kernel) 255)
  (.cons (.call "uintArray" (.snocMemory .nil bytesR (.user "arg") (.var .here rfl))
    (.mem bytesR (.user "result") rfl rfl) (body escape))
  (.cons (litWrite 0 (by decide +kernel) 11) .nil)))

def cert (escape : Bool) : Compiler.Compilation 1 prefixCert.frag (stage escape) :=
  (Compiler.compile 1 prefixCert.frag (stage escape)).get (by cases escape <;> decide +kernel)
def out (escape : Bool) : Solidity.Out C entry.st.H Output :=
  ((stage escape).run entry.st).toOption.get (by cases escape <;> decide +kernel)
attribute [irreducible] cert out

def reference (escape : Bool) : HRef (out escape).st.H bytesR :=
  (TEnv.get .here (out escape).st.env).get (by cases escape <;> decide +kernel)
attribute [irreducible] reference

theorem run (escape : Bool) : (stage escape).run entry.st = .ok (out escape) := by
  unfold out
  exact source_get _ _
theorem get (escape : Bool) : TEnv.get .here (out escape).st.env = some (reference escape) := by
  unfold reference
  exact EntryControls.option_get _ _
theorem memoryCalls (escape : Bool) : (cert escape).isMemoryCalls = true := by
  cases escape <;> decide +kernel
theorem noPay (escape : Bool) : Evm.Prog.pays (stage escape) = false := by
  cases escape <;> decide +kernel
theorem need (escape : Bool) : (cert escape).requiredFrame = 6 := by
  cases escape <;> decide +kernel
theorem cost (escape : Bool) : (cert escape).allocationCost entry.st = if escape then 9 else 5 := by
  cases escape <;> decide +kernel

def packet (escape : Bool) : List UInt8 :=
  AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes 3 ++ AbiEntry.wordBytes 11 ++
  AbiEntry.wordBytes 300 ++ AbiEntry.wordBytes (if escape then 0 else 255)

theorem encoded (escape : Bool) :
    AbiEntry.encodeArgs (WordArrayPacket.values ((out escape).st.heap.get (reference escape)).1) =
      packet escape := by
  rw [WordArrayPacket.encoded_values]
  cases escape <;> decide +kernel

/-- Actual nonempty caller setup, not an empty-entry BaseExtends instantiation. -/
theorem application (escape : Bool) (base : Nat → Fin Evm.W)
    (hs : StateRepr 1 1 128 prefixCert.frag entry.st base prefixMachine)
    (ha : StructAllocatorRepr entry.st.heap base 128 prefixCursor prefixMachine) :
    ∃ m' base', Evm.run (cert escape).code prefixMachine = .ok m' 0 ∧
      m'.stack = prefixMachine.stack ∧
      StateRepr 1 1 128 (cert escape).frag (out escape).st base' m' ∧
      BaseExtends entry.st.H base base' ∧
      GrowsAllocator 1 128 ((cert escape).allocationCost entry.st) entry.st base
        prefixMachine (out escape).st base' m' ∧
      WordArrayPacket.localObservation m' 1 (.here : Idx Output (.mem bytesR)) =
        some (WordArrayPacket.values ((out escape).st.heap.get (reference escape)).1) := by
  have hi : (cert escape).Input 1 128 base entry.st prefixMachine := by
    apply ((cert escape).memoryCalls_input (memoryCalls escape) 1 128 base entry.st prefixMachine).mpr
    refine ⟨hs, ?_, .inr ⟨by decide, prefixCursor, ha, ?_⟩⟩
    · rw [need]; decide
    · rw [cost,prefix_resources.2]
      cases escape <;> decide +kernel
  exact WordArrayPacket.compiled_observation (cert escape) (memoryCalls escape) hi (noPay escape)
    (out escape) (run escape) .here (reference escape) (get escape)

/-- Both actual machine executions and old reference0 base preservation. The
second is a literal packet emitted AFTER observation, not one runtime compiler. -/
theorem completed (escape : Bool) : ∃ base m' base',
    Evm.run prefixCert.code machine = .ok prefixMachine 0 ∧
    Evm.run (cert escape).code prefixMachine = .ok m' 0 ∧
    StateRepr 1 1 128 (cert escape).frag (out escape).st base' m' ∧
    base' oldRef.id = base oldRef.id ∧
    m'.stack = machine.stack ∧
    GrowsAllocator 1 128 ((cert escape).allocationCost entry.st) entry.st base
      prefixMachine (out escape).st base' m' ∧
    WordArrayPacket.observedPacket m' 1 (.here : Idx Output (.mem bytesR)) 17
      EnumControls.suffix EnumControls.machine =
      some ({EnumControls.machine with memory :=
        (Backend.Failure.Slice.putBytes EnumControls.machine.memory 17 (packet escape))},
        some (.success (packet escape))) := by
  obtain ⟨base,ht,hs,ha,hk⟩ := nonempty_entry
  obtain ⟨m',base',ht',hk',hr,hbase,hgrow,hobs⟩ := application escape base hs ha
  have hp := WordArrayPacket.execute_observed hr (.here : Idx Output (.mem bytesR))
    (reference escape) (get escape) 17 EnumControls.suffix EnumControls.machine
    (by rw [encoded]; unfold Backend.Failure.Fits; cases escape <;> decide +kernel)
    (by decide +kernel)
  rw [encoded] at hp
  exact ⟨base,m',base',ht,ht',hr,hbase oldRef,hk'.trans hk,hgrow,hp⟩

private def projection (res : Evm.Out) : Evm.Machine :=
  match res with
  | .ok m _ => m
  | _ => Evm.Machine.init
attribute [irreducible] projection

private theorem projection_success (res : Evm.Out) (h : ∃ m, res = .ok m 0) :
    res = .ok (projection res) 0 := by
  obtain ⟨m,hm⟩ := h
  cases hm
  unfold projection
  rfl

/-- Finite diagnostic projection; successful target_run is proved separately. -/
def target (escape : Bool) : Evm.Machine :=
  projection (Evm.run (cert escape).code prefixMachine)
attribute [irreducible] target

theorem target_run (escape : Bool) :
    Evm.run (cert escape).code prefixMachine = .ok (target escape) 0 := by
  have h : ∃ m, Evm.run (cert escape).code prefixMachine = .ok m 0 := by
    obtain ⟨base,m',base',ht,ht',hr,hbase,hk,hgrow,hpacket⟩ := completed escape
    exact ⟨m',ht'⟩
  unfold target
  exact projection_success _ h


theorem target_observation (escape : Bool) :
    (WordArrayPacket.localObservation (target escape) 1 (.here : Idx Output (.mem bytesR))).map
      AbiEntry.encodeArgs = some (packet escape) := by
  cases escape <;> decide +kernel

theorem target_fields :
    (target false).mem 4 = w[259] ∧ (target true).mem 4 = w[264] ∧
    (target false).mem 259 = w[3] ∧ (target true).mem 264 = w[3] ∧
    (target false).mem 261 = w[300] ∧ (target true).mem 266 = w[300] ∧
    (target false).mem 2 = w[256] ∧ (target true).mem 2 = w[256] ∧
    (target false).mem 3 = w[259] ∧ (target true).mem 3 = w[259] ∧
    (target false).mem 256 = w[2] ∧ (target true).mem 256 = w[2] ∧
    (target false).mem 257 = w[161] ∧ (target true).mem 257 = w[161] ∧
    (target false).mem 258 = w[178] ∧ (target true).mem 258 = w[178] ∧
    (target false).mem 1 = w[42] ∧ (target true).mem 1 = w[42] ∧
    (target false).mem 127 = w[99] ∧ (target true).mem 127 = w[99] ∧
    (target false).store (.root 0) = 9 ∧ (target true).store (.root 0) = 9 := by
  decide +kernel

/-- The old BYTE observer still refuses300; the new WORD packet retains01,2c. -/
theorem range_and_order :
    ReturnedBytes.localBytes (target false) 1 (.here : Idx Output (.mem bytesR)) = none ∧
    ReturnedBytes.localBytes (target true) 1 (.here : Idx Output (.mem bytesR)) = none ∧
    (packet false).length = 160 ∧ (packet true).length = 160 ∧
    ((packet false).drop 96).take 32 = AbiEntry.wordBytes 300 ∧
    ((packet false).drop 126).take 2 = [1,44] ∧
    packet false ≠ packet true ∧
    ((packet false).drop 32).take 32 ≠ AbiEntry.wordBytes 2 ∧
    ((packet false).take 32) ≠ AbiEntry.wordBytes 64 := by decide +kernel

/-- The wrong pointer yields a different well-typed empty observer value; shortening a
header changes the observation. These reject claims, not new ABI profiles. -/
theorem wrong_pointer_header :
    (WordArrayPacket.arrayObservation (target false) 263).map AbiEntry.encodeArgs =
      some (AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes 0) ∧
    (WordArrayPacket.arrayObservation (target false) 263).map AbiEntry.encodeArgs ≠
      some (packet false) ∧
    (WordArrayPacket.arrayObservation
      {target false with mem := fun a => if a = 259 then w[2] else (target false).mem a} 259).map
        AbiEntry.encodeArgs ≠ some (packet false) := by decide +kernel

/-- A symbolic slot is outside the numeric uint observer, never silently a byte. -/
theorem symbolic_cell :
    (WordArrayPacket.arrayObservation
      {target false with mem := fun a => if a = 261 then .slot (.root 0) else (target false).mem a}
      259).isNone = true := by decide +kernel


/-- info: 'Solidity.Backend.AbiWorld.WordArrayControls.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms application
/-- info: 'Solidity.Backend.AbiWorld.WordArrayControls.completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms completed
/-- info: 'Solidity.Backend.AbiWorld.WordArrayControls.target_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms target_run
/-- info: 'Solidity.Backend.AbiWorld.WordArrayControls.target_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms target_observation
/-- info: 'Solidity.Backend.AbiWorld.WordArrayControls.target_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms target_fields
/-- info: 'Solidity.Backend.AbiWorld.WordArrayControls.range_and_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms range_and_order
/-- info: 'Solidity.Backend.AbiWorld.WordArrayControls.wrong_pointer_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_pointer_header
/-- info: 'Solidity.Backend.AbiWorld.WordArrayControls.symbolic_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms symbolic_cell

end Solidity.Backend.AbiWorld.WordArrayControls
