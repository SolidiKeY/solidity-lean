import Solidity.Backend.AbiWorld.ReturnedBytes
import Solidity.Backend.AbiWorld.PacketEmission
import Solidity.Backend.Scalar.Typed

/-! Complete numeric-word observations of actual represented uint arrays,
transported to the published typed ABI codec. This is a memory observer and
value-specialized packet adapter, NOT emitted runtime memory-reading code or
a relation identifying symbolic word-cell memory with byte-addressed memory. -/
namespace Solidity.Backend.AbiWorld.WordArrayPacket
open Evm Evm.Memory

abbrev UIntWord := AbiEntry.Word (.uint 256)
abbrev Shape := AbiEntry.Shape.array (.word (.uint 256))
abbrev Values := AbiEntry.Vals [Shape]

/-- Reuse the published scalar encoding and its full-word range. No byte bound. -/
def uintWord (v : PrimTy.uint.Denote) : UIntWord :=
  ⟨(Backend.Scalar.encodeValue .uint v).toNat,
    by simpa only [AbiEntry.W_eq] using (Backend.Scalar.encodeValue .uint v).isLt,
    decide_eq_true (Backend.Scalar.encodeValue .uint v).isLt⟩

theorem uintWord_value (v : PrimTy.uint.Denote) : (uintWord v).val = v.val.toNat :=
  Backend.Scalar.encode_uint_toNat v

def finWord (v : Fin Evm.W) : UIntWord :=
  ⟨v.val, by simpa only [AbiEntry.W_eq] using v.isLt, decide_eq_true v.isLt⟩

private theorem word_ext (x y : UIntWord) (h : x.val = y.val) : x = y := by
  cases x; cases y; cases h; rfl

/-- Construction follows the source list, preserving its exact indexed length. -/
def sequence : (vs : List PrimTy.uint.Denote) → AbiEntry.Seq (.word (.uint 256)) vs.length
  | [] => .nil
  | v :: vs => .cons (.word (uintWord v)) (sequence vs)

def values (vs : List PrimTy.uint.Denote) : Values := .cons (.array (sequence vs)) .nil

/-- Observe existing word cells. Symbolic slots are outside this numeric view;
actual ArrayRepr supplies numeric words for every uint element. -/
def readWords (m : Evm.Machine) : (n : Nat) → Nat → Option (AbiEntry.Seq (.word (.uint 256)) n)
  | 0, _ => some .nil
  | n + 1, a => do
    let v ← match m.mem a with
      | .val w => some (finWord w)
      | .slot _ => none
    let rest ← readWords m n (a + 1)
    pure (.cons (.word v) rest)

def arrayObservation (m : Evm.Machine) (ptr : Nat) : Option Values :=
  match m.mem ptr with
  | .val n => do
    let xs ← readWords m n.val (ptr + 1)
    pure (.cons (.array xs) .nil)
  | .slot _ => none

def localObservation {Γ : Ctx} (m : Evm.Machine) (b : Nat)
    (i : Idx Γ (.mem bytesR)) : Option Values :=
  match m.mem (cellOf b i) with
  | .val ptr => arrayObservation m ptr.val
  | .slot _ => none

private theorem read_complete (m : Evm.Machine) (vs : List PrimTy.uint.Denote) (start : Nat)
    (hr : ∀ i v, vs[i]? = some v → ReprV .uint v (m.mem (start + i))) :
    readWords m vs.length start = some (sequence vs) := by
  induction vs generalizing start with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨a, ha, hv, hw⟩ := ReprV.uint_inv (hr 0 v rfl)
    have he : finWord ⟨a,ha⟩ = uintWord v := by
      apply word_ext
      change a = (Backend.Scalar.encodeValue .uint v).toNat
      rw [Backend.Scalar.encode_uint_toNat, hv]
      rfl
    have ht : readWords m vs.length (start + 1) = some (sequence vs) := by
      apply ih
      intro i x hx
      have h := hr (i + 1) x (by simpa only [List.getElem?_cons_succ] using hx)
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using h
    simp only [Nat.add_zero] at hw
    simp only [List.length_cons, readWords, hw, he, ht, Option.bind_some,
      pure, sequence, bind, Option.bind_some]

/-- No ByteRange premise: every represented uint, including300/max-word, is
retained as a complete typed ABI WORD, not truncated to one byte. -/
theorem array_complete {H : HTy} {hp : Heap H} {r : HRef H bytesR}
    {ptr : Fin Evm.W} {m : Evm.Machine} (hr : ArrayRepr hp r ptr m) :
    arrayObservation m ptr.val = some (values (hp.get r).1) := by
  rw [arrayObservation, hr.length, wmod_of_lt (hp.len_dyn_lt r)]
  simp only [Heap.len, MObj.elems_dyn, values]
  rw [read_complete m (hp.get r).1 (ptr.val + 1) (fun i v hv =>
    hr.elements i v (by simpa only [MObj.elems_dyn] using hv))]
  rfl

/-- The actual returned local pointer and header/space are retained. -/
theorem local_complete {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hs : StateRepr L b frame F σ base m) (i : Idx Γ (.mem bytesR))
    (r : HRef σ.H bytesR) (hi : TEnv.get i σ.env = some r) :
    m.mem (cellOf b i) = .val (base r.id) ∧
    m.mem (base r.id).val = .val (wmod (σ.heap.len r .dyn)) ∧
    localObservation m b i = some (values (σ.heap.get r).1) ∧
    frame ≤ (base r.id).val ∧ (base r.id).val + 1 + σ.heap.len r .dyn ≤ Evm.W := by
  obtain ⟨s,hget,hptr⟩ := hs.pointers i
  rw [hi] at hget
  cases hget
  exact ⟨hptr,(hs.heap.arrays r).length,
    by rw [localObservation,hptr]; exact array_complete (hs.heap.arrays r),
    hs.heap.above r,(hs.heap.arrays r).space⟩

/-- This POST-execution adapter emits the observed value as a literal packet.
It does not compile unknown runtime memory reads. The two machine models and
address units remain distinct. -/
def observedPacket {Γ : Ctx} (m : Evm.Machine) (b : Nat) (i : Idx Γ (.mem bytesR))
    (a : Nat) (suffix : Backend.Program) (bm : Backend.Failure.Slice.Machine) :=
  (localObservation m b i).bind (fun vs => Backend.Failure.Slice.checkedRun
    (PacketEmission.emitResult a vs ++ suffix) bm)

theorem execute_observed {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hs : StateRepr L b frame F σ base m) (i : Idx Γ (.mem bytesR))
    (r : HRef σ.H bytesR) (hi : TEnv.get i σ.env = some r)
    (a : Nat) (suffix : Backend.Program) (bm : Backend.Failure.Slice.Machine)
    (fits : Backend.Failure.Fits a (AbiEntry.encodeArgs (values (σ.heap.get r).1)))
    (stack : bm.stack.length + 2 ≤ 1024) :
    observedPacket m b i a suffix bm =
      some ({bm with memory := (Backend.Failure.Slice.putBytes bm.memory a (AbiEntry.encodeArgs (values (σ.heap.get r).1)))},
        some (.success (AbiEntry.encodeArgs (values (σ.heap.get r).1)))) := by
  rw [observedPacket,(local_complete hs i r hi).2.2.1,Option.bind_some]
  exact PacketEmission.execute_result a _ suffix bm fits stack

/-- Actual public compiler correctness supplies the returned representation;
the complete uint-word observer then retains every typed value. -/
theorem compiled_observation {C : Contract} {Γ Δ : Ctx} {b L frame : Nat} {F : Frag Γ}
    {P : Prog C Γ Δ} (c : Compiler.Compilation b F P) (hc : c.isMemoryCalls = true)
    {base : Nat → Fin Evm.W} {σ : State C Γ} {m : Evm.Machine}
    (hi : c.Input L frame base σ m) (hp : Evm.Prog.pays P = false)
    (o : Solidity.Out C σ.H Δ) (hrun : P.run σ = .ok o)
    (i : Idx Δ (.mem bytesR)) (r : HRef o.st.H bytesR)
    (hget : TEnv.get i o.st.env = some r) :
    ∃ m' base', Evm.run c.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      StateRepr L b frame c.frag o.st base' m' ∧ BaseExtends σ.H base base' ∧
      GrowsAllocator b frame (c.allocationCost σ) σ base m o.st base' m' ∧
      localObservation m' b i = some (values (o.st.heap.get r).1) := by
  obtain ⟨m',base',ht,hk,hs,hbase,hgrow⟩ :=
    CompiledMemoryCalls.completed_transport c hc hi hp o hrun
  rw [ReturnedBytes.memory_call_pushes_zero c hc,Nat.add_zero] at hs
  exact ⟨m',base',ht,hk,hs,hbase,hgrow,(local_complete hs i r hget).2.2.1⟩

/-- Source uint values retain complete ordered32-byte words in the real codec. -/
theorem sequence_parts (vs : List PrimTy.uint.Denote) :
    AbiEntry.Seq.parts (sequence vs) =
      vs.map (fun v => (false, AbiEntry.wordBytes v.val.toNat)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [sequence,AbiEntry.Seq.parts,AbiEntry.Val.enc,AbiEntry.Shape.dynamic,
      uintWord_value,List.map_cons,ih]

private theorem static_go (bs : List (List UInt8)) (off : Nat) :
    AbiEntry.assemble.go (bs.map (false, ·)) off = (bs.flatten,[]) := by
  induction bs generalizing off with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons,AbiEntry.assemble.go,ih,Bool.false_eq_true,ite_false,
      List.flatten_cons,List.append_nil]

private theorem static_assemble (bs : List (List UInt8)) :
    AbiEntry.assemble (bs.map (false, ·)) = bs.flatten := by
  simp only [AbiEntry.assemble,static_go,List.append_nil]

/-- Unconditional raw-codec formula: offset32, encoded length, then EVERY
complete source word. Exact nonwrapping length needs vs.length<W (supplied by
actual Core heaps below). Source ABI admission retains its own64-bit/alloc
bounds; this formula neither proves that admission nor changes its refusals. -/
theorem encoded_values (vs : List PrimTy.uint.Denote) :
    AbiEntry.encodeArgs (values vs) = AbiEntry.wordBytes 32 ++
      AbiEntry.wordBytes vs.length ++ vs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) := by
  simp only [values,AbiEntry.encodeArgs,AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,
    AbiEntry.Val.enc,sequence_parts]
  change AbiEntry.assemble [(true,AbiEntry.wordBytes vs.length ++
    AbiEntry.assemble (vs.map (fun v => (false,AbiEntry.wordBytes v.val.toNat))))] = _
  have hs : AbiEntry.assemble (vs.map (fun v => (false,AbiEntry.wordBytes v.val.toNat))) =
      vs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) := by
    simpa only [List.map_map,Function.comp_def,List.flatMap] using
      static_assemble (vs.map (fun v => AbiEntry.wordBytes v.val.toNat))
  rw [hs]
  simp only [AbiEntry.assemble,List.foldl_cons,List.foldl_nil,ite_true,Nat.zero_add,
    AbiEntry.assemble.go,List.append_nil,List.nil_append,List.append_assoc]

/-- Real Core arrays supply the nonwrapping256-bit length bound; this is
separate from Source ABI64-bit allocation/admission conditions. -/
theorem heap_length {H : HTy} (hp : Heap H) (r : HRef H bytesR) :
    (hp.get r).1.length < AbiEntry.W := by
  simpa only [Heap.len,MObj.elems_dyn,AbiEntry.W_eq] using hp.len_dyn_lt r


/-- info: 'Solidity.Backend.AbiWorld.WordArrayPacket.uintWord_value' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms uintWord_value
/-- info: 'Solidity.Backend.AbiWorld.WordArrayPacket.array_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_complete
/-- info: 'Solidity.Backend.AbiWorld.WordArrayPacket.local_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_complete
/-- info: 'Solidity.Backend.AbiWorld.WordArrayPacket.execute_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms execute_observed
/-- info: 'Solidity.Backend.AbiWorld.WordArrayPacket.compiled_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compiled_observation
/-- info: 'Solidity.Backend.AbiWorld.WordArrayPacket.encoded_values' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_values
/-- info: 'Solidity.Backend.AbiWorld.WordArrayPacket.heap_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms heap_length

end Solidity.Backend.AbiWorld.WordArrayPacket
