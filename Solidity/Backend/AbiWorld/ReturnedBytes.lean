import Solidity.Backend.AbiWorld.CompiledMemoryCalls

/-! Complete observations of represented uint-array word cells. This is a
partial memory observer, not an ABI decoder or byte-addressed EVM semantics.
Byte-range premises restrict observation only, never compiler admission. -/
namespace Solidity.Backend.AbiWorld.ReturnedBytes
open Evm Evm.Memory

/-- Reject symbolic slots and words outside the byte range; never truncate. -/
def byteCell : Evm.Word → Option UInt8
  | .val v => if v.val < 256 then some (UInt8.ofNat v.val) else none
  | .slot _ => none

/-- Read every cell in order, at arbitrary word-cell start and length. -/
def cells (m : Machine) : Nat → Nat → Option (List UInt8)
  | _, 0 => some []
  | start, n + 1 => do
    let b ← byteCell (m.mem start)
    let bs ← cells m (start + 1) n
    pure (b :: bs)

def arrayBytes (m : Machine) (ptr : Nat) : Option (List UInt8) :=
  match m.mem ptr with
  | .val n => cells m (ptr + 1) n.val
  | .slot _ => none

def localBytes {Γ : Ctx} (m : Machine) (b : Nat) (i : Idx Γ (.mem bytesR)) : Option (List UInt8) :=
  match m.mem (cellOf b i) with
  | .val ptr => arrayBytes m ptr.val
  | .slot _ => none

def payload {H : HTy} (hp : Heap H) (r : HRef H bytesR) : List UInt8 :=
  (hp.get r).1.map (fun v => UInt8.ofNat v.1.toNat)

def ByteRange {H : HTy} (hp : Heap H) (r : HRef H bytesR) : Prop :=
  ∀ v ∈ (hp.get r).1, v.1.toNat < 256

theorem payload_length {H : HTy} (hp : Heap H) (r : HRef H bytesR) :
    (payload hp r).length = hp.len r .dyn := by
  simp only [payload, Heap.len, MObj.elems_dyn, List.length_map]

/-- Within the observational range premise even the natural values are exact;
no modulo conversion or dropped cell is hidden by the UInt8 payload type. -/
theorem payload_values {H : HTy} {hp : Heap H} {r : HRef H bytesR} (hb : ByteRange hp r) :
    (payload hp r).map UInt8.toNat = (hp.get r).1.map (fun v => v.1.toNat) := by
  simp only [payload, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro v hv
  exact UInt8.toNat_ofNat_of_lt' (hb v hv)

private theorem cells_complete (m : Machine) (vs : List PrimTy.uint.Denote) (start : Nat)
    (hr : ∀ i v, vs[i]? = some v → ReprV .uint v (m.mem (start + i)))
    (hb : ∀ v ∈ vs, v.1.toNat < 256) :
    cells m start vs.length = some (vs.map (fun v => UInt8.ofNat v.1.toNat)) := by
  induction vs generalizing start with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨a, ha, hv, hw⟩ := ReprV.uint_inv (hr 0 v rfl)
    have hn : v.1.toNat = a := by rw [hv]; rfl
    have hb0 : a < 256 := by rw [← hn]; exact hb v (List.mem_cons_self)
    have ht : cells m (start + 1) vs.length = some (vs.map (fun v => UInt8.ofNat v.1.toNat)) := by
      apply ih
      · intro i x hx
        have hh := hr (i + 1) x (by simpa only [List.getElem?_cons_succ] using hx)
        simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hh
      · intro x hx; exact hb x (List.mem_cons_of_mem v hx)
    simp only [Nat.add_zero] at hw
    simp only [List.length_cons, cells, hw, byteCell, hb0, ite_true, ht, pure, hn, List.map_cons]
    rfl

/-- All elements and the header, with no fixed length or starting address. -/
theorem array_complete {H : HTy} {hp : Heap H} {r : HRef H bytesR}
    {ptr : Fin W} {m : Machine} (hr : ArrayRepr hp r ptr m) (hb : ByteRange hp r) :
    m.mem ptr.val = .val (wmod (hp.len r .dyn)) ∧
    ptr.val + 1 + hp.len r .dyn ≤ W ∧
    arrayBytes m ptr.val = some (payload hp r) ∧
    (payload hp r).length = hp.len r .dyn := by
  refine ⟨hr.length, hr.space, ?_, ?_⟩
  · rw [arrayBytes, hr.length, wmod_of_lt (hp.len_dyn_lt r)]
    simp only [Heap.len, MObj.elems_dyn, payload]
    apply cells_complete
    · intro i v hv; exact hr.elements i v (by simpa only [MObj.elems_dyn] using hv)
    · exact hb
  · simp only [payload, Heap.len, MObj.elems_dyn, List.length_map]

/-- Offsets are independent: two actual representations of the same source
array give the same complete bytes at arbitrary, possibly different bases. -/
theorem independent_addresses {H : HTy} {hp : Heap H} {r : HRef H bytesR}
    {a b : Fin W} {m n : Machine} (ha : ArrayRepr hp r a m)
    (hb : ArrayRepr hp r b n) (hbyte : ByteRange hp r) :
    arrayBytes m a.val = arrayBytes n b.val :=
  (array_complete ha hbyte).2.2.1.trans (array_complete hb hbyte).2.2.1.symm

/-- Changes outside the represented header/complete element interval cannot
alter observation; this uses actual ArrayRepr, not a new memory semantics. -/
theorem interval_noninterference {H : HTy} {hp : Heap H} {r : HRef H bytesR}
    {a : Fin W} {m n : Machine} (ha : ArrayRepr hp r a m) (hbyte : ByteRange hp r)
    (heq : ∀ addr, a.val ≤ addr → addr < a.val + 1 + hp.len r .dyn → n.mem addr = m.mem addr) :
    arrayBytes n a.val = some (payload hp r) := by
  have hn : ArrayRepr hp r a n := by
    refine ⟨ha.space, ?_, ?_⟩
    · exact (heq a.val (by omega) (by omega)).trans ha.length
    · intro i v hv
      have hi : i < hp.len r .dyn := (List.getElem?_eq_some_iff.mp hv).1
      rw [heq (a.val + 1 + i) (by omega) (by omega)]
      exact ha.elements i v hv
  exact (array_complete hn hbyte).2.2.1

/-- The actual local pointer selects its represented object; no assumed pointer
or replacement heap relation is introduced. Struct clauses remain in StateRepr. -/
theorem local_complete {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (hs : StateRepr L b frame F σ base m) (i : Idx Γ (.mem bytesR))
    (r : HRef σ.H bytesR) (hi : TEnv.get i σ.env = some r) (hb : ByteRange σ.heap r) :
    m.mem (cellOf b i) = .val (base r.id) ∧
    m.mem (base r.id).val = .val (wmod (σ.heap.len r .dyn)) ∧
    localBytes m b i = some (payload σ.heap r) ∧
    frame ≤ (base r.id).val ∧ (base r.id).val + 1 + σ.heap.len r .dyn ≤ W := by
  obtain ⟨s, hget, hptr⟩ := hs.pointers i
  rw [hi] at hget
  cases hget
  have ha := array_complete (hs.heap.arrays r) hb
  exact ⟨hptr, ha.1, by rw [localBytes, hptr]; exact ha.2.2.1,
    hs.heap.above r, ha.2.1⟩

/-- Uniform payload/offset/length/padding/catch facts of the existing Error codec.
The list need only fit the existing uint length; no canonical calldata claim. -/
theorem error_observations (bs : List UInt8) (hlen : bs.length < 2 ^ 256) :
    Source.errorData bs = Semantics.encodeError bs ∧
    ((Source.errorData bs).drop 4).take 32 = Semantics.wordBytes 32 ∧
    ((Source.errorData bs).drop 36).take 32 = Semantics.wordBytes bs.length ∧
    ((Source.errorData bs).drop 68).take bs.length = bs ∧
    (Source.errorData bs).drop (68 + bs.length) =
      List.replicate ((32 - bs.length % 32) % 32) 0 ∧
    CatchKind.reason.decode (Source.errorData bs) = some bs := by
  rw [PublishedLayout.source_error_bytes]
  refine ⟨rfl, error_offset bs, error_length_word bs, error_payload bs, ?_, ?_⟩
  · rw [← List.drop_drop, error_tail, padded_suffix]
  · exact catch_error bs (by simpa only [show 256 ^ 32 = 2 ^ 256 from by decide +kernel] using hlen)

/-- Error packets retain their actual class; this is not a claim that
arbitrary noncanonical calldata offsets or other packets must be refused. -/
theorem error_not_panic (bs : List UInt8) :
    Semantics.decodePanic (Source.errorData bs) = none := by
  rw [PublishedLayout.source_error_bytes]
  have hs : (Semantics.encodeError bs).take 4 = Semantics.errorSelector := by
    simp only [Semantics.encodeError, List.append_assoc]
    exact List.take_left' (by decide +kernel)
  have hn : Semantics.errorSelector ≠ Semantics.panicSelector := by decide +kernel
  simp only [Semantics.decodePanic, hs, hn, false_and, ite_false]

/-- Zero pushes is an actual field of the published memory-call certificate. -/
theorem memory_call_pushes_zero {C : Contract} {Γ Δ : Ctx} {b : Nat} {F : Frag Γ}
    {P : Prog C Γ Δ} (c : Compiler.Compilation b F P) (hc : c.isMemoryCalls = true) :
    Evm.Prog.pushes P = 0 := by
  cases c with
  | core _ _ => cases hc
  | memory _ => cases hc
  | referenceArrays _ => cases hc
  | objects _ => cases hc
  | construction _ => cases hc
  | memoryCalls _ hz => exact hz
  | memoryLoops _ => cases hc
  | memoryLoopScopes _ => cases hc

/-- Consume actual public compiler correctness, retain all frame/allocator/base
relations, then observe the complete returned object and existing Error codec. -/
theorem compiled_return {C : Contract} {Γ Δ : Ctx} {b L frame : Nat} {F : Frag Γ}
    {P : Prog C Γ Δ} (c : Compiler.Compilation b F P) (hc : c.isMemoryCalls = true)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hinput : c.Input L frame base σ m) (hpay : Evm.Prog.pays P = false)
    (o : Solidity.Out C σ.H Δ) (hrun : P.run σ = .ok o)
    (i : Idx Δ (.mem bytesR)) (r : HRef o.st.H bytesR)
    (hget : TEnv.get i o.st.env = some r) (hb : ByteRange o.st.heap r) :
    ∃ m' base', Evm.run c.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      StateRepr L b frame c.frag o.st base' m' ∧
      BaseExtends σ.H base base' ∧
      GrowsAllocator b frame (c.allocationCost σ) σ base m o.st base' m' ∧
      localBytes m' b i = some (payload o.st.heap r) ∧
      (localBytes m' b i).bind (fun bs => CatchKind.reason.decode (Source.errorData bs)) =
        some (payload o.st.heap r) := by
  obtain ⟨m', base', ht, hk, hs, hbase, hg⟩ :=
    CompiledMemoryCalls.completed_transport c hc hinput hpay o hrun
  rw [memory_call_pushes_zero c hc, Nat.add_zero] at hs
  have hl := (local_complete hs i r hget hb).2.2.1
  refine ⟨m', base', ht, hk, hs, hbase, hg, hl, ?_⟩
  rw [hl, Option.bind_some]
  exact (error_observations _ (by
    rw [(array_complete (hs.heap.arrays r) hb).2.2.2]
    exact o.st.heap.len_dyn_lt r)).2.2.2.2.2

/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytes.payload_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payload_values
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytes.array_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_complete
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytes.independent_addresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms independent_addresses
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytes.interval_noninterference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms interval_noninterference
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytes.local_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_complete
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytes.error_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms error_observations
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytes.error_not_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms error_not_panic
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytes.compiled_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compiled_return

end Solidity.Backend.AbiWorld.ReturnedBytes
