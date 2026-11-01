import Solidity.Backend.AbiWorld.MixedPacket

/-! Two current represented uint arrays through the existing intrinsic codec.
Tuple heads/tails are observations of AbiEntry.encodeArgs, not a replacement
encoder, a runtime memory reader, or a word/byte machine relation. Aliases may
be equal; no array disjointness premise is introduced. -/
namespace Solidity.Backend.AbiWorld.ArrayPairPacket
open Evm Evm.Memory InternalFlow
abbrev Shapes := [WordArrayPacket.Shape,WordArrayPacket.Shape]
abbrev Values := AbiEntry.Vals Shapes

/-- Concatenate the existing intrinsic typed tuples, preserving both indices. -/
def append {ss ts : List AbiEntry.Shape} (vs : AbiEntry.Vals ss) (ws : AbiEntry.Vals ts) :
    AbiEntry.Vals (ss ++ ts) :=
  AbiEntry.Vals.casesOn (motive_3 := fun ss _ => AbiEntry.Vals ts → AbiEntry.Vals (ss ++ ts)) vs
    (fun ws => ws) (fun v tail ws => .cons v (append tail ws)) ws
termination_by structural vs

def values (xs ys : List PrimTy.uint.Denote) : Values :=
  append (WordArrayPacket.values xs) (WordArrayPacket.values ys)

/-- The REAL existing array codec payload, not another serialization. -/
def payload (xs : List PrimTy.uint.Denote) : List UInt8 :=
  AbiEntry.Val.enc (.array (WordArrayPacket.sequence xs))

/-- Real two-member head length plus the first actual encoded dynamic tail.
This natural byte offset may exceed W for raw large lists; heap length<W does
not prove nonwrapping byte offsets or Source ABI admission. -/
def secondOffset (xs : List PrimTy.uint.Denote) : Nat := 64 + (payload xs).length

theorem head_size : AbiEntry.Shape.headsSize Shapes = 64 := rfl

theorem payload_length (xs : List PrimTy.uint.Denote) :
    (payload xs).length = 32 + 32 * xs.length := by
  have word_lengths : (xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat)).length = 32 * xs.length := by
    induction xs with
    | nil => rfl
    | cons v xs ih =>
      simp only [List.flatMap_cons,List.length_append,MixedPacket.word_length,ih,List.length_cons]
      omega
  rw [payload,MixedPacket.array_encoding]
  simp only [List.length_append,MixedPacket.word_length,word_lengths]

theorem second_offset (xs : List PrimTy.uint.Denote) :
    secondOffset xs = 96 + 32 * xs.length := by
  rw [secondOffset,payload_length]
  omega

theorem offset_alignment (xs : List PrimTy.uint.Denote) :
    96 ≤ secondOffset xs ∧ secondOffset xs % 32 = 0 := by
  rw [second_offset]
  omega

/-- Both dynamic offsets come from the actual assemble recursion. The second
is NEVER supplied as a desired packet or assumed constant. -/
theorem encoded_values (xs ys : List PrimTy.uint.Denote) :
    AbiEntry.encodeArgs (values xs ys) = AbiEntry.wordBytes 64 ++
      AbiEntry.wordBytes (secondOffset xs) ++ payload xs ++ payload ys := by
  change AbiEntry.assemble [(true,payload xs),(true,payload ys)] = _
  simp only [AbiEntry.assemble,List.foldl_cons,List.foldl_nil,ite_true,Nat.zero_add,
    AbiEntry.assemble.go,List.append_nil,List.nil_append,secondOffset,List.append_assoc]

theorem encoded_words (xs ys : List PrimTy.uint.Denote) :
    AbiEntry.encodeArgs (values xs ys) = AbiEntry.wordBytes 64 ++
      AbiEntry.wordBytes (96 + 32 * xs.length) ++ AbiEntry.wordBytes xs.length ++
      xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++ AbiEntry.wordBytes ys.length ++
      ys.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) := by
  rw [encoded_values,second_offset,payload,payload,MixedPacket.array_encoding,MixedPacket.array_encoding]
  simp only [List.append_assoc]

theorem encoded_length (xs ys : List PrimTy.uint.Denote) :
    (AbiEntry.encodeArgs (values xs ys)).length = 128 + 32 * (xs.length + ys.length) := by
  rw [encoded_values]
  simp only [List.length_append,MixedPacket.word_length,payload_length]
  omega

/-- The first tail's exact bytes are unaffected by changing the second value,
including when runtime references are equal. This is codec noninterference,
not a claim that heap writes through one alias leave another alias unchanged. -/
theorem first_prefix (xs ys : List PrimTy.uint.Denote) :
    (AbiEntry.encodeArgs (values xs ys)).take (secondOffset xs) =
      AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes (secondOffset xs) ++ payload xs := by
  rw [encoded_values]
  apply List.take_left'
  simp only [List.length_append,MixedPacket.word_length,secondOffset]

theorem second_tail (xs ys : List PrimTy.uint.Denote) :
    (AbiEntry.encodeArgs (values xs ys)).drop (secondOffset xs) = payload ys := by
  rw [encoded_values]
  apply List.drop_left'
  simp only [List.length_append,MixedPacket.word_length,secondOffset]

theorem first_tail (xs ys : List PrimTy.uint.Denote) :
    ((AbiEntry.encodeArgs (values xs ys)).drop 64).take (payload xs).length = payload xs := by
  have grouped : AbiEntry.encodeArgs (values xs ys) =
      (AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes (secondOffset xs)) ++ (payload xs ++ payload ys) := by
    simpa only [List.append_assoc] using encoded_values xs ys
  rw [grouped,List.drop_left' (by simp only [List.length_append,MixedPacket.word_length] :
    (AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes (secondOffset xs)).length = 64),List.take_left]

theorem head_slices (xs ys : List PrimTy.uint.Denote) :
    (AbiEntry.encodeArgs (values xs ys)).take 32 = AbiEntry.wordBytes 64 ∧
    ((AbiEntry.encodeArgs (values xs ys)).drop 32).take 32 = AbiEntry.wordBytes (secondOffset xs) := by
  constructor
  · rw [encoded_values]
    simp only [List.append_assoc]
    exact List.take_left' (MixedPacket.word_length 64)
  · rw [encoded_values]
    simp only [List.append_assoc]
    rw [List.drop_left' (MixedPacket.word_length 64)]
    exact List.take_left' (MixedPacket.word_length (secondOffset xs))

theorem prefix_noninterference (xs ys zs : List PrimTy.uint.Denote) :
    (AbiEntry.encodeArgs (values xs ys)).take (secondOffset xs) =
      (AbiEntry.encodeArgs (values xs zs)).take (secondOffset xs) := by
  rw [first_prefix,first_prefix]

def localObservation {Γ : Ctx} (m : Machine) (b : Nat)
    (i j : Idx Γ (.mem bytesR)) : Option Values := do
  let xs ← WordArrayPacket.localObservation m b i
  let ys ← WordArrayPacket.localObservation m b j
  pure (append xs ys)

/-- SAME reached representation, with no i≠j or r≠s hypothesis. -/
theorem state_complete {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (i j : Idx Γ (.mem bytesR))
    (r s : HRef σ.H bytesR) (hr : TEnv.get i σ.env = some r) (hs : TEnv.get j σ.env = some s) :
    localObservation m b i j = some (values (σ.heap.get r).1 (σ.heap.get s).1) := by
  simp only [localObservation,(WordArrayPacket.local_complete repr i r hr).2.2.1,
    (WordArrayPacket.local_complete repr j s hs).2.2.1,bind,Option.bind_some,pure,values]

/-- Both retained caller references keep their entry addresses while BOTH
payloads come from the current reached heap. Equal old references are permitted. -/
theorem captured {C : Contract} {Γ Ξ : Ctx} {L b frame : Nat} {F : Frag Γ}
    {σ : State C Γ} (out : Solidity.Out C σ.H Γ) (h : Thin Ξ Γ)
    (capture : TEnv.thin h out.st.env = TEnv.wk out.ext Ξ (TEnv.thin h σ.env))
    {base base' : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F out.st base' m) (addresses : BaseExtends σ.H base base')
    (i j : Idx Ξ (.mem bytesR)) (r s : HRef σ.H bytesR)
    (hr : TEnv.get (i.wk h) σ.env = some r) (hs : TEnv.get (j.wk h) σ.env = some s) :
    m.mem (cellOf b (i.wk h)) = .val (base r.id) ∧
    m.mem (cellOf b (j.wk h)) = .val (base s.id) ∧
    localObservation m b (i.wk h) (j.wk h) =
      some (values (out.st.heap.get (r.wk out.ext)).1 (out.st.heap.get (s.wk out.ext)).1) ∧
    (out.st.heap.get (r.wk out.ext)).1.length < AbiEntry.W ∧
    (out.st.heap.get (s.wk out.ext)).1.length < AbiEntry.W := by
  have first := CallerPacket.captured out h capture repr addresses i r hr
  have last := CallerPacket.captured out h capture repr addresses j s hs
  exact ⟨first.1,last.1,state_complete repr (i.wk h) (j.wk h) (r.wk out.ext) (s.wk out.ext)
    (CallerView.reference out h capture i r hr) (CallerView.reference out h capture j s hs),
    WordArrayPacket.heap_length out.st.heap (r.wk out.ext),WordArrayPacket.heap_length out.st.heap (s.wk out.ext)⟩

/-- Two retained aliases through the actual selected compiled call/tail. The
only Disjoint guard is the original return-destination/caller-view guard, NOT
an array-separation assumption. Equal references and equal indices are allowed. -/
theorem selected {C : Contract} {b L frame : Nat} {Γ Δ Ε Ξ rs ps Γf : Ctx}
    {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ} {F : Frag Γ}
    {body : Prog C (rs ++ ps) Γf} {tail : Prog C Δ Ε}
    (h : Thin Ξ Γ) (separate : CallerFrame.Disjoint h ret)
    (within : Prog.withinM .nonpayable tail = true)
    (unwritten : ∀ (t : LTy) (j : Idx Ξ t),
      (t,((j.wk h).ext ret.ext).toNat) ∉ Prog.writesAt 0 tail)
    (condition : Val C Γ .bool) (pre post : List (DispatchArm C Γ)) (fail : Stmt C Γ Γ)
    (compiled : Calls.Statement b F
      (DispatchArm.chain (pre ++ ⟨condition,.cons (.call f args ret body) tail⟩ :: post) fail))
    (σ : State C Γ) (miss : ∀ a ∈ pre, a.cond.evalT σ = .ok false)
    (hit : condition.evalT σ = .ok true) (out : Solidity.Out C σ.H Ε)
    (executed : (Prog.cons (.call f args ret body) tail).run σ = .ok out)
    {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (room : b + compiled.need ≤ frame)
    (capacity : AllocationInput b frame (compiled.cost σ) σ base m)
    (i : Idx Ξ (.mem bytesR)) (r : HRef σ.H bytesR)
    (old : TEnv.get (i.wk h) σ.env = some r)
    (j : Idx Ξ (.mem bytesR)) (s : HRef σ.H bytesR)
    (other : TEnv.get (j.wk h) σ.env = some s) :
    ∃ m' base', Evm.run compiled.code m = .ok m' 0 ∧
      StateRepr L b frame compiled.frag (out.st.drop (ret.ext.trans tail.ext)) base' m' ∧
      m'.stack = m.stack ∧ BaseExtends σ.H base base' ∧
      GrowsAllocator b frame (compiled.cost σ) σ base m
        (out.st.drop (ret.ext.trans tail.ext)) base' m' ∧
      m'.mem (cellOf b (i.wk h)) = .val (base r.id) ∧
      m'.mem (cellOf b (j.wk h)) = .val (base s.id) ∧
      localObservation m' b (i.wk h) (j.wk h) =
        some (values (out.st.heap.get (r.wk out.ext)).1 (out.st.heap.get (s.wk out.ext)).1) ∧
      (localObservation m' b (i.wk h) (j.wk h)).map AbiEntry.encodeArgs =
        some (AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes (secondOffset (out.st.heap.get (r.wk out.ext)).1) ++
          payload (out.st.heap.get (r.wk out.ext)).1 ++ payload (out.st.heap.get (s.wk out.ext)).1) ∧
      (out.st.heap.get (r.wk out.ext)).1.length < AbiEntry.W ∧
      (out.st.heap.get (s.wk out.ext)).1.length < AbiEntry.W := by
  obtain ⟨m',base',target,reached,stack,addresses,growth,pointer,observed,packet⟩ :=
    CallerPacket.selected h separate within unwritten condition pre post fail compiled
      σ miss hit out executed repr room capacity i r old
  have capture := CallerTail.environment h separate within unwritten executed
  have pair := captured
    (⟨out.st.drop (ret.ext.trans tail.ext),out.ext⟩ : Solidity.Out C σ.H Γ)
    h capture reached addresses i j r s old other
  have bytes := congrArg (Option.map AbiEntry.encodeArgs) pair.2.2.1
  rw [Option.map_some,encoded_values] at bytes
  exact ⟨m',base',target,reached,stack,addresses,growth,pair.1,pair.2.1,pair.2.2.1,
    bytes,pair.2.2.2.1,pair.2.2.2.2⟩

/-- info: 'Solidity.Backend.AbiWorld.ArrayPairPacket.payload_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payload_length
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairPacket.second_offset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms second_offset
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairPacket.offset_alignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms offset_alignment
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairPacket.encoded_values' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_values
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairPacket.encoded_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_words
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairPacket.encoded_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_length
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairPacket.first_prefix' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms first_prefix
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairPacket.first_tail' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms first_tail
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairPacket.second_tail' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms second_tail
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairPacket.state_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms state_complete
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairPacket.captured' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms captured
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairPacket.head_slices' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms head_slices
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairPacket.prefix_noninterference' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_noninterference
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairPacket.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
end Solidity.Backend.AbiWorld.ArrayPairPacket
