import Solidity.Backend.AbiWorld.CallerPacket

/-! Heterogeneous dynamic uint-array plus scalar observations using the published
codec. Numeric word-cell observations do not implement a runtime byte encoder,
ABI admission, or a word-memory/byte-memory simulation. -/
namespace Solidity.Backend.AbiWorld.MixedPacket
open Evm Evm.Memory InternalFlow
abbrev ScalarShape := AbiEntry.Shape.word (.uint 256)
abbrev Shapes := [WordArrayPacket.Shape, ScalarShape]
abbrev Values := AbiEntry.Vals Shapes

/-- Append a typed scalar without eliminating the source tuple's intrinsic
shape index. No second encoding or decoding semantics. -/
def snocWord {ss : List AbiEntry.Shape} (vs : AbiEntry.Vals ss)
    (w : WordArrayPacket.UIntWord) : AbiEntry.Vals (ss ++ [ScalarShape]) :=
  AbiEntry.Vals.casesOn (motive_3 := fun ss _ =>
    WordArrayPacket.UIntWord → AbiEntry.Vals (ss ++ [ScalarShape])) vs
    (fun w => .cons (.word w) .nil)
    (fun v tail w => .cons v (snocWord tail w)) w
termination_by structural vs

def values (xs : List PrimTy.uint.Denote) (v : PrimTy.uint.Denote) : Values :=
  snocWord (WordArrayPacket.values xs) (WordArrayPacket.uintWord v)

/-- Observe only the actual existing numeric scalar cell. -/
def scalarObservation {Γ : Ctx} (m : Machine) (b : Nat) (j : Idx Γ (.val .uint)) :
    Option WordArrayPacket.UIntWord :=
  match m.mem (cellOf b j) with
  | .val w => some (WordArrayPacket.finWord w)
  | .slot _ => none

def localObservation {Γ : Ctx} (m : Machine) (b : Nat)
    (i : Idx Γ (.mem bytesR)) (j : Idx Γ (.val .uint)) : Option Values := do
  let xs ← WordArrayPacket.localObservation m b i
  let v ← scalarObservation m b j
  pure (snocWord xs v)

private theorem word_ext (x y : WordArrayPacket.UIntWord) (same : x.val = y.val) : x = y := by
  cases x; cases y; cases same; rfl

theorem scalar_complete {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (j : Idx Γ (.val .uint)) :
    m.mem (cellOf b j) = .val (wmod (TEnv.get j σ.env).val.toNat) ∧
    scalarObservation m b j = some (WordArrayPacket.uintWord (TEnv.get j σ.env)) := by
  obtain ⟨a,ha,hv,hw⟩ := ReprV.uint_inv (repr.core.vals j)
  change (TEnv.get j σ.env).val = (a : Int) at hv
  change m.mem (cellOf b j) = .val ⟨a,ha⟩ at hw
  have value : (TEnv.get j σ.env).val.toNat = a := by rw [hv]; rfl
  have eq : WordArrayPacket.finWord ⟨a,ha⟩ = WordArrayPacket.uintWord (TEnv.get j σ.env) := by
    have same : (WordArrayPacket.finWord ⟨a,ha⟩).val =
        (WordArrayPacket.uintWord (TEnv.get j σ.env)).val := by
      rw [WordArrayPacket.uintWord_value,value]; rfl
    exact word_ext _ _ same
  refine ⟨?_,?_⟩
  · rw [hw,value,wmod_of_lt ha]
  · simp only [scalarObservation,hw,eq]

theorem word_length (n : Nat) : (AbiEntry.wordBytes n).length = 32 := by
  simp only [AbiEntry.wordBytes,List.length_map,List.length_range]

/-- Recover the actual array payload from the established standalone codec law. -/
theorem array_encoding (xs : List PrimTy.uint.Denote) :
    AbiEntry.Val.enc (.array (WordArrayPacket.sequence xs)) =
      AbiEntry.wordBytes xs.length ++ xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) := by
  have encoded := WordArrayPacket.encoded_values xs
  simp only [WordArrayPacket.values,AbiEntry.encodeArgs,AbiEntry.Vals.parts,
    AbiEntry.Shape.dynamic,AbiEntry.assemble,List.foldl_cons,List.foldl_nil,
    ite_true,Nat.zero_add,AbiEntry.assemble.go,List.append_nil,List.nil_append] at encoded
  exact List.append_cancel_left (by simpa only [List.append_assoc] using encoded)

/-- The heterogeneous head size is derived from the published shape layout. -/
theorem head_size : AbiEntry.Shape.headsSize Shapes = 64 := rfl

/-- Raw codec law for every typed scalar and list; no ByteRange premise.
Source admission is separate. Reached heaps supply length<W, not ABI64 bounds. -/
theorem encoded_values (xs : List PrimTy.uint.Denote) (v : PrimTy.uint.Denote) :
    AbiEntry.encodeArgs (values xs v) =
      AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes v.val.toNat ++
      AbiEntry.wordBytes xs.length ++ xs.flatMap (fun x => AbiEntry.wordBytes x.val.toNat) := by
  change AbiEntry.encodeArgs (.cons (.array (WordArrayPacket.sequence xs))
    (.cons (.word (WordArrayPacket.uintWord v)) .nil)) = _
  change AbiEntry.assemble [(true,AbiEntry.Val.enc (.array (WordArrayPacket.sequence xs))),
    (false,AbiEntry.wordBytes (WordArrayPacket.uintWord v).val)] = _
  rw [array_encoding,WordArrayPacket.uintWord_value]
  simp only [AbiEntry.assemble,List.foldl_cons,List.foldl_nil,Bool.false_eq_true,
    ite_false,ite_true,Nat.zero_add,word_length,AbiEntry.assemble.go,
    List.append_nil,List.nil_append,List.append_assoc]

/-- Exact byte length of the existing heterogeneous codec, not a new emitter. -/
theorem encoded_length (xs : List PrimTy.uint.Denote) (v : PrimTy.uint.Denote) :
    (AbiEntry.encodeArgs (values xs v)).length = 96 + 32 * xs.length := by
  have tail_length : (xs.flatMap (fun x => AbiEntry.wordBytes x.val.toNat)).length = 32 * xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.flatMap_cons,List.length_append,word_length,ih,List.length_cons]
      omega
  rw [encoded_values]
  simp only [List.length_append,word_length,tail_length]

theorem state_complete {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (i : Idx Γ (.mem bytesR))
    (r : HRef σ.H bytesR) (reference : TEnv.get i σ.env = some r)
    (j : Idx Γ (.val .uint)) :
    localObservation m b i j = some (values (σ.heap.get r).1 (TEnv.get j σ.env)) := by
  simp only [localObservation,(WordArrayPacket.local_complete repr i r reference).2.2.1,
    (scalar_complete repr j).2,bind,Option.bind_some,pure,values]

/-- Captured primitives remain unchanged while the observed aliased heap is the
CURRENT reached heap. These are different preservation statements. -/
theorem captured {C : Contract} {Γ Ξ : Ctx} {L b frame : Nat} {F : Frag Γ}
    {σ : State C Γ} (out : Solidity.Out C σ.H Γ) (h : Thin Ξ Γ)
    (capture : TEnv.thin h out.st.env = TEnv.wk out.ext Ξ (TEnv.thin h σ.env))
    {base base' : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F out.st base' m) (addresses : BaseExtends σ.H base base')
    (i : Idx Ξ (.mem bytesR)) (r : HRef σ.H bytesR)
    (old : TEnv.get (i.wk h) σ.env = some r) (j : Idx Ξ (.val .uint)) :
    TEnv.get (j.wk h) out.st.env = TEnv.get (j.wk h) σ.env ∧
    m.mem (cellOf b (i.wk h)) = .val (base r.id) ∧
    m.mem (cellOf b (j.wk h)) = .val (wmod (TEnv.get (j.wk h) σ.env).val.toNat) ∧
    localObservation m b (i.wk h) (j.wk h) =
      some (values (out.st.heap.get (r.wk out.ext)).1 (TEnv.get (j.wk h) σ.env)) ∧
    (out.st.heap.get (r.wk out.ext)).1.length < AbiEntry.W := by
  have scalar := congrArg (TEnv.get j) capture
  rw [CallerFrame.read_thin,TEnv.get_wk,CallerFrame.read_thin] at scalar
  change TEnv.get (j.wk h) out.st.env = TEnv.get (j.wk h) σ.env at scalar
  have ref := CallerView.reference out h capture i r old
  have array := CallerPacket.captured out h capture repr addresses i r old
  have numeric := (scalar_complete repr (j.wk h)).1
  have observed := state_complete repr (i.wk h) (r.wk out.ext) ref (j.wk h)
  rw [scalar] at numeric observed
  exact ⟨scalar,array.1,numeric,observed,WordArrayPacket.heap_length out.st.heap (r.wk out.ext)⟩

/-- Actual selected target transport supplies both heterogeneous observations.
Only the captured primitive is unchanged; array values come from the reached heap.
No source ABI admission or runtime byte-memory encoder is asserted. -/
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
    (old : TEnv.get (i.wk h) σ.env = some r) (j : Idx Ξ (.val .uint)) :
    ∃ m' base', Evm.run compiled.code m = .ok m' 0 ∧
      StateRepr L b frame compiled.frag (out.st.drop (ret.ext.trans tail.ext)) base' m' ∧
      m'.stack = m.stack ∧ BaseExtends σ.H base base' ∧
      GrowsAllocator b frame (compiled.cost σ) σ base m
        (out.st.drop (ret.ext.trans tail.ext)) base' m' ∧
      TEnv.get (j.wk h) (TEnv.drop (ret.ext.trans tail.ext) out.st.env) =
        TEnv.get (j.wk h) σ.env ∧
      m'.mem (cellOf b (i.wk h)) = .val (base r.id) ∧
      m'.mem (cellOf b (j.wk h)) = .val (wmod (TEnv.get (j.wk h) σ.env).val.toNat) ∧
      localObservation m' b (i.wk h) (j.wk h) =
        some (values (out.st.heap.get (r.wk out.ext)).1 (TEnv.get (j.wk h) σ.env)) ∧
      (localObservation m' b (i.wk h) (j.wk h)).map AbiEntry.encodeArgs =
        some (AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes (TEnv.get (j.wk h) σ.env).val.toNat ++
          AbiEntry.wordBytes (out.st.heap.get (r.wk out.ext)).1.length ++
          (out.st.heap.get (r.wk out.ext)).1.flatMap (fun v => AbiEntry.wordBytes v.val.toNat)) ∧
      (out.st.heap.get (r.wk out.ext)).1.length < AbiEntry.W := by
  obtain ⟨m',base',target,reached,stack,addresses,growth,pointer,array,packet⟩ :=
    CallerPacket.selected h separate within unwritten condition pre post fail compiled
      σ miss hit out executed repr room capacity i r old
  have capture := CallerTail.environment h separate within unwritten executed
  have cap := captured
    (⟨out.st.drop (ret.ext.trans tail.ext),out.ext⟩ : Solidity.Out C σ.H Γ)
    h capture reached addresses i r old j
  have bytes := congrArg (Option.map AbiEntry.encodeArgs) cap.2.2.2.1
  rw [Option.map_some,encoded_values] at bytes
  exact ⟨m',base',target,reached,stack,addresses,growth,cap.1,cap.2.1,
    cap.2.2.1,cap.2.2.2.1,bytes,cap.2.2.2.2⟩

/-- Generate a literal result packet AFTER observing the word machine. This
separate byte-slice machine is not a runtime word-memory byte encoder. -/
def observedPacket {Γ : Ctx} (m : Machine) (b : Nat)
    (i : Idx Γ (.mem bytesR)) (j : Idx Γ (.val .uint))
    (a : Nat) (suffix : Backend.Program) (bm : Backend.Failure.Slice.Machine) :=
  (localObservation m b i j).bind (fun vs => Backend.Failure.Slice.checkedRun
    (PacketEmission.emitResult a vs ++ suffix) bm)

theorem execute_observed {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (i : Idx Γ (.mem bytesR))
    (r : HRef σ.H bytesR) (reference : TEnv.get i σ.env = some r)
    (j : Idx Γ (.val .uint)) (a : Nat) (suffix : Backend.Program)
    (bm : Backend.Failure.Slice.Machine)
    (fits : Backend.Failure.Fits a (AbiEntry.encodeArgs (values (σ.heap.get r).1 (TEnv.get j σ.env))))
    (stack : bm.stack.length + 2 ≤ 1024) :
    observedPacket m b i j a suffix bm =
      some ({bm with memory := (Backend.Failure.Slice.putBytes bm.memory a
        (AbiEntry.encodeArgs (values (σ.heap.get r).1 (TEnv.get j σ.env))))},
        some (.success (AbiEntry.encodeArgs (values (σ.heap.get r).1 (TEnv.get j σ.env))))) := by
  rw [observedPacket,state_complete repr i r reference j,Option.bind_some]
  exact PacketEmission.execute_result a _ suffix bm fits stack

/-- info: 'Solidity.Backend.AbiWorld.MixedPacket.scalar_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scalar_complete
/-- info: 'Solidity.Backend.AbiWorld.MixedPacket.array_encoding' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms array_encoding
/-- info: 'Solidity.Backend.AbiWorld.MixedPacket.encoded_values' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_values
/-- info: 'Solidity.Backend.AbiWorld.MixedPacket.encoded_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_length
/-- info: 'Solidity.Backend.AbiWorld.MixedPacket.state_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms state_complete
/-- info: 'Solidity.Backend.AbiWorld.MixedPacket.captured' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms captured
/-- info: 'Solidity.Backend.AbiWorld.MixedPacket.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiWorld.MixedPacket.execute_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms execute_observed
end Solidity.Backend.AbiWorld.MixedPacket
