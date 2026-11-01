import Solidity.Backend.AbiWorld.WordArrayPacket
import Solidity.Backend.InternalFlow.CallerTail
import Solidity.Backend.InternalFlow.CallerView

/-! Development consumer of exact committed V12 caller transport. The observed
array is the CURRENT reached heap object behind an OLD captured alias. No heap
content frame, runtime byte encoder, byte-memory simulation or external call
execution is introduced. The producer dependency is staged privately. -/
namespace Solidity.Backend.AbiWorld.CallerPacket
open Evm Evm.Memory InternalFlow
variable {C : Contract}

/-- Eliminate a captured caller frame into complete ordered codec bytes of its
current uint array. Entry-address identity and reached header/space are retained.
No byte-range hypothesis or old-content equality is required. -/
theorem captured {Γ Ξ : Ctx} {L b frame : Nat} {F : Frag Γ}
    {σ : State C Γ} (out : Solidity.Out C σ.H Γ) (h : Thin Ξ Γ)
    (capture : TEnv.thin h out.st.env = TEnv.wk out.ext Ξ (TEnv.thin h σ.env))
    {base base' : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F out.st base' m)
    (addresses : BaseExtends σ.H base base')
    (i : Idx Ξ (.mem bytesR)) (r : HRef σ.H bytesR)
    (old : TEnv.get (i.wk h) σ.env = some r) :
    m.mem (cellOf b (i.wk h)) = .val (base r.id) ∧
    m.mem (base' r.id).val = .val (wmod (out.st.heap.len (r.wk out.ext) .dyn)) ∧
    WordArrayPacket.localObservation m b (i.wk h) =
      some (WordArrayPacket.values (out.st.heap.get (r.wk out.ext)).1) ∧
    (WordArrayPacket.localObservation m b (i.wk h)).map AbiEntry.encodeArgs =
      some (AbiEntry.wordBytes 32 ++
        AbiEntry.wordBytes (out.st.heap.get (r.wk out.ext)).1.length ++
        (out.st.heap.get (r.wk out.ext)).1.flatMap (fun v => AbiEntry.wordBytes v.val.toNat)) ∧
    frame ≤ (base' r.id).val ∧
      (base' r.id).val + 1 + out.st.heap.len (r.wk out.ext) .dyn ≤ W := by
  have reference := CallerView.reference out h capture i r old
  obtain ⟨pointer,header,observed,above,space⟩ :=
    WordArrayPacket.local_complete repr (i.wk h) (r.wk out.ext) reference
  refine ⟨CallerView.represented out h capture repr addresses bytesR i r old,
    header,observed,?_,above,space⟩
  rw [observed,Option.map_some,WordArrayPacket.encoded_values]
  rfl

/-- Actual selected compiled call-plus-tail execution supplies the represented
current array and captured old reference; all producer guards remain explicit. -/
theorem selected {b L frame : Nat} {Γ Δ Ε Ξ rs ps Γf : Ctx}
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
    (old : TEnv.get (i.wk h) σ.env = some r) :
    ∃ m' base', Evm.run compiled.code m = .ok m' 0 ∧
      StateRepr L b frame compiled.frag (out.st.drop (ret.ext.trans tail.ext)) base' m' ∧
      m'.stack = m.stack ∧ BaseExtends σ.H base base' ∧
      GrowsAllocator b frame (compiled.cost σ) σ base m
        (out.st.drop (ret.ext.trans tail.ext)) base' m' ∧
      m'.mem (cellOf b (i.wk h)) = .val (base r.id) ∧
      WordArrayPacket.localObservation m' b (i.wk h) =
        some (WordArrayPacket.values (out.st.heap.get (r.wk out.ext)).1) ∧
      (WordArrayPacket.localObservation m' b (i.wk h)).map AbiEntry.encodeArgs =
        some (AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes (out.st.heap.get (r.wk out.ext)).1.length ++
          (out.st.heap.get (r.wk out.ext)).1.flatMap (fun v => AbiEntry.wordBytes v.val.toNat)) := by
  obtain ⟨m',base',target,reached,stack,addresses,growth,capture,pointers⟩ :=
    CallerTail.selected_target h separate within unwritten condition pre post fail compiled
      σ miss hit out executed repr room capacity
  have observation := captured
    (⟨out.st.drop (ret.ext.trans tail.ext),out.ext⟩ : Solidity.Out C σ.H Γ)
    h capture reached addresses i r old
  exact ⟨m',base',target,reached,stack,addresses,growth,observation.1,
    observation.2.2.1,observation.2.2.2.1⟩

/-- info: 'Solidity.Backend.AbiWorld.CallerPacket.captured' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms captured
/-- info: 'Solidity.Backend.AbiWorld.CallerPacket.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
end Solidity.Backend.AbiWorld.CallerPacket
