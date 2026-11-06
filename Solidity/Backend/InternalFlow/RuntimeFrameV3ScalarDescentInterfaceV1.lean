import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarTurn

/-! Frozen typed contract for allocating scalar descent. Its fields are
explicit producer obligations, not axioms or evidence of an inhabitant.
The guard is an existing typed compiler certificate, with actual public
selection required below. Native recursion/profile closure remains separate;
the existing runtime-frame V3 signatures are unchanged. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarDescentInterfaceV1
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev C := AllocatingScalarTurn.C
abbrev A := AllocatingScalarTurn.A
abbrev F := AllocatingScalarTurn.F


/-- Exact public-guard and allocating-prefix obligations. -/
structure Producer (selectedGuard : CompiledVal 2 F (guard (C:=C) (R:=A))) : Prop where
  public_guard : Memory.compileVal 2 F (guard (C:=C) (R:=A))=some selectedGuard

  guard_run {L frame : Nat} (σ : State C (Frame A)) (n : Nat) (fit : n<W)
   (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue n fit)
   (base : Nat → Fin W) (m : Machine) (repr : StateRepr L 2 frame F σ base m) :
   run selectedGuard.code m=.ok (m.push (.val (bword (decide (0<n))))) 0

  positive_turn {L frame : Nat} (σ : State C (Frame A)) (n : Nat) (fit : n+1<W)
   (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue (n+1) fit)
   (base : Nat → Fin W) (m next : Machine) (repr : StateRepr L 2 frame F σ base m)
   (pointer : Nat) (body : run (AllocatingScalarTurn.code pointer) m=.ok next 0) :
   loopTurn (run selectedGuard.code) (run (AllocatingScalarTurn.code pointer)) m=.inl next

  zero_turn {L frame : Nat} (σ : State C (Frame A))
   (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue 0 W_pos)
   (base : Nat → Fin W) (m : Machine) (repr : StateRepr L 2 frame F σ base m) (pointer : Nat) :
   loopTurn (run selectedGuard.code) (run (AllocatingScalarTurn.code pointer)) m=.inr (.ok m 0)

  running (steps remaining : Nat) {L frame : Nat} (σ : State C (Frame A))
   (fit : remaining+steps<W) (ref : HRef σ.H A)
   (result : TEnv.get (.here : Idx (Frame A) (.val .uint)) σ.env=PrimTy.dflt .uint)
   (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue (remaining+steps) fit)
   (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) σ.env=some ref)
   (base : Nat → Fin W) (before : Machine) (repr : StateRepr L 2 frame F σ base before)
   (cursor : Fin W) (owned : StructAllocatorRepr σ.heap base frame cursor before)
   (heapSpace : cursor.val+4*steps<W) (lo pointer start : Nat)
   (privateBelow : 5<lo) (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame)
   (payloadAbove : lo≤start) (payloadBelow : start+3*steps≤frame) (pointerBefore : pointer<start)
   (fits : start+3*steps<W) (current : before.mem pointer=.val (wmod start)) :
   ∃ (τ : State C (Frame A)) (e : σ.H <+: τ.H) (after : Machine) (addresses : Nat → Fin W),
   loopIterN (run selectedGuard.code) (run (AllocatingScalarTurn.code pointer)) steps before=.inl after ∧
   StateRepr L 2 frame F τ addresses after ∧
   τ.env=(PrimTy.dflt .uint,(countValue remaining (by omega),(some (ref.wk e),()))) ∧
   τ.H.length=σ.H.length+steps ∧ Heap.Keeps e σ.heap τ.heap ∧
   StructAllocatorRepr τ.heap addresses frame (⟨cursor.val+4*steps,heapSpace⟩ : Fin W) after ∧
   BaseExtends σ.H base addresses ∧ GrowsAllocator 2 frame (4*steps) σ base before τ addresses after ∧
   after.stack=before.stack ∧ after.mem pointer=.val (wmod (start+3*steps)) ∧
   (∀ j,j<steps → after.mem (start+3*j)=.val (base ref.id) ∧
     after.mem (start+3*j+1)=.val (wmod (remaining+steps-j)) ∧ after.mem (start+3*j+2)=w[0]) ∧
   (∀ x,6≤x → x<frame → x≠pointer → (x<start ∨ start+3*steps≤x) → after.mem x=before.mem x)

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarDescentInterfaceV1
