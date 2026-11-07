import Solidity.Backend.InternalFlow.RuntimeFrameV3StateShell
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocationInventory
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarTurn
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDescentInterfaceV1

/-! Actual allocating scalar descent prefixes and full three-cell capture
history. This uses the existing value compiler, loop iterator and typed entry
turn. It is not general recursive compiler selection or a native partial trace. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev C := AllocatingScalarTurn.C
abbrev A := AllocatingScalarTurn.A
abbrev F := AllocatingScalarTurn.F

def guardCompiled : CompiledVal 2 F (guard (C:=C) (R:=A)) :=
 ⟨_,.binary .gt rfl rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩
theorem public_guard : Memory.compileVal 2 F (guard (C:=C) (R:=A))=some guardCompiled := by rfl

theorem guard_run {L frame : Nat} (σ : State C (Frame A)) (n : Nat) (fit : n<W)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue n fit)
 (base : Nat → Fin W) (m : Machine) (repr : StateRepr L 2 frame F σ base m) :
 run guardCompiled.code m=.ok (m.push (.val (bword (decide (0<n))))) 0 := by
 have source := ScalarRecursiveSource.guard_eval σ n (congrArg (fun v : PrimTy.uint.Denote => v.val) counter)
 rcases guardCompiled.cert.correct repr with ⟨v,w,evaluated,represented,actual⟩ | ⟨evaluated,actual⟩
 · have same : v=decide (0<n) := Except.ok.inj (evaluated.symm.trans source)
   subst v
   change w=.val (bword (decide (0<n))) at represented
   simpa only [represented] using actual
 · rw [source] at evaluated
   cases evaluated

theorem positive_turn {L frame : Nat} (σ : State C (Frame A)) (n : Nat) (fit : n+1<W)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue (n+1) fit)
 (base : Nat → Fin W) (m next : Machine) (repr : StateRepr L 2 frame F σ base m)
 (pointer : Nat) (body : run (AllocatingScalarTurn.code pointer) m=.ok next 0) :
 loopTurn (run guardCompiled.code) (run (AllocatingScalarTurn.code pointer)) m=.inl next := by
 have guard := guard_run σ (n+1) fit counter base m repr
 have positive : decide (0<n+1)=true := decide_eq_true (by omega)
 have checked : run guardCompiled.code m=.ok (m.push w[1]) 0 := by
   simpa only [positive,bword] using guard
 exact GuardedRecursion.successful_turn _ _ m next checked body

/-- The false guard does not execute an allocating body. -/
theorem zero_turn {L frame : Nat} (σ : State C (Frame A))
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue 0 W_pos)
 (base : Nat → Fin W) (m : Machine) (repr : StateRepr L 2 frame F σ base m) (pointer : Nat) :
 loopTurn (run guardCompiled.code) (run (AllocatingScalarTurn.code pointer)) m=.inr (.ok m 0) := by
 have guard := guard_run σ 0 W_pos counter base m repr
 have checked : run guardCompiled.code m=.ok (m.push w[0]) 0 := by
   simpa only [show decide (0<(0:Nat))=false from rfl,bword] using guard
 exact GuardedRecursion.empty_turn _ _ m checked

theorem running_with_context (steps remaining : Nat) {L frame : Nat} (σ : State C (Frame A))
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
 loopIterN (run guardCompiled.code) (run (AllocatingScalarTurn.code pointer)) steps before=.inl after ∧
 StateRepr L 2 frame F τ addresses after ∧
 τ.env=(PrimTy.dflt .uint,(countValue remaining (by omega),(some (ref.wk e),()))) ∧
 τ.H.length=σ.H.length+steps ∧ Heap.Keeps e σ.heap τ.heap ∧
 StructAllocatorRepr τ.heap addresses frame (⟨cursor.val+4*steps,heapSpace⟩ : Fin W) after ∧
 BaseExtends σ.H base addresses ∧ GrowsAllocator 2 frame (4*steps) σ base before τ addresses after ∧
 after.stack=before.stack ∧ after.mem pointer=.val (wmod (start+3*steps)) ∧
 (∀ j,j<steps → after.mem (start+3*j)=.val (base ref.id) ∧
   after.mem (start+3*j+1)=.val (wmod (remaining+steps-j)) ∧ after.mem (start+3*j+2)=w[0]) ∧
 (∀ x,6≤x → x<frame → x≠pointer → (x<start ∨ start+3*steps≤x) → after.mem x=before.mem x) ∧
 ScalarAllocationInventory.Holds σ.H.length steps cursor.val τ addresses ∧ StateShell.Same σ τ := by
 induction steps generalizing σ base before cursor start with
 | zero =>
   have environment : σ.env=(PrimTy.dflt .uint,(countValue remaining (by omega),(some ref,()))) :=
     Prod.ext result (Prod.ext counter (Prod.ext alias (by cases σ.env.2.2.2;rfl)))
   refine ⟨σ,List.prefix_refl _,before,base,rfl,repr,environment,?_,Heap.Keeps.refl σ.heap,owned,
     BaseExtends.refl base,?_,rfl,current,?_,?_,?_,?_⟩
   · omega
   · intro other positive initial space
     simpa only [Nat.mul_zero,Nat.add_zero] using initial
   · intro j impossible;omega
   · intro x lower upper different region;rfl
   · intro j impossible;omega
   · exact StateShell.refl σ
 | succ steps ih =>
   have firstCounter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue (remaining+steps+1) (by omega) := by
     simpa only [show remaining+(steps+1)=remaining+steps+1 from by omega] using counter
   obtain ⟨seen,seenAlias,seenWord⟩ := repr.pointers (.there (.there .here) : Idx (Frame A) (.mem A))
   have same : seen=ref := Option.some.inj (seenAlias.symm.trans alias)
   subst seen
   have referenceWord : before.mem 2=.val (base ref.id) := seenWord
   have resultRepr := repr.core.vals (.here : Idx (Frame A) (.val .uint))
   change ReprV .uint (TEnv.get (.here : Idx (Frame A) (.val .uint)) σ.env) (before.mem 4) at resultRepr
   rw [result] at resultRepr
   have resultWord : before.mem 4=w[0] := Restore.uint_unique resultRepr (ReprV.dflt_zero .uint)
   have counterRepr := repr.core.vals (.there .here : Idx (Frame A) (.val .uint))
   change ReprV .uint (TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env) (before.mem 3) at counterRepr
   rw [counter] at counterRepr
   have canonical : wmod (remaining+(steps+1))=(⟨remaining+(steps+1),fit⟩ : Fin W) := Fin.ext (Nat.mod_eq_of_lt fit)
   have encoded : ReprV .uint (countValue (remaining+(steps+1)) fit) (.val (wmod (remaining+(steps+1)))) := by
     rw [canonical]
     exact ReprV.uint_of rfl
   have counterWord : before.mem 3=.val (wmod (remaining+(steps+1))) := Restore.uint_unique counterRepr encoded
   have firstSpace : cursor.val+4<W := by omega
   let firstExt := AllocatingScalarSource.extension σ
   let child := entered (AllocatingScalarSource.allocated σ) (remaining+steps) (by omega) (ref.wk firstExt)
   let nextBase := upd base σ.H.length cursor
   obtain ⟨next,source,executed,nextRepr,nextOwner,firstBase,stack,nextPointer,_,_,_,_,firstPayload,firstWords⟩ :=
     AllocatingScalarTurn.turn σ (remaining+steps) (by omega) ref firstCounter alias base before repr cursor owned firstSpace
       lo pointer start privateBelow pointerAbove pointerBelow payloadAbove (by omega) pointerBefore (by omega) current
   let nextCursor : Fin W := ⟨cursor.val+4,firstSpace⟩
   have remainingSpace : nextCursor.val+4*steps<W := by change cursor.val+4+4*steps<W;omega
   obtain ⟨τ,lastExt,after,addresses,running,finalRepr,finalEnv,finalSize,finalKeeps,finalOwner,finalBase,finalGrowth,finalStack,finalPointer,finalHistory,finalWords,finalInventory,finalContext⟩ :=
     ih (σ:=child) (fit:=by omega) (ref:=ref.wk firstExt) (result:=rfl) (counter:=rfl) (alias:=rfl)
       (base:=nextBase) (before:=next) (repr:=nextRepr) (cursor:=nextCursor) (owned:=nextOwner)
       (heapSpace:=remainingSpace) (start:=start+3) (payloadAbove:=by omega) (payloadBelow:=by omega)
       (pointerBefore:=by omega) (fits:=by omega) (current:=nextPointer)
   have kept : Heap.Keeps firstExt σ.heap child.heap := Heap.keeps_alloc σ.heap (defaultArray .bool AllocatingScalarSource.size)
   have cursorEq : (⟨nextCursor.val+4*steps,remainingSpace⟩ : Fin W)=⟨cursor.val+4*(steps+1),heapSpace⟩ :=
     Fin.ext (by change cursor.val+4+4*steps=cursor.val+4*(steps+1);omega)
   rw [cursorEq] at finalOwner
   have turn := positive_turn σ (remaining+steps) (by omega) firstCounter base before next repr pointer executed
   have oldSaved (i : Nat) (small : i<3) : after.mem (start+i)=next.mem (start+i) :=
     finalWords (start+i) (by omega) (by omega) (by omega) (.inl (by omega))
   refine ⟨τ,firstExt.trans lastExt,after,addresses,?_,finalRepr,finalEnv,?_,kept.trans finalKeeps,finalOwner,
     firstBase.trans firstExt finalBase,?_,finalStack.trans stack,?_,?_,?_,?_,?_⟩
   · simpa only [loopIterN,turn] using running
   · change τ.H.length=(σ.H++([.array (.prim .bool)] : HTy)).length+steps at finalSize
     simpa only [List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm 1 steps] using finalSize
   · intro other positive initial space
     have same : other=cursor := Word.val.inj (initial.arrays.free.cell.symm.trans owned.arrays.free.cell)
     subst other
     exact finalOwner
   · simpa only [show start+3+3*steps=start+3*(steps+1) from by omega] using finalPointer
   · intro j small
     cases j with
     | zero =>
       exact ⟨(oldSaved 0 (by decide)).trans ((firstPayload 0 (by decide)).trans referenceWord),
         (oldSaved 1 (by decide)).trans ((firstPayload 1 (by decide)).trans counterWord),
         (oldSaved 2 (by decide)).trans ((firstPayload 2 (by decide)).trans resultWord)⟩
     | succ j =>
       have known := finalHistory j (by omega)
       have oldBase : nextBase (ref.wk firstExt).id=base ref.id := allocationBase_old base cursor ref
       rw [oldBase] at known
       simpa only [show start+3+3*j=start+3*(j+1) from by omega,
         show remaining+(steps+1)-(j+1)=remaining+steps-j from by omega] using known
   · intro x lower upper hp region
     have first := firstWords x (by omega) (by omega) (by omega) (by omega) hp
       (by have above:=owned.arrays.free.above;omega) (by omega)
     exact (finalWords x lower upper hp (by omega)).trans first

   · intro j small
     cases j with
     | zero =>
       let fresh : HRef child.H (.array (.prim .bool)) := (σ.alloc (defaultArray .bool AllocatingScalarSource.size)).2
       have content : child.heap.get fresh=defaultArray .bool AllocatingScalarSource.size :=
         Heap.get_alloc_self σ.heap (defaultArray .bool AllocatingScalarSource.size)
       refine ⟨fresh.wk lastExt,rfl,?_,?_⟩
       · rw [finalKeeps fresh,content]
         simp only [MObj.wk,defaultArray,List.map_replicate,MVal.wk]
       · have address := finalBase fresh
         change addresses fresh.id=nextBase fresh.id at address
         rw [show nextBase fresh.id=cursor from upd_same base σ.H.length cursor] at address
         change (addresses fresh.id).val=cursor.val+4*0
         rw [address]
         omega
     | succ j =>
       obtain ⟨r,identity,content,address⟩ := finalInventory j (by omega)
       refine ⟨r,?_,content,?_⟩
       · change r.id=(σ.H++([.array (.prim .bool)] : HTy)).length+j at identity
         simp only [List.length_append,List.length_singleton] at identity
         omega
       · change (addresses r.id).val=cursor.val+4+4*j at address
         omega
   · exact StateShell.trans (show StateShell.Same σ child from ⟨rfl,rfl,rfl,rfl⟩) finalContext

theorem running_with_inventory (steps remaining : Nat) {L frame : Nat} (σ : State C (Frame A))
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
 loopIterN (run guardCompiled.code) (run (AllocatingScalarTurn.code pointer)) steps before=.inl after ∧
 StateRepr L 2 frame F τ addresses after ∧
 τ.env=(PrimTy.dflt .uint,(countValue remaining (by omega),(some (ref.wk e),()))) ∧
 τ.H.length=σ.H.length+steps ∧ Heap.Keeps e σ.heap τ.heap ∧
 StructAllocatorRepr τ.heap addresses frame (⟨cursor.val+4*steps,heapSpace⟩ : Fin W) after ∧
 BaseExtends σ.H base addresses ∧ GrowsAllocator 2 frame (4*steps) σ base before τ addresses after ∧
 after.stack=before.stack ∧ after.mem pointer=.val (wmod (start+3*steps)) ∧
 (∀ j,j<steps → after.mem (start+3*j)=.val (base ref.id) ∧
   after.mem (start+3*j+1)=.val (wmod (remaining+steps-j)) ∧ after.mem (start+3*j+2)=w[0]) ∧
 (∀ x,6≤x → x<frame → x≠pointer → (x<start ∨ start+3*steps≤x) → after.mem x=before.mem x) ∧
 ScalarAllocationInventory.Holds σ.H.length steps cursor.val τ addresses := by
 obtain ⟨τ,e,after,addresses,actual,represented,environment,size,kept,owner,extended,growth,stack,position,history,words,inventory,context⟩ :=
   running_with_context steps remaining σ fit ref result counter alias base before repr cursor owned heapSpace
     lo pointer start privateBelow pointerAbove pointerBelow payloadAbove payloadBelow pointerBefore fits current
 exact ⟨τ,e,after,addresses,actual,represented,environment,size,kept,owner,extended,growth,stack,position,history,words,inventory⟩

theorem running (steps remaining : Nat) {L frame : Nat} (σ : State C (Frame A))
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
 loopIterN (run guardCompiled.code) (run (AllocatingScalarTurn.code pointer)) steps before=.inl after ∧
 StateRepr L 2 frame F τ addresses after ∧
 τ.env=(PrimTy.dflt .uint,(countValue remaining (by omega),(some (ref.wk e),()))) ∧
 τ.H.length=σ.H.length+steps ∧ Heap.Keeps e σ.heap τ.heap ∧
 StructAllocatorRepr τ.heap addresses frame (⟨cursor.val+4*steps,heapSpace⟩ : Fin W) after ∧
 BaseExtends σ.H base addresses ∧ GrowsAllocator 2 frame (4*steps) σ base before τ addresses after ∧
 after.stack=before.stack ∧ after.mem pointer=.val (wmod (start+3*steps)) ∧
 (∀ j,j<steps → after.mem (start+3*j)=.val (base ref.id) ∧
   after.mem (start+3*j+1)=.val (wmod (remaining+steps-j)) ∧ after.mem (start+3*j+2)=w[0]) ∧
 (∀ x,6≤x → x<frame → x≠pointer → (x<start ∨ start+3*steps≤x) → after.mem x=before.mem x) := by
 obtain ⟨τ,e,after,addresses,actual,represented,environment,size,kept,owner,extended,growth,stack,position,history,words,inventory⟩ :=
   running_with_inventory steps remaining σ fit ref result counter alias base before repr cursor owned heapSpace
     lo pointer start privateBelow pointerAbove pointerBelow payloadAbove payloadBelow pointerBefore fits current
 exact ⟨τ,e,after,addresses,actual,represented,environment,size,kept,owner,extended,growth,stack,position,history,words⟩

/-- The frozen narrow descent contract, inhabited by the actual checked
compiler/guard/prefix theorems above. This is not a V3 recursion/profile instance. -/
def producer : ScalarDescentInterfaceV1.Producer guardCompiled where
 public_guard := ScalarAllocatingDescent.public_guard
 guard_run := ScalarAllocatingDescent.guard_run
 positive_turn := ScalarAllocatingDescent.positive_turn
 zero_turn := ScalarAllocatingDescent.zero_turn
 running := ScalarAllocatingDescent.running

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.public_guard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.public_guard

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.guard_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.guard_run

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.positive_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.positive_turn

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.zero_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.zero_turn

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.running

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.producer

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.running_with_inventory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.running_with_inventory

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.running_with_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.running_with_context
