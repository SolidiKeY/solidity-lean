import Solidity.Backend.InternalFlow.RuntimeFrameRestore
import Solidity.Backend.InternalFlow.RuntimeFrameComposition

/-! Whole caller-cell restoration on the existing runtime-pointer machine.
Captured payloads are genuine input evidence, not a desired simulation.
All contexts/list lengths are allowed; no recursion/admission bound is added.
Capture production and checked-body composition are proved below; source
return/export agreement, world rollback and an unbounded return dispatcher
remain separate obligations. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.Context
open Evm Evm.Memory

/-- Complete local/exterior observations of the actual restore instructions.
External machine fields come from AFTER the body, not the earlier caller. -/
structure Recovered (before after last : Machine) (cells : List Nat) (lo pointer start : Nat) : Prop where
 stack : last.stack=after.stack
 cursor : last.mem pointer=.val (wmod start)
 locals : ∀ x, x<lo → last.mem x=if x∈cells then before.mem x else after.mem x
 exterior : ∀ x, lo≤x → x≠pointer → last.mem x=after.mem x
 fields : {last with mem:=after.mem,stack:=after.stack}=after
 allocator : ∀ {H : HTy} (heap : Heap H) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W),
   (∀ x∈cells,0<x ∧ x<frame) → 0<pointer → pointer<frame →
   StructAllocatorRepr heap base frame cursor after → StructAllocatorRepr heap base frame cursor last

/-- Reverse restoration of ANY finite captured caller list. The payload
matches actual captured source words, and remains untouched by restoration.
The theorem derives the run and all output observations, not assumes them. -/
theorem restore_many (cells : List Nat) :
 ∀ (before after : Machine) (lo pointer start : Nat),
 (∀ x∈cells,x<lo) → lo≤pointer → lo≤start →
 (pointer<start ∨ start+cells.length≤pointer) → start+cells.length<W →
 after.mem pointer=.val (wmod (start+cells.length)) →
 (∀ i (hi : i<cells.length),after.mem (start+i)=before.mem cells[i]) →
 ∃ last, Evm.run (Restore.restoreCells pointer cells) after=.ok last 0 ∧
   Recovered before after last cells lo pointer start := by
 induction cells with
 | nil =>
   intro before after lo pointer start below pointerAbove payloadAbove separate fits current saved
   refine ⟨after,rfl,⟨rfl,?_,?_,?_,rfl,?_⟩⟩
   · simpa only [List.length_nil,Nat.add_zero] using current
   · intro x hx
     simp only [List.not_mem_nil,↓reduceIte]
   · intro x hx hn
     rfl
   · intro H heap base frame cursor bounds positive below allocation
     exact allocation
 | cons head tail ih =>
   intro before after lo pointer start below pointerAbove payloadAbove separate fits current saved
   have headBelow : head<lo := below head List.mem_cons_self
   have tailBelow : ∀ x∈tail,x<lo := by
     intro x hx
     exact below x (List.mem_cons_of_mem head hx)
   have tailSeparate : pointer<start+1 ∨ start+1+tail.length≤pointer := by
     simp only [List.length_cons] at separate
     omega
   have tailFits : start+1+tail.length<W := by
     simp only [List.length_cons] at fits
     omega
   have tailPointer : after.mem pointer=.val (wmod (start+1+tail.length)) := by
     have equal : start+(head::tail).length=start+1+tail.length := by simp only [List.length_cons];omega
     rw [← equal]
     exact current
   have tailSaved : ∀ i (hi : i<tail.length),after.mem (start+1+i)=before.mem tail[i] := by
     intro i hi
     have hi' : i+1<(head::tail).length := by simp only [List.length_cons];omega
     have fact := saved (i+1) hi'
     simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1 i] using fact
   obtain ⟨mid,executed,recovered⟩ := ih before after lo pointer (start+1)
     tailBelow pointerAbove (by omega) tailSeparate tailFits tailPointer tailSaved
   have index : (wmod (start+1)).val=start+1 := Nat.mod_eq_of_lt (by omega)
   have notPayload : start≠pointer := by simp only [List.length_cons] at separate;omega
   have savedHead : mid.mem start=before.mem head := by
     have old := saved 0 (by simp only [List.length_cons];omega)
     simp only [Nat.add_zero,List.getElem_cons_zero] at old
     exact (recovered.exterior start payloadAbove notPayload).trans old
   have step := Restore.run mid head pointer (wmod (start+1)) recovered.cursor
     (by rw [index];omega) (by rw [index];omega)
   refine ⟨Restore.restored mid head pointer (wmod (start+1)),?_,⟨?_,?_,?_,?_,?_,?_⟩⟩
   · change Evm.run (Restore.restoreCells pointer tail ++ Restore.code head pointer) after=_
     rw [Evm.run_append_ok executed]
     exact step
   · exact recovered.stack
   · change upd (upd mid.mem pointer (.val (wmod ((wmod (start+1)).val-1)))) head
       (mid.mem ((wmod (start+1)).val-1)) pointer = _
     rw [index,show start+1-1=start by omega]
     simp only [upd,if_neg (show pointer≠head by omega),↓reduceIte]
   · intro x hx
     by_cases same : x=head
     · subst x
       rw [Restore.destination,index,show start+1-1=start by omega,savedHead]
       rw [if_pos List.mem_cons_self]
     · rw [Restore.outside mid head pointer (wmod (start+1)) x (by omega) same,
         recovered.locals x hx]
       simp only [List.mem_cons,same,false_or]
   · intro x hx notPointer
     rw [Restore.outside mid head pointer (wmod (start+1)) x notPointer (by omega)]
     exact recovered.exterior x hx notPointer
   · change {mid with mem:=after.mem,stack:=after.stack}=after
     exact recovered.fields
   · intro H heap base frame cursor bounds positive below allocation
     have tailBounds : ∀ x∈tail,0<x ∧ x<frame :=
       fun x hx => bounds x (List.mem_cons_of_mem head hx)
     have afterTail := recovered.allocator heap base frame cursor tailBounds positive below allocation
     have headBounds := bounds head List.mem_cons_self
     exact (afterTail.localWrite pointer positive below (.val (wmod ((wmod (start+1)).val-1)))).localWrite
       head headBounds.1 headBounds.2 (mid.mem ((wmod (start+1)).val-1))

/-- Restore every intrinsic caller binding, including same-typed distinct
locals, aliases and symbolic storage-slot words. No physical-byte encoding is
claimed for symbolic slots. Heap/exterior words are framed after the body. -/
theorem restore_context (b : Nat) (Γ : Ctx) (before after : Machine) (lo pointer start : Nat)
 (locals : b+Γ.length≤lo) (pointerAbove : lo≤pointer) (payloadAbove : lo≤start)
 (separate : pointer<start ∨ start+Γ.length≤pointer) (fits : start+Γ.length<W)
 (current : after.mem pointer=.val (wmod (start+Γ.length)))
 (saved : ∀ i (_hi : i<Γ.length),after.mem (start+i)=before.mem (b+i)) :
 ∃ last, Evm.run (Restore.restoreCells pointer (Restore.contextCells b Γ)) after=.ok last 0 ∧
   Recovered before after last (Restore.contextCells b Γ) lo pointer start ∧
   (∀ {t : LTy} (index : Idx Γ t),last.mem (cellOf b index)=before.mem (cellOf b index)) := by
 have count : (Restore.contextCells b Γ).length=Γ.length := by
   simp only [Restore.contextCells,List.length_map,List.length_range]
 have below : ∀ x∈Restore.contextCells b Γ,x<lo := by
   intro x hx
   obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
   have small := List.mem_range.mp hi
   omega
 have payload : ∀ i (_hi : i<(Restore.contextCells b Γ).length),
     after.mem (start+i)=before.mem (Restore.contextCells b Γ)[i] := by
   intro i hi
   have small : i<Γ.length := by simpa only [count] using hi
   simpa only [Restore.contextCells,List.getElem_map,List.getElem_range] using saved i small
 obtain ⟨last,executed,recovered⟩ := restore_many (Restore.contextCells b Γ) before after lo pointer start
   below pointerAbove payloadAbove (by simpa only [count] using separate)
   (by simpa only [count] using fits) (by simpa only [count] using current) payload
 refine ⟨last,executed,recovered,?_⟩
 intro t index
 have small := lvl_lt b index
 have bound : cellOf b index<lo := by
   change lvl b index<lo
   omega
 simpa only [if_pos (Restore.cell_member b index)] using recovered.locals (cellOf b index) bound

/-- Exact successful capture observations, over the existing machine. -/
structure Captured (before last : Machine) (cells : List Nat) (lo pointer start : Nat) : Prop where
 stack : last.stack=before.stack
 cursor : last.mem pointer=.val (wmod (start+cells.length))
 locals : ∀ x, x<lo → last.mem x=before.mem x
 payload : ∀ i (_hi : i<cells.length),last.mem (start+i)=before.mem cells[i]
 exterior : ∀ x, x≠pointer → (x<start ∨ start+cells.length≤x) → last.mem x=before.mem x
 fields : {last with mem:=before.mem,stack:=before.stack}=before

/-- Capture is itself proved by actual save instructions, preserving the FULL
typed state and consuming zero allocator cells. No captured-value oracle or
body simulation is assumed. Actual runtime pointer/separation/W-fit and
reserved-frame bounds are the explicit input conditions. -/
theorem capture_many {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {σ : State C Γ} {base : Nat → Fin W} (cells : List Nat) :
 ∀ (before : Machine) (lo pointer start : Nat),
 StateRepr L b frame F σ base before → b+Γ.length≤lo →
 (∀ x∈cells,x<lo) → lo≤pointer → pointer<frame → lo≤start →
 start+cells.length≤frame → (pointer<start ∨ start+cells.length≤pointer) →
 start+cells.length<W → before.mem pointer=.val (wmod start) →
 ∃ last, Evm.run (Restore.saveCells pointer cells) before=.ok last 0 ∧
 Captured before last cells lo pointer start ∧ StateRepr L b frame F σ base last ∧
 GrowsAllocator b frame 0 σ base before σ base last := by
 induction cells with
 | nil =>
   intro before lo pointer start repr localBound below pointerAbove pointerBelow payloadAbove payloadBelow separate fits current
   refine ⟨before,rfl,?_,repr,?_⟩
   · refine ⟨rfl,?_,?_,?_,?_,rfl⟩
     · simpa only [List.length_nil,Nat.add_zero] using current
     · intro x hx; rfl
     · intro i hi; cases hi
     · intro x hx hs; rfl
   · intro cursor positive allocation space
     simpa only [Nat.add_zero] using allocation
 | cons head tail ih =>
   intro before lo pointer start repr localBound below pointerAbove pointerBelow payloadAbove payloadBelow separate fits current
   have headBelow : head<lo := below head List.mem_cons_self
   have tailBelow : ∀ x∈tail,x<lo := fun x hx => below x (List.mem_cons_of_mem head hx)
   have small : start<W := by simp only [List.length_cons] at fits;omega
   have firstValue : (wmod start).val=start := Nat.mod_eq_of_lt small
   have separated : pointer≠start := by simp only [List.length_cons] at separate;omega
   let first := Stack.pushed before pointer (wmod start) (before.mem head)
   have executed := save_word_run before head pointer (wmod start) current (by rw [firstValue];exact separated)
   have firstRepr : StateRepr L b frame F σ base first := pushed_repr repr pointer (wmod start) _
     (by omega) pointerBelow (by rw [firstValue];omega)
     (by rw [firstValue];simp only [List.length_cons] at payloadBelow;omega)
   have firstGrowth : GrowsAllocator b frame 0 σ base before σ base first :=
     pushed_allocator pointer (wmod start) _ (by omega) pointerBelow
       (by rw [firstValue];omega) (by rw [firstValue];simp only [List.length_cons] at payloadBelow;omega)
   have low : ∀ x, x<lo → first.mem x=before.mem x := by
     intro x hx
     change upd (upd before.mem (wmod start).val (before.mem head)) pointer
       (.val (wmod (1+(wmod start).val))) x=before.mem x
     rw [firstValue]
     simp only [upd,if_neg (show x≠pointer by omega),if_neg (show x≠start by omega)]
   have next : first.mem pointer=.val (wmod (start+1)) := by
     change upd _ pointer (Word.val (wmod (1+(wmod start).val))) pointer=Word.val (wmod (start+1))
     rw [upd_same,firstValue,Nat.add_comm 1 start]
   obtain ⟨last,tailRun,captured,finalRepr,growth⟩ := ih first lo pointer (start+1) firstRepr localBound
     tailBelow pointerAbove pointerBelow (by omega)
     (by simp only [List.length_cons] at payloadBelow;omega)
     (by simp only [List.length_cons] at separate;omega)
     (by simp only [List.length_cons] at fits;omega) next
   refine ⟨last,?_,?_,finalRepr,?_⟩
   · change Evm.run (saveCode head pointer ++ Restore.saveCells pointer tail) before=_
     rw [Evm.run_append_ok executed]
     exact tailRun
   · refine ⟨captured.stack,?_,?_,?_,?_,?_⟩
     · have eq : start+(head::tail).length=start+1+tail.length := by simp only [List.length_cons];omega
       rw [eq]
       exact captured.cursor
     · intro x hx
       exact (captured.locals x hx).trans (low x hx)
     · intro i hi
       cases i with
       | zero =>
         simp only [Nat.add_zero,List.getElem_cons_zero]
         have kept := captured.exterior start (Ne.symm separated) (Or.inl (by omega))
         rw [kept]
         change upd (upd before.mem (wmod start).val (before.mem head)) pointer _ start=before.mem head
         rw [firstValue]
         simp only [upd,if_neg (Ne.symm separated),↓reduceIte]
       | succ i =>
         have bound : i<tail.length := by simp only [List.length_cons] at hi;omega
         have value := captured.payload i bound
         rw [low tail[i] (tailBelow _ (List.getElem_mem bound))] at value
         simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1 i] using value
     · intro x notPointer outside
       have tailOutside : x<start+1 ∨ start+1+tail.length≤x := by
         simp only [List.length_cons] at outside
         omega
       rw [captured.exterior x notPointer tailOutside]
       change upd (upd before.mem (wmod start).val (before.mem head)) pointer _ x=before.mem x
       rw [firstValue]
       simp only [upd,if_neg notPointer,if_neg (show x≠start by simp only [List.length_cons] at outside;omega)]
     · have erased := congrArg (fun m : Machine => {m with mem:=before.mem,stack:=before.stack}) captured.fields
       exact erased
   · simpa only [Nat.zero_add] using firstGrowth.comp growth

/-- Typed whole-context capture, including the genuine represented state and
zero allocation preservation. The payload oracle is an OUTPUT, not a premise. -/
theorem capture_context {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {σ : State C Γ} {base : Nat → Fin W} (before : Machine) (lo pointer start : Nat)
 (repr : StateRepr L b frame F σ base before) (localBound : b+Γ.length≤lo)
 (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame) (payloadAbove : lo≤start)
 (payloadBelow : start+Γ.length≤frame) (separate : pointer<start ∨ start+Γ.length≤pointer)
 (fits : start+Γ.length<W) (current : before.mem pointer=.val (wmod start)) :
 ∃ last, Evm.run (Restore.saveCells pointer (Restore.contextCells b Γ)) before=.ok last 0 ∧
 Captured before last (Restore.contextCells b Γ) lo pointer start ∧
 StateRepr L b frame F σ base last ∧ GrowsAllocator b frame 0 σ base before σ base last := by
 have count : (Restore.contextCells b Γ).length=Γ.length := by
   simp only [Restore.contextCells,List.length_map,List.length_range]
 have below : ∀ x∈Restore.contextCells b Γ,x<lo := by
   intro x hx
   obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
   have small := List.mem_range.mp hi
   omega
 exact capture_many (Restore.contextCells b Γ) before lo pointer start repr localBound below
   pointerAbove pointerBelow payloadAbove (by simpa only [count] using payloadBelow)
   (by simpa only [count] using separate) (by simpa only [count] using fits) current

/-- ACTUAL capture → checked body → restore. Source-indexed body execution,
reached cost, allocation and scratch facts all come from the public producer.
The final locals are the caller's; this does not claim they simulate arbitrary
body assignments or supply runtime return dispatch/source-frame agreement. -/
theorem program {C : Contract} {Γ Δ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {P : Prog C Γ Δ} {σ : State C Γ} {base : Nat → Fin W} {before : Machine}
 (selected : Composition.Program b F P) (repr : StateRepr L b frame F σ base before)
 (lo pointer start : Nat) (localBound : b+Γ.length≤lo) (bodyBound : b+selected.checked.need≤lo)
 (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame) (payloadAbove : lo≤start)
 (payloadBelow : start+Γ.length≤frame) (separate : pointer<start ∨ start+Γ.length≤pointer)
 (fits : start+Γ.length<W) (current : before.mem pointer=.val (wmod start))
 (capacity : AllocationInput b frame (selected.checked.cost σ) σ base before)
 (out : Solidity.Out C σ.H Δ) (source : P.run σ=.ok out) :
 ∃ saved after last addresses,
 Evm.run (Restore.saveCells pointer (Restore.contextCells b Γ)) before=.ok saved 0 ∧
 Evm.run selected.checked.code saved=.ok after 0 ∧
 Evm.run (Restore.restoreCells pointer (Restore.contextCells b Γ)) after=.ok last 0 ∧
 Evm.run (Restore.saveCells pointer (Restore.contextCells b Γ) ++ selected.checked.code ++
   Restore.restoreCells pointer (Restore.contextCells b Γ)) before=.ok last 0 ∧
 Captured before saved (Restore.contextCells b Γ) lo pointer start ∧
 StateRepr L b frame selected.checked.frag out.st addresses after ∧
 Recovered before after last (Restore.contextCells b Γ) lo pointer start ∧
 BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (selected.checked.cost σ) σ base before out.st addresses last ∧
 last.stack=before.stack ∧
 (∀ {t : LTy} (index : Idx Γ t),last.mem (cellOf b index)=before.mem (cellOf b index)) := by
 obtain ⟨saved,captureRun,captured,savedRepr,captureGrowth⟩ := capture_context before lo pointer start repr
   localBound pointerAbove pointerBelow payloadAbove payloadBelow separate fits current
 have input : AllocationInput b frame (selected.checked.cost σ) σ base saved :=
   captureGrowth.nextInput (by simpa only [Nat.zero_add] using capacity)
 obtain ⟨after,addresses,bodyRun,bodyRepr,stack,extended,growth,words⟩ :=
   Composition.endpoint selected savedRepr bodyBound (by omega) input out source
 have reachedPointer : after.mem pointer=.val (wmod (start+Γ.length)) := by
   have count : (Restore.contextCells b Γ).length=Γ.length := by
     simp only [Restore.contextCells,List.length_map,List.length_range]
   exact (words pointer pointerAbove pointerBelow).trans (by simpa only [count] using captured.cursor)
 have reachedPayload : ∀ i (_hi : i<Γ.length),after.mem (start+i)=before.mem (b+i) := by
   intro i hi
   have count : (Restore.contextCells b Γ).length=Γ.length := by
     simp only [Restore.contextCells,List.length_map,List.length_range]
   have bound : i<(Restore.contextCells b Γ).length := by simpa only [count] using hi
   have actual := captured.payload i bound
   simp only [Restore.contextCells,List.getElem_map,List.getElem_range] at actual
   exact (words (start+i) (by omega) (by omega)).trans actual
 obtain ⟨last,restoreRun,recovered,bindings⟩ := restore_context b Γ before after lo pointer start localBound
   pointerAbove payloadAbove separate fits reachedPointer reachedPayload
 refine ⟨saved,after,last,addresses,captureRun,bodyRun,restoreRun,?_,captured,bodyRepr,recovered,extended,?_,
   recovered.stack.trans (stack.trans captured.stack),bindings⟩
 · rw [List.append_assoc,Evm.run_append_ok captureRun,Evm.run_append_ok bodyRun]
   exact restoreRun
 · intro cursor positive allocation space
   have bounds : ∀ x∈Restore.contextCells b Γ,0<x ∧ x<frame := by
     intro x hx
     obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
     have small := List.mem_range.mp hi
     constructor <;> omega
   have totalGrowth : GrowsAllocator b frame (selected.checked.cost σ) σ base before out.st addresses after := by
     simpa only [Nat.zero_add] using captureGrowth.comp growth
   exact recovered.allocator out.st.heap addresses frame _ bounds (by omega) pointerBelow
     (totalGrowth cursor positive allocation space)

end Solidity.Backend.InternalFlow.RuntimeFrame.Context
