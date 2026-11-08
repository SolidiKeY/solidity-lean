import Solidity.Backend.InternalFlow.RuntimeFrameV3DisjointScalarEntry
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveCall

/-! Arbitrary caller contexts around the checked scalar countdown family.
Arguments execute into disjoint cells; the actual private result is exported
into the caller's destination, whose old value is unrestricted. Source globals
and heap stay identical for this family, so no fragile exclusion is needed.
General public recursive compiler/profile closure remains open. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.DisjointScalarReturn
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

def call {C : Contract} {Γ : Ctx} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (reference : Idx Γ (.mem R)) (count : Val C Γ .uint) (destination : Idx Γ (.val .uint))
 (f : Name) (depth : Nat) : Stmt C Γ Γ :=
 InterfaceV1.recursiveSource f (DisjointScalarEntry.args hm reference count)
   (.val .uint (.user "result") (some destination)) (ScalarRecursiveSource.step R hm) depth

def code {C : Contract} {Γ : Ctx} {R : RefTy} {F : Frag Γ} {count : Val C Γ .uint}
 (b c : Nat) (reference : Idx Γ (.mem R)) (value : CompiledVal b F count)
 (destination : Idx Γ (.val .uint)) (pointer bottom : Nat) : List Instr :=
 DisjointScalarEntry.code b c reference value ++
 (ScalarReturn.image (C:=C) c (Frag.init (Parameters R)) pointer bottom ++
 [.mload (c+2),.mstore (cellOf b destination)])

theorem endpoint {C : Contract} {Γ : Ctx} {R : RefTy} {L b c frame : Nat} {F : Frag Γ}
 (hm : (Ty.ref R).mapFree=true) (σ : State C Γ) (reference : Idx Γ (.mem R))
 (count : Val C Γ .uint) (value : CompiledVal b F count) (destination : Idx Γ (.val .uint))
 (n : Nat) (bound : n<W) (evaluated : count.evalT σ=.ok (countValue n bound))
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (lo pointer bottom start : Nat) (disjoint : b+Γ.length≤c)
 (locals : c+3≤lo) (above : lo≤pointer) (below : pointer<frame)
 (payload : lo≤start) (separate : pointer<start)
 (bottomAbove : c+3≤bottom) (bottomBelow : bottom<frame) (bottomBefore : bottom<start)
 (bottomSeparate : bottom≠pointer) (capacity : start+2*n≤frame) (fits : start+2*n<W)
 (current : before.mem pointer=.val (wmod start)) :
 ∃ after addresses,
 run (code b c reference value destination pointer bottom) before=.ok after 0 ∧
 (∀ f depth,(call hm reference count destination f depth).run σ=
   if n<depth then .ok ⟨σ.setLocal destination (countValue n bound),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr L b frame F (σ.setLocal destination (countValue n bound)) addresses after ∧
 after.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 after.mem (cellOf b destination)=.val (wmod n) ∧ after.mem (c+2)=.val (wmod n) ∧
 after.mem (c+1)=.val (wmod n) ∧ after.mem c=before.mem (cellOf b reference) ∧
 after.mem pointer=.val (wmod start) ∧ after.mem bottom=.val (wmod start) ∧
 GrowsAllocator b frame 0 σ base before (σ.setLocal destination (countValue n bound)) addresses after ∧
 (∀ x,x≠cellOf b destination → x≠pointer → x≠bottom → x≠c → x≠c+1 → x≠c+2 →
   (x<start ∨ start+2*n≤x) → after.mem x=before.mem x) ∧
 (∀ j,j<n → after.mem (start+2*j)=before.mem (cellOf b reference) ∧
   after.mem (start+2*j+1)=.val (wmod (n-j))) := by
 obtain ⟨ref,entered,arguments,entryRun,childRepr,callerRepr,entryStack,entryRef,entryOutside,entryGrowth⟩ :=
   DisjointScalarEntry.entered hm σ reference count value n bound evaluated base before repr disjoint (by omega)
 let child := (σ.withEnv (Δ:=Parameters R) (countValue n bound,(some ref,()))).push (t:=.val .uint) (PrimTy.dflt .uint)
 have position : entered.mem pointer=.val (wmod start) :=
   (entryOutside pointer (by omega) (by omega) (by omega)).trans current
 obtain ⟨last,addresses,body,sourceBody,reached,stack,extended,cursor,bottomWord,bodyRef,growth,outside,saved⟩ :=
   ScalarReturn.endpoint (F:=Frag.init (Parameters R)) hm n bound child ref rfl rfl base entered childRepr
     lo pointer bottom start locals above below payload separate bottomAbove bottomBelow bottomBefore bottomSeparate capacity fits position
 have encoded : ReprV .uint (countValue n bound) (.val (wmod n)) := by
   have exactWord : wmod n=(⟨n,bound⟩ : Fin W) := Fin.ext (Nat.mod_eq_of_lt bound)
   rw [exactWord]
   exact ReprV.uint_of rfl
 have result : last.mem (c+2)=.val (wmod n) := Restored.value_unique (reached.core.vals .here) encoded
 let address := cellOf b destination
 let after := writeMachine last address (last.mem (c+2))
 have destinationBelow : address<c := Nat.lt_of_lt_of_le (lvl_lt b destination) disjoint
 have afterRepr : StateRepr L c frame ((Frag.init (Parameters R)).push (.val .uint) .ok)
     (finished child n bound) addresses after :=
   Restored.memory_transport reached after.mem (by
     intro t index observed
     exact upd_other _ _ (by have lower:=le_lvl c index;change c≤cellOf c index at lower;change cellOf c index≠address;omega)) (by
     intro x high
     exact upd_other _ _ (by omega))
 have desired := repr.setVal destination (countValue n bound) (.val (wmod n)) encoded
 have words : ∀ {t : LTy} (index : Idx Γ t),
     after.mem (cellOf b index)=(writeMachine before address (.val (wmod n))).mem (cellOf b index) := by
   intro t index
   have oldBelow : cellOf b index<c := Nat.lt_of_lt_of_le (lvl_lt b index) disjoint
   by_cases target : cellOf b index=address
   · change upd last.mem address (last.mem (c+2)) (cellOf b index)=upd before.mem address (.val (wmod n)) (cellOf b index)
     simp only [upd,if_pos target,result]
   · exact (upd_other last.mem _ target).trans
       ((outside _ (by omega) (by omega) (by omega) (by omega) (by omega) (.inl (by omega))).trans
         ((entryOutside _ (by omega) (by omega) (by omega)).trans (upd_other before.mem _ target).symm))
 have counterWord : last.mem (c+1)=.val (wmod n) :=
   Restored.value_unique (reached.core.vals (.there .here : Idx (Frame R) (.val .uint))) encoded
 have restored := SameGlobals.reframe (σ.setLocal destination (countValue n bound)) (finished child n bound).env
   base addresses (writeMachine before address (.val (wmod n))) after desired afterRepr extended words
 refine ⟨after,addresses,?_,?_,restored,stack.trans entryStack,extended,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · unfold code
   rw [run_append_ok entryRun,run_append_ok body]
   rfl
 · intro f depth
   exact ScalarRecursiveSource.call_all_horizons hm f (DisjointScalarEntry.args hm reference count) destination
     depth σ n bound ref arguments
 · exact (upd_same _ _ _).trans result
 · exact (upd_other last.mem _ (by omega)).trans result
 · exact (upd_other last.mem _ (by omega)).trans counterWord
 · exact (upd_other last.mem _ (by omega)).trans (bodyRef.trans entryRef)
 · exact (upd_other last.mem _ (by omega)).trans cursor
 · exact (upd_other last.mem _ (by omega)).trans bottomWord
 · intro allocation positive owner free
   have enteredOwner := entryGrowth allocation positive owner free
   have bodyOwner := growth allocation (by omega) enteredOwner free
   simpa only [Nat.add_zero] using bodyOwner.localWrite address
     (Nat.lt_of_lt_of_le positive (le_lvl b destination)) (by omega) (last.mem (c+2))
 · intro x hd hp hb h0 h1 h2 region
   exact (upd_other last.mem _ hd).trans
     ((outside x hp hb h0 h1 h2 region).trans (entryOutside x h0 h1 h2))

 · intro j small
   exact ⟨(upd_other last.mem _ (by omega)).trans ((saved j small).1.trans entryRef),
     (upd_other last.mem _ (by omega)).trans (saved j small).2⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.DisjointScalarReturn
