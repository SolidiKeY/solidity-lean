import Solidity.Backend.InternalFlow.RuntimeFrameV3EffectfulScalarFailure
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallerReframe

/-! Argument execution precedes the callee mutation, including heap-reading
scalar arguments. The subsequent return uses the captured count. No source
profile, arbitrary-body selector or physical-world simulation is supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulScalar
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev A : RefTy := EffectfulScalarSource.A

def changed {C : Contract} {Γ : Ctx} (σ : State C Γ) (ref : HRef σ.H A) :=
 σ.withHeap (σ.heap.set ref (MObj.setElem .dyn (σ.heap.get ref) 0 EffectfulScalarSource.replacement))

theorem write_addr {C : Contract} {Γ : Ctx} (σ : State C Γ) (ref : HRef σ.H A)
 (live : 0<σ.heap.len ref .dyn) :
 σ.heap.writeAddr (.index ref .dyn (countValue 0 W_pos)) EffectfulScalarSource.replacement=some (changed σ ref).heap := by
 change (if 0<σ.heap.len ref .dyn then
   some (σ.heap.set ref (MObj.setElem .dyn (σ.heap.get ref) 0 EffectfulScalarSource.replacement)) else none)=_
 exact if_pos live

def call {C : Contract} {Γ : Ctx} (reference : Idx Γ (.mem A)) (count : Val C Γ .uint)
 (destination : Idx Γ (.val .uint)) (function : Name) (depth : Nat) : Stmt C Γ Γ :=
 EffectfulScalarSource.invoke function (DisjointScalarEntry.args rfl reference count) destination depth

def calleeCode {C : Contract} (c : Nat) : List Instr :=
 (EffectfulScalarFailure.selected (C:=C) c (Frag.init (Frame A)) (.there (.there .here))).code

theorem callee_public_root {C : Contract} (c : Nat) :
 (Memory.compileStmt c (Frag.init (Frame A)) (EffectfulScalarSource.write (C:=C))).map (fun checked => checked.code)=
 some (calleeCode (C:=C) c) := rfl

def code {C : Contract} {Γ : Ctx} {F : Frag Γ} {count : Val C Γ .uint}
 (b c : Nat) (reference : Idx Γ (.mem A)) (value : CompiledVal b F count)
 (destination : Idx Γ (.val .uint)) (pointer bottom : Nat) : List Instr :=
 DisjointScalarEntry.code b c reference value ++
 (calleeCode (C:=C) c ++ (ScalarReturn.image (C:=C) c (Frag.init (Parameters A)) pointer bottom ++
 [.mload (c+2),.mstore (cellOf b destination)]))

theorem endpoint {C : Contract} {Γ : Ctx} {L b c frame : Nat} {F : Frag Γ}
 (σ : State C Γ) (reference : Idx Γ (.mem A))
 (ref : HRef σ.H A) (binding : TEnv.get reference σ.env=some ref) (live : 0<σ.heap.len ref .dyn)
 (count : Val C Γ .uint) (value : CompiledVal b F count) (destination : Idx Γ (.val .uint))
 (n : Nat) (bound : n<W) (evaluated : count.evalT σ=.ok (countValue n bound))
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (lo pointer bottom start : Nat) (disjoint : b+Γ.length≤c)
 (locals : c+3≤lo) (above : lo≤pointer) (below : pointer<frame)
 (payload : lo≤start) (separate : pointer<start)
 (bottomAbove : c+3≤bottom) (bottomBelow : bottom<frame) (bottomBefore : bottom<start)
 (bottomSeparate : bottom≠pointer) (capacity : start+2*n≤frame) (fits : start+2*n<W)
 (current : before.mem pointer=.val (wmod start))
 (notFragile : ∀ {R : RefTy} (i : Idx Γ (.alias R)), F.get i≠.fragile) :
 ∃ after addresses,
 run (code b c reference value destination pointer bottom) before=.ok after 0 ∧
 (∀ f depth,(call reference count destination f depth).run σ=
   if n<depth then .ok ⟨(changed σ ref).setLocal destination (countValue n bound),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr L b frame F ((changed σ ref).setLocal destination (countValue n bound)) addresses after ∧
 after.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 after.mem (cellOf b destination)=.val (wmod n) ∧ after.mem (c+2)=.val (wmod n) ∧
 after.mem (c+1)=.val (wmod n) ∧ after.mem c=before.mem (cellOf b reference) ∧
 after.mem pointer=.val (wmod start) ∧ after.mem bottom=.val (wmod start) ∧
 GrowsAllocator b frame 0 σ base before ((changed σ ref).setLocal destination (countValue n bound)) addresses after ∧
 (∀ x,x≠cellOf b destination → x≠pointer → x≠bottom → x≠c → x≠c+1 → x≠c+2 →
   (x<start ∨ start+2*n≤x) → after.mem x=(writeMachine before ((base ref.id).val+1) w[37]).mem x) ∧
 (∀ j,j<n → after.mem (start+2*j)=before.mem (cellOf b reference) ∧
   after.mem (start+2*j+1)=.val (wmod (n-j))) := by
 obtain ⟨actualRef,entered,arguments,entryRun,childRepr,callerRepr,entryStack,entryRef,entryOutside,entryGrowth⟩ :=
   DisjointScalarEntry.entered rfl σ reference count value n bound evaluated base before repr disjoint (by omega)
 have expected : (DisjointScalarEntry.args rfl reference count).evalT σ=.ok (countValue n bound,(some ref,())) := by
   simp only [DisjointScalarEntry.args,Args.evalT,MPath.mvalT,binding,evaluated,ok_bind]
   rfl
 have identical : actualRef=ref := Option.some.inj (congrArg (fun env : TEnv C σ.H (Parameters A) => env.2.1)
   (Except.ok.inj (arguments.symm.trans expected)))
 subst actualRef
 let child := (σ.withEnv (Δ:=Parameters A) (countValue n bound,(some ref,()))).push (t:=.val .uint) (PrimTy.dflt .uint)
 let mutated := changed child ref
 let written := writeMachine entered ((base ref.id).val+1) w[37]
 obtain ⟨word,representedWord,wrote,writeTarget,writeRepr,writeWords⟩ := Footprint.write_local childRepr
   (.there (.there .here)) ref rfl (.simple (.lit 0 rfl)) (.simple (.lit 37 rfl))
   ⟨_,.core _ rfl⟩ ⟨_,.core _ rfl⟩ (⟨0,by decide⟩ : Fin W) rfl
   EffectfulScalarSource.replacement rfl live 0
 have wordEqual : word=w[37] := Restored.value_unique representedWord (ReprV.uint_of rfl)
 rw [wordEqual] at writeTarget writeRepr writeWords
 have writeRun : run (calleeCode (C:=C) c) entered=.ok written 0 := writeTarget
 have position : written.mem pointer=.val (wmod start) :=
   (writeWords pointer (Nat.zero_le _) below).trans
     ((entryOutside pointer (by omega) (by omega) (by omega)).trans current)
 obtain ⟨last,addresses,body,sourceBody,reached,stack,extended,cursor,bottomWord,bodyRef,growth,outside,saved⟩ :=
   ScalarReturn.endpoint (F:=Frag.init (Parameters A)) rfl n bound mutated ref rfl rfl base written writeRepr
     lo pointer bottom start locals above below payload separate bottomAbove bottomBelow bottomBefore bottomSeparate capacity fits position
 have encoded : ReprV .uint (countValue n bound) (.val (wmod n)) := by
   have exactWord : wmod n=(⟨n,bound⟩ : Fin W) := Fin.ext (Nat.mod_eq_of_lt bound)
   rw [exactWord]
   exact ReprV.uint_of rfl
 have result : last.mem (c+2)=.val (wmod n) := Restored.value_unique (reached.core.vals .here) encoded
 let address := cellOf b destination
 let after := writeMachine last address (last.mem (c+2))
 have destinationBelow : address<c := Nat.lt_of_lt_of_le (lvl_lt b destination) disjoint
 have afterRepr : StateRepr L c frame ((Frag.init (Parameters A)).push (.val .uint) .ok)
     (finished mutated n bound) addresses after :=
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
         ((writeWords _ (Nat.zero_le _) (by omega)).trans
           ((entryOutside _ (by omega) (by omega) (by omega)).trans (upd_other before.mem _ target).symm)))
 have counterWord : last.mem (c+1)=.val (wmod n) :=
   Restored.value_unique (reached.core.vals (.there .here : Idx (Frame A) (.val .uint))) encoded
 have restored : StateRepr L b frame F ((changed σ ref).setLocal destination (countValue n bound)) addresses after := by
   have framed := CallerReframe.reframe (σ.setLocal destination (countValue n bound)) (finished mutated n bound)
     (List.prefix_refl _) base addresses (writeMachine before address (.val (wmod n))) after desired afterRepr extended words notFragile
   simpa only [TEnv.wk_self] using framed
 refine ⟨after,addresses,?_,?_,restored,stack.trans entryStack,extended,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · unfold code
   rw [run_append_ok entryRun,run_append_ok writeRun,run_append_ok body]
   rfl
 · intro f depth
   exact EffectfulScalarSource.all_horizons f (DisjointScalarEntry.args rfl reference count) destination
     depth σ n bound ref expected (changed σ ref).heap (write_addr σ ref live)
 · exact (upd_same _ _ _).trans result
 · exact (upd_other last.mem _ (by omega)).trans result
 · exact (upd_other last.mem _ (by omega)).trans counterWord
 · exact (upd_other last.mem _ (by omega)).trans (bodyRef.trans ((writeWords c (Nat.zero_le _) (by omega)).trans entryRef))
 · exact (upd_other last.mem _ (by omega)).trans cursor
 · exact (upd_other last.mem _ (by omega)).trans bottomWord
 · intro allocation positive owner free
   have enteredOwner := entryGrowth allocation positive owner free
   have modified := enteredOwner.setArray ref 0 live EffectfulScalarSource.replacement w[37] (ReprV.uint_of rfl)
   have bodyOwner := growth allocation (by omega) modified free
   simpa only [Nat.add_zero] using bodyOwner.localWrite address
     (Nat.lt_of_lt_of_le positive (le_lvl b destination)) (by omega) (last.mem (c+2))
 · intro x hd hp hb h0 h1 h2 region
   apply (upd_other last.mem _ hd).trans
   apply (outside x hp hb h0 h1 h2 region).trans
   by_cases hit : x=(base ref.id).val+1
   · subst x
     simp only [written,writeMachine,upd,if_true]
   · exact (upd_other entered.mem w[37] hit).trans
       ((entryOutside x h0 h1 h2).trans (upd_other before.mem w[37] hit).symm)

 · intro j small
   exact ⟨(upd_other last.mem _ (by omega)).trans ((saved j small).1.trans ((writeWords c (Nat.zero_le _) (by omega)).trans entryRef)),
     (upd_other last.mem _ (by omega)).trans (saved j small).2⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulScalar
