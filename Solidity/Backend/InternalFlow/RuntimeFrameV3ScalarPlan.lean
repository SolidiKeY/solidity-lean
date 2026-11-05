import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarEmitterSound

/-! Packaging the scalar-family code in the frozen runtime-frame metadata.
Arena demand depends on the quotation index, not a hand-picked caller or a
success predicate. These lemmas do not establish approved-profile admission
or inhabit the universal V3 producer. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPlan
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

def plan {C : Contract} {Γ : Ctx} {R : RefTy} {b c selectedFrame pointer bottom : Nat}
 {F : Frag Γ} {count : Val C Γ .uint}
 (emitted : ScalarEmitter.Emission b c selectedFrame pointer bottom F count)
 (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint)) : InterfaceV1.RecursiveEmission C Γ Γ :=
 ⟨emitted.code reference destination,fun _ => F,fun _ => c+3-b,pointer,pointer,
   fun depth _ => max (Γ.length+1) (2*(depth-1)),fun _ _ => 0⟩

theorem entered_capacity {C : Contract} {Γ : Ctx} {R : RefTy}
 {b c selectedFrame pointer bottom L frame depth : Nat} {F : Frag Γ} {count : Val C Γ .uint}
 (emitted : ScalarEmitter.Emission b c selectedFrame pointer bottom F count)
 (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint))
 {caller : State C Γ} {base : Nat → Fin W} {before : Machine} {start : Nat}
 (entry : InterfaceV1.Entry ((plan emitted reference destination).at depth) L b frame F caller base before start)
 (n : Nat) (enough : n<depth) :
 pointer<start ∧ c+3≤start ∧ start+2*n≤frame ∧ start+2*n<W := by
 have above : pointer≤start := entry.payloadAbove
 have space : start+max (Γ.length+1) (2*(depth-1))≤frame := entry.reserve
 have fits : start+max (Γ.length+1) (2*(depth-1))<W := entry.noWrap
 have minimum := Nat.le_max_left (Γ.length+1) (2*(depth-1))
 have amount := Nat.le_max_right (Γ.length+1) (2*(depth-1))
 have apart : pointer<start := by
   rcases entry.separate with left | right
   · exact left
   · change start+max (Γ.length+1) (2*(depth-1))≤pointer at right
     omega
 have locals := emitted.geometry.2.1
 exact ⟨apart,by omega,by omega,by omega⟩

theorem returned_of_eval {C : Contract} {Γ : Ctx} {R : RefTy}
 {b c selectedFrame pointer bottom L frame depth : Nat} {F : Frag Γ} {count : Val C Γ .uint}
 (emitted : ScalarEmitter.Emission b c selectedFrame pointer bottom F count)
 (below : bottom<pointer) (hm : (Ty.ref R).mapFree=true)
 (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint))
 {caller : State C Γ} {base : Nat → Fin W} {before : Machine} {start : Nat}
 (entry : InterfaceV1.Entry ((plan emitted reference destination).at depth) L b frame F caller base before start)
 (n : Nat) (bound : n<W) (evaluated : count.evalT caller=.ok (countValue n bound)) (enough : n<depth) :
 InterfaceV1.Returned ((plan emitted reference destination).at depth) L b frame caller base before start
   ⟨caller.setLocal destination (countValue n bound),List.prefix_refl _⟩ := by
 obtain ⟨apart,payload,capacity,fits⟩ := entered_capacity emitted reference destination entry n enough
 have pointerBound : pointer<frame := entry.pointerBelow
 let actual : ScalarEmitter.Emission b c frame pointer bottom F count :=
   ⟨emitted.value,emitted.geometry.1,emitted.geometry.2.1,pointerBound,
    emitted.geometry.2.2.2.1,by omega,by omega⟩
 obtain ⟨after,addresses,executed,source,reached,stack,extended,result,privateWord,counter,alias,cursor,bottomWord,growth,outside,saved⟩ :=
   ScalarEmitter.endpoint hm caller reference count actual destination n bound evaluated base before entry.represented
     start payload apart (by omega) capacity fits entry.cursor
 refine ⟨after,addresses,executed,reached,stack,extended,growth,cursor,?_⟩
 intro x lower upper
 change pointer≤x at lower
 by_cases same : x=pointer
 · subst x
   exact cursor.trans entry.cursor.symm
 · have address := lvl_lt b destination
   have disjoint := emitted.geometry.1
   have locals := emitted.geometry.2.1
   exact outside x (by change x≠lvl b destination;omega) same (by omega) (by omega) (by omega) (by omega) (.inl upper)

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPlan
