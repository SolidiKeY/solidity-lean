import Solidity.Yul.Adapters.HeapWriteback

/-! Actual typed Source object replacement, independent of physical decoding.
The input is the existing dependent Data packet consumed by owner heapPut. -/
namespace Solidity.Yul.Adapters.ObjectWriteback
variable {E : Source.Env} {Γ : Source.RCtx}

/-- All required owner data invariants, not a new or weakened MemOK. -/
def Prepared (y : Source.EMState E Γ) (x : Σ τ, Source.Data E.layout τ) : Prop :=
  Source.DataOK E y.2.heap.ty x.2 ∧ x.2.Top ∧ x.2.Inner

theorem success (y : Source.EMState E Γ) (a : Nat) (x : Σ τ, Source.Data E.layout τ)
    (typed : y.2.heap.ty a=some x.1) :
    (Source.heapPut a x).run y=
      (.ok (), (y.1,{y.2 with heap:=y.2.heap.write a x.2 typed})) := by
  rw [Source.heapPut,Source.Hoare.run_bind]
  change ((if h : y.2.heap.ty a=some x.1 then
    Source.EM.setSt {y.2 with heap:=y.2.heap.write a x.2 h}
    else Source.EM.halt (.stuck "memory write type")) : Source.EM E Γ Unit).run y=_
  rw [dif_pos typed]
  rfl

theorem failure (y : Source.EMState E Γ) (a : Nat) (x : Σ τ, Source.Data E.layout τ)
    (wrong : y.2.heap.ty a≠some x.1) :
    (Source.heapPut a x).run y=(.error (.stuck "memory write type"),y) := by
  rw [Source.heapPut,Source.Hoare.run_bind]
  change ((if h : y.2.heap.ty a=some x.1 then
    Source.EM.setSt {y.2 with heap:=y.2.heap.write a x.2 h}
    else Source.EM.halt (.stuck "memory write type")) : Source.EM E Γ Unit).run y=_
  rw [dif_neg wrong]
  rfl

/-- Every original-H owner MemOK conjunct is transported, on BOTH success and
halt. Input facts concern actual typed data, never desired output safety. -/
theorem memOK (y : Source.EMState E Γ) (a : Nat) (x : Σ τ, Source.Data E.layout τ)
    (data : Prepared y x) (H : Source.HeapTy) (ok : Source.MemOK E H y) :
    Source.MemOK E H ((Source.heapPut a x).run y).2 := by
  have typed:=Source.heapPut_pres (E:=E) (Γ:=Γ) (H:=H) a x y ⟨ok.1,data.1⟩
  have shaped:=Source.heapPut_top (E:=E) (Γ:=Γ) a x y ⟨ok.2.1,data.2.1⟩
  have inner:=Source.heapPut_inner (E:=E) (Γ:=Γ) a x y ⟨ok.2.2,data.2.2⟩
  cases run : (Source.heapPut a x : Source.EM E Γ Unit).run y with
  | mk result z=>
    rw [run] at typed shaped inner
    cases result <;> exact ⟨typed,shaped,inner⟩

/-- Unchanged typed contents preserve the WHOLE Source machine and locals. -/
theorem unchanged (y : Source.EMState E Γ) (a : Nat) (x : Σ τ, Source.Data E.layout τ)
    (found : y.2.heap.get a=some x) :
    (Source.heapPut a x).run y=(.ok (),y) := by
  have typed : y.2.heap.ty a=some x.1 := by
    change (y.2.heap.get a).map Sigma.fst=some x.1
    rw [found];rfl
  rw [success y a x typed,HeapWriteback.heap_write_same _ _ _ typed found]

/-- Exact selected readback, every other heap cell, every type, finite next,
locals and ALL nonheap state fields, for every actual declared object type. -/
theorem writeback (y : Source.EMState E Γ) (a : Nat) (x : Σ τ, Source.Data E.layout τ)
    (typed : y.2.heap.ty a=some x.1) :
    ∃ z : Source.EMState E Γ,
      (Source.heapPut a x).run y=(.ok (),z) ∧ z.2.heap.get a=some x ∧
      (∀ b,b≠a → z.2.heap.get b=y.2.heap.get b) ∧ z.2.heap.ty=y.2.heap.ty ∧
      z.2.heap.next=y.2.heap.next ∧ z.1=y.1 ∧ z.2={y.2 with heap:=z.2.heap} := by
  refine ⟨(y.1,{y.2 with heap:=y.2.heap.write a x.2 typed}),success y a x typed,?_,?_,?_,rfl,rfl,rfl⟩
  · exact Source.Heap.write_get y.2.heap a x.2 typed
  · intro b hb;exact Source.Heap.write_other y.2.heap hb x.2 typed
  · funext b;exact Source.Heap.write_ty y.2.heap a b x.2 typed
/-- A list of the owner's existing typed heapPut requests, not an alternate
object representation or evaluator. -/
abbrev Request (E : Source.Env) := Nat × (Σ τ, Source.Data E.layout τ)

def putAll : List (Request E) → Source.EM E Γ Unit
  | []=>pure ()
  | (a,x)::xs=>do Source.heapPut a x;putAll xs

/-- Every actual object type composes. Input data invariants are checked against
the ORIGINAL heap typing, transported by the proved unchanged typing. -/
theorem all_types (y : Source.EMState E Γ) (xs : List (Request E))
    (ready : ∀ request∈xs, y.2.heap.ty request.1=some request.2.1 ∧ Prepared y request.2) :
    ∃ z, (putAll xs).run y=(.ok (),z) ∧ z.2.heap.ty=y.2.heap.ty ∧
      z.2.heap.next=y.2.heap.next ∧ z.1=y.1 ∧ z.2={y.2 with heap:=z.2.heap} ∧
      (∀ b,(∀ request∈xs,b≠request.1) → z.2.heap.get b=y.2.heap.get b) ∧
      (∀ H : Source.HeapTy, Source.MemOK E H y → Source.MemOK E H z) := by
  induction xs generalizing y with
  | nil=>exact ⟨y,rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl,fun _ h=>h⟩
  | cons request xs ih=>
    obtain ⟨a,x⟩:=request
    have head:=ready (a,x) (List.mem_cons_self)
    obtain ⟨z,run,found,others,types,next,locals,state⟩:=writeback y a x head.1
    have rest : ∀ request∈xs,z.2.heap.ty request.1=some request.2.1 ∧ Prepared z request.2 := by
      intro request hr
      have h:=ready request (List.mem_cons_of_mem _ hr)
      rw [types]
      exact ⟨h.1,by simpa only [Prepared,types] using h.2⟩
    obtain ⟨final,tail,ty,nx,ls,st,other,mem⟩:=ih z rest
    refine ⟨final,?_,ty.trans types,nx.trans next,ls.trans locals,?_,?_,?_⟩
    · rw [putAll,Source.Hoare.run_bind,run];exact tail
    · rw [st,state]
    · intro b hb
      exact (other b (fun request hr=>hb request (List.mem_cons_of_mem _ hr))).trans
        (others b (hb (a,x) List.mem_cons_self))
    · intro H ok
      apply mem H
      have keep:=memOK y a x head.2 H ok
      rw [run] at keep
      exact keep

theorem all_unchanged (y : Source.EMState E Γ) (xs : List (Request E))
    (found : ∀ request∈xs,y.2.heap.get request.1=some request.2) :
    (putAll xs).run y=(.ok (),y) := by
  induction xs with
  | nil=>rfl
  | cons request xs ih=>
    obtain ⟨a,x⟩:=request
    rw [putAll,Source.Hoare.run_bind,unchanged y a x (found (a,x) List.mem_cons_self)]
    exact ih (fun request hr=>found request (List.mem_cons_of_mem _ hr))
/-- Distinct actual typed heap writes commute on the COMPLETE heap; same-root
aliases deliberately have no such premise-free order law. -/
theorem heap_commute {D : Source.Layout} (h : Source.Heap D) (a b : Nat)
    {τ υ : Source.STy} (x : Source.Data D τ) (u : Source.Data D υ)
    (tx : h.ty a=some τ) (tu : h.ty b=some υ) (different : a≠b) :
    (h.write a x tx).write b u ((Source.Heap.write_ty h a b x tx).trans tu)=
      (h.write b u tu).write a x ((Source.Heap.write_ty h b a u tu).trans tx) := by
  cases h with
  | mk cells next bounded=>
    change (⟨(fun k=>if k=b then some ⟨υ,u⟩ else if k=a then some ⟨τ,x⟩ else cells k),next,_⟩ : Source.Heap D)=
      ⟨(fun k=>if k=a then some ⟨τ,x⟩ else if k=b then some ⟨υ,u⟩ else cells k),next,_⟩
    congr 1
    funext k
    by_cases ka : k=a <;> by_cases kb : k=b
    · exact False.elim (different (ka.symm.trans kb))
    · simp only [ka,different,↓reduceIte]
    · simp only [kb,Ne.symm different,↓reduceIte]
    · simp only [ka,kb,↓reduceIte]
theorem putAll_append (xs ys : List (Request E)) :
    (putAll (Γ:=Γ) (xs++ys))=(putAll xs >>= fun _=>putAll ys) := by
  induction xs with
  | nil=>rfl
  | cons request xs ih=>simp only [List.cons_append,putAll,ih,bind_assoc]

/-- A later type error retains the successful all-type caller prefix, exactly
as the actual Source monad specifies. No rollback is supplied by this lemma. -/
theorem late_type_error (y : Source.EMState E Γ) (xs : List (Request E))
    (ready : ∀ request∈xs,y.2.heap.ty request.1=some request.2.1 ∧ Prepared y request.2)
    (a : Nat) (x : Σ τ, Source.Data E.layout τ) (wrong : y.2.heap.ty a≠some x.1) :
    ∃ z, (putAll xs).run y=(.ok (),z) ∧
      (putAll (xs++[(a,x)])).run y=(.error (.stuck "memory write type"),z) ∧
      (∀ H : Source.HeapTy, Source.MemOK E H y → Source.MemOK E H z) := by
  obtain ⟨z,run,types,next,locals,state,other,mem⟩:=all_types y xs ready
  refine ⟨z,run,?_,mem⟩
  rw [putAll_append,Source.Hoare.run_bind,run]
  change (putAll [(a,x)]).run z=_
  rw [putAll,Source.Hoare.run_bind,failure z a x (by rw [types];exact wrong)]
end Solidity.Yul.Adapters.ObjectWriteback
