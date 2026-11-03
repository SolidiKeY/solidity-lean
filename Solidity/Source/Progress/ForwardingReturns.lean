import Solidity.Source.Progress.CallComposition

/-! Single-return bodies may forward a certified composed expression, including
ordinary calls to earlier ready memory callees. This derives body and call
progress/preservation from expression composition, not a body oracle. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

theorem return_composed_nsp {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    {n : Nat} (context : CompositionAt A G c ds n) (F : Fr) (contract : F.contract = c)
    (nps : Nat) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (same : τ.implicit E.isBase τ = true) (plain : PlainResultType τ)
    (ready : ComposedExpr A (fun d => d ∈ ds) e) (l : Locals E.layout Γ)
    (frame : BodyFrame nps [τ] Γ) :
    NSP (execS G F (n+1) nps none (.retVal (M := false) (k := .body) rfl e same) l)
      (fun out => ∃ last, out = .ret last) := by
  rw [execS]
  have child : NS (do getV (← convRV F n τ (← evalE G F n e))) := by
    refine NS.bind (context.expr F contract e ready (Heap.empty : Heap E.layout).ty).1 (fun v => ?_)
    simp only [convRV,↓reduceDIte,pure_bind]
    exact getV_plain_ns plain v
  obtain ⟨ys,ps,rfl,length⟩ := frame
  refine NSP.bind (NSP.sub' (Q := fun _ => True)
    (NSP.weaken (NSP.of_ns child) (fun _ _ _ => trivial))) (fun p _ => ?_)
  have offset : (ys ++ ([τ].reverse ++ ps)).length - (nps + [τ].length) = ys.length := by
    simp only [List.length_append,List.length_reverse,List.length_singleton]
    omega
  rw [offset]
  exact NSP.bind (NSP.lift_ok (Locals.setAt_ok' ys rfl p.2 p.1))
    (fun last _ => NSP.pure' ⟨last,rfl⟩)

theorem return_composed_mem {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    {n : Nat} (context : CompositionAt A G c ds n) (F : Fr) (contract : F.contract = c)
    (nps : Nat) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (same : τ.implicit E.isBase τ = true) (ready : ComposedExpr A (fun d => d ∈ ds) e)
    (l : Locals E.layout Γ) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
      (execS G F (n+1) nps none (.retVal (M := false) (k := .body) rfl e same) l)
      (fun o y => MemOK E H y ∧ ∃ last, o = .ret last ∧ LocalsOK E y.2.heap.ty last)
      (fun _ y => MemOK E H y) := by
  have child : ∀ H', Hoare (MemOK E H')
      (do getV (← convRV F n τ (← evalE G F n e)))
      (fun v y => MemOK E H' y ∧ v.RefOK E y.2.heap.ty) (fun _ y => MemOK E H' y) := by
    intro H'
    refine Hoare.bind (context.expr F contract e ready H').2 (fun v => ?_)
    simp only [convRV,↓reduceDIte,pure_bind]
    exact Preservation.getV_ref_mem v H'
  rw [execS]
  refine Hoare.bind (Preservation.sub_result_mem l _ (fun v st => v.RefOK E st.heap.ty) child H) (fun r => ?_)
  refine Hoare.bind (Hoare.lift' (r := r.2.setAt (Γ.length - (nps + [τ].length)) r.1)
    (Q := fun last y => MemOK E H y ∧ LocalsOK E y.2.heap.ty last) (fun y valid => ?_)) (fun last => ?_)
  · cases actual : r.2.setAt (Γ.length - (nps + [τ].length)) r.1 with
    | error e => exact valid.1
    | ok last => exact ⟨valid.1,Preservation.localsSetAt_ok _ r.2 r.1 last valid.2.1 valid.2.2 actual⟩
  · exact Hoare.pure' (fun _ valid => ⟨valid.1,last,rfl,valid.2⟩)

theorem forwarding_items {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    (compositions : ∀ n, CompositionAt A G c ds n) (F : Fr) (contract : F.contract = c)
    (ps : List STy) (τ : STy) (e : RExpr E (returnContext ps τ) τ)
    (same : τ.implicit E.isBase τ = true) (plain : PlainResultType τ)
    (ready : ComposedExpr A (fun d => d ∈ ds) e)
    (l : Locals E.layout (returnContext ps τ)) (H : HeapTy) :
    ∀ n, NSP (execItems G F n ps.length none (singleReturningBody ps τ e same).items l)
        (fun out => ∃ last, out = .ret last) ∧
      Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
        (execItems G F n ps.length none (singleReturningBody ps τ e same).items l)
        (fun o y => MemOK E H y ∧ Preservation.OutRefsOK (E := E) y.2.heap.ty o)
        (fun _ y => MemOK E H y)
  | 0 => by
    rw [execItems.eq_1]
    exact ⟨NSP.halt' trivial,Hoare.halt' (fun _ h => h.1)⟩
  | 1 => by
    simp only [singleReturningBody,execItems,execS,bind]
    exact ⟨NSP.halt' trivial,Hoare.halt' (fun _ h => h.1)⟩
  | n+2 => by
    have frame : BodyFrame ps.length [τ] (returnContext ps τ) := by
      refine ⟨[],ps.reverse,?_,List.length_reverse⟩
      simp only [returnContext,List.reverseAux_eq,List.append_nil,List.nil_append]
    constructor
    · simp only [singleReturningBody]
      rw [execItems]
      refine NSP.bind (return_composed_nsp (compositions n) F contract ps.length e same plain ready l frame)
        (fun out returned => ?_)
      rcases returned with ⟨last,rfl⟩
      exact NSP.pure' ⟨last,rfl⟩
    · simp only [singleReturningBody]
      rw [execItems]
      refine Hoare.bind (return_composed_mem (compositions n) F contract ps.length e same ready l H) (fun out => ?_)
      intro state valid
      rcases valid.2 with ⟨last,rfl,locals⟩
      exact ⟨valid.1,locals⟩

theorem forwarding_body {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    (compositions : ∀ n, CompositionAt A G c ds n) (F : Fr) (contract : F.contract = c)
    (ps : List STy) (τ : STy) (e : RExpr E (returnContext ps τ) τ)
    (same : τ.implicit E.isBase τ = true) (plain : PlainResultType τ)
    (ready : ComposedExpr A (fun d => d ∈ ds) e)
    (l : Locals E.layout (returnContext ps τ)) (H : HeapTy) :
    ∀ n, NS (runMods G F n (singleReturningBody ps τ e same) [] l) ∧
      Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
        (runMods G F n (singleReturningBody ps τ e same) [] l)
        (fun last y => MemOK E H y ∧ LocalsOK E y.2.heap.ty last) (fun _ y => MemOK E H y)
  | 0 => by
    rw [runMods.eq_1]
    exact ⟨NS.halt' (fun _ h => by cases h),Hoare.halt' (fun _ h => h.1)⟩
  | n+1 => by
    have items := forwarding_items compositions F contract ps τ e same plain ready l H n
    constructor
    · rw [runMods]
      refine NSP.ns (NSP.bind (R := fun _ => True) items.1 (fun out returned => ?_))
      rcases returned with ⟨last,rfl⟩
      exact NSP.pure' trivial
    · exact Preservation.runBody_mem G F n (singleReturningBody ps τ e same) l H items.2

theorem forwarding_call {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    (compositions : ∀ n, CompositionAt A G c ds n) (F : Fr) (contract : F.contract = c)
    (d : Decl) (ps : List STy) (τ : STy) (e : RExpr E (returnContext ps τ) τ)
    (same : τ.implicit E.isBase τ = true) (plain : PlainResultType τ)
    (ready : ComposedExpr A (fun d => d ∈ ds) e) (defaults : ZeroReady E τ)
    (body : G.prog.body (G.dispatchFn F.contract d) = some (singleReturningBody ps τ e same))
    (vs : Vals E.layout ps) (H : HeapTy) :
    ∀ n, NS (callInternal G F n d vs [τ]) ∧
      Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR)
        (callInternal G F n d vs [τ])
        (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y)
  | 0 => by
    rw [callInternal.eq_1]
    exact ⟨NS.halt' (fun _ h => by cases h),Hoare.halt' (fun _ h => h.1)⟩
  | n+1 => by
    have frameEq : [τ].reverseAux (ps.reverseAux []) = (singleReturningBody ps τ e same).locals := rfl
    constructor
    · simp only [callInternal,body]
      refine NS.bind (zero_ready_vals_ns n [τ] (fun σ member => ?_)) (fun rv => ?_)
      · rcases List.mem_singleton.mp member with rfl
        exact defaults
      · rw [dif_pos frameEq]
        refine NS.bind (forwarding_body compositions {F with checked := true} contract ps τ e same plain ready _ H n).1
          (fun last => ?_)
        have layout : returnContext ps τ = [τ].reverse ++ ps.reverse := by
          simp only [returnContext,List.reverseAux_eq,List.append_nil]
        exact NS.bind (NS.lift' (Source.retVals_ok last [τ] layout)) (fun _ => NS.pure' _)
    · exact Preservation.callFrame_mem G F n d vs [τ] (singleReturningBody ps τ e same) body frameEq rfl
        (fun H' l => (forwarding_body compositions {F with checked := true} contract ps τ e same plain ready l H' n).2) H

theorem extend_forwarding_calls {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    (values : CallsOK A G c) (prior : ReadyMemoryCalls G c ds) (d : Decl)
    (ps : List STy) (τ : STy) (signature : d.fnSig E = some (ps,[τ]))
    (e : RExpr E (returnContext ps τ) τ) (same : τ.implicit E.isBase τ = true)
    (plain : PlainResultType τ) (ready : ComposedExpr A (fun d => d ∈ ds) e) (defaults : ZeroReady E τ)
    (body : G.prog.body (G.dispatchFn c d) = some (singleReturningBody ps τ e same)) :
    ReadyMemoryCalls G c (d :: ds) := by
  intro F contract called inputs outputs calledSig member vs H n
  rcases List.mem_cons.mp member with selected | earlier
  · subst called
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (signature.symm.trans calledSig))
    exact forwarding_call (composition_at values prior) F contract d ps τ e same plain ready defaults
      (by rw [contract]; exact body) vs H n
  · exact prior F contract called calledSig earlier vs H n

theorem forwarding_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values memory : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (catalogue : ReadyMemoryCatalogue (fun d => d ∈ values) G c memory)
    (F : Fr) (contract : F.contract = c) (ps : List STy) (τ : STy)
    (d : {d : Decl // d ∈ Solidity.Lowering.P9.WholeProgram.functions res ∧ d.fnSig res.env = some (ps,[τ])})
    (e : RExpr res.env (returnContext ps τ) τ) (same : τ.implicit res.env.isBase τ = true)
    (plain : PlainResultType τ) (ready : ComposedExpr (fun d => d ∈ values) (fun d => d ∈ memory) e)
    (defaults : ZeroReady res.env τ)
    (body : G.prog.body (G.dispatchFn F.contract d.val) = some (singleReturningBody ps τ e same))
    (vs : Vals res.env.layout ps) (H : HeapTy) (n : Nat) :
    NS (callInternal G F n d.val vs [τ]) ∧
      Hoare (fun y => MemOK res.env H y ∧ RValsOK res.env y.2.heap.ty vs.toR)
        (callInternal G F n d.val vs [τ])
        (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) :=
  forwarding_call (composition_from_elaborate res elaborated G program c values memory checked catalogue)
    F contract d.val ps τ e same plain ready defaults body vs H n

#print axioms return_composed_mem
#print axioms forwarding_call
#print axioms extend_forwarding_calls
#print axioms forwarding_from_elaborate
end Solidity.Source.Progress
