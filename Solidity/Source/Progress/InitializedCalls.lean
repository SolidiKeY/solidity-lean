import Solidity.Source.Progress.InitializedPrefixes

/-! Modifier-free internal calls with initialized-local prefixes and one return.
Frame packing, defaults and the final return extraction are the existing source
operations. The items certificate supplies progress and memory preservation. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

def initializedBody (ps : List STy) (τ : STy) {Δ : RCtx}
    (items : RItems E [τ] false .body (returnContext ps τ) Δ) : RBody E :=
  {ps := ps,rs := [τ],inModifier := false,locals := returnContext ps τ,out := Δ,items := items}

theorem initialized_body {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    (compositions : ∀ n, CompositionAt A G c ds n) (F : Fr) (contract : F.contract = c)
    (ps : List STy) (τ : STy) {Δ : RCtx}
    (items : RItems E [τ] false .body (returnContext ps τ) Δ)
    (ready : InitializedReturns A (fun d => d ∈ ds) τ items)
    (l : Locals E.layout (returnContext ps τ)) (H : HeapTy) :
    ∀ n, NS (runMods G F n (initializedBody ps τ items) [] l) ∧
      Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
        (runMods G F n (initializedBody ps τ items) [] l)
        (fun last y => MemOK E H y ∧ LocalsOK E y.2.heap.ty last) (fun _ y => MemOK E H y)
  | 0 => by
    rw [runMods.eq_1]
    exact ⟨NS.halt' (fun _ h => by cases h),Hoare.halt' (fun _ h => h.1)⟩
  | n+1 => by
    have frame : BodyFrame ps.length [τ] (returnContext ps τ) := by
      refine ⟨[],ps.reverse,?_,List.length_reverse⟩
      simp only [returnContext,List.reverseAux_eq,List.append_nil,List.nil_append]
    have body := initialized_prefix_items compositions F contract ps.length n items ready l frame H
    constructor
    · simp only [initializedBody,runMods]
      obtain ⟨ys,ext⟩ := RItems.ext items
      refine NSP.ns (NSP.bind (R := fun _ => True) body.1 (fun out safe => ?_))
      cases out with
      | normal last => exact NSP.of_ns (NS.lift' (Locals.restore_ok' ys ext last))
      | ret last => exact NSP.pure' trivial
      | brk _ => exact nomatch safe
      | cont _ => exact nomatch safe
    · exact Preservation.runBody_mem G F n (initializedBody ps τ items) l H body.2

theorem initialized_call {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    (compositions : ∀ n, CompositionAt A G c ds n) (F : Fr) (contract : F.contract = c)
    (d : Decl) (ps : List STy) (τ : STy) {Δ : RCtx} (items : RItems E [τ] false .body (returnContext ps τ) Δ)
    (ready : InitializedReturns A (fun d => d ∈ ds) τ items) (defaults : ZeroReady E τ)
    (body : G.prog.body (G.dispatchFn F.contract d) = some (initializedBody ps τ items))
    (vs : Vals E.layout ps) (H : HeapTy) :
    ∀ n, NS (callInternal G F n d vs [τ]) ∧
      Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR)
        (callInternal G F n d vs [τ])
        (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y)
  | 0 => by
    rw [callInternal.eq_1]
    exact ⟨NS.halt' (fun _ h => by cases h),Hoare.halt' (fun _ h => h.1)⟩
  | n+1 => by
    have frameEq : [τ].reverseAux (ps.reverseAux []) = (initializedBody ps τ items).locals := rfl
    constructor
    · simp only [callInternal,body]
      refine NS.bind (zero_ready_vals_ns n [τ] (fun σ member => ?_)) (fun rv => ?_)
      · rcases List.mem_singleton.mp member with rfl
        exact defaults
      · rw [dif_pos frameEq]
        refine NS.bind (initialized_body compositions {F with checked := true} contract ps τ items ready _ H n).1
          (fun last => ?_)
        have layout : returnContext ps τ = [τ].reverse ++ ps.reverse := by
          simp only [returnContext,List.reverseAux_eq,List.append_nil]
        exact NS.bind (NS.lift' (Source.retVals_ok last [τ] layout)) (fun _ => NS.pure' _)
    · exact Preservation.callFrame_mem G F n d vs [τ] (initializedBody ps τ items) body frameEq rfl
        (fun H' l => (initialized_body compositions {F with checked := true} contract ps τ items ready l H' n).2) H

theorem extend_initialized_calls {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    (values : CallsOK A G c) (prior : ReadyMemoryCalls G c ds) (d : Decl)
    (ps : List STy) (τ : STy) (signature : d.fnSig E = some (ps,[τ]))
    {Δ : RCtx} (items : RItems E [τ] false .body (returnContext ps τ) Δ)
    (ready : InitializedReturns A (fun d => d ∈ ds) τ items) (defaults : ZeroReady E τ)
    (body : G.prog.body (G.dispatchFn c d) = some (initializedBody ps τ items)) :
    ReadyMemoryCalls G c (d :: ds) := by
  intro F contract called inputs outputs calledSig member vs H n
  rcases List.mem_cons.mp member with selected | earlier
  · subst called
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (signature.symm.trans calledSig))
    exact initialized_call (composition_at values prior) F contract d ps τ items ready defaults
      (by rw [contract]; exact body) vs H n
  · exact prior F contract called calledSig earlier vs H n

theorem initialized_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values memory : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (catalogue : ReadyMemoryCatalogue (fun d => d ∈ values) G c memory)
    (F : Fr) (contract : F.contract = c) (ps : List STy) (τ : STy)
    (d : {d : Decl // d ∈ Solidity.Lowering.P9.WholeProgram.functions res ∧ d.fnSig res.env = some (ps,[τ])})
    {Δ : RCtx} (items : RItems res.env [τ] false .body (returnContext ps τ) Δ)
    (ready : InitializedReturns (fun d => d ∈ values) (fun d => d ∈ memory) τ items)
    (defaults : ZeroReady res.env τ)
    (body : G.prog.body (G.dispatchFn F.contract d.val) = some (initializedBody ps τ items))
    (vs : Vals res.env.layout ps) (H : HeapTy) (n : Nat) :
    NS (callInternal G F n d.val vs [τ]) ∧
      Hoare (fun y => MemOK res.env H y ∧ RValsOK res.env y.2.heap.ty vs.toR)
        (callInternal G F n d.val vs [τ])
        (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) :=
  initialized_call (composition_from_elaborate res elaborated G program c values memory checked catalogue)
    F contract d.val ps τ items ready defaults body vs H n

#print axioms initialized_body
#print axioms initialized_call
end Solidity.Source.Progress
