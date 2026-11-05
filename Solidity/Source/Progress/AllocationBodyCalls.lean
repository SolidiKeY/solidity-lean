import Solidity.Source.Progress.InlineArrayParents
import Solidity.Source.Progress.StructParents
import Solidity.Source.Progress.ReadyBodyCalls

/-! Finite allocation-parent expression prefixes over the existing Source
items. Their memory admission and actual progress are derived, then composed
with modifier-free internal calls. Existing readiness predicates are unchanged. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

inductive AllocationParent (A : Decl → Prop) {Γ : RCtx} : {τ : STy} → RExpr E Γ τ → Prop
  | inline {σ : STy} {m : Nat} {args : RConvArgs E Γ (List.replicate m σ)}
      (word : σ.oneWord = true) : ReadyArgs A args → AllocationParent A (.inlineArray args word)
  | structNew {dn : DeclName} {ps : List STy}
      (typed : (E.structFields dn .memory).map (·.map Prod.snd) = some ps)
      {args : RConvArgs E Γ ps} : ReadyArgs A args → AllocationParent A (.structNew typed args)

theorem AllocationParent.memory {A : Decl → Prop} {Γ : RCtx} {τ : STy}
    {e : RExpr E Γ τ} (parent : AllocationParent A e) : Preservation.BodyExpr A e := by
  cases parent with
  | inline word ready => exact .inlineArray word ready.exact
  | structNew typed ready => exact .structNew typed ready.exact

theorem AllocationParent.ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n : Nat)
    {Γ : RCtx} {τ : STy} {e : RExpr E Γ τ} (parent : AllocationParent A e) :
    NS (evalE G F n e) := by
  cases parent with
  | @inline σ m args word ready => exact inline_array_ns calls F contract n (σ:=σ) (m:=m) args word ready
  | structNew typed ready => exact struct_parent_ns calls F contract n typed _ ready

inductive AllocationItems (A : Decl → Prop) (R : List STy) (M : Bool) :
    {k : SCtx} → {Γ Δ : RCtx} → RItems E R M k Γ Δ → Prop
  | ready {k Γ Δ} {items : RItems E R M k Γ Δ} :
      ReadyItems A R M items → AllocationItems A R M items
  | expr {k Γ Δ τ} {e : RExpr E Γ τ} {rest : RItems E R M k Γ Δ} :
      AllocationParent A e → AllocationItems A R M rest →
      AllocationItems A R M (.stmt (.expr e) rest)

theorem AllocationItems.memory {A : Decl → Prop} {R : List STy} {M : Bool}
    {k : SCtx} {Γ Δ : RCtx} {items : RItems E R M k Γ Δ}
    (ready : AllocationItems A R M items) : Preservation.MemoryItems A R M items := by
  induction ready with
  | ready tail => exact tail.memory
  | expr parent tail ih => exact .stmt (.expr parent.memory) ih

theorem allocation_items_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) : ∀ n, ∀ (F : Fr), F.contract = c → ∀ nps ph
    {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx} (items : RItems E R M k Γ Δ),
    AllocationItems A R M items → ∀ l, BodyFrame nps R Γ →
    NSP (execItems G F n nps ph items l) (fun o=>k.loop = false → o.esc = false)
  | 0, F, contract, nps, ph, _, _, _, _, _, items, ready, l, frame => by
      rw [execItems.eq_1]; exact NSP.halt' trivial
  | n+1, F, contract, nps, ph, R, M, k, Γ, Δ, items, ready, l, frame => by
      cases ready with
      | ready tail => exact (ready_body_at calls (n+1)).items F contract nps ph _ tail l frame
      | @expr τ e rest parent tail =>
        rw [execItems]
        cases n with
        | zero => rw [execS.eq_1]; exact NSP.halt' trivial
        | succ n =>
          have step : NSP (execS G F (n+1) nps ph (.expr (R:=R) (M:=M) (k:=k) e) l)
              (fun out=>∃ last, out = .normal last) := by
            rw [execS]
            exact NSP.bind (NSP.sub' (Q:=fun _=>True) (NSP.weaken
              (NSP.of_ns (AllocationParent.ns calls F contract n parent)) (fun _ _ _=>trivial)))
              (fun pair _=>NSP.pure' ⟨pair.2,rfl⟩)
          refine NSP.bind step (fun out ⟨last,same⟩=>?_)
          cases same
          exact NSP.bind (allocation_items_ns calls (n+1) F contract nps ph _ tail last frame)
            (fun out h=>NSP.weaken (Out.up_esc [] out) (fun _ same loop=>same.trans (h loop)))

theorem run_allocation_body_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (b : RBody E)
    (ready : AllocationItems A b.rs b.inModifier b.items) (l : Locals E.layout b.locals)
    (frame : BodyFrame b.ps.length b.rs b.locals) : ∀ n, NS (runMods G F n b [] l)
  | 0 => by rw [runMods.eq_1]; exact NS.halt' (fun _ h=>by cases h)
  | n+1 => by
    rw [runMods]
    obtain ⟨ys,equality⟩ := RItems.ext b.items
    refine NSP.ns (NSP.bind (R:=fun _=>True)
      (NSP.weaken (allocation_items_ns calls n F contract b.ps.length none b.items ready l frame)
        (fun _ h=>h rfl)) (fun out result=>?_))
    cases out with
    | normal last => exact NSP.of_ns (NS.lift' (Locals.restore_ok' ys equality last))
    | ret last => exact NSP.pure' trivial
    | brk _ | cont _ => exact nomatch result

theorem call_allocation_body_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, ZeroReady E τ)
    (ready : AllocationItems A b.rs b.inModifier b.items) (vs : Vals E.layout ps) :
    ∀ n, NS (callInternal G F n d vs rs)
  | 0 => by rw [callInternal.eq_1]; exact NS.halt' (fun _ h=>by cases h)
  | n+1 => by
    have frameEq : rs.reverseAux (ps.reverseAux []) = b.locals := by
      rw [layout,parameters,returns,List.reverseAux_eq,List.reverseAux_eq,List.append_nil]
    have frame : BodyFrame b.ps.length b.rs b.locals := by
      refine ⟨[],b.ps.reverse,?_,List.length_reverse⟩
      simp only [List.nil_append]
      exact layout
    have resultLayout : b.locals = rs.reverse ++ b.ps.reverse := by rw [layout,returns]
    rw [callInternal,body]
    refine NS.bind (zero_ready_vals_ns n rs defaults) (fun _=>?_)
    rw [dif_pos frameEq,mods]
    exact NS.bind (run_allocation_body_ns calls {F with checked:=true} contract b ready _ frame n)
      (fun last=>NS.bind (NS.lift' (Source.retVals_ok last rs resultLayout)) (fun _=>NS.pure' _))

theorem allocation_body_call_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, ZeroReady E τ)
    (ready : AllocationItems A b.rs b.inModifier b.items) (vs : Vals E.layout ps) (H : HeapTy) (n : Nat) :
    NS (callInternal G F n d vs rs) ∧
    Hoare (fun y=>MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (callInternal G F n d vs rs)
      (fun v y=>MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y=>MemOK E H y) :=
  ⟨call_allocation_body_ns calls F contract d ps rs b body parameters returns layout mods defaults ready vs n,
    Preservation.call_memory_body_mem calls F contract d ps rs b body parameters returns layout mods
      ready.memory vs H n⟩

theorem allocation_body_expr_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (signature : d.fnSig E = some (ps,rs)) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, ZeroReady E τ)
    (ready : AllocationItems A b.rs b.inModifier b.items)
    {Γ : RCtx} (args : RConvArgs E Γ ps) (argsOK : ReadyArgs A args) (H : HeapTy) (n : Nat) :
    NS (evalE G F (n+1) (.call d signature args)) ∧
    Hoare (MemOK E H) (evalE G F (n+1) (.call d signature args))
      (fun v y=>MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y=>MemOK E H y) := by
  have progress : NS (evalE G F (n+1) (.call d signature args)) := by
    rw [evalE]
    refine NS.bind (eval_ready_args_ns calls F contract n args argsOK) (fun vs=>?_)
    refine NS.bind ?_ (fun _=>NS.pure' _)
    exact NSP.ns (NSP.sub' (Q:=fun _=>True) (NSP.weaken
      (NSP.of_ns (call_allocation_body_ns calls F contract d ps rs b body parameters returns layout mods defaults ready vs n))
      (fun _ _ _=>trivial)))
  exact ⟨progress,Preservation.eval_memory_call_mem calls F contract d ps rs signature b
    body parameters returns layout mods ready.memory args argsOK.exact H n⟩

theorem allocation_body_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (F : Fr) (contract : F.contract = c) (ps rs : List STy)
    (d : {d : Decl // d ∈ Solidity.Lowering.P9.WholeProgram.functions res ∧ d.fnSig res.env = some (ps,rs)})
    (b : RBody res.env) (body : G.prog.body (G.dispatchFn F.contract d.val) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, ZeroReady res.env τ)
    (ready : AllocationItems (fun d=>d ∈ values) b.rs b.inModifier b.items)
    (vs : Vals res.env.layout ps) (H : HeapTy) (n : Nat) :
    NS (callInternal G F n d.val vs rs) ∧
    Hoare (fun y=>MemOK res.env H y ∧ RValsOK res.env y.2.heap.ty vs.toR) (callInternal G F n d.val vs rs)
      (fun v y=>MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y=>MemOK res.env H y) :=
  allocation_body_call_progress_and_memory
    (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    F contract d.val ps rs b body parameters returns layout mods defaults ready vs H n

#print axioms AllocationParent.memory
#print axioms AllocationParent.ns
#print axioms AllocationItems.memory
#print axioms allocation_items_ns
#print axioms run_allocation_body_ns
#print axioms call_allocation_body_ns
#print axioms allocation_body_call_progress_and_memory
#print axioms allocation_body_expr_progress_and_memory
#print axioms allocation_body_from_elaborate
end Solidity.Source.Progress
