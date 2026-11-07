import Solidity.Source.Progress.AllocationBodyCalls
import Solidity.Source.Progress.AggregateDefaults

/-! Allocation parents bound to new locals before an unchanged ready suffix.
Progress follows the actual declaration, growing local frame and scope exit;
preservation derives from MemoryItems. Original certificates are unchanged. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

inductive BoundParentItems (A : Decl → Prop) (R : List STy) (M : Bool) :
    {k : SCtx} → {Γ Δ : RCtx} → RItems E R M k Γ Δ → Prop
  | ready {k Γ Δ} {items : RItems E R M k Γ Δ} :
      ReadyItems A R M items → BoundParentItems A R M items
  | initialized {k Γ Δ τ} {e : RExpr E Γ τ}
      {rest : RItems E R M k (τ :: Γ) Δ}
      (same : τ.implicit E.isBase E.mapFree τ = true) :
      PlainResultType τ → AllocationParent A e → BoundParentItems A R M rest →
      BoundParentItems A R M (.stmt (.declInit e same) rest)

theorem BoundParentItems.memory {A : Decl → Prop} {R : List STy} {M : Bool}
    {k : SCtx} {Γ Δ : RCtx} {items : RItems E R M k Γ Δ}
    (ready : BoundParentItems A R M items) : Preservation.MemoryItems A R M items := by
  induction ready with
  | ready tail => exact tail.memory
  | initialized same plain parent tail ih => exact .stmt (.declInit same parent.memory) ih

theorem bound_parent_items_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) : ∀ n, ∀ (F : Fr), F.contract = c → ∀ nps ph
    {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx} (items : RItems E R M k Γ Δ),
    BoundParentItems A R M items → ∀ l, BodyFrame nps R Γ →
    NSP (execItems G F n nps ph items l) (fun o=>k.loop = false → o.esc = false)
  | 0, F, contract, nps, ph, _, _, _, _, _, items, ready, l, frame => by
      rw [execItems.eq_1]; exact NSP.halt' trivial
  | n+1, F, contract, nps, ph, R, M, k, Γ, Δ, items, ready, l, frame => by
      cases ready with
      | ready tail => exact (ready_body_at calls (n+1)).items F contract nps ph _ tail l frame
      | @initialized _ _ τ e rest same plain parent tail =>
        rw [execItems]
        cases n with
        | zero => rw [execS.eq_1];exact NSP.halt' trivial
        | succ n =>
          have step : NSP (execS G F (n+1) nps ph
              (.declInit (R:=R) (M:=M) (k:=k) e same) l)
              (fun out=>∃ last, out = .normal last) := by
            rw [execS]
            have child : NS (do getV (← convRV F n τ (← evalE G F n e))) := by
              refine NS.bind (parent.ns calls F contract n) (fun v=>?_)
              simp only [convRV,↓reduceDIte,pure_bind]
              exact getV_plain_ns plain v
            exact NSP.bind (NSP.sub' (Q:=fun _=>True) (NSP.weaken
              (NSP.of_ns child) (fun _ _ _=>trivial))) (fun pair _=>NSP.pure' ⟨_,rfl⟩)
          refine NSP.bind step (fun out ⟨last,equal⟩=>?_)
          cases equal
          exact NSP.bind (bound_parent_items_ns calls (n+1) F contract nps ph _ tail last (frame.ext [τ]))
            (fun out h=>NSP.weaken (Out.up_esc [τ] out) (fun _ same loop=>same.trans (h loop)))

theorem run_bound_parent_body_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (b : RBody E)
    (ready : BoundParentItems A b.rs b.inModifier b.items) (l : Locals E.layout b.locals)
    (frame : BodyFrame b.ps.length b.rs b.locals) : ∀ n, NS (runMods G F n b [] l)
  | 0 => by rw [runMods.eq_1]; exact NS.halt' (fun _ h=>by cases h)
  | n+1 => by
    rw [runMods]
    obtain ⟨ys,equality⟩ := RItems.ext b.items
    refine NSP.ns (NSP.bind (R:=fun _=>True)
      (NSP.weaken (bound_parent_items_ns calls n F contract b.ps.length none b.items ready l frame)
        (fun _ h=>h rfl)) (fun out result=>?_))
    cases out with
    | normal last => exact NSP.of_ns (NS.lift' (Locals.restore_ok' ys equality last))
    | ret last => exact NSP.pure' trivial
    | brk _ | cont _ => exact nomatch result

theorem call_bound_parent_body_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, FiniteDefault E τ)
    (ready : BoundParentItems A b.rs b.inModifier b.items) (vs : Vals E.layout ps) :
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
    refine NS.bind (finite_default_vals_ns n rs defaults) (fun _=>?_)
    rw [dif_pos frameEq,mods]
    exact NS.bind (run_bound_parent_body_ns calls {F with checked:=true} contract b ready _ frame n)
      (fun last=>NS.bind (NS.lift' (Source.retVals_ok last rs resultLayout)) (fun _=>NS.pure' _))

theorem bound_parent_body_call_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, FiniteDefault E τ)
    (ready : BoundParentItems A b.rs b.inModifier b.items) (vs : Vals E.layout ps) (H : HeapTy) (n : Nat) :
    NS (callInternal G F n d vs rs) ∧
    Hoare (fun y=>MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (callInternal G F n d vs rs)
      (fun v y=>MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y=>MemOK E H y) :=
  ⟨call_bound_parent_body_ns calls F contract d ps rs b body parameters returns layout mods defaults ready vs n,
    Preservation.call_memory_body_mem calls F contract d ps rs b body parameters returns layout mods
      ready.memory vs H n⟩

theorem bound_parent_body_expr_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (signature : d.fnSig E = some (ps,rs)) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, FiniteDefault E τ)
    (ready : BoundParentItems A b.rs b.inModifier b.items)
    {Γ : RCtx} (args : RConvArgs E Γ ps) (argsOK : ReadyArgs A args) (H : HeapTy) (n : Nat) :
    NS (evalE G F (n+1) (.call d signature args)) ∧
    Hoare (MemOK E H) (evalE G F (n+1) (.call d signature args))
      (fun v y=>MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y=>MemOK E H y) := by
  have progress : NS (evalE G F (n+1) (.call d signature args)) := by
    rw [evalE]
    refine NS.bind (eval_ready_args_ns calls F contract n args argsOK) (fun vs=>?_)
    refine NS.bind ?_ (fun _=>NS.pure' _)
    exact NSP.ns (NSP.sub' (Q:=fun _=>True) (NSP.weaken
      (NSP.of_ns (call_bound_parent_body_ns calls F contract d ps rs b body parameters returns layout mods defaults ready vs n))
      (fun _ _ _=>trivial)))
  exact ⟨progress,Preservation.eval_memory_call_mem calls F contract d ps rs signature b
    body parameters returns layout mods ready.memory args argsOK.exact H n⟩

theorem bound_parent_body_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (F : Fr) (contract : F.contract = c) (ps rs : List STy)
    (d : {d : Decl // d ∈ Solidity.Lowering.P9.WholeProgram.functions res ∧ d.fnSig res.env = some (ps,rs)})
    (b : RBody res.env) (body : G.prog.body (G.dispatchFn F.contract d.val) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, FiniteDefault res.env τ)
    (ready : BoundParentItems (fun d=>d ∈ values) b.rs b.inModifier b.items)
    (vs : Vals res.env.layout ps) (H : HeapTy) (n : Nat) :
    NS (callInternal G F n d.val vs rs) ∧
    Hoare (fun y=>MemOK res.env H y ∧ RValsOK res.env y.2.heap.ty vs.toR) (callInternal G F n d.val vs rs)
      (fun v y=>MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y=>MemOK res.env H y) :=
  bound_parent_body_call_progress_and_memory
    (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    F contract d.val ps rs b body parameters returns layout mods defaults ready vs H n


#print axioms BoundParentItems.memory
#print axioms bound_parent_items_ns
#print axioms run_bound_parent_body_ns
#print axioms call_bound_parent_body_ns
#print axioms bound_parent_body_call_progress_and_memory
#print axioms bound_parent_body_expr_progress_and_memory
#print axioms bound_parent_body_from_elaborate
end Solidity.Source.Progress
