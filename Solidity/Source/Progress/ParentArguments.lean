import Solidity.Source.Progress.AllocationBodyCalls
import Solidity.Source.Progress.AggregateDefaults

/-! Exact direct-call arguments may be ready expressions or allocation
parents with ready children. This additive certificate derives actual
left-to-right argument evaluation and keeps earlier references valid through
later heap growth. It does not change the existing argument certificates. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

inductive ParentArgument (A : Decl → Prop) {Γ : RCtx} : {τ : STy} → RExpr E Γ τ → Prop
  | ready {τ} {e : RExpr E Γ τ} : ReadyExpr A e → ParentArgument A e
  | parent {τ} {e : RExpr E Γ τ} : AllocationParent A e → ParentArgument A e

theorem ParentArgument.memory {A : Decl → Prop} {Γ : RCtx} {τ : STy}
    {e : RExpr E Γ τ} (ready : ParentArgument A e) : Preservation.BodyExpr A e := by
  cases ready with
  | ready h => exact .base h.allocating
  | parent h => exact h.memory

theorem ParentArgument.ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n : Nat)
    {Γ : RCtx} {τ : STy} {e : RExpr E Γ τ} (ready : ParentArgument A e) : NS (evalE G F n e) := by
  cases ready with
  | ready h => exact eval_ready_expr_ns calls F contract n e h
  | parent h => exact h.ns calls F contract n

inductive ParentArgs (A : Decl → Prop) {Γ : RCtx} : {ts : List STy} → RConvArgs E Γ ts → Prop
  | nil : ParentArgs A .nil
  | cons {τ ts} {e : RExpr E Γ τ} {tail : RConvArgs E Γ ts}
      (same : τ.implicit E.isBase E.mapFree τ = true) (plain : PlainResultType τ) :
      ParentArgument A e → ParentArgs A tail → ParentArgs A (.cons e same tail)

theorem eval_parent_args_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) :
    ∀ n {Γ : RCtx} {ts : List STy} (args : RConvArgs E Γ ts),
      ParentArgs A args → NS (evalConvArgs G F n args)
  | 0, _, _, _, _ => NS.halt' (fun _ h=>by cases h)
  | n+1, _, _, _, ready => by
    cases ready with
    | nil => exact NS.pure' _
    | cons same plain head tail =>
      rw [evalConvArgs]
      refine NS.bind (head.ns calls F contract n) (fun v=>?_)
      simp only [convRV,↓reduceDIte,pure_bind]
      refine NS.bind (getV_plain_ns plain v) (fun _=>?_)
      exact NS.bind (eval_parent_args_ns calls F contract n _ tail) (fun _=>NS.pure' _)

theorem eval_parent_args_mem {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) :
    ∀ n {Γ : RCtx} {ts : List STy} (args : RConvArgs E Γ ts), ParentArgs A args → ∀ H,
      Hoare (MemOK E H) (evalConvArgs G F n args)
        (fun vs y=>MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (fun _ y=>MemOK E H y)
  | 0, _, _, _, _, _ => by rw [evalConvArgs.eq_1];exact Hoare.halt' (fun _ h=>h)
  | n+1, _, _, _, ready, H => by
    cases ready with
    | nil => exact Hoare.pure' (fun _ h=>⟨h,trivial⟩)
    | cons same plain head tail =>
      rw [evalConvArgs]
      refine Hoare.bind (Preservation.eval_body_expr_mem calls F contract n _ head.memory H) (fun v=>?_)
      simp only [convRV,↓reduceDIte,pure_bind]
      refine Hoare.bind (Preservation.getV_ref_mem v H) (fun x=>?_)
      refine Hoare.bind (Hoare.memGrow (R:=fun H'=>x.RefOK E H')
        (fun H'=>eval_parent_args_mem calls F contract n _ tail H')) (fun vs=>?_)
      refine Hoare.pure' (fun y h=>?_)
      rcases h.2.2 with ⟨H',reference,growth⟩
      exact ⟨h.1,Val.RefOK.mono growth reference,h.2.1⟩

theorem call_ready_finite_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, FiniteDefault E τ)
    (ready : ReadyItems A b.rs b.inModifier b.items) (vs : Vals E.layout ps) :
    ∀ n, NS (callInternal G F n d vs rs)
  | 0 => by rw [callInternal.eq_1];exact NS.halt' (fun _ h=>by cases h)
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
    exact NS.bind (run_ready_body_ns calls {F with checked:=true} contract b ready _ frame n)
      (fun last=>NS.bind (NS.lift' (Source.retVals_ok last rs resultLayout)) (fun _=>NS.pure' _))

theorem parent_args_call_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (signature : d.fnSig E = some (ps,rs)) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, FiniteDefault E τ) (ready : ReadyItems A b.rs b.inModifier b.items)
    {Γ : RCtx} (args : RConvArgs E Γ ps) (admitted : ParentArgs A args) (H : HeapTy) (n : Nat) :
    NS (evalE G F (n+1) (.call d signature args)) ∧
    Hoare (MemOK E H) (evalE G F (n+1) (.call d signature args))
      (fun v y=>MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y=>MemOK E H y) := by
  constructor
  · rw [evalE]
    refine NS.bind (eval_parent_args_ns calls F contract n args admitted) (fun vs=>?_)
    refine NS.bind ?_ (fun _=>NS.pure' _)
    exact NSP.ns (NSP.sub' (Q:=fun _=>True) (NSP.weaken
      (NSP.of_ns (call_ready_finite_ns calls F contract d ps rs b body parameters returns layout mods defaults ready vs n))
      (fun _ _ _=>trivial)))
  · rw [evalE]
    refine Hoare.bind (eval_parent_args_mem calls F contract n args admitted H) (fun vs=>?_)
    exact Hoare.bind (Preservation.sub_memory_body_mem calls F contract d ps rs b body
      parameters returns layout mods ready.memory vs H n) (fun r=>Hoare.pure' (fun _ h=>h))

theorem parent_args_call_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (F : Fr) (contract : F.contract = c) (ps rs : List STy)
    (d : {d : Decl // d ∈ Solidity.Lowering.P9.WholeProgram.functions res ∧
      d.fnSig res.env = some (ps,rs)})
    (b : RBody res.env) (body : G.prog.body (G.dispatchFn F.contract d.val) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, FiniteDefault res.env τ)
    (ready : ReadyItems (fun d=>d ∈ values) b.rs b.inModifier b.items)
    {Γ : RCtx} (args : RConvArgs res.env Γ ps) (admitted : ParentArgs (fun d=>d ∈ values) args)
    (H : HeapTy) (n : Nat) :
    NS (evalE G F (n+1) (.call d.val d.property.2 args)) ∧
    Hoare (MemOK res.env H) (evalE G F (n+1) (.call d.val d.property.2 args))
      (fun v y=>MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y=>MemOK res.env H y) :=
  parent_args_call_progress_and_memory
    (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    F contract d.val ps rs d.property.2 b body parameters returns layout mods defaults ready args admitted H n

#print axioms ParentArgument.memory
#print axioms ParentArgument.ns
#print axioms eval_parent_args_ns
#print axioms eval_parent_args_mem
#print axioms call_ready_finite_ns
#print axioms parent_args_call_progress_and_memory
#print axioms parent_args_call_from_elaborate
end Solidity.Source.Progress
