import Solidity.Source.Progress.ReadyCatalogue

/-! Finite composition of certified ordinary calls inside intrinsic expressions
and exact argument lists. Callee admission is derived separately from actual
elaboration; no recursive memory-call body graph is introduced. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

mutual
inductive ComposedExpr (A B : Decl → Prop) {Γ : RCtx} : {τ : STy} → RExpr E Γ τ → Prop
  | base {τ} {e : RExpr E Γ τ} : ReadyExpr A e → ComposedExpr A B e
  | call {d : Decl} {ps rs : List STy} (signature : d.fnSig E = some (ps,rs))
      {args : RConvArgs E Γ ps} : B d → ComposedArgs A B args →
      ComposedExpr A B (.call d signature args)
  | same {τ} {e : RExpr E Γ τ} (identity : Conv E.isBase τ τ) :
      ComposedExpr A B e → ComposedExpr A B (.conv e identity)
  | branch {τ} {condition : RExpr E Γ .bool} {yes no : RExpr E Γ τ} :
      ComposedExpr A B condition → ComposedExpr A B yes → ComposedExpr A B no →
      ComposedExpr A B (.cond condition yes no)
  | newArray {τ σ : STy} (ready : NewReady E τ) {len : RExpr E Γ σ}
      (indexable : σ.isIndex = true) : ComposedExpr A B len →
      ComposedExpr A B (.newArray ready.newable len indexable)
inductive ComposedArgs (A B : Decl → Prop) {Γ : RCtx} :
    {ts : List STy} → RConvArgs E Γ ts → Prop
  | nil : ComposedArgs A B .nil
  | cons {τ ts} {e : RExpr E Γ τ} {es : RConvArgs E Γ ts}
      (same : τ.implicit E.isBase τ = true) (plain : PlainResultType τ) :
      ComposedExpr A B e → ComposedArgs A B es → ComposedArgs A B (.cons e same es)
end

theorem sub_ready_memory_call_mem {G : Glob E} {c : String} {ds : List Decl}
    (calls : ReadyMemoryCalls G c ds) (F : Fr) (contract : F.contract = c)
    (d : Decl) {ps rs : List STy} (signature : d.fnSig E = some (ps,rs)) (member : d ∈ ds)
    (vs : Vals E.layout ps) (H : HeapTy) (n : Nat) {Γ : RCtx} :
    Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR)
      (sub .nil (callInternal G F n d vs rs) : EM E Γ _)
      (fun r y => MemOK E H y ∧ RValOK E y.2.heap.ty r.1) (fun _ y => MemOK E H y) := by
  intro ⟨l,s⟩ ⟨outer,args⟩
  have result := (calls F contract d signature member vs s.heap.ty n).2
    (.nil,s) ⟨Preservation.relocalize outer.self .nil trivial,args⟩
  unfold EM.sub
  rcases actual : (callInternal G F n d vs rs).run (.nil,s) with ⟨r,⟨last,after⟩⟩
  rw [actual] at result
  have finish (valid : MemOK E s.heap.ty (last,after)) : MemOK E H (l,after) :=
    Preservation.relocalize (valid.weaken outer.le) l (LocalsOK.mono valid.le l outer.1.2)
  have actual' : callInternal G F n d vs rs (.nil,s) = (r,(last,after)) := actual
  cases r with
  | ok a =>
    simp only [ExceptT.run,ExceptT.mk,actual']
    exact ⟨finish result.1,result.2⟩
  | error e =>
    simp only [ExceptT.run,ExceptT.mk,actual']
    exact finish result

structure CompositionAt (A : Decl → Prop) (G : Glob E) (c : String) (ds : List Decl) (n : Nat) : Prop where
  expr : ∀ F, F.contract = c → ∀ {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ),
    ComposedExpr A (fun d => d ∈ ds) e → ∀ H,
    NS (evalE G F n e) ∧
    Hoare (MemOK E H) (evalE G F n e)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y)
  args : ∀ F, F.contract = c → ∀ {Γ : RCtx} {ts : List STy} (es : RConvArgs E Γ ts),
    ComposedArgs A (fun d => d ∈ ds) es → ∀ H,
    NS (evalConvArgs G F n es) ∧
    Hoare (MemOK E H) (evalConvArgs G F n es)
      (fun vs y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (fun _ y => MemOK E H y)

theorem composed_expr_step {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl} {n : Nat}
    (values : CallsOK A G c) (calls : ReadyMemoryCalls G c ds) (ih : CompositionAt A G c ds n)
    (F : Fr) (contract : F.contract = c) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (ready : ComposedExpr A (fun d => d ∈ ds) e) (H : HeapTy) :
    NS (evalE G F (n+1) e) ∧
    Hoare (MemOK E H) (evalE G F (n+1) e)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  cases ready with
  | base certified => exact ready_progress_and_preservation values F contract (n+1) e certified H
  | @call d ps rs signature args member arguments =>
    have evaluated := ih.args F contract args arguments H
    constructor
    · rw [evalE]
      refine NS.bind evaluated.1 (fun vs => NS.bind ?_ (fun _ => NS.pure' _))
      exact NSP.ns (NSP.sub' (Q := fun _ => True) (NSP.weaken
        (NSP.of_ns (calls F contract d signature member vs H n).1) (fun _ _ _ => trivial)))
    · rw [evalE]
      exact Hoare.bind evaluated.2 (fun vs =>
        Hoare.bind (sub_ready_memory_call_mem calls F contract d signature member vs H n)
          (fun r => Hoare.pure' (fun _ h => h)))
  | @same τ e identity child =>
    have evaluated := ih.expr F contract e child H
    constructor
    · rw [evalE]
      exact NS.bind evaluated.1 (fun v => by simp only [convRV]; exact NS.pure' _)
    · rw [evalE]
      exact Hoare.bind evaluated.2 (fun v => by
        simp only [convRV]
        exact Hoare.pure' (fun _ h => h))
  | @branch τ guard yes no condition left right =>
    have tested := ih.expr F contract guard condition H
    constructor
    · rw [evalE]
      refine NS.bind tested.1 (fun v => NS.bind (getV_ns rfl v) (fun x => ?_))
      split
      · exact (ih.expr F contract yes left H).1
      · exact (ih.expr F contract no right H).1
    · rw [evalE]
      refine Hoare.bind (Hoare.conseq tested.2 (fun _ h => h) (fun _ _ h => h.1) (fun _ _ h => h)) (fun v => ?_)
      refine Hoare.bind (Preservation.MemPres.getV' v H) (fun x => ?_)
      split
      · exact (ih.expr F contract yes left H).2
      · exact (ih.expr F contract no right H).2
  | newArray ready indexable child =>
    have len := ih.expr F contract _ child H
    exact ⟨eval_new_ns G F n ready _ indexable len.1,
      Solidity.Roadmap.V16.SSCP2.NewAllocation.eval_new_mem _ _ G F n H _ _ ready.newable _ indexable
        (Hoare.conseq len.2 (fun _ h => h) (fun _ _ h => h.1) (fun _ _ h => h))⟩

theorem composed_args_step {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl} {n : Nat}
    (ih : CompositionAt A G c ds n) (F : Fr) (contract : F.contract = c)
    {Γ : RCtx} {ts : List STy} (es : RConvArgs E Γ ts)
    (ready : ComposedArgs A (fun d => d ∈ ds) es) (H : HeapTy) :
    NS (evalConvArgs G F (n+1) es) ∧
    Hoare (MemOK E H) (evalConvArgs G F (n+1) es)
      (fun vs y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (fun _ y => MemOK E H y) := by
  cases ready with
  | nil => exact ⟨NS.pure' _,Hoare.pure' (fun _ h => ⟨h,trivial⟩)⟩
  | @cons τ ts e es same plain head tail =>
    have first := ih.expr F contract e head H
    constructor
    · rw [evalConvArgs]
      refine NS.bind first.1 (fun v => ?_)
      simp only [convRV,↓reduceDIte,pure_bind]
      exact NS.bind (getV_plain_ns plain v) (fun _ =>
        NS.bind (ih.args F contract es tail H).1 (fun _ => NS.pure' _))
    · rw [evalConvArgs]
      refine Hoare.bind first.2 (fun v => ?_)
      simp only [convRV,↓reduceDIte,pure_bind]
      refine Hoare.bind (Preservation.getV_ref_mem v H) (fun x => ?_)
      refine Hoare.bind (Hoare.memGrow (R := fun H' => x.RefOK E H')
        (fun H' => (ih.args F contract es tail H').2)) (fun vs => ?_)
      refine Hoare.pure' (fun y h => ?_)
      rcases h.2.2 with ⟨H',valid,growth⟩
      exact ⟨h.1,Val.RefOK.mono growth valid,h.2.1⟩

theorem composition_at {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    (values : CallsOK A G c) (calls : ReadyMemoryCalls G c ds) : ∀ n, CompositionAt A G c ds n
  | 0 => {
      expr := by intros; exact ⟨NS.halt' (fun _ h => by cases h),Hoare.halt' (fun _ h => h)⟩
      args := by intros; exact ⟨NS.halt' (fun _ h => by cases h),Hoare.halt' (fun _ h => h)⟩ }
  | n+1 => {
      expr := composed_expr_step values calls (composition_at values calls n)
      args := composed_args_step (composition_at values calls n) }

theorem composition_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (catalogue : ReadyMemoryCatalogue (fun d => d ∈ values) G c ds) (n : Nat) :
    CompositionAt (fun d => d ∈ values) G c ds n :=
  composition_at (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    (ready_memory_from_elaborate res elaborated G program c values ds checked catalogue) n

theorem composition_program_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values memory : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (catalogue : ReadyMemoryCatalogue (fun d => d ∈ values) G c memory)
    (complete : readyCoverage res values memory = true) (n : Nat) :
    CompositionAt (fun d => d ∈ values) G c (Solidity.Lowering.P9.WholeProgram.functions res) n :=
  composition_at (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    (ready_memory_program_calls res elaborated G program c values memory checked catalogue complete) n

#print axioms sub_ready_memory_call_mem
#print axioms composition_at
#print axioms composition_from_elaborate
#print axioms composition_program_from_elaborate
end Solidity.Source.Progress
