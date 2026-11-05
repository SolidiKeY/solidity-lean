import Solidity.Source.Progress.AggregateDefaults
import Solidity.Source.Progress.AllocationBodyCalls
import Solidity.Source.Progress.ReadyReturns

/-! Returning actual allocating parents from modifier-free ordinary internal
bodies. The body constructor and call evaluator are reused; parent progress,
finite aggregate defaults and memory preservation are derived syntactically.
No body execution or desired poststate is an admission premise. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

theorem return_parent_nsp {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n nps : Nat)
    (ph : Option (Ph E)) {Γ : RCtx} {τ : STy}
    (e : RExpr E Γ τ) (same : τ.implicit E.isBase τ = true)
    (plain : PlainResultType τ) (ready : AllocationParent A e) (l : Locals E.layout Γ)
    (frame : BodyFrame nps [τ] Γ) :
    NSP (execS G F (n+1) nps ph (.retVal (M := false) (k := .body) rfl e same) l)
      (fun out => ∃ last, out = .ret last) := by
  rw [execS]
  have child : NS (do getV (← convRV F n τ (← evalE G F n e))) := by
    refine NS.bind (AllocationParent.ns calls F contract n ready) (fun v => ?_)
    simp only [convRV,↓reduceDIte,pure_bind]
    exact getV_plain_ns plain v
  obtain ⟨ys,ps,rfl,length⟩ := frame
  refine NSP.bind (NSP.sub' (Q := fun _ => True)
    (NSP.weaken (NSP.of_ns child) (fun _ _ _ => trivial))) (fun p _ => ?_)
  have base : (ys ++ ([τ].reverse ++ ps)).length - (nps + [τ].length) = ys.length := by
    simp only [List.length_append,List.length_reverse,List.length_singleton]
    omega
  rw [base]
  exact NSP.bind (NSP.lift_ok (Locals.setAt_ok' ys rfl p.2 p.1))
    (fun last _ => NSP.pure' ⟨last,rfl⟩)

theorem parent_return_items_nsp {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (ps : List STy) (τ : STy)
    (e : RExpr E (returnContext ps τ) τ) (same : τ.implicit E.isBase τ = true)
    (plain : PlainResultType τ) (ready : AllocationParent A e) (l : Locals E.layout (returnContext ps τ)) :
    ∀ n, NSP (execItems G F n ps.length none (singleReturningBody ps τ e same).items l)
      (fun out => ∃ last, out = .ret last)
  | 0 => NSP.halt' trivial
  | 1 => by
    simp only [singleReturningBody,execItems,execS,bind]
    exact NSP.halt' trivial
  | n+2 => by
    have frame : BodyFrame ps.length [τ] (returnContext ps τ) := by
      refine ⟨[],ps.reverse,?_,List.length_reverse⟩
      simp only [returnContext,List.reverseAux_eq,List.append_nil,List.nil_append]
    simp only [singleReturningBody]
    rw [execItems]
    refine NSP.bind (return_parent_nsp calls F contract n ps.length none e same plain ready l frame)
      (fun out returned => ?_)
    rcases returned with ⟨last,rfl⟩
    exact NSP.pure' ⟨last,rfl⟩

theorem run_parent_return_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (ps : List STy) (τ : STy)
    (e : RExpr E (returnContext ps τ) τ) (same : τ.implicit E.isBase τ = true)
    (plain : PlainResultType τ) (ready : AllocationParent A e) (l : Locals E.layout (returnContext ps τ)) :
    ∀ n, NS (runMods G F n (singleReturningBody ps τ e same) [] l)
  | 0 => by rw [runMods.eq_1]; exact NS.halt' (fun _ h => by cases h)
  | n+1 => by
    rw [runMods]
    refine NSP.ns (NSP.bind (R := fun _ => True)
      (parent_return_items_nsp calls F contract ps τ e same plain ready l n) (fun out returned => ?_))
    rcases returned with ⟨last,rfl⟩
    exact NSP.pure' trivial

theorem call_parent_return_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps : List STy) (τ : STy) (e : RExpr E (returnContext ps τ) τ)
    (same : τ.implicit E.isBase τ = true) (plain : PlainResultType τ)
    (ready : AllocationParent A e) (defaults : FiniteDefault E τ)
    (body : G.prog.body (G.dispatchFn F.contract d) = some (singleReturningBody ps τ e same))
    (vs : Vals E.layout ps) : ∀ n, NS (callInternal G F n d vs [τ])
  | 0 => by rw [callInternal.eq_1]; exact NS.halt' (fun _ h => by cases h)
  | n+1 => by
    simp only [callInternal,body]
    refine NS.bind (finite_default_vals_ns n [τ] (fun σ member => ?_)) (fun rv => ?_)
    · rcases List.mem_singleton.mp member with rfl
      exact defaults
    · have frameEq : [τ].reverseAux (ps.reverseAux []) = (singleReturningBody ps τ e same).locals := rfl
      rw [dif_pos frameEq]
      refine NS.bind (run_parent_return_ns calls {F with checked := true} contract ps τ e same plain ready _ n)
        (fun last => ?_)
      have layout : returnContext ps τ = [τ].reverse ++ ps.reverse := by
        simp only [returnContext,List.reverseAux_eq,List.append_nil]
      exact NS.bind (NS.lift' (Source.retVals_ok last [τ] layout)) (fun _ => NS.pure' _)

theorem parent_return_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps : List STy) (τ : STy) (e : RExpr E (returnContext ps τ) τ)
    (same : τ.implicit E.isBase τ = true) (plain : PlainResultType τ)
    (ready : AllocationParent A e) (defaults : FiniteDefault E τ)
    (body : G.prog.body (G.dispatchFn F.contract d) = some (singleReturningBody ps τ e same))
    (vs : Vals E.layout ps) (H : HeapTy) (n : Nat) :
    NS (callInternal G F n d vs [τ]) ∧
    Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (callInternal G F n d vs [τ])
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  have layout : (singleReturningBody ps τ e same).locals =
      (singleReturningBody ps τ e same).rs.reverse ++ (singleReturningBody ps τ e same).ps.reverse := by
    simp only [singleReturningBody,returnContext,List.reverseAux_eq,List.append_nil]
  exact ⟨call_parent_return_ns calls F contract d ps τ e same plain ready defaults body vs n,
    Preservation.call_memory_body_mem calls F contract d ps [τ] (singleReturningBody ps τ e same)
      body rfl rfl layout rfl (.stmt (.returnValue rfl same ready.memory) .nil) vs H n⟩

theorem parent_return_expr_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps : List STy) (τ : STy) (signature : d.fnSig E = some (ps,[τ]))
    (e : RExpr E (returnContext ps τ) τ) (same : τ.implicit E.isBase τ = true)
    (plain : PlainResultType τ) (ready : AllocationParent A e) (defaults : FiniteDefault E τ)
    (body : G.prog.body (G.dispatchFn F.contract d) = some (singleReturningBody ps τ e same))
    {Γ : RCtx} (args : RConvArgs E Γ ps) (argsOK : ReadyArgs A args) (H : HeapTy) (n : Nat) :
    NS (evalE G F (n+1) (.call d signature args)) ∧
    Hoare (MemOK E H) (evalE G F (n+1) (.call d signature args))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  have progress : NS (evalE G F (n+1) (.call d signature args)) := by
    rw [evalE]
    refine NS.bind (eval_ready_args_ns calls F contract n args argsOK) (fun vs => ?_)
    refine NS.bind ?_ (fun _ => NS.pure' _)
    exact NSP.ns (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns (call_parent_return_ns calls F contract d ps τ e same plain ready defaults body vs n))
      (fun _ _ _ => trivial)))
  have layout : (singleReturningBody ps τ e same).locals =
      (singleReturningBody ps τ e same).rs.reverse ++ (singleReturningBody ps τ e same).ps.reverse := by
    simp only [singleReturningBody,returnContext,List.reverseAux_eq,List.append_nil]
  exact ⟨progress,Preservation.eval_memory_call_mem calls F contract d ps [τ] signature
    (singleReturningBody ps τ e same) body rfl rfl layout rfl
    (.stmt (.returnValue rfl same ready.memory) .nil) args argsOK.exact H n⟩

theorem parent_return_from_elaborate (res : Resolution) (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (F : Fr) (contract : F.contract = c) (ps : List STy) (τ : STy)
    (d : {d : Decl // d ∈ Solidity.Lowering.P9.WholeProgram.functions res ∧
      d.fnSig res.env = some (ps,[τ])})
    (e : RExpr res.env (returnContext ps τ) τ) (same : τ.implicit res.env.isBase τ = true)
    (plain : PlainResultType τ) (ready : AllocationParent (fun d => d ∈ values) e) (defaults : FiniteDefault res.env τ)
    (body : G.prog.body (G.dispatchFn F.contract d.val) = some (singleReturningBody ps τ e same))
    (vs : Vals res.env.layout ps) (H : HeapTy) (n : Nat) :
    NS (callInternal G F n d.val vs [τ]) ∧
    Hoare (fun y => MemOK res.env H y ∧ RValsOK res.env y.2.heap.ty vs.toR) (callInternal G F n d.val vs [τ])
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) :=
  parent_return_progress_and_memory
    (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    F contract d.val ps τ e same plain ready defaults body vs H n

theorem parent_return_expr_from_elaborate (res : Resolution) (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (F : Fr) (contract : F.contract = c) (ps : List STy) (τ : STy)
    (d : {d : Decl // d ∈ Solidity.Lowering.P9.WholeProgram.functions res ∧ d.fnSig res.env = some (ps,[τ])})
    (e : RExpr res.env (returnContext ps τ) τ) (same : τ.implicit res.env.isBase τ = true)
    (plain : PlainResultType τ) (ready : AllocationParent (fun d => d ∈ values) e) (defaults : FiniteDefault res.env τ)
    (body : G.prog.body (G.dispatchFn F.contract d.val) = some (singleReturningBody ps τ e same))
    {Γ : RCtx} (args : RConvArgs res.env Γ ps) (argsOK : ReadyArgs (fun d => d ∈ values) args)
    (H : HeapTy) (n : Nat) :
    NS (evalE G F (n+1) (.call d.val d.property.2 args)) ∧
    Hoare (MemOK res.env H) (evalE G F (n+1) (.call d.val d.property.2 args))
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) :=
  parent_return_expr_progress_and_memory
    (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    F contract d.val ps τ d.property.2 e same plain ready defaults body args argsOK H n


#print axioms return_parent_nsp
#print axioms parent_return_items_nsp
#print axioms run_parent_return_ns
#print axioms call_parent_return_ns
#print axioms parent_return_progress_and_memory
#print axioms parent_return_expr_progress_and_memory
#print axioms parent_return_from_elaborate
#print axioms parent_return_expr_from_elaborate
end Solidity.Source.Progress
