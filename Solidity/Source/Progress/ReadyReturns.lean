import Solidity.Source.Progress.ReadyDefaults
import Solidity.Source.Preservation.MemoryBodyCalls

/-! Actual single-return memory bodies and calls. Return-slot default progress
is proved from ZeroReady; body progress follows ready expression evaluation and
checked frame writes. Preservation reuses the existing memory-body simulation.
No arbitrary memory-call graph, modifier or transaction progress is assumed. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

abbrev returnContext (ps : List STy) (τ : STy) : RCtx := [τ].reverseAux (ps.reverseAux [])

def singleReturningBody (ps : List STy) (τ : STy)
    (e : RExpr E (returnContext ps τ) τ) (same : τ.implicit E.isBase τ = true) : RBody E :=
  {ps := ps,rs := [τ],inModifier := false,locals := returnContext ps τ,out := returnContext ps τ,
   items := .stmt (.retVal rfl e same) .nil}

theorem return_ready_nsp {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n nps : Nat)
    (ph : Option (Ph E)) {Γ : RCtx} {τ : STy}
    (e : RExpr E Γ τ) (same : τ.implicit E.isBase τ = true)
    (plain : PlainResultType τ) (ready : ReadyExpr A e) (l : Locals E.layout Γ)
    (frame : BodyFrame nps [τ] Γ) :
    NSP (execS G F (n+1) nps ph (.retVal (M := false) (k := .body) rfl e same) l)
      (fun out => ∃ last, out = .ret last) := by
  rw [execS]
  have child : NS (do getV (← convRV F n τ (← evalE G F n e))) := by
    refine NS.bind (eval_ready_expr_ns calls F contract n e ready) (fun v => ?_)
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

theorem single_return_items_nsp {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (ps : List STy) (τ : STy)
    (e : RExpr E (returnContext ps τ) τ) (same : τ.implicit E.isBase τ = true)
    (plain : PlainResultType τ) (ready : ReadyExpr A e) (l : Locals E.layout (returnContext ps τ)) :
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
    refine NSP.bind (return_ready_nsp calls F contract n ps.length none e same plain ready l frame)
      (fun out returned => ?_)
    rcases returned with ⟨last,rfl⟩
    exact NSP.pure' ⟨last,rfl⟩

theorem run_single_return_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (ps : List STy) (τ : STy)
    (e : RExpr E (returnContext ps τ) τ) (same : τ.implicit E.isBase τ = true)
    (plain : PlainResultType τ) (ready : ReadyExpr A e) (l : Locals E.layout (returnContext ps τ)) :
    ∀ n, NS (runMods G F n (singleReturningBody ps τ e same) [] l)
  | 0 => by rw [runMods.eq_1]; exact NS.halt' (fun _ h => by cases h)
  | n+1 => by
    rw [runMods]
    refine NSP.ns (NSP.bind (R := fun _ => True)
      (single_return_items_nsp calls F contract ps τ e same plain ready l n) (fun out returned => ?_))
    rcases returned with ⟨last,rfl⟩
    exact NSP.pure' trivial

theorem call_single_return_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps : List STy) (τ : STy) (e : RExpr E (returnContext ps τ) τ)
    (same : τ.implicit E.isBase τ = true) (plain : PlainResultType τ)
    (ready : ReadyExpr A e) (defaults : ZeroReady E τ)
    (body : G.prog.body (G.dispatchFn F.contract d) = some (singleReturningBody ps τ e same))
    (vs : Vals E.layout ps) : ∀ n, NS (callInternal G F n d vs [τ])
  | 0 => by rw [callInternal.eq_1]; exact NS.halt' (fun _ h => by cases h)
  | n+1 => by
    simp only [callInternal,body]
    refine NS.bind (zero_ready_vals_ns n [τ] (fun σ member => ?_)) (fun rv => ?_)
    · rcases List.mem_singleton.mp member with rfl
      exact defaults
    · have frameEq : [τ].reverseAux (ps.reverseAux []) = (singleReturningBody ps τ e same).locals := rfl
      rw [dif_pos frameEq]
      refine NS.bind (run_single_return_ns calls {F with checked := true} contract ps τ e same plain ready _ n)
        (fun last => ?_)
      have layout : returnContext ps τ = [τ].reverse ++ ps.reverse := by
        simp only [returnContext,List.reverseAux_eq,List.append_nil]
      exact NS.bind (NS.lift' (Source.retVals_ok last [τ] layout)) (fun _ => NS.pure' _)

theorem single_return_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps : List STy) (τ : STy) (e : RExpr E (returnContext ps τ) τ)
    (same : τ.implicit E.isBase τ = true) (plain : PlainResultType τ)
    (ready : ReadyExpr A e) (defaults : ZeroReady E τ)
    (body : G.prog.body (G.dispatchFn F.contract d) = some (singleReturningBody ps τ e same))
    (vs : Vals E.layout ps) (H : HeapTy) (n : Nat) :
    NS (callInternal G F n d vs [τ]) ∧
    Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (callInternal G F n d vs [τ])
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  have layout : (singleReturningBody ps τ e same).locals =
      (singleReturningBody ps τ e same).rs.reverse ++ (singleReturningBody ps τ e same).ps.reverse := by
    simp only [singleReturningBody,returnContext,List.reverseAux_eq,List.append_nil]
  exact ⟨call_single_return_ns calls F contract d ps τ e same plain ready defaults body vs n,
    Preservation.call_memory_body_mem calls F contract d ps [τ] (singleReturningBody ps τ e same)
      body rfl rfl layout rfl (.stmt (.returnValue rfl same (.base ready.allocating)) .nil) vs H n⟩

theorem single_return_expr_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps : List STy) (τ : STy) (signature : d.fnSig E = some (ps,[τ]))
    (e : RExpr E (returnContext ps τ) τ) (same : τ.implicit E.isBase τ = true)
    (plain : PlainResultType τ) (ready : ReadyExpr A e) (defaults : ZeroReady E τ)
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
      (NSP.of_ns (call_single_return_ns calls F contract d ps τ e same plain ready defaults body vs n))
      (fun _ _ _ => trivial)))
  have layout : (singleReturningBody ps τ e same).locals =
      (singleReturningBody ps τ e same).rs.reverse ++ (singleReturningBody ps τ e same).ps.reverse := by
    simp only [singleReturningBody,returnContext,List.reverseAux_eq,List.append_nil]
  exact ⟨progress,Preservation.eval_memory_call_mem calls F contract d ps [τ] signature
    (singleReturningBody ps τ e same) body rfl rfl layout rfl
    (.stmt (.returnValue rfl same (.base ready.allocating)) .nil) args argsOK.exact H n⟩

theorem single_return_from_elaborate (res : Resolution) (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (F : Fr) (contract : F.contract = c) (ps : List STy) (τ : STy)
    (d : {d : Decl // d ∈ Solidity.Lowering.P9.WholeProgram.functions res ∧
      d.fnSig res.env = some (ps,[τ])})
    (e : RExpr res.env (returnContext ps τ) τ) (same : τ.implicit res.env.isBase τ = true)
    (plain : PlainResultType τ) (ready : ReadyExpr (fun d => d ∈ values) e) (defaults : ZeroReady res.env τ)
    (body : G.prog.body (G.dispatchFn F.contract d.val) = some (singleReturningBody ps τ e same))
    (vs : Vals res.env.layout ps) (H : HeapTy) (n : Nat) :
    NS (callInternal G F n d.val vs [τ]) ∧
    Hoare (fun y => MemOK res.env H y ∧ RValsOK res.env y.2.heap.ty vs.toR) (callInternal G F n d.val vs [τ])
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) :=
  single_return_progress_and_memory
    (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    F contract d.val ps τ e same plain ready defaults body vs H n

theorem single_return_expr_from_elaborate (res : Resolution) (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (F : Fr) (contract : F.contract = c) (ps : List STy) (τ : STy)
    (d : {d : Decl // d ∈ Solidity.Lowering.P9.WholeProgram.functions res ∧ d.fnSig res.env = some (ps,[τ])})
    (e : RExpr res.env (returnContext ps τ) τ) (same : τ.implicit res.env.isBase τ = true)
    (plain : PlainResultType τ) (ready : ReadyExpr (fun d => d ∈ values) e) (defaults : ZeroReady res.env τ)
    (body : G.prog.body (G.dispatchFn F.contract d.val) = some (singleReturningBody ps τ e same))
    {Γ : RCtx} (args : RConvArgs res.env Γ ps) (argsOK : ReadyArgs (fun d => d ∈ values) args)
    (H : HeapTy) (n : Nat) :
    NS (evalE G F (n+1) (.call d.val d.property.2 args)) ∧
    Hoare (MemOK res.env H) (evalE G F (n+1) (.call d.val d.property.2 args))
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) :=
  single_return_expr_progress_and_memory
    (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    F contract d.val ps τ d.property.2 e same plain ready defaults body args argsOK H n

#print axioms single_return_expr_from_elaborate
#print axioms call_single_return_ns
#print axioms single_return_progress_and_memory
#print axioms single_return_from_elaborate
end Solidity.Source.Progress
