import Solidity.Source.Progress.ReadyBodyCalls

/-! Progress for same-type local rebinding with a ready RHS. Finite rebinding
prefixes lead into the existing ready-body admission. The preservation proof
uses BodyExpr.rebind and its local-reference writer; no evaluator is changed.
These are Source-only results, with explicit call/body/default premises. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

theorem eval_ready_rebind_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n : Nat)
    {Γ : RCtx} {τ : STy} (i : Idx Γ τ) (e : RExpr E Γ τ)
    (plain : PlainResultType τ) (ready : ReadyExpr A e) :
    NS (evalE G F n (.assign (.local i) e)) := by
  cases n with
  | zero => rw [evalE]; exact NS.halt' (fun _ h => by cases h)
  | succ n =>
    have locate : NSP (evalLoc G F n (.local i)) (fun L => L = .local i) := by
      cases n with
      | zero => rw [evalLoc]; exact NSP.halt' trivial
      | succ n => rw [evalLoc]; exact NSP.pure' rfl
    rw [evalE]
    refine NS.bind (eval_ready_expr_ns calls F contract n e ready) (fun v => ?_)
    refine NSP.ns (Q := fun _ => True) (NSP.bind locate (fun L same => ?_))
    cases same
    exact NSP.of_ns (NS.bind (getV_plain_ns plain v) (fun x =>
      NS.bind (writeLoc_local_ns F n i x) (fun _ => NS.pure' _)))

theorem ready_rebind_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n : Nat)
    {Γ : RCtx} {τ : STy} (i : Idx Γ τ) (e : RExpr E Γ τ)
    (plain : PlainResultType τ) (ready : ReadyExpr A e) (H : HeapTy) :
    NS (evalE G F n (.assign (.local i) e)) ∧
    Hoare (MemOK E H) (evalE G F n (.assign (.local i) e))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) :=
  ⟨eval_ready_rebind_ns calls F contract n i e plain ready,
    Preservation.eval_body_expr_mem calls F contract n _ (.rebind i ready.allocating) H⟩

/-- A finite prefix certificate over the existing indexed items. The tail is
an unchanged ReadyItems body; this adds no arbitrary nested assignment RHS. -/
inductive RebindingItems (A : Decl → Prop) (R : List STy) (M : Bool) :
    {k : SCtx} → {Γ Δ : RCtx} → RItems E R M k Γ Δ → Prop
  | ready {k Γ Δ} {items : RItems E R M k Γ Δ} :
      ReadyItems A R M items → RebindingItems A R M items
  | rebind {k Γ Δ τ} (i : Idx Γ τ) {e : RExpr E Γ τ}
      {rest : RItems E R M k Γ Δ} : PlainResultType τ → ReadyExpr A e →
      RebindingItems A R M rest → RebindingItems A R M (.stmt (.expr (.assign (.local i) e)) rest)

theorem RebindingItems.memory {A : Decl → Prop} {R : List STy} {M : Bool}
    {k : SCtx} {Γ Δ : RCtx} {items : RItems E R M k Γ Δ}
    (ready : RebindingItems A R M items) : Preservation.MemoryItems A R M items := by
  induction ready with
  | ready tail => exact tail.memory
  | rebind i plain rhs tail ih => exact .stmt (.expr (.rebind i rhs.allocating)) ih

theorem rebinding_items_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) : ∀ n, ∀ (F : Fr), F.contract = c → ∀ nps ph
    {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx} (items : RItems E R M k Γ Δ),
    RebindingItems A R M items → ∀ l, BodyFrame nps R Γ →
    NSP (execItems G F n nps ph items l) (fun o => k.loop = false → o.esc = false)
  | 0, F, contract, nps, ph, _, _, _, _, _, items, ready, l, frame => by
      rw [execItems.eq_1]; exact NSP.halt' trivial
  | n+1, F, contract, nps, ph, R, M, k, Γ, Δ, items, ready, l, frame => by
      cases ready with
      | ready tail => exact (ready_body_at calls (n+1)).items F contract nps ph _ tail l frame
      | @rebind τ i e rest plain rhs tail =>
        rw [execItems]
        cases n with
        | zero => rw [execS.eq_1]; exact NSP.halt' trivial
        | succ n =>
          have step : NSP (execS G F (n+1) nps ph
              (.expr (R := R) (M := M) (k := k) (.assign (.local i) e)) l)
              (fun o => ∃ last, o = .normal last) := by
            rw [execS]
            exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
              (NSP.of_ns (eval_ready_rebind_ns calls F contract n i e plain rhs))
              (fun _ _ _ => trivial))) (fun pair _ => NSP.pure' ⟨pair.2,rfl⟩)
          refine NSP.bind step (fun out ⟨last,same⟩ => ?_)
          cases same
          exact NSP.bind (rebinding_items_ns calls (n+1) F contract nps ph _ tail last frame)
            (fun out h => NSP.weaken (Out.up_esc [] out) (fun _ same loop => same.trans (h loop)))


theorem run_rebinding_body_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (b : RBody E)
    (ready : RebindingItems A b.rs b.inModifier b.items) (l : Locals E.layout b.locals)
    (frame : BodyFrame b.ps.length b.rs b.locals) :
    ∀ n, NS (runMods G F n b [] l)
  | 0 => by rw [runMods.eq_1]; exact NS.halt' (fun _ h => by cases h)
  | n+1 => by
    rw [runMods]
    obtain ⟨ys,equality⟩ := RItems.ext b.items
    refine NSP.ns (NSP.bind (R := fun _ => True)
      (NSP.weaken (rebinding_items_ns calls n F contract b.ps.length none b.items ready l frame)
        (fun _ h => h rfl)) (fun o result => ?_))
    cases o with
    | normal last => exact NSP.of_ns (NS.lift' (Locals.restore_ok' ys equality last))
    | ret last => exact NSP.pure' trivial
    | brk _ | cont _ => exact nomatch result

theorem call_rebinding_body_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, ZeroReady E τ)
    (ready : RebindingItems A b.rs b.inModifier b.items) (vs : Vals E.layout ps) :
    ∀ n, NS (callInternal G F n d vs rs)
  | 0 => by rw [callInternal.eq_1]; exact NS.halt' (fun _ h => by cases h)
  | n+1 => by
    have frameEq : rs.reverseAux (ps.reverseAux []) = b.locals := by
      rw [layout,parameters,returns,List.reverseAux_eq,List.reverseAux_eq,List.append_nil]
    have frame : BodyFrame b.ps.length b.rs b.locals := by
      refine ⟨[],b.ps.reverse,?_,List.length_reverse⟩
      simp only [List.nil_append]
      exact layout
    have resultLayout : b.locals = rs.reverse ++ b.ps.reverse := by rw [layout,returns]
    rw [callInternal,body]
    refine NS.bind (zero_ready_vals_ns n rs defaults) (fun _ => ?_)
    rw [dif_pos frameEq,mods]
    exact NS.bind (run_rebinding_body_ns calls {F with checked := true} contract b ready _ frame n)
      (fun last => NS.bind (NS.lift' (Source.retVals_ok last rs resultLayout)) (fun _ => NS.pure' _))

theorem rebinding_body_call_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, ZeroReady E τ)
    (ready : RebindingItems A b.rs b.inModifier b.items) (vs : Vals E.layout ps) (H : HeapTy) (n : Nat) :
    NS (callInternal G F n d vs rs) ∧
    Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (callInternal G F n d vs rs)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) :=
  ⟨call_rebinding_body_ns calls F contract d ps rs b body parameters returns layout mods defaults ready vs n,
    Preservation.call_memory_body_mem calls F contract d ps rs b body parameters returns layout mods
      ready.memory vs H n⟩


theorem rebinding_body_expr_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (signature : d.fnSig E = some (ps,rs)) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, ZeroReady E τ)
    (ready : RebindingItems A b.rs b.inModifier b.items)
    {Γ : RCtx} (args : RConvArgs E Γ ps) (argsOK : ReadyArgs A args) (H : HeapTy) (n : Nat) :
    NS (evalE G F (n+1) (.call d signature args)) ∧
    Hoare (MemOK E H) (evalE G F (n+1) (.call d signature args))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  have progress : NS (evalE G F (n+1) (.call d signature args)) := by
    rw [evalE]
    refine NS.bind (eval_ready_args_ns calls F contract n args argsOK) (fun vs => ?_)
    refine NS.bind ?_ (fun _ => NS.pure' _)
    exact NSP.ns (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns (call_rebinding_body_ns calls F contract d ps rs b body parameters returns layout mods defaults ready vs n))
      (fun _ _ _ => trivial)))
  exact ⟨progress,Preservation.eval_memory_call_mem calls F contract d ps rs signature b
    body parameters returns layout mods ready.memory args argsOK.exact H n⟩

theorem rebinding_body_call_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (F : Fr) (contract : F.contract = c) (ps rs : List STy)
    (d : {d : Decl // d ∈ Solidity.Lowering.P9.WholeProgram.functions res ∧ d.fnSig res.env = some (ps,rs)})
    (b : RBody res.env) (body : G.prog.body (G.dispatchFn F.contract d.val) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, ZeroReady res.env τ)
    (ready : RebindingItems (fun d => d ∈ values) b.rs b.inModifier b.items)
    (vs : Vals res.env.layout ps) (H : HeapTy) (n : Nat) :
    NS (callInternal G F n d.val vs rs) ∧
    Hoare (fun y => MemOK res.env H y ∧ RValsOK res.env y.2.heap.ty vs.toR) (callInternal G F n d.val vs rs)
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) :=
  rebinding_body_call_progress_and_memory
    (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    F contract d.val ps rs b body parameters returns layout mods defaults ready vs H n

#print axioms eval_ready_rebind_ns
#print axioms ready_rebind_progress_and_memory
#print axioms RebindingItems.memory
#print axioms rebinding_items_ns
#print axioms run_rebinding_body_ns
#print axioms call_rebinding_body_ns
#print axioms rebinding_body_call_progress_and_memory
#print axioms rebinding_body_expr_progress_and_memory
#print axioms rebinding_body_call_from_elaborate
end Solidity.Source.Progress
