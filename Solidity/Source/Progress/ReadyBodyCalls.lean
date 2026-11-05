import Solidity.Source.Progress.ReadyBodies

/-! Modifier-free calls whose complete memory statement sequences are ready.
All statement progress and memory preservation follow syntactic admission;
return defaults and the actual selected frame/body remain explicit. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

theorem ready_items_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c)
    (n nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx}
    (items : RItems E R M k Γ Δ) (ready : ReadyItems A R M items)
    (l : Locals E.layout Γ) (frame : BodyFrame nps R Γ) (H : HeapTy) :
    NSP (execItems G F n nps ph items l) (fun o => k.loop = false → o.esc = false) ∧
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l) (execItems G F n nps ph items l)
      (fun o y => MemOK E H y ∧ Preservation.OutRefsOK (E := E) y.2.heap.ty o)
      (fun _ y => MemOK E H y) :=
  ⟨(ready_body_at calls n).items F contract nps ph items ready l frame,
    (Preservation.memory_body_at calls n).items F contract nps ph items ready.memory l H⟩

theorem run_ready_body_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (b : RBody E)
    (ready : ReadyItems A b.rs b.inModifier b.items) (l : Locals E.layout b.locals)
    (frame : BodyFrame b.ps.length b.rs b.locals) :
    ∀ n, NS (runMods G F n b [] l)
  | 0 => by rw [runMods.eq_1]; exact NS.halt' (fun _ h => by cases h)
  | n+1 => by
    rw [runMods]
    obtain ⟨ys,equality⟩ := RItems.ext b.items
    refine NSP.ns (NSP.bind (R := fun _ => True)
      (NSP.weaken ((ready_body_at calls n).items F contract b.ps.length none b.items ready l frame)
        (fun _ h => h rfl)) (fun o result => ?_))
    cases o with
    | normal last => exact NSP.of_ns (NS.lift' (Locals.restore_ok' ys equality last))
    | ret last => exact NSP.pure' trivial
    | brk _ | cont _ => exact nomatch result

theorem call_ready_body_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, ZeroReady E τ)
    (ready : ReadyItems A b.rs b.inModifier b.items) (vs : Vals E.layout ps) :
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
    exact NS.bind (run_ready_body_ns calls {F with checked := true} contract b ready _ frame n)
      (fun last => NS.bind (NS.lift' (Source.retVals_ok last rs resultLayout)) (fun _ => NS.pure' _))

theorem ready_body_call_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, ZeroReady E τ)
    (ready : ReadyItems A b.rs b.inModifier b.items) (vs : Vals E.layout ps) (H : HeapTy) (n : Nat) :
    NS (callInternal G F n d vs rs) ∧
    Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (callInternal G F n d vs rs)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) :=
  ⟨call_ready_body_ns calls F contract d ps rs b body parameters returns layout mods defaults ready vs n,
    Preservation.call_memory_body_mem calls F contract d ps rs b body parameters returns layout mods
      ready.memory vs H n⟩

theorem ready_body_expr_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (signature : d.fnSig E = some (ps,rs)) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, ZeroReady E τ)
    (ready : ReadyItems A b.rs b.inModifier b.items)
    {Γ : RCtx} (args : RConvArgs E Γ ps) (argsOK : ReadyArgs A args) (H : HeapTy) (n : Nat) :
    NS (evalE G F (n+1) (.call d signature args)) ∧
    Hoare (MemOK E H) (evalE G F (n+1) (.call d signature args))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  have progress : NS (evalE G F (n+1) (.call d signature args)) := by
    rw [evalE]
    refine NS.bind (eval_ready_args_ns calls F contract n args argsOK) (fun vs => ?_)
    refine NS.bind ?_ (fun _ => NS.pure' _)
    exact NSP.ns (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns (call_ready_body_ns calls F contract d ps rs b body parameters returns layout mods defaults ready vs n))
      (fun _ _ _ => trivial)))
  exact ⟨progress,Preservation.eval_memory_call_mem calls F contract d ps rs signature b
    body parameters returns layout mods ready.memory args argsOK.exact H n⟩

theorem ready_body_call_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (F : Fr) (contract : F.contract = c) (ps rs : List STy)
    (d : {d : Decl // d ∈ Solidity.Lowering.P9.WholeProgram.functions res ∧ d.fnSig res.env = some (ps,rs)})
    (b : RBody res.env) (body : G.prog.body (G.dispatchFn F.contract d.val) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, ZeroReady res.env τ)
    (ready : ReadyItems (fun d => d ∈ values) b.rs b.inModifier b.items)
    (vs : Vals res.env.layout ps) (H : HeapTy) (n : Nat) :
    NS (callInternal G F n d.val vs rs) ∧
    Hoare (fun y => MemOK res.env H y ∧ RValsOK res.env y.2.heap.ty vs.toR) (callInternal G F n d.val vs rs)
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) :=
  ready_body_call_progress_and_memory
    (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    F contract d.val ps rs b body parameters returns layout mods defaults ready vs H n

#print axioms ready_body_expr_progress_and_memory
#print axioms ready_items_progress_and_memory
#print axioms call_ready_body_ns
#print axioms ready_body_call_from_elaborate
end Solidity.Source.Progress
