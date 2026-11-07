import Solidity.Source.Progress.ReadyArguments
import Solidity.Source.Preservation.MemoryBodies

/-! Typed struct-constructor allocation parents. Member layout agreement is
derived from the existing constructor typing proof, not supplied as a semantic
execution premise. Existing readiness and memory-body admissions are unchanged. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

theorem struct_member_types {dn : DeclName} {ps : List STy}
    (typed : (E.structFields dn .memory).map (·.map Prod.snd) = some ps) :
    E.layout.fields dn = ps := by
  cases fields : E.structFields dn .memory with
  | none => simp only [fields,Option.map_none,reduceCtorEq] at typed
  | some members =>
    have same : members.map Prod.snd = ps := by
      simpa only [fields,Option.map_some,Option.some.injEq] using typed
    change ((E.structFields dn .memory).getD []).map Prod.snd = ps
    rw [fields]
    exact same

theorem fields_same_ns {Γ : RCtx} : ∀ {ps : List STy} (values : Vals E.layout ps),
    NS (fieldsOf (E:=E) (Γ:=Γ) values ps)
  | [], .nil => NS.pure' _
  | _::_, .cons value rest => by
    rw [fieldsOf,dif_pos rfl]
    exact NS.bind (fields_same_ns rest) (fun _ => NS.pure' _)

theorem struct_parent_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) :
    ∀ n {Γ : RCtx} {dn : DeclName} {ps : List STy}
      (typed : (E.structFields dn .memory).map (·.map Prod.snd) = some ps)
      (args : RConvArgs E Γ ps), ReadyArgs A args → NS (evalE G F n (.structNew typed args))
  | 0, _, _, _, _, _, _ => NS.halt' (fun _ h => by cases h)
  | n+1, Γ, dn, ps, typed, args, ready => by
    rw [evalE]
    refine NS.bind (eval_ready_args_ns calls F contract n args ready) (fun values => ?_)
    have packed : NS (fieldsOf (E:=E) (Γ:=Γ) values (E.layout.fields dn)) := by
      rw [struct_member_types typed]
      exact fields_same_ns (E:=E) values
    exact NS.bind packed (fun fields =>
      NS.bind (allocRef_ns rfl (Data.struct fields)) (fun _ => NS.pure' _))

theorem struct_parent_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n : Nat)
    {Γ : RCtx} {dn : DeclName} {ps : List STy}
    (typed : (E.structFields dn .memory).map (·.map Prod.snd) = some ps)
    (args : RConvArgs E Γ ps) (ready : ReadyArgs A args) (H : HeapTy) :
    NS (evalE G F n (.structNew typed args)) ∧
    Hoare (MemOK E H) (evalE G F n (.structNew typed args))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) :=
  ⟨struct_parent_ns calls F contract n typed args ready,
    Preservation.eval_body_expr_mem calls F contract n _ (.structNew typed ready.exact) H⟩

theorem struct_statement_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c)
    {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {dn : DeclName} {ps : List STy}
    (typed : (E.structFields dn .memory).map (·.map Prod.snd) = some ps)
    (args : RConvArgs E Γ ps) (ready : ReadyArgs A args)
    (nps : Nat) (ph : Option (Ph E)) (locals : Locals E.layout Γ) :
    ∀ n, NS (execS G F n nps ph (.expr (R:=R) (M:=M) (k:=k) (.structNew typed args)) locals)
  | 0 => by rw [execS.eq_1]; exact NS.halt' (fun _ h => by cases h)
  | n+1 => by
    rw [execS]
    have child : NS (sub (Γ:=[]) locals (evalE G F n (.structNew typed args))) :=
      NSP.ns (NSP.sub' (Q:=fun _ => True) (NSP.weaken
        (NSP.of_ns (struct_parent_ns calls F contract n typed args ready)) (fun _ _ _ => trivial)))
    exact NS.bind child (fun _ => NS.pure' _)

theorem struct_statement_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n : Nat)
    {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {dn : DeclName} {ps : List STy}
    (typed : (E.structFields dn .memory).map (·.map Prod.snd) = some ps)
    (args : RConvArgs E Γ ps) (ready : ReadyArgs A args)
    (nps : Nat) (ph : Option (Ph E)) (locals : Locals E.layout Γ) (H : HeapTy) :
    NS (execS G F n nps ph (.expr (R:=R) (M:=M) (k:=k) (.structNew typed args)) locals) ∧
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty locals)
      (execS G F n nps ph (.expr (R:=R) (M:=M) (k:=k) (.structNew typed args)) locals)
      (fun out y => MemOK E H y ∧ Preservation.OutRefsOK (E:=E) y.2.heap.ty out)
      (fun _ y => MemOK E H y) :=
  ⟨struct_statement_ns calls F contract typed args ready nps ph locals n,
    (Preservation.memory_body_at calls n).stmt F contract nps ph _
      (.expr (.structNew typed ready.exact)) locals H⟩

theorem struct_parent_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (F : Fr) (contract : F.contract = c) (n : Nat) {Γ : RCtx} {dn : DeclName} {ps : List STy}
    (typed : (res.env.structFields dn .memory).map (·.map Prod.snd) = some ps)
    (args : RConvArgs res.env Γ ps) (ready : ReadyArgs (fun d => d ∈ values) args) (H : HeapTy) :
    NS (evalE G F n (.structNew typed args)) ∧
    Hoare (MemOK res.env H) (evalE G F n (.structNew typed args))
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) :=
  struct_parent_progress_and_memory
    (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    F contract n typed args ready H

#print axioms struct_member_types
#print axioms fields_same_ns
#print axioms struct_parent_ns
#print axioms struct_parent_progress_and_memory
#print axioms struct_statement_ns
#print axioms struct_statement_progress_and_memory
#print axioms struct_parent_from_elaborate
end Solidity.Source.Progress
