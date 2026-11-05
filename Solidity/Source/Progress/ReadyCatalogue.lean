import Solidity.Source.Progress.ReadyBodyCalls
import Solidity.Source.Progress.ReadyProgram
import Solidity.Source.Preservation.MemoryProgram

/-! Ready memory-call catalogues over actual elaborated programs. Elaboration
derives selected-body parameter, return and local-frame metadata. Catalogue
entries retain signatures, default readiness and syntactic statement admission;
they carry no semantic progress/preservation oracle or frame equation. -/
namespace Solidity.Source.Progress
open EM Solidity.Lowering.P9
variable {E : Env}

def ReadyMemoryCatalogue (A : Decl → Prop) (G : Glob E) (c : String) (ds : List Decl) : Prop :=
  ∀ d ∈ ds, d ∈ E.decls ∧ ∃ (ps rs targetPs : List STy) (b : RBody E),
    d.fnSig E = some (ps,rs) ∧
    (G.dispatchFn c d).fnSig E = some (targetPs,rs) ∧
    G.prog.body (G.dispatchFn c d) = some b ∧ b.mods = [] ∧
    (∀ τ ∈ rs, ZeroReady E τ) ∧ ReadyItems A b.rs b.inModifier b.items

def ReadyMemoryCalls (G : Glob E) (c : String) (ds : List Decl) : Prop :=
  ∀ F, F.contract = c → ∀ d {ps rs : List STy},
    d.fnSig E = some (ps,rs) → d ∈ ds → ∀ (vs : Vals E.layout ps) H n,
    NS (callInternal G F n d vs rs) ∧
    Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR)
      (callInternal G F n d vs rs)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y)

theorem ReadyMemoryCatalogue.memory {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    (catalogue : ReadyMemoryCatalogue A G c ds) : Preservation.MemoryCatalogue A G c ds := by
  intro d member
  obtain ⟨declared,ps,rs,targetPs,b,signature,targetSig,body,mods,defaults,ready⟩ := catalogue d member
  exact ⟨declared,ps,rs,targetPs,b,signature,targetSig,body,mods,ready.memory⟩

theorem ready_memory_catalogue_sound (el : Elaborated) (G : Glob el.res.env)
    (program : G.prog = el.prog) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check el.res G c values = true)
    (catalogue : ReadyMemoryCatalogue (fun d => d ∈ values) G c ds) : ReadyMemoryCalls G c ds := by
  intro F contract d ps rs signature member vs H n
  obtain ⟨declared,inputs,outputs,targetInputs,b,sourceSig,targetSig,body,mods,defaults,ready⟩ := catalogue d member
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (sourceSig.symm.trans signature))
  have environment : el.res.env.decls = el.res.unit.decls := by
    have certificate := checked
    simp only [WholeProgram.check,Bool.and_eq_true,decide_eq_true_eq] at certificate
    exact certificate.1
  have targetMember : G.dispatchFn c d ∈ el.res.unit.decls := by
    rw [← environment]
    exact WholeProgram.dispatch_mem G c d el.res.env.decls rfl declared
  have actualBody : el.prog.body (G.dispatchFn c d) = some b := by rw [← program]; exact body
  obtain ⟨parameters,returns⟩ := el.body_sig targetMember actualBody targetSig
  have params : b.ps = inputs := parameters.trans (G.dispatchFn_params c d signature targetSig)
  have layout : b.locals = b.rs.reverse ++ b.ps.reverse := by
    rw [el.body_locals targetMember actualBody,parameters,returns]
  exact ready_body_call_progress_and_memory (WholeProgram.check_sound el G program c values checked)
    F contract d inputs outputs b (by rw [contract]; exact body) params returns layout mods defaults ready vs H n

theorem ready_memory_from_elaborate (res : Resolution) (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (catalogue : ReadyMemoryCatalogue (fun d => d ∈ values) G c ds) : ReadyMemoryCalls G c ds := by
  obtain ⟨el,result⟩ := Option.isSome_iff_exists.mp elaborated
  obtain ⟨resolution,bodyProgram⟩ := elaborate_program result
  rcases el with ⟨r,prog,bodies,constructors,mods,constructorTypes,constructorOrder,inits,bases⟩
  dsimp only at resolution bodyProgram
  subst res
  have same : prog = Source.progOf r.env := eq_of_heq bodyProgram
  subst prog
  exact ready_memory_catalogue_sound ⟨r,Source.progOf r.env,bodies,constructors,mods,
    constructorTypes,constructorOrder,inits,bases⟩ G program c values ds checked catalogue

theorem ready_memory_expr_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (catalogue : ReadyMemoryCatalogue (fun d => d ∈ values) G c ds)
    (F : Fr) (contract : F.contract = c) (d : Decl) {ps rs : List STy}
    (signature : d.fnSig res.env = some (ps,rs)) (member : d ∈ ds)
    {Γ : RCtx} (args : RConvArgs res.env Γ ps) (argsOK : ReadyArgs (fun d => d ∈ values) args)
    (H : HeapTy) (n : Nat) :
    NS (evalE G F (n+1) (.call d signature args)) ∧
    Hoare (MemOK res.env H) (evalE G F (n+1) (.call d signature args))
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) := by
  have calls := WholeProgram.from_elaborate res elaborated G program c values checked
  have admitted := ready_memory_from_elaborate res elaborated G program c values ds checked catalogue
  have progress : NS (evalE G F (n+1) (.call d signature args)) := by
    rw [evalE]
    refine NS.bind (eval_ready_args_ns calls F contract n args argsOK) (fun vs => ?_)
    refine NS.bind ?_ (fun _ => NS.pure' _)
    exact NSP.ns (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns (admitted F contract d signature member vs H n).1) (fun _ _ _ => trivial)))
  exact ⟨progress,Preservation.memory_expr_from_elaborate res elaborated G program c values ds
    checked catalogue.memory F contract d signature member args argsOK.exact H n⟩

theorem ready_memory_program_calls (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values memory : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (catalogue : ReadyMemoryCatalogue (fun d => d ∈ values) G c memory)
    (complete : readyCoverage res values memory = true) : ReadyProgramCalls res G c := by
  have calls := WholeProgram.from_elaborate res elaborated G program c values checked
  have admitted := ready_memory_from_elaborate res elaborated G program c values memory checked catalogue
  intro F contract d ps rs signature declared vs H n
  have covered : d ∈ values ∨ d ∈ memory :=
    of_decide_eq_true ((List.all_eq_true.mp complete) d declared)
  rcases covered with value | mem
  · exact ⟨callInternal_callFrag_ns calls F contract n d signature value vs,
      (Preservation.fragMemAt calls n).call F contract d signature value vs H⟩
  · exact admitted F contract d signature mem vs H n

theorem ReadyProgramCalls.expr_context {res : Resolution} {G : Glob res.env} {c : String}
    (calls : ReadyProgramCalls res G c) (F : Fr) (contract : F.contract = c) :
    ∀ n, ExprNSAt (fun d => d ∈ WholeProgram.functions res) G F n
  | 0 => exprNSAt_zero _ _ _
  | n+1 => exprNSAt_step (calls.expr_context F contract n) (by
      intro d ps rs signature declared vs
      exact (calls F contract d signature declared vs (Heap.empty : Heap res.env.layout).ty n).1)

#print axioms ready_memory_catalogue_sound
#print axioms ready_memory_from_elaborate
#print axioms ready_memory_expr_from_elaborate
#print axioms ready_memory_program_calls
#print axioms ReadyProgramCalls.expr_context
end Solidity.Source.Progress
