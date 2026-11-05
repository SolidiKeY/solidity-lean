import Solidity.Source.Progress.BoundParents
import Solidity.Source.Progress.ReadyCatalogue
import Solidity.Source.Progress.ParentArguments
import Solidity.Source.Progress.CallComposition

/-! Catalogues of finite bound-parent bodies with metadata derived from actual
elaboration. Entries contain syntax/default admission and actual body identity,
not frame equations or execution oracles. Checked value and memory entries use
the existing complete-coverage contract. -/
namespace Solidity.Source.Progress
open EM Solidity.Lowering.P9
variable {E : Env}

def BoundMemoryCatalogue (A : Decl → Prop) (G : Glob E) (c : String) (ds : List Decl) : Prop :=
  ∀ d ∈ ds, d ∈ E.decls ∧ ∃ (ps rs targetPs : List STy) (b : RBody E),
    d.fnSig E = some (ps,rs) ∧
    (G.dispatchFn c d).fnSig E = some (targetPs,rs) ∧
    G.prog.body (G.dispatchFn c d) = some b ∧ b.mods = [] ∧
    (∀ τ ∈ rs, FiniteDefault E τ) ∧ BoundParentItems A b.rs b.inModifier b.items

theorem BoundMemoryCatalogue.memory {A : Decl → Prop} {G : Glob E} {c : String} {ds : List Decl}
    (catalogue : BoundMemoryCatalogue A G c ds) : Preservation.MemoryCatalogue A G c ds := by
  intro d member
  obtain ⟨declared,ps,rs,targetPs,b,signature,targetSig,body,mods,defaults,ready⟩ := catalogue d member
  exact ⟨declared,ps,rs,targetPs,b,signature,targetSig,body,mods,ready.memory⟩

theorem bound_memory_catalogue_sound (el : Elaborated) (G : Glob el.res.env)
    (program : G.prog = el.prog) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check el.res G c values = true)
    (catalogue : BoundMemoryCatalogue (fun d => d ∈ values) G c ds) : ReadyMemoryCalls G c ds := by
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
  exact bound_parent_body_call_progress_and_memory (WholeProgram.check_sound el G program c values checked)
    F contract d inputs outputs b (by rw [contract]; exact body) params returns layout mods defaults ready vs H n

theorem bound_memory_from_elaborate (res : Resolution) (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (catalogue : BoundMemoryCatalogue (fun d => d ∈ values) G c ds) : ReadyMemoryCalls G c ds := by
  obtain ⟨el,result⟩ := Option.isSome_iff_exists.mp elaborated
  obtain ⟨resolution,bodyProgram⟩ := elaborate_program result
  rcases el with ⟨r,prog,bodies,constructors,mods,constructorTypes,constructorOrder,inits,bases⟩
  dsimp only at resolution bodyProgram
  subst res
  have same : prog = Source.progOf r.env := eq_of_heq bodyProgram
  subst prog
  exact bound_memory_catalogue_sound ⟨r,Source.progOf r.env,bodies,constructors,mods,
    constructorTypes,constructorOrder,inits,bases⟩ G program c values ds checked catalogue

theorem bound_memory_expr_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (catalogue : BoundMemoryCatalogue (fun d => d ∈ values) G c ds)
    (F : Fr) (contract : F.contract = c) (d : Decl) {ps rs : List STy}
    (signature : d.fnSig res.env = some (ps,rs)) (member : d ∈ ds)
    {Γ : RCtx} (args : RConvArgs res.env Γ ps) (argsOK : ReadyArgs (fun d => d ∈ values) args)
    (H : HeapTy) (n : Nat) :
    NS (evalE G F (n+1) (.call d signature args)) ∧
    Hoare (MemOK res.env H) (evalE G F (n+1) (.call d signature args))
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) := by
  have calls := WholeProgram.from_elaborate res elaborated G program c values checked
  have admitted := bound_memory_from_elaborate res elaborated G program c values ds checked catalogue
  have progress : NS (evalE G F (n+1) (.call d signature args)) := by
    rw [evalE]
    refine NS.bind (eval_ready_args_ns calls F contract n args argsOK) (fun vs => ?_)
    refine NS.bind ?_ (fun _ => NS.pure' _)
    exact NSP.ns (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns (admitted F contract d signature member vs H n).1) (fun _ _ _ => trivial)))
  exact ⟨progress,Preservation.memory_expr_from_elaborate res elaborated G program c values ds
    checked catalogue.memory F contract d signature member args argsOK.exact H n⟩

theorem bound_memory_program_calls (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values memory : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (catalogue : BoundMemoryCatalogue (fun d => d ∈ values) G c memory)
    (complete : readyCoverage res values memory = true) : ReadyProgramCalls res G c := by
  have calls := WholeProgram.from_elaborate res elaborated G program c values checked
  have admitted := bound_memory_from_elaborate res elaborated G program c values memory checked catalogue
  intro F contract d ps rs signature declared vs H n
  have covered : d ∈ values ∨ d ∈ memory :=
    of_decide_eq_true ((List.all_eq_true.mp complete) d declared)
  rcases covered with value | mem
  · exact ⟨callInternal_callFrag_ns calls F contract n d signature value vs,
      (Preservation.fragMemAt calls n).call F contract d signature value vs H⟩
  · exact admitted F contract d signature mem vs H n


theorem bound_memory_parent_expr_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (catalogue : BoundMemoryCatalogue (fun d=>d ∈ values) G c ds)
    (F : Fr) (contract : F.contract = c) (d : Decl) {ps rs : List STy}
    (signature : d.fnSig res.env = some (ps,rs)) (member : d ∈ ds)
    {Γ : RCtx} (args : RConvArgs res.env Γ ps) (admitted : ParentArgs (fun d=>d ∈ values) args)
    (H : HeapTy) (n : Nat) :
    NS (evalE G F (n+1) (.call d signature args)) ∧
    Hoare (MemOK res.env H) (evalE G F (n+1) (.call d signature args))
      (fun v y=>MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y=>MemOK res.env H y) := by
  have calls := WholeProgram.from_elaborate res elaborated G program c values checked
  have callees := bound_memory_from_elaborate res elaborated G program c values ds checked catalogue
  constructor
  · rw [evalE]
    refine NS.bind (eval_parent_args_ns calls F contract n args admitted) (fun vs=>?_)
    refine NS.bind ?_ (fun _=>NS.pure' _)
    exact NSP.ns (NSP.sub' (Q:=fun _=>True) (NSP.weaken
      (NSP.of_ns (callees F contract d signature member vs H n).1) (fun _ _ _=>trivial)))
  · rw [evalE]
    refine Hoare.bind (eval_parent_args_mem calls F contract n args admitted H) (fun vs=>?_)
    exact Hoare.bind (sub_ready_memory_call_mem callees F contract d signature member vs H n)
      (fun r=>Hoare.pure' (fun _ h=>h))

theorem bound_memory_program_expr_ns (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values memory : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (catalogue : BoundMemoryCatalogue (fun d=>d ∈ values) G c memory)
    (complete : readyCoverage res values memory = true)
    (F : Fr) (contract : F.contract = c) (n : Nat) {Γ : RCtx} {τ : STy}
    (e : RExpr res.env Γ τ) (fragment : e.ValFragC (fun d=>d ∈ WholeProgram.functions res))
    (operations : e.OpsOK) : NS (evalE G F n e) :=
  ((bound_memory_program_calls res elaborated G program c values memory checked catalogue complete).expr_context
    F contract n).val e fragment operations

#print axioms BoundMemoryCatalogue.memory
#print axioms bound_memory_catalogue_sound
#print axioms bound_memory_from_elaborate
#print axioms bound_memory_expr_from_elaborate
#print axioms bound_memory_program_calls
#print axioms bound_memory_parent_expr_from_elaborate
#print axioms bound_memory_program_expr_ns
end Solidity.Source.Progress
