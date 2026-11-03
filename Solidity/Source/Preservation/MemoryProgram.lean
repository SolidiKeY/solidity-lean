import Solidity.Source.Preservation.MemoryBodyCalls
import Solidity.Lowering.P9.FunctionCatalog

/-! Source memory-call admission tied to actual elaborated bodies. A finite
syntactic catalogue supplies body membership; elaboration supplies signatures
and frame layout, and P9 derives the original value-callee CallsOK. No semantic
callee-preservation or caller-provided frame equation is accepted. -/
namespace Solidity.Source.Preservation
open EM Solidity.Lowering.P9
variable {E : Env}

def MemoryCatalogue (A : Decl → Prop) (G : Glob E) (c : String) (ds : List Decl) : Prop :=
  ∀ d ∈ ds, d ∈ E.decls ∧ ∃ (ps rs targetPs : List STy) (b : RBody E),
    d.fnSig E = some (ps,rs) ∧
    (G.dispatchFn c d).fnSig E = some (targetPs,rs) ∧
    G.prog.body (G.dispatchFn c d) = some b ∧ b.mods = [] ∧
    MemoryItems A b.rs b.inModifier b.items

def MemoryCallsOK (G : Glob E) (c : String) (ds : List Decl) : Prop :=
  ∀ F, F.contract = c → ∀ d {ps rs : List STy},
    d.fnSig E = some (ps,rs) → d ∈ ds → ∀ (vs : Vals E.layout ps) H n,
    Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR)
      (callInternal G F n d vs rs)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y)

theorem memory_catalogue_sound (el : Elaborated) (G : Glob el.res.env)
    (program : G.prog = el.prog) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check el.res G c values = true)
    (admission : MemoryCatalogue (fun d => d ∈ values) G c ds) : MemoryCallsOK G c ds := by
  intro F hc d ps rs signature member vs H n
  obtain ⟨declared,inputs,outputs,targetInputs,b,sourceSig,targetSig,body,mods,fragment⟩ := admission d member
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (sourceSig.symm.trans signature))
  have environment : el.res.env.decls = el.res.unit.decls := by
    have h := checked
    simp only [WholeProgram.check,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1
  have targetMember : G.dispatchFn c d ∈ el.res.unit.decls := by
    rw [← environment]
    exact WholeProgram.dispatch_mem G c d el.res.env.decls rfl declared
  have actualBody : el.prog.body (G.dispatchFn c d) = some b := by rw [← program]; exact body
  obtain ⟨parameters,returns⟩ := el.body_sig targetMember actualBody targetSig
  have params : b.ps = inputs := parameters.trans (G.dispatchFn_params c d signature targetSig)
  have layout : b.locals = b.rs.reverse ++ b.ps.reverse := by
    rw [el.body_locals targetMember actualBody,parameters,returns]
  exact call_memory_body_mem (WholeProgram.check_sound el G program c values checked) F hc d inputs outputs b
    (by rw [hc]; exact body) params returns layout mods fragment vs H n

theorem memory_from_elaborate (res : Resolution) (ha : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (admission : MemoryCatalogue (fun d => d ∈ values) G c ds) : MemoryCallsOK G c ds := by
  obtain ⟨el,hel⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨resolution,bodyProgram⟩ := elaborate_program hel
  rcases el with ⟨r,prog,hb,hcs,hm,hct,hco,hi,hba⟩
  dsimp only at resolution bodyProgram
  subst res
  have hp : prog = Source.progOf r.env := eq_of_heq bodyProgram
  subst prog
  exact memory_catalogue_sound ⟨r,Source.progOf r.env,hb,hcs,hm,hct,hco,hi,hba⟩
    G program c values ds checked admission

theorem memory_catalogue_expr_mem (el : Elaborated) (G : Glob el.res.env)
    (program : G.prog = el.prog) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check el.res G c values = true)
    (admission : MemoryCatalogue (fun d => d ∈ values) G c ds)
    (F : Fr) (hc : F.contract = c) (d : Decl) {ps rs : List STy}
    (signature : d.fnSig el.res.env = some (ps,rs)) (member : d ∈ ds)
    {Γ : RCtx} (args : RConvArgs el.res.env Γ ps)
    (argsOK : ExactArgs (fun d => d ∈ values) args) (H : HeapTy) (n : Nat) :
    Hoare (MemOK el.res.env H) (evalE G F (n+1) (.call d signature args))
      (fun v y => MemOK el.res.env H y ∧ RValOK el.res.env y.2.heap.ty v)
      (fun _ y => MemOK el.res.env H y) := by
  obtain ⟨declared,inputs,outputs,targetInputs,b,sourceSig,targetSig,body,mods,fragment⟩ := admission d member
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (sourceSig.symm.trans signature))
  have environment : el.res.env.decls = el.res.unit.decls := by
    have h := checked
    simp only [WholeProgram.check,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1
  have targetMember : G.dispatchFn c d ∈ el.res.unit.decls := by
    rw [← environment]
    exact WholeProgram.dispatch_mem G c d el.res.env.decls rfl declared
  have actualBody : el.prog.body (G.dispatchFn c d) = some b := by rw [← program]; exact body
  obtain ⟨parameters,returns⟩ := el.body_sig targetMember actualBody targetSig
  have params : b.ps = inputs := parameters.trans (G.dispatchFn_params c d signature targetSig)
  have layout : b.locals = b.rs.reverse ++ b.ps.reverse := by
    rw [el.body_locals targetMember actualBody,parameters,returns]
  exact eval_memory_call_mem (WholeProgram.check_sound el G program c values checked) F hc d inputs outputs
    signature b (by rw [hc]; exact body) params returns layout mods fragment args argsOK H n

theorem memory_expr_from_elaborate (res : Resolution) (ha : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (admission : MemoryCatalogue (fun d => d ∈ values) G c ds)
    (F : Fr) (hc : F.contract = c) (d : Decl) {ps rs : List STy}
    (signature : d.fnSig res.env = some (ps,rs)) (member : d ∈ ds)
    {Γ : RCtx} (args : RConvArgs res.env Γ ps)
    (argsOK : ExactArgs (fun d => d ∈ values) args) (H : HeapTy) (n : Nat) :
    Hoare (MemOK res.env H) (evalE G F (n+1) (.call d signature args))
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v)
      (fun _ y => MemOK res.env H y) := by
  obtain ⟨el,hel⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨resolution,bodyProgram⟩ := elaborate_program hel
  rcases el with ⟨r,prog,hb,hcs,hm,hct,hco,hi,hba⟩
  dsimp only at resolution bodyProgram
  subst res
  have hp : prog = Source.progOf r.env := eq_of_heq bodyProgram
  subst prog
  exact memory_catalogue_expr_mem ⟨r,Source.progOf r.env,hb,hcs,hm,hct,hco,hi,hba⟩
    G program c values ds checked admission F hc d signature member args argsOK H n

/-- The explicit coverage check prevents silently omitting a source function.
The memory-body catalogue is a proof certificate, not an executable recognizer. -/
theorem checked_memory_call (res : Resolution) (ha : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (admission : MemoryCatalogue (fun d => d ∈ values) G c ds)
    (complete : (WholeProgram.functions res).all (fun d => decide (d ∈ ds)) = true)
    (F : Fr) (hc : F.contract = c) (d : Decl) {ps rs : List STy}
    (signature : d.fnSig res.env = some (ps,rs)) (member : d ∈ WholeProgram.functions res)
    (vs : Vals res.env.layout ps) (H : HeapTy) (n : Nat) :
    Hoare (fun y => MemOK res.env H y ∧ RValsOK res.env y.2.heap.ty vs.toR)
      (callInternal G F n d vs rs)
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) :=
  memory_from_elaborate res ha G program c values ds checked admission F hc d signature
    (of_decide_eq_true ((List.all_eq_true.mp complete) d member)) vs H n

#print axioms memory_catalogue_sound
#print axioms memory_from_elaborate
#print axioms checked_memory_call
#print axioms memory_expr_from_elaborate
end Solidity.Source.Preservation
