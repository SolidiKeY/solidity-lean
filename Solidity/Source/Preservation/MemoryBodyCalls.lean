import Solidity.Source.Preservation.MemoryBodies

/-! Actual modifier-free internal calls with syntactically admitted memory
bodies. Parameters, returns and local-frame layout remain explicit typed facts;
body preservation is derived from MemoryItems, not assumed. -/
namespace Solidity.Source.Preservation
open EM
variable {E : Env}

theorem run_memory_body_mem {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (hc : F.contract = c) (b : RBody E)
    (admitted : MemoryItems A b.rs b.inModifier b.items) (l : Locals E.layout b.locals) (H : HeapTy) :
    ∀ n, Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l) (runMods G F n b [] l)
      (fun l' y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l') (fun _ y => MemOK E H y)
  | 0 => by rw [runMods.eq_1]; exact Hoare.halt' (fun _ h => h.1)
  | n+1 => runBody_mem G F n b l H ((memory_body_at calls n).items F hc b.ps.length none b.items admitted l H)

theorem call_memory_body_mem {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (hc : F.contract = c) (d : Decl)
    (ps rs : List STy) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (admitted : MemoryItems A b.rs b.inModifier b.items) (vs : Vals E.layout ps) (H : HeapTy) :
    ∀ n, Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR)
      (callInternal G F n d vs rs)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y)
  | 0 => by rw [callInternal.eq_1]; exact Hoare.halt' (fun _ h => h.1)
  | n+1 => by
    have frame : rs.reverseAux (ps.reverseAux []) = b.locals := by
      rw [layout,parameters,returns,List.reverseAux_eq,List.reverseAux_eq,List.append_nil]
    exact callFrame_mem G F n d vs rs b body frame mods
      (fun H' l => run_memory_body_mem calls {F with checked := true} hc b admitted l H' n) H

/-- The source call expression's actual sub restores arbitrary caller locals
and retains the reached heap and returned-reference witnesses on every path. -/
theorem sub_memory_body_mem {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (hc : F.contract = c) (d : Decl)
    (ps rs : List STy) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (admitted : MemoryItems A b.rs b.inModifier b.items) (vs : Vals E.layout ps)
    (H : HeapTy) (n : Nat) {Γ : RCtx} :
    Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR)
      (sub .nil (callInternal G F n d vs rs) : EM E Γ _)
      (fun r y => MemOK E H y ∧ RValOK E y.2.heap.ty r.1) (fun _ y => MemOK E H y) := by
  intro ⟨l,s⟩ ⟨outer,args⟩
  have result := call_memory_body_mem calls F hc d ps rs b body parameters returns layout mods admitted
    vs s.heap.ty n (.nil,s) ⟨relocalize outer.self .nil trivial,args⟩
  unfold EM.sub
  rcases actual : (callInternal G F n d vs rs).run (.nil,s) with ⟨r,⟨last,after⟩⟩
  rw [actual] at result
  have finish (valid : MemOK E s.heap.ty (last,after)) : MemOK E H (l,after) :=
    relocalize (valid.weaken outer.le) l (LocalsOK.mono valid.le l outer.1.2)
  have actual' : callInternal G F n d vs rs (.nil,s) = (r,(last,after)) := actual
  cases r with
  | ok a =>
    simp only [ExceptT.run,ExceptT.mk,actual']
    exact ⟨finish result.1,result.2⟩
  | error e =>
    simp only [ExceptT.run,ExceptT.mk,actual']
    exact finish result

theorem eval_memory_call_mem {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (hc : F.contract = c) (d : Decl)
    (ps rs : List STy) (signature : d.fnSig E = some (ps,rs)) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (parameters : b.ps = ps) (returns : b.rs = rs)
    (layout : b.locals = b.rs.reverse ++ b.ps.reverse) (mods : b.mods = [])
    (admitted : MemoryItems A b.rs b.inModifier b.items)
    {Γ : RCtx} (args : RConvArgs E Γ ps) (argsOK : ExactArgs A args) (H : HeapTy) (n : Nat) :
    Hoare (MemOK E H) (evalE G F (n+1) (.call d signature args))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  rw [evalE]
  refine Hoare.bind (eval_exact_args_mem calls F hc n args argsOK H) (fun vs => ?_)
  exact Hoare.bind (sub_memory_body_mem calls F hc d ps rs b body parameters returns layout mods admitted vs H n)
    (fun r => Hoare.pure' (fun _ h => h))

#print axioms call_memory_body_mem
#print axioms eval_memory_call_mem
end Solidity.Source.Preservation
