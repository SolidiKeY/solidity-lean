import Solidity.Source.Preservation.ReferenceArguments

/-! Reference-return consumers of actual sub/body/call frames. The supported
body returns an exact-type argument list; its expressions may allocate or read
reference parameters. Other reference bodies remain outside this admission. -/
namespace Solidity.Source.Preservation
open EM

/-- Preserve a returned witness as well as callee locals through actual sub.
The caller's old references are transported over the callee's heap growth. -/
theorem sub_result_mem {E : Env} {Γ Δ : RCtx} {α : Type} (l' : Locals E.layout Δ)
    (m : EM E Δ α) (Q : α → St E → Prop)
    (hm : ∀ H', Hoare (MemOK E H') m (fun a y => MemOK E H' y ∧ Q a y.2)
      (fun _ y => MemOK E H' y)) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l')
      (sub l' m : EM E Γ (α × Locals E.layout Δ))
      (fun r y => MemOK E H y ∧ LocalsOK E y.2.heap.ty r.2 ∧ Q r.1 y.2)
      (fun _ y => MemOK E H y) := by
  intro ⟨l,s⟩ ⟨outer,inner⟩
  have result := hm s.heap.ty (l',s) (relocalize outer.self l' inner)
  unfold EM.sub
  rcases actual : m.run (l',s) with ⟨r,⟨last,after⟩⟩
  rw [actual] at result
  have finish (valid : MemOK E s.heap.ty (last,after)) : MemOK E H (l,after) :=
    relocalize (valid.weaken outer.le) l (LocalsOK.mono valid.le l outer.1.2)
  have actual' : m (l',s) = (r,(last,after)) := actual
  cases r with
  | ok a =>
    simp only [ExceptT.run, ExceptT.mk, actual']
    exact ⟨finish result.1, result.1.1.2, result.2⟩
  | error e =>
    simp only [ExceptT.run, ExceptT.mk, actual']
    exact finish result

/-- Actual return-slot writes retain reference validity, with no value-type
restriction and no assumed successful setRets. -/
theorem return_exact_mem {E : Env} {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n nps : Nat)
    (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx}
    (es : RConvArgs E Γ R) (admitted : ExactArgs A es) (l : Locals E.layout Γ) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
      (execS G F (n+1) nps ph (.retTuple (M := M) (k := k) es) l)
      (fun o y => MemOK E H y ∧ ∃ l', o = .ret l' ∧ LocalsOK E y.2.heap.ty l')
      (fun _ y => MemOK E H y) := by
  rw [execS]
  refine Hoare.bind (sub_result_mem l (evalConvArgs G F n es)
    (fun vs s => RValsOK E s.heap.ty vs.toR)
    (fun H' => eval_exact_args_mem calls F contract n es admitted H') H) (fun r => ?_)
  refine Hoare.bind (Hoare.lift' (r := setRets r.2 (Γ.length - (nps + R.length)) r.1)
    (Q := fun l' y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l') (fun y h => ?_)) (fun l' => ?_)
  · cases actual : setRets r.2 (Γ.length - (nps + R.length)) r.1 with
    | error e => exact h.1
    | ok last => exact ⟨h.1, setRets_ok r.2 _ r.1 last h.2.1 h.2.2 actual⟩
  · exact Hoare.pure' (fun _ h => ⟨h.1, l', rfl, h.2⟩)

/-- The intrinsic body shape certified here. Return slots precede reversed
parameters, exactly as callInternal constructs them. -/
def returningBody {E : Env} (ps rs : List STy)
    (es : RConvArgs E (rs.reverseAux (ps.reverseAux [])) rs) : RBody E :=
  {ps := ps, rs := rs, inModifier := false,
   locals := rs.reverseAux (ps.reverseAux []), out := rs.reverseAux (ps.reverseAux []),
   items := .stmt (.retTuple es) .nil}

theorem returning_items_mem {E : Env} {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (ps rs : List STy)
    (es : RConvArgs E (rs.reverseAux (ps.reverseAux [])) rs) (admitted : ExactArgs A es)
    (l : Locals E.layout (rs.reverseAux (ps.reverseAux []))) (H : HeapTy) :
    ∀ n, Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
      (execItems G F n ps.length none (returningBody ps rs es).items l)
      (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o) (fun _ y => MemOK E H y)
  | 0 => by rw [execItems.eq_1]; exact Hoare.halt' (fun _ h => h.1)
  | 1 => by simp only [returningBody,execItems,execS,bind]; exact Hoare.halt' (fun _ h => h.1)
  | n+2 => by
    simp only [returningBody]
    rw [execItems]
    refine Hoare.bind (return_exact_mem calls F contract n ps.length none es admitted l H)
      (fun o => ?_)
    intro y h
    rcases h.2 with ⟨last,rfl,valid⟩
    exact ⟨h.1,valid⟩

/-- Nonrecursive reference parameters/results for a body returning admitted
exact-type expressions. Its preservation premise is derived here, not supplied
as an interpreter axiom. Defaults and all actual halts remain unchanged. -/
theorem call_returning_mem {E : Env} {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (es : RConvArgs E (rs.reverseAux (ps.reverseAux [])) rs)
    (admitted : ExactArgs A es)
    (body : G.prog.body (G.dispatchFn F.contract d) = some (returningBody ps rs es))
    (vs : Vals E.layout ps) (H : HeapTy) :
    ∀ n, Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR)
      (callInternal G F n d vs rs)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y)
  | 0 => by rw [callInternal.eq_1]; exact Hoare.halt' (fun _ h => h.1)
  | n+1 => by
    apply callFrame_mem G F n d vs rs (returningBody ps rs es) body rfl rfl
    intro H' l
    cases n with
    | zero => rw [runMods.eq_1]; exact Hoare.halt' (fun _ h => h.1)
    | succ k =>
      exact runBody_mem G {F with checked := true} k (returningBody ps rs es) l H'
        (returning_items_mem calls {F with checked := true} contract ps rs es admitted l H' k)


/-- The public expression call frame restores arbitrary caller locals while
retaining the return witness and all heap growth of the supported body. -/
theorem sub_returning_mem {E : Env} {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (es : RConvArgs E (rs.reverseAux (ps.reverseAux [])) rs)
    (admitted : ExactArgs A es)
    (body : G.prog.body (G.dispatchFn F.contract d) = some (returningBody ps rs es))
    (vs : Vals E.layout ps) (H : HeapTy) (n : Nat) {Γ : RCtx} :
    Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR)
      (sub .nil (callInternal G F n d vs rs) : EM E Γ _)
      (fun r y => MemOK E H y ∧ RValOK E y.2.heap.ty r.1) (fun _ y => MemOK E H y) := by
  intro ⟨l,s⟩ ⟨outer,args⟩
  have result := call_returning_mem calls F contract d ps rs es admitted body vs s.heap.ty n
    (.nil,s) ⟨relocalize outer.self .nil trivial,args⟩
  unfold EM.sub
  rcases actual : (callInternal G F n d vs rs).run (.nil,s) with ⟨r,⟨last,after⟩⟩
  rw [actual] at result
  have finish (valid : MemOK E s.heap.ty (last,after)) : MemOK E H (l,after) :=
    relocalize (valid.weaken outer.le) l (LocalsOK.mono valid.le l outer.1.2)
  have actual' : callInternal G F n d vs rs (.nil,s) = (r,(last,after)) := actual
  cases r with
  | ok a =>
    simp only [ExceptT.run, ExceptT.mk, actual']
    exact ⟨finish result.1,result.2⟩
  | error e =>
    simp only [ExceptT.run, ExceptT.mk, actual']
    exact finish result

/-- Actual RExpr.call with exact-type reference/allocating arguments and the
certified return-only body. Body selection and fnSig remain explicit. -/
theorem eval_call_returning_mem {E : Env} {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (d : Decl)
    (ps rs : List STy) (signature : d.fnSig E = some (ps,rs))
    (es : RConvArgs E (rs.reverseAux (ps.reverseAux [])) rs) (admitted : ExactArgs A es)
    (body : G.prog.body (G.dispatchFn F.contract d) = some (returningBody ps rs es))
    {Γ : RCtx} (args : RConvArgs E Γ ps) (argsOK : ExactArgs A args) (H : HeapTy) (n : Nat) :
    Hoare (MemOK E H) (evalE G F (n+1) (.call d signature args))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  rw [evalE]
  refine Hoare.bind (eval_exact_args_mem calls F contract n args argsOK H) (fun vs => ?_)
  exact Hoare.bind (sub_returning_mem calls F contract d ps rs es admitted body vs H n)
    (fun r => Hoare.pure' (fun _ h => h))

#print axioms sub_result_mem
#print axioms return_exact_mem
#print axioms call_returning_mem
#print axioms sub_returning_mem
#print axioms eval_call_returning_mem
end Solidity.Source.Preservation
