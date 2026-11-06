import Solidity.Source.Preservation.LocalFrames
import Solidity.Source.Decode

/-! Hoare bridges for actual modifier-free body and internal-call frames.
The caller supplies the recursive body-preservation step; this module discharges
frame packing, defaults, heap growth, scope restoration and returned references.
It does not assume that the whole interpreter preserves memory.
-/
namespace Solidity.Source.Preservation
open EM
variable {E : Env}

def OutRefsOK (H : HeapTy) {Γ Δ : RCtx} : Out E.layout Γ Δ → Prop
  | .normal l => LocalsOK E H l
  | .brk l | .cont l | .ret l => LocalsOK E H l

theorem runBody_mem (G : Glob E) (F : Fr) (n : Nat) (b : RBody E)
    (l : Locals E.layout b.locals) (H : HeapTy)
    (hb : Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
      (execItems G F n b.ps.length none b.items l)
      (fun o y => MemOK E H y ∧ OutRefsOK (E := E) y.2.heap.ty o)
      (fun _ y => MemOK E H y)) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
      (runMods G F (n + 1) b [] l)
      (fun l' y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l')
      (fun _ y => MemOK E H y) := by
  simp only [runMods]
  refine Hoare.bind hb fun o => ?_
  cases o with
  | normal l' =>
    refine Hoare.lift' fun y h => ?_
    cases hr : l'.restore b.locals with
    | error e => exact h.1
    | ok l'' => exact ⟨h.1, localsRestore_ok l' l'' h.2 hr⟩
  | ret l' => exact Hoare.pure' fun _ h => h
  | brk l' => exact Hoare.halt' fun _ h => h.1
  | cont l' => exact Hoare.halt' fun _ h => h.1

theorem retVals_mem {Γ : RCtx} (l : Locals E.layout Γ) (base : Nat) (rs : List STy) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
      (lift (retVals l base rs) : EM E [] _)
      (fun vs y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs)
      (fun _ y => MemOK E H y) := by
  refine Hoare.lift' fun y h => ?_
  cases hr : retVals l base rs with
  | error e => exact h.1
  | ok vs => exact ⟨h.1, retVals_ok l base rs vs h.2 hr⟩

theorem callFrame_mem (G : Glob E) (F : Fr) (n : Nat) (d : Decl)
    {ps : List STy} (vs : Vals E.layout ps) (rs : List STy) (b : RBody E)
    (hb : G.prog.body (G.dispatchFn F.contract d) = some b)
    (hl : rs.reverseAux (ps.reverseAux []) = b.locals) (hm : b.mods = [])
    (hbody : ∀ (H : HeapTy) (l : Locals E.layout b.locals),
      Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
        (runMods G {F with checked := true} n b [] l)
        (fun l' y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l')
        (fun _ y => MemOK E H y)) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR)
      (callInternal G F (n + 1) d vs rs)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  simp only [callInternal, hb]
  refine Hoare.bind (Hoare.memGrow (R := fun H' => RValsOK E H' vs.toR)
    (fun H' => zeroVals_mem n rs H')) fun rv => ?_
  rw [dif_pos hl, hm]
  have hp : Hoare
      (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty rv.toR ∧
        ∃ H', RValsOK E H' vs.toR ∧ H'.Le y.2.heap.ty)
      (runMods G {F with checked := true} n b [] (hl ▸ rv.onto (vs.onto (L0 E))))
      (fun l' y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l')
      (fun _ y => MemOK E H y) := by
    refine Hoare.conseq (hbody H _) ?_ (fun _ _ h => h) (fun _ _ h => h)
    intro y h
    rcases h.2.2 with ⟨H', hv, hle⟩
    exact ⟨h.1, localsCast_ok hl _
      (valsOnto_ok rv _ h.2.1 (valsOnto_ok vs _ (RValsOK.mono hle vs.toR hv) trivial))⟩
  exact Hoare.bind hp fun l' => Hoare.bind (retVals_mem l' 0 rs H) fun out =>
    Hoare.pure' fun _ h => ⟨h.1, RValOK.mkRet rs out h.2⟩

#print axioms runBody_mem
#print axioms retVals_mem
#print axioms callFrame_mem
end Solidity.Source.Preservation
