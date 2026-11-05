import Solidity.Source.Preservation.Statements
import Solidity.Source.Preservation.ResultValidity

/-! Joint all-horizon Hoare preservation for the original call value fragment.
The existing `CallsOK` hypothesis is consumed, not replaced by a preservation
assumption. Separate P9 admission derives it for actual elaborated programs.
-/
namespace Solidity.Source.Preservation
open EM
variable {E : Env}

structure FragMemAt (A : Decl → Prop) (G : Glob E) (c : String) (n : Nat) : Prop where
  expr : ∀ F, F.contract = c → ExprMemAt A G F n
  stmt : StmtMemAt A G c n
  mods : ∀ F, F.contract = c → ∀ (b : RBody E) (l : Locals E.layout b.locals),
    b.items.ValFragC A → b.items.OpsOK → ∀ H,
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l)
      (runMods G F n b [] l)
      (fun l' y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l') (fun _ y => MemOK E H y)
  call : ∀ F, F.contract = c → CallMemAt A G F n

theorem fragMemAt_zero (A : Decl → Prop) (G : Glob E) (c : String) : FragMemAt A G c 0 where
  expr F _ := exprMemAt_zero A G F
  stmt := stmtMemAt_zero A G c
  mods := by intros; rw [runMods.eq_1]; exact Hoare.halt' fun _ h => h.1
  call := by
    intro F hc
    unfold CallMemAt
    intros
    rw [callInternal.eq_1]
    exact Hoare.halt' fun _ h => h.1

theorem callMem_step {A : Decl → Prop} {G : Glob E} {c : String} {n : Nat}
    (hG : CallsOK A G c) (ih : FragMemAt A G c n) (F : Fr) (hc : F.contract = c) :
    CallMemAt A G F (n + 1) := by
  intro d ps rs hs hA vs H
  obtain ⟨b, hb, hm, hl, hrs, hps, hz, hf, ho⟩ := hG d hs hA
  exact callFrame_mem G F n d vs rs b (by rw [hc]; exact hb) hl hm
    (fun H l => ih.mods {F with checked := true} hc b l hf ho H) H

/-- No recursive preservation premise remains: the same horizon induction
closes expressions, all statements/loops, modifier-free bodies and calls. -/
theorem fragMemAt {A : Decl → Prop} {G : Glob E} {c : String} (hG : CallsOK A G c) :
    ∀ n, FragMemAt A G c n
  | 0 => fragMemAt_zero A G c
  | n + 1 => by
    have ih := fragMemAt hG n
    exact {
      expr := fun F hc => exprMemAt_step (ih.expr F hc) (ih.call F hc)
      stmt := stmtMemAt_step ih.stmt ih.expr
      mods := fun F hc b l hf ho H => runBody_mem G F n b l H
        (ih.stmt.execItems F hc b.ps.length none b.items l hf ho H)
      call := callMem_step hG ih }

/-- Source progress and full memory preservation use the same unmodified
fragment and call predicate, without changing halt semantics or the progress theorem's original frame premises. -/
theorem progress_and_preservation {A : Decl → Prop} {G : Glob E} {c : String}
    (hG : CallsOK A G c) (n : Nat) : Source.FragAt A G c n ∧ FragMemAt A G c n :=
  ⟨Source.fragAt hG n, fragMemAt hG n⟩

/-- Public expression triple: memory, current locals and returned references
are valid after success; every halt retains the complete memory invariant. -/
theorem evalE_fragment_mem {A : Decl → Prop} {G : Glob E} {c : String}
    (hG : CallsOK A G c) (F : Fr) (hc : F.contract = c) (n : Nat)
    {Γ : RCtx} {t : STy} (e : RExpr E Γ t) (hf : e.ValFragC A) (ho : e.OpsOK) (H : HeapTy) :
    Hoare (MemOK E H) (evalE G F n e)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) :=
  Hoare.conseq (((fragMemAt hG n).expr F hc).val e hf ho H) (fun _ h => h)
    (fun v _ h => ⟨h, expr_result_ok hG e hf ho v⟩) (fun _ _ h => h)

#print axioms evalE_fragment_mem
#print axioms callMem_step
#print axioms fragMemAt
#print axioms progress_and_preservation
end Solidity.Source.Preservation
