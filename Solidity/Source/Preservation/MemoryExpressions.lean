import Solidity.Source.Preservation.ReferenceReturns
import Solidity.Source.Preservation.EncodingArguments
import Solidity.Source.Preservation.ArrayLiterals
import Solidity.Source.Preservation.MemberPacking

/-! Memory body expressions over the existing intrinsic source syntax.
Reference rebinding and primitive memory-array writes retain actual bounds,
type and horizon halts. No evaluator or original fragment is changed. -/
namespace Solidity.Source.Preservation
open EM
variable {E : Env}

inductive BodyExpr (A : Decl → Prop) {Γ : RCtx} : {τ : STy} → RExpr E Γ τ → Prop
  | base {τ} {e : RExpr E Γ τ} : AllocatingExpr A e → BodyExpr A e
  | structNew {dn : DeclName} {ps : List STy}
      (hs : (E.structFields dn .memory).map (·.map Prod.snd) = some ps)
      {args : RConvArgs E Γ ps} : ExactArgs A args → BodyExpr A (.structNew hs args)
  | inlineArray {σ : STy} {m : Nat} {args : RConvArgs E Γ (List.replicate m σ)}
      (hs : σ.oneWord = true) : ExactArgs A args → BodyExpr A (.inlineArray args hs)
  | encode {ts : List STy} (kind : AbiKind) {args : RArgs E Γ ts}
      (hk : kind.argsOK E.isBase E.mapFree ts = true) : EncodingArgs A args → BodyExpr A (.abiEncode kind args)
  | rebind {τ} (i : Idx Γ τ) {e : RExpr E Γ τ} :
      AllocatingExpr A e → BodyExpr A (.assign (.local i) e)
  | arrayWrite {τ σ : STy} {size : Option Nat}
      {a : RExpr E Γ (.array .memory τ size)} {i : RExpr E Γ σ} {e : RExpr E Γ τ}
      (hi : σ.isIndex = true) : τ.isValue = true → AllocatingExpr A a →
      AllocatingExpr A i → AllocatingExpr A e →
      BodyExpr A (.assign (.indexArray a (by decide) i hi) e)

theorem write_local_ref_mem {Γ : RCtx} {τ : STy} (F : Fr) (n : Nat)
    (i : Idx Γ τ) (v : Val E.layout τ) (H : HeapTy) :
    Hoare (fun y => MemOK E H y ∧ v.RefOK E y.2.heap.ty)
      (writeLoc F n (.local i) v)
      (fun _ y => MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun _ y => MemOK E H y) := by
  rw [writeLoc]
  refine Hoare.bind (Hoare.locals' (Q := fun l y => y.1 = l ∧ MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun y h => ⟨rfl,h⟩)) (fun l => ?_)
  refine Hoare.setLocals' (fun ⟨l',s⟩ h => ?_)
  rcases h with ⟨same,valid,reference⟩
  change l' = l at same
  subst l'
  exact ⟨relocalize valid (l.set i v) (LocalsOK.set l i valid.1.2 reference),reference⟩

theorem local_loc_mem {Γ : RCtx} {τ : STy} (G : Glob E) (F : Fr) (i : Idx Γ τ)
    (P : EMState E Γ → Prop) : ∀ n,
    Hoare P (evalLoc G F n (.local i)) (fun L y => P y ∧ L = .local i) (fun _ y => P y)
  | 0 => Hoare.halt' (fun _ h => h)
  | _+1 => Hoare.pure' (fun _ h => ⟨h,rfl⟩)

theorem array_length_keep {Γ : RCtx} {τ : STy} {size : Option Nat}
    (F : Fr) (a : Val E.layout (.array .memory τ size)) (P : EMState E Γ → Prop) :
    Hoare P (lengthOf F a) (fun _ y => P y) (fun _ y => P y) := by
  cases a with
  | storRef impossible p => cases impossible
  | cdRef impossible off len => cases impossible
  | memRef hm addr =>
    cases size with
    | some n => exact Hoare.pure' (fun _ h => h)
    | none =>
      rw [lengthOf]
      refine Hoare.bind (heapObj_get (a := addr) (fun _ h _ => h)) (fun ⟨t,d⟩ => ?_)
      cases d <;> first
        | exact Hoare.pure' (fun _ h => h.1)
        | exact Hoare.halt' (fun _ h => h.1)
      all_goals
        intro loc elem m x impossible heq
        cases impossible

theorem array_index_pres {Γ : RCtx} {τ : STy} {size : Option Nat}
    (F : Fr) (a : Val E.layout (.array .memory τ size)) (i : Nat) :
    MemPres (indexLoc (Γ := Γ) F a i) := by
  unfold MemPres
  intro H
  unfold indexLoc
  refine Hoare.bind (array_length_keep F a (MemOK E H)) (fun len => ?_)
  split
  · cases a with
    | storRef impossible _ => cases impossible
    | cdRef impossible _ _ => cases impossible
    | memRef _ _ => exact Hoare.pure' (fun _ h => h)
  · exact MemPres.lift' _ H

theorem memory_array_loc_pres {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n : Nat)
    {Γ : RCtx} {τ σ : STy} {size : Option Nat}
    (a : RExpr E Γ (.array .memory τ size)) (i : RExpr E Γ σ) (hi : σ.isIndex = true)
    (ha : AllocatingExpr A a) (hx : AllocatingExpr A i) :
    MemPres (evalLoc G F n (.indexArray a (by decide) i hi)) := by
  cases n with
  | zero => exact MemPres.halt' _
  | succ n =>
    rw [evalLoc]
    have arrayStep : MemPres (evalE G F n a) := fun H =>
      Hoare.conseq (eval_allocating_mem calls F contract n a ha H)
        (fun _ h => h) (fun _ _ h => h.1) (fun _ _ h => h)
    have indexStep : MemPres (evalE G F n i) := fun H =>
      Hoare.conseq (eval_allocating_mem calls F contract n i hx H)
        (fun _ h => h) (fun _ _ h => h.1) (fun _ _ h => h)
    exact MemPres.bind arrayStep (fun v => MemPres.bind (MemPres.getV' v) (fun av =>
      MemPres.bind indexStep (fun ix => MemPres.bind (MemPres.lift' ix.amount)
        (fun k => array_index_pres F av k))))

theorem eval_body_expr_mem {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n : Nat)
    {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) (admitted : BodyExpr A e) (H : HeapTy) :
    Hoare (MemOK E H) (evalE G F n e)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  cases admitted with
  | base h => exact eval_allocating_mem calls F contract n e h H
  | structNew hs args =>
    cases n with
    | zero => exact Hoare.halt' (fun _ h => h)
    | succ n => exact evalE_structNew_mem G F n hs _ (eval_exact_args_mem calls F contract n _ args H)
  | inlineArray hs args =>
    cases n with
    | zero => exact Hoare.halt' (fun _ h => h)
    | succ n => exact evalE_inlineArray_mem G F n _ hs (eval_exact_args_mem calls F contract n _ args H)
  | encode kind hk args =>
    cases n with
    | zero => exact Hoare.halt' (fun _ h => h)
    | succ n => exact evalE_abiKind_mem G F n kind _ hk (eval_encoding_args_mem calls F contract n _ args H)
  | @rebind τ i rhs hr =>
    cases n with
    | zero => exact Hoare.halt' (fun _ h => h)
    | succ n =>
      rw [evalE]
      refine Hoare.bind (eval_allocating_mem calls F contract n rhs hr H) (fun v => ?_)
      refine Hoare.bind (Hoare.conseq (local_loc_mem G F i (fun y => MemOK E H y ∧ RValOK E y.2.heap.ty v) n)
        (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h.1))
        (fun L => ?_)
      refine Hoare.conseq (P' := fun y => (MemOK E H y ∧ RValOK E y.2.heap.ty v) ∧ L = .local i) ?_
        (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h)
      intro y h
      rcases h with ⟨valid,rfl⟩
      exact (Hoare.bind (getV_ref_mem v H) (fun x =>
        Hoare.bind (write_local_ref_mem F n i x H) (fun _ => Hoare.pure' (fun _ h => h)))) y valid
  | @arrayWrite τ σ size a i rhs hi value ha hx hr =>
    cases n with
    | zero => exact Hoare.halt' (fun _ h => h)
    | succ n =>
      rw [evalE]
      refine Hoare.bind (Hoare.conseq (eval_allocating_mem calls F contract n rhs hr H)
        (fun _ h => h) (fun _ _ h => h.1) (fun _ _ h => h)) (fun v => ?_)
      refine Hoare.bind (memory_array_loc_pres calls F contract n a i hi ha hx H) (fun L => ?_)
      refine Hoare.bind (MemPres.getV' v H) (fun x => ?_)
      refine Hoare.bind (MemPres.writeLoc' F n (loc_of_frag (.inl value)) L x H) (fun _ => ?_)
      exact Hoare.pure' (fun _ h => ⟨h,rval_value_ok value (.val x)⟩)

#print axioms eval_body_expr_mem
#print axioms memory_array_loc_pres
end Solidity.Source.Preservation
