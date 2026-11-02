import Solidity.Source.Preservation.ValueConversions
import Solidity.Source.Preservation.Reads
import Solidity.Source.Preservation.CallFrames

/-! The expression half of joint memory preservation on the UNCHANGED value
fragment. Progress remains the independently proved source `FragAt` theorem.
-/
namespace Solidity.Source.Preservation
open EM
variable {E : Env}

def CallMemAt (C : Decl → Prop) (G : Glob E) (F : Fr) (n : Nat) : Prop :=
  ∀ (d : Decl) {ps rs : List STy}, d.fnSig E = some (ps, rs) → C d →
    ∀ (vs : Vals E.layout ps) (H : HeapTy),
      Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR)
        (callInternal G F n d vs rs)
        (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y)

structure ExprMemAt (C : Decl → Prop) (G : Glob E) (F : Fr) (n : Nat) : Prop where
  val : ∀ {Γ : RCtx} {t : STy} (e : RExpr E Γ t), e.ValFragC C → e.OpsOK → MemPres (evalE G F n e)
  pair : ∀ {Γ : RCtx} {s t : STy} (a : RExpr E Γ s) (b : RExpr E Γ t),
    a.ValFragC C → a.OpsOK → b.ValFragC C → b.OpsOK → MemPres (evalPair G F n a b)
  ref : ∀ {Γ : RCtx} {t : STy} (e : RExpr E Γ t), e.MapRefC C → e.OpsOK → MemPres (evalE G F n e)
  loc : ∀ {Γ : RCtx} {t : STy} (l : RLVal E Γ t), l.IsSimpleC C → l.OpsOK → MemPres (evalLoc G F n l)
  convArgs : ∀ {Γ : RCtx} {ts : List STy} (es : RConvArgs E Γ ts),
    es.ValFragC C → es.OpsOK → MemPres (evalConvArgs G F n es)

theorem args_value_types {C : Decl → Prop} {Γ : RCtx} : ∀ {ts : List STy} (es : RConvArgs E Γ ts),
    es.ValFragC C → ts.all STy.isValue = true
  | _, .nil, _ => rfl
  | _, .cons e h es, hf => by
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨hf.2.1, args_value_types es hf.2.2.2⟩

theorem vals_value_refs (H : HeapTy) : ∀ {ts : List STy} (vs : Vals E.layout ts),
    ts.all STy.isValue = true → RValsOK E H vs.toR
  | _, .nil, _ => trivial
  | _, .cons v vs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨ht, hs⟩ := h
    exact ⟨Val.refOK_of_loc (loc_of_frag (.inl ht)) v, vals_value_refs H vs hs⟩

section
variable {C : Decl → Prop} {G : Glob E} {F : Fr} {n : Nat}

theorem exprVal_step (ih : ExprMemAt C G F n) (hcall : CallMemAt C G F n) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (hf : RExpr.ValFragC C e) (ho : e.OpsOK) : MemPres (evalE G F (n + 1) e) := by
    cases e with
    | const _ => exact MemPres.pure' _
    | bytesLit _ _ => exact MemPres.pure' _
    | addressLit _ => exact MemPres.pure' _
    | bool _ => exact MemPres.pure' _
    | this _ => exact MemPres.pure' _
    | «local» i =>
      simp only [evalE]
      exact MemPres.bind MemPres.locals' fun _ => MemPres.pure' _
    | state d h =>
      simp only [evalE]
      rw [if_neg (by rw [hf.1]; exact Bool.false_ne_true), if_neg (by rw [hf.2.1]; exact Bool.false_ne_true)]
      exact MemPres.bind (MemPres.readAt' F d.path _) fun _ => MemPres.pure' _
    | unary op a =>
      simp only [evalE]
      exact MemPres.bind (ih.val a hf.1 ho.2) fun v => MemPres.bind (MemPres.getV' v) fun x =>
        MemPres.bind (MemPres.lift' _) fun _ => MemPres.pure' _
    | binary op a b =>
      simp only [evalE]
      split
      · rename_i hl
        have hb : τ = .bool := fitsAt_logic ho.1 hl
        subst hb
        refine MemPres.bind (ih.val a hf.1 ho.2.1) fun v => MemPres.bind (MemPres.getV' v) fun x => ?_
        obtain ⟨c, rfl⟩ := Val.eq_bool x
        show MemPres (match some (if c then (1 : Int) else 0) with
          | some kx =>
            if (decide (op = BinOp.and) && decide (kx = 0) || decide (op = BinOp.or) && decide (kx = 1)) = true then
              pure (RVal.val (Val.bool c))
            else do
              let __do_lift ← evalE G F n b
              let __do_lift ← getV __do_lift
              pure (RVal.val __do_lift)
          | none => halt (Halt.stuck "logical operand"))
        dsimp only
        split <;> split <;> first
          | exact MemPres.pure' _
          | exact MemPres.bind (ih.val b hf.2.1 ho.2.2) fun w => MemPres.bind (MemPres.getV' w) fun _ =>
              MemPres.pure' _
      · exact MemPres.bind (ih.pair a b hf.1 ho.2.1 hf.2.1 ho.2.2) fun p =>
          MemPres.bind (MemPres.getV' p.1) fun x => MemPres.bind (MemPres.getV' p.2) fun y =>
            MemPres.bind (MemPres.lift' _) fun _ => MemPres.pure' _
    | compare op a b =>
      simp only [evalE]
      exact MemPres.bind (ih.pair a b hf.1 ho.2.2.1 hf.2.1 ho.2.2.2) fun p =>
        MemPres.bind (MemPres.getV' p.1) fun x => MemPres.bind (MemPres.getV' p.2) fun y =>
          MemPres.bind (MemPres.lift' _) fun _ => MemPres.pure' _
    | compareConst op qa qb =>
      simp only [evalE]
      exact MemPres.bind (MemPres.lift' _) fun _ => MemPres.pure' _
    | shiftLike op a b h =>
      simp only [evalE]
      exact MemPres.bind (ih.pair a b hf.1 ho.2.1 hf.2.1 ho.2.2) fun p =>
        MemPres.bind (MemPres.lift' _) fun k => MemPres.bind (MemPres.getV' p.1) fun x =>
          MemPres.bind (MemPres.lift' _) fun _ => MemPres.pure' _
    | cond c a b =>
      simp only [evalE]
      refine MemPres.bind (ih.val c hf.1 ho.1) fun v => MemPres.bind (MemPres.getV' v) fun x => ?_
      split
      · exact ih.val a hf.2.1 ho.2.1
      · exact ih.val b hf.2.2.1 ho.2.2
    | conv a h =>
      simp only [evalE]
      exact MemPres.bind (ih.val a hf.1 ho) fun v => convRV_pres F n h hf.2.2 v
    | assign l e =>
      simp only [evalE]
      exact MemPres.bind (ih.val e hf.2.1 ho.2) fun v =>
        MemPres.bind (ih.loc l hf.1 ho.1) fun L => MemPres.bind (MemPres.getV' v) fun x =>
          MemPres.bind (MemPres.writeLoc' F n (loc_of_frag (.inl hf.2.2)) L x) fun _ => MemPres.pure' _
    | @compound _ σ op l e h =>
      simp only [evalE]
      have core : ∀ (L : Loc E.layout Γ τ) (v : RVal E.layout σ), MemPres (do
          let old ← readLoc F L
          let new ← match op.kind? with
            | some .shift => lift (shiftVal F.checked (if op = .shl then .shl else if op = .sar then .sar else .shr)
                (← lift v.amount) old)
            | _ => do let y ← getV (← convRV F n τ v); lift (binVal F.checked (AssignOp.binOp op) old y)
          writeLoc F n L new
          return RVal.val new) := by
        intro L v
        refine MemPres.bind (MemPres.readLoc_all F L) fun old => ?_
        dsimp only
        rcases compound_dom h with ⟨hk, hi, hfit⟩ | ⟨hk, hb, ha⟩
        · split
          · rename_i hk'; exact absurd hk' hk
          · exact MemPres.bind (convRV_pres F n (.inl hi) hf.2.2.2 v) fun w =>
              MemPres.bind (MemPres.getV' w) fun y => MemPres.bind (MemPres.lift' _) fun nw =>
                MemPres.bind (MemPres.writeLoc' F n (loc_of_frag (.inl hf.2.2.1)) L nw) fun _ => MemPres.pure' _
        · split
          · exact MemPres.bind (MemPres.lift' _) fun k => MemPres.bind (MemPres.lift' _) fun nw =>
              MemPres.bind (MemPres.writeLoc' F n (loc_of_frag (.inl hf.2.2.1)) L nw) fun _ => MemPres.pure' _
          · rename_i hn; exact (hn hk).elim
      exact MemPres.bind (ih.val e hf.2.1 ho.2) fun v => MemPres.bind (ih.loc l hf.1 ho.1) fun L => core L v
    | incDec inc pre l =>
      have hn := ho.1
      have hl : τ.loc? = none := by cases τ <;> first | rfl | cases hn
      simp only [evalE]
      exact MemPres.bind (ih.loc l hf ho.2) fun L => MemPres.bind (MemPres.readLoc_all F L) fun old =>
        MemPres.bind (MemPres.lift' _) fun nw => MemPres.bind (MemPres.writeLoc' F n hl L nw) fun _ => MemPres.pure' _
    | indexMapping a k =>
      simp only [evalE]
      refine MemPres.bind (ih.ref a hf.1 ho.1) fun v => MemPres.bind (MemPres.getV' v) fun x => ?_
      cases x with
      | storRef hs p =>
        exact MemPres.bind (ih.val k hf.2.1 ho.2) fun kv => MemPres.bind (MemPres.keyStep' F n kv) fun st =>
          MemPres.bind (MemPres.readLoc_all F (.stor (p.go st))) fun _ => MemPres.pure' _
      | memRef hm _ => cases hm
      | cdRef hm _ _ => cases hm
    | call d h args =>
      simp only [evalE]
      refine MemPres.bind (ih.convArgs args hf.2 ho) fun vs => ?_
      have hm : MemPres (callInternal G F n d vs _) := fun H =>
        Hoare.conseq (hcall d h hf.1 vs H)
          (fun _ hi => ⟨hi, vals_value_refs _ vs (args_value_types args hf.2)⟩)
          (fun _ _ hi => hi.1) (fun _ _ hi => hi)
      exact MemPres.bind (MemPres.subNil _ hm) fun _ => MemPres.pure' _
    | _ => exact hf.elim

theorem exprPair_step (ih : ExprMemAt C G F n) {Γ : RCtx} {s t : STy}
    (a : RExpr E Γ s) (b : RExpr E Γ t) (ha : a.ValFragC C) (ha' : a.OpsOK)
    (hb : b.ValFragC C) (hb' : b.OpsOK) : MemPres (evalPair G F (n + 1) a b) := by
  simp only [evalPair]
  split
  · exact MemPres.bind (ih.val b hb hb') fun _ => MemPres.bind (ih.val a ha ha') fun _ => MemPres.pure' _
  · exact MemPres.bind (ih.val a ha ha') fun _ => MemPres.bind (ih.val b hb hb') fun _ => MemPres.pure' _

theorem exprRef_step (ih : ExprMemAt C G F n) {Γ : RCtx} {t : STy}
    (e : RExpr E Γ t) (hf : e.MapRefC C) (ho : e.OpsOK) : MemPres (evalE G F (n + 1) e) := by
  cases e with
  | state d h =>
    obtain ⟨hc, hp, tk, tv, rfl⟩ := hf
    simp only [evalE]
    rw [if_neg (by rw [hc]; exact Bool.false_ne_true), if_pos (show (STy.mapping tk tv).byRef = true from rfl)]
    exact MemPres.bind (MemPres.storRef' _ _) fun _ => MemPres.pure' _
  | indexMapping a k =>
    obtain ⟨ha, hk, hkey, tk, tv, rfl⟩ := hf
    simp only [evalE]
    refine MemPres.bind (ih.ref a ha ho.1) fun v => MemPres.bind (MemPres.getV' v) fun x => ?_
    cases x with
    | storRef hs p =>
      exact MemPres.bind (ih.val k hk ho.2) fun kv => MemPres.bind (MemPres.keyStep' F n kv) fun st =>
        MemPres.bind (MemPres.readLoc_all F (.stor (p.go st))) fun _ => MemPres.pure' _
    | memRef hm _ => cases hm
    | cdRef hm _ _ => cases hm
  | _ => exact hf.elim

theorem exprLoc_step (ih : ExprMemAt C G F n) {Γ : RCtx} {t : STy}
    (l : RLVal E Γ t) (hf : l.IsSimpleC C) (ho : l.OpsOK) : MemPres (evalLoc G F (n + 1) l) := by
  cases l with
  | «local» i => exact MemPres.pure' _
  | state d h hm => exact MemPres.pure' _
  | indexMapping a k =>
    obtain ⟨ha, hk, hkey, hv, hd⟩ := hf
    simp only [evalLoc]
    refine MemPres.bind (ih.ref a ha ho.1) fun v => MemPres.bind (MemPres.getV' v) fun x => ?_
    cases x with
    | storRef hs p =>
      exact MemPres.bind (ih.val k hk ho.2) fun kv => MemPres.bind (MemPres.keyStep' F n kv) fun _ => MemPres.pure' _
    | memRef hm _ => cases hm
    | cdRef hm _ _ => cases hm
  | _ => exact hf.elim

theorem exprArgs_step (ih : ExprMemAt C G F n) {Γ : RCtx} {ts : List STy}
    (es : RConvArgs E Γ ts) (hf : es.ValFragC C) (ho : es.OpsOK) :
    MemPres (evalConvArgs G F (n + 1) es) := by
  cases es with
  | nil => exact MemPres.pure' _
  | cons e h es =>
    simp only [evalConvArgs]
    exact MemPres.bind (ih.val e hf.1 ho.1) fun v =>
      MemPres.bind (convRV_pres F n (.inl h) hf.2.2.1 v) fun w =>
        MemPres.bind (MemPres.getV' w) fun _ => MemPres.bind (ih.convArgs es hf.2.2.2 ho.2) fun _ => MemPres.pure' _

end

theorem exprMemAt_zero (C : Decl → Prop) (G : Glob E) (F : Fr) : ExprMemAt C G F 0 where
  val := by intros; rw [evalE.eq_1]; exact MemPres.halt' _
  pair := by intros; rw [evalPair.eq_1]; exact MemPres.halt' _
  ref := by intros; rw [evalE.eq_1]; exact MemPres.halt' _
  loc := by intros; rw [evalLoc.eq_1]; exact MemPres.halt' _
  convArgs := by intros; rw [evalConvArgs.eq_1]; exact MemPres.halt' _

theorem exprMemAt_step {C : Decl → Prop} {G : Glob E} {F : Fr} {n : Nat}
    (ih : ExprMemAt C G F n) (hc : CallMemAt C G F n) : ExprMemAt C G F (n + 1) where
  val := exprVal_step ih hc
  pair := exprPair_step ih
  ref := exprRef_step ih
  loc := exprLoc_step ih
  convArgs := exprArgs_step ih

#print axioms exprVal_step
#print axioms exprMemAt_step
end Solidity.Source.Preservation
