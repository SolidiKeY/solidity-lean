import Solidity.Source.Preservation.Expressions

/-! The existing fragment's result/reference validity, including its checked
call return defaults. No outcome or memory-operation admission is changed. -/
namespace Solidity.Source.Preservation
variable {E : Env} {H : HeapTy}

theorem rval_value_ok {t : STy} (h : t.isValue = true) (v : RVal E.layout t) : RValOK E H v := by
  cases v with
  | val x => exact Val.refOK_of_loc (loc_of_frag (.inl h)) x
  | const _ => trivial
  | strLit _ => trivial
  | hex _ _ => trivial
  | tuple _ => cases h

theorem rval_frag_ok {t : STy}
    (h : t.isValue = true ∨ (∃ q, t = .rational q) ∨ (∃ q k, t = .hexConst q k))
    (v : RVal E.layout t) : RValOK E H v := by
  rcases h with h | ⟨q, rfl⟩ | ⟨q, k, rfl⟩
  · exact rval_value_ok h v
  · cases v <;> first | trivial | exact Val.refOK_of_loc rfl _
  · cases v <;> first | trivial | exact Val.refOK_of_loc rfl _

theorem rvals_value_ok : ∀ {ts : List STy} (vs : RVals E.layout ts),
    ts.all STy.isValue = true → RValsOK E H vs
  | _, .nil, _ => trivial
  | _, .cons v vs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact ⟨rval_value_ok h.1 v, rvals_value_ok vs h.2⟩

theorem default_some_value {t : STy} (h : (Val.default E.layout t).isSome = true) : t.isValue = true := by
  cases t <;> first | rfl | (simp only [Val.default, Val.defaultElem] at h; cases h)

theorem ret_value_ok (rs : List STy) (h : rs.all STy.isValue = true)
    (v : RVal E.layout (STy.ret rs)) : RValOK E H v := by
  cases rs with
  | nil =>
    cases v with
    | val x => exact Val.refOK_of_loc rfl x
    | tuple vs => cases vs; trivial
  | cons t ts =>
    cases ts with
    | nil => exact rval_value_ok (by simpa only [List.all_cons, List.all_nil, Bool.and_true] using h) v
    | cons u us =>
      cases v with
      | val x => exact Val.refOK_of_loc rfl x
      | tuple vs => exact rvals_value_ok vs h

theorem expr_result_ok {A : Decl → Prop} {G : Glob E} {c : String} (hG : CallsOK A G c)
    {Γ : RCtx} {t : STy} (e : RExpr E Γ t) (hf : e.ValFragC A) (ho : e.OpsOK)
    (v : RVal E.layout t) : RValOK E H v := by
  cases e with
  | const q => exact rval_frag_ok (.inr (.inl ⟨q, rfl⟩)) v
  | bytesLit _ _ => exact rval_frag_ok (.inr (.inr ⟨_, _, rfl⟩)) v
  | addressLit _ => exact rval_value_ok rfl v
  | bool _ => exact rval_value_ok rfl v
  | this _ => exact rval_value_ok rfl v
  | «local» _ => exact rval_value_ok hf v
  | state _ _ => exact rval_value_ok hf.2.2.2.2 v
  | unary _ _ => exact rval_value_ok hf.2 v
  | binary _ _ _ => exact rval_value_ok hf.2.2 v
  | compare _ _ _ => exact rval_value_ok rfl v
  | compareConst _ _ _ => exact rval_value_ok rfl v
  | shiftLike _ _ _ _ => exact rval_value_ok hf.2.2 v
  | cond _ _ _ => exact rval_value_ok hf.2.2.2 v
  | conv _ _ => exact rval_value_ok hf.2.1 v
  | assign _ _ => exact rval_value_ok hf.2.2 v
  | compound _ _ _ _ => exact rval_value_ok hf.2.2.1 v
  | incDec _ _ _ =>
    have hn := ho.1
    have ht : t.isValue = true := by cases t <;> first | rfl | cases hn
    exact rval_value_ok ht v
  | indexMapping _ _ => exact rval_value_ok hf.2.2.2.1 v
  | call d h args =>
    obtain ⟨b, hb, hm, hl, hrs, hps, hz, hfrag, hops⟩ := hG d h hf.1
    apply ret_value_ok _ _ v
    simp only [List.all_eq_true]
    intro t ht
    exact default_some_value (hz t ht)
  | _ => exact hf.elim

#print axioms expr_result_ok
end Solidity.Source.Preservation
