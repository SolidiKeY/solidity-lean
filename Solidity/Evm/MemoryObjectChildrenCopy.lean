import Solidity.Evm.MemoryObjectChildLoop

/-! The actual source fold for a run of empty dynamic-array defaults. -/
namespace Solidity.Evm.Memory.Objects

def childrenCopy {H : HTy} (hp : Heap H) (E : Ty)
    (hm : (Ty.ref (.array E)).mapFree = true) (n : Nat) :=
  (SVec.ofList (List.replicate n (SVal.dflt (.ref (.array E))))).copyStToM hp hm

theorem childrenCopy_zero {H : HTy} (hp : Heap H) (E : Ty)
    (hm : (Ty.ref (.array E)).mapFree = true) :
    childrenCopy hp E hm 0 = ⟨List.prefix_refl H, hp, ⟨[], rfl⟩⟩ := by
  simp only [childrenCopy, List.replicate_zero, SVec.ofList, SVec.copyStToM_nil]

theorem childrenCopy_succ {H : HTy} (hp : Heap H) (E : Ty)
    (hm : (Ty.ref (.array E)).mapFree = true) (n : Nat) :
    childrenCopy hp E hm (n + 1) =
      let g₁ := Grown.alloc (R := .array E) ⟨List.prefix_refl H, hp, emptyArray E⟩
      let g₂ := childrenCopy g₁.heap E hm n
      ⟨g₁.ext.trans g₂.ext, g₂.heap,
        ⟨g₁.val.wk g₂.ext :: g₂.val.1, by
          simpa only [List.length_cons, List.length_replicate] using
            congrArg Nat.succ g₂.val.2⟩⟩ := by
  simp only [childrenCopy, List.replicate_succ, SVec.ofList,
    SVec.copyStToM_cons, SVal.dflt_array, SVal.copyStToM_array, SVec.copyStToM_nil]
  rfl

/-- Every default child is a different actual newly appended source identity. -/
theorem childrenCopy_ids {H : HTy} (hp : Heap H) (E : Ty)
    (hm : (Ty.ref (.array E)).mapFree = true) (n : Nat) :
    (childrenCopy hp E hm n).val.1.map (fun r => r.id) = List.range' H.length n := by
  induction n generalizing H with
  | zero => rw [childrenCopy_zero]; rfl
  | succ n ih =>
    rw [childrenCopy_succ]
    change H.length :: (childrenCopy (hp.alloc (emptyArray E)).1 E hm n).val.1.map
      (fun r => r.id) = List.range' H.length (n + 1)
    rw [ih, List.range'_succ]
    simp only [List.length_append, List.length_singleton]

private theorem loopTurn_true (rc rb : Machine → Out) (m m' : Machine)
    (hc : rc m = .ok (m.push w[1]) 0) (hb : rb m = .ok m' 0) :
    loopTurn rc rb m = .inl m' := by
  rw [loopTurn, hc]
  change (match rb m with
    | .ok m₂ 0 => Sum.inl m₂
    | .ok _ (_ + 1) => Sum.inr Out.fault
    | r => .inr r) = _
  rw [hb]

private theorem loopTurn_false (rc rb : Machine → Out) (m : Machine)
    (hc : rc m = .ok (m.push w[0]) 0) : loopTurn rc rb m = .inr (.ok m 0) := by
  rw [loopTurn, hc]
  rfl

/-- One successful turn returns the exact machine used by the source-fold induction. -/
theorem childrenTurn_more (m : Machine) (parent total index cursor : Fin W)
    (hc : m.mem 0 = .val cursor) (hi : index.val < total.val) :
    loopTurn (run childrenCondition) (run childrenBody) (control m parent total index) =
      .inl (control (storeChildMachine (allocateMachine m cursor (wmod 0)) parent index cursor)
        parent total (wmod (index.val + 1))) := by
  have hcond : run childrenCondition (control m parent total index) =
      .ok ((control m parent total index).push w[1]) 0 := by
    simpa only [hi, decide_true, bword, if_true] using childrenCondition_run m parent total index
  exact loopTurn_true _ _ _ _ hcond (childrenBody_run m parent total index cursor hc)

theorem childrenTurn_done (m : Machine) (parent total : Fin W) :
    loopTurn (run childrenCondition) (run childrenBody) (control m parent total total) =
      .inr (.ok (control m parent total total) 0) := by
  have hcond : run childrenCondition (control m parent total total) =
      .ok ((control m parent total total).push w[0]) 0 := by
    simpa only [Nat.lt_irrefl, decide_false, bword, Bool.false_eq_true, if_false] using
      childrenCondition_run m parent total total
  exact loopTurn_false _ _ _ hcond

end Solidity.Evm.Memory.Objects
