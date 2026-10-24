import Solidity.Evm.MemorySource

/-!
# Local operations in the memory compiler

Array lengths and pointer aliases read the represented typed heap. Local
assignments and declarations write below its reserved frame limit, so neither
can disturb an object. Declaration correctness requires the new cell to fit
inside that limit.
-/
namespace Solidity.Evm.Memory

variable {C : Contract}

def lengthLocalCode {Γ : Ctx} {p : PrimTy} (b : Nat)
    (src : Idx Γ (.mem (.array (.prim p)))) : List Instr :=
  [.mload (cellOf b src), .mloadAt]

theorem lengthLocal_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (src : Idx Γ (.mem (.array (.prim p)))) :
    ValOutT .uint ((Val.mlen (.var src rfl) rfl).evalT σ)
      (run (lengthLocalCode b src) m) m := by
  obtain ⟨r, hr, hm⟩ := h.pointers src
  refine .inl ⟨σ.heap.lenU r, .val (wmod (σ.heap.len r .dyn)), ?_, ?_, ?_⟩
  · simp only [Val.evalT, MPath.mvalT, hr, bind, Except.bind]
    rfl
  · have hn : σ.heap.len r .dyn < W := σ.heap.len_dyn_lt r
    exact ReprV.uint_of (by
      simp only [Heap.lenU, Solidity.lenU, wmod_def, Nat.mod_eq_of_lt hn])
  · simp only [run, lengthLocalCode, exec_cons_zero, Instr.step, Machine.next,
      Out.ok_bind, hm, (h.heap.arrays r).length, exec_nil, Machine.push]

/-- A value-producing sequence followed by a local store implements a scoped
primitive assignment. The sequence's simulation is a kernel-checked premise. -/
theorem assignValue_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (dst : Idx Γ (.val p)) (e : Val C Γ p) (code : List Instr)
    (he : ValOutT p (e.evalT σ) (run code m) m) :
    ResultRepr L b frame F σ base m (TRun.assignLocal dst e σ)
      (run (code ++ [.mstore (cellOf b dst)]) m) := by
  rcases he with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
  · refine .inl ⟨⟨σ.setLocal dst v, List.prefix_refl _⟩,
      writeMachine m (cellOf b dst) w, ?_, ?_, h.setVal dst v w hw, rfl, ?_⟩
    · simp only [TRun.assignLocal, hv, bind, Except.bind]
      rfl
    · rw [run_append_ok hc]
      rfl
    · intro cursor hb ha
      exact ha.localWrite _ (Nat.lt_of_lt_of_le hb (le_lvl b dst))
        (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) w
  · refine .inr ⟨?_, run_append_revert hc⟩
    simp only [TRun.assignLocal, hv, bind, Except.bind]

/-- Rebinding a memory local changes its actual identity and pointer
together while preserving value locals, storage aliases and heap objects. -/
theorem StateRepr.setMem {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    (dst : Idx Γ (.mem R)) (r : HRef σ.H R) :
    StateRepr L b frame F (σ.setLocal dst (some r)) base
      (writeMachine m (cellOf b dst) (.val (base r.id))) := by
  have hl : lvl b dst < frame := Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals
  have hlook {t : LTy} (i : Idx Γ t) (hi : i.toNat ≠ dst.toNat) :
      Look.ofTEnv (σ.setLocal dst (some r)).env i = Look.ofTEnv σ.env i :=
    (Look.ofTEnv_set dst (some r) σ.env i).trans (Look.set_other _ _ _ _ hi)
  have hmem {t : LTy} (i : Idx Γ t) (hi : i.toNat ≠ dst.toNat) :
      (writeMachine m (cellOf b dst) (.val (base r.id))).memAt (lvl b i) =
        m.memAt (lvl b i) :=
    upd_other _ _ (fun he => hi ((lvl_eq_iff b i dst).mp he))
  constructor
  · refine ⟨h.core.store, ?_, ?_, h.core.net, h.core.netSelf, h.core.bound,
      ?_, h.core.env, h.core.funds, h.core.oracle⟩
    · intro q i
      have hi : i.toNat ≠ dst.toNat := fun he => by cases Idx.ty_eq i dst he
      rw [hlook i hi, hmem i hi]
      exact h.core.vals i
    · intro R i hi
      have hn : i.toNat ≠ dst.toNat := fun he => by cases Idx.ty_eq i dst he
      rw [hlook i hn, hmem i hn]
      exact h.core.aliases i hi
    · intro R i hi
      have hn : i.toNat ≠ dst.toNat := fun he => by cases Idx.ty_eq i dst he
      rw [hlook i hn, hmem i hn]
      exact h.core.fragile i hi
  · exact h.heap.localWrite _ hl _
  · intro q i
    by_cases hi : i.toNat = dst.toNat
    · cases Idx.ty_eq i dst hi
      cases Idx.toNat_inj i dst hi
      exact ⟨r, TEnv.get_set _ _ _, upd_same _ _ _⟩
    · obtain ⟨s, hs, hm⟩ := h.pointers i
      refine ⟨s, (TEnv.get_set_ne dst i (some r) σ.env (Ne.symm hi)).trans hs, ?_⟩
      exact (hmem i hi).trans hm
  · exact h.locals
  · exact h.structs.localWrite _ hl _
  · exact h.separated
  · exact RefFieldsRepr.localWrite h.refs h.structs _ hl _

theorem StateRepr.consVal {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy} (v : p.Denote) (w : Word)
    (hw : ReprV p v w) (hcap : b + (Γ.length + 1) ≤ frame) :
    StateRepr L b frame (F.push (.val p) .ok) (σ.push (t := .val p) v) base
      (writeMachine m (cell (b + Γ.length)) w) := by
  have hl : b + Γ.length < frame := by omega
  constructor
  · have hc := (h.core.consVal hw).congrLook (fun i => Look.ofTEnv_cons v σ.env i)
    exact ⟨hc.store, hc.vals, hc.aliases, hc.net, hc.netSelf, hc.bound,
      hc.fragile, hc.env, hc.funds, hc.oracle⟩
  · exact h.heap.localWrite _ hl w
  · intro q i
    cases i with
    | there j =>
      obtain ⟨r, hr, hm⟩ := h.pointers j
      refine ⟨r, hr, ?_⟩
      change upd m.mem (b + Γ.length) w (lvl b (.there j)) = _
      rw [lvl_there, upd_other _ _ (Nat.ne_of_lt (lvl_lt b j))]
      exact hm
  · exact hcap
  · exact h.structs.localWrite _ hl w
  · exact h.separated
  · exact RefFieldsRepr.localWrite h.refs h.structs _ hl _

theorem StateRepr.consMem {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    (r : HRef σ.H R) (hcap : b + (Γ.length + 1) ≤ frame) :
    StateRepr L b frame (F.push (.mem R) .ok)
      (σ.push (t := .mem R) (some r)) base
      (writeMachine m (cell (b + Γ.length)) (.val (base r.id))) := by
  have hl : b + Γ.length < frame := by omega
  have hmem {t : LTy} (i : Idx Γ t) :
      (writeMachine m (cell (b + Γ.length)) (.val (base r.id))).memAt (lvl b i) =
        m.memAt (lvl b i) := upd_other _ _ (Nat.ne_of_lt (lvl_lt b i))
  constructor
  · refine ⟨h.core.store, ?_, ?_, h.core.net, h.core.netSelf, h.core.bound,
      ?_, h.core.env, h.core.funds, h.core.oracle⟩
    · intro q i
      cases i with
      | there j => simpa only [Look.ofTEnv_cons, Look.cons_there, lvl_there, hmem] using h.core.vals j
    · intro R i hi
      cases i with
      | there j =>
        simpa only [Look.ofTEnv_cons, Look.cons_there, lvl_there, hmem] using h.core.aliases j hi
    · intro R i hi
      cases i with
      | there j =>
        simpa only [Look.ofTEnv_cons, Look.cons_there, lvl_there, hmem] using h.core.fragile j hi
  · exact h.heap.localWrite _ hl _
  · intro q i
    cases i with
    | here =>
      refine ⟨r, rfl, ?_⟩
      change upd m.mem (b + Γ.length) (.val (base r.id)) (lvl b (.here : Idx _ _)) = _
      rw [lvl_here, upd_same]
    | there j =>
      obtain ⟨s, hs, hm⟩ := h.pointers j
      refine ⟨s, hs, ?_⟩
      change upd m.mem (b + Γ.length) (.val (base r.id)) (lvl b (.there j)) = _
      rw [lvl_there, upd_other _ _ (Nat.ne_of_lt (lvl_lt b j))]
      exact hm
  · exact hcap
  · exact h.structs.localWrite _ hl _
  · exact h.separated
  · exact RefFieldsRepr.localWrite h.refs h.structs _ hl _

def aliasLocalCode {Γ : Ctx} {R : RefTy} (b : Nat)
    (dst src : Idx Γ (.mem R)) : List Instr :=
  [.mload (cellOf b src), .mstore (cellOf b dst)]

theorem aliasLocal_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    (dst src : Idx Γ (.mem R)) (hmf : (Ty.ref R).mapFree = true) :
    ResultRepr L b frame F σ base m (TRun.rebindMem dst (.alias (.var src hmf)) σ)
      (run (aliasLocalCode b dst src) m) := by
  obtain ⟨r, hr, hm⟩ := h.pointers src
  refine .inl ⟨⟨σ.setLocal dst (some r), List.prefix_refl _⟩, _, ?_, ?_, h.setMem dst r, rfl, ?_⟩
  · simp only [TRun.rebindMem, MRhs.evalT, MPath.mvalT, hr, bind, Except.bind,
      pure, Except.pure]
  · simp only [run, aliasLocalCode, exec_cons_zero, Instr.step, Machine.next,
      Out.ok_bind, hm, exec_nil, writeMachine]
  · intro cursor hb ha
    exact ha.localWrite _ (Nat.lt_of_lt_of_le hb (le_lvl b dst))
      (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) _

def declareAliasCode {Γ : Ctx} {R : RefTy} (b : Nat)
    (src : Idx Γ (.mem R)) : List Instr :=
  [.mload (cellOf b src), .mstore (cell (b + Γ.length))]

theorem declareAlias_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    (src : Idx Γ (.mem R)) (hmf : (Ty.ref R).mapFree = true) (hcap : b + (Γ.length + 1) ≤ frame) :
    ResultRepr L b frame (F.push (.mem R) .ok) σ base m
      (TRun.declMem R (some (.alias (.var src hmf))) hmf σ)
      (run (declareAliasCode b src) m) := by
  obtain ⟨r, hr, hm⟩ := h.pointers src
  refine .inl ⟨⟨σ.push (t := .mem R) (some r), List.prefix_refl _⟩,
    _, ?_, ?_, h.consMem r hcap, rfl, ?_⟩
  · simp only [TRun.declMem, MRhs.evalT, MPath.mvalT, hr, bind, Except.bind,
      pure, Except.pure]
  · simp only [run, declareAliasCode, exec_cons_zero, Instr.step, Machine.next,
      Out.ok_bind, hm, exec_nil, writeMachine]
  · intro cursor hb ha
    exact ha.localWrite (b + Γ.length) (by omega) (by omega) _

theorem declareValue_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (e : Val C Γ p) (code : List Instr) (he : ValOutT p (e.evalT σ) (run code m) m)
    (hcap : b + (Γ.length + 1) ≤ frame) :
    ResultRepr L b frame (F.push (.val p) .ok) σ base m
      (TRun.declLocal p (some e) σ) (run (code ++ [.mstore (cell (b + Γ.length))]) m) := by
  rcases he with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
  · refine .inl ⟨⟨σ.push (t := .val p) v, List.prefix_refl _⟩,
      writeMachine m (cell (b + Γ.length)) w, ?_, ?_, h.consVal v w hw hcap, rfl, ?_⟩
    · simp only [TRun.declLocal, hv, bind, Except.bind]
      rfl
    · rw [run_append_ok hc]
      rfl
    · intro cursor hb ha
      exact ha.localWrite (b + Γ.length) (by omega) (by omega) w
  · refine .inr ⟨?_, run_append_revert hc⟩
    simp only [TRun.declLocal, hv, bind, Except.bind]

theorem declareDefault_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (p : PrimTy)
    (hcap : b + (Γ.length + 1) ≤ frame) :
    ResultRepr L b frame (F.push (.val p) .ok) σ base m
      (TRun.declLocal p none σ)
      (run [.push w[0], .mstore (cell (b + Γ.length))] m) := by
  refine .inl ⟨⟨σ.push (t := .val p) (PrimTy.dflt p), List.prefix_refl _⟩,
    writeMachine m (cell (b + Γ.length)) w[0], rfl, rfl,
    h.consVal _ _ (ReprV.dflt_zero p) hcap, rfl,
      fun _ hb ha => ha.localWrite (b + Γ.length) (by omega) (by omega) w[0]⟩

end Solidity.Evm.Memory
