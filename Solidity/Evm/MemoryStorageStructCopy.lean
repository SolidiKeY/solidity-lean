import Solidity.Evm.MemoryStorageCopySource
import Solidity.Evm.MemoryStructDefault

/-!
# Primitive-member memory-to-storage struct copies

Primitive fields occupy one word each in both layouts. The copy traverses
that finite payload with the existing structured loop, and preserves every
slot outside the destination's primitive members.
-/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

theorem primitiveField_offset {fs : List (Name × Ty)} (hp : primitiveMembers fs = true) :
    ∀ f, offsetIn fs f = fieldOffset fs f := by
  induction fs with
  | nil => intro f; rfl
  | cons ft fs ih =>
    obtain ⟨g, T⟩ := ft
    cases T with
    | ref R => cases hp
    | prim p =>
      intro f
      simp only [offsetIn, fieldOffset, size_prim, ih hp]

/-- Every payload position is an actual uniquely named primitive member. -/
theorem primitiveField_at {fs : List (Name × Ty)} (hp : primitiveMembers fs = true)
    (hd : nodupKeysB fs = true) (i : Nat) (hi : i < fs.length) :
    ∃ f p, ∃ _hf : lookupBy f fs = some (.prim p), fieldOffset fs f = i := by
  induction fs generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons ft fs ih =>
    obtain ⟨f, T⟩ := ft
    cases T with
    | ref R => cases hp
    | prim p =>
      have hh : (lookupBy f fs).isNone = true ∧ nodupKeysB fs = true := by
        simpa only [nodupKeysB, Bool.and_eq_true] using hd
      cases i with
      | zero => exact ⟨f, p, by simp only [lookupBy, if_true], by simp only [fieldOffset, if_true]⟩
      | succ i =>
        obtain ⟨g, q, hg, ho⟩ := ih hp hh.2 i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)
        have hgf : g ≠ f := by
          intro he
          subst g
          simp only [hg, Option.isNone_some, Bool.false_eq_true, false_and] at hh
        refine ⟨g, q, ?_, ?_⟩
        · simp only [lookupBy, hgf, if_false, hg]
        · simp only [fieldOffset, hgf, if_false, ho, Nat.add_comm]

/-- A finite primitive payload copy; input is destination above memory base. -/
def memoryStructCopyCode (n : Nat) : List Instr :=
  [.swap 1, .push (.val (wmod n)), .push w[0]] ++
  [.loop copyRangeCond copyRangeBody] ++ [.pop, .pop, .pop, .pop]

attribute [local irreducible] loopRun

theorem memoryStructCopy_run (m : Machine) (base : Fin W) (dst : Slot) (n : Nat)
    (words : Nat → Fin W) (hn : n < W) (hs : base.val + n ≤ W)
    (hw : ∀ i, i < n → m.mem (base.val + i) = .val (words i)) :
    run (memoryStructCopyCode n) ((m.push (.val base)).push (.slot dst)) =
      .ok {m with store := rangeStore (fun i st => WordStore.write st (dst.add i) (words i).val) 0 n m.store} 0 := by
  have he : run [.swap 1, .push (.val (wmod n)), .push w[0]]
      ((m.push (.val base)).push (.slot dst)) = .ok (rangeMachine m 0 n base dst) 0 := by
    simp only [run, rangeMachine, Machine.push, exec_cons_zero, Instr.step, Machine.next,
      Out.ok_bind, exec_nil, List.getElem?_cons_zero, List.set_cons_zero,
      List.cons_append, List.nil_append, wmod_def, Nat.zero_mod]
  rw [memoryStructCopyCode, List.append_assoc, run_append_ok he,
    run_append_ok (copyRange_run m n base dst words hn hs hw)]
  unfold run
  rfl

theorem StructRepr.payloads {H : HTy} {s : Name} {hp : Heap H} {r : HRef H (.struct s)}
    {base : Fin W} {m : Machine} (h : StructRepr hp r base m)
    (hprim : primitiveMembers (structDef s) = true) :
    ∀ i, i < (structDef s).length →
      m.mem (base.val + i) = .val (payloadWord (m.mem (base.val + i))) := by
  intro i hi
  obtain ⟨f, p, hf, ho⟩ := primitiveField_at hprim (structDef_nodup s) i hi
  have hr := ReprV.payload (h.fields hf)
  simpa only [ho] using hr

/-- The copied store represents the actual heap snapshot, at every primitive field. -/
theorem primitiveStruct_copy_repr {H : HTy} {s : Name} {hp : Heap H} {r : HRef H (.struct s)}
    {base : Fin W} {m : Machine} (h : StructRepr hp r base m)
    (hprim : primitiveMembers (structDef s) = true) (st : WordStore) (dst : Slot) (L : Nat) :
    ReprAt (rangeStore (fun i st => WordStore.write st (dst.add i)
      (payloadWord (m.mem (base.val + i))).val) 0 (structDef s).length st)
      L (.ref (.struct s)) dst (MVal.copyMToSt hp (T := .ref (.struct s)) r) := by
  generalize hsnap : MVal.copyMToSt hp (T := .ref (.struct s)) r = snap
  cases snap with
  | struct fields =>
    refine .struct ?_
    intro f T hf
    cases T with
    | ref R => exact (primitiveMembers_noRef hprim hf).elim
    | prim p =>
      have hv := MVal.copyMToSt_field hp r hf
      rw [hsnap, SVal.find_field, SVal.find_nil] at hv
      have he : fields.get hf = .prim (hp.field r hf) := Option.some.inj hv
      rw [he]
      have ho : offset s f = fieldOffset (structDef s) f := primitiveField_offset hprim f
      have hi := fieldOffset_bound hf
      have hr := h.fields hf
      have hw : (rangeStore (fun i st => WordStore.write st (dst.add i)
          (payloadWord (m.mem (base.val + i))).val) 0 (structDef s).length st).cells
          (dst.add (offset s f)) = payloadWord (m.mem (base.val + fieldOffset (structDef s) f)) :=
        Fin.ext (by rw [ho]; exact rangeStore_written dst _ _ 0 st _ (Nat.zero_le _) (by omega))
      exact .prim (by rw [hw, ← ReprV.payload hr]; exact hr)

/-- A struct payload write touches only the destination's typed members. -/
theorem primitiveStruct_copy_other {s : Name} (hprim : primitiveMembers (structDef s) = true)
    (st : WordStore) (dst : Slot) (words : Nat → Fin W) (x : Slot)
    (hx : ¬ Occ (.ref (.struct s)) dst x) :
    rangeStore (fun i st => WordStore.write st (dst.add i) (words i).val) 0 (structDef s).length st x = st x := by
  apply rangeStore_other
  intro i _ hi he
  obtain ⟨f, p, hf, ho⟩ := primitiveField_at hprim (structDef_nodup s) i (by omega)
  apply hx
  rw [he, ← ho, ← primitiveField_offset hprim f]
  exact .field hf .prim

def assignMemoryStructCode {Γ : Ctx} {s : Name} (b : Nat)
    (dst : Loc C Γ (.ref (.struct s))) (pointer : List Instr) : List Instr :=
  pointer ++ Evm.compileLoc b dst ++ memoryStructCopyCode (structDef s).length

attribute [local irreducible] run exec Instr.step

/-- Actual typed struct assignment, through any admitted finite source and
storage paths; source memory remains independent of the stored snapshot. -/
theorem assignMemoryStruct_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {s : Name}
    (dst : Loc C Γ (.ref (.struct s))) (src : MPath C Γ (.ref (.struct s)))
    (pointer : List Instr) (hp : PtrFrag b src pointer) (hl : locIn F false dst = true)
    (hprim : primitiveMembers (structDef s) = true)
    (hst : static (.ref (.struct s)) = true) (hfit : (structDef s).length < W) :
    ResultRepr L b frame F σ base m (TRun.assignFromMem dst src σ)
      (run (assignMemoryStructCode b dst pointer) m) := by
  obtain ⟨r, hr, hptr⟩ := hp.correct h
  let n := (structDef s).length
  let words := fun i => payloadWord (m.mem ((base r.id).val + i))
  have hs := h.structs.objects r
  rw [assignMemoryStructCode, List.append_assoc, run_append_ok hptr]
  rcases loc_sim dst (h.core.push (.val (base r.id))) hl with
    ⟨sr, slot, old, hres, hold, hpath, _, hloc⟩ | ⟨hres, hloc⟩
  · rw [run_append_ok hloc]
    have hrun := memoryStructCopy_run m (base r.id) slot n words hfit hs.space (hs.payloads hprim)
    rw [hrun]
    let copied := rangeStore (fun i st => WordStore.write st (slot.add i) (words i).val) 0 n m.store
    have hn := primitiveStruct_copy_repr hs hprim m.store slot L
    have hnew := (overlay_repr hn _ (Nat.lt_succ_self _) hst).2 old
    obtain ⟨st', hsave, hrep⟩ := save_repr h.core.store hpath ⟨old, hold⟩ hnew
      (fun x hx => primitiveStruct_copy_other hprim m.store slot words x hx)
    have hwrite : σ.storage.write sr (MVal.copyMToSt σ.heap (T := .ref (.struct s)) r) = some st' := by
      rw [write_ref _ _ _ (Sto.find_of_findLive hold)]
      exact hsave
    have hlen : ∀ x, LenSlot C x → m.store x ≤ copied x := by
      intro x hx
      have he : copied x = m.store x := rangeStore_other slot words x n 0 m.store (by
        intro i _ hi he
        obtain ⟨f, p, hf, ho⟩ := primitiveField_at hprim (structDef_nodup s) i (by omega)
        have hoc : OccAt true (.ref (.struct s)) slot (slot.add i) := by
          rw [← ho, ← primitiveField_offset hprim f]
          exact .field hf .prim
        obtain ⟨T, ht, hp⟩ := hpath.occAt hoc
        exact len_prim_disjoint hx ⟨sr.root, T, ht, he ▸ hp⟩)
      rw [he]
      exact Nat.le_refl _
    refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, {m with store := copied}, ?_, rfl,
      h.store hrep hlen, rfl, fun _ _ ha => ha.mem_eq rfl⟩
    simp only [TRun.assignFromMem, hr, hres, hwrite, bind, Except.bind, TRes.ofOpt, pure, Except.pure]
  · exact .inr ⟨by simp only [TRun.assignFromMem, hr, hres, bind, Except.bind], run_append_revert hloc⟩

end Solidity.Evm.Memory
