import Solidity.Evm.MemoryAlloc
import Solidity.Evm.MemoryLocals
import Solidity.Semantics.AllocBytes

/-!
# Source allocation and word-memory allocation

Primitive `new T[](n)` allocates one typed heap object, with no child objects.
The compiler's free cursor occupies cell zero, so a represented local frame
must start strictly above it. These local simulation lemmas prepare the
growing address-map result used by the compiler's allocation and
reached-capacity clauses.
-/
namespace Solidity.Evm.Memory

variable {C : Contract}

private theorem alloc_defaults_eq {H : HTy} (hp : Heap H) (p : PrimTy) (size : Fin W)
    {n : Nat} (g : Grown H (fun H' => {l : List (MVal H' (.prim p)) // l.length = n}))
    (hl : (List.replicate size.val (PrimTy.dflt p)).length = n)
    (hg : g = ⟨List.prefix_refl H, hp, ⟨List.replicate size.val (PrimTy.dflt p),
      hl⟩⟩) (q : g.val.1.length < 2 ^ 256) :
    Grown.alloc (R := .array (.prim p)) ⟨g.ext, g.heap, ⟨g.val.1, q⟩⟩ =
      Grown.alloc ⟨List.prefix_refl H, hp, defaultArray p size⟩ := by
  subst hg
  rfl

/-- Copying a new primitive array creates exactly the allocator's default object. -/
theorem newArray_copy {H : HTy} (hp : Heap H) (p : PrimTy) (size : Fin W) :
    (newArrT (.array (.prim p)) (indexValue size) rfl).copyStToM hp rfl =
      Grown.alloc ⟨List.prefix_refl H, hp, defaultArray p size⟩ := by
  rw [newArrT, SVal.copyStToM_array]
  have he : List.replicate size.val (SVal.dflt (.prim p)) =
      (List.replicate size.val (PrimTy.dflt p)).map
        (fun v => (SVal.prim v : SVal (.prim p))) := by
    rw [List.map_replicate]
    rfl
  with_unfolding_all exact (alloc_defaults_eq hp p size _ _
    (SVec.copyStToM_prims' hp _ _ rfl he) _)

/-- The actual scoped declaration run adopts that object and binds its fresh reference. -/
theorem newArray_decl {Γ : Ctx} (σ : State C Γ) (p : PrimTy)
    (n : Simple C Γ .uint) (size : Fin W) (hn : n.evalT σ = indexValue size) :
    TRun.declMem (.array (.prim p)) (some (.newArr n rfl)) rfl σ =
      .ok ⟨σ.allocPush (defaultArray p size), List.prefix_append _ _⟩ := by
  have he : (newArrT (.array (.prim p)) (n.evalT σ) rfl).copyStToM σ.heap rfl =
      Grown.alloc ⟨List.prefix_refl σ.H, σ.heap, defaultArray p size⟩ :=
    hn.symm ▸ newArray_copy σ.heap p size
  simp only [TRun.declMem, MRhs.evalT, State.copyStToMG, State.grow,
    bind, Except.bind, pure, Except.pure]
  with_unfolding_all exact State.adopt_push_alloc σ _ _ he _ _

private theorem adopt_rebind_alloc {Γ : Ctx} {R : RefTy} (σ : State C Γ)
    (dst : Idx Γ (.mem R)) (o : MObj σ.H R) (g : Grown σ.H (MVal · (.ref R)))
    (hg : g = Grown.alloc ⟨List.prefix_refl _, σ.heap, o⟩)
    (e : σ.H <+: (σ.adopt g).1.H) :
    (Except.ok ⟨(σ.adopt g).1.setLocal dst (some g.val), e⟩ : TRes (Solidity.Out C σ.H Γ)) =
      .ok ⟨(σ.alloc o).1.setLocal dst (some (σ.alloc o).2), List.prefix_append _ _⟩ := by
  subst hg
  rfl

/-- Rebinding adopts the fresh object while retaining all other source locals. -/
theorem newArray_rebind {Γ : Ctx} (σ : State C Γ) (p : PrimTy)
    (dst : Idx Γ (.mem (.array (.prim p)))) (n : Simple C Γ .uint)
    (size : Fin W) (hn : n.evalT σ = indexValue size) :
    TRun.rebindMem dst (.newArr n rfl) σ =
      .ok ⟨(σ.alloc (defaultArray p size)).1.setLocal dst
        (some (σ.alloc (defaultArray p size)).2), List.prefix_append _ _⟩ := by
  have he : (newArrT (.array (.prim p)) (n.evalT σ) rfl).copyStToM σ.heap rfl =
      Grown.alloc ⟨List.prefix_refl σ.H, σ.heap, defaultArray p size⟩ :=
    hn.symm ▸ newArray_copy σ.heap p size
  simp only [TRun.rebindMem, MRhs.evalT, State.copyStToMG, State.grow,
    bind, Except.bind, pure, Except.pure]
  with_unfolding_all exact adopt_rebind_alloc σ dst _ _ he _

/-- Allocation grows source identities while retaining every older local and pointer. -/
theorem StateRepr.allocate {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : StructAllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (p : PrimTy) (size : Fin W) (hspace : cursor.val + size.val + 1 < W) :
    StateRepr L b frame F (σ.alloc (defaultArray p size)).1
      (upd base σ.H.length cursor) (allocateMachine m cursor size) := by
  have hm : ∀ l, b ≤ l → l < b + Γ.length →
      (allocateMachine m cursor size).mem (cell l) = m.mem (cell l) := by
    intro l hl hu
    have hf : frame ≤ cursor.val := ha.arrays.free.above
    have hh : b + Γ.length ≤ frame := h.locals
    exact allocateMachine_other m cursor size l (by omega) (by omega)
  constructor
  · have hc := (h.core.congrMem hm).congrLook
      (fun i => Look.ofTEnv_wk (List.prefix_append σ.H [.array (.prim p)]) σ.env i)
    exact ⟨hc.store, hc.vals, hc.aliases, hc.net, hc.netSelf, hc.bound,
      hc.fragile, hc.env, hc.funds, hc.oracle⟩
  · exact (ha.allocateArray p size hspace).arrays.heap
  · intro q i
    obtain ⟨r, hr, hp⟩ := h.pointers i
    refine ⟨r.wk (List.prefix_append _ _), ?_, ?_⟩
    · change TEnv.get i (TEnv.wk _ Γ σ.env) = _
      rw [TEnv.get_wk, hr]
      rfl
    · change (allocateMachine m cursor size).mem (cell (lvl b i)) =
        .val (upd base σ.H.length cursor r.id)
      rw [hm _ (le_lvl b i) (lvl_lt b i), allocationBase_old base cursor r]
      exact hp
  · exact h.locals
  · exact (ha.allocateArray p size hspace).structs
  · exact (ha.allocateArray p size hspace).separated
  · exact RefFieldsRepr.allocateArray h.refs ha p size

/-- Evaluate a length, allocate its array, and store the pointer in the new local. -/
def declareNewCode {Γ : Ctx} (b : Nat) (n : Simple C Γ .uint) : List Instr :=
  compileSimple b n ++ allocateArrayCode ++ [.mstore (cell (b + Γ.length))]

/-- Allocate a fresh array, then replace one existing pointer local. -/
def rebindNewCode {Γ : Ctx} {p : PrimTy} (b : Nat)
    (dst : Idx Γ (.mem (.array (.prim p)))) (n : Simple C Γ .uint) : List Instr :=
  compileSimple b n ++ allocateArrayCode ++ [.mstore (cellOf b dst)]

/-- The source declaration and emitted instructions agree, with a grown address
map, a represented fresh pointer, and allocator invariants for the next statement. -/
theorem newArray_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : StructAllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (p : PrimTy) (n : Simple C Γ .uint) (hn : simpleIn n = true)
    (size : Fin W) (hs : n.evalT σ = indexValue size)
    (hspace : cursor.val + size.val + 1 < W) (hcap : b + (Γ.length + 1) ≤ frame) :
    let σ' := σ.allocPush (defaultArray p size)
    let base' := upd base σ.H.length cursor
    let m' := writeMachine (allocateMachine m cursor size)
      (cell (b + Γ.length)) (.val cursor)
    TRun.declMem (.array (.prim p)) (some (.newArr n rfl)) rfl σ =
        .ok ⟨σ', List.prefix_append _ _⟩ ∧
      run (declareNewCode b n) m = .ok m' 0 ∧
      StateRepr L b frame (F.push (.mem (.array (.prim p))) .ok) σ' base' m' ∧
      StructAllocatorRepr σ'.heap base' frame ⟨cursor.val + size.val + 1, hspace⟩ m' ∧
      m'.stack = m.stack := by
  refine ⟨newArray_decl σ p n size hs, ?_, ?_, ?_, rfl⟩
  · obtain ⟨w, hw, hr⟩ := simple_sim h.core n hn
    rw [hs] at hw
    obtain ⟨a, rfl, he⟩ := hw
    have he' : a = size := Fin.ext (Int.ofNat_inj.mp he.symm)
    subst a
    rw [declareNewCode, List.append_assoc, run_append_ok hr,
      run_append_ok (allocateArray_run m cursor size ha.arrays.free.cell)]
    rfl
  · have hid : (σ.alloc (defaultArray p size)).2.id = σ.H.length := rfl
    simpa only [hid, upd_same] using
      (h.allocate ha hb p size hspace).consMem (σ.alloc (defaultArray p size)).2 hcap
  · exact (ha.allocateArray p size hspace).localWrite (b + Γ.length)
      (by omega) (by omega) (.val cursor)

/-- Allocating rebinding changes the destination's identity and runtime pointer
together; old aliases, objects, allocator state and evaluation stack survive. -/
theorem rebindNew_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : StructAllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (p : PrimTy) (dst : Idx Γ (.mem (.array (.prim p))))
    (n : Simple C Γ .uint) (hn : simpleIn n = true)
    (size : Fin W) (hs : n.evalT σ = indexValue size)
    (hspace : cursor.val + size.val + 1 < W) :
    let σ' := (σ.alloc (defaultArray p size)).1.setLocal dst
      (some (σ.alloc (defaultArray p size)).2)
    let base' := upd base σ.H.length cursor
    let m' := writeMachine (allocateMachine m cursor size) (cellOf b dst) (.val cursor)
    TRun.rebindMem dst (.newArr n rfl) σ = .ok ⟨σ', List.prefix_append _ _⟩ ∧
      run (rebindNewCode b dst n) m = .ok m' 0 ∧
      StateRepr L b frame F σ' base' m' ∧
      StructAllocatorRepr σ'.heap base' frame ⟨cursor.val + size.val + 1, hspace⟩ m' ∧
      m'.stack = m.stack := by
  refine ⟨newArray_rebind σ p dst n size hs, ?_, ?_, ?_, rfl⟩
  · obtain ⟨w, hw, hr⟩ := simple_sim h.core n hn
    rw [hs] at hw
    obtain ⟨a, rfl, he⟩ := hw
    have he' : a = size := Fin.ext (Int.ofNat_inj.mp he.symm)
    subst a
    rw [rebindNewCode, List.append_assoc, run_append_ok hr,
      run_append_ok (allocateArray_run m cursor size ha.arrays.free.cell)]
    rfl
  · have hid : (σ.alloc (defaultArray p size)).2.id = σ.H.length := rfl
    simpa only [hid, upd_same] using
      (h.allocate ha hb p size hspace).setMem dst (σ.alloc (defaultArray p size)).2
  · exact (ha.allocateArray p size hspace).localWrite (cellOf b dst)
      (Nat.lt_of_lt_of_le hb (le_lvl b dst))
      (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) (.val cursor)

end Solidity.Evm.Memory
