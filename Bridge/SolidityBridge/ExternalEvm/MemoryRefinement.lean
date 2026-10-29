import SolidityBridge.ExternalEvm.MemoryBytes

/-! A persistent preallocated numeric-cell refinement. The capacity is active
before execution; all accesses stay inside it. Only the opaque padding allocator
is contracted, explicitly, rather than any read/write or simulation result. -/
namespace Solidity.Evm.External.Memory
open private EvmYul.toBytes' from EvmYul.UInt256

/-- A capacity-wide byte representation, independent of lookupMemory. Cells
outside the capacity are deliberately unobserved. All represented words are numeric. -/
structure Represents (cells : Nat) (m : Machine) (s : EvmYul.MachineState) : Prop where
  bounded : Bounded cells
  active : s.activeWords.toNat = cells
  physical : s.memory.size = 32 * cells
  cell : ∀ i, i < cells → ∃ v : EvmYul.UInt256,
    m.mem i = .val (wmod v.toNat) ∧
    ∀ j, j < 32 → s.memory.data[32 * i + j]! = (encoding v).data[j]!

theorem canonical (v : EvmYul.UInt256) : EvmYul.UInt256.ofNat v.toNat = v := by
  cases v with
  | mk v =>
    apply congrArg EvmYul.UInt256.mk
    apply Fin.ext
    exact Nat.mod_eq_of_lt v.isLt

theorem extent (cells : Nat) (m : Machine) (s : EvmYul.MachineState)
    (h : Represents cells m s) : (s.activeWords * (⟨32⟩ : EvmYul.UInt256)).toNat = 32 * cells := by
  change (s.activeWords.toNat * 32) % EvmYul.UInt256.size = 32 * cells
  rw [h.active, Nat.mul_comm, Nat.mod_eq_of_lt h.bounded.1]

theorem stable_active (cells : Nat) (m : Machine) (s : EvmYul.MachineState)
    (h : Represents cells m s) (i : Nat) (hi : i < cells) :
    EvmYul.UInt256.ofNat (EvmYul.MachineState.M s.activeWords.toNat (address i).toNat 32) =
      s.activeWords := by
  have ha : 32 * i < EvmYul.UInt256.size := by have := h.bounded.1; omega
  rw [address_toNat i ha]
  have hm : EvmYul.MachineState.M s.activeWords.toNat (32 * i) 32 = s.activeWords.toNat := by
    simp only [EvmYul.MachineState.M, h.active]
    omega
  rw [hm, canonical]

theorem lookup_represents (bound cells : Nat) (hp : PaddingCorrect bound) (_hb : 32 ≤ bound)
    (m : Machine) (s : EvmYul.MachineState) (h : Represents cells m s)
    (i : Nat) (hi : i < cells) :
    m.mem i = .val (wmod (s.lookupMemory (address i)).toNat) := by
  obtain ⟨v, hv, hbytes⟩ := h.cell i hi
  have ha : 32 * i < EvmYul.UInt256.size := by have := h.bounded.1; omega
  have hr := readback s.memory (encoding v) (32 * i) (padding_zero bound hp)
    (encoding_spec v).1 (by rw [h.physical]; omega) hbytes
  have hguard : ¬((address i).toNat ≥ s.memory.size ∨
      address i ≥ s.activeWords * (⟨32⟩ : EvmYul.UInt256)) := by
    have he := extent cells m s h
    change ¬((address i).toNat ≥ s.memory.size ∨
      (s.activeWords * (⟨32⟩ : EvmYul.UInt256)).toNat ≤ (address i).toNat)
    rw [address_toNat i ha, h.physical, he]
    omega
  rw [EvmYul.MachineState.lookupMemory, if_neg hguard, address_toNat i ha, hr]
  change m.mem i = .val (wmod (EvmYul.UInt256.ofNat
    (EvmYul.fromByteArrayBigEndian (encoding v))).toNat)
  rw [(encoding_spec v).2, canonical, hv]

theorem load_preserves (cells : Nat) (m : Machine) (s : EvmYul.MachineState)
    (h : Represents cells m s) (i : Nat) (hi : i < cells) :
    Represents cells {m with stack := m.mem i :: m.stack} (s.mload (address i)).2 := by
  have hs : (s.mload (address i)).2 = s := by
    change ({s with activeWords := EvmYul.UInt256.ofNat (EvmYul.MachineState.M s.activeWords.toNat (address i).toNat 32)} : EvmYul.MachineState) = s
    rw [stable_active cells m s h i hi]
  rw [hs]
  exact ⟨h.bounded, h.active, h.physical, h.cell⟩

theorem store_preserves (bound cells : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (m : Machine) (s : EvmYul.MachineState) (h : Represents cells m s)
    (i : Nat) (hi : i < cells) (v : EvmYul.UInt256) :
    Represents cells {m with mem := upd m.mem i (.val (wmod v.toNat))}
      (s.mstore (address i) v) := by
  have ha : 32 * i < EvmYul.UInt256.size := by have := h.bounded.1; omega
  have hs : v.toByteArray.size = 32 := (serialize bound hp hb v).1
  have hin : 32 * i + 32 ≤ s.memory.size := by rw [h.physical]; omega
  have hz := padding_zero bound hp
  have hstate : s.mstore (address i) v =
      {s with memory := ByteArray.write v.toByteArray 0 s.memory (32 * i) 32} := by
    unfold EvmYul.MachineState.mstore
    dsimp only []
    have hactive : (s.writeWord (address i) v).activeWords = s.activeWords := rfl
    rw [hactive, stable_active cells m s h i hi]
    unfold EvmYul.MachineState.writeWord EvmYul.writeBytes
    rw [address_toNat i ha]

  rw [hstate]
  refine ⟨h.bounded, h.active, ?_, ?_⟩
  · dsimp only []
    have hpSize : (ByteArray.write v.toByteArray 0 s.memory (32 * i) 32).size = 32 * cells :=
      (write_size v.toByteArray s.memory (32 * i) hz hs hin).trans h.physical
    exact hpSize
  · dsimp only []
    intro k hk
    by_cases hki : k = i
    · subst k
      refine ⟨v, upd_same m.mem i (.val (wmod v.toNat)), ?_⟩
      intro j hj
      rw [← serialize_eq bound hp hb v]
      exact write_get_same v.toByteArray s.memory (32 * i) j hz hs hin hj
    · obtain ⟨w, hw, hbytes⟩ := h.cell k hk
      refine ⟨w, ?_, ?_⟩
      · rw [upd_other m.mem (.val (wmod v.toNat)) hki]; exact hw
      · intro j hj
        rw [write_get_frame v.toByteArray s.memory (32 * i) (32 * k + j) hz hs hin
          (by rw [h.physical]; omega) (by omega)]
        exact hbytes j hj

theorem Represents.transport {cells : Nat} {m : Machine} {s : EvmYul.MachineState}
    (h : Represents cells m s) (m' : Machine) (s' : EvmYul.MachineState)
    (hm : m'.mem = m.mem) (ha : s'.activeWords = s.activeWords)
    (hb : s'.memory = s.memory) : Represents cells m' s' := by
  refine ⟨h.bounded, ?_, ?_, ?_⟩
  · rw [ha]; exact h.active
  · rw [hb]; exact h.physical
  · intro i hi
    rw [hm, hb]
    exact h.cell i hi

/-- Fixed-cell actual core/macro simulation, preserving the whole byte relation. -/
theorem load_refines (bound cells : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (m : Machine) (s : EvmYul.EVM.State) (h : Represents cells m s.toMachineState)
    (i : Nat) (hi : i < cells) (hst : m.stack = words s.stack) :
    ∃ m' s', (Instr.mload i).step m = .ok m' 0 ∧ run (loadMacro i) s = .ok s' ∧
      m'.stack = words s'.stack ∧ Represents cells m' s'.toMachineState := by
  let m' : Machine := {m with stack := m.mem i :: m.stack}
  let s' : EvmYul.EVM.State := loaded (pushed s i) (address i) s.stack
  refine ⟨m', s', rfl, load_macro s i, ?_, ?_⟩
  · change m.mem i :: m.stack =
      .val (wmod (s.toMachineState.lookupMemory (address i)).toNat) :: words s.stack
    rw [lookup_represents bound cells hp hb m s.toMachineState h i hi, hst]
  · apply h.transport m' s'.toMachineState rfl
    · exact stable_active cells m s.toMachineState h i hi
    · rfl

/-- Fixed-cell store simulation has a persistent postrelation, not just stack agreement. -/
theorem store_refines (bound cells : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (m : Machine) (s : EvmYul.EVM.State) (h : Represents cells m s.toMachineState)
    (i : Nat) (hi : i < cells) (v : EvmYul.UInt256) (st : List EvmYul.UInt256)
    (hst : m.stack = .val (wmod v.toNat) :: words st) :
    ∃ m' s', (Instr.mstore i).step m = .ok m' 0 ∧
      run (storeMacro i) {s with stack := v :: st} = .ok s' ∧
      m'.stack = words s'.stack ∧ Represents cells m' s'.toMachineState := by
  obtain ⟨m', s', hc, he, hstack, hsame, hframe, _⟩ := store_core_macro m s i v st hst
  refine ⟨m', s', hc, he, hstack, ?_⟩
  rw [store_macro] at he
  cases he
  have hm : m'.mem = upd m.mem i (.val (wmod v.toNat)) := by
    funext k
    by_cases hk : k = i
    · subst k; rw [upd_same]; exact hsame
    · rw [upd_other m.mem (.val (wmod v.toNat)) hk]; exact hframe k hk
  exact (store_preserves bound cells hp hb m s.toMachineState h i hi v).transport
    m' _ hm rfl rfl

/-- Dynamic addresses are word indices; the actual macro multiplies them by 32. -/
theorem loadAt_refines (bound cells : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (m : Machine) (s : EvmYul.EVM.State) (h : Represents cells m s.toMachineState)
    (a : EvmYul.UInt256) (ha : a.toNat < cells) (st : List EvmYul.UInt256)
    (hst : m.stack = .val (wmod a.toNat) :: words st) :
    ∃ m' s', Instr.mloadAt.step m = .ok m' 0 ∧
      run loadAtMacro {s with stack := a :: st} = .ok s' ∧
      m'.stack = words s'.stack ∧ Represents cells m' s'.toMachineState := by
  let m' : Machine := {m with stack := m.mem a.toNat :: words st}
  let s' : EvmYul.EVM.State :=
    loaded (scaled {s with stack := a :: st} a st) (address a.toNat) st
  refine ⟨m', s', ?_, loadAt_macro s a st, ?_, ?_⟩
  · change (match m.stack with
      | .val x :: tail => m.next (m.mem x.val :: tail)
      | _ => Out.fault) = .ok m' 0
    rw [hst]
    change m.next (m.mem (wmod a.toNat).val :: words st) = .ok m' 0
    rw [word_index]; rfl
  · change m.mem a.toNat :: words st =
      .val (wmod (s.toMachineState.lookupMemory (address a.toNat)).toNat) :: words st
    rw [lookup_represents bound cells hp hb m s.toMachineState h a.toNat ha]
  · apply h.transport m' s'.toMachineState rfl
    · exact stable_active cells m s.toMachineState h a.toNat ha
    · rfl

theorem storeAt_refines (bound cells : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (m : Machine) (s : EvmYul.EVM.State) (h : Represents cells m s.toMachineState)
    (a : EvmYul.UInt256) (ha : a.toNat < cells) (v : EvmYul.UInt256)
    (st : List EvmYul.UInt256)
    (hst : m.stack = .val (wmod a.toNat) :: .val (wmod v.toNat) :: words st) :
    ∃ m' s', Instr.mstoreAt.step m = .ok m' 0 ∧
      run storeAtMacro {s with stack := a :: v :: st} = .ok s' ∧
      m'.stack = words s'.stack ∧ Represents cells m' s'.toMachineState := by
  obtain ⟨m', s', hc, he, hstack, hsame, hframe, _⟩ := storeAt_core_macro m s a v st hst
  refine ⟨m', s', hc, he, hstack, ?_⟩
  rw [storeAt_macro] at he
  cases he
  have hm : m'.mem = upd m.mem a.toNat (.val (wmod v.toNat)) := by
    funext k
    by_cases hk : k = a.toNat
    · subst k; rw [upd_same]; exact hsame
    · rw [upd_other m.mem (.val (wmod v.toNat)) hk]; exact hframe k hk
  exact (store_preserves bound cells hp hb m s.toMachineState h a.toNat ha v).transport
    m' _ hm rfl rfl

private theorem canonical_injective (a b : EvmYul.UInt256)
    (h : wmod a.toNat = wmod b.toNat) : a = b := by
  have hv := congrArg Fin.val h
  rw [word_index, word_index] at hv
  cases a with
  | mk a => cases b with
    | mk b => exact congrArg EvmYul.UInt256.mk (Fin.ext hv)

/-- Pure zero encoding; this fact and the initial represented state need no FFI contract. -/
theorem encoding_zero : encoding (EvmYul.UInt256.ofNat 0) =
    ⟨Array.replicate 32 (0 : UInt8)⟩ := by
  have hb : BE (EvmYul.UInt256.ofNat 0).toNat = ByteArray.empty := by
    change (EvmYul.toBytes' 0).reverse.toByteArray = ByteArray.empty
    rw [EvmYul.toBytes']
    rfl
  apply ByteArray.ext
  simp only [encoding, hb, ByteArray.size, ByteArray.empty, ByteArray.emptyWithCapacity,
    Array.size_empty, Nat.sub_zero, ByteArray.data_append, Array.append_empty]

def controlState : EvmYul.EVM.State :=
  {(default : EvmYul.EVM.State) with
    memory := ⟨Array.replicate 64 (0 : UInt8)⟩, activeWords := .ofNat 2, stack := []}

/-- Inhabited 2-cell input, proved independently of PaddingCorrect. -/
theorem control_represents : Represents 2 Machine.init controlState.toMachineState := by
  refine ⟨by constructor <;> decide, rfl, by decide, ?_⟩
  intro i hi
  refine ⟨.ofNat 0, rfl, ?_⟩
  intro j hj
  rw [encoding_zero]
  change (Array.replicate 64 (0 : UInt8))[32 * i + j]! = (Array.replicate 32 (0 : UInt8))[j]!
  rw [getElem!_pos _ _ (by simp only [Array.size_replicate]; omega),
    getElem!_pos _ _ (by simp only [Array.size_replicate]; omega)]
  simp only [Array.getElem_replicate]

/-- Actual upstream store then load has readback and a persistent relation,
for any word at either valid boundary of the independently inhabited input. -/
theorem roundtrip_control (bound : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (i : Fin 2) (v : EvmYul.UInt256) :
    let s₁ := controlState.toMachineState.mstore (address i.val) v
    let m₁ := {Machine.init with mem := upd Machine.init.mem i.val (.val (wmod v.toNat))}
    Represents 2 m₁ s₁ ∧ s₁.lookupMemory (address i.val) = v ∧
      (∀ k, k < 2 → k ≠ i.val → s₁.lookupMemory (address k) = .ofNat 0) := by
  dsimp only []
  have h := store_preserves bound 2 hp hb Machine.init controlState.toMachineState
    control_represents i.val i.isLt v
  refine ⟨h, ?_, ?_⟩
  · have hr := lookup_represents bound 2 hp hb _ _ h i.val i.isLt
    dsimp only [] at hr
    rw [upd_same] at hr
    have hw : wmod v.toNat = wmod
        ((controlState.toMachineState.mstore (address i.val) v).lookupMemory (address i.val)).toNat :=
      Word.val.inj hr
    exact (canonical_injective v _ hw).symm
  · intro k hk hki
    have hr := lookup_represents bound 2 hp hb _ _ h k hk
    dsimp only [] at hr
    rw [upd_other Machine.init.mem (.val (wmod v.toNat)) hki] at hr
    have hw : wmod (EvmYul.UInt256.ofNat 0).toNat = wmod
        ((controlState.toMachineState.mstore (address i.val) v).lookupMemory (address k)).toNat :=
      Word.val.inj hr
    exact (canonical_injective (.ofNat 0) _ hw).symm

/-- Concrete core and upstream macro controls use the independently inhabited
input. The allocator contract is explicit and is not claimed inhabited. -/
theorem fixed_store_control (bound : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (i : Fin 2) (v : EvmYul.UInt256) :
    ∃ m' s', (Instr.mstore i.val).step
        {Machine.init with stack := [.val (wmod v.toNat)]} = .ok m' 0 ∧
      run (storeMacro i.val) {controlState with stack := [v]} = .ok s' ∧
      m'.stack = words s'.stack ∧ Represents 2 m' s'.toMachineState := by
  apply store_refines bound 2 hp hb _ controlState _ i.val i.isLt v [] rfl
  exact control_represents.transport _ _ rfl rfl rfl

theorem dynamic_store_control (bound : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (i : Fin 2) (v : EvmYul.UInt256) :
    ∃ m' s', Instr.mstoreAt.step
        {Machine.init with stack := [.val (wmod (EvmYul.UInt256.ofNat i.val).toNat),
          .val (wmod v.toNat)]} = .ok m' 0 ∧
      run storeAtMacro {controlState with stack := [.ofNat i.val, v]} = .ok s' ∧
      m'.stack = words s'.stack ∧ Represents 2 m' s'.toMachineState := by
  have hi : (EvmYul.UInt256.ofNat i.val).toNat = i.val := Nat.mod_eq_of_lt (by have := i.isLt; unfold EvmYul.UInt256.size; omega)
  apply storeAt_refines bound 2 hp hb _ controlState _ (.ofNat i.val) (by rw [hi]; exact i.isLt) v [] rfl
  exact control_represents.transport _ _ rfl rfl rfl

theorem fixed_load_control (bound : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (i : Fin 2) :
    ∃ m' s', (Instr.mload i.val).step Machine.init = .ok m' 0 ∧
      run (loadMacro i.val) controlState = .ok s' ∧
      m'.stack = words s'.stack ∧ Represents 2 m' s'.toMachineState :=
  load_refines bound 2 hp hb Machine.init controlState control_represents i.val i.isLt rfl

theorem dynamic_load_control (bound : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (i : Fin 2) :
    ∃ m' s', Instr.mloadAt.step
        {Machine.init with stack := [.val (wmod (EvmYul.UInt256.ofNat i.val).toNat)]} = .ok m' 0 ∧
      run loadAtMacro {controlState with stack := [.ofNat i.val]} = .ok s' ∧
      m'.stack = words s'.stack ∧ Represents 2 m' s'.toMachineState := by
  have hi : (EvmYul.UInt256.ofNat i.val).toNat = i.val := Nat.mod_eq_of_lt (by have := i.isLt; unfold EvmYul.UInt256.size; omega)
  apply loadAt_refines bound 2 hp hb _ controlState _ (.ofNat i.val) (by rw [hi]; exact i.isLt) [] rfl
  exact control_represents.transport _ _ rfl rfl rfl

/-- Outside alignment, a store of one starting at byte 1 changes byte 32,
which belongs to the next word-cell. Thus the aligned cell frame cannot extend here. -/
theorem unaligned_store_counterexample (bound : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound) :
    (controlState.toMachineState.mstore (.ofNat 1) (.ofNat 1)).memory.data[32]! = 1 ∧
      controlState.memory.data[32]! = 0 := by
  have hbe : BE (EvmYul.UInt256.ofNat 1).toNat = ⟨#[1]⟩ := by
    change (EvmYul.toBytes' 1).reverse.toByteArray = ⟨#[1]⟩
    rw [EvmYul.toBytes']
    change ((1 : UInt8) :: EvmYul.toBytes' 0).reverse.toByteArray = ⟨#[1]⟩
    rw [EvmYul.toBytes']
    rfl
  have hlast : (EvmYul.UInt256.ofNat 1).toByteArray.data[31]! = 1 := by
    rw [serialize_eq bound hp hb (.ofNat 1)]
    unfold encoding
    rw [hbe]
    decide +kernel
  have hs := (serialize bound hp hb (.ofNat 1)).1
  have hw := write_get_same (EvmYul.UInt256.ofNat 1).toByteArray controlState.memory 1 31
    (padding_zero bound hp) hs (by decide) (by decide)
  rw [hlast] at hw
  exact ⟨hw, by decide⟩

/-- Two actual fixed macros compose: the load uses the store's proved postrelation.
The final numeric stack observation is exact, with no ReadAgrees assumption. -/
theorem fixed_roundtrip (bound : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (i : Fin 2) (v : EvmYul.UInt256) :
    ∃ m₁ s₁ m₂ s₂,
      (Instr.mstore i.val).step {Machine.init with stack := [.val (wmod v.toNat)]} = .ok m₁ 0 ∧
      run (storeMacro i.val) {controlState with stack := [v]} = .ok s₁ ∧
      (Instr.mload i.val).step m₁ = .ok m₂ 0 ∧
      run (loadMacro i.val) s₁ = .ok s₂ ∧
      m₂.stack = [.val (wmod v.toNat)] ∧ m₂.stack = words s₂.stack ∧
      Represents 2 m₂ s₂.toMachineState := by
  obtain ⟨m₁, s₁, hc, he, hstack, hrep⟩ := fixed_store_control bound hp hb i v
  obtain ⟨m₂, s₂, hlc, hle, hlstack, hlrep⟩ :=
    load_refines bound 2 hp hb m₁ s₁ hrep i.val i.isLt hstack
  refine ⟨m₁, s₁, m₂, s₂, hc, he, hlc, hle, ?_, hlstack, hlrep⟩
  have hc' : Out.ok {Machine.init with stack := [], mem := upd Machine.init.mem i.val (.val (wmod v.toNat))} 0 = .ok m₁ 0 := hc
  have hmc : {Machine.init with stack := [], mem := upd Machine.init.mem i.val (.val (wmod v.toNat))} = m₁ := by
    injection hc'
  have hlc' : Out.ok {m₁ with stack := m₁.mem i.val :: m₁.stack} 0 = .ok m₂ 0 := hlc
  have hml : {m₁ with stack := m₁.mem i.val :: m₁.stack} = m₂ := by
    injection hlc'
  rw [← hml, ← hmc]
  dsimp only []
  rw [upd_same]

/-- The first index past capacity cannot satisfy the simulation's access premise.
This is not an executable interpreter refusal. -/
theorem capacity_refusal (cells : Nat) : ¬cells < cells := Nat.lt_irrefl cells

/-- The actual upstream out-of-capacity load expands activeWords but does not
allocate physical bytes. The original capacity relation is therefore lost. -/
theorem capacity_load_counterexample :
    let post := (controlState.toMachineState.mload (address 2)).2
    post.activeWords.toNat = 3 ∧ post.memory.size = 64 ∧
      ∀ m : Machine, ¬Represents 2 m post := by
  have ha : (controlState.toMachineState.mload (address 2)).2.activeWords.toNat = 3 := by decide
  refine ⟨ha, by decide, ?_⟩
  intro m h
  have he := h.active
  rw [ha] at he
  contradiction

end Solidity.Evm.External.Memory

/-- info: 'Solidity.Evm.External.Memory.lookup_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.lookup_represents

/-- info: 'Solidity.Evm.External.Memory.load_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.load_preserves

/-- info: 'Solidity.Evm.External.Memory.store_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.store_preserves

/-- info: 'Solidity.Evm.External.Memory.load_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.load_refines

/-- info: 'Solidity.Evm.External.Memory.store_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.store_refines

/-- info: 'Solidity.Evm.External.Memory.loadAt_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.loadAt_refines

/-- info: 'Solidity.Evm.External.Memory.storeAt_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.storeAt_refines

/-- info: 'Solidity.Evm.External.Memory.control_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.control_represents

/-- info: 'Solidity.Evm.External.Memory.roundtrip_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.roundtrip_control

/-- info: 'Solidity.Evm.External.Memory.fixed_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.fixed_roundtrip

/-- info: 'Solidity.Evm.External.Memory.unaligned_store_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.unaligned_store_counterexample

/-- info: 'Solidity.Evm.External.Memory.capacity_load_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.capacity_load_counterexample
