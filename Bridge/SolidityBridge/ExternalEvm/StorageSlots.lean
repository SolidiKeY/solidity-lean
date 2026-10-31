import SolidityBridge.ExternalEvm.StorageMacros

/-!
Finite storage macro refinement. The relation observes a finite list of
symbolic cells and a represented stack. It does not equate gas, PC, byte memory,
unbounded layouts or other accounts. Setup records exact stack shapes, scratch
memory for hashing, observed read membership and alias-compatible writes.
-/
namespace Solidity.Evm.StorageSlots

structure Agrees (domain : List Slot) (m : Machine) (s : EvmYul.EVM.State) : Prop where
  stack : s.stack = m.stack.map wordAddress
  storage : Represents domain address m.store (storageRead s.toState)
  present : ∃ acc, s.toState.lookupAccount s.executionEnv.codeOwner = some acc

inductive Setup (domain : List Slot) : Instr → Machine → EvmYul.EVM.State → Prop where
  | push {m s} (w : Word) : Setup domain (.push w) m s
  | load {m s} (a : Slot) (tail : List Word)
      (stack : m.stack = .slot a :: tail) (observed : a ∈ domain) : Setup domain .sload m s
  | store {m s} (a : Slot) (v : Fin W) (tail : List Word)
      (stack : m.stack = .slot a :: .val v :: tail)
      (aliases : WriteCompatible domain address m.store a v) : Setup domain .sstore m s
  | array {m s} (a : Slot) (tail : List Word)
      (stack : m.stack = .slot a :: tail)
      (memory : ArraySetup s.toMachineState (address a)) : Setup domain .keccakArr m s
  | mapping {m s} (key : Fin W) (a : Slot) (tail : List Word)
      (stack : m.stack = .val key :: .slot a :: tail)
      (memory : MapSetup s.toMachineState (encode key) (address a)) : Setup domain .keccakMap m s

/-- Every admitted source step lowers to actual upstream evaluator steps and
preserves the finite relation. Writes use the exact alias condition, not a
collision-freedom premise. -/
theorem step_refines (domain : List Slot) (i : Instr) (m : Machine) (s : EvmYul.EVM.State)
    (h : Agrees domain m s) (setup : Setup domain i m s) :
    ∃ ops m' s', lowerInstr i = .ok ops ∧ i.step m = .ok m' 0 ∧
      runMacro ops s = .ok s' ∧ Agrees domain m' s' := by
  cases setup with
  | push w =>
    obtain ⟨out, he, hs, hf, _⟩ := push_step s (wordAddress w)
    have hl : lowerInstr (.push w) = .ok [(.Push .PUSH32, some (wordAddress w, 32))] := by
      cases w <;> rfl
    refine ⟨_, {m with stack := w :: m.stack}, out, hl, rfl, ?_, ?_⟩
    · rw [runMacro_cons_of_step he]
      rfl
    · refine ⟨?_, ?_, ?_⟩
      · change out.stack = (w :: m.stack).map wordAddress
        rw [hs, h.stack]
        rfl
      · change Represents domain address m.store (storageRead out.toState)
        rw [hf]
        exact h.storage
      · change ∃ acc, out.toState.lookupAccount out.toState.executionEnv.codeOwner = some acc
        rw [hf]
        exact h.present
  | load a tail hm ha =>
    have hstack : s.stack = address a :: tail.map wordAddress := by rw [h.stack, hm]; rfl
    obtain ⟨out, he, hs, hf⟩ := sload_step s (address a) (tail.map wordAddress) hstack
    refine ⟨[(.SLOAD, none)], {m with stack := .val (m.store.cells a) :: tail}, out, rfl, ?_, ?_, ?_⟩
    · simp only [Instr.step, hm, Machine.next]
    · rw [runMacro_cons_of_step he]
      rfl
    · refine ⟨?_, ?_, ?_⟩
      · change out.stack = encode (m.store.cells a) :: tail.map wordAddress
        have hv : encode (m.store.cells a) = (EvmYul.State.sload s.toState (address a)).2 := by
          rw [h.storage a ha]
          exact encode_decode _
        rw [hs, hv]
      · change Represents domain address m.store (storageRead out.toState)
        rw [hf, sload_preserves]
        exact h.storage
      · rcases h.present with ⟨acc, hp⟩
        refine ⟨acc, ?_⟩
        change out.toState.lookupAccount out.toState.executionEnv.codeOwner = some acc
        rw [hf, sload_account]
        exact hp
  | store a v tail hm hw =>
    have hstack : s.stack = address a :: encode v :: tail.map wordAddress := by rw [h.stack, hm]; rfl
    obtain ⟨out, he, hs, hf⟩ := sstore_step s (address a) (encode v) (tail.map wordAddress) hstack
    rcases h.present with ⟨acc, hp⟩
    refine ⟨[(.SSTORE, none)], {m with stack := tail, store := m.store.write a v.val}, out,
      rfl, ?_, ?_, ?_⟩
    · simp only [Instr.step, hm]
    · rw [runMacro_cons_of_step he]
      rfl
    · refine ⟨hs, ?_, ?_⟩
      · change Represents domain address (m.store.write a v.val) (storageRead out.toState)
        have hr : storageRead (EvmYul.State.sstore s.toState (address a) (encode v)) =
            (fun n => if n = address a then v else storageRead s.toState n) := by
          funext n
          rw [storage_read_write s.toState acc hp, decode_encode]
        rw [hf, hr]
        exact (write_iff h.storage a v).mpr hw
      · refine ⟨acc.updateStorage (address a) (encode v), ?_⟩
        change out.toState.lookupAccount out.toState.executionEnv.codeOwner = _
        rw [hf]
        exact account_after_sstore s.toState acc hp (address a) (encode v)
  | array a tail hm hmem =>
    have hstack : s.stack = address a :: tail.map wordAddress := by rw [h.stack, hm]; rfl
    obtain ⟨out, he, hs, hf, _⟩ := array_macro s a (tail.map wordAddress) hmem
    rw [← hstack] at he
    refine ⟨arrayMacro, {m with stack := .slot (.data a 0) :: tail}, out, rfl, ?_, he, ?_⟩
    · simp only [Instr.step, hm, Machine.next]
    · refine ⟨hs, ?_, ?_⟩
      · change Represents domain address m.store (storageRead out.toState)
        rw [hf]
        exact h.storage
      · change ∃ acc, out.toState.lookupAccount out.toState.executionEnv.codeOwner = some acc
        rw [hf]
        exact h.present
  | mapping key a tail hm hmem =>
    have hstack : s.stack = encode key :: address a :: tail.map wordAddress := by rw [h.stack, hm]; rfl
    obtain ⟨out, he, hs, hf, _⟩ := map_macro s key a (tail.map wordAddress) hmem
    rw [← hstack] at he
    refine ⟨mapMacro, {m with stack := .slot (.hash key a 0) :: tail}, out, rfl, ?_, he, ?_⟩
    · simp only [Instr.step, hm, Machine.next]
    · refine ⟨hs, ?_, ?_⟩
      · change Represents domain address m.store (storageRead out.toState)
        rw [hf]
        exact h.storage
      · change ∃ acc, out.toState.lookupAccount out.toState.executionEnv.codeOwner = some acc
        rw [hf]
        exact h.present

/-- Per-step representation assumptions along a finite program. The recursive
premise asks only for setup at the actual successful next configurations; the
refinement theorem establishes their existence rather than assuming it. -/
def Ready (domain : List Slot) : List Instr → Machine → EvmYul.EVM.State → Prop
  | [], _, _ => True
  | i :: code, m, s => Setup domain i m s ∧
      ∀ ops m' s', lowerInstr i = .ok ops → i.step m = .ok m' 0 →
        runMacro ops s = .ok s' → Ready domain code m' s'

/-- Forward refinement of every finite setup-admitted program, using the
actual symbolic-instruction runner, compiler lowering and upstream evaluator macro runner.
The finite observation domain and all setup/alias assumptions remain explicit. -/
theorem bounded_refinement (domain : List Slot) (code : List Instr)
    (m : Machine) (s : EvmYul.EVM.State) (h : Agrees domain m s)
    (ready : Ready domain code m s) :
    ∃ ops m' s', lowerProgram code = .ok ops ∧ Evm.run code m = .ok m' 0 ∧
      runMacro ops s = .ok s' ∧ Agrees domain m' s' := by
  induction code generalizing m s with
  | nil => exact ⟨[], m, s, rfl, rfl, rfl, h⟩
  | cons i code ih =>
    rcases ready with ⟨setup, next⟩
    obtain ⟨ops, m1, s1, hl, hc, ht, hr⟩ := step_refines domain i m s h setup
    obtain ⟨rest, m2, s2, hrl, hrc, hrt, hrr⟩ := ih m1 s1 hr (next ops m1 s1 hl hc ht)
    refine ⟨ops ++ rest, m2, s2, ?_, ?_, ?_, hrr⟩
    · simp only [lowerProgram, hl, hrl]
      rfl
    · change (i.step m).bind (fun m' k => Evm.exec code k m') = _
      rw [hc]
      exact hrc
    · rw [runMacro_append, ht]
      exact hrt

theorem singleton_compatible (store : WordStore) (a : Slot) (v : Fin W) :
    WriteCompatible [a] address store a v := by
  intro b hb hn _
  have he : b = a := by simpa only [List.mem_singleton] using hb
  exact False.elim (hn he)

/-- Nonempty initial relation for every finite domain, including hash slots
and colliding roots. Storage is genuinely zero and the executing account exists. -/
theorem fresh_agrees (domain : List Slot) : Agrees domain Machine.init freshAccount := by
  refine ⟨rfl, ?_, ⟨default, rfl⟩⟩
  intro a _
  rfl

/-- Arbitrary singleton write inputs inhabit the setup fragment. -/
theorem ready_write (m : Machine) (s : EvmYul.EVM.State) (a : Slot) (v : Fin W) :
    Ready [a] [.push (.val v), .push (.slot a), .sstore] m s := by
  refine ⟨.push _, ?_⟩
  intro ops m1 s1 _ hc _
  cases hc
  refine ⟨.push _, ?_⟩
  intro ops m2 s2 _ hc _
  cases hc
  refine ⟨.store a v m.stack rfl (singleton_compatible m.store a v), ?_⟩
  intro ops m3 s3 _ _ _
  trivial

theorem ready_read (m : Machine) (s : EvmYul.EVM.State) (a : Slot) :
    Ready [a] [.push (.slot a), .sload] m s := by
  refine ⟨.push _, ?_⟩
  intro ops m1 s1 _ hc _
  cases hc
  refine ⟨.load a m.stack rfl (by simp only [List.mem_singleton]), ?_⟩
  intro ops m2 s2 _ _ _
  trivial

theorem Ready.append {domain : List Slot} (first rest : List Instr) (m : Machine) (s : EvmYul.EVM.State)
    (hfirst : Ready domain first m s) (hrest : ∀ m' s', Ready domain rest m' s') :
    Ready domain (first ++ rest) m s := by
  induction first generalizing m s with
  | nil => exact hrest m s
  | cons i code ih =>
    refine ⟨hfirst.1, ?_⟩
    intro ops m1 s1 hl hc ht
    exact ih m1 s1 (hfirst.2 ops m1 s1 hl hc ht)

/-- Refusals for instructions outside this projected storage fragment remain
in the lowering and cannot be bypassed by a setup certificate. -/
theorem no_call_setup (domain : List Slot) (m : Machine) (s : EvmYul.EVM.State) :
    ¬ Setup domain .call m s := by intro h; cases h



theorem push_memory (w : Word) (s out : EvmYul.EVM.State) (ops : List Opcode)
    (hl : lowerInstr (.push w) = .ok ops) (ht : runMacro ops s = .ok out) :
    out.memory = s.memory := by
  obtain ⟨next, he, _, _, hm⟩ := push_step s (wordAddress w)
  have hlower : lowerInstr (.push w) =
      .ok [(.Push .PUSH32, some (wordAddress w, 32))] := by cases w <;> rfl
  rw [hlower] at hl
  cases hl
  rw [runMacro_cons_of_step he] at ht
  cases ht
  exact hm

/-- Source compiler mapping prefixes start with ordinary represented pushes;
the hash premise is discharged from their unchanged empty byte memory. -/
theorem ready_map_write_empty (m : Machine) (s : EvmYul.EVM.State)
    (a : Slot) (key v : Fin W)
    (hm : s.memory = (default : EvmYul.MachineState).memory) :
    Ready [.hash key a 0]
      [.push (.val v), .push (.slot a), .push (.val key), .keccakMap, .sstore] m s := by
  refine ⟨.push _, ?_⟩
  intro ops m1 s1 hl hc ht
  have hm1 := (push_memory (.val v) s s1 ops hl ht).trans hm
  cases hc
  refine ⟨.push _, ?_⟩
  intro ops m2 s2 hl hc ht
  have hm2 := (push_memory (.slot a) s1 s2 ops hl ht).trans hm1
  cases hc
  refine ⟨.push _, ?_⟩
  intro ops m3 s3 hl hc ht
  have hm3 := (push_memory (.val key) s2 s3 ops hl ht).trans hm2
  cases hc
  refine ⟨.mapping key a (.val v :: m.stack) rfl (map_setup_empty _ _ _ hm3), ?_⟩
  intro ops m4 s4 _ hc _
  cases hc
  exact ⟨.store (.hash key a 0) v m.stack rfl (singleton_compatible _ _ _),
    fun _ _ _ _ _ _ => True.intro⟩


/-- A source read followed by assignment to the same singleton cell. -/
theorem ready_read_store (m : Machine) (s : EvmYul.EVM.State) (a : Slot) :
    Ready [a] [.push (.slot a), .sload, .push (.slot a), .sstore] m s := by
  refine ⟨.push _, ?_⟩
  intro ops m1 s1 _ hc _
  cases hc
  refine ⟨.load a m.stack rfl (by simp only [List.mem_singleton]), ?_⟩
  intro ops m2 s2 _ hc _
  cases hc
  refine ⟨.push _, ?_⟩
  intro ops m3 s3 _ hc _
  cases hc
  exact ⟨.store a (m.store.cells a) m.stack rfl (singleton_compatible _ _ _),
    fun _ _ _ _ _ _ => True.intro⟩

/-- Empty memory and the finite storage relation jointly inhabit array setup. -/
theorem array_joint (domain : List Slot) (a : Slot) :
    let m := {Machine.init with stack := [.slot a]}
    let s := {freshAccount with stack := [address a]}
    Agrees domain m s ∧ Ready domain [.keccakArr] m s := by
  refine ⟨⟨rfl, (fresh_agrees domain).storage, (fresh_agrees domain).present⟩, ?_⟩
  exact ⟨.array a [] rfl (array_setup_empty _ _ rfl), fun _ _ _ _ _ _ => True.intro⟩

/-- Arbitrary keys and parents jointly inhabit mapping setup, without any
assumption on hash injectivity or numeric address separation. -/
theorem map_joint (domain : List Slot) (key : Fin W) (a : Slot) :
    let m := {Machine.init with stack := [.val key, .slot a]}
    let s := {freshAccount with stack := [encode key, address a]}
    Agrees domain m s ∧ Ready domain [.keccakMap] m s := by
  refine ⟨⟨rfl, (fresh_agrees domain).storage, (fresh_agrees domain).present⟩, ?_⟩
  exact ⟨.mapping key a [] rfl (map_setup_empty _ _ _ rfl), fun _ _ _ _ _ _ => True.intro⟩

/-- A concrete numeric collision prevents a nonzero symbolic write from
preserving both observed cells; no cryptographic collision is needed. -/
theorem actual_alias_refusal :
    ¬ WriteCompatible [.root 0, .root W] address Machine.init.store (.root 0) (wmod 7) := by
  intro h
  have he := h (.root W) (by exact List.mem_cons_of_mem _ (List.mem_singleton_self _)) (by intro he; cases he) root_alias
  change wmod 0 = wmod 7 at he
  have hn := congrArg Fin.val he
  norm_num [wmod, W] at hn

/-- info: 'Solidity.Evm.StorageSlots.bounded_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bounded_refinement
/-- info: 'Solidity.Evm.StorageSlots.array_macro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms array_macro
/-- info: 'Solidity.Evm.StorageSlots.map_macro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms map_macro

end Solidity.Evm.StorageSlots
