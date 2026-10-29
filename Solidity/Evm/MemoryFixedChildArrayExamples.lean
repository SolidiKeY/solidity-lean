import Solidity.Evm.Compiler

/-! Inhabited public compiler inputs with two real primitive children and a
populated parent. Redirecting a parent keeps an old alias; writes through the
old and new paths mutate different children. -/
namespace Solidity.Evm.Memory.FixedChildArrayExamples
open Semantics

private def C : Contract := contract!{}
private def childTy : RefTy := .fixed (.prim .uint) 1
private def parentTy : RefTy := .fixed (.ref childTy) 2
private def H : HTy := [childTy, childTy, parentTy]
private def left : HRef H childTy := ⟨0, rfl⟩
private def right : HRef H childTy := ⟨1, rfl⟩
private def parent : HRef H parentTy := ⟨2, rfl⟩
private def u (n : Nat) : PrimTy.uint.Denote := indexValue (wmod n)
private def hp : Heap H := (⟨[u 7], by decide⟩, (⟨[u 9], by decide⟩,
  (⟨[left, left], by decide⟩, ())))
private def base (i : Nat) : Fin W := if i = 0 then wmod 16 else if i = 1 then wmod 24 else wmod 32
private def machine : Machine := { Machine.init with stack := [w[77]], mem := fun a =>
  if a = 0 then w[40] else if a = 1 then w[24] else if a = 2 then w[24] else if a = 3 then w[32]
  else if a = 16 then w[7] else if a = 24 then w[9]
  else if a = 32 then w[16] else if a = 33 then w[16] else w[0] }
private def Γ : Ctx := [.mem parentTy, .mem childTy, .mem childTy]
private def state : State C Γ :=
  { storage := Storage.init C, H := H, heap := hp, env := (some parent, (some right, (some right, ()))) }

private theorem refs {R : RefTy} (r : HRef H R) :
    (R = childTy ∧ HEq r left) ∨ (R = childTy ∧ HEq r right) ∨
      (R = parentTy ∧ HEq r parent) := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi; exact .inl ⟨rfl, HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi; exact .inr (.inl ⟨rfl, HEq.rfl⟩)
    | succ i => cases i with
      | zero => cases hi; exact .inr (.inr ⟨rfl, HEq.rfl⟩)
      | succ i => cases hi

private theorem heap_repr : Objects.HeapRepr hp base 8 machine := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro R r
    rcases refs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr <;> decide +kernel
  · intro R r
    rcases refs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr <;> decide +kernel
  · intro R Q r q hn
    rcases refs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr
      <;> rcases refs q with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩ <;> cases hq
      <;> first | exact (hn rfl).elim | decide +kernel
  · intro A E a r
    rcases refs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr <;> cases a
    all_goals
      refine ⟨by decide +kernel, ?_, ?_⟩
      · intro hh
        first | cases (by simpa only [Objects.header] using hh : (0 : Nat) = 1)
              | decide +kernel
      · intro i v hv
        first
        | rw [MObj.elems_dyn] at hv
          cases i with
          | zero => cases hv; exact ReprV.uint_of rfl
          | succ i => cases hv
        | rw [MObj.elems_fixed] at hv
          cases i with
          | zero => cases hv <;> first | exact ReprV.uint_of rfl | rfl
          | succ i => cases i with
            | zero => cases hv <;> first | exact ReprV.uint_of rfl | rfl
            | succ i => cases hv
  · intro s r
    rcases refs r with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩ <;> cases ht
  · intro s f R r hf
    rcases refs r with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩ <;> cases ht

/-- Full ownership has a concrete populated fixed-parent input. -/
theorem initial_repr : Objects.StateRepr 1 1 8 (Frag.init Γ) state base machine := by
  refine ⟨?_, heap_repr, ?_, by decide⟩
  · have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
    refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
    all_goals intro p i
    all_goals cases i with
      | there i => cases i with
        | there i => cases i with
          | there i => nomatch i
  · intro R i
    cases i with
    | here => exact ⟨parent, rfl, rfl⟩
    | there i => cases i with
      | here => exact ⟨right, rfl, rfl⟩
      | there i => cases i with
        | here => exact ⟨right, rfl, rfl⟩
        | there i => nomatch i

/-- The complete allocator premise is inhabited, including the fixed parent. -/
theorem initial_allocator : Objects.AllocatorRepr hp base 8 ⟨40, by decide⟩ machine := by
  refine ⟨heap_repr, ⟨by decide, by decide, rfl, ?_⟩, ?_⟩
  · intro addr ha
    change 40 ≤ addr at ha
    simp only [machine, if_neg (show addr ≠ 0 by omega), if_neg (show addr ≠ 1 by omega), if_neg (show addr ≠ 2 by omega), if_neg (show addr ≠ 3 by omega), if_neg (show addr ≠ 16 by omega), if_neg (show addr ≠ 24 by omega), if_neg (show addr ≠ 32 by omega), if_neg (show addr ≠ 33 by omega)]
  · intro R r
    rcases refs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr <;> decide +kernel

/-- A cursor inside the live fixed parent cannot satisfy the complete allocator. -/
theorem allocator_overlap_refuted :
    ¬ Objects.AllocatorRepr hp base 8 ⟨33, by decide⟩ machine := by
  intro h
  have hh := h.live parent
  exact (by decide +kernel : ¬ ((base parent.id).val + Objects.cells hp parent ≤ 33)) hh

private def a : MPath C Γ (.ref parentTy) := .var .here rfl
private def x : Idx Γ (.mem childTy) := .there .here
private def y : MPath C Γ (.ref childTy) := .var (.there (.there .here)) rfl
private def lit (n : Int) (hn : PrimTy.uint.inRange n = true) : Val C Γ .uint := .simple (.lit n hn)
private def childPath (n : Int) (hn : PrimTy.uint.inRange n = true) : MPath C Γ (.ref childTy) :=
  .loc (.index .fixed a (lit n hn))
private def program : Prog C Γ Γ :=
  .cons (.rebindMem x (.alias (childPath 0 rfl)))
  (.cons (.assignMem (.index .fixed a (lit 0 rfl)) (.ref y))
  (.cons (.assignMem (.index .fixed (.var x rfl) (lit 0 rfl)) (.val (lit 11 rfl)))
  (.cons (.assignMem (.index .fixed (childPath 0 rfl) (lit 0 rfl)) (.val (lit 13 rfl))) .nil)))
private def compiled := (Compiler.compile (C := C) 1 (Frag.init Γ) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem compiled_input : compiled.Input 1 8 base state machine := by
  apply (compiled.object_input (by decide +kernel) 1 8 base state machine).mpr
  exact ⟨initial_repr, by decide +kernel⟩

theorem compiled_agrees : compiled.Agrees 1 8 base state machine := compiled.correct compiled_input

/-- Public agreement really preserves an inhabited complete allocator. -/
theorem allocator_preserved : ∃ o m', program.run state = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧ Objects.AllocatorRepr o.st.heap base 8 ⟨40, by decide⟩ m' := by
  have hc := compiled_agrees
  obtain ⟨o, ho⟩ : ∃ o, program.run state = .ok o := by
    have hok : (program.run state).toOption.isSome = true := by decide +kernel
    cases he : program.run state with
    | error e => simp only [he, Except.toOption, Option.isSome] at hok; cases hok
    | ok o => exact ⟨o, rfl⟩
  rcases hc with ⟨out, m', hs, ht, hk, hr⟩ | ⟨hs, ht⟩ | ⟨hp, ht, out, m', hs, hr⟩ | ⟨hs, ht⟩
  · have rep : Objects.StateRepr 1 1 8 compiled.frag out.st base m' ∧
        Objects.KeepsAllocator 1 8 state base machine out.st m' := by
      apply (compiled.object_rep (by decide +kernel) 1 8 base state machine out.st m').mp
      simpa only [show Evm.Prog.pushes program = 0 from rfl, Nat.add_zero] using hr
    exact ⟨out, m', hs, ht, rep.2 _ (by decide) initial_allocator⟩
  · simp only [ho, reduceCtorEq, and_false, or_self] at hs
  · cases hp
  · rw [ho] at hs; cases hs

private def observeSource (res : TRes (Solidity.Out C H Γ)) : Option (List Nat) := do
  let o ← res.toOption
  let a ← TEnv.get (.here : Idx Γ (.mem parentTy)) o.st.env
  let x ← TEnv.get (.there .here : Idx Γ (.mem childTy)) o.st.env
  let y ← TEnv.get (.there (.there .here) : Idx Γ (.mem childTy)) o.st.env
  let first ← o.st.heap.index a .fixed (u 0)
  let second ← o.st.heap.index a .fixed (u 1)
  let old ← o.st.heap.index x .fixed (u 0)
  let new ← o.st.heap.index y .fixed (u 0)
  pure [(base a.id).val, (base x.id).val, (base y.id).val,
    (base first.id).val, (base second.id).val, old.val.toNat, new.val.toNat]

private def observeTarget : Out → Option (List Nat)
  | .ok m _ => [m.mem 3, m.mem 2, m.mem 1, m.mem 32, m.mem 33, m.mem 16, m.mem 24].mapM
      (fun w => match w with | .val v => some v.val | .slot _ => none)
  | _ => none

theorem source_observation : observeSource (program.run state) = some [32,16,24,24,16,11,13] := by
  decide +kernel

theorem target_observation : observeTarget (run compiled.code machine) = some [32,16,24,24,16,11,13] := by
  decide +kernel

private def stackObservation : Out → Option (List Word)
  | .ok m _ => some m.stack
  | _ => none

theorem retained_stack : stackObservation (run compiled.code machine) = some [w[77]] := by
  decide +kernel

/-- A wrong child pointer is rejected even though all primitive children still match. -/
theorem wrong_pointer_refuted : ¬ Objects.ArrayRepr hp parent .fixed base (writeMachine machine 32 w[24]) := by
  intro h
  have he : w[24] = w[16] := h.elements 0 left (by rw [MObj.elems_fixed]; rfl)
  exact (by decide +kernel : w[24] ≠ w[16]) he

private def failingProgram (k : Fin 3) : Prog C Γ Γ :=
  if k.val = 0 then .cons (.rebindMem x (.alias (childPath 2 rfl))) .nil
  else if k.val = 1 then .cons (.assignMem (.index .fixed a (lit 2 rfl)) (.ref y)) .nil
  else .cons (.assignMem (.index .fixed (childPath 0 rfl) (lit 1 rfl)) (.val (lit 13 rfl))) .nil

private theorem failures_compile : ∀ k : Fin 3,
    (Compiler.compile (C := C) 1 (Frag.init Γ) (failingProgram k)).isSome = true := by decide +kernel
private def failed (k : Fin 3) :=
  (Compiler.compile (C := C) 1 (Frag.init Γ) (failingProgram k)).get (failures_compile k)
attribute [irreducible] failed

theorem failed_input (k : Fin 3) : (failed k).Input 1 8 base state machine := by
  have hm : ∀ k : Fin 3, (failed k).isObject = true := by decide +kernel
  exact ((failed k).object_input (hm k) 1 8 base state machine).mpr ⟨initial_repr, by
    have hc : ∀ k : Fin 3, 1 + frameNeedProg (failingProgram k) ≤ 8 := by decide +kernel
    exact hc k⟩

theorem failed_agrees (k : Fin 3) : (failed k).Agrees 1 8 base state machine :=
  (failed k).correct (failed_input k)

private def sourceReverted : TRes (Solidity.Out C H Γ) → Bool
  | .error .revert => true
  | _ => false
private def targetReverted : Out → Bool
  | .revert => true
  | _ => false

theorem source_bounds : ∀ k : Fin 3, sourceReverted ((failingProgram k).run state) = true := by
  decide +kernel

theorem target_bounds : ∀ k : Fin 3, targetReverted (run (failed k).code machine) = true := by
  decide +kernel


private def readProgram : Prog C Γ (.val .uint :: Γ) :=
  .cons (.declLocal .uint (.user "observed")
    (some (.readMem (.index .fixed (childPath 0 rfl) (lit 0 rfl))))) .nil
private def readCompiled := (Compiler.compile (C := C) 1 (Frag.init Γ) readProgram).get (by decide +kernel)
attribute [irreducible] readCompiled

theorem read_input : readCompiled.Input 1 8 base state machine :=
  (readCompiled.object_input (by decide +kernel) 1 8 base state machine).mpr
    ⟨initial_repr, by decide +kernel⟩
theorem read_agrees : readCompiled.Agrees 1 8 base state machine := readCompiled.correct read_input

private def readSource : Option Nat := do
  let o ← (readProgram.run state).toOption
  pure (TEnv.get (.here : Idx (.val .uint :: Γ) (.val .uint)) o.st.env).val.toNat
private def readTarget : Option Word := do
  let m ← match run readCompiled.code machine with | .ok m _ => some m | _ => none
  pure (m.mem 4)
theorem source_read : readSource = some 7 := by decide +kernel
theorem target_read : readTarget = some w[7] := by decide +kernel

private def aliasProgram : Prog C Γ (.mem childTy :: Γ) :=
  .cons (.declMem childTy (.user "retained") (some (.alias (childPath 0 rfl))) rfl rfl) .nil
private def aliasCompiled := (Compiler.compile (C := C) 1 (Frag.init Γ) aliasProgram).get (by decide +kernel)
attribute [irreducible] aliasCompiled

theorem alias_input : aliasCompiled.Input 1 8 base state machine :=
  (aliasCompiled.object_input (by decide +kernel) 1 8 base state machine).mpr
    ⟨initial_repr, by decide +kernel⟩
theorem alias_agrees : aliasCompiled.Agrees 1 8 base state machine := aliasCompiled.correct alias_input
private def aliasSource : Option Nat := do
  let o ← (aliasProgram.run state).toOption
  let r ← TEnv.get (.here : Idx (.mem childTy :: Γ) (.mem childTy)) o.st.env
  pure (base r.id).val
private def aliasTarget : Option Word := do
  let m ← match run aliasCompiled.code machine with | .ok m _ => some m | _ => none
  pure (m.mem 4)
theorem source_alias : aliasSource = some 16 := by decide +kernel
theorem target_alias : aliasTarget = some w[16] := by decide +kernel

end Solidity.Evm.Memory.FixedChildArrayExamples
