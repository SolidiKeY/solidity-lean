import Solidity.Evm.Compiler

/-! Inhabited public compiler inputs with two real primitive children and a
populated parent. Redirecting a parent keeps an old alias; writes through the
old and new paths mutate different children. -/
namespace Solidity.Evm.Memory.RefArrayExamples
open Semantics

private def C : Contract := contract!{}
private def childTy : RefTy := .array (.prim .uint)
private def parentTy : RefTy := .array (.ref childTy)
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
  else if a = 16 then w[1] else if a = 17 then w[7] else if a = 24 then w[1] else if a = 25 then w[9]
  else if a = 32 then w[2] else if a = 33 then w[16] else if a = 34 then w[16] else w[0] }
private def Γ : Ctx := [.mem parentTy, .mem childTy, .mem childTy]
private def state : State C Γ :=
  { storage := Storage.init C, H := H, heap := hp, env := (some parent, (some right, (some right, ()))) }

private theorem primitiveRefs {p : PrimTy} (r : HRef H (.array (.prim p))) :
    p = .uint ∧ (HEq r left ∨ HEq r right) := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi; exact ⟨rfl, .inl HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi; exact ⟨rfl, .inr HEq.rfl⟩
    | succ i => cases i with
      | zero => cases hi
      | succ i => cases hi

private theorem referenceRefs {R : RefTy} (r : HRef H (.array (.ref R))) :
    R = childTy ∧ HEq r parent := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases i with
      | zero => cases hi; exact ⟨rfl, HEq.rfl⟩
      | succ i => cases hi

private theorem noStructs {s : Name} (r : HRef H (.struct s)) : False := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases i with
      | zero => cases hi
      | succ i => cases hi

private theorem primitive_repr : HeapRepr hp base 8 machine := by
  refine ⟨?_, ?_, ?_⟩
  · intro p r
    obtain ⟨rfl, hr | hr⟩ := primitiveRefs r <;> cases hr
    all_goals
      refine ⟨by decide +kernel, by decide +kernel, ?_⟩
      intro i v hv
      rw [MObj.elems_dyn] at hv
      cases i with
      | zero => cases hv; exact ReprV.uint_of rfl
      | succ i => cases hv
  · intro p r
    obtain ⟨rfl, hr | hr⟩ := primitiveRefs r <;> cases hr <;> decide +kernel
  · intro p q r s hn
    obtain ⟨rfl, hr | hr⟩ := primitiveRefs r <;> cases hr
      <;> obtain ⟨rfl, hs | hs⟩ := primitiveRefs s <;> cases hs
      <;> first | exact (hn rfl).elim | decide +kernel

private theorem reference_repr : RefArrayHeapRepr hp base 8 machine := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro R r
    obtain ⟨rfl, hr⟩ := referenceRefs r
    cases hr
    refine ⟨by decide +kernel, by decide +kernel, ?_⟩
    intro i v hv
    rw [MObj.elems_dyn] at hv
    cases i with
    | zero => cases hv; rfl
    | succ i => cases i with
      | zero => cases hv; rfl
      | succ i => cases hv
  · intro R r
    obtain ⟨rfl, hr⟩ := referenceRefs r
    cases hr
    decide +kernel
  · intro R Q r q hn
    obtain ⟨rfl, hr⟩ := referenceRefs r
    obtain ⟨rfl, hq⟩ := referenceRefs q
    cases hr
    cases hq
    exact (hn rfl).elim
  · intro R p r q
    obtain ⟨rfl, hr⟩ := referenceRefs r
    cases hr
    obtain ⟨rfl, hq | hq⟩ := primitiveRefs q <;> cases hq <;> decide +kernel
  · intro R s r q
    exact (noStructs q).elim

/-- The supplementary public input is actually inhabited. -/
theorem initial_repr : RefArrayStateRepr 1 1 8 (Frag.init Γ) state base machine := by
  refine ⟨⟨?_, primitive_repr, ?_, by decide,
    ⟨fun r => (noStructs r).elim, fun r => (noStructs r).elim, fun r => (noStructs r).elim⟩,
    (fun _ r => (noStructs r).elim), RefFieldsRepr.withoutStructs hp base machine (fun r => noStructs r)⟩,
    reference_repr⟩
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

private def a : MPath C Γ (.ref parentTy) := .var .here rfl
private def x : Idx Γ (.mem childTy) := .there .here
private def y : MPath C Γ (.ref childTy) := .var (.there (.there .here)) rfl
private def lit (n : Int) (hn : PrimTy.uint.inRange n = true) : Val C Γ .uint := .simple (.lit n hn)
private def childPath (n : Int) (hn : PrimTy.uint.inRange n = true) : MPath C Γ (.ref childTy) :=
  .loc (.index .dyn a (lit n hn))
private def program : Prog C Γ Γ :=
  .cons (.rebindMem x (.alias (childPath 0 rfl)))
  (.cons (.assignMem (.index .dyn a (lit 0 rfl)) (.ref y))
  (.cons (.assignMem (.index .dyn (.var x rfl) (lit 0 rfl)) (.val (lit 11 rfl)))
  (.cons (.assignMem (.index .dyn (childPath 0 rfl) (lit 0 rfl)) (.val (lit 13 rfl))) .nil)))
private def compiled := (Compiler.compile (C := C) 1 (Frag.init Γ) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem compiled_input : compiled.Input 1 8 base state machine := by
  apply (compiled.referenceArray_input (by decide +kernel) 1 8 base state machine).mpr
  exact initial_repr

theorem compiled_agrees : compiled.Agrees 1 8 base state machine := compiled.correct compiled_input

private def observeSource (res : TRes (Solidity.Out C H Γ)) : Option (List Nat) := do
  let o ← res.toOption
  let a ← TEnv.get (.here : Idx Γ (.mem parentTy)) o.st.env
  let x ← TEnv.get (.there .here : Idx Γ (.mem childTy)) o.st.env
  let y ← TEnv.get (.there (.there .here) : Idx Γ (.mem childTy)) o.st.env
  let first ← o.st.heap.index a .dyn (u 0)
  let second ← o.st.heap.index a .dyn (u 1)
  let old ← o.st.heap.index x .dyn (u 0)
  let new ← o.st.heap.index y .dyn (u 0)
  pure [(base a.id).val, (base x.id).val, (base y.id).val,
    (base first.id).val, (base second.id).val, old.val.toNat, new.val.toNat]

private def observeTarget : Out → Option (List Nat)
  | .ok m _ => [m.mem 3, m.mem 2, m.mem 1, m.mem 33, m.mem 34, m.mem 17, m.mem 25].mapM
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
theorem wrong_pointer_refuted : ¬ RefArrayRepr hp parent base (writeMachine machine 33 w[24]) := by
  intro h
  have he : w[24] = w[16] := h.elements 0 left (by rw [MObj.elems_dyn]; rfl)
  exact (by decide +kernel : w[24] ≠ w[16]) he

private def failingProgram (k : Fin 3) : Prog C Γ Γ :=
  if k.val = 0 then .cons (.rebindMem x (.alias (childPath 2 rfl))) .nil
  else if k.val = 1 then .cons (.assignMem (.index .dyn a (lit 2 rfl)) (.ref y)) .nil
  else .cons (.assignMem (.index .dyn (childPath 0 rfl) (lit 1 rfl)) (.val (lit 13 rfl))) .nil

private theorem failures_compile : ∀ k : Fin 3,
    (Compiler.compile (C := C) 1 (Frag.init Γ) (failingProgram k)).isSome = true := by decide +kernel
private def failed (k : Fin 3) :=
  (Compiler.compile (C := C) 1 (Frag.init Γ) (failingProgram k)).get (failures_compile k)
attribute [irreducible] failed

theorem failed_input (k : Fin 3) : (failed k).Input 1 8 base state machine := by
  have hm : ∀ k : Fin 3, (failed k).isReferenceArray = true := by decide +kernel
  exact ((failed k).referenceArray_input (hm k) 1 8 base state machine).mpr initial_repr

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

/-- Nonempty construction is still refused, rather than emitting zero child pointers. -/
theorem allocation_refused :
    (Compiler.compile (C := C) 1 (Frag.init Γ) (.cons
      (.declMem parentTy (.user "fresh") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil)).isNone = true := by
  decide +kernel

theorem default_declaration_refused :
    (Compiler.compile (C := C) 1 (Frag.init Γ) (.cons
      (.declMem parentTy (.user "fresh") none rfl rfl) .nil)).isNone = true := by
  decide +kernel

private def fixedΓ : Ctx := [.mem childTy, .mem (.fixed (.ref childTy) 2)]
private def fixedPath : MPath C fixedΓ (.ref childTy) :=
  .loc (.index .fixed (.var (.there .here) rfl) (.simple (.lit 0 rfl)))

theorem fixed_index_refused :
    (Compiler.compile (C := C) 1 (Frag.init fixedΓ) (.cons
      (.rebindMem .here (.alias fixedPath)) .nil)).isNone = true := by
  decide +kernel

end Solidity.Evm.Memory.RefArrayExamples
