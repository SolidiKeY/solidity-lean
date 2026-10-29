import Solidity.Evm.Compiler

/-! Populated reference-bearing structs inside a fixed reference array.
This validates the layout and RefFieldsRepr path without constructing the
reference-bearing struct, whose constructor remains another lane's API. -/
namespace Solidity.Evm.Memory.StructArrayInputExamples
open Semantics
private def C : Contract := contract!{ struct Holder { uint[] items; } }
private def leaf : RefTy := .array (.prim .uint)
private def holderName : Name := (C.structName? "Holder").getD ""
private def holder : RefTy := .struct holderName
private def parent : RefTy := .fixed (.ref holder) 2
private def H : HTy := [leaf, leaf, holder, holder, parent]
private def l0 : HRef H leaf := ⟨0, rfl⟩
private def l1 : HRef H leaf := ⟨1, rfl⟩
private def h0 : HRef H holder := ⟨2, rfl⟩
private def h1 : HRef H holder := ⟨3, rfl⟩
private def a0 : HRef H parent := ⟨4, rfl⟩
private def u (n : Nat) := indexValue (wmod n)
private def hp : Heap H := (⟨[u 7], by decide⟩, (⟨[u 9], by decide⟩,
  ((l0, ()), ((l1, ()), (⟨[h0,h0], by decide⟩, ())))))
private def base (i : Nat) : Fin W := if i = 0 then wmod 16 else if i = 1 then wmod 24
  else if i = 2 then wmod 32 else if i = 3 then wmod 40 else wmod 48
private def machine : Machine := {Machine.init with stack := [w[77]], mem := fun a =>
  if a = 0 then w[56] else if a = 1 then w[40] else if a = 2 then w[40] else if a = 3 then w[48]
  else if a = 16 then w[1] else if a = 17 then w[7] else if a = 24 then w[1] else if a = 25 then w[9]
  else if a = 32 then w[16] else if a = 40 then w[24] else if a = 48 then w[32] else if a = 49 then w[32] else w[0]}
private def Γ : Ctx := [.mem parent, .mem holder, .mem holder]
private def state : State C Γ :=
  {storage := Storage.init C, H := H, heap := hp,
    env := (some a0, (some h1, (some h1, ())))}

private theorem refs {R : RefTy} (r : HRef H R) :
    (R = leaf ∧ HEq r l0) ∨ (R = leaf ∧ HEq r l1) ∨ (R = holder ∧ HEq r h0) ∨
      (R = holder ∧ HEq r h1) ∨ (R = parent ∧ HEq r a0) := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi; exact .inl ⟨rfl, HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi; exact .inr (.inl ⟨rfl, HEq.rfl⟩)
    | succ i => cases i with
      | zero => cases hi; exact .inr (.inr (.inl ⟨rfl, HEq.rfl⟩))
      | succ i => cases i with
        | zero => cases hi; exact .inr (.inr (.inr (.inl ⟨rfl, HEq.rfl⟩)))
        | succ i => cases i with
          | zero => cases hi; exact .inr (.inr (.inr (.inr ⟨rfl, HEq.rfl⟩)))
          | succ i => cases hi

private theorem heap_repr : Objects.HeapRepr hp base 8 machine := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro R r
    rcases refs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩
      <;> cases hr <;> decide +kernel
  · intro R r
    rcases refs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩
      <;> cases hr <;> decide +kernel
  · intro R Q r q hn
    rcases refs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr
      <;> rcases refs q with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩ <;> cases hq
      <;> first | exact (hn rfl).elim | decide +kernel
  · intro A E a r
    rcases refs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩
      <;> cases hr <;> cases a
    all_goals
      refine ⟨by decide +kernel, ?_, ?_⟩
      · intro hh
        first | cases (by simpa only [Objects.header] using hh : (0 : Nat) = 1) | decide +kernel
      · intro i v hv
        first
        | rw [MObj.elems_dyn] at hv
          cases i with
          | zero => cases hv; exact ReprV.uint_of rfl
          | succ i => cases hv
        | rw [MObj.elems_fixed] at hv
          cases i with
          | zero => cases hv; rfl
          | succ i => cases i with
            | zero => cases hv; rfl
            | succ i => cases hv
  · intro s r
    rcases refs r with ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨ht, hr⟩
      <;> cases ht <;> cases hr
    all_goals
      refine ⟨by decide +kernel, ?_⟩
      intro f p hf
      change lookupBy f [("items", Ty.ref leaf)] = some (Ty.prim p) at hf
      by_cases he : f = "items"
      · subst f; cases hf
      · simp only [lookupBy, he, if_false] at hf; cases hf
  · intro s f R r hf
    rcases refs r with ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨ht, hr⟩
      <;> cases ht <;> cases hr
    all_goals
      change lookupBy f [("items", Ty.ref leaf)] = some (Ty.ref R) at hf
      by_cases he : f = "items"
      · subst f; cases hf; rfl
      · simp only [lookupBy, he, if_false] at hf; cases hf

/-- The reference fields and parent entries are populated, not vacuous assumptions. -/
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
    | here => exact ⟨a0, rfl, rfl⟩
    | there i => cases i with
      | here => exact ⟨h1, rfl, rfl⟩
      | there i => cases i with
        | here => exact ⟨h1, rfl, rfl⟩
        | there i => nomatch i
private def a : MPath C Γ (.ref parent) := .var .here rfl
private def x : Idx Γ (.mem holder) := .there .here
private def y : MPath C Γ (.ref holder) := .var (.there (.there .here)) rfl
private def lit (n : Int) (hn : PrimTy.uint.inRange n = true) : Val C Γ .uint := .simple (.lit n hn)
private def childPath (n : Int) (hn : PrimTy.uint.inRange n = true) : MPath C Γ (.ref holder) :=
  .loc (.index .fixed a (lit n hn))
private def items (p : MPath C Γ (.ref holder)) : MPath C Γ (.ref leaf) :=
  .loc (.field p "items" rfl)
private def program : Prog C Γ Γ :=
  .cons (.rebindMem x (.alias (childPath 0 rfl)))
  (.cons (.assignMem (.index .fixed a (lit 0 rfl)) (.ref y))
  (.cons (.assignMem (.index .dyn (items (.var x rfl)) (lit 0 rfl)) (.val (lit 11 rfl)))
  (.cons (.assignMem (.index .dyn (items (childPath 0 rfl)) (lit 0 rfl)) (.val (lit 13 rfl))) .nil)))
private def compiled := (Compiler.compile 1 (Frag.init Γ) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem compiled_input : compiled.Input 1 8 base state machine :=
  (compiled.object_input (by decide +kernel) 1 8 base state machine).mpr
    ⟨initial_repr, by decide +kernel⟩
theorem compiled_agrees : compiled.Agrees 1 8 base state machine := compiled.correct compiled_input
private def observeSource : Option (List Nat) := do
  let o ← (program.run state).toOption
  let a ← TEnv.get (.here : Idx Γ (.mem parent)) o.st.env
  let x ← TEnv.get (.there .here : Idx Γ (.mem holder)) o.st.env
  let y ← TEnv.get (.there (.there .here) : Idx Γ (.mem holder)) o.st.env
  let first ← o.st.heap.index a .fixed (u 0)
  let second ← o.st.heap.index a .fixed (u 1)
  let old ← o.st.heap.index (o.st.heap.field x (f := "items") rfl) .dyn (u 0)
  let new ← o.st.heap.index (o.st.heap.field y (f := "items") rfl) .dyn (u 0)
  pure [(base a.id).val, (base x.id).val, (base y.id).val, (base first.id).val,
    (base second.id).val, old.val.toNat, new.val.toNat,
    (base (o.st.heap.field x (f := "items") rfl).id).val,
    (base (o.st.heap.field y (f := "items") rfl).id).val]
private def observeTarget : Option (List Nat) := do
  let m ← match run compiled.code machine with | .ok m _ => some m | _ => none
  [m.mem 3,m.mem 2,m.mem 1,m.mem 48,m.mem 49,m.mem 17,m.mem 25,m.mem 32,m.mem 40].mapM
    (fun w => match w with | .val n => some n.val | _ => none)

theorem source_observation : observeSource = some [48,32,40,40,32,11,13,16,24] := by decide +kernel
theorem target_observation : observeTarget = some [48,32,40,40,32,11,13,16,24] := by decide +kernel

theorem wrong_reference_field_refuted : ¬ Objects.HeapRepr hp base 8 (writeMachine machine 32 w[24]) := by
  intro h
  have he : w[24] = w[16] := h.refs h0 (f := "items") rfl
  exact (by decide +kernel : w[24] ≠ w[16]) he

/-- Nonempty reference-bearing struct construction needs the separate constructor API. -/
theorem reference_struct_construction_refused :
    (Compiler.compile (C := C) 1 (Frag.init Γ) (.cons
      (.declMem (.array (.ref holder)) (.user "fresh")
        (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil)).isNone = true := by decide +kernel

private def failing : Prog C Γ Γ := .cons (.rebindMem x (.alias (childPath 2 rfl))) .nil
private def failed := (Compiler.compile 1 (Frag.init Γ) failing).get (by decide +kernel)
attribute [irreducible] failed

theorem failed_input : failed.Input 1 8 base state machine :=
  (failed.object_input (by decide +kernel) 1 8 base state machine).mpr
    ⟨initial_repr, by decide +kernel⟩
theorem failed_agrees : failed.Agrees 1 8 base state machine := failed.correct failed_input

theorem source_bounds : failing.run state = .error .revert := by with_unfolding_all rfl
theorem target_bounds : run failed.code machine = .revert :=
  Out.eq_revert (by decide +kernel)

end Solidity.Evm.Memory.StructArrayInputExamples
