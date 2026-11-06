import Solidity.Evm.Compiler
import Solidity.Syntax.Splice

/-! One inhabited public fixed-memory input contains all three copy families. -/
namespace Solidity.Evm.Memory.FixedMixedExamples
open Semantics
private def C : Contract := contract!{
  struct Record { uint n; }
  uint[2] fixedValues;
  uint[] values;
  Record stored;
}
private def name : Name := (C.structName? "Record").getD ""
private def H : HTy := [.fixed (.prim .uint) 2, .array (.prim .uint), .struct name]
private def r0 : HRef H (.fixed (.prim .uint) 2) := ⟨0, rfl⟩
private def r1 : HRef H (.array (.prim .uint)) := ⟨1, rfl⟩
private def r2 : HRef H (.struct name) := ⟨2, rfl⟩
private def hp : Heap H := (⟨[indexValue (wmod 31), indexValue (wmod 47)], rfl⟩,
  ⟨[indexValue (wmod 91), indexValue (wmod 92)], by decide⟩, (indexValue (wmod 77), ()), ())
private def Γ : Ctx := [.mem (.fixed (.prim .uint) 2), .mem (.array (.prim .uint)), .mem (.struct name)]
private def state : State C Γ :=
  {storage := Storage.init C, H := H, heap := hp, env := (some r0, some r1, some r2, ())}
private def bases (i : Nat) : Fin W := if i = 0 then wmod 128 else if i = 1 then wmod 160 else wmod 192
private def machine : Machine := {Machine.init with stack := [w[55]], mem := fun a =>
  if a = 3 then w[128] else if a = 2 then w[160] else if a = 1 then w[192]
  else if a = 128 then w[31] else if a = 129 then w[47]
  else if a = 160 then w[2] else if a = 161 then w[91] else if a = 162 then w[92]
  else if a = 192 then w[77] else w[0]}
private theorem onlyFixed {p : PrimTy} {n : Nat} (r : HRef H (.fixed (.prim p) n)) :
    p = .uint ∧ n = 2 ∧ HEq r r0 := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi; exact ⟨rfl, rfl, HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases i with | zero => cases hi | succ i => cases hi
private theorem onlyArray {p : PrimTy} (r : HRef H (.array (.prim p))) : p = .uint ∧ HEq r r1 := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi; exact ⟨rfl, HEq.rfl⟩
    | succ i => cases i with | zero => cases hi | succ i => cases hi
private theorem onlyStruct {s : Name} (r : HRef H (.struct s)) : s = name ∧ HEq r r2 := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases i with
      | zero => cases hi; exact ⟨rfl, HEq.rfl⟩
      | succ i => cases hi

theorem initial_repr : FixedStateRepr 4 1 64 (Frag.init Γ) state bases machine := by
  have ha : HeapRepr hp bases 64 machine := by
    constructor
    · intro p r
      rcases onlyArray r with ⟨rfl, he⟩
      cases he
      refine ⟨by decide +kernel, by decide +kernel, ?_⟩
      intro i v hv
      rw [MObj.elems_dyn] at hv
      cases i with
      | zero => cases hv; exact ReprV.uint_of rfl
      | succ i => cases i with
        | zero => cases hv; exact ReprV.uint_of rfl
        | succ i => cases hv
    · intro p r
      rcases onlyArray r with ⟨rfl, he⟩
      cases he
      change 64 ≤ 160
      decide
    · intro p q r s hn
      rcases onlyArray r with ⟨rfl, hr⟩
      rcases onlyArray s with ⟨rfl, hs⟩
      cases hr; cases hs
      exact (hn rfl).elim
  have hs : StructHeapRepr hp bases 64 machine := by
    constructor
    · intro s r
      rcases onlyStruct r with ⟨rfl, he⟩
      cases he
      refine ⟨by decide, ?_⟩
      intro f p hf
      change lookupBy f [("n", Ty.prim .uint)] = some (Ty.prim p) at hf
      simp only [lookupBy] at hf
      split at hf
      · rename_i he
        subst f
        cases hf
        exact ReprV.uint_of rfl
      · cases hf
    · intro s r
      rcases onlyStruct r with ⟨rfl, he⟩
      cases he
      change 64 ≤ 192
      decide
    · intro s t r q hn
      rcases onlyStruct r with ⟨rfl, hr⟩
      rcases onlyStruct q with ⟨rfl, hq⟩
      cases hr; cases hq
      exact (hn rfl).elim
  refine ⟨?_, ?_⟩
  · have hc := (Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl).mono (L' := 4) (by decide) (by decide)
    refine ⟨?_, ha, ?_, by decide, hs, ?_, ?_⟩
    · refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
      · intro p i; nomatch i
      · intro R i hi; nomatch i
      · intro R i hi; nomatch i
    · intro R i
      cases i with
      | here => exact ⟨r0, rfl, rfl⟩
      | there i => cases i with
        | here => exact ⟨r1, rfl, rfl⟩
        | there i => cases i with
          | here => exact ⟨r2, rfl, rfl⟩
          | there i => nomatch i
    · intro p s a r
      rcases onlyArray a with ⟨rfl, ha⟩
      rcases onlyStruct r with ⟨rfl, hr⟩
      cases ha; cases hr
      exact Or.inl (by decide +kernel)
    · intro s f R r hf
      rcases onlyStruct r with ⟨rfl, he⟩
      cases he
      change lookupBy f [("n", Ty.prim .uint)] = some (Ty.ref R) at hf
      simp only [lookupBy] at hf
      split at hf <;> cases hf
  · constructor
    · intro p n r
      rcases onlyFixed r with ⟨rfl, rfl, he⟩
      cases he
      refine ⟨by decide, ?_⟩
      intro i v hv
      cases i with
      | zero => cases hv; exact ReprV.uint_of rfl
      | succ i => cases i with
        | zero => cases hv; exact ReprV.uint_of rfl
        | succ i => cases hv
    · intro p n r
      rcases onlyFixed r with ⟨rfl, rfl, he⟩
      cases he
      change 64 ≤ 128
      decide

private def program : Prog C Γ Γ :=
  .cons (.assignFromMem (.root "fixedValues" (by decide +kernel)) (.var .here rfl))
  (.cons (.assignFromMem (.root "values" (by decide +kernel)) (.var (.there .here) rfl))
  (.cons (.assignFromMem (.root "stored" (by decide +kernel)) (.var (.there (.there .here)) rfl)) .nil))
private def compiled : Compiler.Compilation 1 (Frag.init Γ) program :=
  (Compiler.compile 1 (Frag.init Γ) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem fixed_route : compiled.isFixedMemory = true := by decide +kernel
theorem compiled_input : compiled.Input 4 64 bases state machine := by
  apply (compiled.fixed_input fixed_route 4 64 bases state machine).mpr
  exact ⟨initial_repr, by decide +kernel⟩
theorem compiled_agrees : compiled.Agrees 4 64 bases state machine := compiled.correct compiled_input
private def sourceObservation : Option (List Nat) := do
  let o ← (program.run state).toOption
  let fixed := (o.st.storage.get (f := "fixedValues") (T := .ref (.fixed (.prim .uint) 2)) (by decide +kernel)).view
  let dyn := (o.st.storage.get (f := "values") (T := .ref (.array (.prim .uint))) (by decide +kernel)).view
  let record : SFields (structDef name) := (o.st.storage.get (f := "stored") (T := .ref (.struct name)) (by decide +kernel)).view
  pure (fixed.toList.map (fun x => x.view.1.toNat) ++ [dyn.n] ++
    dyn.elems.toList.map (fun x => x.view.1.toNat) ++
    [(record.get (f := "n") (T := .prim .uint) (by decide +kernel)).view.1.toNat])
private def targetObservation : Option (List Nat) := do
  let .ok m _ := run compiled.code machine | none
  let fixed := rootSlot C "fixedValues"
  let dyn := rootSlot C "values"
  pure [m.store fixed, m.store (fixed.add 1), m.store dyn, m.store (.data dyn 0),
    m.store (.data dyn 1), m.store (rootSlot C "stored"), (payloadWord (m.mem 128)).val,
    (payloadWord (m.mem 161)).val, (payloadWord (m.mem 192)).val]
theorem source_observation : sourceObservation = some [31, 47, 2, 91, 92, 77] := by decide +kernel
/-- info: some [31, 47, 2, 91, 92, 77, 31, 91, 77] -/
#guard_msgs in #eval targetObservation

end Solidity.Evm.Memory.FixedMixedExamples
