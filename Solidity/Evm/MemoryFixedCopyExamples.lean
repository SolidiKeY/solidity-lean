import Solidity.Evm.Compiler
import Solidity.Syntax.Splice

/-!
Initialized, inhabited fixed primitive-array inputs to the public compiler.
Both branches run the same compiled code. Root, member and mapping endpoints
are observed, along with a controlled post-copy mutation outside the new
read-only compiler route. No allocator or unproved separation is assumed.
-/
namespace Solidity.Evm.Memory.FixedCopyExamples
open Semantics

private def C : Contract := contract!{
  struct FixedHolder { uint[2] pair; }
  uint[2] pair;
  FixedHolder box;
  mapping(uint => uint[2]) pairs;
  uint[3] padded;
  uint[] dynamicPair;
  FixedHolder[2] references;
  uint[][] shapeRows;
}
private def holderName : Name := (C.structName? "FixedHolder").getD ""
private def H : HTy := [.fixed (.prim .uint) 2]
private def r0 : HRef H (.fixed (.prim .uint) 2) := ⟨0, rfl⟩
private def hp : Heap H := (⟨[indexValue (wmod 31), indexValue (wmod 47)], rfl⟩, ())
private def Γ : Ctx := [.val .bool, .mem (.fixed (.prim .uint) 2)]
private def state (flag : Bool) : State C Γ :=
  {storage := Storage.init C, H := H, heap := hp, env := (flag, some r0, ())}
private def bases : Nat → Fin W := fun _ => wmod 128
private def machine (flag : Bool) : Machine := {Machine.init with stack := [w[77]], mem := fun a =>
  if a = 2 then (Word.val (bword flag)) else if a = 1 then w[128]
  else if a = 128 then w[31] else if a = 129 then w[47] else w[0]}

private theorem noArray {p : PrimTy} (r : HRef H (.array (.prim p))) : False := by
  rcases r with ⟨i, hi⟩
  cases i with | zero => cases hi | succ i => cases hi
private theorem noStruct {s : Name} (r : HRef H (.struct s)) : False := by
  rcases r with ⟨i, hi⟩
  cases i with | zero => cases hi | succ i => cases hi
private theorem onlyFixed {p : PrimTy} {n : Nat} (r : HRef H (.fixed (.prim p) n)) :
    p = .uint ∧ n = 2 ∧ HEq r r0 := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi; exact ⟨rfl, rfl, HEq.rfl⟩
  | succ i => cases hi

private theorem initial_repr_at (L : Nat) (hpos : 1 ≤ L) (hL : L ≤ Lmax) (flag : Bool) : FixedStateRepr L 1 64 (Frag.init Γ) (state flag) bases (machine flag) := by
  have ha : HeapRepr hp bases 64 (machine flag) :=
    ⟨fun r => (noArray r).elim, fun r => (noArray r).elim, fun r => (noArray r).elim⟩
  have hs : StructHeapRepr hp bases 64 (machine flag) :=
    ⟨fun r => (noStruct r).elim, fun r => (noStruct r).elim, fun r => (noStruct r).elim⟩
  refine ⟨?_, ?_⟩
  · have hc := (Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl).mono (L' := L) hpos hL
    refine ⟨?_, ha, ?_, by decide, hs, fun _ r => (noStruct r).elim,
      RefFieldsRepr.withoutStructs _ _ _ (fun r => noStruct r)⟩
    · refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
      · intro p i
        cases i with | here => cases flag <;> rfl | there i => nomatch i
      · intro R i hi; nomatch i
      · intro R i hi; nomatch i
    · intro R i
      cases i with
      | there i => cases i with
        | here => exact ⟨r0, rfl, rfl⟩
        | there i => nomatch i
  · constructor
    · intro p n r
      rcases onlyFixed r with ⟨rfl, rfl, he⟩
      cases he
      refine ⟨by change 128 + 2 ≤ W; decide, ?_⟩
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
      decide +kernel

theorem initial_repr (flag : Bool) : FixedStateRepr 4 1 64 (Frag.init Γ) (state flag) bases (machine flag) :=
  initial_repr_at 4 (by decide) (by decide) flag

private def src : MPath C Γ (.ref (.fixed (.prim .uint) 2)) := .var (.there .here) rfl
private def root : Loc C Γ (.ref (.fixed (.prim .uint) 2)) := .root "pair" (by decide +kernel)
private def member : Loc C Γ (.ref (.fixed (.prim .uint) 2)) :=
  .field (.loc (.root (T := .ref (.struct holderName)) "box" (by decide +kernel))) "pair" (by decide +kernel)
private def mapped : Loc C Γ (.ref (.fixed (.prim .uint) 2)) :=
  .index (IndexTy.map (k := .uint)) (.loc (.root "pairs" (by decide +kernel))) (.simple (.lit 5 rfl))
private def readAt (dst : Loc C Γ (.ref (.fixed (.prim .uint) 2)))
    (i : Int) (hi : PrimTy.uint.inRange i = true) : Val C Γ .uint :=
  .read (.index (.arr .fixed) (.loc dst) (.simple (.lit i hi)))
private def eq (v : Val C Γ .uint) (n : Int) (hn : PrimTy.uint.inRange n = true) : Val C Γ .bool :=
  .binop .eqB rfl rfl v (.simple (.lit n hn))
private def program : Prog C Γ Γ :=
  .cons (.assignFromMem root src)
  (.cons (.ite (.simple (.local .here)) (.cons (.assignFromMem member src) .nil) .nil)
  (.cons (.block (.cons (.assign mapped (.copyMem src)) .nil))
  (.cons (.require (eq (readAt root 0 rfl) 31 rfl))
  (.cons (.require (eq (readAt root 1 rfl) 47 rfl))
  (.cons (.require (eq (readAt mapped 0 rfl) 31 rfl))
  (.cons (.require (eq (readAt mapped 1 rfl) 47 rfl)) .nil))))))
private def compiled : Compiler.Compilation 1 (Frag.init Γ) program :=
  (Compiler.compile 1 (Frag.init Γ) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem fixed_route : compiled.isFixedMemory = true ∧ compiled.usesMemory = true := by decide +kernel
theorem compiled_input (flag : Bool) : compiled.Input 4 64 bases (state flag) (machine flag) := by
  apply (compiled.fixed_input (by decide +kernel) 4 64 bases (state flag) (machine flag)).mpr
  refine ⟨initial_repr flag, ?_⟩
  rw [copyBoundProg_zero program (by decide +kernel)]
  exact Nat.zero_le _
theorem compiled_agrees (flag : Bool) : compiled.Agrees 4 64 bases (state flag) (machine flag) :=
  compiled.correct (compiled_input flag)

private def sourceObservation (flag : Bool) : Option (List Nat) := do
  let o ← (program.run (state flag)).toOption
  let pair := (o.st.storage.get (f := "pair") (T := .ref (.fixed (.prim .uint) 2)) (by decide +kernel)).view
  let box : SFields (structDef holderName) :=
    (o.st.storage.get (f := "box") (T := .ref (.struct holderName)) (by decide +kernel)).view
  let inside := (box.get (f := "pair") (T := .ref (.fixed (.prim .uint) 2)) (by decide +kernel)).view
  let mapping := (o.st.storage.get (f := "pairs")
    (T := .ref (.mapping .uint (.ref (.fixed (.prim .uint) 2)))) (by decide +kernel)).view
  let entry := ((lookupBy (5 : Int) mapping.1.hashed).getD mapping.2).view
  pure ((pair.toList ++ inside.toList ++ entry.toList).map (fun x => x.view.1.toNat))
private def targetObservation (flag : Bool) : Option (List Nat) := do
  let .ok m _ := run compiled.code (machine flag) | none
  let pair := rootSlot C "pair"
  let box := rootSlot C "box"
  let entry := Slot.hash (wmod 5) (rootSlot C "pairs") 0
  pure ([m.store pair, m.store (pair.add 1), m.store box, m.store (box.add 1),
    m.store entry, m.store (entry.add 1), m.store (rootSlot C "padded"),
    m.store (rootSlot C "dynamicPair"), (payloadWord (m.mem 128)).val,
    (payloadWord (m.mem 129)).val] ++ m.stack.map (fun x => (payloadWord x).val))

theorem source_false : sourceObservation false = some [31, 47, 0, 0, 31, 47] := by decide +kernel
theorem source_true : sourceObservation true = some [31, 47, 31, 47, 31, 47] := by decide +kernel
/-- info: some [31, 47, 0, 0, 31, 47, 0, 0, 31, 47, 77] -/
#guard_msgs in #eval targetObservation false
/-- info: some [31, 47, 31, 47, 31, 47, 0, 0, 31, 47, 77] -/
#guard_msgs in #eval targetObservation true

private def mutation : Prog C Γ Γ :=
  .cons (.assignMem (.index .fixed src (.simple (.lit 0 rfl))) (.val (.simple (.lit 99 rfl)))) .nil
/-- Heap mutation is not silently admitted without cross-layout ownership. -/
example : (Fixed.compileProg 1 (Frag.init Γ) (.cons (.block program) mutation)).isNone = true := by decide +kernel
private def sourceMutationObservation : Option (List Nat) := do
  let o ← ((Prog.cons (.block program) mutation).run (state true)).toOption
  let pair := (o.st.storage.get (f := "pair") (T := .ref (.fixed (.prim .uint) 2)) (by decide +kernel)).view
  let r := HRef.wk o.ext r0
  let first ← (o.st.heap.get r).val[0]?
  pure (pair.toList.map (fun x => x.view.1.toNat) ++ [first.val.toNat])
private def targetMutationObservation : Option (List Nat) := do
  let .ok m _ := run (compiled.code ++ [.push w[99], .push w[128], .mstoreAt]) (machine true) | none
  pure [m.store (rootSlot C "pair"), m.store ((rootSlot C "pair").add 1), (payloadWord (m.mem 128)).val]
theorem source_independent : sourceMutationObservation = some [31, 47, 99] := by decide +kernel
/-- info: some [31, 47, 99] -/
#guard_msgs in #eval targetMutationObservation

private def shapeProgram : Prog C Γ Γ :=
  .cons (.block program)
  (.cons (.assign (.root "padded" (by decide +kernel))
    (.fixedCopyMem src (.fixed 3 (by decide +kernel))))
  (.cons (.assign (.root "dynamicPair" (by decide +kernel))
    (.fixedCopyMem src (.dynamic (by decide +kernel)))) .nil))
private def shapeCompiled : Compiler.Compilation 1 (Frag.init Γ) shapeProgram :=
  (Compiler.compile 1 (Frag.init Γ) shapeProgram).get (by decide +kernel)
attribute [irreducible] shapeCompiled

theorem shape_input : shapeCompiled.Input 4 64 bases (state true) (machine true) := by
  apply (shapeCompiled.fixed_input (by decide +kernel) 4 64 bases (state true) (machine true)).mpr
  exact ⟨initial_repr true, by decide +kernel⟩
theorem shape_demand : copyBoundProg shapeProgram (state true) = 3 := by decide +kernel
/-- Successful copying needs the existing storage bound; it is not weakened. -/
theorem shape_bound_invalid : ¬ shapeCompiled.Input 1 64 bases (state true) (machine true) := by
  intro h
  have hb := ((shapeCompiled.fixed_input (by decide +kernel) 1 64 bases (state true) (machine true)).mp h).2
  rw [shape_demand] at hb
  omega

theorem shape_agrees : shapeCompiled.Agrees 4 64 bases (state true) (machine true) :=
  shapeCompiled.correct shape_input
private def shapeSourceObservation : Option (List Nat) := do
  let o ← (shapeProgram.run (state true)).toOption
  let pad := (o.st.storage.get (f := "padded") (T := .ref (.fixed (.prim .uint) 3)) (by decide +kernel)).view
  let dyn := (o.st.storage.get (f := "dynamicPair") (T := .ref (.array (.prim .uint))) (by decide +kernel)).view
  pure (pad.toList.map (fun x => x.view.1.toNat) ++ [dyn.n] ++ dyn.elems.toList.map (fun x => x.view.1.toNat))
private def shapeTargetObservation : Option (List Nat) := do
  let .ok m _ := run shapeCompiled.code (machine true) | none
  let pad := rootSlot C "padded"
  let dyn := rootSlot C "dynamicPair"
  pure [m.store pad, m.store (pad.add 1), m.store (pad.add 2), m.store dyn,
    m.store (.data dyn 0), m.store (.data dyn 1)]
theorem shape_source : shapeSourceObservation = some [31, 47, 0, 2, 31, 47] := by decide +kernel
/-- info: some [31, 47, 0, 2, 31, 47] -/
#guard_msgs in #eval shapeTargetObservation

private def failedDestination : Loc C Γ (.ref (.array (.prim .uint))) :=
  .index (.arr .dyn) (.loc (.root "shapeRows" (by decide +kernel))) (.simple (.lit 0 rfl))
private def failedProgram : Prog C Γ Γ :=
  .cons (.assign failedDestination (.fixedCopyMem src (.dynamic (by decide +kernel)))) .nil
private def failedCompiled : Compiler.Compilation 1 (Frag.init Γ) failedProgram :=
  (Compiler.compile 1 (Frag.init Γ) failedProgram).get (by decide +kernel)
attribute [irreducible] failedCompiled
/-- An unreachable payload does not impose the successful-copy length bound. -/
theorem failed_demand : copyBoundProg failedProgram (state true) = 0 := by decide +kernel
private theorem initial_repr_one : FixedStateRepr 1 1 64 (Frag.init Γ) (state true) bases (machine true) :=
  initial_repr_at 1 (by decide) (by decide) true
theorem failed_input : failedCompiled.Input 1 64 bases (state true) (machine true) := by
  apply (failedCompiled.fixed_input (by decide +kernel) 1 64 bases (state true) (machine true)).mpr
  exact ⟨initial_repr_one, by rw [failed_demand]; decide⟩
theorem failed_agrees : failedCompiled.Agrees 1 64 bases (state true) (machine true) :=
  failedCompiled.correct failed_input
example : (failedProgram.run (state true)).isOk = false := by decide +kernel
/-- info: true -/
#guard_msgs in #eval match run failedCompiled.code (machine true) with | .revert => true | _ => false

/-- The exact iterative dynamic copy clears the discarded old live tail. -/
private def recycledObservation : Option (List Nat) := do
  let dst := rootSlot C "dynamicPair"
  let st := WordStore.write (WordStore.write (WordStore.write (WordStore.write WordStore.zero dst 3) (.data dst 0) 8) (.data dst 1) 9) (.data dst 2) 88
  let m := {machine true with store := st}
  let .ok o _ := run (memoryFixedDynamicCode 2) ((m.push (.val (wmod 128))).push (.slot dst)) | none
  pure [o.store dst, o.store (.data dst 0), o.store (.data dst 1), o.store (.data dst 2),
    (payloadWord (o.mem 128)).val]
/-- info: some [2, 31, 47, 0, 31] -/
#guard_msgs in #eval recycledObservation

private def paddedOldObservation : Option (List Nat) := do
  let dst := rootSlot C "padded"
  let m := {machine true with store := WordStore.write WordStore.zero (dst.add 2) 88}
  let .ok o _ := run (memoryFixedPadCode 2 3) ((m.push (.val (wmod 128))).push (.slot dst)) | none
  pure [o.store dst, o.store (dst.add 1), o.store (dst.add 2)]
/-- info: some [31, 47, 0] -/
#guard_msgs in #eval paddedOldObservation

private def badΓ : Ctx := [.mem (.fixed (.ref (.struct holderName)) 2)]
private def bad : Prog C badΓ badΓ :=
  .cons (.assignFromMem (.root "references" (by decide +kernel)) (.var .here (by decide +kernel))) .nil
/-- Fixed reference-element arrays remain refused from initialized paths. -/
example : (Compiler.compile 1 (Frag.init badΓ) bad).isNone = true := by decide +kernel

end Solidity.Evm.Memory.FixedCopyExamples
