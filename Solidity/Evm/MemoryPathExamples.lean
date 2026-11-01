import Solidity.Evm.Compiler

/-! Populated reference fields exercise nested pointer reads and aliases through
the public compiler. The inputs include actual separated child objects and
pointer words, rather than assuming an arbitrary source/target relation. -/
namespace Solidity.Evm.Memory.PathExamples
open Semantics

private def C : Contract := contract!{
  struct Leaf { uint n; bool flag; }
  struct Holder { Leaf leaf; uint[] items; bool marker; }
  struct Wrapper { Holder holder; uint own; }
}
private def leafName : Name := (C.structName? "Leaf").getD ""
private def holderName : Name := (C.structName? "Holder").getD ""
private def wrapperName : Name := (C.structName? "Wrapper").getD ""
private def H : HTy := [.struct leafName, .array (.prim .uint), .struct holderName, .struct wrapperName]
private def leaf : HRef H (.struct leafName) := ⟨0, rfl⟩
private def arr : HRef H (.array (.prim .uint)) := ⟨1, rfl⟩
private def holder : HRef H (.struct holderName) := ⟨2, rfl⟩
private def wrapper : HRef H (.struct wrapperName) := ⟨3, rfl⟩
private def u (n : Nat) : PrimTy.uint.Denote := indexValue (wmod n)
private def hp : Heap H :=
  ((u 7, (true, ())), (⟨[u 4, u 5], by decide⟩,
    ((leaf, (arr, (false, ()))), ((holder, (u 99, ())), ()))))
private def base (i : Nat) : Fin W :=
  if i = 0 then wmod 32 else if i = 1 then wmod 40 else if i = 2 then wmod 48 else wmod 56
private def machine : Machine :=
  {Machine.init with stack := [w[77]], mem := fun a =>
    if a < 64 then
      if a = 0 then w[64] else if a = 1 then w[56] else if a = 15 then w[88]
      else if a = 32 then w[7] else if a = 33 then w[1]
      else if a = 40 then w[2] else if a = 41 then w[4] else if a = 42 then w[5]
      else if a = 48 then w[32] else if a = 49 then w[40]
      else if a = 56 then w[48] else if a = 57 then w[99] else w[0]
    else w[0]}
private def Γ : Ctx := [.mem (.struct wrapperName)]
private def state : State C Γ :=
  {storage := Storage.init C, H := H, heap := hp, env := (some wrapper, ())}

private theorem structRefs {s : Name} (r : HRef H (.struct s)) :
    (s = leafName ∧ HEq r leaf) ∨ (s = holderName ∧ HEq r holder) ∨
      (s = wrapperName ∧ HEq r wrapper) := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi; exact .inl ⟨rfl, HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases i with
      | zero => cases hi; exact .inr (.inl ⟨rfl, HEq.rfl⟩)
      | succ i => cases i with
        | zero => cases hi; exact .inr (.inr ⟨rfl, HEq.rfl⟩)
        | succ i => cases hi

private theorem arrayRefs {p : PrimTy} (r : HRef H (.array (.prim p))) :
    p = .uint ∧ HEq r arr := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi; exact ⟨rfl, HEq.rfl⟩
    | succ i => cases i with
      | zero => cases hi
      | succ i => cases i with
        | zero => cases hi
        | succ i => cases hi

private theorem leaf_repr : StructRepr hp leaf (base leaf.id) machine := by
  refine ⟨by decide +kernel, ?_⟩
  intro f p hf
  change lookupBy f [("n", Ty.uint), ("flag", Ty.bool)] = some (.prim p) at hf
  by_cases hn : f = "n"
  · subst f; cases hf; exact ReprV.uint_of rfl
  · by_cases hb : f = "flag"
    · subst f; cases hf; rfl
    · simp only [lookupBy, hn, hb, if_false, reduceCtorEq] at hf

private theorem holder_repr : StructRepr hp holder (base holder.id) machine := by
  refine ⟨by decide +kernel, ?_⟩
  intro f p hf
  change lookupBy f [("leaf", .ref (.struct leafName)), ("items", .ref (.array (.prim .uint))),
    ("marker", Ty.bool)] = some (.prim p) at hf
  by_cases hl : f = "leaf"
  · subst f; cases hf
  · by_cases hi : f = "items"
    · subst f; simp only [lookupBy, hl, if_false, if_true] at hf; cases hf
    · by_cases hm : f = "marker"
      · subst f; simp only [lookupBy, hl, hi, if_false, if_true] at hf; cases hf; rfl
      · simp only [lookupBy, hl, hi, hm, if_false, reduceCtorEq] at hf

private theorem wrapper_repr : StructRepr hp wrapper (base wrapper.id) machine := by
  refine ⟨by decide +kernel, ?_⟩
  intro f p hf
  change lookupBy f [("holder", .ref (.struct holderName)), ("own", Ty.uint)] = some (.prim p) at hf
  by_cases hh : f = "holder"
  · subst f; cases hf
  · by_cases ho : f = "own"
    · subst f; simp only [lookupBy, hh, if_false, if_true] at hf; cases hf; exact ReprV.uint_of rfl
    · simp only [lookupBy, hh, ho, if_false, reduceCtorEq] at hf

private theorem structs_repr : StructHeapRepr hp base 16 machine := by
  refine ⟨?_, ?_, ?_⟩
  · intro s r
    rcases structRefs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr
    · exact leaf_repr
    · exact holder_repr
    · exact wrapper_repr
  · intro s r
    rcases structRefs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr <;> decide +kernel
  · intro s t r q hn
    rcases structRefs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr
      <;> rcases structRefs q with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩ <;> cases hq
      <;> first | exact (hn rfl).elim | decide +kernel

private theorem arrays_repr : HeapRepr hp base 16 machine := by
  refine ⟨?_, ?_, ?_⟩
  · intro p a
    obtain ⟨rfl, ha⟩ := arrayRefs a
    cases ha
    refine ⟨by decide +kernel, by decide +kernel, ?_⟩
    intro i v hv
    rw [MObj.elems_dyn] at hv
    change [u 4, u 5][i]? = some v at hv
    cases i with
    | zero => cases hv; exact ReprV.uint_of rfl
    | succ i => cases i with
      | zero => cases hv; exact ReprV.uint_of rfl
      | succ i => cases hv
  · intro p a
    obtain ⟨rfl, ha⟩ := arrayRefs a
    cases ha
    decide +kernel
  · intro p q a b hn
    obtain ⟨rfl, ha⟩ := arrayRefs a
    obtain ⟨rfl, hb⟩ := arrayRefs b
    cases ha
    cases hb
    exact (hn rfl).elim

private theorem separated : StructArraySeparated hp base := by
  intro p s a r
  obtain ⟨rfl, ha⟩ := arrayRefs a
  cases ha
  rcases structRefs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr <;> decide +kernel

theorem reference_words : RefFieldsRepr hp base machine := by
  intro s f R r hf
  rcases structRefs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr
  · exact (primitiveMembers_noRef (by decide) hf).elim
  · change lookupBy f [("leaf", .ref (.struct leafName)), ("items", .ref (.array (.prim .uint))),
      ("marker", Ty.bool)] = some (.ref R) at hf
    by_cases hl : f = "leaf"
    · subst f; cases hf; rfl
    · by_cases hi : f = "items"
      · subst f; simp only [lookupBy, hl, if_false, if_true] at hf; cases hf; rfl
      · by_cases hm : f = "marker"
        · subst f; simp only [lookupBy, hl, hi, if_false, if_true] at hf; cases hf
        · simp only [lookupBy, hl, hi, hm, if_false, reduceCtorEq] at hf
  · change lookupBy f [("holder", .ref (.struct holderName)), ("own", Ty.uint)] = some (.ref R) at hf
    by_cases hh : f = "holder"
    · subst f; cases hf; rfl
    · by_cases ho : f = "own"
      · subst f; simp only [lookupBy, hh, if_false, if_true] at hf; cases hf
      · simp only [lookupBy, hh, ho, if_false, reduceCtorEq] at hf

theorem fixture : StateRepr 1 1 16 (Frag.init Γ) state base machine ∧
    StructAllocatorRepr hp base 16 (wmod 64) machine := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
  refine ⟨⟨?_, arrays_repr, ?_, by decide, structs_repr, separated, reference_words⟩,
    ⟨⟨arrays_repr, ?_, ?_⟩, structs_repr, separated, ?_⟩⟩
  · refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
    · intro p i; cases i with | there i => nomatch i
    · intro R i; cases i with | there i => nomatch i
    · intro R i; cases i with | there i => nomatch i
  · intro R i
    cases i with
    | here => exact ⟨wrapper, rfl, rfl⟩
    | there i => nomatch i
  · refine ⟨by decide, by decide, rfl, ?_⟩
    intro a ha
    simp only [machine, show ¬ a < 64 by change 64 ≤ a at ha; omega, if_false]
  · intro p a
    obtain ⟨rfl, ha⟩ := arrayRefs a
    cases ha
    decide +kernel
  · intro s r
    rcases structRefs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr <;> decide +kernel

theorem wrong_pointer_refuted : ¬ RefFieldsRepr hp base (writeMachine machine 48 w[40]) := by
  intro h
  have he : w[40] = w[32] := h holder (f := "leaf") rfl
  have hn : w[40] ≠ w[32] := by decide +kernel
  exact hn he

private def holderPath {Δ : Ctx} (i : Idx Δ (.mem (.struct wrapperName))) :
    MPath C Δ (.ref (.struct holderName)) := .loc (.field (.var i rfl) "holder" rfl)
private def leafPath {Δ : Ctx} (i : Idx Δ (.mem (.struct wrapperName))) :
    MPath C Δ (.ref (.struct leafName)) := .loc (.field (holderPath i) "leaf" rfl)
private def itemsPath {Δ : Ctx} (i : Idx Δ (.mem (.struct wrapperName))) :
    MPath C Δ (.ref (.array (.prim .uint))) := .loc (.field (holderPath i) "items" rfl)
private def nestedN {Δ : Ctx} (i : Idx Δ (.mem (.struct wrapperName))) : Val C Δ .uint :=
  .readMem (.field (leafPath i) "n" rfl)
private def lit {Δ : Ctx} (n : Int) (hn : PrimTy.uint.inRange n = true) : Val C Δ .uint :=
  .simple (.lit n hn)
private def eqN {Δ : Ctx} (v : Val C Δ .uint) (n : Int) (hn : PrimTy.uint.inRange n = true) :
    Val C Δ .bool := .binop .eqB rfl rfl v (lit n hn)
private def Δ : Ctx := [.mem (.struct leafName), .mem (.array (.prim .uint))] ++ Γ
private def root : Idx Δ (.mem (.struct wrapperName)) := .there (.there .here)

private def scopedBody : Prog C Δ (.mem (.array (.prim .bool)) :: .mem (.struct holderName) :: Δ) :=
  .cons (.declMem (.struct holderName) (.user "h") (some (.alias (holderPath root))) rfl rfl)
  (.cons (.assignMem (.field (.var .here rfl) "marker" rfl) (.val (.simple (.bool true))))
  (.cons (.declMem (.array (.prim .bool)) (.user "fresh") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl)
  (.cons (.require (eqN (nestedN (.there (.there root))) 17 rfl))
  (.cons (.require (eqN (.mlen (itemsPath (.there (.there root))) rfl) 2 rfl)) .nil))))

private def program : Prog C Γ (.mem (.struct leafName) :: Δ) :=
  .cons (.declMem (.array (.prim .uint)) (.user "xs") (some (.alias (itemsPath .here))) rfl rfl)
  (.cons (.declMem (.struct leafName) (.user "l") (some (.alias (leafPath (.there .here)))) rfl rfl)
  (.cons (.assignMem (.field (.var .here rfl) "n" rfl) (.val (lit 17 rfl)))
  (.cons (.assignMem (.index .dyn (.var (.there .here) rfl) (lit 1 rfl)) (.val (nestedN root)))
  (.cons (.rebindMem .here (.alias (leafPath root)))
  (.cons (.block scopedBody)
  (.cons (.declMem (.struct leafName) (.user "newLeaf") none rfl rfl)
  (.cons (.require (eqN (nestedN (.there root)) 17 rfl))
  (.cons (.require (eqN (.readMem (.index .dyn (itemsPath (.there root)) (lit 1 rfl))) 17 rfl))
  (.cons (.rebindMem .here (.alias (leafPath (.there root))))
  (.cons (.assignMem (.field (.var .here rfl) "n" rfl) (.val (lit 22 rfl)))
  (.cons (.require (eqN (nestedN (.there root)) 22 rfl)) .nil)))))))))))

private def compiled : Compiler.Compilation 1 (Frag.init Γ) program :=
  (Compiler.compile 1 (Frag.init Γ) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem program_cost : allocationCostProg program state = 4 := by decide +kernel

theorem compiled_input : compiled.Input 1 16 base state machine := by
  apply (compiled.memory_input (by decide +kernel) 1 16 base state machine).mpr
  exact ⟨fixture.1, by decide +kernel,
    .inr ⟨by decide, wmod 64, fixture.2, by decide +kernel⟩⟩

theorem compiled_agrees : compiled.Agrees 1 16 base state machine := compiled.correct compiled_input

private def observeTarget : Out → Option (List Nat)
  | .ok m _ => do
    let words := m.stack ++ [m.mem 0, m.mem 15, m.mem 1, m.mem 2, m.mem 3, m.mem 4,
      m.mem 32, m.mem 33, m.mem 40, m.mem 41, m.mem 42, m.mem 48, m.mem 49,
      m.mem 50, m.mem 56, m.mem 57, m.mem 64, m.mem 65, m.mem 66, m.mem 67]
    words.mapM fun w => match w with | .val v => some v.val | .slot _ => none
  | _ => none

theorem target_observation : observeTarget (run compiled.code machine) =
    some [77, 68, 88, 56, 40, 32, 32, 22, 1, 2, 4, 17, 32, 40, 1, 48, 99, 1, 0, 0, 0] := by
  decide +kernel

private def refAt? (H : HTy) (i : Nat) (R : RefTy) : Option (HRef H R) :=
  if h : H[i]? = some R then some ⟨i, h⟩ else none
private def observeSource {Ω : Ctx} : TRes (Solidity.Out C H Ω) → Option (List Int)
  | .ok o => do
    let l ← refAt? o.st.H 0 (.struct leafName)
    let a ← refAt? o.st.H 1 (.array (.prim .uint))
    let h ← refAt? o.st.H 2 (.struct holderName)
    let w ← refAt? o.st.H 3 (.struct wrapperName)
    let b ← refAt? o.st.H 4 (.array (.prim .bool))
    let fresh ← refAt? o.st.H 5 (.struct leafName)
    let x ← o.st.heap.index a .dyn (indexValue (wmod 1))
    let marker : Bool := o.st.heap.field h (f := "marker") rfl
    some [(o.st.heap.field l (f := "n") rfl).1, x.1, if marker then 1 else 0,
      (o.st.heap.field w (f := "own") rfl).1, o.st.heap.len b .dyn,
      (o.st.heap.field fresh (f := "n") rfl).1]
  | .error _ => none

theorem source_observation : observeSource (program.run state) = some [22, 17, 1, 99, 1, 0] := by
  decide +kernel

private def bad : Prog C Γ (.val .uint :: Γ) :=
  .cons (.declLocal .uint (.user "bad")
    (some (.readMem (.index .dyn (itemsPath .here) (lit 9 rfl))))) .nil
private def badCompilation : Compiler.Compilation 1 (Frag.init Γ) bad :=
  (Compiler.compile 1 (Frag.init Γ) bad).get (by decide +kernel)
attribute [irreducible] badCompilation

theorem bad_input : badCompilation.Input 1 16 base state machine := by
  apply (badCompilation.memory_input (by decide +kernel) 1 16 base state machine).mpr
  exact ⟨fixture.1, by decide +kernel, .inl (by decide +kernel)⟩

theorem bad_agrees : badCompilation.Agrees 1 16 base state machine := badCompilation.correct bad_input

private def reverted : Out → Bool | .revert => true | _ => false
theorem bad_reverts : bad.run state = .error .revert ∧ reverted (run badCompilation.code machine) = true := by
  constructor
  · with_unfolding_all rfl
  · decide +kernel

namespace Direct

private def Δ : Ctx := .val .uint :: Γ
private def root : Idx Δ (.mem (.struct wrapperName)) := .there .here
private def nLoc : MLoc C Δ (.prim .uint) := .field (leafPath root) "n" rfl
private def nOp : OpLoc C Δ .uint := .mfield (leafPath root) "n" rfl
private def aOp : OpLoc C Δ .uint := .mindex .dyn (itemsPath root) (.lit 0 rfl)
private def saved (n : Int) (hn : PrimTy.uint.inRange n = true) : Stmt C Δ Δ :=
  .require (eqN (.simple (.local .here)) n hn)
private def steps : List (Stmt C Δ Δ) := [
  .assignMem nLoc (.val (lit 10 rfl)),
  .incDec .postInc rfl nOp, .incDec .preInc rfl nOp,
  .incDec .postDec rfl nOp, .incDec .preDec rfl nOp,
  .opAssign .add rfl rfl nOp (lit 2 rfl),
  .opAssign .mul rfl rfl nOp (lit 3 rfl),
  .opAssign .sub rfl rfl nOp (lit 6 rfl),
  .opAssign .div rfl rfl nOp (lit 5 rfl),
  .opAssign .mod rfl rfl nOp (lit 4 rfl),
  .assignMem (.index .dyn (itemsPath root) (lit 0 rfl)) (.val (nestedN root)),
  .opAssign .add rfl rfl aOp (lit 3 rfl),
  .opAssign .mul rfl rfl aOp (lit 4 rfl),
  .opAssign .sub rfl rfl aOp (lit 2 rfl),
  .opAssign .div rfl rfl aOp (lit 3 rfl),
  .opAssign .mod rfl rfl aOp (lit 4 rfl),
  .incDec .postInc rfl aOp, .incDec .preInc rfl aOp,
  .incDec .postDec rfl aOp, .incDec .preDec rfl aOp,
  .assignLocal .here (.readMem (.index .dyn (itemsPath root) (lit 0 rfl))), saved 2 rfl,
  .deleteMem (.loc (.index .dyn (itemsPath root) (lit 1 rfl))) rfl,
  .deleteMem (.loc (.field (leafPath root) "flag" rfl)) rfl,
  .deleteMem (.loc nLoc) rfl,
  .block (.cons (.declMem (.array (.prim .bool)) (.user "fresh")
    (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil),
  .require (eqN (nestedN root) 0 rfl),
  .require (eqN (.readMem (.index .dyn (itemsPath root) (lit 0 rfl))) 2 rfl)]

private def body : Prog C Δ Δ := steps.foldr (fun s p => .cons s p) .nil
private def program : Prog C Γ Δ :=
  .cons (.declLocal .uint (.user "saved") (some (lit 0 rfl))) body
private def compiled : Compiler.Compilation 1 (Frag.init Γ) program :=
  (Compiler.compile 1 (Frag.init Γ) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem program_cost : allocationCostProg program state = 2 := by decide +kernel

theorem compiled_input : compiled.Input 1 16 base state machine := by
  apply (compiled.memory_input (by decide +kernel) 1 16 base state machine).mpr
  exact ⟨fixture.1, by decide +kernel,
    .inr ⟨by decide, wmod 64, fixture.2, by decide +kernel⟩⟩

theorem compiled_agrees : compiled.Agrees 1 16 base state machine := compiled.correct compiled_input

private def observeTarget : Out → Option (List Nat)
  | .ok m _ => do
    let words := m.stack ++ [m.mem 0, m.mem 15, m.mem 1, m.mem 2,
      m.mem 32, m.mem 33, m.mem 40, m.mem 41, m.mem 42, m.mem 48, m.mem 49,
      m.mem 50, m.mem 56, m.mem 57, m.mem 64, m.mem 65]
    words.mapM fun w => match w with | .val v => some v.val | .slot _ => none
  | _ => none

theorem target_observation : observeTarget (run compiled.code machine) =
    some [77, 66, 88, 56, 2, 0, 0, 2, 2, 0, 32, 40, 0, 48, 99, 1, 0] := by decide +kernel

private def observeSource {Ω : Ctx} : TRes (Solidity.Out C H Ω) → Option (List Int)
  | .ok o => do
    let l ← refAt? o.st.H 0 (.struct leafName)
    let a ← refAt? o.st.H 1 (.array (.prim .uint))
    let b ← refAt? o.st.H 4 (.array (.prim .bool))
    let x ← o.st.heap.index a .dyn (indexValue (wmod 0))
    let y ← o.st.heap.index a .dyn (indexValue (wmod 1))
    let flag : Bool := o.st.heap.field l (f := "flag") rfl
    some [(o.st.heap.field l (f := "n") rfl).1, if flag then 1 else 0, x.1, y.1, o.st.heap.len b .dyn]
  | .error _ => none

theorem source_observation : observeSource (program.run state) = some [0, 0, 2, 0, 1] := by decide +kernel

private def failure (k : Fin 3) : Prog C Γ Γ :=
  if k.val = 0 then
    .cons (.assignMem (.index .dyn (itemsPath .here) (lit 9 rfl)) (.val (lit 12 rfl))) .nil
  else if k.val = 1 then
    .cons (.assignMem (.field (leafPath .here) "n" rfl)
      (.val (lit (W - 1) (by decide +kernel))))
    (.cons (.incDec .preInc rfl (.mfield (leafPath .here) "n" rfl)) .nil)
  else
    .cons (.assignMem (.index .dyn (itemsPath .here) (lit 0 rfl))
      (.val (.binop .div rfl rfl (lit 1 rfl) (lit 0 rfl)))) .nil

private def failureCompilation (k : Fin 3) : Compiler.Compilation 1 (Frag.init Γ) (failure k) :=
  (Compiler.compile 1 (Frag.init Γ) (failure k)).get (by
    have h : ∀ k : Fin 3, (Compiler.compile 1 (Frag.init Γ) (failure k)).isSome = true := by decide +kernel
    exact h k)
attribute [irreducible] failureCompilation

theorem failure_inputs (k : Fin 3) : (failureCompilation k).Input 1 16 base state machine := by
  have hd : ∀ k : Fin 3, (failureCompilation k).isMemory = true := by decide +kernel
  have hc : ∀ k : Fin 3, 1 + frameNeedProg (failure k) ≤ 16 := by decide +kernel
  have hz : ∀ k : Fin 3, allocationCostProg (failure k) state = 0 := by decide +kernel
  apply ((failureCompilation k).memory_input (hd k) 1 16 base state machine).mpr
  exact ⟨fixture.1, hc k, .inl (hz k)⟩

theorem failure_agrees (k : Fin 3) : (failureCompilation k).Agrees 1 16 base state machine :=
  (failureCompilation k).correct (failure_inputs k)

private def sourceReverted {Ω : Ctx} : TRes (Solidity.Out C H Ω) → Bool
  | .error .revert => true
  | _ => false

theorem failures_revert : ∀ k : Fin 3, sourceReverted ((failure k).run state) = true ∧
    reverted (run (failureCompilation k).code machine) = true := by decide +kernel

end Direct

namespace ReferenceWrite

private def Δ : Ctx := [.mem (.array (.prim .uint)), .mem (.struct leafName),
  .mem (.array (.prim .uint)), .mem (.struct leafName)] ++ Γ
private def root : Idx Δ (.mem (.struct wrapperName)) := .there (.there (.there (.there .here)))
private def newLeaf : Idx Δ (.mem (.struct leafName)) := .there .here
private def oldLeaf : Idx Δ (.mem (.struct leafName)) := .there (.there (.there .here))
private def newArray : Idx Δ (.mem (.array (.prim .uint))) := .here
private def oldArray : Idx Δ (.mem (.array (.prim .uint))) := .there (.there .here)
private def steps : List (Stmt C Δ Δ) := [
  .assignMem (.field (.var newLeaf rfl) "n" rfl) (.val (lit 23 rfl)),
  .assignMem (.index .dyn (.var newArray rfl) (lit 0 rfl)) (.val (lit 41 rfl)),
  .assignMem (.index .dyn (.var newArray rfl) (lit 1 rfl)) (.val (lit 43 rfl)),
  .assignMem (.field (holderPath root) "leaf" rfl) (.ref (.var newLeaf rfl)),
  .assignMem (.field (leafPath root) "n" rfl) (.val (lit 31 rfl)),
  .assignMem (.field (holderPath root) "items" rfl) (.ref (.var newArray rfl)),
  .assignMem (.index .dyn (itemsPath root) (lit 1 rfl)) (.val (lit 45 rfl)),
  .assignMem (.field (holderPath root) "leaf" rfl) (.ref (leafPath root)),
  .require (eqN (nestedN root) 31 rfl),
  .require (eqN (.readMem (.field (.var oldLeaf rfl) "n" rfl)) 7 rfl),
  .require (eqN (.readMem (.index .dyn (.var oldArray rfl) (lit 1 rfl))) 5 rfl),
  .assignMem (.field (holderPath root) "leaf" rfl) (.ref (.var oldLeaf rfl)),
  .assignMem (.field (holderPath root) "items" rfl) (.ref (.var oldArray rfl)),
  .assignMem (.index .dyn (itemsPath root) (lit 0 rfl)) (.val (lit 9 rfl)),
  .block (.cons (.declMem (.array (.prim .bool)) (.user "fresh")
    (some (.newArr (.lit 0 rfl) rfl)) rfl rfl) .nil),
  .require (eqN (nestedN root) 7 rfl),
  .require (eqN (.readMem (.field (.var newLeaf rfl) "n" rfl)) 31 rfl),
  .require (eqN (.readMem (.index .dyn (.var newArray rfl) (lit 1 rfl))) 45 rfl),
  .require (eqN (.readMem (.index .dyn (.var oldArray rfl) (lit 0 rfl))) 9 rfl)]
private def body : Prog C Δ Δ := steps.foldr (fun s p => .cons s p) .nil
private def program : Prog C Γ Δ :=
  .cons (.declMem (.struct leafName) (.user "oldLeaf") (some (.alias (leafPath .here))) rfl rfl)
  (.cons (.declMem (.array (.prim .uint)) (.user "oldArray")
    (some (.alias (itemsPath (.there .here)))) rfl rfl)
  (.cons (.declMem (.struct leafName) (.user "newLeaf") none rfl rfl)
  (.cons (.declMem (.array (.prim .uint)) (.user "newArray")
    (some (.newArr (.lit 2 rfl) rfl)) rfl rfl) body)))
private def compiled : Compiler.Compilation 1 (Frag.init Γ) program :=
  (Compiler.compile 1 (Frag.init Γ) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem program_cost : allocationCostProg program state = 6 := by decide +kernel

theorem compiled_input : compiled.Input 1 16 base state machine := by
  apply (compiled.memory_input (by decide +kernel) 1 16 base state machine).mpr
  exact ⟨fixture.1, by decide +kernel,
    .inr ⟨by decide, wmod 64, fixture.2, by decide +kernel⟩⟩

theorem compiled_agrees : compiled.Agrees 1 16 base state machine := compiled.correct compiled_input

private def observeTarget : Out → Option (List Nat)
  | .ok m _ => do
    let words := m.stack ++ [m.mem 0, m.mem 15, m.mem 1, m.mem 2, m.mem 3, m.mem 4, m.mem 5,
      m.mem 32, m.mem 33, m.mem 40, m.mem 41, m.mem 42, m.mem 48, m.mem 49,
      m.mem 50, m.mem 56, m.mem 57, m.mem 64, m.mem 65, m.mem 66, m.mem 67, m.mem 68, m.mem 69]
    words.mapM fun w => match w with | .val v => some v.val | .slot _ => none
  | _ => none

theorem target_observation : observeTarget (run compiled.code machine) =
    some [77, 70, 88, 56, 32, 40, 64, 66, 7, 1, 2, 9, 5, 32, 40, 0, 48, 99, 31, 0, 2, 41, 45, 0] := by
  decide +kernel

private def observeSource {Ω : Ctx} : TRes (Solidity.Out C H Ω) → Option (List Int)
  | .ok o => do
    let l ← refAt? o.st.H 0 (.struct leafName)
    let a ← refAt? o.st.H 1 (.array (.prim .uint))
    let h ← refAt? o.st.H 2 (.struct holderName)
    let fresh ← refAt? o.st.H 4 (.struct leafName)
    let xs ← refAt? o.st.H 5 (.array (.prim .uint))
    let b ← refAt? o.st.H 6 (.array (.prim .bool))
    let oldX ← o.st.heap.index a .dyn (indexValue (wmod 0))
    let newX ← o.st.heap.index xs .dyn (indexValue (wmod 1))
    let linkedLeaf : HRef o.st.H (.struct leafName) := o.st.heap.field h (f := "leaf") rfl
    let linkedArray : HRef o.st.H (.array (.prim .uint)) := o.st.heap.field h (f := "items") rfl
    some [(o.st.heap.field l (f := "n") rfl).1, oldX.1,
      (o.st.heap.field fresh (f := "n") rfl).1, newX.1, linkedLeaf.id, linkedArray.id,
      o.st.heap.len b .dyn]
  | .error _ => none

theorem source_observation : observeSource (program.run state) = some [7, 9, 31, 45, 0, 1, 0] := by
  decide +kernel

example : (Compiler.compile 0 (Frag.init Γ) program).isSome = false := by decide +kernel

end ReferenceWrite

namespace ReferenceDelete

private def Δ : Ctx := [.mem (.array (.prim .uint)), .mem (.struct leafName),
  .mem (.array (.prim .uint)), .mem (.struct leafName)] ++ Γ
private def root : Idx Δ (.mem (.struct wrapperName)) := .there (.there (.there (.there .here)))
private def firstLeaf : Idx Δ (.mem (.struct leafName)) := .there .here
private def firstArray : Idx Δ (.mem (.array (.prim .uint))) := .here
private def oldArray : Idx Δ (.mem (.array (.prim .uint))) := .there (.there .here)
private def rootBefore : Idx ([.mem (.array (.prim .uint)), .mem (.struct leafName)] ++ Γ)
    (.mem (.struct wrapperName)) := .there (.there .here)

private def scopedBody : Prog C Δ (.mem (.array (.prim .bool)) :: Δ) :=
  .cons (.deleteMem (.loc (.field (holderPath root) "leaf" rfl)) rfl)
  (.cons (.assignMem (.field (leafPath root) "n" rfl) (.val (lit 33 rfl)))
  (.cons (.deleteMem (.loc (.field (holderPath root) "items" rfl)) rfl)
  (.cons (.declMem (.array (.prim .bool)) (.user "fresh")
    (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil)))
private def steps : List (Stmt C Δ Δ) := [
  .deleteMem (.loc (.field (holderPath root) "leaf" rfl)) rfl,
  .deleteMem (.loc (.field (holderPath root) "items" rfl)) rfl,
  .require (eqN (nestedN root) 0 rfl),
  .require (eqN (.mlen (itemsPath root) rfl) 0 rfl),
  .require (eqN (.readMem (.field (.var firstLeaf rfl) "n" rfl)) 21 rfl),
  .require (.readMem (.field (.var firstLeaf rfl) "flag" rfl)),
  .require (eqN (.mlen (.var firstArray rfl) rfl) 0 rfl),
  .block scopedBody,
  .assignMem (.index .dyn (.var oldArray rfl) (lit 0 rfl)) (.val (lit 9 rfl)),
  .require (eqN (nestedN root) 33 rfl),
  .require (eqN (.mlen (itemsPath root) rfl) 0 rfl),
  .require (eqN (.readMem (.field (.var firstLeaf rfl) "n" rfl)) 21 rfl)]
private def body : Prog C Δ Δ := steps.foldr (fun s p => .cons s p) .nil
private def program : Prog C Γ Δ :=
  .cons (.declMem (.struct leafName) (.user "oldLeaf") (some (.alias (leafPath .here))) rfl rfl)
  (.cons (.declMem (.array (.prim .uint)) (.user "oldArray")
    (some (.alias (itemsPath (.there .here)))) rfl rfl)
  (.cons (.deleteMem (.loc (.field (holderPath rootBefore) "leaf" rfl)) rfl)
  (.cons (.deleteMem (.loc (.field (holderPath rootBefore) "items" rfl)) rfl)
  (.cons (.require (eqN (nestedN rootBefore) 0 rfl))
  (.cons (.require (eqN (.mlen (itemsPath rootBefore) rfl) 0 rfl))
  (.cons (.require (.binop .eqB rfl rfl (.readMem (.field (leafPath rootBefore) "flag" rfl))
    (.simple (.bool false))))
  (.cons (.assignMem (.field (leafPath rootBefore) "n" rfl) (.val (lit 21 rfl)))
  (.cons (.assignMem (.field (leafPath rootBefore) "flag" rfl) (.val (.simple (.bool true))))
  (.cons (.declMem (.struct leafName) (.user "firstLeaf") (some (.alias (leafPath rootBefore))) rfl rfl)
  (.cons (.declMem (.array (.prim .uint)) (.user "firstArray")
    (some (.alias (itemsPath (.there rootBefore)))) rfl rfl) body))))))))))
private def compiled : Compiler.Compilation 1 (Frag.init Γ) program :=
  (Compiler.compile 1 (Frag.init Γ) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem program_cost : allocationCostProg program state = 11 := by decide +kernel

theorem compiled_input : compiled.Input 1 16 base state machine := by
  apply (compiled.memory_input (by decide +kernel) 1 16 base state machine).mpr
  exact ⟨fixture.1, by decide +kernel,
    .inr ⟨by decide, wmod 64, fixture.2, by decide +kernel⟩⟩

theorem compiled_agrees : compiled.Agrees 1 16 base state machine := compiled.correct compiled_input

private def observeTarget : Out → Option (List Nat)
  | .ok m _ => do
    let words := m.stack ++ [m.mem 0, m.mem 15, m.mem 1, m.mem 2, m.mem 3, m.mem 4, m.mem 5,
      m.mem 32, m.mem 33, m.mem 40, m.mem 41, m.mem 42, m.mem 48, m.mem 49,
      m.mem 50, m.mem 56, m.mem 57] ++ (List.range 11).map (fun i => m.mem (64 + i))
    words.mapM fun w => match w with | .val v => some v.val | .slot _ => none
  | _ => none

theorem target_observation : observeTarget (run compiled.code machine) =
    some [77, 75, 88, 56, 32, 40, 64, 66, 7, 1, 2, 9, 5, 70, 72, 0, 48, 99,
      21, 1, 0, 0, 0, 0, 33, 0, 0, 1, 0] := by decide +kernel

private def observeSource {Ω : Ctx} : TRes (Solidity.Out C H Ω) → Option (List Int)
  | .ok o => do
    let l ← refAt? o.st.H 0 (.struct leafName)
    let a ← refAt? o.st.H 1 (.array (.prim .uint))
    let h ← refAt? o.st.H 2 (.struct holderName)
    let first ← refAt? o.st.H 4 (.struct leafName)
    let xs ← refAt? o.st.H 5 (.array (.prim .uint))
    let second ← refAt? o.st.H 6 (.struct leafName)
    let current ← refAt? o.st.H 8 (.struct leafName)
    let currentArray ← refAt? o.st.H 9 (.array (.prim .uint))
    let b ← refAt? o.st.H 10 (.array (.prim .bool))
    let x ← o.st.heap.index a .dyn (indexValue (wmod 0))
    let flag : Bool := o.st.heap.field first (f := "flag") rfl
    let linkedLeaf : HRef o.st.H (.struct leafName) := o.st.heap.field h (f := "leaf") rfl
    let linkedArray : HRef o.st.H (.array (.prim .uint)) := o.st.heap.field h (f := "items") rfl
    some [(o.st.heap.field l (f := "n") rfl).1, x.1, (o.st.heap.field first (f := "n") rfl).1,
      if flag then 1 else 0, o.st.heap.len xs .dyn, (o.st.heap.field second (f := "n") rfl).1,
      (o.st.heap.field current (f := "n") rfl).1, linkedLeaf.id, linkedArray.id,
      o.st.heap.len currentArray .dyn, o.st.heap.len b .dyn]
  | .error _ => none

theorem source_observation : observeSource (program.run state) = some [7, 9, 21, 1, 0, 0, 33, 8, 9, 0, 1] := by
  decide +kernel

private def tooFull : Machine := writeMachine machine 0 (.val (wmod (W - 10)))
theorem capacity_invalid : ¬ compiled.Input 1 16 base state tooFull := by
  intro h
  have hi := ((compiled.memory_input (by decide +kernel) 1 16 base state tooFull).mp h).2.2
  rcases hi with hz | ⟨_, c, ha, hs⟩
  · rw [program_cost] at hz
    cases hz
  · have he : c = wmod (W - 10) := Word.val.inj ha.arrays.free.cell.symm
    subst c
    rw [program_cost] at hs
    have hn : ¬ (wmod (W - 10)).val + 11 < W := by decide +kernel
    exact hn hs

example : (Compiler.compile 0 (Frag.init Γ) program).isSome = false := by decide +kernel

private def single : Prog C Γ Γ :=
  .cons (.deleteMem (.loc (.field (holderPath .here) "leaf" rfl)) rfl) .nil
private def singleCompilation : Compiler.Compilation 1 (Frag.init Γ) single :=
  (Compiler.compile 1 (Frag.init Γ) single).get (by decide +kernel)
attribute [irreducible] singleCompilation
private def unset : State C Γ := state.setLocal .here none

theorem unset_cost : allocationCostProg single unset = 0 := by decide +kernel
theorem unset_reverts : single.run unset = .error .revert := by with_unfolding_all rfl
theorem unset_input_refuted : ¬ singleCompilation.Input 1 16 base unset machine := by
  intro h
  have hs := ((singleCompilation.memory_input (by decide +kernel) 1 16 base unset machine).mp h).1
  obtain ⟨r, hr, _⟩ := hs.pointers .here
  change (none : Option (HRef H (.struct wrapperName))) = some r at hr
  cases hr

private theorem cursor_state (w : Word) :
    StateRepr 1 1 16 (Frag.init Γ) state base (writeMachine machine 0 w) := by
  have h := fixture.1
  have hc := h.core.congrMem (mem := upd machine.mem 0 w)
    (by
      intro l hl hu
      change upd machine.mem 0 w l = machine.mem l
      exact upd_other _ _ (by omega))
  refine ⟨hc, h.heap.localWrite 0 (by decide) _, ?_, h.locals,
    h.structs.localWrite 0 (by decide) _, h.separated,
    RefFieldsRepr.localWrite h.refs h.structs 0 (by decide) _⟩
  intro R i
  obtain ⟨r, hr, hm⟩ := h.pointers i
  refine ⟨r, hr, ?_⟩
  change upd machine.mem 0 w (lvl 1 i) = _
  rw [upd_other _ _ (by have hi := le_lvl 1 i; omega)]
  exact hm

private def unreached : Prog C Γ Γ :=
  .cons (.require (.simple (.bool false)))
    (.cons (.deleteMem (.loc (.field (holderPath .here) "leaf" rfl)) rfl)
    (.cons (.deleteMem (.loc (.field (holderPath .here) "items" rfl)) rfl) .nil))
private def unreachedCompilation : Compiler.Compilation 1 (Frag.init Γ) unreached :=
  (Compiler.compile 1 (Frag.init Γ) unreached).get (by decide +kernel)
attribute [irreducible] unreachedCompilation

theorem unreached_cost : allocationCostProg unreached state = 0 := by decide +kernel
theorem unreached_input :
    unreachedCompilation.Input 1 16 base state (writeMachine machine 0 w[0]) := by
  apply (unreachedCompilation.memory_input (by decide +kernel) 1 16 base state _).mpr
  exact ⟨cursor_state _, by decide +kernel, .inl unreached_cost⟩
theorem unreached_agrees :
    unreachedCompilation.Agrees 1 16 base state (writeMachine machine 0 w[0]) :=
  unreachedCompilation.correct unreached_input
theorem unreached_reverts : unreached.run state = .error .revert ∧
    reverted (run unreachedCompilation.code (writeMachine machine 0 w[0])) = true := by
  constructor
  · rfl
  · decide +kernel

end ReferenceDelete

end Solidity.Evm.Memory.PathExamples
