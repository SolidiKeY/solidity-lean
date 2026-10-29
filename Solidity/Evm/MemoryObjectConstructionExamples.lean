import Solidity.Evm.Compiler
import Solidity.Syntax.Splice

/-! Source-spliced construction with a local runtime length, retained aliases,
primitive child allocation and a kernel-derived actual target result. -/
namespace Solidity.Evm.Memory.ConstructionExamples
private def C : Contract := contract!{}
private def child : RefTy := .array (.prim .uint)
private def parent : RefTy := .array (.ref child)
private def Δ : Ctx := [.val .uint, .mem child, .mem child, .mem child, .mem parent, .val .uint, .mem parent]
private def program : Prog C [] Δ := sol[C]{
  uint[][] memory empty;
  uint n = 2;
  uint[][] memory a = new uint[][](n);
  uint[] memory left = new uint[](1);
  uint[] memory right = new uint[](1);
  left[0] = 7;
  right[0] = 9;
  a[0] = left;
  a[1] = left;
  uint[] memory x = right;
  x = a[0];
  a[0] = right;
  x[0] = 11;
  a[0][0] = 13;
  uint result = x[0] * 1000 + a[0][0];
  a = new uint[][](n);
  result = x[0] * 1000 + right[0];
}
private def base : Nat → Fin W := fun _ => wmod 0
private def machine : Machine := {Machine.init with stack := [w[77]], mem := fun a =>
  if a = 0 then w[16] else if a = 15 then w[99] else w[0]}
private def state := State.init C
private theorem noRefs {R : RefTy} (r : HRef [] R) : False := by
  simpa only [List.getElem?_nil, reduceCtorEq] using r.get?
private theorem heap_repr : Objects.HeapRepr state.heap base 8 machine := by
  exact ⟨⟨fun r => (noRefs r).elim, fun r => (noRefs r).elim, fun r _ _ => (noRefs r).elim⟩,
    (fun _ r => (noRefs r).elim), (fun r => (noRefs r).elim), (fun r _ => (noRefs r).elim)⟩

theorem initial_repr : Objects.StateRepr 1 1 8 (Frag.init []) state base machine := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
  refine ⟨⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩,
    heap_repr, ?_, by decide⟩
  all_goals intro p i; nomatch i

theorem initial_allocator : Objects.AllocatorRepr state.heap base 8 ⟨16, by decide⟩ machine := by
  refine ⟨heap_repr, ⟨by decide, by decide, rfl, ?_⟩, fun r => (noRefs r).elim⟩
  intro addr ha
  change 16 ≤ addr at ha
  simp only [machine, if_neg (show addr ≠ 0 by omega), if_neg (show addr ≠ 15 by omega)]

private def compiled := (Compiler.compile 1 (Frag.init []) program).get (by decide +kernel)
attribute [irreducible] compiled

theorem source_cost : Construction.allocationCostProg program state = 15 := by decide +kernel

theorem compiled_input : compiled.Input 1 8 base state machine := by
  apply (compiled.construction_input (by decide +kernel) 1 8 base state machine).mpr
  refine ⟨initial_repr, by decide +kernel, .inr ⟨by decide, ⟨16, by decide⟩, initial_allocator, ?_⟩⟩
  rw [source_cost]
  decide +kernel

theorem compiled_agrees : compiled.Agrees 1 8 base state machine := compiled.correct compiled_input

private def observeSource (r : TRes (Solidity.Out C [] Δ)) : Option Nat := do
  let o ← r.toOption
  pure (TEnv.get (.here : Idx Δ (.val .uint)) o.st.env).val.toNat

theorem source_result : observeSource (program.run state) = some 11013 := by decide +kernel

/-- Actual target-run observation follows from the checked loop simulation,
not evaluator fuel, native agreement or an assumed empty input relation. -/
theorem target_result : ∃ m', run compiled.code machine = .ok m' 0 ∧
    m'.mem 7 = w[11013] ∧ m'.stack = [w[77]] := by
  have hok : (program.run state).toOption.isSome = true := by decide +kernel
  obtain ⟨o, ho⟩ : ∃ o, program.run state = .ok o := by
    cases he : program.run state with
    | error e => simp only [he, Except.toOption, Option.isSome] at hok; cases hok
    | ok o => exact ⟨o, rfl⟩
  rcases compiled_agrees with ⟨out, m', hs, ht, hstack, hr⟩ | ⟨hs, ht⟩ |
      ⟨hp, ht, out, m', hs, hr⟩ | ⟨hs, ht⟩
  · have hp : Evm.Prog.pushes program = 0 := rfl
    have hr' : compiled.Rep 1 8 base state machine out.st m' := by
      simpa only [hp, Nat.add_zero] using hr
    obtain ⟨base', hrepr, _, _⟩ :=
      (compiled.construction_rep (by decide +kernel) 1 8 base state machine out.st m').mp hr'
    have hv := hrepr.core.vals (.here : Idx Δ (.val .uint))
    change ReprV .uint (TEnv.get (.here : Idx Δ (.val .uint)) out.st.env) (m'.mem 7) at hv
    have hval : (TEnv.get (.here : Idx Δ (.val .uint)) out.st.env).val.toNat = 11013 := by
      have he := source_result
      simpa only [observeSource, hs, Except.toOption, bind, Option.bind, pure,
        Option.some.injEq] using he
    obtain ⟨a, ha, he, hw⟩ := hv.uint_inv
    have ha' : a = 11013 := by simpa only [he, Int.toNat_natCast] using hval
    subst a
    exact ⟨m', ht, hw, hstack⟩
  · simp only [ho, reduceCtorEq, and_false, or_self] at hs
  · have hpays : Evm.Prog.pays program = false := rfl
    rw [hpays] at hp
    cases hp
  · rw [ho] at hs; cases hs

private def BoundsΔ : Ctx := [.val .uint, .mem parent, .val .uint]
private def failing (k : Fin 3) : Prog C [] BoundsΔ :=
  if k.val = 0 then sol[C]{ uint n = 2; uint[][] memory a = new uint[][](n); uint unused = a[2].length; }
  else if k.val = 1 then sol[C]{ uint n = 2; uint[][] memory a = new uint[][](n); uint unused = a[0][0]; }
  else sol[C]{ uint n = 0; uint[][] memory a = new uint[][](n); uint unused = a[0].length; }
private theorem failures_compile : ∀ k : Fin 3,
    (Compiler.compile 1 (Frag.init []) (failing k)).isSome = true := by decide +kernel
private def failed (k : Fin 3) := (Compiler.compile 1 (Frag.init []) (failing k)).get (failures_compile k)
attribute [irreducible] failed

theorem failed_input (k : Fin 3) : (failed k).Input 1 8 base state machine := by
  have hm : ∀ k : Fin 3, (failed k).isConstruction = true := by decide +kernel
  have hf : ∀ k : Fin 3, 1 + frameNeedProg (failing k) ≤ 8 := by decide +kernel
  have hc : ∀ k : Fin 3, 16 + Construction.allocationCostProg (failing k) state < W := by decide +kernel
  apply ((failed k).construction_input (hm k) 1 8 base state machine).mpr
  refine ⟨initial_repr, hf k, .inr ⟨by decide, ⟨16, by decide⟩, initial_allocator, ?_⟩⟩
  exact hc k

theorem failed_agrees (k : Fin 3) : (failed k).Agrees 1 8 base state machine :=
  (failed k).correct (failed_input k)

private def sourceReverted {Δ : Ctx} : TRes (Solidity.Out C [] Δ) → Bool
  | .error .revert => true
  | _ => false
private theorem sourceReverted_eq {Δ : Ctx} (r : TRes (Solidity.Out C [] Δ))
    (h : sourceReverted r = true) : r = .error .revert := by
  cases r with
  | ok o => cases h
  | error e => cases e <;> cases h <;> rfl

theorem source_bounds (k : Fin 3) : (failing k).run state = .error .revert := by
  have h : ∀ k : Fin 3, sourceReverted ((failing k).run state) = true := by decide +kernel
  exact sourceReverted_eq _ (h k)

theorem target_bounds (k : Fin 3) : run (failed k).code machine = .revert := by
  have hs := source_bounds k
  rcases failed_agrees k with ⟨o, m', ho, hc, hk, hr⟩ | ⟨ho, hc⟩ |
      ⟨hp, hc, o, m', ho, hr⟩ | ⟨ho, hc⟩
  · cases ho.symm.trans hs
  · exact hc
  · exact hc
  · cases ho.symm.trans hs

private def defaults := Objects.nestedCopy state.heap (.prim .uint) rfl (wmod 2)
private def first : HRef defaults.H' child := ⟨0, by decide +kernel⟩
private def second : HRef defaults.H' child := ⟨1, by decide +kernel⟩
private def u (n : Nat) := indexValue (wmod n)

theorem source_default_identities : defaults.val.id = 2 ∧
    (defaults.heap.index defaults.val .dyn (u 0)).map (fun r => r.id) = some 0 ∧
    (defaults.heap.index defaults.val .dyn (u 1)).map (fun r => r.id) = some 1 := by
  decide +kernel

/-- Two empty source children produce distinct represented pointers, not zero
or a shared dummy address; this is an actual terminating target run. -/
theorem target_default_identities : ∃ (base' : Nat → Fin W) (m' : Machine),
    run Objects.nestedCode (machine.push w[2]) = .ok (m'.push w[16]) 0 ∧
    m'.mem 17 = .val (base' 0) ∧ m'.mem 18 = .val (base' 1) ∧ base' 0 ≠ base' 1 ∧
    m'.mem (base' 0).val = w[0] ∧ m'.mem (base' 1).val = w[0] := by
  obtain ⟨base', m', hr, ha, hb, hext, hs, hf, hm⟩ :=
    Objects.nested_correct state.heap (.prim .uint) rfl (wmod 2) base 8 machine
      ⟨16, by decide⟩ initial_allocator (by decide +kernel)
  have hb' : base' defaults.val.id = wmod 16 := hb
  have hparent := ha.heap.arrays .dyn defaults.val
  have hfirst : (MObj.elems .dyn (defaults.heap.get defaults.val))[0]? = some first := by with_unfolding_all rfl
  have hsecond : (MObj.elems .dyn (defaults.heap.get defaults.val))[1]? = some second := by with_unfolding_all rfl
  have hp0 := hparent.elements 0 first hfirst
  have hp1 := hparent.elements 1 second hsecond
  change m'.mem ((base' defaults.val.id).val + 1 + 0) = .val (base' 0) at hp0
  change m'.mem ((base' defaults.val.id).val + 1 + 1) = .val (base' 1) at hp1
  rw [hb'] at hp0 hp1
  have hlen0 : defaults.heap.len first .dyn = 0 := by decide +kernel
  have hlen1 : defaults.heap.len second .dyn = 0 := by decide +kernel
  have hc0 := (ha.heap.arrays .dyn first).length rfl
  have hc1 := (ha.heap.arrays .dyn second).length rfl
  change m'.mem (base' 0).val = .val (wmod (defaults.heap.len first .dyn)) at hc0
  rw [hlen0] at hc0
  change m'.mem (base' 1).val = .val (wmod (defaults.heap.len second .dyn)) at hc1
  rw [hlen1] at hc1
  refine ⟨base', m', hr, hp0, hp1, ?_, hc0, hc1⟩
  intro he
  have hid := ha.heap.owner.base_injective first second he
  exact (by decide : first.id ≠ second.id) hid

private def boundaryMachine (c : Fin W) : Machine :=
  { machine with mem := fun a => (if a = 0 then Word.val c else w[0]) }
private theorem boundary_repr (c : Fin W) :
    Objects.StateRepr 1 1 8 (Frag.init []) state base (boundaryMachine c) := by
  refine ⟨initial_repr.core.congrMem (fun l hl hu => by change l < 1 at hu; omega), ?_, ?_, by decide⟩
  · exact ⟨⟨fun r => (noRefs r).elim, fun r => (noRefs r).elim, fun r _ _ => (noRefs r).elim⟩,
      (fun _ r => (noRefs r).elim), (fun r => (noRefs r).elim), (fun r _ => (noRefs r).elim)⟩
  · intro R i; nomatch i
private theorem boundary_allocator (c : Fin W) (hc : 8 ≤ c.val) :
    Objects.AllocatorRepr state.heap base 8 c (boundaryMachine c) := by
  refine ⟨(boundary_repr c).heap, ⟨by decide, hc, rfl, ?_⟩, fun r => (noRefs r).elim⟩
  intro a ha
  exact if_neg (by omega)
private def exactCursor : Fin W := ⟨W - 16, by
  have hw : 16 < W := by decide
  omega⟩
private def badCursor : Fin W := ⟨W - 15, by
  have hw : 15 < W := by decide
  omega⟩

/-- The last permitted cursor is inhabited: the result cursor is W-1. -/
theorem exact_capacity_input : compiled.Input 1 8 base state (boundaryMachine exactCursor) := by
  apply (compiled.construction_input (by decide +kernel) 1 8 base state (boundaryMachine exactCursor)).mpr
  have hw : 24 < W := by decide
  refine ⟨boundary_repr _, by decide +kernel, .inr ⟨by decide, exactCursor,
    boundary_allocator _ (by change 8 ≤ W - 16; omega), ?_⟩⟩
  rw [source_cost]
  change W - 16 + 15 < W
  omega

theorem exact_capacity_agrees : compiled.Agrees 1 8 base state (boundaryMachine exactCursor) :=
  compiled.correct exact_capacity_input

/-- A cursor plus cost equal to W is explicitly excluded, never wrapped to zero. -/
theorem insufficient_capacity_refuted : ¬ compiled.Input 1 8 base state (boundaryMachine badCursor) := by
  intro h
  have hi := (compiled.construction_input (by decide +kernel) 1 8 base state (boundaryMachine badCursor)).mp h
  rcases hi.2.2 with hz | ⟨hb, c, ha, hs⟩
  · rw [source_cost] at hz; cases hz
  · have he : c = badCursor := Word.val.inj (ha.free.cell.symm.trans (by rfl))
    subst c
    rw [source_cost] at hs
    change W - 15 + 15 < W at hs
    have hw : 15 < W := by decide
    omega

private def UnreachableΔ : Ctx := [.mem parent, .val .uint, .mem parent]
private def unreachable : Prog C [] UnreachableΔ := sol[C]{
  uint[][] memory a = new uint[][](2);
  uint unused = a[0][0];
  uint[][] memory unreachable = new uint[][](115792089237316195423570985008687907853269984665640564039457584007913129639935);
}
private def unreachableCompiled :=
  (Compiler.compile 1 (Frag.init []) unreachable).get (by decide +kernel)
attribute [irreducible] unreachableCompiled

theorem unreachable_cost : Construction.allocationCostProg unreachable state = 5 := by decide +kernel

theorem unreachable_input : unreachableCompiled.Input 1 8 base state machine := by
  apply (unreachableCompiled.construction_input (by decide +kernel) 1 8 base state machine).mpr
  refine ⟨initial_repr, by decide +kernel, .inr ⟨by decide, ⟨16, by decide⟩, initial_allocator, ?_⟩⟩
  rw [unreachable_cost]
  decide +kernel

theorem unreachable_source : unreachable.run state = .error .revert := by
  apply sourceReverted_eq
  decide +kernel

theorem unreachable_target : run unreachableCompiled.code machine = .revert := by
  rcases unreachableCompiled.correct unreachable_input with ⟨o, m', ho, hc, hk, hr⟩ | ⟨ho, hc⟩ |
      ⟨hp, hc, o, m', ho, hr⟩ | ⟨ho, hc⟩
  · cases ho.symm.trans unreachable_source
  · exact hc
  · exact hc
  · cases ho.symm.trans unreachable_source

private def zeroDefaults := Objects.nestedCopy state.heap (.prim .uint) rfl (wmod 0)
theorem zero_source_length : zeroDefaults.heap.len zeroDefaults.val .dyn = 0 := by decide +kernel

theorem zero_target_allocation : ∃ m' : Machine,
    run Objects.nestedCode (machine.push w[0]) = .ok (m'.push w[16]) 0 ∧
    m'.mem 16 = w[0] ∧ m'.mem 0 = w[17] := by
  obtain ⟨base', m', hr, ha, hb, hext, hs, hf, hm⟩ :=
    Objects.nested_correct state.heap (.prim .uint) rfl (wmod 0) base 8 machine
      ⟨16, by decide⟩ initial_allocator (by decide +kernel)
  have hb' : base' zeroDefaults.val.id = wmod 16 := hb
  have hh := (ha.heap.arrays .dyn zeroDefaults.val).length rfl
  change m'.mem (base' zeroDefaults.val.id).val = .val (wmod (zeroDefaults.heap.len zeroDefaults.val .dyn)) at hh
  rw [hb', zero_source_length] at hh
  exact ⟨m', hr, hh, ha.free.cell⟩

private def zeroProgram : Prog C [] BoundsΔ := sol[C]{
  uint n = 0; uint[][] memory a = new uint[][](n); uint observed = a.length;
}
private def zeroCompiled := (Compiler.compile 1 (Frag.init []) zeroProgram).get (by decide +kernel)
attribute [irreducible] zeroCompiled

theorem zero_public_input : zeroCompiled.Input 1 8 base state machine := by
  apply (zeroCompiled.construction_input (by decide +kernel) 1 8 base state machine).mpr
  refine ⟨initial_repr, by decide +kernel, .inr ⟨by decide, ⟨16, by decide⟩, initial_allocator, ?_⟩⟩
  decide +kernel

theorem zero_public_agrees : zeroCompiled.Agrees 1 8 base state machine := zeroCompiled.correct zero_public_input

theorem zero_public_source : ((zeroProgram.run state).toOption.map
    (fun o => (TEnv.get (.here : Idx BoundsΔ (.val .uint)) o.st.env).val.toNat)) = some 0 := by
  decide +kernel

private def fixedChild : RefTy := .fixed (.prim .uint) 1
private def fixedParent : RefTy := .array (.ref fixedChild)
private def FixedZeroΔ : Ctx := [.val .uint, .mem fixedParent]
private def fixedZeroProgram : Prog C [] FixedZeroΔ := sol[C]{
  uint[1][] memory a = new uint[1][](0);
  a = new uint[1][](0);
  uint observed = a.length;
}
private def fixedZeroCompiled := (Compiler.compile 1 (Frag.init []) fixedZeroProgram).get (by decide +kernel)
attribute [irreducible] fixedZeroCompiled

theorem fixed_zero_input : fixedZeroCompiled.Input 1 8 base state machine := by
  apply (fixedZeroCompiled.construction_input (by decide +kernel) 1 8 base state machine).mpr
  refine ⟨initial_repr, by decide +kernel, .inr ⟨by decide, ⟨16, by decide⟩, initial_allocator, ?_⟩⟩
  decide +kernel

theorem fixed_zero_agrees : fixedZeroCompiled.Agrees 1 8 base state machine :=
  fixedZeroCompiled.correct fixed_zero_input
private def fixedZeroSource : Option (List Nat) := do
  let o ← (fixedZeroProgram.run state).toOption
  let r ← TEnv.get (.there .here : Idx FixedZeroΔ (.mem fixedParent)) o.st.env
  pure [o.st.H.length, r.id, o.st.heap.len r .dyn,
    (TEnv.get (.here : Idx FixedZeroΔ (.val .uint)) o.st.env).val.toNat]
private def fixedZeroTarget : Option (List Nat) := do
  let m ← match run fixedZeroCompiled.code machine with | .ok m _ => some m | _ => none
  [m.mem 0,m.mem 1,m.mem 2,m.mem 16,m.mem 17].mapM
    (fun w => match w with | .val n => some n.val | _ => none)
theorem fixed_zero_source : fixedZeroSource = some [2,1,0,0] := by decide +kernel
theorem fixed_zero_target : fixedZeroTarget = some [18,17,0,0,0] := by decide +kernel

/-- Former fixed-child refusal is now an explicit public registration control. -/
theorem fixed_child_nonempty_allocation_registered :
    (Compiler.compile (C := C) 1 (Frag.init []) (.cons
      (.declMem fixedParent (.user "fresh") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil)).isSome = true := by
  decide +kernel

theorem fixed_parent_default_registered :
    (Compiler.compile (C := C) 1 (Frag.init []) (.cons
      (.declMem (.fixed (.ref child) 2) (.user "fresh") none rfl rfl) .nil)).isSome = true := by
  decide +kernel

end Solidity.Evm.Memory.ConstructionExamples
