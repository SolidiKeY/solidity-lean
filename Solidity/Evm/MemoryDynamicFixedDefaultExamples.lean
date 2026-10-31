import Solidity.Evm.Compiler
import Solidity.Syntax.Splice

namespace Solidity.Evm.Memory.DynamicFixedDefaultExamples
private def C : Contract := contract!{}
private def child : RefTy := .fixed (.prim .uint) 1
private def parent : RefTy := .array (.ref child)
private def Δ : Ctx := [.val .uint, .mem child, .mem parent, .val .uint]
private def program : Prog C [] Δ := sol[C]{ uint n = 2; uint[1][] memory a = new uint[1][](n); uint[1] memory x = a[0]; a[0] = a[1]; x[0] = 11; a[0][0] = 13; uint result = x[0] * 1000 + a[0][0]; }
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

theorem source_cost : Construction.allocationCostProg program state = 5 := by decide +kernel

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
    m'.mem 4 = w[11013] ∧ m'.stack = [w[77]] := by
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
    change ReprV .uint (TEnv.get (.here : Idx Δ (.val .uint)) out.st.env) (m'.mem 4) at hv
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
private def failing (k : Fin 2) : Prog C [] BoundsΔ :=
  if k.val = 0 then sol[C]{ uint n = 2; uint[1][] memory a = new uint[1][](n); uint unused = a[n][0]; }
  else sol[C]{ uint n = 2; uint[1][] memory a = new uint[1][](n); uint unused = a[0][n - 1]; }
private theorem failures_compile : ∀ k : Fin 2,
    (Compiler.compile 1 (Frag.init []) (failing k)).isSome = true := by decide +kernel
private def failed (k : Fin 2) := (Compiler.compile 1 (Frag.init []) (failing k)).get (failures_compile k)
attribute [irreducible] failed

theorem failed_input (k : Fin 2) : (failed k).Input 1 8 base state machine := by
  have hm : ∀ k : Fin 2, (failed k).isConstruction = true := by decide +kernel
  have hf : ∀ k : Fin 2, 1 + frameNeedProg (failing k) ≤ 8 := by decide +kernel
  have hc : ∀ k : Fin 2, 16 + Construction.allocationCostProg (failing k) state < W := by decide +kernel
  apply ((failed k).construction_input (hm k) 1 8 base state machine).mpr
  refine ⟨initial_repr, hf k, .inr ⟨by decide, ⟨16, by decide⟩, initial_allocator, ?_⟩⟩
  exact hc k

theorem failed_agrees (k : Fin 2) : (failed k).Agrees 1 8 base state machine :=
  (failed k).correct (failed_input k)

private def sourceReverted {Δ : Ctx} : TRes (Solidity.Out C [] Δ) → Bool
  | .error .revert => true
  | _ => false
private theorem sourceReverted_eq {Δ : Ctx} (r : TRes (Solidity.Out C [] Δ))
    (h : sourceReverted r = true) : r = .error .revert := by
  cases r with
  | ok o => cases h
  | error e => cases e <;> cases h <;> rfl

theorem source_bounds (k : Fin 2) : (failing k).run state = .error .revert := by
  have h : ∀ k : Fin 2, sourceReverted ((failing k).run state) = true := by decide +kernel
  exact sourceReverted_eq _ (h k)

theorem target_bounds (k : Fin 2) : run (failed k).code machine = .revert := by
  have hs := source_bounds k
  rcases failed_agrees k with ⟨o, m', ho, hc, hk, hr⟩ | ⟨ho, hc⟩ |
      ⟨hp, hc, o, m', ho, hr⟩ | ⟨ho, hc⟩
  · cases ho.symm.trans hs
  · exact hc
  · exact hc
  · cases ho.symm.trans hs


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
private def exactCursor : Fin W := ⟨W - 6, by
  have hw : 6 < W := by decide
  omega⟩
private def badCursor : Fin W := ⟨W - 5, by
  have hw : 5 < W := by decide
  omega⟩

/-- The last permitted cursor is inhabited: the result cursor is W-1. -/
theorem exact_capacity_input : compiled.Input 1 8 base state (boundaryMachine exactCursor) := by
  apply (compiled.construction_input (by decide +kernel) 1 8 base state (boundaryMachine exactCursor)).mpr
  have hw : 24 < W := by decide
  refine ⟨boundary_repr _, by decide +kernel, .inr ⟨by decide, exactCursor,
    boundary_allocator _ (by change 8 ≤ W - 6; omega), ?_⟩⟩
  rw [source_cost]
  change W - 6 + 5 < W
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
    change W - 5 + 5 < W at hs
    have hw : 5 < W := by decide
    omega


end Solidity.Evm.Memory.DynamicFixedDefaultExamples
