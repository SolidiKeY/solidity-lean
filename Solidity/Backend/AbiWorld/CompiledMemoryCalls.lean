import Solidity.Evm.Compiler
import Solidity.Backend.AbiWorld.PublishedLayout

/-! Published direct internal memory-call compiler consumption. Word-cell memory
is observed explicitly; no external CALL, ABI aggregate codec or byte-addressed
REVERT composition is supplied by this component. -/
namespace Solidity.Backend.AbiWorld.CompiledMemoryCalls
open Evm Evm.Memory

/-- Expose the actual memory-call output relation, retaining old bases and exact
reached allocator cost rather than replacing either with frame preservation. -/
theorem memory_calls_rep {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (c : Compiler.Compilation b F P)
    (hc : c.isMemoryCalls = true) (base : Nat → Fin W) (σ : State C Γ)
    (m : Machine) (τ : State C Δ) (m' : Machine) :
    c.Rep L frame base σ m τ m' ↔ ∃ base',
      StateRepr L b frame c.frag τ base' m' ∧ BaseExtends σ.H base base' ∧
      GrowsAllocator b frame (c.allocationCost σ) σ base m τ base' m' := by
  cases c <;> cases hc <;> rfl

/-- The public correctness branch transports a completed intrinsic execution.
The no-payment premise is explicit and discharged by the inhabited controls. -/
theorem completed_transport {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (c : Compiler.Compilation b F P)
    (hc : c.isMemoryCalls = true) {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : c.Input L frame base σ m) (hp : Evm.Prog.pays P = false)
    (o : Solidity.Out C σ.H Δ) (ho : P.run σ = .ok o) :
    ∃ m' base', Evm.run c.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      StateRepr (L + Evm.Prog.pushes P) b frame c.frag o.st base' m' ∧
      BaseExtends σ.H base base' ∧
      GrowsAllocator b frame (c.allocationCost σ) σ base m o.st base' m' := by
  rcases c.correct hi with ⟨o', m', hs, ht, hk, hr⟩ | hbad
  · rw [ho] at hs
    cases hs
    obtain ⟨base', hst, hb, ha⟩ := (memory_calls_rep c hc base σ m o.st m').mp hr
    exact ⟨m', base', ht, hk, hst, hb, ha⟩
  · rcases hbad with ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨hs, _⟩
    · rcases hs with hs | ⟨_, hs⟩ <;> rw [ho] at hs <;> cases hs
    · rw [hp] at hs; cases hs
    · rw [ho] at hs; cases hs

private def C : Contract := { vars := [("saved", .prim .uint)] }
private def initial : State C [] := State.init C
private def bases : Nat → Fin W := fun _ => wmod 0
private def machine : Machine :=
  {Machine.init with stack := [w[77]], mem := fun a =>
    if a = 0 then w[256] else if a = 127 then w[99] else w[0]}
private theorem noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?

private theorem initial_repr : StateRepr 1 1 128 (Frag.init []) initial bases machine ∧
    StructAllocatorRepr initial.heap bases 128 (wmod 256) machine := by
  have hh : HeapRepr initial.heap bases 128 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hs : StructHeapRepr initial.heap bases 128 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hx : StructArraySeparated initial.heap bases := fun _ r => (noRef r).elim
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
  refine ⟨⟨?_, hh, ?_, by decide, hs, hx, ?_⟩,
    ⟨⟨hh, ?_, fun r => (noRef r).elim⟩, hs, hx, fun r => (noRef r).elim⟩⟩
  · refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
    · intro p i; nomatch i
    · intro R i hi; nomatch i
    · intro R i hi; nomatch i
  · intro R i; nomatch i
  · intro s f R r hf; exact (noRef r).elim
  · refine ⟨by decide, by decide, rfl, ?_⟩
    intro a ha
    change 256 ≤ a at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · rfl

private def u {Γ : Ctx} (n : Nat) (h : n < 2 ^ 256 := by decide +kernel) : Val C Γ .uint :=
  .simple (.lit n (PrimTy.inRange_uint_of_lt h))
private def element {Γ : Ctx} (x : Idx Γ (.mem bytesR)) (i : Nat)
    (h : i < 2 ^ 256 := by decide +kernel) : MLoc C Γ (.prim .uint) :=
  .index .dyn (.var x rfl) (u i h)
private abbrev Body := Prog C [.mem bytesR, .mem bytesR]
  [.val .uint, .mem bytesR, .mem bytesR]
private def shared : Body :=
  .cons (.assignMem (element (.there .here) 1) (.val (u 127)))
  (.cons (.rebindMem .here (.alias (.var (.there .here) rfl)))
  (.cons (.rebindMem (.there .here) (.newArr (.lit 1 rfl) rfl))
  (.cons (.assignMem (element (.there .here) 0) (.val (u 238)))
  (.cons (.declLocal .uint (.user "private") (some (u 99))) .nil))))
private def escaping : Body :=
  .cons (.rebindMem .here (.newArr (.lit 2 rfl) rfl))
  (.cons (.assignMem (element .here 0) (.val (u 153)))
  (.cons (.assignMem (element .here 1) (.val (u 136)))
  (.cons (.declLocal .uint (.user "private") (some (u 99))) .nil)))
private def emptyReturn : Body :=
  .cons (.declLocal .uint (.user "private") (some (u 99))) .nil
private def wideReturn : Body :=
  .cons (.rebindMem .here (.alias (.var (.there .here) rfl)))
  (.cons (.assignMem (element (.there .here) 1) (.val (u 300)))
  (.cons (.declLocal .uint (.user "private") (some (u 99))) .nil))
private def failing : Body := .cons (.require (.simple (.bool false))) shared
private abbrev Output : Ctx := [.mem bytesR, .mem bytesR, .mem bytesR, .val .uint]
private def program (body : Body) : Prog C [] Output :=
  .cons (.assign (.root "saved" rfl) (.val (u 9)))
  (.cons (.declLocal .uint (.user "marker") (some (u 77)))
  (litBytes (.user "reason") [66, 0, 254]
  (.cons (.declMem bytesR (.user "olderAlias") (some (.alias (.var .here rfl))) rfl rfl)
  (.cons (.call "transport" (.snocMemory .nil bytesR (.user "arg") (.var .here rfl))
    (.mem bytesR (.user "result") rfl rfl) body)
  (.cons (litWrite 0 (by decide +kernel) 67) .nil)))))

private def compiledShared : Compiler.Compilation 1 (Frag.init []) (program shared) :=
  (Compiler.compile 1 (Frag.init []) (program shared)).get (by decide +kernel)
private def compiledEscape : Compiler.Compilation 1 (Frag.init []) (program escaping) :=
  (Compiler.compile 1 (Frag.init []) (program escaping)).get (by decide +kernel)
private def compiledFailure : Compiler.Compilation 1 (Frag.init []) (program failing) :=
  (Compiler.compile 1 (Frag.init []) (program failing)).get (by decide +kernel)
private def compiledEmpty : Compiler.Compilation 1 (Frag.init []) (program emptyReturn) :=
  (Compiler.compile 1 (Frag.init []) (program emptyReturn)).get (by decide +kernel)
private def compiledWide : Compiler.Compilation 1 (Frag.init []) (program wideReturn) :=
  (Compiler.compile 1 (Frag.init []) (program wideReturn)).get (by decide +kernel)
attribute [irreducible] compiledShared compiledEscape compiledFailure compiledEmpty compiledWide

theorem shared_input : compiledShared.Input 1 128 bases initial machine := by
  apply (compiledShared.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem escape_input : compiledEscape.Input 1 128 bases initial machine := by
  apply (compiledEscape.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem failure_input : compiledFailure.Input 1 128 bases initial machine := by
  apply (compiledFailure.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩

theorem empty_input : compiledEmpty.Input 1 128 bases initial machine := by
  apply (compiledEmpty.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem wide_input : compiledWide.Input 1 128 bases initial machine := by
  apply (compiledWide.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem empty_agrees : compiledEmpty.Agrees 1 128 bases initial machine :=
  compiledEmpty.correct empty_input
theorem wide_agrees : compiledWide.Agrees 1 128 bases initial machine :=
  compiledWide.correct wide_input

theorem shared_agrees : compiledShared.Agrees 1 128 bases initial machine :=
  compiledShared.correct shared_input
theorem escape_agrees : compiledEscape.Agrees 1 128 bases initial machine :=
  compiledEscape.correct escape_input
theorem failure_agrees : compiledFailure.Agrees 1 128 bases initial machine :=
  compiledFailure.correct failure_input

private def targetWords (out : Evm.Out) (addresses : List Nat) : Option (List Nat) := do
  match out with
  | .ok m _ => (m.stack ++ addresses.map m.mem).mapM fun w => match w with
    | .val v => some v.val | .slot _ => none
  | _ => none
private def sourceRefs (res : TRes (Solidity.Out C [] Output)) : Option (List Nat) := do
  let o ← res.toOption
  let r ← TEnv.get .here o.st.env
  let a ← TEnv.get (.there .here) o.st.env
  let b ← TEnv.get (.there (.there .here)) o.st.env
  pure [o.st.H.length, r.id, a.id, b.id, (TEnv.get (.there (.there (.there .here))) o.st.env).1.toNat]

/-- The returned reference aliases both old caller locals despite parameter
rebinding; private local binders are dropped, caller marker/store and stack survive. -/
theorem shared_observations :
    sourceRefs ((program shared).run initial) = some [3, 0, 0, 0, 77] ∧
    targetWords (Evm.run compiledShared.code machine)
      [0, 127, 1, 2, 3, 4, 256, 257, 258, 259, 260, 261, 262] =
      some [77, 263, 99, 77, 256, 256, 256, 3, 67, 127, 254, 0, 1, 238] := by decide +kernel

/-- A callee-local allocation escapes after private-frame dropping and remains
separate from both older aliases; writing the result does not mutate the old buffer. -/
theorem escape_observations :
    sourceRefs ((program escaping).run initial) = some [3, 2, 0, 0, 77] ∧
    targetWords (Evm.run compiledEscape.code machine)
      [0, 127, 1, 2, 3, 4, 256, 257, 258, 259, 260, 261, 262, 263] =
      some [77, 264, 99, 77, 256, 256, 261, 3, 66, 0, 254, 0, 2, 67, 136] := by decide +kernel

/-- The public branch's full state/base/allocator relation is inhabited, not
only an independent execution observation or conditional certificate. -/
theorem shared_completed : ∃ o m' base',
    (program shared).run initial = .ok o ∧ Evm.run compiledShared.code machine = .ok m' 0 ∧
    m'.stack = machine.stack ∧ StateRepr 1 1 128 compiledShared.frag o.st base' m' ∧
    BaseExtends initial.H bases base' ∧
    GrowsAllocator 1 128 (compiledShared.allocationCost initial) initial bases machine o.st base' m' := by
  have hs : ((program shared).run initial).toOption.isSome = true := by decide +kernel
  cases ho : (program shared).run initial with
  | error e => rw [ho] at hs; cases hs
  | ok o =>
    obtain ⟨m', base', ht, hk, hr, hb, ha⟩ := completed_transport compiledShared
      (by decide +kernel) shared_input (by decide +kernel) o ho
    exact ⟨o, m', base', rfl, ht, hk, hr, hb, ha⟩

private def stored : Evm.Out → Option Nat
  | .ok m _ => some (m.store (.root 0))
  | _ => none

/-- Actual compiler and intrinsic writes preserve the caller's nonzero store
value; no failing-state rollback or external-world relation is inferred. -/
theorem store_observations :
    stored (Evm.run compiledShared.code machine) = some 9 ∧
    stored (Evm.run compiledEscape.code machine) = some 9 := by decide +kernel

theorem reached_costs : compiledShared.allocationCost initial = 7 ∧
    compiledEscape.allocationCost initial = 8 ∧
    compiledFailure.allocationCost initial = 5 := by decide +kernel

theorem completed_failure : (program failing).run initial = .error .revert ∧
    Evm.run compiledFailure.code machine = .revert := by
  constructor
  · have hs : ((program failing).run initial).halt? = some .revert := by decide +kernel
    cases hr : (program failing).run initial with
    | error e => rw [hr] at hs; cases hs; rfl
    | ok o => rw [hr] at hs; cases hs
  · exact Evm.Out.eq_revert (by decide +kernel)

/-- Expanded need includes argument, default return and clause-private locals,
not merely the four locals remaining after the call. -/
theorem required_frames : compiledShared.requiredFrame = 6 ∧
    compiledEscape.requiredFrame = 6 ∧ compiledFailure.requiredFrame = 6 ∧
    compiledEmpty.requiredFrame = 6 ∧ compiledWide.requiredFrame = 6 := by decide +kernel

/-- Exact expanded-frame and capacity premises remain necessary. -/
theorem short_frame_refused : ¬ compiledShared.Input 1 1 bases initial machine := by
  intro h
  have hf := ((compiledShared.memoryCalls_input (by decide +kernel) 1 1 bases initial machine).mp h).2.1
  have hn : 0 < compiledShared.requiredFrame := by decide +kernel
  omega
private def tooFull := writeMachine machine 0 (.val (wmod (W - 7)))
theorem capacity_refused : ¬ compiledShared.Input 1 128 bases initial tooFull := by
  intro h
  have hi := ((compiledShared.memoryCalls_input (by decide +kernel) 1 128 bases initial tooFull).mp h).2.2
  rcases hi with hz | ⟨_, cursor, ha, hs⟩
  · rw [reached_costs.1] at hz; cases hz
  · have he : cursor = wmod (W - 7) := Word.val.inj ha.arrays.free.cell.symm
    subst cursor
    rw [reached_costs.1] at hs
    have hn : ¬ (wmod (W - 7)).val + 7 < W := by decide +kernel
    exact hn hs

private def recursive : Prog C [] [] := .cons (.callRec "recursive" 1 .nil .none (fun _ => .nil)) .nil
private def externalCall : Prog C [] [] :=
  .cons (.tryCall ⟨.lit 1 rfl, "other", []⟩ .nil .nil .nil .none .nil .nil .nil .nil false) .nil
theorem unsupported_calls_refused :
    (Compiler.compile 1 (Frag.init []) recursive).isSome = false ∧
    (Compiler.compile 1 (Frag.init []) externalCall).isSome = false := by decide +kernel

private def returnedWords : Evm.Out → Option (List UInt8)
  | .ok m _ => do
    let ptr ← match m.mem 4 with | .val v => some v.val | .slot _ => none
    let n ← match m.mem ptr with | .val v => some v.val | .slot _ => none
    if n ≠ 3 then none else
    [1, 2, 3].mapM fun i => match m.mem (ptr + i) with
      | .val v => if v.val < 256 then some (UInt8.ofNat v.val) else none
      | .slot _ => none
  | _ => none

/-- Observe the returned target pointer and its range-checked word cells, then
consume the existing Source/Error byte agreement and actual reason decoder.
This does not run a byte-addressed encoder over target memory. -/
theorem returned_error_observation :
    returnedWords (Evm.run compiledShared.code machine) = some [67, 127, 254] ∧
    Source.errorData [67, 127, 254] = Semantics.encodeError [67, 127, 254] ∧
    (returnedWords (Evm.run compiledShared.code machine)).bind
      (fun bs => CatchKind.reason.decode (Source.errorData bs)) = some [67, 127, 254] := by
  have hw : returnedWords (Evm.run compiledShared.code machine) = some [67, 127, 254] := by decide +kernel
  refine ⟨hw, PublishedLayout.source_error_bytes _, ?_⟩
  rw [hw, Option.bind_some, PublishedLayout.source_error_bytes]
  exact catch_error _ (by decide +kernel)

private def sourceStored (res : TRes (Solidity.Out C [] Output)) : Option Nat := do
  let o ← res.toOption
  let v ← ((Val.read (.root "saved" rfl) : Val C Output .uint).evalT o.st).toOption
  pure v.1.toNat

theorem source_store_observations :
    sourceStored ((program shared).run initial) = some 9 ∧
    sourceStored ((program escaping).run initial) = some 9 := by decide +kernel

/-- An unset-by-body default empty return is a real reference; the caller's
post-call indexed write refuses. Returning the old parameter instead would pass. -/
theorem empty_return_failure :
    ((program emptyReturn).run initial).halt? = some .revert ∧
    (Evm.run compiledEmpty.code machine).isRevert = true ∧
    compiledEmpty.allocationCost initial = 5 := by decide +kernel

/-- The compiler accepts an intrinsic uint cell 300. The three-byte observation
refuses it, rather than silently converting it modulo256 or declaring source
byte-profile coverage. A different return length is also outside this observer. -/
theorem byte_observation_negatives :
    returnedWords (Evm.run compiledWide.code machine) = none ∧
    returnedWords (Evm.run compiledEscape.code machine) = none ∧
    sourceRefs ((program wideReturn).run initial) = some [2, 0, 0, 0, 77] := by decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.empty_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_agrees
/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.wide_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wide_agrees
/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.empty_return_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_return_failure
/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.byte_observation_negatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms byte_observation_negatives

/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.memory_calls_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memory_calls_rep
/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.completed_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms completed_transport
/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.shared_completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shared_completed
/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.escape_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms escape_agrees
/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.returned_error_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms returned_error_observation
/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.shared_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shared_observations
/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.escape_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms escape_observations
/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.completed_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms completed_failure
/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.short_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_frame_refused
/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.capacity_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity_refused
/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.required_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms required_frames

end Solidity.Backend.AbiWorld.CompiledMemoryCalls
