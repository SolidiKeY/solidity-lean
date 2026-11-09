import Solidity.Backend.Passes.WholeProgram.Refusal
import Solidity.Backend.Passes.MappedTail
import Solidity.Backend.Payments.CompilerExact

/-!
# The whole-program intrinsic stage of the checked compiler entry

For every program `Compiler.compile` accepts, on each of its eleven branches:
the static check refuses or the explicit `Input` (the world premise) gives
`AgreesExact`; success and revert transport; saved-tail
independence with one shared canonical machine; and typed sequencing of two
accepted programs through `BoundaryLink` / `MappedBoundaryLink` (success and
terminal failure for both).

None of these carries the payment-freedom premise `Evm.Prog.pays P = false`
of the generic Passes results (`Boundary`, `Sequence`, `EmittedTail`,
`MappedTail`, `MappedSequence`): `correct_exact`
(`Backend/Payments/CompilerExact.lean`) has no payment disjunct, so each
proof here is the earlier one with `correct_exact` in place of
`compilation_exact`. `Input` is unchanged; its dynamic part (a machine and
base map representing the typed state) stays an explicit hypothesis.
-/
namespace Solidity.Backend.Passes.WholeProgram

open Solidity.Evm Solidity.Evm.Compiler

variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}

/-- `correct_exact` with `AgreesExact` unfolded: the three outcomes of the
pays-gated `compilation_exact`, here without its payment premise. -/
theorem exact (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m) :
    (∃ o m', P.run σ = .ok o ∧ run result.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧
      result.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m') ∨
    ((P.run σ = .error .revert ∨ (P.asserts = true ∧ P.run σ = .error .panic)) ∧
      run result.code m = .revert) ∨
    (P.run σ = .error .diverge ∧ run result.code m = .fault) :=
  Compilation.correct_exact result hi

/-- **Whole-program intrinsic stage.** For a program the checked entry
accepts: if the static check fires at `L`/`frame` no state is admitted, and
every state and machine meeting its `Input` agree exactly. Both conjuncts hold
for any `Compilation`; the acceptance premise fixes the result the endpoint
names and is not used by the proof. -/
theorem whole_program {result : Compilation b F P}
    (_accepted : Compiler.compile b F P = some result) :
    (staticRefused result L frame = true →
      ∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
        ¬ result.Input L frame base σ m) ∧
    (∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
      result.Input L frame base σ m → result.AgreesExact L frame base σ m) :=
  ⟨fun h _ _ _ => staticRefused_input result h,
    fun _ _ _ hi => Compilation.correct_exact result hi⟩

/-- A successful typed run is matched by a successful machine run. -/
theorem success (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o) :
    ∃ m', run result.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      result.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m' :=
  Compilation.compile_success result hi hs

/-- Two-sided coarse revert transport, with panic visible in the source. -/
theorem revert_iff (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m) :
    run result.code m = .revert ↔
      P.run σ = .error .revert ∨ (P.asserts = true ∧ P.run σ = .error .panic) := by
  refine ⟨Compilation.revert_exact result hi, fun hs => ?_⟩
  rcases exact result hi with ⟨_, _, hs', _, _, _⟩ | ⟨_, ht⟩ | ⟨hs', _⟩
  · rcases hs with hs | ⟨_, hs⟩ <;> rw [hs] at hs' <;> cases hs'
  · exact ht
  · rcases hs with hs | ⟨_, hs⟩ <;> rw [hs] at hs' <;> cases hs'

/-- Every saved tail: success with that exact tail and the full `Rep`. -/
theorem success_tail (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o) (tail : List Word) :
    ∃ m', run result.code {m with stack := tail} = .ok m' 0 ∧
      m'.stack = tail ∧ result.Rep (L + Evm.Prog.pushes P) frame base
        σ {m with stack := tail} o.st m' :=
  success result (compilation_input_stack result hi tail) hs

/-- **Saved-tail independence**: the exact outcome and every non-stack field
do not depend on the saved tail. -/
theorem tail_exact (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m) (tail : List Word) :
    run result.code {m with stack := tail} =
      replaceOutStack tail (run result.code {m with stack := []}) := by
  rcases exact result (compilation_input_stack result hi []) with
    ⟨o, canonical, hs, ht, hstack, hr⟩ | ⟨hs, ht⟩ | ⟨hs, ht⟩
  · have he := run_tail result.code {m with stack := []} tail
      (by rw [ht]; intro h; cases h)
    rw [ht]
    simpa only [ht, appendTail, appendOut, replaceOutStack, hstack,
      List.nil_append] using he
  · have he := run_tail result.code {m with stack := []} tail
      (by rw [ht]; intro h; cases h)
    rw [ht]
    simpa only [ht, appendTail, appendOut, replaceOutStack, List.nil_append] using he
  · rw [ht]
    change run result.code {m with stack := tail} = .fault
    rcases exact result (compilation_input_stack result hi tail) with
      ⟨o, out, hs', _, _, _⟩ | ⟨hs' | ⟨_, hs'⟩, _⟩ | ⟨_, ht'⟩
    · rw [hs] at hs'
      cases hs'
    · rw [hs] at hs'
      cases hs'
    · rw [hs] at hs'
      cases hs'
    · exact ht'

/-- Equality after erasing only the returned stack, for any two tails. -/
theorem two_tails (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m) (left right : List Word) :
    replaceOutStack [] (run result.code {m with stack := left}) =
      replaceOutStack [] (run result.code {m with stack := right}) := by
  rw [tail_exact result hi left, tail_exact result hi right]
  cases run result.code {m with stack := []} <;> rfl

/-- **One shared canonical machine** for every saved tail, with the full
branch-specific `Rep` per run. -/
theorem success_shared (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o) :
    ∃ canonical, run result.code {m with stack := []} = .ok canonical 0 ∧
      canonical.stack = [] ∧
      ∀ tail, run result.code {m with stack := tail} =
          .ok {canonical with stack := tail} 0 ∧
        result.Rep (L + Evm.Prog.pushes P) frame base σ {m with stack := tail}
          o.st {canonical with stack := tail} := by
  obtain ⟨canonical, ht, hstack, _⟩ := success_tail result hi hs []
  refine ⟨canonical, ht, hstack, fun tail => ?_⟩
  have he := tail_exact result hi tail
  rw [ht] at he
  change run result.code {m with stack := tail} =
    .ok {canonical with stack := tail} 0 at he
  obtain ⟨actual, ha, _, hr⟩ := success_tail result hi hs tail
  have hm : actual = {canonical with stack := tail} :=
    (Evm.Out.ok.inj (ha.symm.trans he)).1
  exact ⟨he, hm ▸ hr⟩

/-- The shared canonical machine with one fixed selected output map. -/
theorem success_shared_mapped (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o) :
    ∃ canonical outBase, run result.code {m with stack := []} = .ok canonical 0 ∧
      canonical.stack = [] ∧ ∀ tail,
        run result.code {m with stack := tail} = .ok {canonical with stack := tail} 0 ∧
        MappedOutput result (L + Evm.Prog.pushes P) frame base σ {m with stack := tail}
          o.st {canonical with stack := tail} outBase := by
  obtain ⟨canonical, ht, hstack, hr⟩ := success_tail result hi hs []
  obtain ⟨outBase, hm⟩ := (mapped_output_iff result _ _ _ _ _ _ _).mp hr
  refine ⟨canonical, outBase, ht, hstack, fun tail => ?_⟩
  have he := tail_exact result hi tail
  rw [ht] at he
  exact ⟨he, mapped_output_stack result hm tail tail⟩

/-- **Typed sequencing of two accepted programs**: both stages succeed on
the joined intrinsic program, retaining both representation witnesses. -/
theorem sequence_success
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base nextBase : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L frame base σ m)
    (link : BoundaryLink left right L frame base nextBase σ m)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    {o' : Solidity.Out C o.st.H Ξ} (hs' : Q.run o.st = .ok o') :
    ∃ m' m'',
      (P.join Q).run σ = .ok ⟨o'.st, o.ext.trans o'.ext⟩ ∧
      run left.code m = .ok m' 0 ∧
      run (left.code ++ right.code) m = .ok m'' 0 ∧
      m''.stack = m.stack ∧
      left.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m' ∧
      right.Rep ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
        frame nextBase o.st m' o'.st m'' := by
  obtain ⟨m', ht, hstack, hr⟩ := success left hi hs
  obtain ⟨m'', ht', hstack', hr'⟩ := success right (link o m' hs ht hr) hs'
  refine ⟨m', m'', ?_, ht, ?_, hstack'.trans hstack, hr, hr'⟩
  · rw [DeferredSource.join_run]
    simp only [TRun.seq, hs, hs', Except.map]
  · rw [run_append_ok ht]
    exact ht'

/-- Two-sided terminal failure transport for two sequenced accepted programs. -/
theorem sequence_revert_iff
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base nextBase : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L frame base σ m)
    (link : BoundaryLink left right L frame base nextBase σ m) :
    run (left.code ++ right.code) m = .revert ↔
      TerminalFailure P σ ∨ ∃ o, P.run σ = .ok o ∧ TerminalFailure Q o.st := by
  constructor
  · intro ht
    rcases exact left hi with ⟨o, m', hs, ht', _, hr⟩ | ⟨hs, _⟩ | ⟨_, ht'⟩
    · rw [run_append_ok ht'] at ht
      exact .inr ⟨o, hs, (revert_iff right (link o m' hs ht' hr)).mp ht⟩
    · exact .inl hs
    · have hf : run (left.code ++ right.code) m = .fault := run_append_fault ht'
      rw [ht] at hf
      cases hf
  · rintro (hs | ⟨o, hs, hfail⟩)
    · exact run_append_revert ((revert_iff left hi).mpr hs)
    · obtain ⟨m', ht, _, hr⟩ := success left hi hs
      rw [run_append_ok ht]
      exact (revert_iff right (link o m' hs ht hr)).mpr hfail

/-- Sequencing with the intermediate output map named and shared. -/
theorem sequence_mapped_success
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L frame base σ m)
    (link : MappedBoundaryLink left right L frame base σ m)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    {o' : Solidity.Out C o.st.H Ξ} (hs' : Q.run o.st = .ok o') :
    ∃ midBase outBase mid final,
      (P.join Q).run σ = .ok ⟨o'.st, o.ext.trans o'.ext⟩ ∧
      run left.code m = .ok mid 0 ∧
      run (left.code ++ right.code) m = .ok final 0 ∧
      final.stack = m.stack ∧
      MappedOutput left (L + Evm.Prog.pushes P) frame base σ m o.st mid midBase ∧
      MappedOutput right ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
        frame midBase o.st mid o'.st final outBase := by
  obtain ⟨mid, ht, hstack, hr⟩ := success left hi hs
  obtain ⟨midBase, hleft⟩ :=
    (mapped_output_iff left (L + Evm.Prog.pushes P) frame base σ m o.st mid).mp hr
  obtain ⟨final, ht', hstack', hr'⟩ := success right (link o mid midBase hs ht hleft) hs'
  obtain ⟨outBase, hright⟩ :=
    (mapped_output_iff right ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
      frame midBase o.st mid o'.st final).mp hr'
  refine ⟨midBase, outBase, mid, final, ?_, ht, ?_, hstack'.trans hstack, hleft, hright⟩
  · rw [DeferredSource.join_run]
    simp only [TRun.seq, hs, hs', Except.map]
  · rw [run_append_ok ht]
    exact ht'

/-- Two-sided terminal failure through the explicit-map boundary. -/
theorem sequence_mapped_revert_iff
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L frame base σ m)
    (link : MappedBoundaryLink left right L frame base σ m) :
    run (left.code ++ right.code) m = .revert ↔
      TerminalFailure P σ ∨ ∃ o, P.run σ = .ok o ∧ TerminalFailure Q o.st := by
  constructor
  · intro ht
    rcases exact left hi with ⟨o, mid, hs, hm, _, hr⟩ | ⟨hs, _⟩ | ⟨_, hm⟩
    · obtain ⟨mb, hr'⟩ :=
        (mapped_output_iff left (L + Evm.Prog.pushes P) frame base σ m o.st mid).mp hr
      rw [run_append_ok hm] at ht
      exact .inr ⟨o, hs, (revert_iff right (link o mid mb hs hm hr')).mp ht⟩
    · exact .inl hs
    · have hf := run_append_fault (c₂ := right.code) hm
      rw [ht] at hf
      cases hf
  · rintro (hs | ⟨o, hs, hfail⟩)
    · exact run_append_revert ((revert_iff left hi).mpr hs)
    · obtain ⟨mid, hm, _, hr⟩ := success left hi hs
      obtain ⟨mb, hr'⟩ :=
        (mapped_output_iff left (L + Evm.Prog.pushes P) frame base σ m o.st mid).mp hr
      rw [run_append_ok hm]
      exact (revert_iff right (link o mid mb hs hm hr')).mpr hfail

/-- The checked entry sees only the joined program, so the two associations
of a three-stage program compile to the same code (or are both refused). -/
theorem compile_codes_assoc {Ω : Ctx} (F : Frag Γ)
    (P : Prog C Γ Δ) (Q : Prog C Δ Ξ) (R : Prog C Ξ Ω) :
    (Compiler.compile b F ((P.join Q).join R)).map (·.code) =
      (Compiler.compile b F (P.join (Q.join R))).map (·.code) := by
  rw [typed_sequencing_assoc]

end Solidity.Backend.Passes.WholeProgram
