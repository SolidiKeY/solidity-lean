import Solidity.Backend.Passes.MappedTail

/-! Three independently compiled stages. The second physical link is a
family at the first stage's actual reached state, machine and selected map.
No preservation equality or replacement source relation is assumed. -/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ Ω : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ} {R : Prog C Ξ Ω}

/-- A third Input is transported from the second MappedOutput, after the
first boundary has selected its actual state and map. -/
def ReachedMappedLink (a : Compilation b F P) (d : Compilation b a.frag Q)
    (e : Compilation b d.frag R) (L frame : Nat) (base : Nat → Fin W)
    (σ : State C Γ) (m : Machine) : Prop :=
  ∀ (o : Solidity.Out C σ.H Δ) (mid : Machine) (mb : Nat → Fin W),
    P.run σ = .ok o → run a.code m = .ok mid 0 →
    MappedOutput a (L + Evm.Prog.pushes P) frame base σ m o.st mid mb →
    MappedBoundaryLink d e (L + Evm.Prog.pushes P) frame mb o.st mid

/-- A third allocating stage obtains its capacity from the first stage's
actual allocator growth and a reached total budget. The second binary link
then consumes its own actual output map and derives the final Input. -/
theorem memory_third_budgeted_link
    (a : Memory.CompiledProg b F P) (d : Memory.CompiledProg b a.frag Q)
    (e : Memory.CompiledProg b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hframe : b + Memory.frameNeedProg R ≤ frame)
    (budget : ∀ (o : Solidity.Out C σ.H Δ) (u : Solidity.Out C o.st.H Ξ),
      P.run σ = .ok o → Q.run o.st = .ok u →
      Memory.AllocationInput b frame
        (a.cert.cost σ + (d.cert.cost o.st + e.cert.cost u.st)) σ base m) :
    ReachedMappedLink (.memory a) (.memory d) (.memory e) L frame base σ m := by
  intro o mid mb hs _ ha
  apply memory_budgeted_mapped_link d e hframe
  intro u hu
  exact ha.2.2.nextInput (budget o u hs hu)

/-- All three actual executions, maps and full branch-indexed relations.
Both parenthesizations end at the same actual terminal machine. -/
theorem compilation_triple_success
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m)
    (ad : MappedBoundaryLink a d L frame base σ m)
    (de : ReachedMappedLink a d e L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    {u : Solidity.Out C o.st.H Ξ} (hu : Q.run o.st = .ok u)
    {v : Solidity.Out C u.st.H Ω} (hv : R.run u.st = .ok v) :
    ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine),
      run a.code m = .ok mid 0 ∧ run d.code mid = .ok next 0 ∧
      run e.code next = .ok final 0 ∧
      run ((a.code ++ d.code) ++ e.code) m = .ok final 0 ∧
      run (a.code ++ (d.code ++ e.code)) m = .ok final 0 ∧
      final.stack = m.stack ∧
      MappedOutput a (L + Evm.Prog.pushes P) frame base σ m o.st mid mb ∧
      MappedOutput d ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
        frame mb o.st mid u.st next nb ∧
      MappedOutput e (((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) + Evm.Prog.pushes R)
        frame nb u.st next v.st final ob := by
  obtain ⟨mid, hm, hstack, hrep⟩ := compilation_success a hi hp hs
  obtain ⟨mb, ha⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp hrep
  obtain ⟨nb, ob, next, final, _, hn, hnf, hfstack, hd, he⟩ :=
    compilation_mapped_success d e (ad o mid mb hs hm ha) (de o mid mb hs hm ha) hq hr hu hv
  have hf : run e.code next = .ok final 0 := by
    rw [run_append_ok hn] at hnf
    exact hnf
  have hall : run (a.code ++ (d.code ++ e.code)) m = .ok final 0 := by
    rw [run_append_ok hm]
    exact hnf
  exact ⟨mb, nb, ob, mid, next, final, hm, hn, hf,
    by simpa only [List.append_assoc] using hall,
    hall, hfstack.trans hstack, ha, hd, he⟩

/-- Failure is either immediate, reached in stage two, or reached in stage
three. No later source run is required after an earlier failure. -/
theorem compilation_triple_revert_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m)
    (ad : MappedBoundaryLink a d L frame base σ m)
    (de : ReachedMappedLink a d e L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    run (a.code ++ (d.code ++ e.code)) m = .revert ↔
      TerminalFailure P σ ∨ ∃ o, P.run σ = .ok o ∧
        (TerminalFailure Q o.st ∨ ∃ u, Q.run o.st = .ok u ∧ TerminalFailure R u.st) := by
  constructor
  · intro ht
    rcases compilation_exact a hi hp with
      ⟨o, mid, hs, hm, _, hrep⟩ | ⟨hs, _⟩ | ⟨_, hm⟩
    · obtain ⟨mb, ha⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp hrep
      rw [run_append_ok hm] at ht
      exact .inr ⟨o, hs, (compilation_mapped_revert_iff d e
        (ad o mid mb hs hm ha) (de o mid mb hs hm ha) hq hr).mp ht⟩
    · exact .inl hs
    · have hf := run_append_fault (c₂ := d.code ++ e.code) hm
      rw [ht] at hf
      cases hf
  · rintro (hs | ⟨o, hs, hrest⟩)
    · exact run_append_revert ((compilation_revert_iff a hi hp).mpr hs)
    · obtain ⟨mid, hm, _, hrep⟩ := compilation_success a hi hp hs
      obtain ⟨mb, ha⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp hrep
      rw [run_append_ok hm]
      exact (compilation_mapped_revert_iff d e
        (ad o mid mb hs hm ha) (de o mid mb hs hm ha) hq hr).mpr hrest

/-- Memory stages additionally compose both real allocation boundaries.
Costs are evaluated at each reached intrinsic state, never the initial
state again. Payment freedom is not added to the memory certificate. -/
theorem memory_triple_resources
    (a : Memory.CompiledProg b F P) (d : Memory.CompiledProg b a.frag Q)
    (e : Memory.CompiledProg b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : (Compilation.memory a).Input L frame base σ m)
    (ad : MappedBoundaryLink (.memory a) (.memory d) L frame base σ m)
    (de : ReachedMappedLink (.memory a) (.memory d) (.memory e) L frame base σ m)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    {u : Solidity.Out C o.st.H Ξ} (hu : Q.run o.st = .ok u)
    {v : Solidity.Out C u.st.H Ω} (hv : R.run u.st = .ok v) :
    ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine),
      run a.code m = .ok mid 0 ∧
      run (a.code ++ d.code ++ e.code) m = .ok final 0 ∧
      final.stack = m.stack ∧
      MappedOutput (.memory a) (L + Evm.Prog.pushes P) frame base σ m o.st mid mb ∧
      MappedOutput (.memory d) ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
        frame mb o.st mid u.st next nb ∧
      MappedOutput (.memory e) (((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) + Evm.Prog.pushes R)
        frame nb u.st next v.st final ob ∧
      Memory.BaseExtends σ.H base ob ∧
      Memory.BaseExtends o.st.H mb ob ∧
      Memory.GrowsAllocator b frame (a.cert.cost σ + (d.cert.cost o.st + e.cert.cost u.st))
        σ base m v.st ob final := by
  obtain ⟨mb, mid, hm, hstack, ha⟩ := memory_mapped_success a hi hs
  obtain ⟨nb, ob, next, final, _, ht, hfstack, hd, he, hb, hg⟩ :=
    memory_sequence_resources d e (ad o mid mb hs hm ha) (de o mid mb hs hm ha) hu hv
  refine ⟨mb, nb, ob, mid, next, final, hm, ?_, hfstack.trans hstack,
    ha, hd, he, Memory.BaseExtends.trans o.ext ha.2.1 hb, hb,
    Memory.GrowsAllocator.comp ha.2.2 hg⟩
  rw [List.append_assoc, run_append_ok hm]
  exact ht

/-- Intrinsic source success under both associations; extension proofs
are composed in their original dependent order. -/
theorem triple_source_success (σ : State C Γ)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    {u : Solidity.Out C o.st.H Ξ} (hu : Q.run o.st = .ok u)
    {v : Solidity.Out C u.st.H Ω} (hv : R.run u.st = .ok v) :
    ((P.join Q).join R).run σ = .ok ⟨v.st, (o.ext.trans u.ext).trans v.ext⟩ ∧
    (P.join (Q.join R)).run σ = .ok ⟨v.st, o.ext.trans (u.ext.trans v.ext)⟩ := by
  have hq : (Q.join R).run o.st = .ok ⟨v.st, u.ext.trans v.ext⟩ := by
    rw [DeferredSource.join_run]
    simp only [TRun.seq, hu, hv, Except.map]
  have hp : (P.join Q).run σ = .ok ⟨u.st, o.ext.trans u.ext⟩ := by
    rw [DeferredSource.join_run]
    simp only [TRun.seq, hs, hu, Except.map]
  constructor
  · rw [DeferredSource.join_run]
    simp only [TRun.seq, hp, hv, Except.map]
  · rw [DeferredSource.join_run]
    simp only [TRun.seq, hs, hq, Except.map]

/-- Output stack equality from the actual successful compiler execution.
This uses determinism, not merely the branch representation relation. -/
private theorem reached_stack (a : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m n : Machine}
    (hi : a.Input L frame base σ m) (hp : Evm.Prog.pays P = false)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    (ht : run a.code m = .ok n 0) : n.stack = m.stack := by
  obtain ⟨actual, ha, hstack, _⟩ := compilation_success a hi hp hs
  have he : actual = n := by
    have h := Evm.Out.ok.inj (ha.symm.trans ht)
    exact h.1
  cases he
  exact hstack

/-- All three selected maps and machines precede the saved-tail quantifier.
Each boundary's complete mapped relation is transported, and each individual
stage as well as both code associations actually executes at every tail. -/
theorem compilation_triple_shared
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m) (hempty : m.stack = [])
    (ad : MappedBoundaryLink a d L frame base σ m)
    (de : ReachedMappedLink a d e L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    {u : Solidity.Out C o.st.H Ξ} (hu : Q.run o.st = .ok u)
    {v : Solidity.Out C u.st.H Ω} (hv : R.run u.st = .ok v) :
    ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine),
      mid.stack = [] ∧ next.stack = [] ∧ final.stack = [] ∧ ∀ tail,
      run a.code {m with stack := tail} = .ok {mid with stack := tail} 0 ∧
      run d.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
      run e.code {next with stack := tail} = .ok {final with stack := tail} 0 ∧
      run ((a.code ++ d.code) ++ e.code) {m with stack := tail} =
        .ok {final with stack := tail} 0 ∧
      run (a.code ++ (d.code ++ e.code)) {m with stack := tail} =
        .ok {final with stack := tail} 0 ∧
      MappedOutput a (L + Evm.Prog.pushes P) frame base σ {m with stack := tail}
        o.st {mid with stack := tail} mb ∧
      MappedOutput d ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
        frame mb o.st {mid with stack := tail} u.st {next with stack := tail} nb ∧
      MappedOutput e (((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) + Evm.Prog.pushes R)
        frame nb u.st {next with stack := tail} v.st {final with stack := tail} ob := by
  obtain ⟨mb, nb, ob, mid, next, final, hm, hn, hf, hl, ht, hstack, ha, hd, he⟩ :=
    compilation_triple_success a d e hi ad de hp hq hr hs hu hv
  have sm : mid.stack = [] := (reached_stack a hi hp hs hm).trans hempty
  have sn : next.stack = [] :=
    (reached_stack d (ad o mid mb hs hm ha) hq hu hn).trans sm
  have sf : final.stack = [] := hstack.trans hempty
  refine ⟨mb, nb, ob, mid, next, final, sm, sn, sf, ?_⟩
  intro tail
  have transport (code : List Instr) (x y : Machine)
      (hx : x.stack = []) (hy : y.stack = []) (h : run code x = .ok y 0) :
      run code {x with stack := tail} = .ok {y with stack := tail} 0 := by
    have hh := run_tail code x tail (by rw [h]; intro bad; cases bad)
    simpa only [h, appendOut, appendTail, hx, hy, List.nil_append] using hh
  exact ⟨transport _ _ _ hempty sm hm, transport _ _ _ sm sn hn,
    transport _ _ _ sn sf hf, transport _ _ _ hempty sf hl,
    transport _ _ _ hempty sf ht, mapped_output_stack a ha tail tail,
    mapped_output_stack d hd tail tail, mapped_output_stack e he tail tail⟩

end Solidity.Backend.Passes
