import Solidity.Lowering.V07.ReferenceCapture

/-! Capturing a reference around an actual local rebind. This retains typed
HRef identity, not a storage/value snapshot. No heap allocation, referent
write, copy, free/delete or source-graph admission is implemented here. -/
namespace Solidity.Lowering.V07

theorem singleton_run {C : Contract} {Γ Δ : Ctx} (target : State C Γ) (s : Stmt C Γ Δ) :
    (Prog.cons s .nil).run target = s.run target := by
  change TRun.seq s.runR (Prog.nil : Prog C Δ Δ).runR target = s.runR target
  unfold TRun.seq
  cases run : s.runR target with
  | error err => rfl
  | ok out => rfl

theorem memory_declaration_run {C : Contract} {Γ : Ctx} {R : RefTy}
    (target : State C Γ) (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (r : HRef target.H R) (read : TEnv.get i target.env = some r) :
    (Stmt.declMem R (.user "v07_reference") (some (.alias (.var i hm))) rfl hm).run target =
      .ok (⟨target.push (t := .mem R) (some r),List.prefix_refl _⟩) := by
  have h := memory_capture_run target i hm r read
  change (Prog.cons (.declMem R (.user "v07_reference") (some (.alias (.var i hm))) rfl hm) .nil).run target = _ at h
  rw [singleton_run] at h
  exact h

theorem memory_rebind_run {C : Contract} {Γ : Ctx} {R : RefTy}
    (target : State C Γ) (i a : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (r : HRef target.H R) (read : TEnv.get a target.env = some r) :
    (Stmt.rebindMem i (.alias (.var a hm))).run target =
      .ok (⟨target.setLocal i (some r),List.prefix_refl _⟩) := by
  have rhs : (MRhs.alias (.var a hm)).evalT target =
      .ok (⟨target,List.prefix_refl _,r⟩ : Grew C Γ target.H (HRef · R)) := by
    dsimp only [MRhs.evalT,MPath.mvalT]
    rw [read]
    rfl
  change (do
    let g ← (MRhs.alias (.var a hm)).evalT target
    pure (⟨g.st.setLocal i (some g.val),g.ext⟩ : Out C target.H Γ)) = _
  rw [rhs]
  rfl

def memoryAssignReadPrefix {C : Contract} {Γ : Ctx} {R : RefTy}
    (pipeline : Roadmap.Pipeline) (i a : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    Prog C Γ (.mem R :: .mem R :: Γ) :=
  match pipeline with
  | .legacy => .cons (.declMem R (.user "v07_reference") (some (.alias (.var i hm))) rfl hm)
      (.cons (.rebindMem (.there i) (.alias (.var (.there a) hm)))
        (.cons (.declMem R (.user "v07_reference") (some (.alias (.var (.there i) hm))) rfl hm) .nil))
  | .viaIR => .cons (.rebindMem i (.alias (.var a hm)))
      (.cons (.declMem R (.user "v07_reference") (some (.alias (.var i hm))) rfl hm)
        (.cons (.declMem R (.user "v07_reference") (some (.alias (.var (.there i) hm))) rfl hm) .nil))

theorem memory_assign_read_prefix_run {C : Contract} {Γ : Ctx} {R : RefTy}
    (pipeline : Roadmap.Pipeline) (target : State C Γ) (i a : Idx Γ (.mem R))
    (hm : (Ty.ref R).mapFree = true) (old assigned : HRef target.H R)
    (readI : TEnv.get i target.env = some old) (readA : TEnv.get a target.env = some assigned) :
    (memoryAssignReadPrefix pipeline i a hm).run target =
      .ok (⟨((target.setLocal i (some assigned)).push (t := .mem R)
        (some (if pipeline = .legacy then old else assigned))).push (t := .mem R) (some assigned),
        List.prefix_refl _⟩) := by
  cases pipeline
  · unfold memoryAssignReadPrefix
    rw [Prog.run_cons_ok (memory_declaration_run target i hm old readI)]
    rw [Prog.run_cons_ok (memory_rebind_run (target.push (t := .mem R) (some old))
      (.there i) (.there a) hm assigned readA)]
    rw [Prog.run_cons_ok (memory_declaration_run
      ((target.push (t := .mem R) (some old)).setLocal (.there i) (some assigned))
      (.there i) hm assigned (TEnv.get_set _ _ _)),Prog.run_nil]
    rfl
  · unfold memoryAssignReadPrefix
    rw [Prog.run_cons_ok (memory_rebind_run target i a hm assigned readA)]
    rw [Prog.run_cons_ok (memory_declaration_run (target.setLocal i (some assigned))
      i hm assigned (TEnv.get_set _ _ _))]
    rw [Prog.run_cons_ok (memory_declaration_run
      ((target.setLocal i (some assigned)).push (t := .mem R) (some assigned))
      (.there i) hm assigned (TEnv.get_set _ _ _)),Prog.run_nil]
    rfl

/-- Initial address/reference correspondence is an independent predicate.
Both actual operations retain it and its selected-pair alias reflection.
The input relation contains no compiler/evaluator/preservation premise. -/
theorem reference_assignment_pair_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (i a : Source.Idx srcΓ (.bytes .memory)) (j b : Idx Γ (.mem bytesR))
    (oldAddress newAddress : Nat) (old assigned : HRef target.H bytesR)
    (readI : source.1.get i = .memRef rfl oldAddress)
    (readA : source.1.get a = .memRef rfl newAddress)
    (targetI : TEnv.get j target.env = some old) (targetA : TEnv.get b target.env = some assigned)
    (R : Nat → HRef target.H bytesR → Prop) (oldRel : R oldAddress old) (newRel : R newAddress assigned)
    (aliases : oldAddress = newAddress ↔ old = assigned) :
    (Source.evalPair G F (fuel+3) (.assign (.local i) (.local a)) (.local i)).run source =
      (.ok (.val (.memRef rfl newAddress),
        .val (.memRef rfl (if G.pipeline = .legacy then oldAddress else newAddress))),
        (source.1.set i (.memRef rfl newAddress),source.2)) ∧
    (memoryAssignReadPrefix G.pipeline j b rfl).run target =
      .ok (⟨((target.setLocal j (some assigned)).push (t := .mem bytesR)
        (some (if G.pipeline = .legacy then old else assigned))).push (t := .mem bytesR) (some assigned),
        List.prefix_refl _⟩) ∧
    R (if G.pipeline = .legacy then oldAddress else newAddress)
      (if G.pipeline = .legacy then old else assigned) ∧
    (newAddress = (if G.pipeline = .legacy then oldAddress else newAddress) ↔
      assigned = (if G.pipeline = .legacy then old else assigned)) := by
  have src := source_assign_read_pair G F fuel source i a
    (.memRef rfl newAddress) (.memRef rfl oldAddress) readA readI
  refine ⟨?_,memory_assign_read_prefix_run G.pipeline target j b rfl old assigned targetI targetA,?_,?_⟩
  · cases order : G.pipeline <;> simpa only [order,reduceCtorEq,if_true,if_false] using src
  · cases G.pipeline
    · exact oldRel
    · exact newRel
  · cases G.pipeline
    · exact ⟨fun eq => (aliases.mp eq.symm).symm,fun eq => (aliases.mpr eq.symm).symm⟩
    · exact ⟨fun _ => rfl,fun _ => rfl⟩

end Solidity.Lowering.V07
