import Solidity.Semantics.RunFuel

/-!
# Revert data read from typed memory

A memory operand reads the current object, including writes through aliases.
The result is an immutable byte list which survives callee heap rollback.
Finite execution certificates describe the unbounded run when they halt
without exhausting their loop fuel.
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-- A set memory local reverts with its current bytes, encoded for its kind. -/
theorem RevPart.evalT_mem (σ : State C Γ) (kind : CatchKind)
    (src : Idx Γ (.mem bytesR)) (r : HRef σ.H bytesR)
    (h : TEnv.get src σ.env = some r) :
    (RevPart.mem kind src).evalT σ = .ok
      (let bs := (σ.heap.get r).1.map (fun v => UInt8.ofNat v.val.toNat)
       match kind with | .raw => bs | .reason => Semantics.encodeError bs) := by
  cases kind <;> simp only [RevPart.evalT, MPath.mvalT, h, bind, Except.bind, pure, Except.pure]

/-- A finite non-divergent halt is the exact halt of the unbounded run. -/
theorem TRes.Approx.halt_eq {α : Type} {a b : TRes α} (hab : TRes.Approx a b)
    {e : THalt} (he : e ≠ .diverge) (h : a.halt? = some e) : b.halt? = some e := by
  apply Eq.trans (congrArg TRes.halt? (hab.eq ?_).symm) h
  intro hd
  rw [hd] at h
  exact he (Option.some.inj h).symm

/-- A sole memory operand produces exactly these bytes, with the empty raw
buffer represented by the ordinary empty-data revert. -/
theorem TRun.revertData_mem (σ : State C Γ) (kind : CatchKind)
    (src : Idx Γ (.mem bytesR)) (r : HRef σ.H bytesR)
    (h : TEnv.get src σ.env = some r) :
    TRun.revertData [.mem kind src] σ = .error
      (THalt.ofData (let bs := (σ.heap.get r).1.map (fun v => UInt8.ofNat v.val.toNat)
       match kind with | .raw => bs | .reason => Semantics.encodeError bs)) := by
  simp only [TRun.revertData, List.mapM_cons, RevPart.evalT_mem σ kind src r h,
    List.mapM_nil, bind, Except.bind, pure, Except.pure, List.flatten_cons,
    List.flatten_nil, List.append_nil]

/-- An unset memory source fails before producing any data. -/
theorem RevPart.evalT_mem_unset (σ : State C Γ) (kind : CatchKind)
    (src : Idx Γ (.mem bytesR)) (h : TEnv.get src σ.env = none) :
    (RevPart.mem kind src).evalT σ = .error .revert := by
  simp only [RevPart.evalT, MPath.mvalT, h, bind, Except.bind]

/-- The loop bound is absent from the certified execution conclusion. -/
theorem Prog.run_halt_of_runF {Γ' : Ctx} (P : Prog C Γ Γ') (σ : State C Γ)
    (fuel : Nat) {e : THalt} (he : e ≠ .diverge)
    (h : (P.runF fuel σ).halt? = some e) : (Prog.run σ P).halt? = some e :=
  (P.runF_approx fuel σ).halt_eq he h

/-- A successful bounded run also certifies successful unbounded execution. -/
theorem TRes.Approx.returned {α : Type} {a b : TRes α} (hab : TRes.Approx a b)
    (h : a.toOption.isSome = true) : b.toOption.isSome = true := by
  rcases hab with hd | rfl
  · rw [hd] at h; cases h
  · exact h

end Solidity
