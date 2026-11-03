import Solidity.Evm.MemoryRecursiveComposition

namespace Solidity.Evm.Memory.Recursive.Composition
variable {C : Contract}

/-- One-level elimination view of the EXISTING demand relation. Generalized
recursors avoid inverting a noninjective computed fragment meet. -/
private def stmtShape {b Γ Δ F G s code} (hs : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code) : State C Γ → Nat → Prop := by
  exact StmtCert.rec
    (motive_1:=fun {Γ Δ} F G s code hs=>State C Γ → Nat → Prop)
    (motive_2:=fun {Γ Δ} F G P code hp=>State C Γ → Nat → Prop)
    (fun _ _ _=>True) (fun _ _ _ _=>True)
    (fun {Γ Δ Ξ F G K c P Q cond lc rc} hc hp hq ihp ihq σ amount=>
      (c.evalT σ=.ok true ∧ Demand hp σ amount) ∨ (c.evalT σ=.ok false ∧ Demand hq σ amount))
    (fun _ _ _ _ _ _ _=>True) (fun _ _ _=>True) (fun _ _ _ _ _ _=>True) hs

private theorem stmt_shape {b Γ Δ F G s code} {hs : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code}
    {σ amount} (demand : StmtDemand hs σ amount) : stmtShape hs σ amount := by
  exact StmtDemand.rec
    (motive_1:=fun hs σ amount _=>stmtShape hs σ amount)
    (motive_2:=fun hp σ amount _=>True)
    (fun _=>True.intro) (fun _ _=>True.intro)
    (fun condition inner ih=>Or.inl ⟨condition,inner⟩)
    (fun condition inner ih=>Or.inr ⟨condition,inner⟩)
    (fun _=>True.intro) (fun _ _ _ _=>True.intro)
    (fun _ _=>True.intro) (fun _ _ _ _=>True.intro) demand

private def progShape {b Γ Δ F G P code} (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code) : State C Γ → Nat → Prop := by
  exact ProgCert.rec
    (motive_1:=fun {Γ Δ} F G s code hs=>State C Γ → Nat → Prop)
    (motive_2:=fun {Γ Δ} F G P code hp=>State C Γ → Nat → Prop)
    (fun _ _ _=>True) (fun _ _ _ _=>True) (fun _ _ _ _ _ _ _=>True)
    (fun _ _ _ _ _ _ _=>True) (fun _ _ _=>False)
    (fun {Γ Δ Ξ F G K s P head tail} hs hp ihs ihp σ amount=>
      StmtDemand hs σ amount ∨ ∃ (out : Solidity.Out C σ.H Δ) (spent rest : Nat),
        s.run σ=.ok out ∧ StmtCost hs σ out spent ∧ Demand hp out.st rest ∧ amount=spent+rest) hp

private theorem prog_shape {b Γ Δ F G P code} {hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code}
    {σ amount} (demand : Demand hp σ amount) : progShape hp σ amount := by
  exact Demand.rec
    (motive_1:=fun hs σ amount _=>True)
    (motive_2:=fun hp σ amount _=>progShape hp σ amount)
    (fun _=>True.intro) (fun _ _=>True.intro)
    (fun _ _ _=>True.intro) (fun _ _ _=>True.intro)
    (fun _=>True.intro) (fun _ _ _ _=>True.intro)
    (fun inner ih=>Or.inl inner)
    (fun run cost inner ih=>Or.inr ⟨_,_,_,run,cost,inner,rfl⟩) demand

/-- Only the ACTUALLY selected branch's real demands are required. There is
no all-branches allocator premise or nonallocating compilation restriction. -/
theorem branch_room_true {b frame Γ Δ Ξ F P Q} {c : Val C Γ .bool}
    (condition : Memory.CompiledVal b F c) (yes : CompiledProg b (Γ:=Γ) (Δ:=Δ) F P)
    (no : CompiledProg b (Γ:=Γ) (Δ:=Ξ) F Q) (σ : State C Γ) (base : Nat → Fin W) (m : Machine)
    (selected : c.evalT σ=.ok true) (room : Room yes.cert frame σ base m) :
    ∀ amount,StmtDemand (branch condition yes no).cert σ amount → AllocationInput b frame amount σ base m := by
  intro amount demand
  rcases stmt_shape demand with ⟨observed,inner⟩ | ⟨observed,inner⟩
  · exact room _ inner
  · rw [selected] at observed;cases observed

theorem branch_room_false {b frame Γ Δ Ξ F P Q} {c : Val C Γ .bool}
    (condition : Memory.CompiledVal b F c) (yes : CompiledProg b (Γ:=Γ) (Δ:=Δ) F P)
    (no : CompiledProg b (Γ:=Γ) (Δ:=Ξ) F Q) (σ : State C Γ) (base : Nat → Fin W) (m : Machine)
    (selected : c.evalT σ=.ok false) (room : Room no.cert frame σ base m) :
    ∀ amount,StmtDemand (branch condition yes no).cert σ amount → AllocationInput b frame amount σ base m := by
  intro amount demand
  rcases stmt_shape demand with ⟨observed,inner⟩ | ⟨observed,inner⟩
  · rw [selected] at observed;cases observed
  · exact room _ inner

def singleton {b Γ Δ F s} (head : CompiledStmt (C:=C) b (Γ:=Γ) (Δ:=Δ) F s) :
    CompiledProg b F (.cons s .nil) := cons head ⟨head.frag,[],.nil _⟩

theorem singleton_room {b frame Γ Δ F s} (head : CompiledStmt (C:=C) b (Γ:=Γ) (Δ:=Δ) F s)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine)
    (room : ∀ amount,StmtDemand head.cert σ amount → AllocationInput b frame amount σ base m) :
    Room (singleton head).cert frame σ base m := by
  intro amount demand
  rcases prog_shape demand with inner | ⟨out,spent,rest,run,cost,inner,total⟩
  · exact room _ inner
  · exact False.elim (prog_shape inner)

end Solidity.Evm.Memory.Recursive.Composition
