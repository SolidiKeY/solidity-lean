import Solidity.Evm.MemoryMixedLoop

namespace Solidity.Evm.Memory.MixedLoops
variable {C : Contract} {Γ Δ : Ctx}

theorem Prefix.cost_zero {b F c body cond code}
    {cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code}
    {σ : State C Γ} {o : Solidity.Out C σ.H Γ} {cost : Nat}
    (hp : Prefix cert σ o cost) (nonallocating : cert.bodyCert.allocates=false) : cost=0 := by
  induction hp with
  | start => rfl
  | next hp hc hr spent ih => rw [ih,LoopScopes.cost_nonallocating spent nonallocating]

theorem room_nonallocating {b frame F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    (nonallocating : cert.bodyCert.allocates=false)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine) : Room cert frame σ base m := by
  intro o cost hp hc amount demand
  left
  rw [hp.cost_zero nonallocating,LoopScopes.demand_nonallocating cert.bodyCert nonallocating demand]

/-- For an actual body that forces its next condition false, only the initial
body demands are reached. The Source stopping fact is explicit and can be
proved from concrete writes; no target simulation or final-view premise. -/
theorem room_one_turn {b frame F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine)
    (stops : ∀ (state : State C Γ) (out : Solidity.Out C state.H Δ),
      body.run state=.ok out → c.evalT (out.st.drop body.ext)=.ok false)
    (initial : LoopScopes.Room cert.bodyCert frame σ base m) : Room cert frame σ base m := by
  intro out cost hp condition amount demand
  cases hp with
  | start => simpa only [Nat.zero_add] using initial amount demand
  | next hp hc run spent =>
    have falseAfter := stops _ _ run
    rw [falseAfter] at condition
    cases condition

/-- Full actual loop execution, not finite-horizon success or a loop annotation
assumption. Body divergence and infinite outer iteration both remain divergence. -/
theorem Certificate.correct {b L frame F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code) (a : LoopAnn C Γ)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (cap : b+cert.bodyCert.need≤frame)
    (room : Room cert frame σ base m) :
    LoopScopes.Result L b frame F σ base m (fun o cost=>Prefix cert σ o cost)
      ((Stmt.loop a c body).run σ) (run [.loop cond code] m) := by
  have codeRun : run [.loop cond code] m=
      loopRun (fun m=>exec cond 0 m) (fun m=>exec code 0 m) m := by
    show (Instr.step (.loop cond code) m).bind (fun m' k'=>exec [] k' m')=_
    simp only [Instr.step]
    cases loopRun _ _ m <;> rfl
  rw [codeRun,Stmt.run_loop]
  change LoopScopes.Result L b frame F σ base m (fun o cost=>Prefix cert σ o cost)
    (TLoop.run (horizonBody body) (fun o=>c.evalT o.st) ⟨σ,List.prefix_refl _⟩) _
  by_cases finishes : ∃ res n,TLoop.iterN (horizonBody body) (fun o=>c.evalT o.st) n
      ⟨σ,List.prefix_refl _⟩=.inr res
  · obtain ⟨res,n,sourceRun⟩ := finishes
    have related := cert.correct_horizon repr cap room n
    rw [sourceRun] at related
    rw [TLoop.run_of_iterN sourceRun]
    generalize targetRun : loopIterN _ _ n m=target at related
    cases related with
    | done hp hr hs he hg => exact .inl ⟨_,_,_,_,rfl,loopRun_of_iterN targetRun,hp,hr,hs,he,hg⟩
    | revert => exact .inr (.inl ⟨rfl,loopRun_of_iterN targetRun⟩)
    | diverge => exact .inr (.inr ⟨rfl,loopRun_of_iterN targetRun⟩)
  · have diverges : TLoop.run (horizonBody body) (fun o=>c.evalT o.st)
        ⟨σ,List.prefix_refl _⟩=.error .diverge := by
      simp only [TLoop.run,finishes,dif_neg,not_false_eq_true]
    rw [diverges]
    refine .inr (.inr ⟨rfl,loopRun_of_forall fun n=>?_⟩)
    have related := cert.correct_horizon repr cap room n
    generalize sourceRun : TLoop.iterN _ _ n _=source at related
    generalize targetRun : loopIterN _ _ n m=target at related
    cases related with
    | more => exact ⟨_,rfl⟩
    | done => exact (finishes ⟨_,n,sourceRun⟩).elim
    | revert => exact (finishes ⟨_,n,sourceRun⟩).elim
    | diverge => exact (finishes ⟨_,n,sourceRun⟩).elim

structure Compiled (b : Nat) (F : Frag Γ) (c : Val C Γ .bool) (body : Prog C Γ Δ) where
  cond : List Instr
  code : List Instr
  cert : Certificate b F c body cond code

/-- Reuse the EXISTING condition and loop/scope-aware body compilers. The only
new check is the actual output-fragment restriction required by loop reuse. -/
def compile (b : Nat) (F : Frag Γ) (c : Val C Γ .bool) (body : Prog C Γ Δ) :
    Option (Compiled b F c body) := do
  let condition ← Memory.compileVal b F c
  let compiled ← LoopScopes.compileProg b body F
  if stable : compiled.frag.restrict Γ=F then
    pure ⟨condition.code,compiled.code,⟨condition.cert,compiled.frag,compiled.cert,stable⟩⟩
  else none

/-- Pending is never reported as source/target completion. -/
theorem Horizon.pending {b F c body cond code}
    {cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code}
    {L frame σ base m} {o : Solidity.Out C σ.H Γ} {result}
    (related : Horizon cert L frame σ base m (.inl o) result) : ∃ next,result=.inl next := by
  cases related with
  | more => exact ⟨_,rfl⟩

end Solidity.Evm.Memory.MixedLoops
