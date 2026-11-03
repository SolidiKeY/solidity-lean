import Solidity.Evm.MemoryRecursiveHorizon

/-! One-turn allocator-room reduction for existing recursive body certificates.
A real source stopping fact removes future active prefixes; initial reached body
demands still require real allocator inputs. No loop or proof-fuel cap is added. -/
namespace Solidity.Evm.Memory.RecursiveLift
variable {C : Contract} {Γ Δ : Ctx}
/-- A real successful body that stops its next condition leaves only initial
active body demands. This is allocator-room reduction, not assumed adequacy. -/
theorem room_one_turn {b frame F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine)
    (stops : ∀ (state : State C Γ) (out : Solidity.Out C state.H Δ),
      body.run state=.ok out → c.evalT (out.st.drop body.ext)=.ok false)
    (initial : ∀ amount,cert.profile.demand σ amount → AllocationInput b frame amount σ base m) :
    Room cert frame σ base m := by
  intro out cost before condition amount demand
  cases before with
  | start => simpa only [Nat.zero_add] using initial amount demand
  | next before tested run spent =>
    have falseAfter := stops _ _ run
    rw [falseAfter] at condition
    cases condition

end Solidity.Evm.Memory.RecursiveLift

namespace Solidity.Evm.Memory.Recursive
variable {C : Contract}

/-- Actual recursive body certificates discharge the lifting metadata; only
initial reached body demands need allocation room for a stopping body. -/
theorem loop_room_one_turn {b frame Γ Δ F G body cond code} {c : Val C Γ .bool}
    (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G body code)
    (hc : ValFrag b F c cond) (stable : G.restrict Γ=F)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine)
    (stops : ∀ (state : State C Γ) (out : Solidity.Out C state.H Δ),
      body.run state=.ok out → c.evalT (out.st.drop body.ext)=.ok false)
    (initial : Room hp frame σ base m) :
    RecursiveLift.Room (loopKit hc hp stable) frame σ base m := by
  exact RecursiveLift.room_one_turn (loopKit hc hp stable) σ base m stops initial

/-- Full unbounded source/target loop transport for an actually stopping
recursive body. Initial body room remains explicit; profile soundness is derived
from the existing recursive certificate, never supplied as an adequacy field. -/
theorem ProgCert.loop_correct_one_turn {b L frame Γ Δ F G body cond code}
    {c : Val C Γ .bool} (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G body code)
    (hc : ValFrag b F c cond) (stable : G.restrict Γ=F) (a : LoopAnn C Γ)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (cap : b+hp.need≤frame)
    (stops : ∀ (state : State C Γ) (out : Solidity.Out C state.H Δ),
      body.run state=.ok out → c.evalT (out.st.drop body.ext)=.ok false)
    (initial : Room hp frame σ base m) :
    LoopScopes.Result L b frame F σ base m
      (fun out amount=>RecursiveLift.Prefix (loopKit hc hp stable) σ out amount)
      ((Stmt.loop a c body).run σ) (run [.loop cond code] m) := by
  exact (loopKit hc hp stable).correct hp.profile_sound a repr cap
    (loop_room_one_turn hp hc stable σ base m stops initial)

end Solidity.Evm.Memory.Recursive
