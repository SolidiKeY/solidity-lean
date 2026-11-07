import Solidity.Evm.MemoryLoopHorizonObjectFinite

/-! A genuine empty-array declaration loop certified by the complete-object
construction compiler. Every successful turn reserves one cell. Finite transport
consumes an explicit strong initial allocation input for the requested horizon;
no concrete capacity witness or unbounded execution is fabricated. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
open Construction
variable {C : Contract} {Γ : Ctx}

def body : Prog C Γ (.mem (.array (.prim .uint))::Γ) :=
  .cons (.declMem (.array (.prim .uint)) (.user "fresh") none rfl rfl) .nil

def code (b : Nat) (Γ : Ctx) : List Instr :=
  ([.push w[0]] ++ allocateArrayCode ++ [.mstore (cell (b + Γ.length))]) ++ []

def cert (b : Nat) (positive : 0 < b) : Construction.LoopCert b (Frag.init Γ)
    (.simple (.bool true) : Val C Γ .bool) body
    (Evm.compileVal b (.simple (.bool true) : Val C Γ .bool)) (code b Γ) := by
  refine ⟨.core _ rfl, (Frag.init Γ).push (.mem (.array (.prim .uint))) .ok,
    .cons (.empty _ _ _ rfl rfl positive) (.nil _), ?_⟩
  simp only [Frag.restrict, Frag.push, List.length_cons, Nat.add_sub_cancel_left,
    List.drop_succ_cons, List.drop_zero]

theorem body_cost (state : State C Γ) : Construction.allocationCostProg body state = 1 := by rfl

theorem room {b frame : Nat} {state : State C Γ} {base : Nat → Fin W}
    {machine : Machine} (horizon : Nat)
    (demand : Objects.AllocationInput b frame horizon state base machine) :
    Construction.FiniteLoopRoom b frame (.simple (.bool true)) body state base machine horizon := by
  intro reached cost turns hp within condition
  have exactCost : cost = turns := by
    clear within condition
    induction hp with
    | start => rfl
    | next hp hc hs ih => rw [ih, body_cost]
  apply demand.of_le
  rw [exactCost, body_cost]
  omega

theorem represented {L b frame : Nat} {state : State C Γ} {base : Nat → Fin W}
    {machine : Machine} (positive : 0 < b) (horizon : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame horizon state base machine) :
    Construction.CountedHorizonRelation L b frame (Frag.init Γ) (.simple (.bool true))
      body state base machine horizon
      (TLoop.iterN (horizonBody body) (fun o => (.simple (.bool true) : Val C Γ .bool).evalT o.st)
        horizon ⟨state,List.prefix_refl _⟩)
      (loopIterN (fun m => exec (Evm.compileVal b (.simple (.bool true) : Val C Γ .bool)) 0 m)
        (fun m => exec (code b Γ) 0 m) horizon machine) := by
  exact (cert b positive).correct_finite_horizon horizon repr capacity (room horizon demand)

end Solidity.Evm.Memory.HorizonObjectAllocating
