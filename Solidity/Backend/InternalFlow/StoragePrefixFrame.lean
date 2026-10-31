import Solidity.Backend.InternalFlow.FragilePop

/-! An effect consequence of the actual target semantics, not another evaluator.
Storage-only straight-line prefixes may mutate storage while framing memory. -/
namespace Solidity.Backend.InternalFlow.StoragePrefixFrame
open Evm

def noMemoryStore : Instr → Bool
  | .mstore _ | .mstoreAt | .loop _ _ => false
  | _ => true

theorem step_mem {i : Instr} (allowed : noMemoryStore i = true)
    {m m' : Machine} {k : Nat} (ran : i.step m = .ok m' k) : m'.mem = m.mem := by
  cases i <;> simp only [noMemoryStore,Bool.false_eq_true] at allowed
  all_goals simp only [Instr.step,Machine.next] at ran
  all_goals repeat' split at ran
  all_goals cases ran <;> rfl

theorem exec_mem (code : List Instr) (allowed : code.all noMemoryStore = true)
    {m m' : Machine} {k n : Nat} (ran : Evm.exec code k m = .ok m' n) : m'.mem = m.mem := by
  induction code generalizing m k with
  | nil => cases ran; rfl
  | cons i code ih =>
    have parts : noMemoryStore i = true ∧ code.all noMemoryStore = true := by
      simpa only [List.all_cons,Bool.and_eq_true] using allowed
    cases k with
    | succ k => exact ih parts.2 ran
    | zero =>
      simp only [Evm.exec] at ran
      cases hs : i.step m with
      | ok mid skip =>
        rw [hs,Out.ok_bind] at ran
        exact (ih parts.2 ran).trans (step_mem parts.1 hs)
      | revert => rw [hs,Out.bind] at ran; contradiction
      | fault => rw [hs,Out.bind] at ran; contradiction

theorem run_mem (code : List Instr) (allowed : code.all noMemoryStore = true)
    {m m' : Machine} {n : Nat} (ran : Evm.run code m = .ok m' n) : m'.mem = m.mem :=
  exec_mem code allowed ran

variable {C : Contract}

/-- This is a separate operation classifier, NOT a weakening of within/withinM. -/
def storeStmt {Γ Δ : Ctx} : Stmt C Γ Δ → Bool
  | .assign .. | .push .. => true
  | _ => false

def storeProg {Γ Δ : Ctx} : Prog C Γ Δ → Bool
  | .nil => true
  | .cons s P => storeStmt s && storeProg P

theorem store_stmt_frame {Γ Δ : Ctx} (s : Stmt C Γ Δ) (allowed : storeStmt s = true)
    {σ : State C Γ} {o : Solidity.Out C σ.H Δ} (ran : s.run σ = .ok o) :
    TGFrame .nonpayable σ o.st := by
  cases s <;> simp only [storeStmt,Bool.false_eq_true] at allowed
  case assign l v => exact (Stmt.run_frame (.assign l v) (by rfl) 0 ran).1
  case push path init hd =>
    change TRun.push path init σ = .ok o at ran
    unfold TRun.push at ran
    obtain ⟨ref,href,ran⟩ := tbind_ok_inv ran
    cases init <;> simp only [bind,Except.bind,pure,Except.pure,TRes.ofOpt] at ran
    all_goals repeat' split at ran
    all_goals cases ran
    all_goals exact TGFrame.withStorage σ _

theorem store_prog_frame : {Γ Δ : Ctx} → (P : Prog C Γ Δ) → storeProg P = true →
    {σ : State C Γ} → {o : Solidity.Out C σ.H Δ} → P.run σ = .ok o →
    TGFrame .nonpayable σ o.st
  | _,_,.nil,_,σ,_,ran => by cases ran; exact TGFrame.refl σ
  | _,_,.cons s P,allowed,σ,o,ran => by
    have parts : storeStmt s = true ∧ storeProg P = true := by
      simpa only [storeProg,Bool.and_eq_true] using allowed
    change TRun.seq s.runR P.runR σ = .ok o at ran
    unfold TRun.seq at ran
    split at ran
    · rename_i first hfirst
      obtain ⟨last,hlast,rfl⟩ := tmap_ok_inv ran
      exact (store_stmt_frame s parts.1 hfirst).trans (store_prog_frame P parts.2 hlast)
    · cases ran

/-- Transport actual allocator ownership along an existing source heap frame. -/
theorem allocator_heap {H H' : HTy} {hp : Heap H} {hp' : Heap H'}
    {base : Nat → Fin W} {frame : Nat} {cursor : Fin W} {m : Machine}
    (typing : H = H') (heaps : HEq hp hp')
    (h : Evm.Memory.StructAllocatorRepr hp base frame cursor m) :
    Evm.Memory.StructAllocatorRepr hp' base frame cursor m := by
  cases typing
  cases heaps
  exact h

end Solidity.Backend.InternalFlow.StoragePrefixFrame
