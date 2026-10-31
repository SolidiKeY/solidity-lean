import Solidity.Semantics.LibraryTryFrame

/-! Consumers of the published installed-library boundary. These are typed
source-world facts, not a backend simulation. The journal world in WorldFrames
is a different intrinsic interface; no equality between those worlds is assumed. -/
namespace Solidity.Backend.AbiWorld.LibraryFrameTransport
open ContractWorld
variable {K : Type} [DecidableEq K] {contracts : K → Contract} {caller : K}
variable {Γ Δ : Ctx} {α β γ : Type}

/-- Only the live caller portion: storage, funds and settled ledger are observed
separately, never conflated with heap or transaction identity. -/
structure Live (C : Contract) (Γ : Ctx) where
  H : HTy
  heap : Heap H
  env : TEnv C H Γ
  tx : TTx

def live (σ : State C Γ) : Live C Γ := ⟨σ.H, σ.heap, σ.env, σ.tx⟩

/-- Every live typed reference and its entire object survive refresh. This
includes arbitrary older aliases, not merely a finite list of sample bytes. -/
theorem resume_live (w : World contracts) (self : Handle caller)
    (σ : State (contracts caller) Γ) (storage : Storage (contracts caller))
    (installed : w.storage? self = some storage) :
    (LibraryTryFrame.resume w self σ).map
      (fun τ => (live τ, τ.storage, τ.selfBalance, τ.net)) =
      .ok (live σ, storage, w.funds self.address, []) := by
  rw [LibraryTryFrame.resume_exact w self σ storage installed]
  rfl

/-- The exact continuation used by execute, exposed as a consumer adapter. -/
def tail (next : World contracts) (self : Handle caller)
    (start : State (contracts caller) Γ) (body : TStep (contracts caller) Γ Δ)
    (read : State (contracts caller) Δ → TRes γ) : TRes (World contracts × γ) := do
  let resumed ← LibraryTryFrame.resume next self start
  let out ← body resumed
  let result ← read out.st
  let final ← next.finish self.address out.st
  pure (final, result)

/-- Selection supplies the actual next world. The callback receives the old
live heap/frame but fresh storage/balance and no already-settled ledger. -/
theorem tail_refresh (next : World contracts) (self : Handle caller)
    (start : State (contracts caller) Γ) (storage : Storage (contracts caller))
    (body : TStep (contracts caller) Γ Δ) (read : State (contracts caller) Δ → TRes γ)
    (installed : next.storage? self = some storage) :
    tail next self start body read = (do
      let out ← body { start with storage, selfBalance := next.funds self.address, net := [] }
      let result ← read out.st
      let final ← next.finish self.address out.st
      pure (final, result)) := by
  unfold tail
  rw [LibraryTryFrame.resume_exact next self start storage installed]
  rfl

/-- Successful call transport consumes the real operation and decoder. No
caller-tail execution or preservation premise is substituted for that call. -/
theorem execute_success (w pre next : World contracts) (self : Handle caller)
    (σ : State (contracts caller) []) (before : TStep (contracts caller) [] Γ)
    (start : Out (contracts caller) σ.H Γ)
    (args : State (contracts caller) Γ → TRes α) (a : α)
    (library : α → LibraryTryFrame.RawLibrary contracts caller) (ctx : Context)
    (decode : List Word → TRes β) (words : List Word) (value : β)
    (ok : β → TStep (contracts caller) Γ Δ) (err : THalt → TStep (contracts caller) Γ Δ)
    (read : State (contracts caller) Δ → TRes γ)
    (prefixRun : before σ = .ok start) (arguments : args start.st = .ok a)
    (settled : w.finish self.address start.st = .ok pre)
    (called : pre.libraryCall self (library a).target ctx = .ok (next, words))
    (decoded : decode words = .ok value) :
    LibraryTryFrame.execute w self σ before args library ctx decode ok err read =
      tail next self start.st (ok value) read := by
  simp only [LibraryTryFrame.execute, prefixRun, arguments, settled, bind, Except.bind]
  exact LibraryTryFrame.success pre next self a library ctx decode _ _ words value called decoded

/-- A completed callee failure uses the actual settled prefix world, with its
full halt packet. Argument/decoder/tail failures are not covered by this case. -/
theorem execute_caught (w pre : World contracts) (self : Handle caller)
    (σ : State (contracts caller) []) (before : TStep (contracts caller) [] Γ)
    (start : Out (contracts caller) σ.H Γ)
    (args : State (contracts caller) Γ → TRes α) (a : α)
    (library : α → LibraryTryFrame.RawLibrary contracts caller) (ctx : Context)
    (decode : List Word → TRes β) (ok : β → TStep (contracts caller) Γ Δ)
    (err : THalt → TStep (contracts caller) Γ Δ)
    (read : State (contracts caller) Δ → TRes γ) (halt : THalt)
    (prefixRun : before σ = .ok start) (arguments : args start.st = .ok a)
    (settled : w.finish self.address start.st = .ok pre)
    (called : pre.libraryCall self (library a).target ctx = .error halt)
    (completed : catchable halt = true) :
    LibraryTryFrame.execute w self σ before args library ctx decode ok err read =
      tail pre self start.st (err halt) read := by
  simp only [LibraryTryFrame.execute, prefixRun, arguments, settled, bind, Except.bind]
  exact LibraryTryFrame.caught pre self a library ctx decode _ _ halt called completed

/-- Outer atomic rollback is the actual ContractWorld checkpoint. It is
separate from the Source.ExecState journal law in WorldFrames. -/
theorem failed_tail_checkpoint (w selected : World contracts) (self : Handle caller)
    (start : State (contracts caller) Γ) (body : TStep (contracts caller) Γ Δ)
    (read : State (contracts caller) Δ → TRes γ) (e : THalt)
    (failed : tail selected self start body read = .error e) :
    atomic w (tail selected self start body read) = (w, .error e) := by
  rw [failed]
  exact atomic_failure w e

/-- info: 'Solidity.Backend.AbiWorld.LibraryFrameTransport.resume_live' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms resume_live
/-- info: 'Solidity.Backend.AbiWorld.LibraryFrameTransport.execute_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms execute_success
/-- info: 'Solidity.Backend.AbiWorld.LibraryFrameTransport.execute_caught' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms execute_caught
/-- info: 'Solidity.Backend.AbiWorld.LibraryFrameTransport.failed_tail_checkpoint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms failed_tail_checkpoint
end Solidity.Backend.AbiWorld.LibraryFrameTransport
