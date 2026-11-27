import Solidity.Source.Session

namespace Solidity.Source
open Solidity.Roadmap (Request Outcome SessionEnv Prefix Event)
variable {E : Env}

def runCheckedTx (G : Glob E) (n : Nat) (q : Request) (s : St E) :
    Option (Except Halt Outcome) × St E :=
  if requestFunded G.fixed G.balance0 s.events q then
    let result := runAt (fun f => runTx G f q) s n
    (some result.1, result.2)
  else (none, s)

theorem runCheckedTx_invalid (G : Glob E) (n : Nat) (q : Request) (s : St E)
    (h : requestFunded G.fixed G.balance0 s.events q = false) :
    runCheckedTx G n q s = (none, s) := by
  rw [runCheckedTx, h]
  rfl

theorem runCheckedTx_valid (G : Glob E) (n : Nat) (q : Request) (s : St E)
    (h : requestFunded G.fixed G.balance0 s.events q = true) :
    runCheckedTx G n q s =
      (some (runAt (fun f => runTx G f q) s n).1, (runAt (fun f => runTx G f q) s n).2) := by
  rw [runCheckedTx, h]
  rfl

theorem runCheckedTx_result_funded (G : Glob E) (n : Nat) (q : Request) (s : St E)
    {r : Except Halt Outcome} {post : St E} (h : runCheckedTx G n q s = (some r, post)) :
    RequestFunded G.fixed G.balance0 s.events q := by
  unfold runCheckedTx at h
  split at h
  next funded => exact (requestFunded_true_iff _ _ _ _).1 funded
  next unfunded => cases h

theorem runCheckedTx_invalid_state (G : Glob E) (q : Request) (s : St E)
    (h : requestFunded G.fixed G.balance0 s.events q = false) (n : Nat) :
    (runCheckedTx G n q s).2 = s :=
  congrArg Prod.snd (runCheckedTx_invalid G n q s h)

theorem runCheckedTx_stable (G : Glob E) (q : Request) (s : St E)
    {n n' : Nat} (hn : n ≤ n')
    (hd : Done (runAt (fun f => runTx G f q) s n) = true) :
    runCheckedTx G n' q s = runCheckedTx G n q s := by
  unfold runCheckedTx
  split
  · rw [runTx_stable G q s hn hd]
  · rfl

theorem sessionGo_drop_unfunded (P : SrcProg E) (env : SessionEnv) (n k i : Nat)
    (s : St E) (last : Outcome) (q : Request)
    (issued : env.requests s.events i = some (.request q))
    (bad : requestFunded P.fixed env.balance s.events q = false) :
    sessionGo P env n (k + 1) i s last = sessionGo P env n k (i + 1) s last := by
  simp only [sessionGo, issued, bad, Bool.false_eq_true, if_false]

theorem sessionGoEvents_drop_unfunded (P : SrcProg E) (env : SessionEnv) (n k i : Nat)
    (s : St E) (last : Outcome) (q : Request)
    (issued : env.requests s.events i = some (.request q))
    (bad : requestFunded P.fixed env.balance s.events q = false) :
    sessionGoEvents P env n (k + 1) i s last = sessionGoEvents P env n k (i + 1) s last := by
  simp only [sessionGoEvents, issued, bad, Bool.false_eq_true, if_false]

theorem dropped_then_end (P : SrcProg E) (env : SessionEnv) (n k i : Nat)
    (s : St E) (last : Outcome) (q : Request)
    (issued : env.requests s.events i = some (.request q))
    (bad : requestFunded P.fixed env.balance s.events q = false)
    (finished : env.requests s.events (i + 1) = none) :
    sessionGo P env n (k + 2) i s last = ⟨s.events, some last⟩ ∧
    sessionGoEvents P env n (k + 2) i s last = ⟨s.events, some last⟩ := by
  constructor
  · rw [sessionGo_drop_unfunded P env n (k + 1) i s last q issued bad, sessionGo, finished]
  · rw [sessionGoEvents_drop_unfunded P env n (k + 1) i s last q issued bad, sessionGoEvents, finished]
end Solidity.Source
