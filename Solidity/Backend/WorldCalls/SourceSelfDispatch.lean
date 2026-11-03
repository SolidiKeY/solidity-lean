import Solidity.Lowering.Readonly.SourceCallPrefix
import Solidity.Backend.Passes.SourceCallFrame

/-! The actual Source external-self path, through callAddr/enterInstance/dispatch.
Funding, depth and static-value admission remain the exact interpreter guards.
No target compiler, ABI/body substitution or unknown-receiver shortcut follows. -/
namespace Solidity.Backend.WorldCalls.SourceSelfDispatch
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly.SourceHistory.CallPrefix
open Solidity.Backend.Passes.SourceCallFrame
variable {E : Env}

def checkpoint (state : St E) : Nat × Nat × Heap E.layout :=
  (state.ex.journal.length,state.logs.length,state.heap)

/-- Self funding checks the live balance but performs no transfer or credit. -/
theorem funded_self (F : Fr) (value : Word) (state : St E)
    (enough : value.val ≤ (state.ex.world.accounts F.this).balance.val) :
    (fund (E := E) F F.this value).run (L0 E,state) = (.ok true,(L0 E,state)) := by
  simp only [fund, ↓reduceIte, EM.st, bind, pure, ExceptT.bind, ExceptT.pure,
    ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure,
    StateT.get, get, getThe, MonadStateOf.get, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map, enough, decide_true]

theorem enter (G : Glob E) (F : Fr) (n : Nat) (value : Word) (input : Bytes)
    (requested : Bool) (code : String) (state : St E)
    (depth : ¬ F.depth ≥ 1024)
    (guard : (F.static && decide (value.val ≠ 0)) = false)
    (lookup : (instanceAt G F.this : EM E [] _).run (L0 E,state) =
      (.ok (some code),(L0 E,state)))
    (enough : value.val ≤ (state.ex.world.accounts F.this).balance.val) :
    (callAddr G F (n+1) F.this value input requested).run (L0 E,state) =
      (enterInstance G n F.this F.this value input (requested || F.static)
        code (F.depth+1) (checkpoint state)).run (L0 E,state) := by
  rw [known_run G F n F.this value input requested code state depth guard lookup]
  have marked : (Solidity.Source.mark : EM E [] _).run (L0 E,state) =
      (.ok (checkpoint state),(L0 E,state)) := rfl
  simp only [known, Hoare.run_bind, marked, funded_self F value state enough,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem success (G : Glob E) (F : Fr) (n : Nat) (value : Word) (input data : Bytes)
    (requested : Bool) (code : String) (state dirty : St E) (locals : Locals E.layout [])
    (depth : ¬ F.depth ≥ 1024)
    (guard : (F.static && decide (value.val ≠ 0)) = false)
    (lookup : (instanceAt G F.this : EM E [] _).run (L0 E,state) =
      (.ok (some code),(L0 E,state)))
    (enough : value.val ≤ (state.ex.world.accounts F.this).balance.val)
    (actual : (dispatch G (childFrame F.this F.this value input (requested || F.static)
      code (F.depth+1)) n input).run (L0 E,{state with heap := Heap.empty}) =
        (.ok data,(locals,dirty))) :
    (callAddr G F (n+2) F.this value input requested).run (L0 E,state) =
      (.ok (.success data),(locals,{dirty with heap := state.heap})) := by
  rw [enter G F (n+1) value input requested code state depth guard lookup enough]
  exact enter_success G n F.this F.this value input data (requested || F.static) code
    (F.depth+1) (checkpoint state) state dirty locals actual

theorem reverted (G : Glob E) (F : Fr) (n : Nat) (value : Word) (input data : Bytes)
    (requested : Bool) (code : String) (state dirty : St E) (locals : Locals E.layout [])
    (depth : ¬ F.depth ≥ 1024)
    (guard : (F.static && decide (value.val ≠ 0)) = false)
    (lookup : (instanceAt G F.this : EM E [] _).run (L0 E,state) =
      (.ok (some code),(L0 E,state)))
    (enough : value.val ≤ (state.ex.world.accounts F.this).balance.val)
    (actual : (dispatch G (childFrame F.this F.this value input (requested || F.static)
      code (F.depth+1)) n input).run (L0 E,{state with heap := Heap.empty}) =
        (.error (.revert data),(locals,dirty))) :
    (callAddr G F (n+2) F.this value input requested).run (L0 E,state) =
      (.ok (.revert data),(locals,rolledBack dirty (checkpoint state))) := by
  rw [enter G F (n+1) value input requested code state depth guard lookup enough]
  exact enter_revert G n F.this F.this value input data (requested || F.static) code
    (F.depth+1) (checkpoint state) state dirty locals actual

theorem halted (G : Glob E) (F : Fr) (n : Nat) (value : Word) (input : Bytes)
    (requested : Bool) (code : String) (state dirty : St E) (locals : Locals E.layout [])
    (halt : Halt) (notRevert : ∀ bytes, halt ≠ .revert bytes)
    (depth : ¬ F.depth ≥ 1024)
    (guard : (F.static && decide (value.val ≠ 0)) = false)
    (lookup : (instanceAt G F.this : EM E [] _).run (L0 E,state) =
      (.ok (some code),(L0 E,state)))
    (enough : value.val ≤ (state.ex.world.accounts F.this).balance.val)
    (actual : (dispatch G (childFrame F.this F.this value input (requested || F.static)
      code (F.depth+1)) n input).run (L0 E,{state with heap := Heap.empty}) =
        (.error halt,(locals,dirty))) :
    (callAddr G F (n+2) F.this value input requested).run (L0 E,state) =
      (.error halt,(locals,{dirty with heap := state.heap})) := by
  rw [enter G F (n+1) value input requested code state depth guard lookup enough]
  exact enter_halt G n F.this F.this value input (requested || F.static) code
    (F.depth+1) (checkpoint state) state dirty locals halt notRevert actual
end Solidity.Backend.WorldCalls.SourceSelfDispatch
