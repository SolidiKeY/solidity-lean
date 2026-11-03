import Solidity.Lowering.Readonly.SourceCallUnknown

/-! Exhaustive actual Source callAddr successor. No receiver restriction,
no changed outcome set, and no native/Core representation assumption. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
open StaticJournal
variable {E : Env}
private def codeAt (global : Glob E) (receiver : Address) (state : St E) : Option String :=
  match (state.ex.world.accounts receiver).code with
  | some code => global.contractAt code
  | none => none
private theorem lookup_run (global : Glob E) (receiver : Address) (state : St E) :
    (instanceAt global receiver : EM E [] _).run (L0 E,state) =
      (.ok (codeAt global receiver state),(L0 E,state)) := by
  simp only [instanceAt,EM.st,codeAt,bind,pure,ExceptT.bind,ExceptT.pure,
    ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,
    get,getThe,MonadStateOf.get,liftM,monadLift,MonadLift.monadLift,ExceptT.lift,
    Functor.map,StateT.map]
  cases (state.ex.world.accounts receiver).code <;> rfl

theorem callAddr_succ (global : Glob E) (frame : Fr) (n : Nat) (smaller : At global n)
    (receiver : Address) (value : Word) (input : Bytes) (requested : Bool) :
    Effect (requested || frame.static) (callAddr global frame (n+1) receiver value input requested) := by
  intro locals state
  cases locals
  by_cases depth : frame.depth ≥ 1024
  · simp only [callAddr,depth,↓reduceIte]
    exact .start _ _
  · cases guard : frame.static && decide (value.val ≠ 0) with
    | true =>
      simp only [callAddr,depth,guard,↓reduceIte]
      exact .start _ _
    | false =>
      have lookup := lookup_run global receiver state
      cases found : codeAt global receiver state with
      | none =>
        rw [found] at lookup
        rw [CallPrefix.unknown_run global frame n receiver value input requested state depth guard lookup]
        exact CallPrefix.unknown_effect global frame n smaller receiver value input requested (L0 E) state
      | some code =>
        rw [found] at lookup
        rw [CallPrefix.known_run global frame n receiver value input requested code state depth guard lookup]
        exact CallPrefix.known_effect global frame n smaller receiver value input requested code (L0 E) state
end Solidity.Lowering.Readonly.SourceHistory
