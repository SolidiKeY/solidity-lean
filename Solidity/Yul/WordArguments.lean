import Solidity.Yul.WordLoops

/-! Right-to-left typed operand modalities for the ACTUAL collectValues
expression evaluator. This is a formula construction, not an untyped IR or
another execution model. Every operand has exactly one word result. -/
namespace Solidity.Yul.Logic
open Solidity.Yul.Closed
open Solidity (Modality)

def appendArg {arity : Nat} (last : Word) (rest : Values arity) : Values (arity+1) :=
  Fin.lastCases last rest

def argsModal {F n} (mode : Modality) (model : Model F) :
    (arity : Nat) → (Fin arity → Term F n 1) → (Values arity → Fml n) → Fml n
  | 0, _, post => post Fin.elim0
  | arity+1, args, post =>
    .termModal mode model (args (Fin.last arity)) (fun last =>
      argsModal mode model arity (fun i => args i.castSucc)
        (fun rest => post (appendArg (last 0) rest)))

/-- Alias of the existing evaluator's argument collection, with typed operands. -/
def evalArgs {F n} (fuel : Nat) (model : Model F) (arity : Nat)
    (args : Fin arity → Term F n 1) (vars : Values n) : Option (Values arity) :=
  collectValues arity (fun i =>
    (evalExpr fuel model.environment model.words (args i).code (args i).words vars).map (fun result => result 0))

theorem evalArgs_succ {F n} (fuel : Nat) (model : Model F) (arity : Nat)
    (args : Fin (arity+1) → Term F n 1) (vars : Values n) :
    evalArgs fuel model (arity+1) args vars =
    (do let last ← (evalExpr fuel model.environment model.words
          (args (Fin.last arity)).code (args (Fin.last arity)).words vars).map (fun result => result 0)
        let rest ← evalArgs fuel model arity (fun i => args i.castSucc) vars
        pure (appendArg last rest)) := rfl

theorem evalArgs_stable {F n lo hi} (bound : lo ≤ hi) (model : Model F) (arity : Nat)
    (args : Fin arity → Term F n 1) (vars : Values n) {result : Values arity}
    (done : evalArgs lo model arity args vars = some result) :
    evalArgs hi model arity args vars = some result := by
  apply collectValues_refines arity _ _ ?_ result done
  intro i
  apply Refines.map
  intro value ran
  exact evalExpr_stable bound model.environment model.words (args i).code (args i).words vars ran

theorem args_completed {F n arity lo hi} (model : Model F)
    (args : Fin (arity+1) → Term F n 1) (vars : Values n) (last : Values 1) (rest : Values arity)
    (lastRan : evalExpr lo model.environment model.words
      (args (Fin.last arity)).code (args (Fin.last arity)).words vars = some last)
    (restRan : evalArgs hi model arity (fun i => args i.castSucc) vars = some rest) :
    evalArgs (max lo hi) model (arity+1) args vars = some (appendArg (last 0) rest) := by
  rw [evalArgs_succ,evalExpr_stable (Nat.le_max_left lo hi) model.environment model.words
    (args (Fin.last arity)).code (args (Fin.last arity)).words vars lastRan]
  change (do let result ← evalArgs (max lo hi) model arity (fun i => args i.castSucc) vars
             pure (appendArg (last 0) result)) = _
  rw [evalArgs_stable (Nat.le_max_right lo hi) model arity (fun i => args i.castSucc) vars restRan]
  rfl

def ArgsHolds {F n} (mode : Modality) (model : Model F) (arity : Nat)
    (args : Fin arity → Term F n 1) (post : Values arity → Fml n) (vars : Values n) : Prop :=
  match mode with
  | .box => ∀ fuel result, evalArgs fuel model arity args vars = some result → (post result).holds vars
  | .diamond => ∃ fuel result, evalArgs fuel model arity args vars = some result ∧ (post result).holds vars

/-- The shared interpreter horizon and nested right-to-left modalities agree.
Different genuine operand horizons are synchronized internally by max/stability. -/
theorem args_modal_iff {F n} (arity : Nat) (mode : Modality) (model : Model F) (vars : Values n) :
    ∀ (args : Fin arity → Term F n 1) (post : Values arity → Fml n),
      ArgsHolds mode model arity args post vars ↔ (argsModal mode model arity args post).holds vars := by
  induction arity with
  | zero =>
    intro args post
    cases mode with
    | box =>
      constructor
      · intro all; exact all 0 Fin.elim0 rfl
      · intro after fuel result ran
        change some Fin.elim0 = some result at ran
        cases Option.some.inj ran
        exact after
    | diamond =>
      constructor
      · rintro ⟨fuel,result,ran,after⟩
        change some Fin.elim0 = some result at ran
        cases Option.some.inj ran
        exact after
      · intro after; exact ⟨0,Fin.elim0,rfl,after⟩
  | succ arity ih =>
    intro args post
    cases mode with
    | box =>
      constructor
      · intro all lastFuel last lastRan
        apply (ih (fun i => args i.castSucc) (fun rest => post (appendArg (last 0) rest))).mp
        intro restFuel rest restRan
        exact all (max lastFuel restFuel) _ (args_completed model args vars last rest lastRan restRan)
      · intro folded fuel result ran
        rw [evalArgs_succ] at ran
        cases lastRan : evalExpr fuel model.environment model.words
          (args (Fin.last arity)).code (args (Fin.last arity)).words vars with
        | none => rw [lastRan] at ran; cases ran
        | some last =>
          rw [lastRan] at ran
          change (do let rest ← evalArgs fuel model arity (fun i => args i.castSucc) vars
                     pure (appendArg (last 0) rest)) = _ at ran
          cases restRan : evalArgs fuel model arity (fun i => args i.castSucc) vars with
          | none => rw [restRan] at ran; cases ran
          | some rest =>
            rw [restRan] at ran
            cases Option.some.inj ran
            have after := folded fuel last lastRan
            exact ((ih (fun i => args i.castSucc) (fun rest => post (appendArg (last 0) rest))).mpr after)
              fuel rest restRan
    | diamond =>
      constructor
      · rintro ⟨fuel,result,ran,after⟩
        rw [evalArgs_succ] at ran
        cases lastRan : evalExpr fuel model.environment model.words
          (args (Fin.last arity)).code (args (Fin.last arity)).words vars with
        | none => rw [lastRan] at ran; cases ran
        | some last =>
          rw [lastRan] at ran
          change (do let rest ← evalArgs fuel model arity (fun i => args i.castSucc) vars
                     pure (appendArg (last 0) rest)) = _ at ran
          cases restRan : evalArgs fuel model arity (fun i => args i.castSucc) vars with
          | none => rw [restRan] at ran; cases ran
          | some rest =>
            rw [restRan] at ran
            cases Option.some.inj ran
            refine ⟨fuel,last,lastRan,?_⟩
            exact (ih (fun i => args i.castSucc) (fun rest => post (appendArg (last 0) rest))).mp
              ⟨fuel,rest,restRan,after⟩
      · rintro ⟨lastFuel,last,lastRan,after⟩
        rcases (ih (fun i => args i.castSucc) (fun rest => post (appendArg (last 0) rest))).mpr after with
          ⟨restFuel,rest,restRan,done⟩
        exact ⟨max lastFuel restFuel,_,args_completed model args vars last rest lastRan restRan,done⟩


theorem collected_at (arity : Nat) (read : Fin arity → Option Word) (values : Values arity)
    (done : collectValues arity read = some values) (position : Fin arity) :
    read position = some (values position) := by
  induction arity with
  | zero => exact Fin.elim0 position
  | succ arity ih =>
    change (do let last ← read (Fin.last arity)
               let rest ← collectValues arity (fun i => read i.castSucc)
               pure (appendArg last rest)) = some values at done
    cases lastRan : read (Fin.last arity) with
    | none => rw [lastRan] at done; cases done
    | some last =>
      rw [lastRan] at done
      change (do let rest ← collectValues arity (fun i => read i.castSucc)
                 pure (appendArg last rest)) = some values at done
      cases restRan : collectValues arity (fun i => read i.castSucc) with
      | none => rw [restRan] at done; cases done
      | some rest =>
        rw [restRan] at done
        cases Option.some.inj done
        apply Fin.lastCases (motive := fun i => read i = some (appendArg last rest i)) ?_ ?_ position
        · simpa only [appendArg,Fin.lastCases_last] using lastRan
        · intro i
          simpa only [appendArg,Fin.lastCases_castSucc] using ih (fun i => read i.castSucc) rest restRan i

/-- An incomplete operand prevents collection at that horizon. This does NOT
assert divergence unless its caller proves incompletion for EVERY horizon. -/
theorem evalArgs_none_at {F n arity} (fuel : Nat) (model : Model F)
    (args : Fin arity → Term F n 1) (vars : Values n) (position : Fin arity)
    (stuck : evalExpr fuel model.environment model.words (args position).code (args position).words vars = none) :
    evalArgs fuel model arity args vars = none := by
  cases ran : evalArgs fuel model arity args vars with
  | none => rfl
  | some values =>
    unfold evalArgs at ran
    have present := collected_at arity _ values ran position
    rw [stuck] at present
    cases present

end Solidity.Yul.Logic
