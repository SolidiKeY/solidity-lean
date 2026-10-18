import Solidity.Calculus.SymbolicPaths
import Solidity.Calculus.DeclarationFacts

/-!
# Definedness guards for declaration paths

A declared root/field/mapping path returns exactly when all its key terms
return. Its guard sequences those same terms and returns `true`; failure
stays failure. Arrays need presence constraints and are rejected here.
-/

namespace Solidity.Decide

open Semantics

variable {C : Contract}

structure TSegs.Guard {T U : Ty} (p : TSegs C T U) where
  test : LTm C (.val .bool)
  correct : ∀ (g : State C []) (ν : AEnv), test.eval g ν = (p.eval g ν).map (fun _ => true)
  declared : ∀ (g : State C []) (ν : AEnv) (q : Path T U),
    p.eval g ν = some q → q.Declared

private def TSegs.guardFuel? : Nat → {T U : Ty} → (p : TSegs C T U) → Option (TSegs.Guard p)
  | 0, _, _, _ => none
  | _ + 1, _, _, .nil => some ⟨.tt, fun _ _ => rfl, by
      intro _ _ q h
      cases h
      exact .nil⟩
  | fuel + 1, _, _, .field h p => do
    let a ← TSegs.guardFuel? fuel p
    return ⟨a.test, by
      intro g ν
      rw [a.correct g ν, TSegs.eval_field]
      cases p.eval g ν <;> rfl, by
      intro g ν q hq
      obtain ⟨q', hq', rfl⟩ := eval_field_some g ν hq
      exact .field h (a.declared g ν q' hq')⟩
  | fuel + 1, _, _, .key k p => do
    let a ← TSegs.guardFuel? fuel p
    return ⟨.seq k a.test, by
      intro g ν
      rw [LTm.eval_seq, a.correct g ν, TSegs.eval_key]
      cases k.eval g ν <;> cases p.eval g ν <;> rfl, by
      intro g ν q hq
      obtain ⟨j, q', _, hq', rfl⟩ := eval_key_some g ν hq
      exact .key j (a.declared g ν q' hq')⟩
  | _ + 1, _, _, .at .. | _ + 1, _, _, .atF .. => none

structure SPath.Guard {T : Ty} (p : SPath C T) where
  test : LTm C (.val .bool)
  correct : ∀ (g : State C []) (ν : AEnv), test.eval g ν = (p.eval g ν).map (fun _ => true)
  declared : ∀ (g : State C []) (ν : AEnv) (q : SRef C T),
    p.eval g ν = some q → q.Declared

def SPath.guard? {T : Ty} (p : SPath C T) : Option (SPath.Guard p) := do
  let a ← TSegs.guardFuel? 1024 p.segs
  return ⟨a.test, by
    intro g ν
    rw [a.correct g ν, SPath.eval]
    cases p.segs.eval g ν <;> rfl, by
    intro g ν q hq
    rw [SPath.eval, Option.map_eq_some_iff] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact a.declared g ν q' hq'⟩

end Solidity.Decide
