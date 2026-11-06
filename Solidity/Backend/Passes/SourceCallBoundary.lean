import Solidity.Source.Eval

/-! G22 call-boundary facts about the actual source interpreter. These are
source execution equations, not a source-to-intrinsic representation theorem.
No caller-storage or ledger projection is assumed or concluded here. -/
namespace Solidity.Backend.Passes.SourceCallBoundary
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open EM
variable {E : Env} {Γ : RCtx}

private theorem halt_bind {α β : Type} (h : Halt) (k : α → EM E Γ β) :
    (halt h >>= k : EM E Γ β) = halt h := rfl

/-- An exhausted horizon stays exhausted, independent of metadata. -/
theorem call_zero (G : Glob E) (F : Fr) (a : Address) (v : Word)
    (input : Bytes) (requested : Bool) :
    callAddr G F 0 a v input requested = halt .timeout := by
  rw [callAddr]

/-- Depth failure precedes value/static checks and does not execute a callee. -/
theorem call_depth (G : Glob E) (F : Fr) (n : Nat) (a : Address) (v : Word)
    (input : Bytes) (requested : Bool) (h : F.depth ≥ 1024) :
    callAddr G F (n + 1) a v input requested = pure (.revert []) := by
  simp only [callAddr, h, ↓reduceIte]

/-- A value-bearing call in an inherited static frame halts the caller,
not a catchable callee outcome; receiver identity is unrestricted. -/
theorem call_static_value (G : Glob E) (F : Fr) (n : Nat) (a : Address) (v : Word)
    (input : Bytes) (requested : Bool) (depth : ¬ F.depth ≥ 1024)
    (static : F.static = true) (nonzero : v.val ≠ 0) :
    callAddr G F (n + 1) a v input requested = halt (.revert []) := by
  simp [callAddr, depth, static, nonzero, halt_bind]

/-- The real interpreter refuses every journal operation in a static frame. -/
theorem static_operation (F : Fr) (o : Op E.layout E.lay E.lay)
    (h : F.static = true) :
    applyOp (Γ := Γ) F o = halt (.revert []) := by
  simp only [applyOp, h, ↓reduceIte, halt_bind]

/-- Return failure is raised before the caller can consume any return values. -/
theorem return_revert (rs : List STy) (data : Bytes) :
    extReturn (E := E) (Γ := Γ) rs (.revert data) = halt (.revert data) := by
  rfl

/-- Declared returns must fit even when their values will later be discarded. -/
theorem return_short (rs : List STy) (data : Bytes)
    (short : data.length < 32 * rs.length) :
    extReturn (E := E) (Γ := Γ) rs (.success data) = halt (.revert []) := by
  simp [extReturn, reraise, short, halt_bind]

/-- Static inheritance is monotone: a child cannot request a downgrade. -/
theorem inherited_static (requested : Bool) : requested || true = true := by
  cases requested <;> rfl

end Solidity.Backend.Passes.SourceCallBoundary
