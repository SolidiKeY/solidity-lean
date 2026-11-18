import Solidity.Goals.YulAcceptedCompilesWithArtifact

/-! Pin and controls for the plan goal `yulAcceptedCompilesWithArtifact`. -/

namespace Solidity.Goals

/--
info: open Solidity.Goals.yulAcceptedCompilesWithArtifact ← Solidity.Yul.accepted_compiles_with_artifact plan y1-yul-artifact-producers
-/
#guard_msgs in
#roadmap_goal yulAcceptedCompilesWithArtifact

/-! The accepted Yul language is inhabited at every local count and control, is
closed under arbitrarily deep composition and arithmetic nesting, admits
nonzero newer-prefix depths, and refuses constructors the producer does not
visit. -/
namespace YulArtifact

/-- Two operands for a binary builtin, left first. -/
def operands {n : Nat} (left right : Yul.Expr [] [] n 1) : Fin 2 → Yul.Expr [] [] n 1 :=
  fun k => if k.val = 0 then left else right

/-- `x := (x + w) * (y - x)`, then `y := x`. -/
def sample {c : Yul.Control} {n : Nat} (x y : Fin n) (w : Yul.Word) : Yul.Stmt [] [] c n :=
  .seq
    (.assign (fun _ => .local x) (.builtin (.pure .mul) (operands
      (.builtin (.pure .add) (operands (.local x) (.literal w)))
      (.builtin (.pure .sub) (operands (.local y) (.local x))))))
    (.assign (fun _ => .local y) (.local x))

example {c : Yul.Control} {n : Nat} (x y : Fin n) (w : Yul.Word) :
    Accepted (sample (c := c) x y w) :=
  .seq (.assign _ (.binary (.inr (.inr rfl))
      (.binary (.inl rfl) (.local x) (.literal w))
      (.binary (.inr (.inl rfl)) (.local y) (.local x))))
    (.assign _ (.local x))

/-- Composition of `k + 1` copies of a statement. -/
def iterate {c : Yul.Control} {n : Nat} (s : Yul.Stmt [] [] c n) : Nat → Yul.Stmt [] [] c n
  | 0 => s
  | k + 1 => .seq s (iterate s k)

example {c : Yul.Control} {n : Nat} (s : Yul.Stmt [] [] c n) (accepted : Accepted s)
    (k : Nat) : Accepted (iterate s k) := by
  induction k with
  | zero => exact accepted
  | succ k ih => exact .seq accepted ih

/-- With locals `0` and `1`, `sample` fits under three newer words. -/
example {c : Yul.Control} (w : Yul.Word) :
    Fits 3 (sample (c := c) (0 : Fin 2) 1 w) :=
  .seq (.assign _ (fun i same => by cases same; decide)
      (.builtin
        (.builtin (.local (height := 3) (0 : Fin 2) (by decide))
          (.local (height := 4) (1 : Fin 2) (by decide)))
        (.builtin (.literal _ _) (.local (height := 5) (0 : Fin 2) (by decide)))))
    (.assign _ (fun i same => by cases same; decide)
      (.local (height := 3) (0 : Fin 2) (by decide)))

/-- `Fits` is a real limit: a write to local 0 under sixteen newer words has no
SWAP reach. -/
example {c : Yul.Control} (w : Yul.Word) :
    ¬ Fits 16 (.assign (c := c) (fun _ => .local (0 : Fin 1)) (.literal w)) := by
  intro fits
  cases fits with
  | assign _ reach _ => exact absurd (reach 0 rfl) (by decide)

example {c : Yul.Control} {n : Nat} (test : Yul.Expr [] [] n 1) (body : Yul.Stmt [] [] c n) :
    ¬ Accepted (.if_ test body) := nofun

end YulArtifact

end Solidity.Goals
