import Solidity.Optimizer.CSE
import Solidity.Optimizer.Laws

/-!
# O03 common-subexpression elimination controls

Kernel-checked witnesses on the existing typed IR: a repeated expression is
replaced by the local holding it, an assignment to an operand kills the entry,
and the rewritten program runs exactly as the original.
-/
namespace Solidity.Optimizer.O03Controls
open Solidity Solidity.Optimizer.ConstFold

abbrev C := StandardExample
abbrev G : Ctx := [.val .uint]

def lit {Γ : Ctx} (n : Nat) (h : PrimTy.uint.inRange n = true := by decide) : Val C Γ .uint :=
  .simple (.lit n h)

def add {Γ : Ctx} (a b : Val C Γ .uint) : Val C Γ .uint := .binop .add rfl rfl a b

/-- `a + 1` read in the context `[b, a]`. -/
def aPlus1 : Val C [.val .uint, .val .uint] .uint := add (.simple (.local (.there .here))) (lit 1)

/-- `uint b = a + 1; uint c = a + 1;` becomes `uint b = a + 1; uint c = b;`. -/
def cseProg : Prog C G [.val .uint, .val .uint, .val .uint] :=
  .cons (.declLocal .uint (.user "b") (some (add (.simple (.local .here)) (lit 1))))
    (.cons (.declLocal .uint (.user "c") (some aPlus1)) .nil)

theorem cse_replaced : Prog.cse [] cseProg =
    .cons (.declLocal .uint (.user "b") (some (add (.simple (.local .here)) (lit 1))))
      (.cons (.declLocal .uint (.user "c") (some (.simple (.local .here)))) .nil) := rfl

theorem cse_same : Prog.runC (Prog.cse [] cseProg) = Prog.runC cseProg :=
  Prog.cse_empty_runC cseProg

/-- `uint b = a + 1; a = 7; uint c = a + 1;`: the assignment to `a` kills the
entry, so `c` still computes `a + 1` (reading `b` would observe the old `a`). -/
def killProg : Prog C G [.val .uint, .val .uint, .val .uint] :=
  .cons (.declLocal .uint (.user "b") (some (add (.simple (.local .here)) (lit 1))))
    (.cons (.assignLocal (.there .here) (lit 7))
      (.cons (.declLocal .uint (.user "c") (some aPlus1)) .nil))

theorem cse_killed : Prog.cse [] killProg = killProg := rfl

/-- Negative control: the unkilled rewrite changes the result. With `a = 0`
initially, `c` would read `b = 1` instead of `7 + 1 = 8`. -/
def wrongKill : Prog C G [.val .uint, .val .uint, .val .uint] :=
  .cons (.declLocal .uint (.user "b") (some (add (.simple (.local .here)) (lit 1))))
    (.cons (.assignLocal (.there .here) (lit 7))
      (.cons (.declLocal .uint (.user "c") (some (.simple (.local .here)))) .nil))

def start : State C G := (State.init C).push (t := .val .uint) (uintOfNat 0)

/-- The value of the last local `c` after a run. -/
def lastLocal (r : TRes (Out C start.H [.val .uint, .val .uint, .val .uint])) : TRes Int :=
  r.map fun o => (TEnv.get .here o.st.env : PrimTy.uint.Denote).1

theorem kill_runs_eight : lastLocal (Prog.runC killProg start) = .ok 8 := rfl

theorem wrong_kill_runs_one : lastLocal (Prog.runC wrongKill start) = .ok 1 := rfl

theorem wrong_kill_differs :
    lastLocal (Prog.runC wrongKill start) ≠ lastLocal (Prog.runC killProg start) := by
  rw [kill_runs_eight, wrong_kill_runs_one]
  intro h
  injection h with h
  omega

theorem cse_pipeline (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ')) (Prog.cse []) :=
  cse_preserves Γ Γ'

#print axioms Val.pbeq_eq
#print axioms Val.cse_evalT
#print axioms Prog.cse_empty_runC
#print axioms cse_replaced
#print axioms wrong_kill_differs

end Solidity.Optimizer.O03Controls
