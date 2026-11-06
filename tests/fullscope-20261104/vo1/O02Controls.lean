import Solidity.Optimizer.Simplify
import Solidity.Optimizer.Laws
import Solidity.Optimizer.UnusedVar
import Solidity.Optimizer.DeadCode

/-!
# O02 value-pass controls

Kernel-checked witnesses on the existing typed IR and its interpreter:
each pass changes a nontrivial program, the changed program runs exactly as
the original, failures (checked overflow `revert`, `assert` Panic) survive,
and the restricted rules leave the forms they must not touch unchanged.
-/
namespace Solidity.Optimizer.O02Controls
open Solidity Solidity.Optimizer.ConstFold

abbrev C := StandardExample
abbrev G : Ctx := [.val .uint]
abbrev G2 : Ctx := [.val .uint, .val .uint]

def lit (n : Nat) (h : PrimTy.uint.inRange n = true := by decide) : Val C Γ .uint :=
  .simple (.lit n h)

def add (a b : Val C Γ .uint) : Val C Γ .uint := .binop .add rfl rfl a b
def gt (a b : Val C Γ .uint) : Val C Γ .bool := .binop .gt rfl rfl a b
def maxU : Val C Γ .uint := lit (2 ^ 256 - 1)

def x : Val C G .uint := .simple (.local .here)

/-! ## Constant folding -/

/-- `2 + 3` folds to the literal `5`. -/
theorem fold_add : (add (lit 2) (lit 3) : Val C [] .uint).cfold = lit 5 := rfl

/-- Checked overflow is not folded: the node stays, and it still reverts. -/
theorem overflow_kept : (add maxU (lit 1) : Val C [] .uint).cfold = add maxU (lit 1) := rfl

theorem overflow_reverts (σ : State C []) :
    (add maxU (lit 1) : Val C [] .uint).cfold.evalT σ = .error .revert := rfl

/-- `x + (2 + 3)` folds its constant operand only. -/
theorem fold_inner : (add x (add (lit 2) (lit 3))).cfold = add x (lit 5) := rfl

/-- `balances[2 + 3]`: the index inside a storage read is folded. -/
def balRead (i : Val C [] .uint) : Val C [] .uint :=
  .read (.index .map (.loc (.root (T := .ref (.mapping .uint (.prim .uint))) "balances" rfl)) i)

theorem index_folded : (balRead (add (lit 2) (lit 3))).cfold = balRead (lit 5) := rfl

/-- `delete balances[1 + 1];`: the statement's location index is folded. -/
def balLoc (i : Val C [] .uint) : Loc C [] (.prim .uint) :=
  .index .map (.loc (.root (T := .ref (.mapping .uint (.prim .uint))) "balances" rfl)) i

theorem delete_index_folded :
    Prog.cfold (.cons (.delete (balLoc (add (lit 1) (lit 1)))) .nil : Prog C [] []) =
      .cons (.delete (balLoc (lit 2))) .nil := rfl

/-- `assert(3 > 2 + 4)`: the condition folds to `false`, the `assert` stays,
and the program still halts with Panic. -/
def assertProg : Prog C [] [] := .cons (.assert (gt (lit 3) (add (lit 2) (lit 4)))) .nil

theorem assert_folded :
    Prog.cfold assertProg = .cons (.assert (.simple (.bool false))) .nil := rfl

theorem assert_panics (σ : State C []) :
    Prog.runC (Prog.cfold assertProg) σ = .error .panic := rfl

theorem assert_same : Prog.runC (Prog.cfold assertProg) = Prog.runC assertProg :=
  Prog.cfold_runC assertProg

/-- `require(1 + 1 > 1); revert;`: the satisfied `require` is dropped. -/
def requireProg : Prog C [] [] :=
  .cons (.require (gt (add (lit 1) (lit 1)) (lit 1))) (.cons .revert .nil)

theorem require_dropped : Prog.cfold requireProg = .cons .revert .nil := rfl

/-- `if (2 > 3) { revert; } else { }` becomes the block of the else branch. -/
def iteProg : Prog C [] [] := .cons (.ite (gt (lit 2) (lit 3)) (.cons .revert .nil) .nil) .nil

theorem ite_pruned : Prog.cfold iteProg = .cons (.block .nil) .nil := rfl

theorem ite_runs (σ : State C []) : (Prog.runC (Prog.cfold iteProg) σ).toBool = true := rfl

/-! ## Constant and copy propagation -/

/-- `uint a = 5; uint b = a + 1;` becomes `uint a = 5; uint b = 6;`. -/
def propProg : Prog C [] [.val .uint, .val .uint] :=
  .cons (.declLocal .uint (.user "a") (some (lit 5)))
    (.cons (.declLocal .uint (.user "b") (some (add (.simple (.local .here)) (lit 1)))) .nil)

theorem prop_constant : Prog.cprop Facts.empty propProg =
    .cons (.declLocal .uint (.user "a") (some (lit 5)))
      (.cons (.declLocal .uint (.user "b") (some (lit 6))) .nil) := rfl

/-- `uint a = 5; total = a; uint b = a + 1;`: the fact survives the storage write. -/
def storeProp : Prog C [] [.val .uint, .val .uint] :=
  .cons (.declLocal .uint (.user "a") (some (lit 5)))
    (.cons (.assign (.root (T := .prim .uint) "total" rfl) (.val (.simple (.local .here))))
      (.cons (.declLocal .uint (.user "b") (some (add (.simple (.local .here)) (lit 1)))) .nil))

theorem prop_across_store : Prog.cprop Facts.empty storeProp =
    .cons (.declLocal .uint (.user "a") (some (lit 5)))
      (.cons (.assign (.root (T := .prim .uint) "total" rfl) (.val (lit 5)))
        (.cons (.declLocal .uint (.user "b") (some (lit 6))) .nil)) := rfl

/-- `uint b = a; uint c = b;` (copy) reads `a` in place of `b`. -/
def copyProg : Prog C G [.val .uint, .val .uint, .val .uint] :=
  .cons (.declLocal .uint (.user "b") (some x))
    (.cons (.declLocal .uint (.user "c") (some (.simple (.local .here)))) .nil)

theorem prop_copy : Prog.cprop Facts.empty copyProg =
    .cons (.declLocal .uint (.user "b") (some x))
      (.cons (.declLocal .uint (.user "c") (some (.simple (.local (.there .here))))) .nil) := rfl

/-- `uint b = a; a = 7; uint c = b;`: assigning `a` kills the copy fact, so `c`
still reads `b` (reading `a` would observe `7`). -/
def killProg : Prog C G [.val .uint, .val .uint, .val .uint] :=
  .cons (.declLocal .uint (.user "b") (some x))
    (.cons (.assignLocal (.there .here) (lit 7))
      (.cons (.declLocal .uint (.user "c") (some (.simple (.local .here)))) .nil))

theorem prop_killed : Prog.cprop Facts.empty killProg =
    .cons (.declLocal .uint (.user "b") (some x))
      (.cons (.assignLocal (.there .here) (lit 7))
        (.cons (.declLocal .uint (.user "c") (some (.simple (.local .here)))) .nil)) := rfl

theorem prop_same : Prog.runC (Prog.cprop Facts.empty killProg) = Prog.runC killProg :=
  Prog.cprop_empty_runC killProg

/-! ## Simplification -/

/-- `a + 0 → a`. -/
theorem simp_add_zero : (add x (lit 0)).simp = x := rfl

/-- `a - a → 0` for a local. -/
theorem simp_sub_self : (Val.binop .sub rfl rfl x x : Val C G .uint).simp = lit 0 := rfl

/-- `(max + 1) - (max + 1)` is not rewritten: its operand reverts. -/
def overflowSub : Val C [] .uint := .binop .sub rfl rfl (add maxU (lit 1)) (add maxU (lit 1))

theorem simp_sub_overflow_kept : overflowSub.simp = overflowSub := rfl

/-- Negative control: the unrestricted `X - X → 0` would change the result. -/
theorem unrestricted_sub_wrong (σ : State C []) :
    overflowSub.evalT σ ≠ (lit 0 : Val C [] .uint).evalT σ := by
  intro h
  cases h

/-- Negative control: `X * 0 → 0` for a reverting `X` changes the result, and
the simplifier does not apply it. -/
def overflowMul : Val C [] .uint := .binop .mul rfl rfl (add maxU (lit 1)) (lit 0)

theorem simp_mul_zero_kept : overflowMul.simp = overflowMul := rfl

theorem unrestricted_mul_wrong (σ : State C []) :
    overflowMul.evalT σ ≠ (lit 0 : Val C [] .uint).evalT σ := by
  intro h
  cases h

/-- `s * 0 → 0`, `a ** 1 → a` and `s < s → false` (added solc rules). -/
theorem simp_mul_zero : (Val.binop .mul rfl rfl x (lit 0) : Val C G .uint).simp = lit 0 := rfl

theorem simp_pow_one :
    (Val.binop .pow rfl rfl (add x (lit 2)) (lit 1) : Val C G .uint).simp = add x (lit 2) := rfl

theorem simp_lt_self : (Val.binop .lt rfl rfl x x : Val C G .bool).simp = .simple (.bool false) :=
  rfl

/-! ## Short circuit, dead loops, untouched statements -/

/-- `false && (max + 1 > 0)` folds to `false` without the overflowing operand. -/
theorem short_circuit :
    (Val.binop .and rfl rfl (.simple (.bool false)) (gt (add maxU (lit 1)) (lit 0)) :
      Val C [] .bool).cfold = .simple (.bool false) := rfl

/-- `while (1 > 2) { revert; } revert;`: the dead loop is dropped. -/
def deadLoop : Prog C [] [] :=
  .cons (.loop .auto (gt (lit 1) (lit 2)) (.cons .revert .nil)) (.cons .revert .nil)

theorem dead_loop_dropped : Prog.cfold deadLoop = .cons .revert .nil := rfl

/-- `uint a = 5; while (a > 0) { a = a - 1; }`: entry facts are not used in the
loop, so its condition and body still read `a`. -/
def loopProg : Prog C [] [.val .uint] :=
  .cons (.declLocal .uint (.user "a") (some (lit 5)))
    (.cons (.loop .auto (gt (.simple (.local .here)) (lit 0))
      (.cons (.assignLocal .here (.binop .sub rfl rfl (.simple (.local .here)) (lit 1))) .nil))
      .nil)

theorem loop_facts_discarded : Prog.cprop Facts.empty loopProg = loopProg := rfl

/-- A storage write is left as written by every O02 pass. -/
def storageProg : Prog C [] [] := .cons (.delete (.root (T := .prim .uint) "total" rfl)) .nil

theorem storage_untouched :
    Prog.cfold storageProg = storageProg ∧ Prog.cprop Facts.empty storageProg = storageProg ∧
      Prog.simplify storageProg = storageProg ∧ Prog.uve storageProg = storageProg :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `total = 2 + 3; total += 0 + 1;`: both value positions are folded. -/
def storeProg : Prog C [] [] :=
  .cons (.assign (.root (T := .prim .uint) "total" rfl) (.val (add (lit 2) (lit 3))))
    (.cons (.opAssign .add rfl rfl (.root "total" rfl) (add (lit 0) (lit 1))) .nil)

theorem store_folded : Prog.cfold storeProg =
    .cons (.assign (.root (T := .prim .uint) "total" rfl) (.val (lit 5)))
      (.cons (.opAssign .add rfl rfl (.root "total" rfl) (lit 1)) .nil) := rfl

theorem store_same : Prog.runC (Prog.cfold storeProg) = Prog.runC storeProg :=
  Prog.cfold_runC storeProg

/-! ## Code after a halting statement -/

/-- `{ require(1 > 2); total = 1; uint z = 2; }` becomes `{ require(1 > 2); }`
once folded: the condition is the literal `false`, so the rest never runs. -/
def afterHalt : Stmt C [] [] :=
  .block (.cons (.require (gt (lit 1) (lit 2)))
    (.cons (.assign (.root (T := .prim .uint) "total" rfl) (.val (lit 1)))
      (.cons (.declLocal .uint (.user "z") (some (lit 2))) .nil)))

theorem after_halt_cut :
    Prog.dce (Prog.cfold (.cons afterHalt .nil)) =
      .cons (.block (.cons (.require (.simple (.bool false))) .nil)) .nil := rfl

theorem after_halt_reverts (σ : State C []) :
    Prog.runC (Prog.dce (Prog.cfold (.cons afterHalt .nil))) σ = .error .revert := rfl

/-- A non-literal `require(a > 1)` is not a halt: the rest of the block stays. -/
def guarded : Stmt C G G :=
  .block (.cons (.require (gt x (lit 1))) (.cons (.assignLocal .here (lit 3)) .nil))

theorem guarded_kept : Prog.dce (.cons guarded .nil) = .cons guarded .nil := rfl

/-- Inside an `if` branch: `if (a > 1) { revert; a = 3; }` loses `a = 3`. -/
theorem branch_cut :
    Prog.dce (.cons (.ite (gt x (lit 1)) (.cons .revert (.cons (.assignLocal .here (lit 3)) .nil))
      .nil) .nil : Prog C G G) =
      .cons (.ite (gt x (lit 1)) (.cons .revert .nil) .nil) .nil := rfl

/-- The `require` itself is never cut: dropping it would turn the revert into success. -/
theorem halt_kept_wrong (σ : State C []) :
    Prog.runC (.cons afterHalt .nil) σ ≠
      Prog.runC (.cons (.block .nil) .nil : Prog C [] []) σ := by
  intro h
  cases h

/-! ## Dead local stores -/

def y : Val C G2 .uint := .simple (.local (.there .here))

/-- `a = 1; a = b + 2;` becomes `a = b + 2;`. -/
def deadStore (e₁ e₂ : Val C G2 .uint) : Prog C G2 G2 :=
  .cons (.assignLocal .here e₁) (.cons (.assignLocal .here e₂) .nil)

/-- Stores to different locals are both kept. -/
theorem different_targets_kept :
    Prog.dse (.cons (.assignLocal .here (lit 1))
      (.cons (.assignLocal (.there .here) (lit 2)) .nil) : Prog C G2 G2) =
      .cons (.assignLocal .here (lit 1)) (.cons (.assignLocal (.there .here) (lit 2)) .nil) := rfl

theorem dead_store_removed :
    Prog.dse (deadStore (lit 1) (add y (lit 2))) =
      .cons (.assignLocal .here (add y (lit 2))) .nil := rfl

/-- `a = 1; a = a + 2;` is kept: the second right side reads `a`. -/
theorem self_read_kept :
    Prog.dse (deadStore (lit 1) (add (.simple (.local .here)) (lit 2))) =
      deadStore (lit 1) (add (.simple (.local .here)) (lit 2)) := rfl

/-- `a = max + 1; a = 3;` is kept: the first store reverts. -/
theorem failing_store_kept :
    Prog.dse (deadStore (add maxU (lit 1)) (lit 3)) = deadStore (add maxU (lit 1)) (lit 3) := rfl

/-! ## Unused-variable elimination -/

/-- `{ uint y = 5; require(1 > 0); }`: `y` is unused and dropped. -/
def unusedBlock : Stmt C [] [] :=
  .block (.cons (.declLocal .uint (.user "y") (some (lit 5)))
    (.cons (.require (gt (lit 1) (lit 0))) .nil))

theorem unused_dropped :
    Stmt.uve unusedBlock = .block (.cons (.require (gt (lit 1) (lit 0))) .nil) := rfl

/-- `{ uint y = 5; require(y > 1); }`: `y` is read and kept. -/
def usedBlock : Stmt C [] [] :=
  .block (.cons (.declLocal .uint (.user "y") (some (lit 5)))
    (.cons (.require (gt (.simple (.local .here)) (lit 1))) .nil))

theorem used_kept : Stmt.uve usedBlock = usedBlock := rfl

/-- `{ uint y = max + 1; }`: the unused initialiser reverts, so it is kept. -/
def failingInit : Stmt C [] [] :=
  .block (.cons (.declLocal .uint (.user "y") (some (add maxU (lit 1)))) .nil)

theorem failing_init_kept : Stmt.uve failingInit = failingInit := rfl

theorem failing_init_reverts (σ : State C []) : Stmt.runC failingInit σ = .error .revert := rfl

/-- Negative control: dropping that declaration anyway would hide the revert. -/
theorem failing_init_drop_wrong (σ : State C []) :
    Stmt.runC failingInit σ ≠ Stmt.runC (.block (.nil : Prog C [] [])) σ := by
  intro h
  cases h

/-- Composition of the O02 passes in the O01 pipeline is still certified. -/
theorem o02_pipeline_preserves (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ'))
      (Pass.pipeline [Prog.cprop Facts.empty, Prog.simplify, Prog.cfold, Prog.dce, Prog.dse,
        Prog.uve]) :=
  Preserves.pipeline (Related := SameRun) (fun _ => rfl)
    (fun a b => show SameRun _ _ from Eq.trans a b) _ fun pass mem => by
    rcases List.mem_cons.mp mem with rfl | mem
    · exact cprop_preserves Γ Γ'
    rcases List.mem_cons.mp mem with rfl | mem
    · exact vopt_preserves simpFoldPass Γ Γ'
    rcases List.mem_cons.mp mem with rfl | mem
    · exact cfold_preserves Γ Γ'
    rcases List.mem_cons.mp mem with rfl | mem
    · exact dce_preserves Γ Γ'
    rcases List.mem_cons.mp mem with rfl | mem
    · exact dse_preserves Γ Γ'
    rcases List.mem_cons.mp mem with rfl | mem
    · exact uve_preserves Γ Γ'
    exact absurd mem List.not_mem_nil

#print axioms Val.cfold_evalT
#print axioms Prog.cfold_runC
#print axioms Prog.cprop_empty_runC
#print axioms Val.simp_evalT
#print axioms Prog.simplify_runC
#print axioms o02_pipeline_preserves
#print axioms assert_panics
#print axioms prop_constant
#print axioms unrestricted_mul_wrong
#print axioms Prog.uve_runC
#print axioms Prog.dce_runC
#print axioms cut_scope
#print axioms Prog.dse_runC
#print axioms blockDecl_runC
#print axioms unused_dropped

end Solidity.Optimizer.O02Controls
