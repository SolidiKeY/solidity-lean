import Solidity.Optimizer.CSE
import Solidity.Optimizer.Laws
import Solidity.Optimizer.Inline
import Solidity.Optimizer.Pipeline

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

/-- `uint b = a + 1; total = b; uint c = a + 1;`: the entry survives the store. -/
def storeCse : Prog C G [.val .uint, .val .uint, .val .uint] :=
  .cons (.declLocal .uint (.user "b") (some (add (.simple (.local .here)) (lit 1))))
    (.cons (.assign (.root (T := .prim .uint) "total" rfl) (.val (.simple (.local .here))))
      (.cons (.declLocal .uint (.user "c") (some aPlus1)) .nil))

theorem cse_across_store : Prog.cse [] storeCse =
    .cons (.declLocal .uint (.user "b") (some (add (.simple (.local .here)) (lit 1))))
      (.cons (.assign (.root (T := .prim .uint) "total" rfl) (.val (.simple (.local .here))))
        (.cons (.declLocal .uint (.user "c") (some (.simple (.local .here)))) .nil)) := rfl

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

/-! ## Inlining -/

def gt {Γ : Ctx} (a b : Val C Γ .uint) : Val C Γ .bool := .binop .gt rfl rfl a b

/-- `function f(uint x) internal { require(x > 3); }` -/
def fBody : Prog C ([] ++ [.val .uint]) [.val .uint] :=
  .cons (.require (gt (.simple (.local .here)) (lit 3))) .nil

/-- `f(a + 1);` in a caller with one local `a`. -/
def callF : Stmt C G G :=
  .call "f" (.snoc .nil .uint (.user "x") (add (.simple (.local .here)) (lit 1))) .none fBody

/-- The call becomes `{ uint x = a + 1; require(x > 3); }`. -/
theorem call_inlined : Stmt.inl callF =
    .block (.cons (.declLocal .uint (.user "x") (some (add (.simple (.local .here)) (lit 1))))
      (.cons (.require (gt (.simple (.local .here)) (lit 3))) .nil)) := rfl

def withA (n : Nat) : State C G := (State.init C).push (t := .val .uint) (uintOfNat n)

/-- With `a = 5` both forms succeed; with `a = 1` both revert. -/
theorem inlined_ok : (Stmt.runC (Stmt.inl callF) (withA 5)).toBool = true := rfl
theorem call_ok : (Stmt.runC callF (withA 5)).toBool = true := rfl
theorem inlined_reverts : Stmt.runC (Stmt.inl callF) (withA 1) = .error .revert := rfl
theorem call_reverts : Stmt.runC callF (withA 1) = .error .revert := rfl

theorem inline_same : Stmt.runC (Stmt.inl callF) = Stmt.runC callF := Stmt.inl_runC callF

/-- `function h(uint x, uint y) internal { require(y < x); }` called as
`h(a + 10, a)`: the second argument reads the caller's `a`, one local below the
first parameter once inlined. -/
def hBody : Prog C ([] ++ [.val .uint, .val .uint]) [.val .uint, .val .uint] :=
  .cons (.require (.binop .lt rfl rfl (.simple (.local .here)) (.simple (.local (.there .here)))))
    .nil

def callH : Stmt C G G :=
  .call "h" (.snoc (.snoc .nil .uint (.user "x") (add (.simple (.local .here)) (lit 10)))
    .uint (.user "y") (.simple (.local .here))) .none hBody

theorem two_args_inlined : Stmt.inl callH =
    .block (.cons (.declLocal .uint (.user "x") (some (add (.simple (.local .here)) (lit 10))))
      (.cons (.declLocal .uint (.user "y") (some (.simple (.local (.there .here)))))
        (.cons (.require (.binop .lt rfl rfl (.simple (.local .here))
          (.simple (.local (.there .here))))) .nil))) := rfl

theorem two_args_ok : (Stmt.runC (Stmt.inl callH) (withA 5)).toBool = true := rfl
theorem two_args_call_ok : (Stmt.runC callH (withA 5)).toBool = true := rfl

/-- Negative control: an inliner that does not re-index the later argument
makes `y` read the parameter `x` (`a + 10`), so `require(y < x)` reverts. -/
def wrongInline : Stmt C G G :=
  .block (.cons (.declLocal .uint (.user "x") (some (add (.simple (.local .here)) (lit 10))))
    (.cons (.declLocal .uint (.user "y") (some (.simple (.local .here))))
      (.cons (.require (.binop .lt rfl rfl (.simple (.local .here))
        (.simple (.local (.there .here))))) .nil)))

theorem wrong_inline_reverts : Stmt.runC wrongInline (withA 5) = .error .revert := rfl

/-- `a = g(a)` for `function g(uint x) internal returns (uint r) { r = x + 2; }`. -/
def gBody : Prog C ([.val .uint] ++ [.val .uint]) [.val .uint, .val .uint] :=
  .cons (.assignLocal .here (add (.simple (.local (.there .here))) (lit 2))) .nil

def callRet : Stmt C G G :=
  .call "g" (.snoc .nil .uint (.user "x") (.simple (.local .here)))
    (.val .uint (.user "r") (some .here)) gBody

/-- The call becomes `{ uint x = a; uint r; { r = x + 2; } a = r; }`. -/
theorem ret_call_inlined : Stmt.inl callRet =
    .block (.cons (.declLocal .uint (.user "x") (some (.simple (.local .here))))
      (.cons (.declLocal .uint (.user "r") none)
        (.cons (.block (.cons (.assignLocal .here (add (.simple (.local (.there .here))) (lit 2)))
          .nil))
          (.cons (.assignLocal (.there (.there .here)) (.simple (.local .here))) .nil)))) := rfl

/-- The caller's `a` after the call / the inlined block, from `a = 5`. -/
def aAfter (r : TRes (Out C (withA 5).H G)) : TRes Int :=
  r.map fun o => (TEnv.get .here o.st.env : PrimTy.uint.Denote).1

theorem ret_call_seven : aAfter (Stmt.runC callRet (withA 5)) = .ok 7 := rfl
theorem ret_inlined_seven : aAfter (Stmt.runC (Stmt.inl callRet) (withA 5)) = .ok 7 := rfl

/-- `g2(a)` for `function g2(uint x) internal returns (uint r) { r = r + x + 2; }`,
reading the return variable's default; once assigned to `a`, once discarded. -/
def g2Body : Prog C ([.val .uint] ++ [.val .uint]) [.val .uint, .val .uint] :=
  .cons (.assignLocal .here
    (add (add (.simple (.local .here)) (.simple (.local (.there .here)))) (lit 2))) .nil

def callG2 (res : Option (Idx G (.val .uint))) : Stmt C G G :=
  .call "g2" (.snoc .nil .uint (.user "x") (.simple (.local .here)))
    (.val .uint (.user "r") res) g2Body

theorem g2_assigned : aAfter (Stmt.runC (Stmt.inl (callG2 (some .here))) (withA 5)) = .ok 7 := rfl
theorem g2_call_assigned : aAfter (Stmt.runC (callG2 (some .here)) (withA 5)) = .ok 7 := rfl
theorem g2_discarded : aAfter (Stmt.runC (Stmt.inl (callG2 none)) (withA 5)) = .ok 5 := rfl
theorem g2_call_discarded : aAfter (Stmt.runC (callG2 none) (withA 5)) = .ok 5 := rfl

/-- Negative control: writing the result to the parameter slot instead of `a`
(a wrong target index) leaves `a = 5` where the call gives `7`. -/
def wrongTarget : Stmt C G G :=
  .block (.cons (.declLocal .uint (.user "x") (some (.simple (.local .here))))
    (.cons (.declLocal .uint (.user "r") none)
      (.cons (.block (g2Body.wk (thinTop G [.val .uint, .val .uint])).2.2)
        (.cons (.assignLocal (.there .here) (.simple (.local .here))) .nil))))

theorem wrong_target_differs : aAfter (Stmt.runC wrongTarget (withA 5)) = .ok 5 := rfl

/-- A value-returning call with a storage argument: since the X06 follow-up it is
inlined, the parameter bound as a storage alias (`bindArgs`). -/
def callStorageArg : Stmt C G G :=
  .call "s" (.snocStorage .nil (.array (.prim .uint)) (.user "v") (.loc (.root "values" rfl)))
    (.val .uint (.user "r") (some .here)) (.cons (.assignLocal .here (lit 1)) .nil)

theorem storage_arg_inlined : Stmt.inl callStorageArg =
    inlineBlockVal (.snocStorage .nil (.array (.prim .uint)) (.user "v") (.loc (.root "values" rfl)))
      .uint (.user "r") (some .here) (.cons (.assignLocal .here (lit 1)) .nil) := rfl

theorem storage_arg_same : aAfter (Stmt.runC (Stmt.inl callStorageArg) (withA 5)) =
    aAfter (Stmt.runC callStorageArg (withA 5)) := by
  rw [Stmt.inl_runC]

/-- A call with a memory return is left as written. -/
def callMem : Stmt C G (.mem (.array (.prim .uint)) :: G) :=
  .call "m" .nil (.mem (.array (.prim .uint)) (.user "r") rfl rfl) .nil

theorem mem_call_kept : Stmt.inl callMem = callMem := rfl

/-! ## The whole pipeline -/

/-- `uint a = 2; f(a + 3);` with `f(x) { require(x > 3); }`. -/
def e2e : Prog C [] [.val .uint] :=
  .cons (.declLocal .uint (.user "a") (some (lit 2)))
    (.cons (.call "f" (.snoc .nil .uint (.user "x") (add (.simple (.local .here)) (lit 3)))
      .none fBody) .nil)

/-- One round: inlined, `x = 5` propagated, `require(5 > 3)` folded and dropped, the
unused `x` removed: `uint a = 2; { }`. -/
theorem e2e_optimized : Prog.optimize 1 e2e =
    .cons (.declLocal .uint (.user "a") (some (lit 2))) (.cons (.block .nil) .nil) := rfl

theorem e2e_same : Prog.runC (Prog.optimize 1 e2e) = Prog.runC e2e := Prog.optimize_runC 1 e2e

#print axioms Prog.optimize_runC
#print axioms e2e_optimized
#print axioms inlineBlock_runC
#print axioms Prog.inl_runC
#print axioms call_inlined
#print axioms wrong_inline_reverts
#print axioms inlineBlockVal_runC
#print axioms ret_inlined_seven
#print axioms Val.pbeq_eq
#print axioms Val.cse_evalT
#print axioms Prog.cse_empty_runC
#print axioms cse_replaced
#print axioms wrong_kill_differs

end Solidity.Optimizer.O03Controls
