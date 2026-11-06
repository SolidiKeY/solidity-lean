import Solidity.Optimizer.Loads
import Solidity.Optimizer.DeadStore
import Solidity.Optimizer.LICM
import Solidity.Optimizer.Pipeline

/-!
# X06 memory-optimization controls

Kernel-checked positive, negative and satisfiability controls for the X06
passes over the existing typed IR (`StandardExample`): redundant load
elimination (`Prog.rle`).
-/
namespace Solidity.Optimizer.X06Controls
open Solidity Solidity.Optimizer.ConstFold

abbrev C := StandardExample

def lit {Γ : Ctx} (n : Nat) (h : PrimTy.uint.inRange n = true := by decide) : Val C Γ .uint :=
  .simple (.lit n h)

/-- `total`, a storage read. -/
def total {Γ : Ctx} : Val C Γ .uint := .read (.root "total" rfl)

/-- `total = v;` -/
def setTotal {Γ : Ctx} (v : Val C Γ .uint) : Stmt C Γ Γ :=
  .assign (.root (T := .prim .uint) "total" rfl) (.val v)

/-- `age = v;` -/
def setAge {Γ : Ctx} (v : Val C Γ .uint) : Stmt C Γ Γ :=
  .assign (.root (T := .prim .uint) "age" rfl) (.val v)

def here {Γ : Ctx} {p : PrimTy} : Val C (.val p :: Γ) p := .simple (.local .here)

abbrev G2 : Ctx := [.val .uint, .val .uint]

/-- The value of the innermost local after a run from the initial state, with
`total` and `age` set first. -/
def start : State C [] := State.init C

def topOf {Γ : Ctx} (r : TRes (Out C start.H (.val .uint :: Γ))) : TRes Int :=
  r.map fun o => (TEnv.get .here o.st.env : PrimTy.uint.Denote).1

/-! ## Redundant load elimination -/

/-- `total = 3; uint a = total; uint b = total;` becomes
`total = 3; uint a = 3; uint b = 3;`: store-to-load forwarding, then the
forwarded value again. -/
def twoLoads : Prog C [] G2 :=
  .cons (setTotal (lit 3))
    (.cons (.declLocal .uint (.user "a") (some total))
      (.cons (.declLocal .uint (.user "b") (some total)) .nil))

theorem rle_forwarded : Prog.rle [] twoLoads =
    .cons (setTotal (lit 3))
      (.cons (.declLocal .uint (.user "a") (some (lit 3)))
        (.cons (.declLocal .uint (.user "b") (some (lit 3))) .nil)) := rfl

/-- `uint a = total; uint b = total;` becomes `uint a = total; uint b = a;`. -/
def loadLoad : Prog C [] G2 :=
  .cons (.declLocal .uint (.user "a") (some total))
    (.cons (.declLocal .uint (.user "b") (some total)) .nil)

theorem rle_load_load : Prog.rle [] loadLoad =
    .cons (.declLocal .uint (.user "a") (some total))
      (.cons (.declLocal .uint (.user "b") (some here)) .nil) := rfl

/-- Root separation: `uint a = total; age = 5; uint b = total;` still reuses `a`
(the write to `age` cannot alias `total`). -/
def otherRoot : Prog C [] G2 :=
  .cons (.declLocal .uint (.user "a") (some total))
    (.cons (setAge (lit 5))
      (.cons (.declLocal .uint (.user "b") (some total)) .nil))

theorem rle_other_root : Prog.rle [] otherRoot =
    .cons (.declLocal .uint (.user "a") (some total))
      (.cons (setAge (lit 5))
        (.cons (.declLocal .uint (.user "b") (some here)) .nil)) := rfl

/-- Kill: `uint a = total; total = 7; uint b = total;` is left as written. -/
def killed : Prog C [] G2 :=
  .cons (.declLocal .uint (.user "a") (some total))
    (.cons (setTotal (lit 7))
      (.cons (.declLocal .uint (.user "b") (some total)) .nil))

theorem rle_killed : Prog.rle [] killed =
    .cons (.declLocal .uint (.user "a") (some total))
      (.cons (setTotal (lit 7))
        (.cons (.declLocal .uint (.user "b") (some (lit 7))) .nil)) := rfl

theorem rle_same (P : Prog C [] G2) : Prog.runC (Prog.rle [] P) = Prog.runC P :=
  Prog.rle_empty_runC P

/-- Negative control: without the kill, `uint b = a;` after `total = 7;`
leaves `b = 0` where the program leaves `b = 7`. -/
def wrongKill : Prog C [] G2 :=
  .cons (.declLocal .uint (.user "a") (some total))
    (.cons (setTotal (lit 7))
      (.cons (.declLocal .uint (.user "b") (some here)) .nil))

theorem killed_runs_seven : topOf (Prog.runC killed start) = .ok 7 := rfl
theorem wrong_kill_runs_zero : topOf (Prog.runC wrongKill start) = .ok 0 := rfl

theorem wrong_kill_differs : topOf (Prog.runC wrongKill start) ≠ topOf (Prog.runC killed start) := by
  rw [killed_runs_seven, wrong_kill_runs_zero]
  intro h
  injection h with h
  omega

abbrev uarr : RefTy := .array (.prim .uint)

/-- `xs[k]` for the memory local at `i`. -/
def at_ {Γ : Ctx} (i : Idx Γ (.mem uarr)) (k : Nat) (h : PrimTy.uint.inRange k = true := by decide) :
    MLoc C Γ (.prim .uint) :=
  .index .dyn (.var i rfl) (lit k h)

/-- `uint[] memory xs = new uint[](2);` -/
def newXs {Γ : Ctx} (x : String) : Stmt C Γ (.mem uarr :: Γ) :=
  .declMem uarr (.user x) (some (.newArr (.lit 2 (by decide)) rfl)) rfl rfl

/-- Field sensitivity on indices: `xs[0] = 4; xs[1] = 6; uint a = xs[0];`
becomes `… uint a = 4;` (distinct literal indices never overlap). -/
def memApart : Prog C [] [.val .uint, .mem uarr] :=
  .cons (newXs "xs")
    (.cons (.assignMem (at_ .here 0) (.val (lit 4)))
      (.cons (.assignMem (at_ .here 1) (.val (lit 6)))
        (.cons (.declLocal .uint (.user "a") (some (.readMem (at_ .here 0)))) .nil)))

theorem rle_mem_apart : Prog.rle [] memApart =
    .cons (newXs "xs")
      (.cons (.assignMem (at_ .here 0) (.val (lit 4)))
        (.cons (.assignMem (at_ .here 1) (.val (lit 6)))
          (.cons (.declLocal .uint (.user "a") (some (lit 4))) .nil))) := rfl

/- Memory runs allocate, which the kernel does not unfold here; they are pinned by
the compiled interpreter instead (as `docs/` pins initial-store runs). -/
#guard (topOf (Prog.runC memApart start)).toOption == some 4

/-- Aliasing memory locals: `uint[] memory ys = xs; xs[0] = 4; ys[0] = 6;
uint a = xs[0];` is left as written: `ys[0]` may (and does) alias `xs[0]`. -/
def memAlias : Prog C [] [.val .uint, .mem uarr, .mem uarr] :=
  .cons (newXs "xs")
    (.cons (.declMem uarr (.user "ys") (some (.alias (.var .here rfl))) rfl rfl)
      (.cons (.assignMem (at_ (.there .here) 0) (.val (lit 4)))
        (.cons (.assignMem (at_ .here 0) (.val (lit 6)))
          (.cons (.declLocal .uint (.user "a") (some (.readMem (at_ (.there .here) 0)))) .nil))))

theorem rle_mem_alias : Prog.rle [] memAlias = memAlias := rfl

/-- Negative control: forwarding `4` past the aliasing write. -/
def wrongAlias : Prog C [] [.val .uint, .mem uarr, .mem uarr] :=
  .cons (newXs "xs")
    (.cons (.declMem uarr (.user "ys") (some (.alias (.var .here rfl))) rfl rfl)
      (.cons (.assignMem (at_ (.there .here) 0) (.val (lit 4)))
        (.cons (.assignMem (at_ .here 0) (.val (lit 6)))
          (.cons (.declLocal .uint (.user "a") (some (lit 4))) .nil))))

#guard (topOf (Prog.runC memAlias start)).toOption == some 6
#guard (topOf (Prog.runC wrongAlias start)).toOption == some 4

/-- Satisfiability of `Prog.rle_runC`'s premise with a nonempty entry list:
`total` holds `0` in the initial state. -/
def entry0 : List (LEnt C []) := [⟨.uint, .sroot "total" rfl, .lit 0 (by decide)⟩]

theorem entry0_holds : LEnt.Holds entry0 start := by
  intro a ha
  simp only [entry0, List.mem_singleton] at ha
  subst ha
  rfl

theorem rle_entry0 (P : Prog C [] G2) : Prog.runC (Prog.rle entry0 P) start = Prog.runC P start :=
  Prog.rle_runC entry0 P start entry0_holds

/-! ## Dead store elimination -/

def add {Γ : Ctx} (a b : Val C Γ .uint) : Val C Γ .uint := .binop .add rfl rfl a b

/-- `total = 1; total = 2 + 3;` becomes `total = 2 + 3;`. -/
def deadS : Prog C [] [] := .cons (setTotal (lit 1)) (.cons (setTotal (add (lit 2) (lit 3))) .nil)

theorem dstore_removed : Prog.dstore deadS = .cons (setTotal (add (lit 2) (lit 3))) .nil := rfl

theorem dstore_same (P : Prog C [] []) : Prog.runC (Prog.dstore P) = Prog.runC P :=
  Prog.dstore_runC P

/-- `total = 1; total = total + 1;`: the second value reads `total`, so the first
store is live and kept. -/
def liveS : Prog C [] [] := .cons (setTotal (lit 1)) (.cons (setTotal (add total (lit 1))) .nil)

theorem dstore_live_kept : Prog.dstore liveS = liveS := rfl

/-- Negative control: dropping the live store changes the final storage. -/
def totalOf (r : TRes (Out C start.H [])) : TRes Int :=
  r.map fun o => match o.st.storage.find (SRef.ofRoot (C := C) "total" (T := .prim .uint) rfl) with
    | some v => (v.view : PrimTy.uint.Denote).1
    | none => -1

theorem live_runs_two : totalOf (Prog.runC liveS start) = .ok 2 := rfl
theorem live_dropped_runs_one :
    totalOf (Prog.runC (.cons (setTotal (add total (lit 1))) .nil) start) = .ok 1 := rfl

/-- A first store that can fail is kept: `total = a + 1; total = 2;` with `a` the
largest `uint` reverts, while `total = 2;` alone returns. -/
abbrev maxU : Nat := 2 ^ 256 - 1

def failingFirst : Prog C [.val .uint] [.val .uint] :=
  .cons (setTotal (add here (lit 1))) (.cons (setTotal (lit 2)) .nil)

theorem dstore_failing_kept : Prog.dstore failingFirst = failingFirst := rfl

def startMax : State C [.val .uint] :=
  start.push (t := .val .uint) (⟨maxU, by decide⟩ : PrimTy.uint.Denote)

theorem failing_first_reverts : (Prog.runC failingFirst startMax).toOption.isNone = true := rfl
theorem failing_dropped_returns :
    (Prog.runC (.cons (setTotal (lit 2)) .nil : Prog C [.val .uint] [.val .uint])
      startMax).toOption.isSome = true := rfl

/-- `xs[0] = 1; xs[0] = 2;` becomes `xs[0] = 2;`; `xs[0] = 1; xs[1] = 2;` is kept. -/
def deadM : Prog C [] [.mem uarr] :=
  .cons (newXs "xs") (.cons (.assignMem (at_ .here 0) (.val (lit 1)))
    (.cons (.assignMem (at_ .here 0) (.val (lit 2))) .nil))

theorem dstore_mem_removed : Prog.dstore deadM =
    .cons (newXs "xs") (.cons (.assignMem (at_ .here 0) (.val (lit 2))) .nil) := rfl

def liveM : Prog C [] [.mem uarr] :=
  .cons (newXs "xs") (.cons (.assignMem (at_ .here 0) (.val (lit 1)))
    (.cons (.assignMem (at_ .here 1) (.val (lit 2))) .nil))

theorem dstore_mem_other_kept : Prog.dstore liveM = liveM := rfl

/-- The side conditions of `sstore_dead_runC` are satisfiable (a literal is pure). -/
theorem sstore_witness :
    Prog.runC (.cons (setTotal (lit 1)) (.cons (setTotal (lit 2)) .nil) : Prog C [] []) =
      Prog.runC (.cons (setTotal (lit 2)) .nil) :=
  sstore_dead_runC "total" rfl (.lit 1 (by decide)) (lit 2) rfl .nil

/-! ## Loop-invariant code motion -/

/-- Locals `[x, i]`: `x` innermost. -/
abbrev G : Ctx := [.val .uint, .val .uint]

def xv : Idx G (.val .uint) := .here
def iv : Idx G (.val .uint) := .there .here
def iRead : Val C G .uint := .simple (.local iv)
def lt3 : Val C G .bool := .binop .lt rfl rfl iRead (lit 3)
def incI : Stmt C G G := .assignLocal iv (add iRead (lit 1))

/-- `while (i < 3) { x = total + 1; i = i + 1; }`. -/
def invLoop : Stmt C G G := .loop .auto lt3 (.cons (.assignLocal xv (add total (lit 1))) (.cons incI .nil))

/-- It becomes `if (i < 3) { x = total + 1; while (i < 3) { i = i + 1; } }`. -/
theorem licm_hoisted : Stmt.licm invLoop =
    .ite lt3 (.cons (.assignLocal xv (add total (lit 1)))
      (.cons (.loop .auto lt3 (.cons incI .nil)) .nil)) .nil := rfl

/-- The side conditions are satisfiable: they hold of this loop. -/
theorem licm_witness : LicmOk lt3 xv (add total (lit 1)) (.cons incI .nil) :=
  licmB_ok (by decide)

theorem licm_same : Stmt.runC (Stmt.licm invLoop) = Stmt.runC invLoop := Stmt.licm_runC invLoop

def startG : State C G := (start.push (t := .val .uint) (uintOfNat 0)).push (t := .val .uint) (uintOfNat 0)

/-- The two locals after a run. -/
def xi (r : TRes (Out C startG.H G)) : Option (Int × Int) :=
  (r.map fun o => ((TEnv.get xv o.st.env : PrimTy.uint.Denote).1,
    (TEnv.get iv o.st.env : PrimTy.uint.Denote).1)).toOption

#guard xi (Stmt.runC invLoop startG) == some (1, 3)
#guard xi (Stmt.runC (Stmt.licm invLoop) startG) == some (1, 3)

/-! ### The zero-iteration guard

`while (i < 0) { x = total - 1; … }` never runs from `i = 0`, but `total - 1`
underflows (`total = 0`): the unguarded hoist `x = total - 1; while …` reverts
where the loop returns. The pass emits the guarded form, which returns. -/

def sub {Γ : Ctx} (a b : Val C Γ .uint) : Val C Γ .uint := .binop .sub rfl rfl a b
def lt0 : Val C G .bool := .binop .lt rfl rfl iRead (lit 0)
def failLoop : Stmt C G G :=
  .loop .auto lt0 (.cons (.assignLocal xv (sub total (lit 1))) (.cons incI .nil))

theorem licm_guarded : Stmt.licm failLoop =
    .ite lt0 (.cons (.assignLocal xv (sub total (lit 1)))
      (.cons (.loop .auto lt0 (.cons incI .nil)) .nil)) .nil := rfl

/-- The unguarded hoist (negative control). -/
def unguarded : Prog C G G :=
  .cons (.assignLocal xv (sub total (lit 1))) (.cons (.loop .auto lt0 (.cons incI .nil)) .nil)

#guard xi (Stmt.runC failLoop startG) == some (0, 0)
#guard xi (Stmt.runC (Stmt.licm failLoop) startG) == some (0, 0)
#guard (xi (Prog.runC unguarded startG)).isNone

/-! ### Rejected: not invariant -/

/-- `while (i < 3) { x = total; total = total + 1; i = i + 1; }`: the rest of the
body writes `total`, which `x = total` reads, so nothing is hoisted. -/
def writesRoot : Stmt C G G :=
  .loop .auto lt3 (.cons (.assignLocal xv total)
    (.cons (setTotal (add total (lit 1))) (.cons incI .nil)))

theorem licm_root_rejected : Stmt.licm writesRoot = writesRoot := rfl

/-- Negative control: the unchecked hoist leaves `x = 0` where the loop leaves
`x = 2` (the last iteration reads `total = 2`). -/
def wrongRoot : Stmt C G G :=
  .ite lt3 (.cons (.assignLocal xv total)
    (.cons (.loop .auto lt3 (.cons (setTotal (add total (lit 1))) (.cons incI .nil))) .nil)) .nil

#guard xi (Stmt.runC writesRoot startG) == some (2, 3)
#guard xi (Stmt.runC wrongRoot startG) == some (0, 3)

/-- `while (i < 3) { x = i * 2; i = i + 1; }`: `x = i * 2` reads `i`, which the
body writes; not hoisted. -/
def mul2 : Val C G .uint := .binop .mul rfl rfl iRead (lit 2)
def readsWritten : Stmt C G G := .loop .auto lt3 (.cons (.assignLocal xv mul2) (.cons incI .nil))

theorem licm_local_rejected : Stmt.licm readsWritten = readsWritten := rfl

/-! ## The certified pipeline -/

/-- `total = 3; total = 4; uint a = total;` becomes `total = 4; uint a = 4;` in one
round: the load is forwarded from the last store, and the first store is dead. -/
def e2e : Prog C [] [.val .uint] :=
  .cons (setTotal (lit 3)) (.cons (setTotal (lit 4)) (.cons (.declLocal .uint (.user "a") (some total)) .nil))

theorem e2e_optimized : Prog.optimize 1 e2e =
    .cons (setTotal (lit 4)) (.cons (.declLocal .uint (.user "a") (some (lit 4))) .nil) := rfl

theorem e2e_same : Prog.runC (Prog.optimize 1 e2e) = Prog.runC e2e := Prog.optimize_runC 1 e2e

/-- The loop of `invLoop` inside a program, hoisted by the pipeline. -/
theorem e2e_licm : Prog.optimize 1 (.cons invLoop .nil) =
    .cons (.ite lt3 (.cons (.assignLocal xv (add total (lit 1)))
      (.cons (.loop .auto lt3 (.cons incI .nil)) .nil)) .nil) .nil := rfl

#print axioms Prog.rle_empty_runC
#print axioms Prog.rle_runC
#print axioms rle_preserves
#print axioms Prog.dstore_runC
#print axioms sstore_dead_runC
#print axioms mstore_dead_runC
#print axioms dstore_preserves
#print axioms licm_runC
#print axioms Prog.licm_runC
#print axioms licm_preserves
#print axioms Prog.optimize_runC
#print axioms wrong_kill_differs
#print axioms licm_witness

end Solidity.Optimizer.X06Controls
