import Solidity.Optimizer.Loads

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

end Solidity.Optimizer.X06Controls
