import Solidity.Calculus.Transient
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close
import Solidity.Calculus.Sound

/-! Composed interpreter regressions. Source transient declarations remain
refused; the ordinary fragments below use the existing Solidity elaborator. -/

namespace Solidity.Examples.Tactics.TransientStorage

open Transient

private instance {α : Type} [DecidableEq α] : DecidableEq (TRes α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)


def C : Contract := contract!{ uint saved; }
def layout : Layout := [("count", .uint), ("locked", .bool)]
def count : Slot layout .uint := .here
def locked : Slot layout .bool := .there .here
def seven : PrimTy.uint.Denote := ⟨7, rfl⟩
def nine : PrimTy.uint.Denote := ⟨9, rfl⟩
def eleven : PrimTy.uint.Denote := ⟨11, rfl⟩

def initial : FrameState C layout := ⟨State.init C, Store.empty layout⟩
def put3 : Prog C [] [] := sol[C]{ saved = 3; }
def put5 : Prog C [] [] := sol[C]{ saved = 5; }
def put9 : Prog C [] [] := sol[C]{ saved = 9; }
def ordinary (p : Prog C [] []) (h : Prog.within .nonpayable p = true) :
    Program C layout Unit := .ordinary .nonpayable p h

private def saved (s : State C []) : Int :=
  match s.storage.get (T := .prim .uint) (f := "saved") (by rfl) with
  | .prim n => n.1

private def observe {α : Type} (p : Program C layout α) : TRes (α × Int × Int) :=
  (Program.run p {} initial).map fun (v, s) => (v, (Store.get count s.cells).1, saved s.base)

/-- `count = 7; return this.readCount();` sees the caller's transient write. -/
def reenter : Program C layout Int := do
  Program.write count seven
  let n ← Program.selfCall .view false (Program.read count)
  pure n.1

theorem reentrant_visibility : observe reenter = .ok (7, 7, 0) := by decide +kernel +kernel
theorem false_reentrant_value : observe reenter ≠ .ok (0, 7, 0) := by decide +kernel +kernel

/-- A successful self-call keeps its transient update for its caller. -/
def setAndRead : Program C layout Int := do
  Program.write count seven
  Program.selfCall .nonpayable false (Program.write count nine)
  let n ← Program.read count
  pure n.1

theorem successful_preservation : observe setAndRead = .ok (9, 9, 0) := by decide +kernel +kernel

/-- A boolean transient cell neither aliases the integer cell nor the actual
ordinary persistent store. Both cells retain their declared value types. -/
def typedCells : Program C layout Bool := do
  Program.write count seven
  Program.write locked true
  ordinary put3 (by decide +kernel +kernel)
  Program.read locked

theorem separate_typed_cells : observe typedCells = .ok (true, 7, 3) := by decide +kernel +kernel

/-- A descendant updates both the actual ordinary store and transient cells. -/
def descendant : Program C layout Unit := do
  Program.write count eleven
  ordinary put9 (by decide +kernel +kernel)

def nested (fail : Bool) : Program C layout Unit := do
  Program.write count nine
  ordinary put5 (by decide +kernel +kernel)
  Program.selfCall .nonpayable false descendant
  if fail then Program.halt .revert else pure ()

/-- Catching the parent restores its entry snapshot, including the successful
descendant's persistent writes. Removing the failure commits those writes. -/
def caught (fail : Bool) : Program C layout Int := do
  Program.write count seven
  ordinary put3 (by decide +kernel +kernel)
  let _ ← Program.attempt (Program.selfCall .nonpayable false (nested fail))
  let n ← Program.read count
  pure n.1

theorem nested_rollback : observe (caught true) = .ok (7, 7, 3) := by decide +kernel +kernel
theorem nested_commit : observe (caught false) = .ok (11, 11, 9) := by decide +kernel +kernel
theorem false_partial_rollback : observe (caught true) ≠ .ok (11, 11, 9) := by decide +kernel +kernel

/-- The first transaction writes both stores; only persistent `saved` survives
when the second transaction reads `count`. -/
def firstTransaction : Program C layout Int := do
  Program.write count seven
  ordinary put3 (by decide +kernel +kernel)
  let n ← Program.read count
  pure n.1

def successive : TRes (Int × Int × Int) := do
  let (first, world) ← Program.transact firstTransaction (Lifetime.World.ofState initial.base) {}
  let (second, final) ← Program.transact (Program.read count) world {}
  pure (first, second.1, saved final.observe)

theorem transaction_reset : successive = .ok (7, 0, 3) := by decide +kernel +kernel
theorem false_persistent_transient : successive ≠ .ok (7, 7, 3) := by decide +kernel +kernel

/-- A static call may read; a direct or descendant transient write fails. -/
theorem static_read : observe (Program.selfCall .view true (Program.read count)) =
    .ok (PrimTy.dflt .uint, 0, 0) := by decide +kernel +kernel
theorem static_write : Program.run (Program.write count nine) { static := true } initial =
    .error .revert := rfl
theorem inherited_static_write : observe (Program.selfCall .nonpayable true
    (Program.selfCall .nonpayable false (Program.write count nine))) = .error .revert := by
  decide +kernel
theorem static_ordinary_write : observe (Program.selfCall .nonpayable true
    (ordinary put3 (by decide +kernel +kernel))) = .error .revert := by decide +kernel +kernel
theorem view_write : Program.run (Program.write count nine) { mutability := .view } initial =
    .error .revert := rfl
theorem pure_read : Program.run (Program.read count) { mutability := .pure } initial =
    .error .revert := rfl
theorem view_mutable_call : Program.run
    (Program.selfCall .nonpayable false (Program.pure (C := C) (L := layout) ()))
    { mutability := .view } initial = .error .revert := rfl

/-- Divergence and resource exhaustion do not become successful catch results. -/
theorem divergence_not_caught : observe (Program.attempt
    (Program.halt (α := Unit) .diverge)) = .error .diverge := by decide +kernel +kernel
theorem exhaustion_not_caught : observe (Program.attempt
    (Program.halt (α := Unit) .exhausted)) = .error .exhausted := by decide +kernel +kernel
theorem exhaustion_not_committed : Program.transact
    (Program.halt (C := C) (L := layout) (α := Unit) .exhausted)
    (Lifetime.World.ofState initial.base) {} = .error .exhausted := rfl

/-- An ordinary correctness theorem is reused inside the composed semantics. -/
theorem put3_valid : Spec.Valid (.box put3 .tt) := by
  apply Proves.valid (R := .all)
  sol_prove

theorem ordinary_calculus_bridge : Holds .box (ordinary put3 (by decide +kernel +kernel))
    (fun _ s => Spec.sat s.base .tt) {} initial :=
  ordinary_spec_box put3 (by decide +kernel +kernel) .tt initial (put3_valid initial.base)

/-- A generic write/read proof uses the typed store law in every entry state. -/
theorem write_read (i : Slot layout p) (v : p.Denote) (s : FrameState C layout) :
    Holds .diamond (do Program.write i v; Program.read i) (fun read _ => read = v) {} s := by
  exact ⟨Store.get_set i v s.cells, by intro panic; cases panic⟩

/-- A panic still invalidates the box; the bridge is not success-only. -/
theorem panic_not_valid : ¬ Holds .box (Program.halt (C := C) (L := layout)
    (α := Unit) .panic) (fun _ _ => True) {} initial :=
  fun h => h.2 rfl

end Solidity.Examples.Tactics.TransientStorage

#print axioms Solidity.Transient.Program.static_preserves
#print axioms Solidity.Transient.Program.attempt_rollback
#print axioms Solidity.Transient.Program.transact_ordinary
#print axioms Solidity.Transient.holds_bind
#print axioms Solidity.Transient.ordinary_spec_box
