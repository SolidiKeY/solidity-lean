import Solidity.Theory.Mutability.Pure
import Solidity.Theory.Mutability.Payable
import Solidity.Theory.Mutability.Assignable
import Solidity.Theory.Mutability.Closer
import Solidity.Calculus.Surface

/-! Witnesses and negative controls for the mutability metatheorems (S3.1,
`Theory/Mutability/`): each theorem applied to a concrete program whose
premise is decided, and a program outside the premise whose run breaks the
conclusion, so the premise is needed. -/

namespace Solidity.Examples.Tactics.Mutability

open Solidity.Theory.Mutability

/-- `uint saved; function get() view returns (bool) { … }` and friends. -/
def C : Contract := contract!{ uint saved; }

/-- A `view` body: reads `saved`. -/
def peek : Prog C [] [] := sol[C]{ require(saved == 0); }
/-- A `pure` body: arithmetic on its own locals. -/
def arith : Prog C [] [.val .uint] := sol[C]{ uint y = 2; y = y * 3; assert(y == 6); }
/-- A `nonpayable` body: writes `saved`. -/
def put5 : Prog C [] [] := sol[C]{ saved = 5; }

/-- `require(saved == 0);` is `view`. -/
theorem peek_view : Prog.within .view peek = true := by decide +kernel
/-- `uint y = 2; y = y * 3; assert(y == 6);` is `pure`. -/
theorem arith_pure : Prog.within .pure arith = true := by decide +kernel

/-- Negative controls of the classifier: a write is not `view`, a storage read
is not `pure`. -/
theorem put5_not_view : Prog.within .view put5 = false := by decide +kernel
/-- `require(saved == 0);` reads storage: not `pure`. -/
theorem peek_not_pure : Prog.within .pure peek = false := by decide +kernel

/-- The storage after `saved = 5;`. -/
def stored5 : Storage C :=
  ((put5.run (State.init C)).toOption.map (·.st.storage)).getD (Storage.init C)

/-- An outside with `saved == 5` and a paid transaction. -/
def outside5 : Outside C :=
  ⟨stored5, [], ⟨7, rfl⟩, { msgValue := ⟨3, rfl⟩, msgSender := ⟨9, rfl⟩ }⟩

private def isOkB {α : Type} : TRes α → Bool
  | .ok _ => true
  | .error _ => false

/-! ## View: witness and control -/

/-- **Witness**: `peek` commits its entry's globals, from the initial state
and from the one with `saved == 5` (where it reverts). -/
theorem peek_commits (σ : State C []) : committed σ (Prog.run σ peek) = globals σ :=
  Prog.committed_view peek peek_view σ

/-- The premise is inhabited by a successful run: `peek` returns from the
initial state. -/
example : isOkB (Prog.run (State.init C) peek) = true := by decide +kernel

/-- **Negative control**: `saved = 5;` (not `view`) does change the committed
storage. -/
theorem put5_changes : (committed (State.init C) (Prog.run (State.init C) put5)).storage ≠
    (globals (State.init C)).storage := by
  intro h
  have h' : stored5 = Storage.init C := h
  revert h'
  decide +kernel

/-! ## Pure: witness and control -/

/-- **Witness**: `arith` runs alike from the initial outside and from
`outside5` (theorem), and it does return (a successful run, so the premise
and the conclusion are about an actual result). -/
theorem arith_same : Prog.run (withOutside (State.init C) outside5) arith =
    (Prog.run (State.init C) arith).map (Out.withOutside outside5) :=
  Prog.run_withOutside arith arith_pure (State.init C) outside5

example : isOkB (Prog.run (State.init C) arith) = true := by decide +kernel

/-- **Negative control**: `peek` is `view` but not `pure`, and its outcome
does depend on the outside: it returns from the initial state and reverts
where `saved == 5`. -/
theorem peek_depends : isOkB (Prog.run (State.init C) peek) = true ∧
    isOkB (Prog.run (withOutside (State.init C) outside5) peek) = false := by
  decide +kernel

/-! ## Payable: witness and control -/

/-- One entry, `put5`, payable or not. -/
def entry (payable : Bool) : Lifetime.System C Unit Unit :=
  { deploy := fun _ => .nil, call := fun _ => put5, payable := fun _ => payable }

/-- A transaction paying 1 wei to address 1. -/
def paid : TTx := { msgValue := ⟨1, rfl⟩, selfAddress := ⟨1, rfl⟩ }

/-- **Witness**: the non-payable entry, called with value, reverts. -/
theorem nonpayable_reverts :
    (entry false).run (Lifetime.World.ofState (State.init C)) () paid = .error .revert :=
  System.run_nonpayable _ _ () paid rfl (by decide)

/-- **Negative control**: the same call to a payable entry commits. -/
example : isOkB ((entry true).run (Lifetime.World.ofState (State.init C)) () paid) = true := by
  decide +kernel

/-- **Negative control**: without value the non-payable entry commits. -/
example : isOkB ((entry false).run (Lifetime.World.ofState (State.init C)) ()
    { selfAddress := ⟨1, rfl⟩ }) = true := by
  decide +kernel

/-! ## Transient-layer payable: witness and control -/

/-- **Witness**: a non-payable transient-layer transaction with value
reverts, whatever its effects. -/
theorem transact_reverts :
    Transient.Program.transact (L := []) (Transient.Program.pure (C := C) ())
      (Lifetime.World.ofState (State.init C)) paid false {} = .error .revert :=
  transact_nonpayable _ _ paid {} (by decide)

/-- **Negative control**: the payable transaction commits. -/
example : isOkB (Transient.Program.transact (L := []) (Transient.Program.pure (C := C) ())
    (Lifetime.World.ofState (State.init C)) paid true {}) = true := by decide +kernel

/-! ## Pure on the transient layer: witness and control -/

/-- `uint transient count;` -/
abbrev tl : Transient.Layout := [("count", .uint)]
/-- The transient cell `count`. -/
def countSlot : Transient.Slot tl .uint := .here
/-- A transient store with `count == 4`. -/
def four : Transient.Store tl := (⟨4, rfl⟩, ())
/-- The entry state: initial storage, `count` at its default. -/
def entry0 : Transient.FrameState C tl := ⟨State.init C, Transient.Store.empty tl⟩
/-- `assert(1 == 1);`, an ordinary `pure` fragment. -/
def trivialPure : Prog C [] [] := sol[C]{ assert(1 == 1); }

/-- **Witness**: a pure effect tree runs alike from every outside and
transient store (`Transient.Program.pure_independent`); it returns. -/
theorem pure_tree_same :
    (Transient.Program.run (Transient.Program.ordinary .pure trivialPure (by decide +kernel))
      { mutability := .pure } (Transient.withOutsideCells entry0 outside5 four)).map Prod.fst =
    (Transient.Program.run (Transient.Program.ordinary .pure trivialPure (by decide +kernel))
      { mutability := .pure } entry0).map Prod.fst :=
  Transient.Program.pure_independent _ rfl entry0 outside5 (outside entry0.base) four _

example : isOkB (Transient.Program.run
    (Transient.Program.ordinary .pure trivialPure (by decide +kernel)) { mutability := .pure }
    entry0) = true := by decide +kernel

/-- **Negative control**: in a `view` context a read of `count` depends on
the transient store: `0` at entry, `4` after replacing the cells. -/
theorem view_read_depends :
    (Transient.Program.run (Transient.Program.read countSlot) { mutability := .view }
      entry0).map (fun r => r.1.1) = .ok 0 ∧
    (Transient.Program.run (Transient.Program.read countSlot) { mutability := .view }
      (Transient.withOutsideCells entry0 (outside entry0.base) four)).map (fun r => r.1.1) =
      .ok 4 := ⟨rfl, rfl⟩

/-! ## Assignable (S3.2): witness and control -/

/-- `uint a; uint b;` -/
def D : Contract := contract!{ uint a; uint b; }

/-- `a = 1;` writes the root `a` only. -/
def setA : Prog D [] [] := sol[D]{ a = 1; }

/-- **Witness**: `a = 1;` under `assignable a;` passes the check. -/
theorem setA_check : assignableCheck setA [.root "a"] = true := by decide +kernel

/-- **Negative control**: under `assignable b;` it does not. -/
theorem setA_check_b : assignableCheck setA [.root "b"] = false := by decide +kernel

/-- The reference to `b`, and to `a`. -/
def refB : SRef D (.prim .uint) := SRef.ofRoot "b" rfl
def refA : SRef D (.prim .uint) := SRef.ofRoot "a" rfl

/-- The run of `a = 1;` from the initial state, as an `Out` (it returns). -/
theorem setA_ok : isOkB (Prog.run (State.init D) setA) = true := by decide +kernel

/-- **Witness**: every run of `a = 1;` keeps `b` (theorem, any state). -/
theorem setA_keeps_b (σ : State D []) {o : Out D σ.H []} (h : Prog.run σ setA = .ok o) :
    o.st.storage.find refB = σ.storage.find refB :=
  (assignableCheck_sound setA_check h).find refB (by decide)

/-- **Negative control**: the root the clause names does change, so the frame
is not vacuous: after `a = 1;` from the initial state `a` reads `1`, not `0`. -/
theorem setA_changes_a :
    ((Prog.run (State.init D) setA).toOption.map (·.st.storage.find refA)) ≠
      some ((State.init D).storage.find refA) := by
  decide +kernel

end Solidity.Examples.Tactics.Mutability

/-- info: 'Solidity.Theory.Mutability.Prog.committed_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Prog.committed_view
/-- info: 'Solidity.Theory.Mutability.Prog.committed_readOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Prog.committed_readOnly
/-- info: 'Solidity.Theory.Mutability.ExecP.committed_readOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.ExecP.committed_readOnly
/--
info: 'Solidity.Theory.Mutability.Transient.Program.readOnly_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Transient.Program.readOnly_preserves
/-- info: 'Solidity.Theory.Mutability.Prog.run_withOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Prog.run_withOutside
/-- info: 'Solidity.Theory.Mutability.Prog.pure_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Prog.pure_independent
/-- info: 'Solidity.Theory.Mutability.Prog.pure_halt_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Prog.pure_halt_independent
/-- info: 'Solidity.Theory.Mutability.Prog.pure_local_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Prog.pure_local_independent
/-- info: 'Solidity.Theory.Mutability.Prog.pure_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Prog.pure_outside
/-- info: 'Solidity.Theory.Mutability.System.run_nonpayable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.System.run_nonpayable
/-- info: 'Solidity.Theory.Mutability.deployT_nonpayable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.deployT_nonpayable
/-- info: 'Solidity.Theory.Mutability.transact_nonpayable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.transact_nonpayable
/-- info: 'Solidity.Theory.Mutability.ContractWorld.World.enter_nonpayable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.ContractWorld.World.enter_nonpayable
/--
info: 'Solidity.Theory.Mutability.ContractWorld.World.callFrame_nonpayable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Solidity.Theory.Mutability.ContractWorld.World.callFrame_nonpayable
/-- info: 'Solidity.Theory.Mutability.Prog.frames_readOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Prog.frames_readOnly
/-- info: 'Solidity.Theory.Mutability.Prog.frames_of_storeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Prog.frames_of_storeAt
/-- info: 'Solidity.Theory.Mutability.assignableCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.assignableCheck_sound
/-- info: 'Solidity.Theory.Mutability.committed_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.committed_frames
/-- info: 'Solidity.Theory.Mutability.holds_modal_readOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.holds_modal_readOnly
/-- info: 'Solidity.Theory.Mutability.Spec.box_readOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Spec.box_readOnly
/-- info: 'Solidity.Theory.Mutability.Transient.holds_readOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Transient.holds_readOnly
/-- info: 'Solidity.Theory.Mutability.Transient.holds_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Transient.holds_frame
/--
info: 'Solidity.Theory.Mutability.Transient.Program.static_preserves_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Transient.Program.static_preserves_all
/--
info: 'Solidity.Theory.Mutability.Transient.Program.ordinary_static' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Transient.Program.ordinary_static
/-- info: 'Solidity.Theory.Mutability.ContractWorld.World.enter_static' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.Mutability.ContractWorld.World.enter_static
/--
info: 'Solidity.Theory.Mutability.Transient.Program.run_withOutsideCells' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Transient.Program.run_withOutsideCells
/--
info: 'Solidity.Theory.Mutability.Transient.Program.pure_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Solidity.Theory.Mutability.Transient.Program.pure_independent
