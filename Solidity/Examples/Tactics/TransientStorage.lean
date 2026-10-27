import Solidity.Calculus.Transient
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close
import Solidity.Calculus.Sound

/-! Typed transient effects, ordinary source integration and calculus controls. -/

namespace Solidity.Examples.Tactics.TransientStorage

open scoped Scoped

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

/-- The declaration certificate rules out reference-valued transient roots. -/
theorem transient_root_primitive {C : Contract} {T : Ty}
    (root : Storage.RegionRoot C true T) : ∃ p, T = .prim p := by
  have member : root.name ∈ C.transientRoots := by
    simpa only [List.contains_iff_mem] using root.region
  have allowed := Semantics.all_mem C.transient_ok root.name member
  rw [root.declared] at allowed
  cases T with
  | prim p => exact ⟨p, rfl⟩
  | ref R => cases allowed

example {C : Contract} {R : RefTy} : ¬ Nonempty (Storage.RegionRoot C true (.ref R)) := by
  intro ⟨root⟩
  obtain ⟨p, impossible⟩ := transient_root_primitive root
  cases impossible

/-- error: a transient declaration cannot have an initializer -/
#guard_msgs in #check (contract!{ uint transient invalid = 1; } : Contract)

/-- Joint logical roots retain distinct persistent and transaction-local identities. -/
def Source : Contract := contract!{
  uint saved; uint transient scratch;
  function set(uint x) { scratch = x; }
  function fail() {
    try this.set(11) {} catch {}
    assert(scratch == 11);
    saved = 99;
    revert();
  }
}

/-- The existing scoped calculus proves transient operations in every typed
entry state; no transaction-initial-zero premise is smuggled into this proof. -/
theorem source_calculus : Fml.Valid dl[Source]{
    [ scratch = 7; saved = 3; delete scratch; ] (scratch == 0 ∧ saved == 3) } := by
  sol_prove

/-- Simultaneous source assignment captures both regions before either write. -/
theorem source_tuple_swap : Fml.Valid dl[Source]{
    [ scratch = 7; saved = 3; (scratch, saved) = (saved, scratch); ]
      (scratch == 3 ∧ saved == 7) } := by
  sol_prove

/-- The tuple capture law holds for arbitrary typed input values. -/
theorem source_tuple_generic : Fml.Valid dl[Source]{
    ∀ uint a; ∀ uint b;
    [ scratch = a; saved = b; (scratch, saved) = (saved, scratch); ]
      (scratch == b ∧ saved == a) } := by
  sol_prove

/-- The false sequential-assignment interpretation panics in the actual run. -/
example : (match (sol[Source]{
    scratch = 7; saved = 3; (scratch, saved) = (saved, scratch);
    assert(saved == 3);
  }).run (State.init Source) with | .error .panic => true | _ => false) = true := by
  decide +kernel

/-- Overlapping transient targets capture first and store right to left. -/
theorem source_tuple_overlap : Fml.Valid dl[Source]{
    [ saved = 3; scratch = 0; (scratch, scratch) = (saved, 7); ]
      (scratch == 3 ∧ saved == 3) } := by
  sol_prove

private def sourceEntry : State Source [] :=
  { State.init Source with tx := { selfAddress := ⟨1, rfl⟩ } }

/-- A concrete nonzero self call must succeed and adopt the transient write;
a semantics that rejects every call cannot satisfy this control. -/
def sourceShared : Prog Source [] [] := sol[Source]{
  scratch = 7;
  try this.set(9) { assert(scratch == 9); } catch { assert(false); }
}
theorem source_self_sharing : (sourceShared.run sourceEntry).isOk = true := by decide +kernel

/-- The successful nested call reaches the ancestor's explicit revert, rather
than a panic from losing its transient write. -/
example : (match (sol[Source]{ fail(); }).run sourceEntry with
    | .error .revert => true | _ => false) = true := by decide +kernel

/-- An ancestor failure rolls back both regions, including descendant writes. -/
theorem source_nested_rollback : ((sol[Source]{
    scratch = 7; saved = 3;
    try this.fail() {} catch {}
    assert(scratch == 7 && saved == 3);
  }).run sourceEntry).isOk = true := by decide +kernel

/-- Persistent and transient projections cannot alias, independently of layout. -/
def persistentRoot : Storage.RegionRoot Source false (.prim .uint) := ⟨"saved", rfl, rfl⟩
def transientRoot : Storage.RegionRoot Source true (.prim .uint) := ⟨"scratch", rfl, rfl⟩

example : persistentRoot.name ≠ transientRoot.name := persistentRoot.disjoint transientRoot

/-- Both classes written in one transaction, then only transient cells erased. -/
def sourceWritten : State Source [] :=
  (((sol[Source]{ saved = 3; scratch = 7; }).run (State.init Source)).toOption.map
    (fun o => o.st.glob)).getD (State.init Source)

example : (sourceWritten.transactionEntry.storage.get persistentRoot.declared) =
    .prim (⟨3, rfl⟩ : PrimTy.uint.Denote) := by decide +kernel
example : (sourceWritten.transactionEntry.storage.get transientRoot.declared) =
    .prim (PrimTy.dflt .uint) := by decide +kernel
example : (sourceWritten.storage.get transientRoot.declared) ≠
    sourceWritten.transactionEntry.storage.get transientRoot.declared := by decide +kernel

/-- Captures retain byte alignment and function signatures, rather than
coercing their existing tagged representations through an integer temporary. -/
def Encoded : Contract := contract!{
  bytes2 transient short; bytes2 savedBytes;
  function one() returns (uint) { return 1; }
  function two() returns (uint) { return 2; }
  function () returns (uint) transient fp;
  function () returns (uint) gp;
}
example : ((sol[Encoded]{ {
    short = hex"abcd"; savedBytes = hex"1234";
    (short, savedBytes) = (savedBytes, short);
    assert(short == hex"1234" && savedBytes == hex"abcd");
    fp = one; gp = two; (fp, gp) = (gp, fp);
    uint a = fp(); uint b = gp(); assert(a == 2 && b == 1);
  } }).run (State.init Encoded)).isOk = true := by decide +kernel

end Solidity.Examples.Tactics.TransientStorage

#print axioms Solidity.Transient.Program.static_preserves
#print axioms Solidity.Transient.Program.attempt_rollback
#print axioms Solidity.Transient.Program.transact_ordinary
#print axioms Solidity.Transient.holds_bind
#print axioms Solidity.Transient.ordinary_spec_box

#print axioms Solidity.Storage.resetTransient_get
#print axioms Solidity.Storage.resetTransient_find
#print axioms Solidity.Storage.resetTransient_idem
#print axioms Solidity.Storage.RegionRoot.disjoint
#print axioms Solidity.Examples.Tactics.TransientStorage.source_calculus

#print axioms Solidity.Examples.Tactics.TransientStorage.source_tuple_swap

#print axioms Solidity.Examples.Tactics.TransientStorage.source_self_sharing
#print axioms Solidity.Examples.Tactics.TransientStorage.source_nested_rollback

#print axioms Solidity.Examples.Tactics.TransientStorage.transient_root_primitive

#print axioms Solidity.Examples.Tactics.TransientStorage.source_tuple_generic
