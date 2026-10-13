import Solidity.Update
import Solidity.Semantics.Properties
import Solidity.Semantics.NoPanicOps

/-!
# The interpreter's writes, reshaped

What `sol_decide`'s untyped language and the closer still read of the
untyped interpreter's writes: a storage write as a new storage
(`State.writeStorage_eq`), a push whose element ignores the slot
(`pushAt_const`), a local's write leaving the state's other parts and a
memory location read and written (simp lemmas), and what a binding holds
(`Close.bindingVal`, …).  The rest went with the typed Theory (W10.3.0,
`docs/intrinsic.md`); these go with `sol_decide`'s untyped language (W10.4).
-/

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-! ### A local's write leaves the state's other parts -/

section
variable {σ : State} {x : Var} {b : Binding}

@[simp] theorem Semantics.State.findStorage_setEnv (r : Name) (segs : List Seg) :
    (σ.setEnv x b).findStorage r segs = σ.findStorage r segs := rfl
@[simp] theorem Semantics.State.checkIndex_setEnv (r : Name) (segs : List Seg) (i : Int) :
    (σ.setEnv x b).checkIndex r segs i = σ.checkIndex r segs i := rfl

@[simp] theorem Semantics.State.getObj_setEnv (id : Nat) : (σ.setEnv x b).getObj id = σ.getObj id := rfl
@[simp] theorem arrayLen_setEnv (r : Name) (segs : List Seg) :
    arrayLen (σ.setEnv x b) r segs = arrayLen σ r segs := rfl
@[simp] theorem memArrayLen_setEnv (id : Nat) : memArrayLen (σ.setEnv x b) id = memArrayLen σ id := rfl
end

/-! ### Writes as a new storage or heap, the rest of the state kept -/

/-- The storage a successful `writeStorage` leaves: a word saved, or a copy
over what is there. -/
def Semantics.State.writeRes (σ : State) (r : Name) (segs : List Seg) (x : SVal) :
    Res (List (Name × SVal)) :=
  match x with
  | .prim p => σ.storeRes r segs (.prim p)
  | .struct _ | .array .. | .map .. => do
    let cur ← σ.findStorage r segs
    σ.storeRes r segs (cur.overlay x)

@[simp] theorem Semantics.State.writeRes_toSVal (σ : State) (r segs) (v : Value) :
    σ.writeRes r segs v.toSVal = σ.storeRes r segs v.toSVal := by
  cases v <;> rfl

theorem Semantics.State.writeStorage_eq (σ : State) (r segs x) :
    σ.writeStorage r segs x = (do let s ← σ.writeRes r segs x; pure { σ with storage := s }) := by
  unfold State.writeStorage State.writeRes
  cases x <;> simp only [State.saveStorage_eq, bind_assoc]

/-! ### What a binding holds

The update and the statement read the same things through differently shaped
code; these name the reads, so both sides split on the same atoms. -/

namespace Close

/-- The value a local holds: `x` after `uint x = 10;` is `10`; an alias or
a memory local has none. -/
def bindingVal : Binding → Res Value
  | .val v => .ok v
  | .spath .. | .mref _ | .store _ | .ledger _ | .unset => .error .undef

/-- The path an alias holds: `p` after `Person storage p = alice;` is
`alice`. -/
def bindingPath : Binding → Res (Name × List Seg)
  | .spath r segs => .ok (r, segs)
  | .unset => .error .revert
  | .val _ | .mref _ | .store _ | .ledger _ => .error .undef

/-- The object a memory local holds: `m` after `Person memory m;`; an unset
one reverts, as `MPath.mvalT` does. -/
def bindingRef : Binding → Res Nat
  | .mref id => .ok id
  | .unset => .error .revert
  | .val _ | .spath .. | .store _ | .ledger _ => .error .undef

/-- The storage a storage variable holds: `old` after `{old := storage}`. -/
def bindingStore : Binding → Res (List (Name × SVal))
  | .store st => .ok st
  | .val _ | .spath .. | .mref _ | .ledger _ | .unset => .error .undef

/-- The ledger a ledger variable holds: `oldNet` after `{oldNet := net}`. -/
def bindingLedger : Binding → Res (List (Int × Int))
  | .ledger l => .ok l
  | .val _ | .spath .. | .mref _ | .store _ | .unset => .error .undef

end Close

/-! ### A memory location read and written -/

@[simp] theorem readLoc_eq (σ : State) (a : Addr) : readLoc σ a = (do (← readAddr σ a).asValue) := by
  cases a with
  | memoryField id f =>
    simp only [readLoc, readAddr, bind, Except.bind, pure, Except.pure]
    repeat' split
    all_goals simp_all
  | memoryIndex id i =>
    simp only [readLoc, readAddr, bind, Except.bind, pure, Except.pure]
    cases σ.getObj id with
    | error _ => rfl
    | ok o =>
      cases o with
      | struct _ => rfl
      | array elems => by_cases hh : 0 ≤ i ∧ i.toNat < elems.length <;> simp [hh]

@[simp] theorem Semantics.writeLoc_eq (σ : State) (a : Addr) (v : Value) :
    writeLoc σ a v = writeAddr σ v.toMVal a := by
  cases a <;> rfl

theorem pushAt_const (σ : State) (E E' : Ty) (r : Name) (segs : List Seg) (f : Res SVal) :
    pushAt σ E r segs (fun _ => f) = pushAt σ E' r segs (fun _ => f) := by
  unfold pushAt
  cases σ.findStorage r segs with
  | error _ => rfl
  | ok v =>
    cases v with
    | array elems shadow => cases shadow <;> rfl
    | _ => rfl

end Solidity
