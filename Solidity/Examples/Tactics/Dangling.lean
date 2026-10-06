import Solidity.Tools.ProofTree
import Solidity.Calculus.Derive

/-!
# Dangling aliases, pinned

An alias bound through an index (`Person storage r = persons[0];`) names a
slot, not a live element: KeY's `consr(sp, at(ie))`, checked only when
`storageIndexReadArrayBindLocalRoot` bound it.  After a `pop` the slot is
past the array's end, and a write through the alias lands there
(`LStor.stale`, `Calculus/Decide.lean`); a later `push()` makes the slot
live again, directly, after a `delete` of the emptied array, or after a
copy over it (`LStor.slotU`).  A push through an alias of an inner array
lands in the recycled array, whose length the slot readers count
(`LStor.slotLenU`).  The clauses are solkey's storage taclets;
`docs/lean-key-rule-map.md` names each with the lemmas that transcribe it.

These are solkey `TestSuite`'s dangling-alias functions over
`StandardExample` (`persons`, `people`, `matrix`), each a `sol_prove?` that suggests
`sol_prove`.  If a clause stops applying, or the strategy picks another
rule, they fail.
-/

namespace Solidity.Examples.Tactics.Dangling

open Proves

local instance : InContract := ⟨StandardExample⟩

/-- `wt(storage)`, the premise every TestSuite obligation carries. -/
def wtStd : Fml StandardExample := .defined (.wt StandardExample.vars .storage)

/-! ## A write past the end, made live by a `push()`

`storagePushLengthSaveReferenceElement` then `selectOnSaveCons`: the slot
the `push()` takes is the one the alias wrote. -/

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ .imp wtStd dl!{ [
    delete persons; persons.push(); Person storage r = persons[0]; persons.pop();
    r.age = 5; persons.push(); ] persons[0].age == 5 } := by
  sol_prove?

/-- The diamond: the write through the alias returns, since the slot past
the end is there (`staleOk`, `slotHasU`). -/
example : ⊢ .imp wtStd dl!{ ⟨
    delete persons; persons.push(); Person storage r = persons[0]; persons.pop();
    r.age = 5; persons.push(); ⟩ persons[0].age == 5 } := by
  sol_prove

/-! ## Past a `delete` and a copy

A `delete` of an empty dynamic array keeps its slots past the end
(`selectStDelNodeIndexStruct`, `iv ≥ size`); a copy of an empty array over
it keeps them at its length (`selectOnSaveEmptyIndexStruct`). -/

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ .imp wtStd dl!{ [
    delete persons; persons.push(); Person storage r = persons[0]; persons.pop();
    r.age = 5; delete persons; persons.push(); ] persons[0].age == 5 } := by
  sol_prove?

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ .imp wtStd dl!{ [
    delete people; delete persons; persons.push(); Person storage r = persons[0];
    persons.pop(); r.age = 5; persons = people; persons.push(); ]
    persons[0].age == 5 } := by
  sol_prove?

/-! ## A push through the alias

`storagePushValueSave` at the slot: the inner array the outer `push()`
recycles has the pushed word, and its length is one
(`findDefinitionSize`, then `selectOnSaveCons` on `size`). -/

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ .imp wtStd dl!{ [
    delete matrix; matrix.push(); uint[] storage ptr = matrix[0]; matrix.pop();
    ptr.push(66); matrix.push(); ] matrix[0].length == 1 && matrix[0][0] == 66 } := by
  sol_prove?

/-! ## Rounds of `pop`, write, `push()`

Each round adds a stale write and a pop below the slot reader, so the
reduction grows with the rounds.  Two rounds close; four (twelve
statements) make a leaf within `closeSize` whose reduction is past
`elimSize`, refused in milliseconds (`Derive.leafFits`), as `pushes22`
in `Examples/ProofTree.lean`. -/

/-- Two rounds through one alias. -/
def rounds2 : Fml StandardExample := .imp wtStd dl!{ [
    delete persons; persons.push(); Person storage r = persons[0];
    persons.pop(); r.age = 1; persons.push();
    persons.pop(); r.age = 2; persons.push(); ] persons[0].age == 2 }

/-- Four rounds through one alias: twelve statements after the binding. -/
def rounds4 : Fml StandardExample := .imp wtStd dl!{ [
    delete persons; persons.push(); Person storage r = persons[0];
    persons.pop(); r.age = 1; persons.push();
    persons.pop(); r.age = 2; persons.push();
    persons.pop(); r.age = 3; persons.push();
    persons.pop(); r.age = 4; persons.push(); ] persons[0].age == 4 }

#guard Derive.proves [] rounds2
#guard (Derive.residue Derive.budget Derive.synClose Derive.budget [] rounds4).map
  (fun (ls, _) => ls.map fun (l : List (Hyp StandardExample) × Fml StandardExample) =>
    (((Hyp.wrap (Derive.dropWt l.1) l.2).seqUpd.toL Decide.Sym.empty).fits
      Derive.closeSize).isSome && !Derive.leafFits l.1 l.2) == some [true]

end Solidity.Examples.Tactics.Dangling
