import Solidity.Tools.ProofTree
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Dangling aliases, pinned

An alias bound through an index (`Person storage r = persons[0];`) names a
slot, not a live element: KeY's `consr(sp, at(ie))`, checked only when
`storageIndexReadArrayBindLocalRoot` bound it.  After a `pop` the slot is
past the array's end, and a write through the alias lands there (a save
at the dangling location, `SLoc.dangling`, `Theory/Typed/Obs.lean`); a
later `push()` makes the slot live again, as it is (`TVal.extendA`),
directly, after a `delete` of the emptied array, or after a copy over it.
A push through an alias of an inner array lands in the recycled array,
whose length is read off the slot.  The clauses are solkey's storage taclets;
`docs/lean-key-rule-map.md` names each with the lemmas that transcribe it.

These are solkey `TestSuite`'s dangling-alias functions over
`StandardExample` (`persons`, `people`, `matrix`), each a `sol_prove?` that suggests
`sol_prove`.  If a clause stops applying, or the strategy picks another
rule, they fail.  They read scoped (`open scoped Solidity.Scoped`):
the `⊢` walk, its leaves closed by the scoped closer within its bounds
(`Seq.residue`, `Seq.closeSize`).
-/

namespace Solidity.Examples.Tactics.Dangling


local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## A write past the end, made live by a `push()`

`storagePushLengthSaveReferenceElement` then `selectOnSaveCons`: the slot
the `push()` takes is the one the alias wrote. -/

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ dl!{ defined(wt(storage)) → [
    delete persons; persons.push(); Person storage r = persons[0]; persons.pop();
    r.age = 5; persons.push(); ] persons[0].age == 5 } := by
  sol_prove?

/-- The diamond: the write through the alias returns, since the slot past
the end is there (`staleOk`, `slotHasU`). -/
example : ⊢ dl!{ defined(wt(storage)) → ⟨
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
example : ⊢ dl!{ defined(wt(storage)) → [
    delete persons; persons.push(); Person storage r = persons[0]; persons.pop();
    r.age = 5; delete persons; persons.push(); ] persons[0].age == 5 } := by
  sol_prove?

/--
info: Try this:
  sol_prove
-/
#guard_msgs in
example : ⊢ dl!{ defined(wt(storage)) → [
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
example : ⊢ dl!{ defined(wt(storage)) → [
    delete matrix; matrix.push(); uint[] storage ptr = matrix[0]; matrix.pop();
    ptr.push(66); matrix.push(); ] matrix[0].length == 1 && matrix[0][0] == 66 } := by
  sol_prove?

/-! ## Rounds of `pop`, write, `push()`

Each round adds a stale write and a pop below the slot reader, and three
storage updates (a pop, a write, a push) to the stack a read is taken
through.  Two rounds close;
four (twelve statements) stack fourteen updates, past `stackSize`, and are
refused in milliseconds (`Seq.leafFitsOn`), as `pushes22` in
`Examples/ProofTree.lean`; six and seven too, each leaf within
`closeSize`.  (Under the box, as here, a push asks no room: at a full array
the typed one is out of gas, which the box accepts.)  The leaves are the
walk's (`Seq.residue`, the `⊢` walk `sol_prove` runs), read as the closer
reads them (`Hyps.wrap`, `Fml.toLS`). -/

/-- Two rounds through one alias. -/
def rounds2 : Fml StandardExample [] := dl!{ defined(wt(storage)) → [
    delete persons; persons.push(); Person storage r = persons[0];
    persons.pop(); r.age = 1; persons.push();
    persons.pop(); r.age = 2; persons.push(); ] persons[0].age == 2 }

/-- Four rounds through one alias: twelve statements after the binding. -/
def rounds4 : Fml StandardExample [] := dl!{ defined(wt(storage)) → [
    delete persons; persons.push(); Person storage r = persons[0];
    persons.pop(); r.age = 1; persons.push();
    persons.pop(); r.age = 2; persons.push();
    persons.pop(); r.age = 3; persons.push();
    persons.pop(); r.age = 4; persons.push(); ] persons[0].age == 4 }

/-- Six rounds. -/
def rounds6 : Fml StandardExample [] := dl!{ defined(wt(storage)) → [
    delete persons; persons.push(); Person storage r = persons[0];
    persons.pop(); r.age = 1; persons.push();
    persons.pop(); r.age = 2; persons.push();
    persons.pop(); r.age = 3; persons.push();
    persons.pop(); r.age = 4; persons.push();
    persons.pop(); r.age = 5; persons.push();
    persons.pop(); r.age = 6; persons.push(); ] persons[0].age == 6 }

/-- Seven rounds. -/
def rounds7 : Fml StandardExample [] := dl!{ defined(wt(storage)) → [
    delete persons; persons.push(); Person storage r = persons[0];
    persons.pop(); r.age = 1; persons.push();
    persons.pop(); r.age = 2; persons.push();
    persons.pop(); r.age = 3; persons.push();
    persons.pop(); r.age = 4; persons.push();
    persons.pop(); r.age = 5; persons.push();
    persons.pop(); r.age = 6; persons.push();
    persons.pop(); r.age = 7; persons.push(); ] persons[0].age == 7 }

/-- The walk's leaves of `φ`, each read as the closer reads it: within
`closeSize`, its storage stack, and whether `leafFitsOn` takes it. -/
def leafStats (φ : Fml StandardExample []) : Option (List (Bool × Nat × Bool)) :=
  (Seq.residue .all .nil φ).map fun ls => ls.map fun (l : Seq.SLeaf StandardExample) =>
    match (l.2.1.wrap l.2.2).toLS true Decide.SymS.init with
    | some x => ((x.fits Seq.closeSize).isSome, x.stDepth, Seq.leafFitsOn (l.2.1.wrap l.2.2))
    | none => (false, 0, false)

#guard (Seq.residue .all .nil rounds2).map List.isEmpty == some true
#guard leafStats rounds4 == some [(true, 14, false)]
#guard leafStats rounds6 == some [(true, 20, false)]
#guard leafStats rounds7 == some [(true, 23, false)]

end Solidity.Examples.Tactics.Dangling
