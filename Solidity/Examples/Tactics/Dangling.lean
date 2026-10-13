import Solidity.Tools.ProofTree
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

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
rule, they fail.  They read scoped (`open scoped Solidity.Scoped`):
the `⊢` walk, its leaves closed by the scoped closer within its bounds
(`Seq.residue`, `Decide.closeSize`).
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

Each round adds a stale write and a pop below the slot reader, whose
guards repeat at every read: the leaf grows quadratically with the rounds
and the reduction by about 1.6 times a round.  Two rounds close; four
(twelve statements) make a leaf within `closeSize` whose reduction is past
`elimSize`, refused in milliseconds (`Seq.leafFitsOn`), as `pushes22` in
`Examples/ProofTree.lean`.  Six are the most whose leaf is within
`closeSize`, so the largest reduction `leafFitsOn` builds before refusing;
seven are refused by the leaf's size.  (A push asks no room of the
untyped storage the procedure reads: at a full array the typed one is out
of gas, `Upd.exh`; with a bound guard, W9.8.3d, five fitted.)
The leaves are the walk's (`Seq.residue`, the `⊢` walk `sol_prove` runs),
read as the scoped closer reads them (`Hyps.wrap`, `Fml.dropWtS`,
`Fml.toLS`). -/

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

/-- Six rounds: the most whose leaf is within `closeSize`. -/
def rounds6 : Fml StandardExample [] := dl!{ defined(wt(storage)) → [
    delete persons; persons.push(); Person storage r = persons[0];
    persons.pop(); r.age = 1; persons.push();
    persons.pop(); r.age = 2; persons.push();
    persons.pop(); r.age = 3; persons.push();
    persons.pop(); r.age = 4; persons.push();
    persons.pop(); r.age = 5; persons.push();
    persons.pop(); r.age = 6; persons.push(); ] persons[0].age == 6 }

/-- Seven rounds: refused by the leaf's size. -/
def rounds7 : Fml StandardExample [] := dl!{ defined(wt(storage)) → [
    delete persons; persons.push(); Person storage r = persons[0];
    persons.pop(); r.age = 1; persons.push();
    persons.pop(); r.age = 2; persons.push();
    persons.pop(); r.age = 3; persons.push();
    persons.pop(); r.age = 4; persons.push();
    persons.pop(); r.age = 5; persons.push();
    persons.pop(); r.age = 6; persons.push();
    persons.pop(); r.age = 7; persons.push(); ] persons[0].age == 7 }

#guard (Seq.residue .all .nil rounds2).map List.isEmpty == some true
#guard (Seq.residue .all .nil rounds4).map
  (fun ls => ls.map fun (l : Seq.SLeaf StandardExample) =>
    (((l.2.1.wrap l.2.2).dropWtS.toLS Decide.SymS.empty).fits Decide.closeSize).isSome &&
      !Seq.leafFitsOn (l.2.1.wrap l.2.2)) == some [true]

#guard (Seq.residue .all .nil rounds6).map
  (fun ls => ls.map fun (l : Seq.SLeaf StandardExample) =>
    (((l.2.1.wrap l.2.2).dropWtS.toLS Decide.SymS.empty).fits Decide.closeSize).isSome &&
      !Seq.leafFitsOn (l.2.1.wrap l.2.2)) == some [true]

#guard (Seq.residue .all .nil rounds7).map
  (fun ls => ls.map fun (l : Seq.SLeaf StandardExample) =>
    (((l.2.1.wrap l.2.2).dropWtS.toLS Decide.SymS.empty).fits Decide.closeSize).isSome) ==
  some [false]

end Solidity.Examples.Tactics.Dangling
