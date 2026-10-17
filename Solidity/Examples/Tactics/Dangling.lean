import Solidity.Tools.ProofTree
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Counterexample

/-!
# Dangling-resurrection claims

An empty `push()` saves only the length (solkey's `storagePushLengthSave`
since `d85018517f`), so a slot a popped alias wrote is exposed again as it
was: each claim below holds in every state, as solc's code behaves.
Dangling storage aliases are undefined or compiler-specific in Solidity;
these are facts about the model, solkey's `solc/StorageDangling.sol`.

The longer rounds also retain the closer's resource-bound regressions.
-/

namespace Solidity.Examples.Tactics.Dangling


local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-- A write through a popped alias survives the next push. -/
def survivesPush : Fml StandardExample [] := dl!{ defined(wt(storage)) → [
    delete persons; persons.push(); Person storage r = persons[0]; persons.pop();
    r.age = 5; persons.push(); ] persons[0].age == 5 }

/-- The push exposes the slot as the dangling alias left it. -/
theorem survivesPush_holds : Valid survivesPush := by
  unfold survivesPush
  sol_prove

/-- The old diamond resurrection claim. -/
def survivesDiamond : Fml StandardExample [] := dl!{ defined(wt(storage)) → ⟨
    delete persons; persons.push(); Person storage r = persons[0]; persons.pop();
    r.age = 5; persons.push(); ⟩ persons[0].age == 5 }

/-- The push exposes the slot as the dangling alias left it. -/
theorem survivesDiamond_holds : Valid survivesDiamond := by
  unfold survivesDiamond
  sol_prove

/-- The old claim after deleting the emptied array. -/
def survivesDelete : Fml StandardExample [] := dl!{ defined(wt(storage)) → [
    delete persons; persons.push(); Person storage r = persons[0]; persons.pop();
    r.age = 5; delete persons; persons.push(); ] persons[0].age == 5 }

/-- The push exposes the slot as the dangling alias left it. -/
theorem survivesDelete_holds : Valid survivesDelete := by
  unfold survivesDelete
  sol_prove

/-- The old claim after copying an empty array. -/
def survivesCopy : Fml StandardExample [] := dl!{ defined(wt(storage)) → [
    delete people; delete persons; persons.push(); Person storage r = persons[0];
    persons.pop(); r.age = 5; persons = people; persons.push(); ] persons[0].age == 5 }

/-- The push exposes the slot as the dangling alias left it. -/
theorem survivesCopy_holds : Valid survivesCopy := by
  unfold survivesCopy
  sol_prove

/-- The old claim that a dirty inner array reappears after push. -/
def innerReappears : Fml StandardExample [] := dl!{ defined(wt(storage)) → [
    delete matrix; matrix.push(); uint[] storage ptr = matrix[0]; matrix.pop();
    ptr.push(66); matrix.push(); ] matrix[0].length == 1 && matrix[0][0] == 66 }

/-- The push exposes the slot as the dangling alias left it. -/
theorem innerReappears_holds : Valid innerReappears := by
  unfold innerReappears
  sol_prove

/-! ## Rounds of `pop`, write, `push()`

These variants retain search and storage-stack capacity regressions. Each
round's write survives its push, so every claim holds; the two-round one
closes.  Each additional round adds three storage updates, past the
closer's bounds by four rounds (a `pop` leaves the history unknown,
`Op2.exposes`). -/

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
