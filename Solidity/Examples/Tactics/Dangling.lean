import Solidity.Tools.ProofTree
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Counterexample

/-!
# Historical dangling-resurrection claims, refuted

These claims used to close when reference pushes exposed dirty slots unchanged.
The migrated push resets the slot before exposing it. Five original claims are
retained below and refuted at the initial typed state by kernel evaluation.
These are facts about this model; dangling storage aliases have undefined or
compiler-specific behavior in Solidity. The upstream cases belong to the open
suite, not to portable proof claims.

The longer rounds also retain the closer's resource-bound regressions.
-/

namespace Solidity.Examples.Tactics.Dangling


local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-- The old resurrection claim, retained as a migration counterexample. -/
def survivesPush : Fml StandardExample [] := dl!{ defined(wt(storage)) → [
    delete persons; persons.push(); Person storage r = persons[0]; persons.pop();
    r.age = 5; persons.push(); ] persons[0].age == 5 }

/-- Resetting the reused slot refutes resurrection already at the initial state. -/
theorem survivesPush_refuted : ¬ Valid survivesPush := by
  apply Fml.not_valid_of_eval3Peel (dom := Tools.poolDom []) [] (State.init StandardExample)
  decide +kernel

/-- The old diamond resurrection claim. -/
def survivesDiamond : Fml StandardExample [] := dl!{ defined(wt(storage)) → ⟨
    delete persons; persons.push(); Person storage r = persons[0]; persons.pop();
    r.age = 5; persons.push(); ⟩ persons[0].age == 5 }

/-- The resetting push refutes the historical claim at the initial state. -/
theorem survivesDiamond_refuted : ¬ Valid survivesDiamond := by
  apply Fml.not_valid_of_eval3Peel (dom := Tools.poolDom []) [] (State.init StandardExample)
  decide +kernel

/-- The old claim after deleting the emptied array. -/
def survivesDelete : Fml StandardExample [] := dl!{ defined(wt(storage)) → [
    delete persons; persons.push(); Person storage r = persons[0]; persons.pop();
    r.age = 5; delete persons; persons.push(); ] persons[0].age == 5 }

/-- The resetting push refutes the historical claim at the initial state. -/
theorem survivesDelete_refuted : ¬ Valid survivesDelete := by
  apply Fml.not_valid_of_eval3Peel (dom := Tools.poolDom []) [] (State.init StandardExample)
  decide +kernel

/-- The old claim after copying an empty array. -/
def survivesCopy : Fml StandardExample [] := dl!{ defined(wt(storage)) → [
    delete people; delete persons; persons.push(); Person storage r = persons[0];
    persons.pop(); r.age = 5; persons = people; persons.push(); ] persons[0].age == 5 }

/-- The resetting push refutes the historical claim at the initial state. -/
theorem survivesCopy_refuted : ¬ Valid survivesCopy := by
  apply Fml.not_valid_of_eval3Peel (dom := Tools.poolDom []) [] (State.init StandardExample)
  decide +kernel

/-- The old claim that a dirty inner array reappears after push. -/
def innerReappears : Fml StandardExample [] := dl!{ defined(wt(storage)) → [
    delete matrix; matrix.push(); uint[] storage ptr = matrix[0]; matrix.pop();
    ptr.push(66); matrix.push(); ] matrix[0].length == 1 && matrix[0][0] == 66 }

/-- The resetting push refutes the historical claim at the initial state. -/
theorem innerReappears_refuted : ¬ Valid innerReappears := by
  apply Fml.not_valid_of_eval3Peel (dom := Tools.poolDom []) [] (State.init StandardExample)
  decide +kernel

/-! ## Rounds of `pop`, write, `push()`

These variants retain search and storage-stack capacity regressions. The
two-round claim stays open; that search result alone is not a refutation.
Each additional round adds three storage updates. -/

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

#guard (Seq.residue .all .nil rounds2).map List.isEmpty == some false
#guard leafStats rounds4 == some [(true, 14, false)]
#guard leafStats rounds6 == some [(true, 20, false)]
#guard leafStats rounds7 == some [(true, 23, false)]

end Solidity.Examples.Tactics.Dangling
