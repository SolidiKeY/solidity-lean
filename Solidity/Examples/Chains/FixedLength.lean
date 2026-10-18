import Solidity.Calculus.RewriteChains
import Solidity.Calculus.RewriteChainGen
import Solidity.Calculus.Close
import Solidity.FreshNames
import Solidity.Calculus.LastLine
import Solidity.Calculus.Surface

/-!
# The fixed-length array examples as chains

The calculus's examples of a fixed-length array's length, each one chain term over the contract of the
section (`d1 : uint[9]`, `d2 : uint[]`, `dyn : uint[3][]`) and its concrete postcondition, so that the
reads resolve and the last line is `true`.  A copy of `d1` into `d2` is a save of `d1` viewed at the
dynamic shape (`fixedCopy(uint[], find(storage, d1))`, KeY's `find<[Struct]>(storage, d1)`); the length
read where it was saved is `d1`'s, by its type (`lenOnSaveFixedCopy`, KeY's `selectOnSaveEmptySize` with
the destination not `fixed`), where KeY reads `wf(F₉, …)` from Γ.  A fixed array's own length is a literal
already in the program (`d1.length` elaborates to `9`).  Past the program a write at a root or a member
of one cannot halt (`Tm.totalW`), so the update is applied to the closed postcondition under the diamond
(`applyOnRigid`).  The push example ends where the update binds the alias `sp` through an index, whose
bound it checks and so may halt: KeY reads `0 ≤ ℓ` and `wf(F₃, …)` from Γ there.  Unlike the other files, the
postcondition is the section's concrete one, not `φ : Post`, so the last line is a closed formula, not one
parallel update.
-/

namespace Solidity.Examples.Chains.FixedLength

open scoped Scoped

/-- `uint[9] d1; uint[] d2; uint[3][] dyn;` -/
def FixedLength : Contract := contract!{ uint[9] d1; uint[] d2; uint[3][] dyn; }

local instance : InContract := ⟨FixedLength⟩

/-! ## A fixed array copied to a dynamic one -/

namespace CopyLength
/-- `d2 = d1; x = d2.length;`, then `x = 9`: the copy is saved, its length read back through the save. -/
theorem chain :
    cdl!{ ∀ uint x; ⟨ d2 = d1; x = d2.length; ⟩ x = 9 }
    ~[storageFixedCopySave]~> cdl!{ ∀ uint x; { storage := save(storage, d2, fixedCopy(uint[], find(storage, d1))) } ⟨ x = d2.length; ⟩ x = 9 }
    ~[storageLengthRead]~> cdl!{ ∀ uint x; { storage := save(storage, d2, fixedCopy(uint[], find(storage, d1))) } { x := d2.length } x = 9 }
    ~[sequentialToParallel]~> cdl!{
        ∀ uint x;
          { storage := save(storage, d2, fixedCopy(uint[], find(storage, d1))) ‖
              x := find(save(storage, d2, fixedCopy(uint[], find(storage, d1))), d2.length) }
            x = 9 }
    ~[concrete]~> cdl!{
        ∀ uint x;
          { storage := save(storage, d2, fixedCopy(uint[], find(storage, d1))) ‖
              x := find(save(storage, d2, fixedCopy(uint[], find(storage, d1))), d2.length) }
            (defined(x) ∧ x ≐ 9) }
    ~[lenOnSaveFixedCopy]~> cdl!{ ∀ uint x; { storage := save(storage, d2, fixedCopy(uint[], find(storage, d1))) ‖ x := 9 } (defined(x) ∧ x ≐ 9) }
    ~[applyOnRigid]~> cdl!{ ∀ uint x; defined(9) ∧ 9 ≐ 9 }
    ~[concrete]~> cdl!{ ∀ uint x; true } := by
  sol_chain
#last_line chain
end CopyLength

/-! ## A fixed array deleted -/

namespace DeleteLength
/-- `delete d1; x = d1.length;`, then `x = 9`: the delete resets the elements, the length is the type's. -/
theorem chain :
    cdl!{ ∀ uint x; ⟨ delete d1; x = d1.length; ⟩ x = 9 }
    ~[storageRootDelete]~> cdl!{ ∀ uint x; { storage := delAt(storage, d1) } ⟨ x = 9; ⟩ x = 9 }
    ~[localValueAssign]~> cdl!{ ∀ uint x; { storage := delAt(storage, d1) } { x := 9 } x = 9 }
    ~[sequentialToParallel]~> cdl!{ ∀ uint x; { storage := delAt(storage, d1) ‖ x := 9 } x = 9 }
    ~[applyOnRigid]~> cdl!{ ∀ uint x; 9 = 9 }
    ~[concrete]~> cdl!{ ∀ uint x; true } := by
  sol_chain
#last_line chain
end DeleteLength

/-! ## A fixed array pushed onto a dynamic one -/

namespace PushLength
def names : FreshTable := [("sp", "sp1"), ("ie", "ie2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes FixedLength names).isEmpty
/-- `dyn.push(); x = dyn[dyn.length - 1].length;`, then `x = 3`: the element's length is its type's; the
alias `sp` to the new element is bound through an index whose bound the update checks. -/
theorem chain :
    cdl!{ ∀ uint x; ⟨ dyn.push(); x = dyn[dyn.length - 1].length; ⟩ x = 3 }
    ~[storagePushLengthSaveReferenceElement]~> cdl!{
        ∀ uint x;
          { storage := save(storage, dyn.length, dyn.length + 1) } ⟨ uint[3]storage sp = dyn[dyn.length - 1]; x = 3; ⟩ x = 3 }
    ~[storageLocalDeclInitDrop]~> cdl!{ ∀ uint x; { storage := save(storage, dyn.length, dyn.length + 1) } ⟨ sp = dyn[dyn.length - 1]; x = 3; ⟩ x = 3 }
    ~[storageIndexRead_unfold_rightSndIndex]~> cdl!{
        ∀ uint x;
          { storage := save(storage, dyn.length, dyn.length + 1) } ⟨ uint ie = dyn.length - 1; sp = dyn[ie]; x = 3; ⟩ x = 3 }
    ~[localValueDeclInitDrop]~> cdl!{
        ∀ uint x;
          { storage := save(storage, dyn.length, dyn.length + 1) } ⟨ ie = dyn.length - 1; sp = dyn[ie]; x = 3; ⟩ x = 3 }
    ~[binopUnfoldLeft]~> cdl!{
        ∀ uint x;
          { storage := save(storage, dyn.length, dyn.length + 1) }
            ⟨ uint se3 = dyn.length; ie = se3 - 1; sp = dyn[ie]; x = 3; ⟩ x = 3 }
    ~*> cdl!{
        ∀ uint x;
          { storage := save(storage, dyn.length, dyn.length + 1) }
            { se3 := dyn.length } ⟨ ie = se3 - 1; sp = dyn[ie]; x = 3; ⟩ x = 3 }
    ~[binopAssignment]~> cdl!{
        ∀ uint x;
          { storage := save(storage, dyn.length, dyn.length + 1) }
            { se3 := dyn.length } { ie := se3 - 1 } ⟨ sp = dyn[ie]; x = 3; ⟩ x = 3 }
    ~*> cdl!{
        ∀ uint x;
          { storage := save(storage, dyn.length, dyn.length + 1) }
            { se3 := dyn.length } { ie := se3 - 1 } { sp := dyn[ie] } { x := 3 } x = 3 }
    ~[applyOnRigid]~> cdl!{
        ∀ uint x;
          { storage := save(storage, dyn.length, dyn.length + 1) }
            { se3 := dyn.length } { ie := se3 - 1 } { sp := dyn[ie] } 3 = 3 }
    ~[sequentialToParallel]~> cdl!{
        ∀ uint x;
          { storage := save(storage, dyn.length, dyn.length + 1) ‖
              se3 := find(save(storage, dyn.length, dyn.length + 1), dyn.length) ‖
              ie := find(save(storage, dyn.length, dyn.length + 1), dyn.length) - 1 ‖
              sp :=
                dyn[find(save(storage, dyn.length, dyn.length + 1), dyn.length) -
                    1]@save(storage, dyn.length, dyn.length + 1) }
            3 = 3 }
    ~[concrete]~> cdl!{
        ∀ uint x;
          { storage := save(storage, dyn.length, dyn.length + 1) ‖
              se3 := find(save(storage, dyn.length, dyn.length + 1), dyn.length) ‖
              ie := find(save(storage, dyn.length, dyn.length + 1), dyn.length) - 1 ‖
              sp :=
                dyn[find(save(storage, dyn.length, dyn.length + 1), dyn.length) -
                    1]@save(storage, dyn.length, dyn.length + 1) }
            true } := by
  sol_chain
#last_line chain
end PushLength

end Solidity.Examples.Chains.FixedLength
