import Solidity.Frontend.Testing
import Solidity.Semantics.Run
import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-! Typed mixed-reference joins: source controls in both required evaluation
modes and universal emitted-program proofs. Runtime agreement is observational. -/
solc_import "../solc/Group07Mixed.ast.json" hash 0xfea5f10915fc5cd7 as Legacy.Group07Mixed testing
solc_import "../solc/Group07MixedIR.ast.json" hash 0x8e844db3f2587f64 as ViaIR.Group07Mixed testing

namespace Group07MixedChecks
open Solidity

-- Writable escape of an ordinary calldata alias remains explicitly rejected.
#guard (Legacy.Group07Mixed.report.find? (·.name == "calldataEscape")).any (·.status == .unsupported)
#guard (ViaIR.Group07Mixed.report.find? (·.name == "calldataEscape")).any (·.status == .unsupported)

/-- Source assertions check aliases under Legacy.Group07Mixed. -/
theorem MixedLegacy_aliases :
    (Prog.run (State.init Legacy.Group07Mixed) Legacy.Group07Mixed.aliases).isOk = true := by decide +kernel

/-- Source assertions check snapshots under Legacy.Group07Mixed. -/
theorem MixedLegacy_snapshots :
    (Prog.run (State.init Legacy.Group07Mixed) Legacy.Group07Mixed.snapshots).isOk = true := by decide +kernel

/-- Source assertions check lazyPaths under Legacy.Group07Mixed. -/
theorem MixedLegacy_lazyPaths :
    (Prog.run (State.init Legacy.Group07Mixed) Legacy.Group07Mixed.lazyPaths).isOk = true := by decide +kernel

/-- Source assertions check conditionOnce under Legacy.Group07Mixed. -/
theorem MixedLegacy_conditionOnce :
    (Prog.run (State.init Legacy.Group07Mixed) Legacy.Group07Mixed.conditionOnce).isOk = true := by decide +kernel

/-- Source assertions check effectfulPaths under Legacy.Group07Mixed. -/
theorem MixedLegacy_effectfulPaths :
    (Prog.run (State.init Legacy.Group07Mixed) Legacy.Group07Mixed.effectfulPaths).isOk = true := by decide +kernel

/-- Source assertions check nested under Legacy.Group07Mixed. -/
theorem MixedLegacy_nested :
    (Prog.run (State.init Legacy.Group07Mixed) Legacy.Group07Mixed.nested).isOk = true := by decide +kernel

/-- Exact failure control: selectedFailure retains revert, never exhaustion. -/
theorem MixedLegacy_selectedFailure :
    (match Prog.run (State.init Legacy.Group07Mixed) Legacy.Group07Mixed.selectedFailure with
      | .error .revert => true | _ => false) = true := by decide +kernel

/-- Exact failure control: falseControl retains panic, never exhaustion. -/
theorem MixedLegacy_falseControl :
    (match Prog.run (State.init Legacy.Group07Mixed) Legacy.Group07Mixed.falseControl with
      | .error .panic => true | _ => false) = true := by decide +kernel

/-- Source assertions check aliases under ViaIR.Group07Mixed. -/
theorem MixedIR_aliases :
    (Prog.run (State.init ViaIR.Group07Mixed) ViaIR.Group07Mixed.aliases).isOk = true := by decide +kernel

/-- Source assertions check snapshots under ViaIR.Group07Mixed. -/
theorem MixedIR_snapshots :
    (Prog.run (State.init ViaIR.Group07Mixed) ViaIR.Group07Mixed.snapshots).isOk = true := by decide +kernel

/-- Source assertions check lazyPaths under ViaIR.Group07Mixed. -/
theorem MixedIR_lazyPaths :
    (Prog.run (State.init ViaIR.Group07Mixed) ViaIR.Group07Mixed.lazyPaths).isOk = true := by decide +kernel

/-- Source assertions check conditionOnce under ViaIR.Group07Mixed. -/
theorem MixedIR_conditionOnce :
    (Prog.run (State.init ViaIR.Group07Mixed) ViaIR.Group07Mixed.conditionOnce).isOk = true := by decide +kernel

/-- Source assertions check effectfulPaths under ViaIR.Group07Mixed. -/
theorem MixedIR_effectfulPaths :
    (Prog.run (State.init ViaIR.Group07Mixed) ViaIR.Group07Mixed.effectfulPaths).isOk = true := by decide +kernel

/-- Source assertions check nested under ViaIR.Group07Mixed. -/
theorem MixedIR_nested :
    (Prog.run (State.init ViaIR.Group07Mixed) ViaIR.Group07Mixed.nested).isOk = true := by decide +kernel

/-- Exact failure control: selectedFailure retains revert, never exhaustion. -/
theorem MixedIR_selectedFailure :
    (match Prog.run (State.init ViaIR.Group07Mixed) ViaIR.Group07Mixed.selectedFailure with
      | .error .revert => true | _ => false) = true := by decide +kernel

/-- Exact failure control: falseControl retains panic, never exhaustion. -/
theorem MixedIR_falseControl :
    (match Prog.run (State.init ViaIR.Group07Mixed) ViaIR.Group07Mixed.falseControl with
      | .error .panic => true | _ => false) = true := by decide +kernel

/-- Selected effectfulCalls retains call identities and nominal shape. -/
theorem MixedLegacy_effectfulCalls :
    (Prog.run (State.init Legacy.Group07Mixed) Legacy.Group07Mixed.effectfulCalls).isOk = true := by decide +kernel

/-- Selected stringEffects retains call identities and nominal shape. -/
theorem MixedLegacy_stringEffects :
    (Prog.run (State.init Legacy.Group07Mixed) Legacy.Group07Mixed.stringEffects).isOk = true := by decide +kernel

/-- Selected effectfulCalls retains call identities and nominal shape. -/
theorem MixedIR_effectfulCalls :
    (Prog.run (State.init ViaIR.Group07Mixed) ViaIR.Group07Mixed.effectfulCalls).isOk = true := by decide +kernel

/-- Selected stringEffects retains call identities and nominal shape. -/
theorem MixedIR_stringEffects :
    (Prog.run (State.init ViaIR.Group07Mixed) ViaIR.Group07Mixed.stringEffects).isOk = true := by decide +kernel

/-- A copied fixed array retains its exact bounds failure. -/
theorem MixedLegacy_copiedBoundsFailure :
    (match Prog.run (State.init Legacy.Group07Mixed) Legacy.Group07Mixed.copiedBoundsFailure with
      | .error .revert => true | _ => false) = true := by decide +kernel

/-- A copied fixed array retains its exact bounds failure. -/
theorem MixedIR_copiedBoundsFailure :
    (match Prog.run (State.init ViaIR.Group07Mixed) ViaIR.Group07Mixed.copiedBoundsFailure with
      | .error .revert => true | _ => false) = true := by decide +kernel

def Native : Contract := contract!{ uint[2] stored; }

/-- A selected memory arm preserves identity for every typed state/value. -/
theorem memoryIdentity : ⊨ᶠ dl[Native]{ ∀ uint v;
    [ stored[0] = v; uint[2] memory y; y[0] = v;
      uint[2] memory a = true ? y : stored; a[0] = 3;
      uint yy = y[0]; uint ss = stored[0]; ]
    yy == 3 && ss == v } := by
  sol_symex
  sol_close

/-- A selected storage arm is a snapshot independent of later storage writes. -/
theorem storageSnapshot : ⊨ᶠ dl[Native]{ ∀ uint v;
    [ stored[0] = v; uint[2] memory y;
      uint[2] memory a = false ? y : stored; stored[0] = 3; uint r = a[0]; ]
    r == v } := by
  sol_symex
  sol_close

private theorem fixedPast {E : Ty} {n : Nat} (w : SVal (.ref (.fixed E n)))
    (i : PrimTy.uint.Denote) (h : n ≤ i.1.toNat) : w.find (.atF i .nil) = none := by
  cases w with
  | fixed e =>
    have hi : e.toList[i.1.toNat]? = none := List.getElem?_eq_none (by
      rw [SVec.length_toList]
      exact h)
    rw [SVal.find_atF, hi]

private theorem fixedPastTwo {E : Ty} (w : SVal (.ref (.fixed E 2))) :
    w.find (.atF (⟨2, by decide⟩ : PrimTy.uint.Denote) .nil) = none :=
  fixedPast w _ (by decide)

attribute [local close_rw_s] fixedPastTwo


/-- A copied array's out-of-bounds word cannot be read in any typed state. -/
theorem copiedBounds : ⊨ᶠ dl[Native]{
    [ uint[2] memory y; uint[2] memory a = false ? y : stored;
      uint i = 2; uint r = a[i]; ] false } := by
  sol_symex
  sol_close

/-- Width and location are separate: a mixed join cannot erase element widths. -/
def Narrow : Contract := contract!{ uint8[2] small; }
/--
error: Solidity elaboration failed: small has a narrow element, key or value: it is used through an index, `.length`, `.push`, `.pop` or `delete`, or whole where the same narrow positions are expected, not whole
-/
#guard_msgs in #check sol[Narrow]{ uint[2] memory y;
  uint n = (true ? small : y).length; }

#print axioms Solidity.CloseS.readId_copySt_fixed
#print axioms memoryIdentity
#print axioms storageSnapshot
#print axioms copiedBounds
#print axioms MixedLegacy_effectfulPaths
#print axioms MixedIR_effectfulPaths
end Group07MixedChecks
