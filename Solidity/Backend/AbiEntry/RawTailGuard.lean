import Solidity.Backend.AbiEntry.RawTailGuardInterface
import Solidity.Backend.AbiEntry.TailGuard

/-! Raw-byte agreement for the existing numeric tail guard. All natural
metadata remains allowed: periodicity is proved rather than assumed as bounds.
No native load sequence or conditional branch is certified here. -/
namespace Solidity.Backend.AbiEntry.RawTailGuard
open Scalar Solidity.AbiEntry

private theorem sub_left_mod (a b : Nat) : sub (a%W) b=sub a b := by
  unfold sub
  rw [Nat.add_mod (a%W) (W-b%W),Nat.mod_mod,Nat.add_mod a (W-b%W)]

private theorem sub_right_mod (a b : Nat) : sub a (b%W)=sub a b := by
  simp only [sub,Nat.mod_mod]

private theorem tail_mod (size base relative extent : Nat) :
    tailFits (size%W) (base%W) relative (extent%W)=tailFits size base relative extent := by
  simp only [tailFits,sub_left_mod,sub_right_mod]

private theorem product_mod (length stride : Nat) :
    wrap (length*(stride%W))=wrap (length*stride) := by
  unfold wrap
  rw [Nat.mul_mod length (stride%W),Nat.mod_mod,←Nat.mul_mod]

private theorem region_mod (size address length stride : Nat) :
    regionFits (size%W) address length (stride%W)=regionFits size address length stride := by
  simp only [regionFits,product_mod,sub_left_mod]

private theorem load_mod (bytes : List UInt8) (pointer : Nat) :
    load bytes pointer%W=load bytes pointer := Nat.mod_eq_of_lt (load_lt bytes pointer)

private theorem wrap_mod (value : Nat) : wrap value%W=wrap value := Nat.mod_mod value W

theorem raw (input : Input) (shape : Solidity.AbiEntry.Shape) (base pointer : Nat) (suffix : Stack) :
    run TailGuard.code (Interface.rawTailOperands input shape base pointer++suffix)=
      some (flag (Interface.rawTailCondition input shape base pointer)::suffix) := by
  simp only [Interface.rawTailOperands,List.cons_append,List.nil_append,TailGuard.correct,
    BitVec.toNat_ofNat,←W_eq,load_mod,wrap_mod,tail_mod,region_mod,Interface.rawTailCondition]

private theorem checked_reference {α : Type} (tail region : Bool) (length : Nat) (out : α) :
    (if tail=true then
      if lim<length then (Except.error Fail.revert : Except Fail α)
      else if region=true then .ok out else .error .revert
    else .error .revert)=
      if (tail && decide (length≤lim) && region)=true then .ok out else .error .revert := by
  by_cases small : length≤lim
  · have notLarge : ¬lim<length := Nat.not_lt.mpr small
    cases tail <;> cases region <;>
      simp only [ite_eq_right notLarge,decide_eq_true small,Bool.and_true,Bool.and_false,
        ite_true,ite_false,Bool.false_eq_true]
  · have large : lim<length := Nat.lt_of_not_ge small
    cases tail <;> cases region <;>
      simp only [ite_eq_left large,decide_eq_false small,Bool.and_true,Bool.and_false,
        ite_true,ite_false,Bool.false_eq_true]

theorem reference (input : Input) (shape : Solidity.AbiEntry.Shape) (base pointer : Nat)
    (prefixed : shape.lengthPrefixed=true) :
    tailRef input shape base pointer=
      if Interface.rawTailCondition input shape base pointer=true then
        .ok (wrap (wrap (base+load input.data pointer)+32),
          load input.data (wrap (base+load input.data pointer))) else .error .revert := by
  simp only [tailRef,Interface.rawTailCondition,prefixed,ite_true]
  exact checked_reference _ _ _ _

def certificate : Interface.RawTailGuardCertificate TailGuard.code where
  toTailGuardCertificate := TailGuard.certificate
  raw := raw
  reference := reference

/-- info: 'Solidity.Backend.AbiEntry.RawTailGuard.raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw
/-- info: 'Solidity.Backend.AbiEntry.RawTailGuard.reference' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms reference
/-- info: 'Solidity.Backend.AbiEntry.RawTailGuard.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.RawTailGuard
