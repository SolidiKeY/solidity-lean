import Solidity.Lowering.V07.IntegerLocalFamily

/-!
Guarded regression: equal integer contents must not discharge alias reflection,
and an empty index domain must not masquerade as a joint family witness.
The positive family uses two distinct slots and witnesses every leading input
of IntegerLocalFamily.write; its concrete write copies9 over7. The deliberately
collapsed target map is a negative control, not a feasible family or producer.
These local-state results make no whole-compiler or global-producer claim.
-/
namespace Solidity.H62.AuditV07.IntegerLocalFamilyWitness

open Solidity.Lowering.V07

def sourceIndex (t : Source.IntTy) :
    Bool → Source.Idx [.int t, .int t] (.int t)
  | false => .here
  | true => .there .here

def targetIndex (t : Source.IntTy) :
    Bool → Idx [.val (integerPrim t), .val (integerPrim t)] (.val (integerPrim t))
  | false => .here
  | true => .there .here

def collapsedIndex (t : Source.IntTy) :
    Bool → Idx [.val (integerPrim t), .val (integerPrim t)] (.val (integerPrim t)) :=
  fun _ => .here

def sourceLocals (D : Source.Layout) (t : Source.IntTy) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    Source.Locals D [.int t, .int t] :=
  .cons (.int x hx) (.cons (.int y hy) .nil)

def targetLocals (C : Contract) (H : HTy) (t : Source.IntTy) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    TEnv C H [.val (integerPrim t), .val (integerPrim t)] :=
  (integerValue t x hx, (integerValue t y hy, ()))

/-- Values and alias reflection hold together for a nonempty two-slot family. -/
theorem related_family (D : Source.Layout) (C : Contract) (H : HTy)
    (t : Source.IntTy) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    IntegerLocalFamily t (sourceIndex t) (targetIndex t)
      (sourceLocals D t x y hx hy) (targetLocals C H t x y hx hy) := by
  constructor
  · intro k
    cases k with
    | false => exact integer_related t x hx
    | true => exact integer_related t y hy
  · intro k l
    cases k <;> cases l <;> exact Iff.rfl

/-- Equal contents can coexist with an invalid collapsed alias map. -/
theorem content_without_aliases (D : Source.Layout) (C : Contract) (H : HTy)
    (t : Source.IntTy) (n : Int) (hn : t.lo ≤ n ∧ n ≤ t.hi) :
    (∀ k, IntValueRel t
      ((sourceLocals D t n n hn hn).get (sourceIndex t k))
      (TEnv.get (collapsedIndex t k) (targetLocals C H t n n hn hn))) ∧
    ¬IntegerLocalFamily t (sourceIndex t) (collapsedIndex t)
      (sourceLocals D t n n hn hn) (targetLocals C H t n n hn hn) := by
  constructor
  · intro k
    cases k <;> exact integer_related t n hn
  · intro family
    have impossible : (0 : Nat) = 1 := (family.aliases false true).mpr rfl
    cases impossible

/-- The original write theorem applies to the same joint inputs. -/
theorem related_after_write (D : Source.Layout) (C : Contract) (H : HTy)
    (t : Source.IntTy) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (written rhs : Bool) :
    IntegerLocalFamily t (sourceIndex t) (targetIndex t)
      ((sourceLocals D t x y hx hy).set (sourceIndex t written)
        ((sourceLocals D t x y hx hy).get (sourceIndex t rhs)))
      (TEnv.set (targetIndex t written)
        (TEnv.get (targetIndex t rhs) (targetLocals C H t x y hx hy))
        (targetLocals C H t x y hx hy)) :=
  (related_family D C H t x y hx hy).write written rhs

/-- Copying the second slot updates both existing intrinsic local carriers. -/
theorem copy_second_exact (D : Source.Layout) (C : Contract) (H : HTy)
    (t : Source.IntTy) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    (sourceLocals D t x y hx hy).set (sourceIndex t false)
        ((sourceLocals D t x y hx hy).get (sourceIndex t true)) =
      sourceLocals D t y y hy hy ∧
    TEnv.set (targetIndex t false)
        (TEnv.get (targetIndex t true) (targetLocals C H t x y hx hy))
        (targetLocals C H t x y hx hy) = targetLocals C H t y y hy hy :=
  ⟨rfl, rfl⟩

def witnessLayout : Source.Layout :=
  ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩

def witnessContract : Contract := { vars := [] }

/-- Fail compilation if the imported write telescope gains or changes premises. -/
private def checkedWriteSignature :
    ∀ {D : Source.Layout} {srcΓ : Source.RCtx} {C : Contract} {H : HTy}
      {Γ : Ctx} {ι : Type} {t : Source.IntTy}
      {si : ι → Source.Idx srcΓ (.int t)}
      {ti : ι → Idx Γ (.val (integerPrim t))}
      {source : Source.Locals D srcΓ} {target : TEnv C H Γ},
      IntegerLocalFamily t si ti source target →
      ∀ written rhs : ι,
        IntegerLocalFamily t si ti (source.set (si written) (source.get (si rhs)))
          (TEnv.set (ti written) (TEnv.get (ti rhs) target) target) :=
  @IntegerLocalFamily.write

/-- Every leading input and hypothesis of the current write theorem coexists. -/
theorem complete_write_hypotheses :
    ∃ (D : Source.Layout) (srcΓ : Source.RCtx) (C : Contract) (H : HTy)
      (Γ : Ctx) (ι : Type) (t : Source.IntTy)
      (si : ι → Source.Idx srcΓ (.int t))
      (ti : ι → Idx Γ (.val (integerPrim t)))
      (source : Source.Locals D srcΓ) (target : TEnv C H Γ)
      (_family : IntegerLocalFamily t si ti source target) (written rhs : ι), True := by
  let hx : Source.IntTy.u8.lo ≤ 7 ∧ 7 ≤ Source.IntTy.u8.hi := by decide
  let hy : Source.IntTy.u8.lo ≤ 9 ∧ 9 ≤ Source.IntTy.u8.hi := by decide
  exact ⟨witnessLayout, _, witnessContract, [], _, Bool, Source.IntTy.u8,
    sourceIndex _, targetIndex _, sourceLocals witnessLayout _ 7 9 hx hy,
    targetLocals witnessContract [] _ 7 9 hx hy,
    related_family witnessLayout witnessContract [] _ 7 9 hx hy,
    false, true, True.intro⟩

#check @IntegerLocalFamily.write
#print axioms related_family
#print axioms content_without_aliases
#print axioms related_after_write
#print axioms copy_second_exact
#print axioms complete_write_hypotheses
end Solidity.H62.AuditV07.IntegerLocalFamilyWitness
