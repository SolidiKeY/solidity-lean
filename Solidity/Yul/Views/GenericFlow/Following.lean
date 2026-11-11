/-!
# Checked ownership following
The varying computations and the existing, state-indexed Plan constructor are parameters. `Following` stores only actual inventory/encoding/check equations; it assumes no final view, inverse, frame or freshness law. In particular, its result remains the caller's intrinsic Plan type, not an erased state. The reducible runner preserves the separation-check/decoder branch order used by the existing negative Controls. Matches inspect parameter-only `Option`s, not indexed families (intrinsic Gate G0).
-/

namespace Solidity.Yul.Views.GenericFlow

/-- Intrinsic preparation computations and the checked constructor of an
existing Plan. The inventory computation stays lazy; the constructor receives
every computation equation it needs. -/
structure PreparationShape (Inventory Raw Operation Plan : Type) where
  inventory? : Unit → Option Inventory
  encode? : Inventory → Option Raw
  checkOld : Inventory → Bool
  checkNext : Raw → Bool
  write? : Raw → Option Operation
  build : (old : Inventory) → inventory? () = some old →
    (raw : Raw) → encode? old = some raw → checkOld old = true →
    checkNext raw = true → (op : Operation) → write? raw = some op → Plan

namespace PreparationShape

variable {Inventory Raw Operation Plan : Type}

/-- The same checked preparation as each existing family, with its constructor
and varying computations supplied intrinsically. -/
abbrev prepare? (shape : PreparationShape Inventory Raw Operation Plan) : Option Plan :=
  match oldComputed : shape.inventory? () with
  | none => none
  | some old => match encoded : shape.encode? old with
    | none => none
    | some raw =>
      if oldChecked : shape.checkOld old = true then
        if nextChecked : shape.checkNext raw = true then
          match prepared : shape.write? raw with
          | none => none
          | some op => some (shape.build old oldComputed raw encoded oldChecked nextChecked op prepared)
        else none
      else none

theorem prepare_eq (shape : PreparationShape Inventory Raw Operation Plan)
    (old : Inventory) (oldComputed : shape.inventory? () = some old)
    (raw : Raw) (encoded : shape.encode? old = some raw)
    (oldChecked : shape.checkOld old = true) (nextChecked : shape.checkNext raw = true)
    (op : Operation) (prepared : shape.write? raw = some op) :
    shape.prepare? = some (shape.build old oldComputed raw encoded oldChecked nextChecked op prepared) := by
  unfold prepare?
  split
  next absent => rw [absent] at oldComputed; cases oldComputed
  next old' found =>
    have same := Option.some.inj (found.symm.trans oldComputed)
    subst old'
    split
    next absent => rw [absent] at encoded; cases encoded
    next raw' found =>
      have same := Option.some.inj (found.symm.trans encoded)
      subst raw'
      split
      next accepted =>
        split
        next absent => rw [absent] at prepared; cases prepared
        next op' found =>
          have same := Option.some.inj (found.symm.trans prepared)
          subst op'
          rfl
      next rejected => exact False.elim (rejected oldChecked)

end PreparationShape

/-- Already computed input provenance for following preparation. New output
geometry and decoding remain actual checked computations, not law fields. -/
structure Following {Inventory Raw Operation Plan : Type}
    (shape : PreparationShape Inventory Raw Operation Plan) where
  old : Unit → Inventory
  oldComputed : shape.inventory? () = some (old ())
  raw : Raw
  encoded : shape.encode? (old ()) = some raw
  oldChecked : shape.checkOld (old ()) = true

namespace Following

variable {Inventory Raw Operation Plan : Type}
variable {shape : PreparationShape Inventory Raw Operation Plan}

abbrev run? (p : Following shape) : Option Plan :=
  if checked : shape.checkNext p.raw = true then
    match prepared : shape.write? p.raw with
    | none => none
    | some op => some (shape.build (p.old ()) p.oldComputed p.raw p.encoded p.oldChecked checked op prepared)
  else none

theorem fresh (p : Following shape) : p.run? = shape.prepare? := by
  unfold PreparationShape.prepare?
  split
  next absent =>
    have found := p.oldComputed
    rw [absent] at found
    cases found
  next old found =>
    have same := Option.some.inj (found.symm.trans p.oldComputed)
    subst old
    split
    next absent =>
      have encoded := p.encoded
      rw [absent] at encoded
      cases encoded
    next raw found =>
      have same := Option.some.inj (found.symm.trans p.encoded)
      subst raw
      split
      next accepted =>
        unfold run?
        split <;> rfl
      next rejected => exact False.elim (rejected p.oldChecked)

theorem ready (p : Following shape) (checked : shape.checkNext p.raw = true)
    (decoded : (shape.write? p.raw).isSome) : p.run?.isSome := by
  unfold run?
  rw [dif_pos checked]
  split
  next absent => rw [absent] at decoded; cases decoded
  next op found => rfl

end Following
end Solidity.Yul.Views.GenericFlow
