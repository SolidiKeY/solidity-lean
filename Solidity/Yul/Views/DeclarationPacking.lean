import Solidity.Yul.Views.DeclarationScalars
import Solidity.Source.Machine

namespace Solidity.Yul.Views

inductive DeclarationPackingError where
  | missingRoot | notStruct | missingStruct | unsupportedScalar | cellMismatch | slotOverflow
  deriving DecidableEq, Repr

def declarationFieldPath (root : Source.DeclName) (index : Nat) : Source.SPath := ⟨root,[.field index]⟩

def declarationStart {D L} (c : ScalarPath D L) : Nat := c.slot.val * 32 + c.field.offset
def declarationEnd {D L} (c : ScalarPath D L) : Nat := declarationStart c + c.field.width

def DeclPosition.registration {E : Source.Env} {τ : Source.STy} (position : DeclPosition E.layout τ)
    (p : Source.SPath) (typed : E.cellTy p = τ) (a : Roadmap.Address)
    (bound : position.start / 32 < 2^256) : ScalarPath E.layout (E.lay a) :=
  ⟨p,⟨position.start / 32,bound⟩,position.field,typed.symm ▸ position.codec,typed.symm ▸ position.width⟩

theorem DeclPosition.registration_start {E : Source.Env} {τ} (position : DeclPosition E.layout τ)
    (p : Source.SPath) (typed : E.cellTy p = τ) (a : Roadmap.Address) (bound : position.start / 32 < 2^256) :
    declarationStart (position.registration p typed a bound) = position.start := by
  change position.start / 32 * 32 + position.field.offset = position.start
  rw [position.aligned]
  have := Nat.mod_add_div position.start 32
  omega

/-- Traverses actual declared fields in order. All coordinates come from the
existing packedStart. No final slots/offsets/defaults/separation laws are inputs. -/
def packDeclarationPaths (E : Source.Env) (pathAt : Nat → Source.SPath) (a : Roadmap.Address)
    (index : Nat) (fields : List (String × Source.STy)) (cursor : Nat) :
    Except DeclarationPackingError (List (ScalarPath E.layout (E.lay a)) × Nat) :=
  match fields with
  | [] => .ok ([],cursor)
  | (_,τ)::rest => match declarationScalar? E.layout τ with
    | none => .error .unsupportedScalar
    | some seed =>
      let position := seed.position cursor
      if typed : E.cellTy (pathAt index) = τ then
        if bound : position.start / 32 < 2^256 then
          (packDeclarationPaths E pathAt a (index+1) rest (position.start+position.field.width)).map
            (fun result => (position.registration (pathAt index) typed a bound :: result.1,result.2))
        else .error .slotOverflow
      else .error .cellMismatch

/-- Backwards-compatible flat declaration entry point, with identical guards. -/
def packDeclarationFields (E : Source.Env) (root : Source.DeclName) (a : Roadmap.Address)
    (index : Nat) (fields : List (String × Source.STy)) (cursor : Nat) :
    Except DeclarationPackingError (List (ScalarPath E.layout (E.lay a)) × Nat) :=
  packDeclarationPaths E (declarationFieldPath root) a index fields cursor

structure PackedDeclaration (E : Source.Env) (root : Source.DeclName) (a : Roadmap.Address) (base : Roadmap.Word) where
  name : Source.DeclName
  rootFound : E.rootTy root = some (.struct .storage name)
  fields : List (String × Source.STy)
  fieldsFound : E.structFields name .storage = some fields
  registrations : List (ScalarPath E.layout (E.lay a))
  endByte : Nat
  packed : packDeclarationFields E root a 0 fields (base.val*32) = .ok (registrations,endByte)

def preparePackedDeclaration (E : Source.Env) (root : Source.DeclName) (a : Roadmap.Address) (base : Roadmap.Word) :
    Except DeclarationPackingError (PackedDeclaration E root a base) :=
  match rootFound : E.rootTy root with
  | none => .error .missingRoot
  | some (.struct .storage name) => match fieldsFound : E.structFields name .storage with
    | none => .error .missingStruct
    | some fields => match packed : packDeclarationFields E root a 0 fields (base.val*32) with
      | .error reason => .error reason
      | .ok (registrations,endByte) => .ok ⟨name,rootFound,fields,fieldsFound,registrations,endByte,packed⟩
  | some _ => .error .notStruct

def PackedDeclaration.nextSlot {E root a base} (d : PackedDeclaration E root a base) : Nat := roundSlot d.endByte / 32

theorem PackedDeclaration.end_alignment {E root a base} (d : PackedDeclaration E root a base) :
    d.endByte ≤ d.nextSlot*32 ∧ d.nextSlot*32 < d.endByte+32 := by
  have spec := roundSlot_spec d.endByte
  have exactEnd : d.nextSlot*32 = roundSlot d.endByte := by
    unfold PackedDeclaration.nextSlot
    have := Nat.mod_add_div (roundSlot d.endByte) 32
    omega
  rw [exactEnd]
  exact ⟨spec.1,spec.2.1⟩

end Solidity.Yul.Views
