import Solidity.Yul.Views.DeclarationPacking

/-! Actual declaration-derived fixed-array/struct boundary components. Reuses
repeatedMembers, PackedMembers.endByte and roundSlot; does not treat a storage
reference as inline contents or claim a whole nested Source.Data realization. -/
namespace Solidity.Yul.Views

structure DeclaredArrayStruct (E : Source.Env) (root : Source.DeclName) (base : Roadmap.Word) where
  outer : Source.DeclName
  inner : Source.DeclName
  element : Source.STy
  count : Nat
  positive : 0 < count
  arrayName : String
  structName : String
  rootFound : E.rootTy root = some (.struct .storage outer)
  outerFields : E.structFields outer .storage = some
    [(arrayName,.array .storage element (some count)),(structName,.struct .storage inner)]
  scalar : DeclScalar E.layout element
  scalarFound : declarationScalar? E.layout element = some scalar
  fields : List (String × Source.STy)
  fieldsFound : E.structFields inner .storage = some fields
  members : PackedMembers E.layout (fields.map Prod.snd)
  membersFound : declarationMembers? E.layout (fields.map Prod.snd) = some members

def DeclaredArrayStruct.first {E root base} (d : DeclaredArrayStruct E root base) :=
  repeatedMembers d.scalar.field d.scalar.width d.scalar.codec d.count

def DeclaredArrayStruct.nextByte {E root base} (d : DeclaredArrayStruct E root base) : Nat :=
  roundSlot (d.first.endByte (base.val*32))

def DeclaredArrayStruct.endByte {E root base} (d : DeclaredArrayStruct E root base) : Nat :=
  roundSlot (d.members.endByte d.nextByte)

/-- Explicit supported two-component declaration shape, not an artificial
recursive traversal budget. Other shapes remain unfinished preparation work. -/
def prepareDeclaredArrayStruct (E : Source.Env) (root : Source.DeclName) (base : Roadmap.Word) :
    Option (DeclaredArrayStruct E root base) :=
  match rootFound : E.rootTy root with
  | some (.struct .storage outer) => match outerFields : E.structFields outer .storage with
    | some [(arrayName,.array .storage element (some count)),(structName,.struct .storage inner)] =>
      if positive : 0 < count then match scalarFound : declarationScalar? E.layout element with
      | some scalar => match fieldsFound : E.structFields inner .storage with
        | some fields => match membersFound : declarationMembers? E.layout (fields.map Prod.snd) with
          | some members => some ⟨outer,inner,element,count,positive,arrayName,structName,rootFound,outerFields,
              scalar,scalarFound,fields,fieldsFound,members,membersFound⟩
          | none => none
        | none => none
      | none => none
      else none
    | _ => none
  | _ => none

theorem DeclaredArrayStruct.disjoint {E root base} (d : DeclaredArrayStruct E root base) :
    ComponentsDisjoint d.first (base.val*32) d.members d.nextByte :=
  disjoint_at_roundSlot _ _ _

theorem DeclaredArrayStruct.boundaries {E root base} (d : DeclaredArrayStruct E root base) :
    d.first.endByte (base.val*32) ≤ d.nextByte ∧ d.nextByte % 32 = 0 ∧
    d.members.endByte d.nextByte ≤ d.endByte ∧ d.endByte % 32 = 0 :=
  ⟨(roundSlot_spec _).1,(roundSlot_spec _).2.2,(roundSlot_spec _).1,(roundSlot_spec _).2.2⟩

theorem DeclaredArrayStruct.roundtrip {E root base} (d : DeclaredArrayStruct E root base)
    (arrayData : Source.DataList E.layout (List.replicate d.count d.element))
    (structData : Source.DataList E.layout (d.fields.map Prod.snd))
    (m mid out : ByteView) (arrayEncoded : d.first.encode arrayData (base.val*32) m = some mid)
    (structEncoded : d.members.encode structData d.nextByte mid = some out) :
    d.first.decode (base.val*32) out = some arrayData ∧ d.members.decode d.nextByte out = some structData :=
  composed_roundtrip _ _ _ _ d.disjoint _ _ _ _ _ arrayEncoded structEncoded

end Solidity.Yul.Views
