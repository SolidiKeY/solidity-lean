import Solidity.Yul.Views.OwnedBoolRegistry
import Solidity.Yul.Views.PackedResidualCodec

namespace Solidity.Yul.Views

def chosenPathCode {D L} (c : ScalarPath D L) (old : BoolTrueByte) (raw : SlotView) : BoolTrueByte :=
  if typed : L c.path=.bool then chooseTrueByte old (fieldBooleanByte c.field (c.bool_width typed) (c.field.findWord (raw c.slot))) else old

def pathEncodingWrite {D L} (c : ScalarPath D L) (bank : Bool) (account : Roadmap.Address)
    (raw : SlotView) (before : BoolEncodingJournal) : Option (OwnedByteKey × BoolTrueByte) :=
  let key := ownedByteKey bank account c
  let next := chosenPathCode c (before.cells key) raw
  if next=before.cells key then none else some (key,next)

def encodingWrites {D L} (cs : List (ScalarPath D L)) (bank : Bool) (account : Roadmap.Address)
    (raw : SlotView) (before : BoolEncodingJournal) : List (OwnedByteKey × BoolTrueByte) :=
  cs.filterMap fun c => pathEncodingWrite c bank account raw before

theorem pathEncodingWrite_key {D L} (c : ScalarPath D L) (bank) (a) (raw) (before) (w)
    (computed : pathEncodingWrite c bank a raw before=some w) : w.1=ownedByteKey bank a c := by
  unfold pathEncodingWrite at computed
  dsimp only at computed
  split at computed
  · cases computed
  · cases computed; rfl

theorem boolEncodingRun_other (s : BoolEncodingJournal) (ws : List (OwnedByteKey × BoolTrueByte)) (key)
    (different : ∀ w ∈ ws, key≠w.1) : (boolEncodingRun s ws).cells key=s.cells key := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    rw [boolEncodingRun,ih _ (fun q member => different q (List.mem_cons_of_mem _ member))]
    exact boolEncodingSave_other _ _ _ _ (different w List.mem_cons_self)

theorem encodingWrites_other {D L} (cs : List (ScalarPath D L)) (bank) (a) (raw) (before current : BoolEncodingJournal) (key)
    (different : ∀ c ∈ cs, key≠ownedByteKey bank a c) :
    (boolEncodingRun current (encodingWrites cs bank a raw before)).cells key=current.cells key := by
  apply boolEncodingRun_other
  intro w member
  obtain ⟨c,inside,computed⟩ := List.mem_filterMap.mp member
  rw [pathEncodingWrite_key c bank a raw before w computed]
  exact different c inside

/-- Every new true-byte choice comes from the SAME supplied raw view. Initial
cell equality is a real prefix-state premise, discharged by rfl at top level.
Distinct coordinates are derived from actual finite registry separation. -/
theorem encodingWrites_cells {D L} (cs : List (ScalarPath D L)) (bank) (a) (raw)
    (before current : BoolEncodingJournal) (separated : finiteSeparated cs)
    (currentValues : ∀ c ∈ cs, current.cells (ownedByteKey bank a c)=before.cells (ownedByteKey bank a c))
    (c : ScalarPath D L) (member : c ∈ cs) :
    (boolEncodingRun current (encodingWrites cs bank a raw before)).cells (ownedByteKey bank a c)=
      chosenPathCode c (before.cells (ownedByteKey bank a c)) raw := by
  induction cs generalizing current with
  | nil => cases member
  | cons head tail ih =>
    obtain ⟨apart,tailSep⟩ := List.pairwise_cons.mp separated
    have distinct : ∀ d ∈ tail, ownedByteKey bank a head≠ownedByteKey bank a d :=
      fun d inside => ownedByteKey_distinct head d bank a (apart d inside).2
    unfold encodingWrites
    rw [List.filterMap_cons]
    cases update : pathEncodingWrite head bank a raw before with
    | none =>
      dsimp only
      change (boolEncodingRun current (encodingWrites tail bank a raw before)).cells _=_
      rcases List.mem_cons.mp member with same | inside
      · subst c
        rw [encodingWrites_other tail bank a raw before current _ distinct,currentValues head List.mem_cons_self]
        unfold pathEncodingWrite at update
        dsimp only at update
        split at update
        · rename_i same
          exact same.symm
        · cases update
      · exact ih current tailSep (fun d mem => currentValues d (List.mem_cons_of_mem _ mem)) inside
    | some w =>
      dsimp only
      change (boolEncodingRun (boolEncodingWrite current w) (encodingWrites tail bank a raw before)).cells _=_
      have key := pathEncodingWrite_key head bank a raw before w update
      have value : w.2=chosenPathCode head (before.cells (ownedByteKey bank a head)) raw := by
        unfold pathEncodingWrite at update
        dsimp only at update
        split at update
        · cases update
        · cases update; rfl
      rcases List.mem_cons.mp member with same | inside
      · subst c
        rw [encodingWrites_other tail bank a raw before _ _ distinct]
        change boolEncodingSave current.cells w.1 w.2 (ownedByteKey bank a head)=_
        rw [key,boolEncodingSave_get,value]
      · apply ih _ tailSep _ inside
        intro d mem
        change boolEncodingSave current.cells w.1 w.2 (ownedByteKey bank a d)=_
        rw [boolEncodingSave_other _ _ _ _ (by rw [key]; exact Ne.symm (distinct d mem))]
        exact currentValues d (List.mem_cons_of_mem _ mem)

theorem encodingWrites_result {D L} (cs : List (ScalarPath D L)) (bank) (a) (raw)
    (before : BoolEncodingJournal) (separated : finiteSeparated cs) (c) (member : c ∈ cs) :
    (boolEncodingRun before (encodingWrites cs bank a raw before)).cells (ownedByteKey bank a c)=
      chosenPathCode c (before.cells (ownedByteKey bank a c)) raw :=
  encodingWrites_cells cs bank a raw before before separated (fun _ _ => rfl) c member

end Solidity.Yul.Views
