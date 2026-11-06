import Solidity.Yul.Views.MemoryImageReadUniqueness
import Solidity.Yul.Views.MixedHeapView

/-! Proof-only identities of actual intrinsic images/entries. No global
Subsingleton instance, evaluator or representation change is introduced. -/
namespace Solidity.Yul.Adapters.ImageIdentity
open Solidity.Yul.Views

theorem image_eq {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (one two : MemoryImage p d) : one=two := by
  cases one with
  | bytes bs bound=>
    cases two with
    | bytes _ _=>rfl
    | words _ _ encoded=>cases encoded
  | string bs bound=>
    cases two with
    | string _ _=>rfl
    | words _ _ encoded=>cases encoded
  | words d ws encoded=>
    cases two with
    | bytes _ _=>cases encoded
    | string _ _=>cases encoded
    | words _ vs other=>
      have same:=encoded.words_unique other
      subst vs
      rfl

theorem entry_eq {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (one two : MixedHeapEntry p) (same : one.id=two.id) : one=two := by
  cases one with
  | mk a τ d found image=>
    cases two with
    | mk b σ x other otherImage=>
      change a=b at same
      subst b
      have packet:=Option.some.inj (found.symm.trans other)
      cases packet
      have images:=image_eq image otherImage
      cases images
      rfl

theorem entries_eq {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (one two : List (MixedHeapEntry p)) (same : one.map MixedHeapEntry.id=two.map MixedHeapEntry.id) : one=two := by
  induction one generalizing two with
  | nil=>cases two with
    | nil=>rfl
    | cons head tail=>cases same
  | cons head tail ih=>
    cases two with
    | nil=>cases same
    | cons other rest=>
      have ids:=List.cons.inj same
      rw [entry_eq head other ids.1,ih rest ids.2]
end Solidity.Yul.Adapters.ImageIdentity
