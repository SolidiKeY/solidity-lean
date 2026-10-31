import Solidity.Yul.Views.Packing

/-! Documented storage widths over existing source types, not an alternative
source type language. UDVTs inherit their underlying width. Reference and
internal-function encodings need separate layout/pipeline agreements. -/
namespace Solidity.Yul.Views

inductive StorageWidth (D : Source.Layout) : Source.STy → Nat → Prop where
  | int (t : Source.IntTy) : StorageWidth D (.int t) (t.bits / 8)
  | fixed (t : Source.FixTy) : StorageWidth D (.fixed t) (t.bits / 8)
  | bool : StorageWidth D .bool 1
  | address (payable : Bool) : StorageWidth D (.address payable) 20
  | contract (d : Source.DeclName) : StorageWidth D (.contract d) 20
  | fixedBytes (n : Nat) (h : 1 ≤ n ∧ n ≤ 32) : StorageWidth D (.fixedBytes n h) n
  | enum (d : Source.DeclName) (h : 0 < D.enumSize d ∧ D.enumSize d ≤ 256) :
      StorageWidth D (.enum d) 1
  | udvt (d : Source.DeclName) {n : Nat} (underlying : StorageWidth D (D.underlying d) n) :
      StorageWidth D (.udvt d) n
  | externalFn (ps rs : List Source.STy) (m : Option Source.Mutability) :
      StorageWidth D (.fn true ps rs m) 24

/-- A field cannot cross its slot; zero-width encodings are impossible. -/
theorem StorageWidth.bounds {D : Source.Layout} {τ : Source.STy} {n : Nat}
    (h : StorageWidth D τ n) : 0 < n ∧ n ≤ 32 := by
  induction h with
  | int t => have hv := t.valid; omega
  | fixed t => have hv := t.valid; omega
  | bool | address | contract | enum | externalFn => decide
  | fixedBytes n h => exact h
  | udvt _ _ ih => exact ih

end Solidity.Yul.Views
