import Solidity.Semantics.Storage.Ops
import Solidity.Semantics.Storage.TypeLayout
import Solidity.Storage.HashedKeccak

/-! Typed full-word layout for the actual dependent storage paths.
The shared type layout imports no target semantics.
Symbolic locations and encoded hash inputs remain separate. -/
namespace Solidity.Semantics.IntrinsicStorage

open Solidity.Storage
/-- The existing primitive ABI word, converted explicitly to a natural. -/
def keyWord {p : PrimTy} (k : p.Denote) : Nat := (PrimTy.toWord k).val.toNat

theorem keyWord_lt {p : PrimTy} (k : p.Denote) : keyWord k < 2 ^ 256 := by
  have h : PrimTy.inRange .uint (PrimTy.toWord k).val = true := (PrimTy.toWord k).property
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  unfold keyWord
  omega

export Solidity.Evm (sizeF size sumSizes offsetIn offset tyRank_le_of_mem tyRank_member
  foldr_congr_add sizeF_eq size_struct size_prim size_array size_mapping size_fixed offsetIn_bound)

/-- Interpret only intrinsically well-typed paths; no erased selector lookup. -/
noncomputable def locate {T U : Ty} (p : Path T U) : Storage.Loc → Storage.Loc :=
  @Path.rec (fun _ _ _ => Storage.Loc → Storage.Loc)
    (fun {_} l => l)
    (fun {s f _ _} _ _ ih l => ih (l.add (offset s f)))
    (fun {E _} i _ ih l => ih (.data l (i.val.toNat * size E)))
    (fun {E _ _} i _ ih l => ih (l.add (i.val.toNat * size E)))
    (fun {_ _ _} k _ ih l => ih (.hash (keyWord k) l 0)) T U p

/-- Hash inputs include the entire nested ancestry, in evaluation order. -/
def ancestry (l : Storage.Loc) : List Pre := l.pres (2 ^ 256) keccakH

theorem locate_append {T U V : Ty} (p : Path T U) (q : Path U V) (l : Storage.Loc) :
    locate (p.append q) l = locate q (locate p l) := by
  induction p generalizing l with
  | nil => rw [Path.append_nil]; rfl
  | field h p ih => rw [Path.append_field]; exact ih q _
  | «at» i p ih => rw [Path.append_at]; exact ih q _
  | atF i p ih => rw [Path.append_atF]; exact ih q _
  | key k p ih => rw [Path.append_key]; exact ih q _

theorem ancestry_add (l : Storage.Loc) (i : Nat) : ancestry (l.add i) = ancestry l :=
  Storage.Loc.pres_add _ _ _ _

theorem ancestry_locate {T U : Ty} (p : Path T U) (l : Storage.Loc) :
    ancestry l <+: ancestry (locate p l) := by
  induction p generalizing l with
  | nil => exact List.prefix_refl _
  | field h p ih => simpa only [locate, ancestry_add] using ih (l.add (offset _ _))
  | «at» i p ih =>
    exact List.IsPrefix.trans (List.prefix_append _ _) (ih (.data l (i.val.toNat * size _)))
  | atF i p ih => simpa only [locate, ancestry_add] using ih (l.add (i.val.toNat * size _))
  | key k p ih =>
    exact List.IsPrefix.trans (List.prefix_append _ _) (ih (.hash (keyWord k) l 0))

/-- Every ancestry item has bounded word components; this is not hash injectivity. -/
def BoundedKeys : Storage.Loc → Prop
  | .root _ => True
  | .hash k l _ => k < 2 ^ 256 ∧ BoundedKeys l
  | .data l _ => BoundedKeys l

theorem boundedKeys_add (l : Storage.Loc) (i : Nat) :
    BoundedKeys (l.add i) = BoundedKeys l := by cases l <;> rfl

theorem boundedKeys_locate {T U : Ty} (p : Path T U) (l : Storage.Loc)
    (h : BoundedKeys l) : BoundedKeys (locate p l) := by
  induction p generalizing l with
  | nil => exact h
  | field hf p ih => exact ih _ (by rwa [boundedKeys_add])
  | «at» i p ih => exact ih _ h
  | atF i p ih => exact ih _ (by rwa [boundedKeys_add])
  | key k p ih => exact ih _ ⟨keyWord_lt k, h⟩

theorem word_lt (l : Storage.Loc) : l.word (2 ^ 256) keccakH < 2 ^ 256 := by
  cases l <;> exact Nat.mod_lt _ (by decide)

theorem ancestry_words (l : Storage.Loc) (h : BoundedKeys l) :
    ∀ p ∈ ancestry l, p.Words := by
  induction l with
  | root o => simp [ancestry, Storage.Loc.pres]
  | hash k l o ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ih h.2 p hp
    · have e := List.mem_singleton.mp hp
      subst p
      exact ⟨h.1, word_lt l⟩
  | data l o ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ih h p hp
    · have e := List.mem_singleton.mp hp
      subst p
      exact word_lt l

/-- A reference starts at the actual contract variable's full-word offset. -/
noncomputable def reference {C : Contract} {T : Ty} (r : SRef C T) : Storage.Loc :=
  locate r.path (.root (offsetIn C.vars r.root))

theorem reference_bounded {C : Contract} {T : Ty} (r : SRef C T) :
    BoundedKeys (reference r) := boundedKeys_locate r.path _ True.intro

/-- Explicit conversion from the layout's natural bytes to runtime bytes. -/
def encoded (p : Pre) : List UInt8 := (Storage.encode p).map UInt8.ofNat

theorem bytesBE_bound (n v : Nat) : ∀ b ∈ bytesBE n v, b < 256 := by
  induction n generalizing v with
  | zero => simp [bytesBE]
  | succ n ih =>
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact ih _ b hb
    · have e := List.mem_singleton.mp hb
      subst b
      exact Nat.mod_lt _ (by decide)

theorem encode_bound (p : Pre) : ∀ b ∈ Storage.encode p, b < 256 := by
  cases p with
  | data w => exact bytesBE_bound 32 w
  | entry k w =>
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact bytesBE_bound 32 k b hb
    · exact bytesBE_bound 32 w b hb

theorem encoded_toNat (p : Pre) : (encoded p).map UInt8.toNat = Storage.encode p := by
  unfold encoded
  rw [List.map_map]
  calc
    _ = (Storage.encode p).map id := List.map_congr_left
      (fun b hb => UInt8.toNat_ofNat_of_lt' (encode_bound p b hb))
    _ = _ := List.map_id _

theorem encoded_inj {p q : Pre} (hp : p.Words) (hq : q.Words)
    (h : encoded p = encoded q) : p = q := by
  apply Storage.encode_inj hp hq
  have e := congrArg (List.map UInt8.toNat) h
  simpa only [encoded_toNat] using e


end Solidity.Semantics.IntrinsicStorage
