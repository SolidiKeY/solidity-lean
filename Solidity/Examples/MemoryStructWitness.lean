import Solidity.Calculus.MemStructCut

/-! # Sharing, freshness and absence controls for finite struct witnesses -/
namespace Solidity.Examples.MemoryStructWitness
open Solidity.MemoryWitness
abbrev Tok : RefTy := .struct "Token"
abbrev Acc : RefTy := .struct "Account"
abbrev Per : RefTy := .struct "Person"

/-- Two fresh parents share one existing child, without deep copying it. -/
def shared : Plan [] [Tok, Acc, Per, Per] :=
  ((uintOfNat 7, ()), ((uintOfNat 9, (⟨0, rfl⟩, ())),
    ((⟨1, rfl⟩, (uintOfNat 11, ())), ((⟨1, rfl⟩, (uintOfNat 12, ())), ()))))

/-- Full ordered observations: heap size, both child identities, sentinel,
and each parent's independent primitive field. -/
def sharedObs : List Nat :=
  let hp := realize Heap.empty [Tok, Acc, Per, Per] shared
  [(finalTy [] [Tok, Acc, Per, Per]).length,
   (hp.field (⟨2, rfl⟩ : HRef _ Per) (f := "account") rfl : HRef _ Acc).id,
   (hp.field (⟨3, rfl⟩ : HRef _ Per) (f := "account") rfl : HRef _ Acc).id,
   (hp.field (⟨0, rfl⟩ : HRef _ Tok) (f := "value") rfl : PrimTy.uint.Denote).1.toNat,
   (hp.field (⟨2, rfl⟩ : HRef _ Per) (f := "age") rfl : PrimTy.uint.Denote).1.toNat,
   (hp.field (⟨3, rfl⟩ : HRef _ Per) (f := "age") rfl : PrimTy.uint.Denote).1.toNat,
   (hp.field (⟨1, rfl⟩ : HRef _ Acc) (f := "balance") rfl : PrimTy.uint.Denote).1.toNat,
   (hp.field (⟨1, rfl⟩ : HRef _ Acc) (f := "token") rfl : HRef _ Tok).id]

/-- Sharing and distinct fresh parents coexist; every field is read back. -/
theorem shared_observations : sharedObs = [4, 1, 1, 7, 11, 12, 9, 0] := by decide +kernel
/-- info: [4, 1, 1, 7, 11, 12, 9, 0] -/
#guard_msgs in #eval sharedObs

/-- Independent children stay distinct; no blanket sharing is assumed. -/
def distinct : Plan [] [Tok, Acc, Tok, Acc, Per, Per] :=
  ((uintOfNat 7, ()), ((uintOfNat 9, (⟨0, rfl⟩, ())),
    ((uintOfNat 8, ()), ((uintOfNat 10, (⟨2, rfl⟩, ())),
      ((⟨1, rfl⟩, (uintOfNat 11, ())), ((⟨3, rfl⟩, (uintOfNat 12, ())), ()))))))

/-- Ordered identities and observations of the independently realized graph. -/
def distinctObs : List Nat :=
  let hp := realize Heap.empty [Tok, Acc, Tok, Acc, Per, Per] distinct
  [(finalTy [] [Tok, Acc, Tok, Acc, Per, Per]).length,
   (hp.field (⟨4, rfl⟩ : HRef _ Per) (f := "account") rfl : HRef _ Acc).id,
   (hp.field (⟨5, rfl⟩ : HRef _ Per) (f := "account") rfl : HRef _ Acc).id,
   (hp.field (⟨0, rfl⟩ : HRef _ Tok) (f := "value") rfl : PrimTy.uint.Denote).1.toNat,
   (hp.field (⟨2, rfl⟩ : HRef _ Tok) (f := "value") rfl : PrimTy.uint.Denote).1.toNat,
   (hp.field (⟨4, rfl⟩ : HRef _ Per) (f := "age") rfl : PrimTy.uint.Denote).1.toNat,
   (hp.field (⟨5, rfl⟩ : HRef _ Per) (f := "age") rfl : PrimTy.uint.Denote).1.toNat,
   (hp.field (⟨1, rfl⟩ : HRef _ Acc) (f := "balance") rfl : PrimTy.uint.Denote).1.toNat,
   (hp.field (⟨1, rfl⟩ : HRef _ Acc) (f := "token") rfl : HRef _ Tok).id,
   (hp.field (⟨3, rfl⟩ : HRef _ Acc) (f := "balance") rfl : PrimTy.uint.Denote).1.toNat,
   (hp.field (⟨3, rfl⟩ : HRef _ Acc) (f := "token") rfl : HRef _ Tok).id]

/-- Both child identities, both sentinels and both parent fields are retained. -/
theorem distinct_observations : distinctObs = [6, 1, 3, 7, 8, 11, 12, 9, 0, 10, 2] := by decide +kernel
/-- info: [6, 1, 3, 7, 8, 11, 12, 9, 0, 10, 2] -/
#guard_msgs in #eval distinctObs

/-- A Person cannot be manufactured at an empty heap: its Account is absent. -/
theorem no_empty_person : ¬ Nonempty (MObj [] Per) := by
  intro ⟨o⟩
  have hr := (o.1 : HRef [] Acc).get?
  simp only [List.getElem?_nil, reduceCtorEq] at hr

/-- A child-first prefix supplies the exact two children of a Person. -/
def personChildren : Plan [] [Tok, Acc] :=
  ((uintOfNat 7, ()), ((uintOfNat 9, (⟨0, rfl⟩, ())), ()))

/-- A concrete nonzero-age parent over those realized children. -/
def nonzeroPerson : MObj (finalTy [] [Tok, Acc]) Per :=
  (⟨1, rfl⟩, (uintOfNat 1, ()))

/-- The parent is fresh relative to its Account child. -/
theorem parent_fresh : (root Heap.empty [Tok, Acc] personChildren nonzeroPerson).val.id ≠ 1 :=
  root_fresh Heap.empty _ personChildren nonzeroPerson (⟨1, rfl⟩ : HRef _ Acc)

end Solidity.Examples.MemoryStructWitness
