import Solidity.Yul.Views.FixedNominalMember

/-! Existing intrinsically typed field-list recursion with the concrete extended
member callback. Successful decoding constructs MemoryFields and exact reads;
coverage and actual field support derive its inverse without assumed laws. -/
namespace Solidity.Yul.Views.FixedNominalMember
open Solidity.Yul.Views

def decodeFields {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p)) :=
  decodeFieldsWith (decode p es)

theorem decodeFields_representation {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p))
    (τs : List Source.STy) (m : ByteView) (base : Nat) (fs : Source.DataList E.layout τs)
    (decoded : decodeFields p es τs m base = some fs) :
    ∃ ws, MemoryFields p fs ws ∧ ∀ i w, ws[i]? = some w → mload m (base + i * 32) = w := by
  induction τs generalizing base with
  | nil => cases decoded; exact ⟨[], .nil, fun i w found => by cases i <;> cases found⟩
  | cons τ τs ih =>
    change (do let head ← decode p es τ (mload m base); let tail ← decodeFields p es τs m (base + 32); pure (Source.DataList.cons (Source.Data.val head) tail)) = some fs at decoded
    cases dh : decode p es τ (mload m base) with
    | none => rw [dh] at decoded; cases decoded
    | some head =>
      cases dt : decodeFields p es τs m (base + 32) with
      | none => rw [dh, dt] at decoded; cases decoded
      | some tail =>
        rw [dh, dt] at decoded
        cases decoded
        obtain ⟨ws, fields, reads⟩ := ih _ tail dt
        refine ⟨mload m base :: ws, .cons head _ (sound p es τ _ head dh).2 tail ws fields, ?_⟩
        intro i w found
        cases i with
        | zero => simpa only [Nat.zero_mul, Nat.add_zero] using Option.some.inj found
        | succ i =>
          have eq : base + (i + 1) * 32 = base + 32 + i * 32 := by omega
          rw [eq]; exact reads i w found

theorem decodeFields_reads {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) {τs : List Source.STy} {fs : Source.DataList E.layout τs} {ws : List Roadmap.Word}
    (fields : MemoryFields p fs ws) (supported : ∀ τ ∈ τs, Supported E τ) (m : ByteView) (base : Nat)
    (reads : ∀ i w, ws[i]? = some w → mload m (base + i * 32) = w) : decodeFields p es τs m base = some fs := by
  induction fields generalizing base with
  | nil => rfl
  | @cons τ τs v w encoded fs ws rest ih =>
    have head := reads 0 w rfl
    simp only [Nat.zero_mul, Nat.add_zero] at head
    have tail : decodeFields p es τs m (base + 32) = some fs := by
      apply ih (fun σ hs => supported σ (List.mem_cons_of_mem _ hs))
      intro i word found
      have read := reads (i + 1) word found
      have eq : base + (i + 1) * 32 = base + 32 + i * 32 := by omega
      rwa [eq] at read
    change (do let head ← decode p es τ (mload m base); let tail ← decodeFields p es τs m (base + 32); pure (Source.DataList.cons (Source.Data.val head) tail)) = some (Source.DataList.cons (Source.Data.val v) fs)
    simp only [head, encode p es coverage τ (supported τ List.mem_cons_self) v w encoded, tail]
    rfl

end Solidity.Yul.Views.FixedNominalMember
