import Solidity.Yul.Views.RetainedChildPack

namespace Solidity.Yul.Views

def RetainedArrayLayout.lengthValue {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a) (n : Roadmap.Word) :
    Source.Val E.layout (E.cellTy r.path) := (aggregate_array_cell r.typed).symm ▸ uintValueOfWord E.layout n

theorem RetainedArrayLayout.length_encode {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a) (n : Roadmap.Word) :
    r.header.codec.encode (r.lengthValue n) = r.header.field.findWord n := by
  apply Fin.ext
  have val := congrArg Fin.val (DeclPosition.registration_encode
    ((dynamicHeaderSeed E).position (roundSlot r.cursor)) r.path (aggregate_array_cell r.typed) a r.header_bound
    (uintValueOfWord E.layout n))
  have encoded : (r.header.codec.encode (r.lengthValue n)).val = n.val := by
    rw [show (r.header.codec.encode (r.lengthValue n)).val =
      (((dynamicHeaderSeed E).position (roundSlot r.cursor)).codec.encode (uintValueOfWord E.layout n)).val from val]
    change intPayload .u256 (n.val : Int) = n.val
    simp only [intPayload,if_neg (Int.not_lt.mpr (Int.natCast_nonneg _)),Int.toNat_natCast]
  rw [encoded]
  change n.val = n.val/256^r.header.field.offset%256^r.header.field.width
  have offset : r.header.field.offset=0 := by
    change ((dynamicHeaderSeed E).position (roundSlot r.cursor)).start%32=0
    rw [dynamic_header_start]
    exact (roundSlot_spec r.cursor).2.2
  rw [offset,show r.header.field.width=32 from rfl]
  simp only [Nat.pow_zero,Nat.div_one]
  exact (Nat.mod_eq_of_lt (by simpa only [show 256^32=2^256 from by decide] using n.isLt)).symm

theorem RetainedArrayLayout.view_length_cell {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a)
    (s : Source.Storage E.layout (E.lay a)) (m : SlotView)
    (view : scalarPathView r.header.path r.header.codec r.header.slot s m) :
    s.read r.path=some (r.lengthValue (m r.header.slot)) := by
  obtain ⟨v,read,encoded⟩ := Option.map_eq_some_iff.mp view
  have same := r.header.codec.encode_injective (encoded.trans (r.length_encode _).symm)
  rw [same] at read
  exact read

theorem RetainedArrayLayout.readLen_view {E τ b child active Γ F} (r : @RetainedArrayLayout E τ b child active F.this)
    (s : Source.EMState E Γ) (m : SlotView)
    (view : scalarPathView r.header.path r.header.codec r.header.slot (s.2.ex.world.accounts F.this).storage m) :
    (Source.readLen F r.path).run s = (.ok (m r.header.slot).val,s) := by
  have read := r.view_length_cell _ m view
  have raw : (Source.readCell (E := E) F r.path).run s = (.ok (r.lengthValue (m r.header.slot)),s) := by
    unfold Source.readCell
    rw [Source.Hoare.run_bind,show (Source.EM.st (E := E) (Γ := Γ)).run s = (.ok s.2,s) from rfl]
    dsimp only
    rw [r.bank]
    simp only [Bool.false_eq_true,if_false,read]
    rfl
  have typed : (Source.readAt F r.path (.int .u256)).run s = (.ok (uintValueOfWord E.layout (m r.header.slot)),s) := by
    unfold Source.readAt
    rw [Source.Hoare.run_bind,raw]
    simp only [dif_pos (aggregate_array_cell r.typed)]
    have cancel : (aggregate_array_cell r.typed) ▸ r.lengthValue (m r.header.slot) = uintValueOfWord E.layout (m r.header.slot) := sourceVal_transport_cancel _ _
    change ((Except.ok ((aggregate_array_cell r.typed) ▸ r.lengthValue (m r.header.slot)) : Except Source.Halt (Source.Val E.layout (.int .u256))),s)=_
    rw [cancel]
  unfold Source.readLen
  rw [Source.Hoare.run_bind,typed]
  rfl

theorem RetainedArrayLayout.sourceLength_view {E τ b child active Γ F} (r : @RetainedArrayLayout E τ b child active F.this)
    (s : Source.EMState E Γ) (m : SlotView)
    (view : scalarPathView r.header.path r.header.codec r.header.slot (s.2.ex.world.accounts F.this).storage m) :
    aggregateSourceLengths F s r.header = some (m r.header.slot) := by
  unfold aggregateSourceLengths
  rw [r.header_path,r.readLen_view s m view]
  dsimp only [Except.toOption,Bind.bind,Option.bind]
  rw [dif_pos (m r.header.slot).isLt]

theorem RetainedArrayLayout.indexLoc {E τ b child active Γ} {F : Source.Fr}
    (r : @RetainedArrayLayout E τ b child active F.this) (s : Source.EMState E Γ) (n : Roadmap.Word)
    (length : (Source.readLen F r.path).run s=(.ok n.val,s)) (i : Nat) :
    (Source.indexLoc F (Source.Val.storRef (τ := .array .storage τ none) (by rfl) r.path) i).run s =
      if i<n.val then (.ok (.stor (r.path.go (.index i))),s) else (.error (.revert (Source.panicData .index)),s) := by
  unfold Source.indexLoc Source.lengthOf
  rw [Source.Hoare.run_bind,length]
  dsimp only
  by_cases bound : i<n.val
  · simp only [if_pos bound]; rfl
  · simp only [if_neg bound]; rfl

end Solidity.Yul.Views
