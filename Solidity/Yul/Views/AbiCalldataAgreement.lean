import Solidity.Yul.Views.AbiWordInput

namespace Solidity.Yul.Views

/-- The owner's fitBytes padding and the physical calldata zero-extension
agree at every byte in the requested interval, without an input-size cap. -/
theorem abi_fitBytes_byte (bs : Roadmap.Bytes) (n i : Nat) (inside : i<n) :
    (Source.fitBytes n bs)[i]?=some (bs[i]?.getD 0) := by
  rw [Source.fitBytes,List.getElem?_take_of_lt inside]
  by_cases live : i<bs.length
  · rw [List.getElem?_append_left live,List.getElem?_eq_getElem live]
    rfl
  · rw [List.getElem?_append_right (Nat.le_of_not_gt live),List.getElem?_replicate_of_lt (by omega),
      List.getElem?_eq_none (Nat.le_of_not_gt live)]
    rfl

theorem abi_readBytes_fit (input : Roadmap.Bytes) (a n : Nat) :
    readBytes (calldataBytes input) a n=Source.fitBytes n (input.drop a) := by
  apply List.ext_getElem?
  intro i
  by_cases inside : i<n
  · rw [abi_fitBytes_byte _ n i inside]
    simp only [readBytes,List.getElem?_map,List.getElem?_range inside,Option.map_some,calldataBytes,List.getElem?_drop]
  · have left : (readBytes (calldataBytes input) a n).length≤i := by
      simp only [readBytes,List.length_map,List.length_range]
      omega
    have right : (Source.fitBytes n (input.drop a)).length≤i := by rw [Source.fitBytes_length]; omega
    rw [List.getElem?_eq_none left,List.getElem?_eq_none right]

theorem abi_beValue_readBytes (m : ByteView) (a n : Nat) :
    Source.beValue (readBytes m a n)=readBE m a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have step : readBytes m a (n+1)=readBytes m a n++[m (a+n)] := by
      simp only [readBytes,List.range_succ,List.map_append,List.map_singleton]
    rw [step,Source.beValue_append,ih,readBE]
    omega

/-- Exact actual source ABI input-word agreement with the physical calldata
builtin; source head indices select byte32*i and both pad out-of-input bytes. -/
theorem abi_wordAt_calldataload (input : Roadmap.Bytes) (i : Nat) :
    Source.wordAt input i=calldataload input (32*i) := by
  change Source.beValue (Source.fitBytes 32 (input.drop (32*i)))=readBE (calldataBytes input) (32*i) 32
  rw [← abi_readBytes_fit,abi_beValue_readBytes]

theorem abiInputWord_calldataloadWord (input : Roadmap.Bytes) (i : Nat) :
    abiInputWord input i=calldataloadWord input (32*i) := Fin.ext (abi_wordAt_calldataload input i)

/-- Preserve the distinction between a source argument slice and complete
transaction calldata, including selectors or other exact prefixes. -/
theorem calldata_drop_load (input : Roadmap.Bytes) (base offset : Nat) :
    calldataload (input.drop base) offset=calldataload input (base+offset) := by
  have aux (n : Nat) : readBE (calldataBytes (input.drop base)) offset n=
      readBE (calldataBytes input) (base+offset) n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [readBE,readBE,ih]
      simp only [calldataBytes,List.getElem?_drop,Nat.add_assoc]
  exact aux 32

theorem abi_wordAt_slice_calldataload (input : Roadmap.Bytes) (base i : Nat) :
    Source.wordAt (input.drop base) i=calldataload input (base+32*i) := by
  rw [abi_wordAt_calldataload,calldata_drop_load]

/-- Copying the exact requested raw interval agrees with the owner's actual
fitBytes zero-padding, regardless of residual memory or destination alignment. -/
theorem abi_calldatacopy_fit (m : ByteView) (input : Roadmap.Bytes) (dst src n : Nat) :
    readBytes (calldatacopy m input dst src n) dst n = Source.fitBytes n (input.drop src) :=
  (calldatacopy_readBytes m input dst src n).trans (abi_readBytes_fit input src n)

/-- A copied word agrees with the actual ABI reader of the explicitly selected
input slice. Prefixes/selectors are retained unless the caller chooses base;
no native destination-range or compiler admission is asserted. -/
theorem abi_calldatacopy_slice_word (m : ByteView) (input : Roadmap.Bytes)
    (dst base i : Nat) :
    mload (calldatacopy m input dst (base + 32 * i) 32) dst = abiInputWord (input.drop base) i := by
  apply Fin.ext
  exact (abi_beValue_readBytes (calldatacopy m input dst (base + 32 * i) 32) dst 32).symm.trans
    ((congrArg Source.beValue (calldatacopy_readBytes m input dst (base + 32 * i) 32)).trans
      ((abi_beValue_readBytes (calldataBytes input) (base + 32 * i) 32).trans
        (abi_wordAt_slice_calldataload input base i).symm))

/-- The actual generic ABI word decoder observes the same copied word and
explicit source slice, including unchanged success, revert and stuck results.
No per-type decoder or canonical-memory cleaning is introduced. -/
theorem abi_calldatacopy_decodeWord (D : Source.Layout) (ty : Source.STy)
    (m : ByteView) (input : Roadmap.Bytes) (dst base i : Nat) :
    Source.decodeWord D (mload (calldatacopy m input dst (base + 32 * i) 32) dst).val ty =
      Source.decodeWord D (Source.wordAt (input.drop base) i) ty := by
  -- Infer the elementary numeric equality before applying the decoder; an
  -- expected decoder/Fin projection type causes expensive unfolding here.
  have same := congrArg Fin.val (abi_calldatacopy_slice_word m input dst base i)
  exact congrArg (fun value : Nat => Source.decodeWord D value ty) same

/-- Exact zero padding transported back to the actual source input reader. -/
theorem abi_wordAt_past_input (input : Roadmap.Bytes) (i : Nat) (outside : input.length≤32*i) :
    Source.wordAt input i=0 := by
  rw [abi_wordAt_calldataload]
  exact calldataload_zero input _ outside

end Solidity.Yul.Views
