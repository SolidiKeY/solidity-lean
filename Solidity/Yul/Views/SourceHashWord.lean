import Solidity.Yul.Views.SourceMemoryPayload

namespace Solidity.Yul.Views

/-- bytes32 uses ALL32 bytes, not shorter-bytes ABI/storage alignment. -/
theorem hashWord_fit (word : Roadmap.Word) : Source.fitBytes 32 (Source.wordBytes word)=Source.wordBytes word := by
  unfold Source.fitBytes
  rw [List.take_append,Source.wordBytes_length]
  simp only [Nat.sub_self,List.take_zero,List.append_nil]
  exact List.take_of_length_le (by rw [Source.wordBytes_length]; exact Nat.le_refl _)

/-- The owner's actual ret32/mkBytes representation observes the complete
hash Word. No truncation, dirty-bit cleanup, new value or native oracle. -/
theorem hashWord_observe (D : Source.Layout) (word : Roadmap.Word) :
    (Source.mkBytes (D := D) (n := 32) (h := by decide) (Source.wordBytes word)).word=some word := by
  change some (Source.toWord (Source.beValue (Source.fitBytes 32 (Source.wordBytes word)++
    List.replicate (32-(Source.fitBytes 32 (Source.wordBytes word)).length) 0)))=some word
  apply congrArg some
  apply Fin.ext
  change Source.beValue (Source.fitBytes 32 (Source.wordBytes word)++
    List.replicate (32-(Source.fitBytes 32 (Source.wordBytes word)).length) 0) % 2^256=word.val
  rw [hashWord_fit,Source.wordBytes_length]
  simp only [Nat.sub_self,List.replicate_zero,List.append_nil]
  rw [Source.wordBytes_value]
  exact Nat.mod_eq_of_lt word.isLt

end Solidity.Yul.Views
