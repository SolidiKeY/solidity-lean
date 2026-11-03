import Solidity.Yul.Views.ScalarCodecs
import Solidity.Yul.Views.Regions

/-! Big-endian serialization of canonical packed payloads. Region address
maps still carry the actual layout/endian obligation; this is not an
identification of storage offsets with byte-memory addresses. -/
namespace Solidity.Yul.Views

/-- Reuse concrete scalar identities in the typed byte/residual-region laws. -/
def ScalarCodec.bytesBE {D : Source.Layout} {τ : Source.STy} {f : Field}
    (c : ScalarCodec D τ f) : ByteCodec D τ f.width where
  encode v i := (Source.beBytes f.width (c.encode v).val)[i.val]'(by
    rw [Source.beBytes_length]; exact i.isLt)
  decode bs := c.decode ⟨Source.beValue (List.ofFn bs), by
    have h := scalar_beValue_bound (List.ofFn bs)
    rw [List.length_ofFn] at h
    exact h⟩
  decode_encode v := by
    have hl : List.ofFn (fun i : Fin f.width =>
        (Source.beBytes f.width (c.encode v).val)[i.val]'(by
          rw [Source.beBytes_length]; exact i.isLt)) =
        Source.beBytes f.width (c.encode v).val := by
      apply List.ext_getElem
      · simp only [List.length_ofFn, Source.beBytes_length]
      · intro i hi hj
        simp only [List.getElem_ofFn]
    simp only [hl, Source.beValue_beBytes _ _ (c.encode v).isLt]
    exact c.decode_encode v

end Solidity.Yul.Views
