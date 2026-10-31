import Solidity.Backend.Executable.Prefix

/-!
# Creation consumer of checked runtime assembly

Runtime assembly has coordinate base zero, independently of the embedding
position in creation code. The theorem composes actual constructor segments,
exact returned runtime bytes, decoder roundtrip and resolved runtime targets.
This does not prove account installation, execution of runtime jumps or agreement
with pinned EVM. Arbitrary stack suffixes are certified only through continuing
prefix steps; the terminal runner exposes bytes, not a final caller frame.
The 1024-word stack bound is not proved here.
-/
namespace Solidity.Backend.Executable
open Creation

/-- A base-zero assembled runtime keeps its checked targets in the bytes returned by the constructor; its creation offset is never added to the runtime destinations. -/
theorem assembled_constructor_segments {L Lib : Type} [DecidableEq L]
    {link : Lib → Option (Vector UInt8 20)} {items : List (Item L Lib)}
    {out : Assembled Lib} (assembled : assemble 0 link items = some out)
    (p : Placement pre (encode out.code)) (args middle : List UInt8)
    (sa sb tail : List StackWord) (ma mb : List UInt8)
    (first : Prefix (pre ++ encode (exitWrapper true p.lengthWord p.offsetWord) ++ encode out.code ++ args)
      (pre ++ encode (exitWrapper true p.lengthWord p.offsetWord) ++ encode out.code ++ args)
      [] [] middle sa ma)
    (second : Prefix (pre ++ encode (exitWrapper true p.lengthWord p.offsetWord) ++ encode out.code ++ args)
      middle sa ma (encode (exitWrapper true p.lengthWord p.offsetWord) ++ encode out.code ++ args) sb mb)
    {k : Nat} {label : L} (reference : items[k]? = some (.pushTag label)) :
    let code := pre ++ encode (exitWrapper true p.lengthWord p.offsetWord) ++ encode out.code ++ args
    Exec code code tail [] (.returned (encode out.code)) ∧
    decode (encode out.code) = some out.code ∧
    ∃ j imm, tagIndex items label = some j ∧
      out.code[j]? = some (.op .JUMPDEST) ∧
      out.code[k]? = some (.push (asmWidths 0 items label) imm) ∧
      ofBytesBE imm.toList = offset out.code j ∧
      validJumpdest (encode out.code) (ofBytesBE imm.toList) = true := by
  obtain ⟨j, imm, tag, destination, push, value, _, valid⟩ :=
    assemble_pushTag assembled reference
  refine ⟨constructor_segments p true args middle sa sb tail ma mb first second,
    decode_encode _, j, imm, tag, destination, push, ?_, ?_⟩
  · simpa only [Nat.zero_add] using value
  · simpa only [encode_nil, List.nil_append, List.append_nil] using valid [] [] rfl

/-- info: 'Solidity.Backend.Executable.assembled_constructor_segments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assembled_constructor_segments
end Solidity.Backend.Executable
