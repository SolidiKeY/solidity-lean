import Solidity.Frontend.StatementGrammarH28.MixedSplit

/-! Inhabited actual mixed-list yield and boundary controls. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def mixedItems : Syn (.list (.item ⟨true, false⟩)) :=
  .cons (.stmtItem (.returnStmt .none))
  (.cons (.stmtItem (.blockStmt (.block
    (.cons (.stmtItem (.blockStmt (.block .nil))) .nil))))
  (.cons (.uncheckedItem (.block .nil))
  (.cons (.stmtItem .breakStmt) (.cons (.stmtItem .continueStmt) .nil))))

def mixedParts : List (List Tok) :=
  [[.kw .return_, .punct .semi], braces (braces []),
   .kw .unchecked :: braces [], [.kw .break_, .punct .semi],
   [.kw .continue_, .punct .semi]]

theorem mixed_parts_chunks : ∀ part ∈ mixedParts, Chunk part := by
  intro part hm
  simp only [mixedParts, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h
  · subst part; exact .control .emptyReturn
  · subst part; exact .block (.wrap .empty)
  · subst part; exact .uncheckedBlock .empty
  · subst part; exact .control .breakLoop
  · subst part; exact .control .continueLoop

theorem mixed_intrinsic_control (L : List Choice) :
    IntrinsicItemChunks mixedItems L L mixedParts :=
  ⟨rfl, mixed_parts_chunks⟩

theorem mixed_list_no_resegmentation (parts : List (List Tok))
    (hc : ∀ part ∈ parts, Chunk part) (he : parts.flatten = mixedParts.flatten) :
    parts = mixedParts :=
  mixed_chunks_unique parts mixedParts hc mixed_parts_chunks he

theorem nonempty_layout_mixed :
    mixedItems.yield [.frags [2]] = some (mixedParts, [.frags [2]]) := rfl

theorem mixed_suffix_control (tail : List Tok) :
    chunkSuffix (mixedParts.flatten ++ tail) = some (mixedParts.tail.flatten ++ tail) := rfl

/-- A valued return is valid Solidity but outside this empty-return scanner
fragment. This is not a parser or grammar refusal. -/
theorem valued_return_outside_fragment :
    chunkSuffix [.kw .return_, .ident "x", .punct .semi] = none := rfl

theorem early_close_refused :
    ¬ Chunk [.punct .rbrace, .punct .lbrace] := by
  intro h
  have bad := chunk_frame h []
  cases bad

theorem merged_controls_not_one_chunk :
    ¬ Chunk [.kw .return_, .punct .semi, .kw .break_, .punct .semi] := by
  intro h
  have bad := chunk_frame h []
  cases bad

#print axioms mixed_parts_chunks
#print axioms mixed_intrinsic_control
#print axioms mixed_list_no_resegmentation
#print axioms nonempty_layout_mixed
#print axioms mixed_suffix_control
#print axioms valued_return_outside_fragment
#print axioms early_close_refused
#print axioms merged_controls_not_one_chunk
end Solidity.Frontend.StatementGrammarH28
