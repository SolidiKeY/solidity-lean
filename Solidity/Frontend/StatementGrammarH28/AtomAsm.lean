import Solidity.Frontend.StatementGrammarH28.AtomTry

/-! Inline `assembly` statements over stated sub-parser premises.

The Yul body enters through `YulBodyAtom` (the existing `yulBody` parser
reads exactly `ys` as the body; a body is brace-delimited, so no lookahead
frame is needed) and the flag list through `FlagsAtom` on `asmFlags`, the
flag step of the statement dispatcher (definitionally the parser's own code).
The optional `"evmasm"` dialect token is data. Both premises are proved here
only for the empty body and the single flag `"memory-safe"`; otherwise they
are premises (an elaborator `rfl` on the rethrow body exceeds the heartbeat
budget, so that body is checked by the kernel at fixed fuel in the controls). No Yul parser completeness
is claimed, and assembly stays outside the profile (`Syn.excl`). -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- The tokens of the optional dialect. -/
def evmToks : Bool → List Tok
  | true => [.str (ascii "evmasm")]
  | false => []

/-- The Yul body premise, with fuel budget `a`. -/
def YulBodyAtom (body : Syn (.list .yulStmt)) (ys : List Tok) (a : Nat) : Prop :=
  ∀ (n : Nat) (s : St), yulBody (n + a) (locatedInput ys s) = .ok (body, s)

/-- The flag premise on the parser's flag list `sepBy1 (strArg …)` before `)`. -/
def FlagsAtom (flags : List String) (fts : List Tok) : Prop :=
  ∀ (ys : List Tok) (s : St),
    sepBy1 (strArg "assembly flag") (locatedInput (fts ++ .punct .rparen :: ys) s) =
      .ok (flags, locatedInput (.punct .rparen :: ys) s)

/-- The optional parenthesised flag list: absent, or present under the premise. -/
inductive AsmFlags : List String → List Tok → Prop where
  | none : AsmFlags [] []
  | some {flags : List String} {fts : List Tok} :
      FlagsAtom flags fts → AsmFlags flags ([.punct .lparen] ++ fts ++ [.punct .rparen])

theorem empty_yul_body : YulBodyAtom .nil [.punct .lbrace, .punct .rbrace] 1 :=
  fun _ _ => rfl

theorem memory_safe_flag_atom : FlagsAtom ["memory-safe"] [.str (ascii "memory-safe")] :=
  fun _ _ => rfl

/-- The actual `assembly` branch of `stmt`, from the premises. -/
theorem asm_step {k : SCtx} {evm : Bool} {flags : List String} {fts : List Tok}
    {body : Syn (.list .yulStmt)} {ys : List Tok} {a : Nat}
    (hf : AsmFlags flags fts) (hy : YulBodyAtom body ys a)
    (hl : ys.head? = some (.punct .lbrace)) (m : Nat) (s : St) :
    stmt (m + a + 1) k (locatedInput ([.kw .assembly] ++ evmToks evm ++ fts ++ ys) s) =
      .ok (.assembly evm flags body, s) := by
  have hbody := hy m s
  obtain ⟨ys', rfl⟩ : ∃ ys', ys = .punct .lbrace :: ys' := by
    cases ys with
    | nil => cases hl
    | cons y ys' =>
      cases hl
      exact ⟨ys', rfl⟩
  have hi : locatedInput ([.kw .assembly] ++ evmToks evm ++ fts ++ .punct .lbrace :: ys') s =
      locatedInput ([.kw .assembly] ++ evmToks evm)
        (locatedInput (fts ++ .punct .lbrace :: ys') s) := by
    simp only [← locatedInput_append, List.append_assoc]
  rw [hi]
  cases hf with
  | none =>
    cases evm
    all_goals
      rw [stmt]
      change (yulBody (m + a) (locatedInput (.punct .lbrace :: ys') s)).bind
        (fun p => .ok (Syn.assembly _ [] p.1, p.2)) = _
      rw [hbody]
      rfl
  | @some flags fts hfl =>
    have hflags := hfl (.punct .lbrace :: ys') s
    have hj : locatedInput ([.punct .lparen] ++ fts ++ [.punct .rparen] ++ .punct .lbrace :: ys') s =
        locatedInput [.punct .lparen]
          (locatedInput (fts ++ .punct .rparen :: .punct .lbrace :: ys') s) := by
      simp only [← locatedInput_append, List.append_assoc, List.cons_append, List.nil_append]
    rw [hj]
    cases evm
    all_goals
      rw [stmt]
      change (sepBy1 (strArg "assembly flag")
          (locatedInput (fts ++ .punct .rparen :: .punct .lbrace :: ys') s)).bind
        (fun p => ((do expectP .rparen
                       return Syn.assembly _ p.1 (← yulBody (m + a))) : P (Syn (.stmt k))) p.2) = _
      rw [hflags]
      change (yulBody (m + a) (locatedInput (.punct .lbrace :: ys') s)).bind
        (fun p => .ok (Syn.assembly _ flags p.1, p.2)) = _
      rw [hbody]
      rfl

#print axioms empty_yul_body
#print axioms memory_safe_flag_atom
#print axioms asm_step
end Solidity.Frontend.StatementGrammarH28
