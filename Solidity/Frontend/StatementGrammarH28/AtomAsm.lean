import Solidity.Frontend.StatementGrammarH28.AtomTry

/-! Inline `assembly` statements over stated sub-parser premises.

The Yul body enters through `YulBodyAtom` (the existing `yulBody` parser
reads exactly `ys` as the body; a body is brace-delimited, so no lookahead
frame is needed) and the flag list through `FlagsAtom` on the parser's own
flag-list call `sepBy1 (strArg "assembly flag")` before `)`.
The optional `"evmasm"` dialect token is data. Both premises are proved here
only for the empty body, the canonical rethrow body and the single flag
`"memory-safe"`; otherwise they are premises. An elaborator `rfl` on the whole
rethrow body exceeds the heartbeat budget (which is not raised), so
`rethrow_yul_body` composes small `rfl` steps: the two inner calls, the
argument list, the outer call, the statement and the body loop. No Yul parser completeness
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

theorem yul_add_call (m : Nat) (rest : List Tok) (s : St) :
    yulExpr (m + 3) (locatedInput ([.ident "add", .punct .lparen, .ident "raw", .punct .comma,
      .yulDec 32, .punct .rparen] ++ .punct .comma :: rest) s) =
      .ok (.yulCall "add" (.cons (.yulPath "raw" []) (.cons (.yulLit (.dec 32)) .nil)),
        locatedInput (.punct .comma :: rest) s) := by
  rfl

def rethrowCallToks : List Tok :=
  [.ident "revert", .punct .lparen, .ident "add", .punct .lparen,
    .ident "raw", .punct .comma, .yulDec 32, .punct .rparen, .punct .comma,
    .ident "mload", .punct .lparen, .ident "raw", .punct .rparen, .punct .rparen]

def rethrowCall : Syn .yulExpr :=
  .yulCall "revert" (.cons (.yulCall "add"
      (.cons (.yulPath "raw" []) (.cons (.yulLit (.dec 32)) .nil)))
      (.cons (.yulCall "mload" (.cons (.yulPath "raw" []) .nil)) .nil))

theorem sepByAux_comma {α : Type} (p : P α) (n : Nat) (ts : List Tok) (s : St) :
    sepByAux p (n + 1) (locatedInput (.punct .comma :: ts) s) =
      (p (locatedInput ts s)).bind (fun q =>
        (sepByAux p n q.2).bind (fun r => .ok (q.1 :: r.1, r.2))) := rfl

theorem sepByAux_rparen {α : Type} (p : P α) (n : Nat) (ts : List Tok) (s : St) :
    sepByAux p (n + 1) (locatedInput (.punct .rparen :: ts) s) =
      .ok ([], locatedInput (.punct .rparen :: ts) s) := rfl

theorem located_length_cons (t : Tok) (ts : List Tok) (s : St) :
    (locatedInput (t :: ts) s).ts.length = (locatedInput ts s).ts.length + 1 := by
  simp only [locatedInput, List.map_cons, List.cons_append, List.length_cons]

def mloadToks : List Tok := [.ident "mload", .punct .lparen, .ident "raw", .punct .rparen]

theorem yul_mload_call (m : Nat) (rest : List Tok) (s : St) :
    yulExpr (m + 3) (locatedInput (mloadToks ++ .punct .rparen :: rest) s) =
      .ok (.yulCall "mload" (.cons (.yulPath "raw" []) .nil), locatedInput (.punct .rparen :: rest) s) := by
  rfl

theorem rethrow_call_args (m : Nat) (rest : List Tok) (s : St) :
    sepBy1 (yulExpr (m + 3)) (locatedInput ([.ident "add", .punct .lparen, .ident "raw",
      .punct .comma, .yulDec 32, .punct .rparen] ++ .punct .comma :: (mloadToks ++
        .punct .rparen :: rest)) s) =
      .ok ([.yulCall "add" (.cons (.yulPath "raw" []) (.cons (.yulLit (.dec 32)) .nil)),
        .yulCall "mload" (.cons (.yulPath "raw" []) .nil)], locatedInput (.punct .rparen :: rest) s) := by
  simp only [sepBy1, bind, StateT.bind, yul_add_call, Except.bind]
  rw [sepByAux_comma, yul_mload_call]
  simp only [Except.bind]
  rw [located_length_cons, sepByAux_rparen]
  rfl

/-- The call branch of `yulExpr`, given a non-empty argument list headed by an identifier. -/
theorem yul_call_prefix (m : Nat) (f g : String) (ts : List Tok) (s : St) :
    yulExpr (m + 1) (locatedInput (.ident f :: .punct .lparen :: .ident g :: ts) s) =
      (sepBy1 (yulExpr m) (locatedInput (.ident g :: ts) s)).bind (fun q =>
        (expectP .rparen q.2).bind (fun r => .ok (.yulCall f (toSynList q.1), r.2))) := by
  rfl

theorem rethrow_call_expr (m : Nat) (rest : List Tok) (s : St) :
    yulExpr (m + 4) (locatedInput (rethrowCallToks ++ .punct .rbrace :: rest) s) =
      .ok (rethrowCall, locatedInput (.punct .rbrace :: rest) s) := by
  have hl : rethrowCallToks ++ .punct .rbrace :: rest = .ident "revert" :: .punct .lparen ::
      .ident "add" :: ([.punct .lparen, .ident "raw", .punct .comma, .yulDec 32, .punct .rparen] ++
        .punct .comma :: (mloadToks ++ .punct .rparen :: .punct .rbrace :: rest)) :=
    rfl
  rw [hl, show m + 4 = m + 3 + 1 from rfl]
  rw [yul_call_prefix]
  have ha := rethrow_call_args m (.punct .rbrace :: rest) s
  rw [show ([.ident "add", .punct .lparen, .ident "raw", .punct .comma, .yulDec 32,
      .punct .rparen] ++ .punct .comma :: (mloadToks ++ .punct .rparen ::
        .punct .rbrace :: rest) : List Tok) =
      .ident "add" :: ([.punct .lparen, .ident "raw", .punct .comma, .yulDec 32, .punct .rparen] ++
        .punct .comma :: (mloadToks ++ .punct .rparen :: .punct .rbrace :: rest))
      from rfl] at ha
  rw [ha]
  rfl

/-- The item step of `yulBody`'s statement loop. -/
def yulItemStep (m : Nat) : P (Option (Syn .yulStmt)) := do
  if (← isP .rbrace) || (← peek).isNone then return none
  return some (← yulStmt m)

theorem yul_body_prefix (m : Nat) (ts : List Tok) (s : St) :
    yulBody (m + 1) (locatedInput (.punct .lbrace :: ts) s) =
      (many (yulItemStep m) (locatedInput ts s)).bind (fun q =>
        (expectP .rbrace q.2).bind (fun r => .ok (toSynList q.1, r.2))) := by
  rfl

theorem yul_stmt_call_prefix (m : Nat) (f : String) (ts : List Tok) (s : St) :
    yulStmt (m + 1) (locatedInput (.ident f :: .punct .lparen :: ts) s) =
      (yulExpr m (locatedInput (.ident f :: .punct .lparen :: ts) s)).bind
        (fun q => .ok (.yulExprStmt q.1, q.2)) := by
  rfl

theorem yul_item_step_ident (m : Nat) (f : String) (ts : List Tok) (s : St) :
    yulItemStep m (locatedInput (.ident f :: ts) s) =
      (yulStmt m (locatedInput (.ident f :: ts) s)).bind (fun q => .ok (some q.1, q.2)) := by
  rfl

theorem yul_item_step_rbrace (m : Nat) (ts : List Tok) (s : St) :
    yulItemStep m (locatedInput (.punct .rbrace :: ts) s) =
      .ok (none, locatedInput (.punct .rbrace :: ts) s) := by
  rfl

/-- `{ revert(add(raw, 32), mload(raw)) }`, the canonical rethrow body, by
composing the call, argument and loop steps (no elaborator `rfl` on the
whole body). -/
theorem rethrow_yul_body :
    YulBodyAtom (.cons (.yulExprStmt rethrowCall) .nil)
      (.punct .lbrace :: rethrowCallToks ++ [.punct .rbrace]) 6 := by
  intro n s
  have hstmt : yulStmt (n + 5) (locatedInput (rethrowCallToks ++ [.punct .rbrace]) s) =
      .ok (.yulExprStmt rethrowCall, locatedInput [.punct .rbrace] s) := by
    have hl : rethrowCallToks ++ [.punct .rbrace] = .ident "revert" :: .punct .lparen ::
        (rethrowCallToks.drop 2 ++ [.punct .rbrace]) := rfl
    rw [hl, yul_stmt_call_prefix, ← hl, rethrow_call_expr n []]
    rfl
  have hstep : yulItemStep (n + 5) (locatedInput (rethrowCallToks ++ [.punct .rbrace]) s) =
      .ok (some (.yulExprStmt rethrowCall), locatedInput [.punct .rbrace] s) := by
    have hl : rethrowCallToks ++ [.punct .rbrace] = .ident "revert" ::
        (rethrowCallToks.drop 1 ++ [.punct .rbrace]) := rfl
    rw [hl, yul_item_step_ident, ← hl, hstmt]
    rfl
  have hloop : many (yulItemStep (n + 5)) (locatedInput (rethrowCallToks ++ [.punct .rbrace]) s) =
      .ok ([.yulExprStmt rethrowCall], locatedInput [.punct .rbrace] s) := by
    unfold many
    obtain ⟨k, hk⟩ : ∃ k, (locatedInput (rethrowCallToks ++ [.punct .rbrace]) s).ts.length =
        k + 1 := ⟨_, located_length_cons _ _ s⟩
    rw [hk]
    exact many_aux_cons hstep (many_aux_none (yul_item_step_rbrace (n + 5) [] s))
  rw [show n + 6 = n + 5 + 1 from rfl, show (.punct .lbrace :: rethrowCallToks ++ [.punct .rbrace]
    : List Tok) = .punct .lbrace :: (rethrowCallToks ++ [.punct .rbrace]) from rfl,
    yul_body_prefix, hloop]
  rfl

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
#print axioms sepByAux_comma
#print axioms sepByAux_rparen
#print axioms located_length_cons
#print axioms yul_add_call
#print axioms yul_mload_call
#print axioms rethrow_call_args
#print axioms yul_call_prefix
#print axioms rethrow_call_expr
#print axioms yul_body_prefix
#print axioms yul_stmt_call_prefix
#print axioms yul_item_step_ident
#print axioms yul_item_step_rbrace
#print axioms rethrow_yul_body
#print axioms asm_step
end Solidity.Frontend.StatementGrammarH28
