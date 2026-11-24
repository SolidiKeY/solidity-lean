import Solidity.Correctness.Lowering.Sim.Coverage.BooleanExprInference

/-! Actual statement inference for the H1361 grammar, toward
`Solidity.Goals.loweringBySimulation`. Locals are unchanged because the
selected grammar has no declarations. Fuel is Source's actual node count. -/
namespace Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain

open Source (SCtx Syn STy StmtD ItemsD)

/-- Non-declaration statement inference at every sufficient fuel. -/
def InfersStmt (C : Source.Ctx) (L : List (String × STy)) {k : SCtx}
    (s : Syn (.stmt k)) : Prop :=
  s.isDecl = false ∧ ∀ n, s.nodes.length < n → ∃ d : StmtD C L s L,
    StmtD.inferN n C L s = some ⟨L, d⟩

/-- Sequence inference retaining the caller's locals. -/
def InfersItems (C : Source.Ctx) (L : List (String × STy)) {k : SCtx}
    (b : Syn (.list (.item k))) : Prop :=
  ∀ n, b.nodes.length < n → ∃ d : ItemsD C L b L,
    ItemsD.inferN n C L b = some ⟨L, d⟩

private theorem nil_infers (C : Source.Ctx) (L) (k) : InfersItems C L (k := k) .nil := by
  intro n hn
  cases n with
  | zero => omega
  | succ n => exact ⟨.nil, rfl⟩

private theorem cons_infers {C L k} {s : Syn (.stmt k)} {b}
    (hs : InfersStmt C L s) (hb : InfersItems C L b) :
    InfersItems C L (.cons (.stmtItem s) b) := by
  intro n hn
  simp only [Syn.nodes, List.length_cons, List.length_append] at hn
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨ds, hds⟩ := hs.2 n (by omega)
    obtain ⟨db, hdb⟩ := hb n (by omega)
    unfold ItemsD.inferN
    dsimp only
    rw [hds]
    dsimp only [Option.bind]
    rw [hdb]
    exact ⟨_, rfl⟩

private theorem block_infers {C L k} {b : Syn (.list (.item k))}
    (hb : InfersItems C L b) : InfersStmt C L (.blockStmt (.block b)) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  simp only [Syn.nodes, List.length_cons] at hn
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨d, hd⟩ := hb n (by omega)
    unfold StmtD.inferN
    dsimp only
    rw [hd]
    exact ⟨_, rfl⟩

private theorem unbrace_cons_infers {C L k} {s : Syn (.stmt k)} {b}
    (hs : InfersStmt C L s) (hb : InfersItems C L b) :
    InfersStmt C L (Total.Decode.unbrace (.cons (.stmtItem s) b)) := by
  cases b with
  | nil => exact hs
  | cons i rest => exact block_infers (cons_infers hs hb)

private theorem break_infers (C : Source.Ctx) (L) (u : Bool) :
    InfersStmt C L (k := ⟨true, u⟩) .breakStmt := by
  refine ⟨rfl, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ n => exact ⟨.brk, rfl⟩

private theorem continue_infers (C : Source.Ctx) (L) (u : Bool) :
    InfersStmt C L (k := ⟨true, u⟩) .continueStmt := by
  refine ⟨rfl, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ n => exact ⟨.cont, rfl⟩

private theorem assign_stmt_infers {C L k x t}
    (h : InfersBool (C.at L) (.assign .assign (.ident x) t)) :
    InfersStmt C L (k := k) (.simpleStmt (.exprStmt (.assign .assign (.ident x) t))) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨d, hd⟩ := h.2 _ (Nat.lt_succ_self _)
    have hi : Source.Typed.infer (C.at L) (.assign .assign (.ident x) t) = some ⟨.bool, d⟩ := hd
    unfold StmtD.inferN StmtD.inferSimple
    dsimp only
    rw [hi]
    dsimp only [Option.bind, Source.Syn.isUnderscore]
    simp only [Bool.and_false, dite_true]
    exact ⟨_, rfl⟩

private theorem if_infers {C L k c} {s : Syn (.stmt k)}
    (hc : InfersBool (C.at L) c) (hs : InfersStmt C L s) :
    InfersStmt C L (.ifStmt c s .none) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  simp only [Syn.nodes, List.length_cons, List.length_append, List.length_nil] at hn
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨dc, hdc⟩ := hc.2 _ (Nat.lt_succ_self _)
    have hi : Source.Typed.infer (C.at L) c = some ⟨.bool, dc⟩ := hdc
    obtain ⟨ds, hds⟩ := hs.2 n (by omega)
    unfold StmtD.inferN
    dsimp only
    rw [hi]
    simp only [dif_pos hs.1, hds]
    exact ⟨_, rfl⟩

private theorem if_else_infers {C L k c} {s t : Syn (.stmt k)}
    (hc : InfersBool (C.at L) c) (hs : InfersStmt C L s) (ht : InfersStmt C L t) :
    InfersStmt C L (.ifStmt c s (.some t)) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  simp only [Syn.nodes, List.length_cons, List.length_append] at hn
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨dc, hdc⟩ := hc.2 _ (Nat.lt_succ_self _)
    have hi : Source.Typed.infer (C.at L) c = some ⟨.bool, dc⟩ := hdc
    obtain ⟨ds, hds⟩ := hs.2 n (by omega)
    obtain ⟨dt, hdt⟩ := ht.2 n (by omega)
    unfold StmtD.inferN
    dsimp only
    rw [hi]
    simp only [dif_pos hs.1, dif_pos ht.1, hds, Option.bind_some, hdt]
    exact ⟨_, rfl⟩

private theorem while_infers {C L l u c} {s : Syn (.stmt ⟨true, u⟩)}
    (hc : InfersBool (C.at L) c) (hs : InfersStmt C L s) :
    InfersStmt C L (k := ⟨l, u⟩) (.whileStmt c s) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  simp only [Syn.nodes, List.length_cons, List.length_append] at hn
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨dc, hdc⟩ := hc.2 _ (Nat.lt_succ_self _)
    have hi : Source.Typed.infer (C.at L) c = some ⟨.bool, dc⟩ := hdc
    obtain ⟨ds, hds⟩ := hs.2 n (by omega)
    unfold StmtD.inferN
    dsimp only
    rw [hi]
    simp only [dif_pos hs.1, hds]
    exact ⟨_, rfl⟩

/-- Inference of a singleton preserves the exact resolved statement shape. -/
theorem InfersStmt.singleton {C L k} {s : Syn (.stmt k)} (h : InfersStmt C L s) :
    ∃ d : StmtD C L s L, ItemsD.infer C L (.cons (.stmtItem s) .nil) =
      some ⟨L, .stmt d .nil⟩ := by
  let b : Syn (.list (.item k)) := .cons (.stmtItem s) .nil
  obtain ⟨d, hd⟩ := h.2 b.nodes.length (by
    simp only [b, Syn.nodes, List.length_cons, List.length_append, List.length_nil]
    omega)
  refine ⟨d, ?_⟩
  unfold ItemsD.infer ItemsD.inferN
  dsimp only
  rw [hd]
  dsimp only [Option.bind]
  rfl

variable {names : List String} {C : Source.Ctx} {L : List (String × STy)}

mutual
  /-- Actual statement inference for every selected Boolean control statement. -/
  theorem Stmt.inferred (hL : L = names.map (fun x => (x, STy.bool))) :
      ∀ {inside s}, Stmt names inside s →
        ∃ t, Total.Spells.Stmt ⟨inside, false⟩ s t ∧ InfersStmt C L t
    | _, _, .assign hx he => by
      obtain ⟨t, ht, hi⟩ := (Expr.assign hx he).inferred (Γ := C.at L) hL
      cases ht with
      | assign hl hr =>
        cases hl
        exact ⟨_, .simple (.assign (.name _) hr), assign_stmt_infers hi⟩
    | _, _, .block h => by
      obtain ⟨b, hb, hi, _⟩ := h.inferred hL
      exact ⟨_, .block hb, block_infers hi⟩
    | _, _, @Stmt.ite _ inside c a b hc ha hb => by
      obtain ⟨c', hc', hic⟩ := hc.inferred (Γ := C.at L) hL
      obtain ⟨a', ha', _, hia⟩ := ha.inferred hL
      obtain ⟨b', hb', _, hib⟩ := hb.inferred hL
      cases b with
      | nil => exact ⟨_, .ite hc' ha', if_infers hic hia⟩
      | cons _ _ => exact ⟨_, .iteElse hc' ha' hb', if_else_infers hic hia hib⟩
    | _, _, .whileLoop hc hs => by
      obtain ⟨c, hc, hic⟩ := hc.inferred (Γ := C.at L) hL
      obtain ⟨b, hb, _, hib⟩ := hs.inferred hL
      exact ⟨_, .whileLoop _ hc hb, while_infers hic hib⟩
    | _, _, .brk => ⟨_, .brk, break_infers C L false⟩
    | _, _, .cont => ⟨_, .cont, continue_infers C L false⟩

  /-- Sequence inference and the decoder's exact unbracing rule, without
  assuming any inference-completeness predicate. -/
  theorem Stmts.inferred (hL : L = names.map (fun x => (x, STy.bool))) :
      ∀ {inside ss}, Stmts names inside ss →
        ∃ b, Total.Spells.Items ⟨inside, false⟩ ss b ∧ InfersItems C L b ∧
          InfersStmt C L (Total.Decode.unbrace b)
    | _, _, .nil =>
      ⟨_, .nil, nil_infers C L _, block_infers (nil_infers C L _)⟩
    | _, _, .cons h hs => by
      obtain ⟨t, ht, hi⟩ := h.inferred hL
      obtain ⟨b, hb, hib, _⟩ := hs.inferred hL
      exact ⟨_, .stmt ht hb, cons_infers hi hib, unbrace_cons_infers hi hib⟩
end

end Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain
