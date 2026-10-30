import Solidity.Frontend.Static.InferStmt
import Solidity.Frontend.Static.InferComplete

/-!
# Completeness of statement checking (G13)

`stmt_complete`/`items_complete`: every statement and block derivation of
S01 (`StmtD`, `ItemsD`) leaves locals that `inferS` finds, and so (with
soundness by construction) `inferS` decides `StmtOK`/`ItemsOK`
(`stmtOK_iff`, `itemsOK_iff`).  Expressions inside statements rely on
`typed_complete` (`Solidity/Frontend/Static/InferComplete.lean`).
-/

namespace Solidity.Frontend.Static

open Solidity.Source

section
variable {C : Ctx}

theorem mem_stmts {k : SCtx} {s : Syn (.stmt k)} {L L' : Locals} {X : List (SRes C (.stmt k) s L)}
    {d : StmtD C L s L'} (h : SRes.stmt d ∈ X) : L' ∈ (stmtsOf C X).map Sigma.fst :=
  List.mem_map.mpr ⟨⟨L', d⟩, List.mem_filterMap.mpr ⟨_, h, rfl⟩, rfl⟩

theorem exists_stmt {k : SCtx} {s : Syn (.stmt k)} {L L' : Locals} {X : List (SRes C (.stmt k) s L)}
    (h : L' ∈ (stmtsOf C X).map Sigma.fst) : ∃ d : StmtD C L s L', SRes.stmt d ∈ X := by
  obtain ⟨⟨L'', d⟩, hm, e⟩ := List.mem_map.mp h
  simp only at e
  subst e
  obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hm
  cases r with
  | stmt d' => cases hs; exact ⟨_, hr⟩

theorem exists_items {k : SCtx} {b : Syn (.list (.item k))} {L L' : Locals}
    {X : List (SRes C (.list (.item k)) b L)} (h : L' ∈ (itemsOf C X).map Sigma.fst) :
    ∃ d : ItemsD C L b L', ⟨L', d⟩ ∈ itemsOf C X := by
  obtain ⟨⟨L'', d⟩, hm, e⟩ := List.mem_map.mp h
  simp only at e
  subst e
  exact ⟨d, hm⟩

theorem simple_sub {k : SCtx} {i : Syn .simple} {L L' : Locals} {d : StmtD C (k := k) L (.simpleStmt i) L'}
    (h : ⟨L', d⟩ ∈ simpleRes C L i) : SRes.stmt d ∈ inferS C (.simpleStmt i) L :=
  List.mem_map.mpr ⟨_, h, rfl⟩

theorem simple_of_stmt {k : SCtx} {i : Syn .simple} {L L' : Locals}
    {d : StmtD C (k := k) L (.simpleStmt i) L'} (h : SRes.stmt d ∈ inferS C (.simpleStmt i) L) :
    ∃ d' : StmtD C (k := k) L (.simpleStmt i) L', ⟨L', d'⟩ ∈ simpleRes C L i := by
  obtain ⟨⟨L1, d1⟩, hp, he⟩ := List.mem_map.mp h
  cases he
  exact ⟨_, hp⟩

theorem expr_exists {L : Locals} {e : Syn .expr} {τ : STy} (d : Typed (C.at L) e τ) :
    ∃ d' : Typed (C.at L) e τ, Res.expr d' ∈ infer (C.at L) e := exists_expr (typed_complete d)

theorem condOpt_complete {L : Locals} {c : Syn (.opt .expr)} : OptCond (C.at L) c → ∃ d, d ∈ condOpt C L c
  | .none => ⟨_, List.mem_singleton.mpr rfl⟩
  | .some d => by
    obtain ⟨d', h⟩ := expr_exists d
    exact ⟨_, List.mem_filterMap.mpr ⟨⟨.bool, d'⟩, mem_tysOf' h, rfl⟩⟩

theorem exprOpt_complete {L : Locals} {c : Syn (.opt .expr)} : OptExpr (C.at L) c → ∃ d, d ∈ exprOpt C L c
  | .none => ⟨_, List.mem_singleton.mpr rfl⟩
  | .some d => by
    obtain ⟨d', h⟩ := expr_exists d
    exact ⟨_, List.mem_map.mpr ⟨_, mem_tysOf' h, rfl⟩⟩

theorem resolve_loc_mem {Γ : Ctx} {x : String} {i : Nat} (h : Γ.resolve x = Option.some (.loc i)) :
    x ∈ Γ.locals.map Prod.fst := by
  unfold Ctx.resolve Env.resolve at h
  split at h
  · rename_i j hj
    have : ((Γ.locals.map Prod.fst).idxOf? x).isSome := by rw [hj]; rfl
    exact List.isSome_idxOf?.mp this
  · split at h
    · cases hb : Builtin.ofName x <;> rw [hb] at h <;> cases h
    · cases h

end

mutual

/-- **Completeness for statements**: S01's statement derivations are all
found. -/
theorem stmt_complete {C : Ctx} : {k : SCtx} → {L : Locals} → {s : Syn (.stmt k)} → {L' : Locals} →
    StmtD C L s L' → L' ∈ stmtLocals C s L
  | _, _, _, _, .expr d => by
    obtain ⟨d', h⟩ := expr_exists d
    exact mem_stmts (d := .expr d') (simple_sub (List.mem_append_left _ (List.mem_map.mpr ⟨_, mem_tysOf' h, rfl⟩)))
  | _, _, _, _, .placeholder h => by
    refine mem_stmts (d := .placeholder h) (simple_sub (List.mem_append_right _ ?_))
    simp only
    rw [dif_pos h]
    exact List.mem_singleton.mpr rfl
  | _, L, _, _, .declVar (t := t) (l := l) ht hl => by
    refine mem_stmts (d := .declVar ht hl) (simple_sub ?_)
    simp only [simpleRes]
    split
    · rename_i τ' ht'
      rw [ht] at ht'; cases ht'
      rw [dif_pos hl]; exact List.mem_singleton.mpr rfl
    · rename_i ht'; rw [ht] at ht'; cases ht'
  | _, L, _, _, .declInit ht hl d hc => by
    obtain ⟨d', h⟩ := expr_exists d
    refine mem_stmts (d := .declInit ht hl d' hc) (simple_sub ?_)
    simp only [simpleRes]
    split
    · rename_i τ' ht'
      rw [ht] at ht'; cases ht'
      rw [dif_pos hl]
      refine List.mem_filterMap.mpr ⟨_, mem_tysOf' h, ?_⟩
      simp only
      rw [dif_pos hc]
    · rename_i ht'; rw [ht] at ht'; cases ht'
  | _, _, _, _, .block d => by
    obtain ⟨d', h⟩ := exists_items (items_complete d)
    exact mem_stmts (List.mem_filterMap.mpr ⟨_, List.mem_map.mpr ⟨_, h, rfl⟩, rfl⟩)
  | _, _, _, _, .ifThen dc hs ds => by
    obtain ⟨dc', hc⟩ := expr_exists dc
    obtain ⟨ds', h⟩ := exists_stmt (stmt_complete ds)
    refine mem_stmts (d := .ifThen dc' hs ds') (List.mem_flatMap.mpr ⟨⟨.bool, dc'⟩, mem_tysOf' hc, ?_⟩)
    simp only
    rw [dif_pos hs]
    exact List.mem_flatMap.mpr ⟨_, h, List.mem_filterMap.mpr ⟨_, List.mem_singleton.mpr rfl, rfl⟩⟩
  | _, _, _, _, .ifElse dc hs ht ds dt => by
    obtain ⟨dc', hc⟩ := expr_exists dc
    obtain ⟨ds', h⟩ := exists_stmt (stmt_complete ds)
    obtain ⟨dt', h'⟩ := exists_stmt (stmt_complete dt)
    refine mem_stmts (d := .ifElse dc' hs ht ds' dt') (List.mem_flatMap.mpr ⟨⟨.bool, dc'⟩, mem_tysOf' hc, ?_⟩)
    simp only
    rw [dif_pos hs]
    refine List.mem_flatMap.mpr ⟨_, h, List.mem_filterMap.mpr ⟨SRes.someS dt', ?_, ?_⟩⟩
    · exact List.mem_filterMap.mpr ⟨_, h', rfl⟩
    · simp only [dif_pos ht]
  | _, _, _, _, .whileLoop dc hs ds => by
    obtain ⟨dc', hc⟩ := expr_exists dc
    obtain ⟨ds', h⟩ := exists_stmt (stmt_complete ds)
    refine mem_stmts (d := .whileLoop dc' hs ds') (List.mem_flatMap.mpr ⟨⟨.bool, dc'⟩, mem_tysOf' hc, ?_⟩)
    simp only
    rw [dif_pos hs]
    exact List.mem_filterMap.mpr ⟨_, h, rfl⟩
  | _, _, _, _, .doWhile hs ds dc => by
    obtain ⟨dc', hc⟩ := expr_exists dc
    obtain ⟨ds', h⟩ := exists_stmt (stmt_complete ds)
    refine mem_stmts (d := .doWhile hs ds' dc') (List.mem_flatMap.mpr ⟨⟨.bool, dc'⟩, mem_tysOf' hc, ?_⟩)
    simp only
    rw [dif_pos hs]
    exact List.mem_filterMap.mpr ⟨_, h, rfl⟩
  | _, _, _, _, .forLoop dc dp hs ds => by
    obtain ⟨dc', hc⟩ := condOpt_complete dc
    obtain ⟨dp', hp⟩ := exprOpt_complete dp
    obtain ⟨ds', h⟩ := exists_stmt (stmt_complete ds)
    refine mem_stmts (d := .forLoop dc' dp' hs ds') ?_
    show _ ∈ (if hs : _ then _ else [])
    rw [dif_pos hs]
    exact List.mem_flatMap.mpr ⟨_, hc, List.mem_flatMap.mpr ⟨_, hp, List.mem_filterMap.mpr ⟨_, h, rfl⟩⟩⟩
  | _, _, _, _, .forInit di dc dp hs ds => by
    obtain ⟨di', hi⟩ := exists_stmt (stmt_complete di)
    obtain ⟨di'', hi'⟩ := simple_of_stmt hi
    obtain ⟨dc', hc⟩ := condOpt_complete dc
    obtain ⟨dp', hp⟩ := exprOpt_complete dp
    obtain ⟨ds', h⟩ := exists_stmt (stmt_complete ds)
    refine mem_stmts (d := .forInit di'' dc' dp' hs ds') ?_
    show _ ∈ (if hs : _ then _ else [])
    rw [dif_pos hs]
    exact List.mem_flatMap.mpr ⟨_, hi', List.mem_flatMap.mpr ⟨_, hc,
      List.mem_flatMap.mpr ⟨_, hp, List.mem_filterMap.mpr ⟨_, h, rfl⟩⟩⟩⟩
  | _, _, _, _, .brk => mem_stmts (List.mem_singleton.mpr rfl)
  | _, _, _, _, .cont => mem_stmts (List.mem_singleton.mpr rfl)
  | _, _, _, _, .ret h => by
    refine mem_stmts (d := .ret h) ?_
    show _ ∈ returnRes C _ .none
    unfold returnRes
    split
    · exact List.mem_singleton.mpr rfl
    · rename_i hn; exact absurd h hn
  | _, _, _, _, .retVal hr d hc => by
    obtain ⟨d', h⟩ := expr_exists d
    refine mem_stmts (d := .retVal hr d' hc) (List.mem_append_left _ ?_)
    split
    · rename_i τ' hr'
      rw [hr] at hr'; cases hr'
      refine List.mem_filterMap.mpr ⟨_, mem_tysOf' h, ?_⟩
      simp only [dif_pos hc]
    · rename_i hn; exact absurd hr (hn _)
  | _, _, _, _, .retTuple d ds hf => by
    obtain ⟨d', h⟩ := expr_exists d
    obtain ⟨ds', hs⟩ := exists_slots (slots_complete ds)
    refine mem_stmts (d := .retTuple d' ds' hf) (List.mem_append_right _ ?_)
    refine List.mem_flatMap.mpr ⟨_, mem_tysOf' h, List.mem_filterMap.mpr ⟨_, hs, ?_⟩⟩
    simp only [dif_pos hf]
  | _, _, _, _, .emit ds hf => by
    obtain ⟨ds', h⟩ := exists_args (args_complete ds)
    refine mem_stmts (d := .emit ds' hf) (List.mem_flatMap.mpr ⟨_, h, ?_⟩)
    split
    · rename_i d' hf'
      have e' := hf.symm.trans hf'
      cases e'
      exact List.mem_singleton.mpr rfl
    · rename_i hn; exact absurd hf (hn _)
  | _, _, _, _, .revertError ds hf => by
    obtain ⟨ds', h⟩ := exists_args (args_complete ds)
    refine mem_stmts (d := .revertError ds' hf) (List.mem_flatMap.mpr ⟨_, h, ?_⟩)
    split
    · rename_i d' hf'
      have e' := hf.symm.trans hf'
      cases e'
      exact List.mem_singleton.mpr rfl
    · rename_i hn; exact absurd hf (hn _)
  | _, L, _, _, .rethrow (d := x) hb hr ht hp => by
    refine mem_stmts (d := .rethrow hb hr ht hp) ?_
    show _ ∈ rethrowRes C L _ _
    unfold rethrowRes
    rw [dif_pos hb]
    refine List.mem_filterMap.mpr ⟨x, resolve_loc_mem hr, ?_⟩
    split
    · rename_i i' hr'
      rw [hr] at hr'; cases hr'
      split
      · rw [dif_pos hp]
      · rename_i hn; exact absurd ht hn
    · rename_i hn; exact absurd hr (hn _)

/-- **Completeness for blocks.** -/
theorem items_complete {C : Ctx} : {k : SCtx} → {L : Locals} → {b : Syn (.list (.item k))} →
    {L' : Locals} → ItemsD C L b L' → L' ∈ itemsLocals C b L
  | _, _, _, _, .nil => List.mem_map.mpr ⟨⟨_, .nil⟩, List.mem_filterMap.mpr ⟨_, List.mem_singleton.mpr rfl, rfl⟩, rfl⟩
  | _, _, _, _, .stmt ds drest => by
    obtain ⟨ds', h⟩ := exists_stmt (stmt_complete ds)
    obtain ⟨dr', hr⟩ := exists_items (items_complete drest)
    refine List.mem_map.mpr ⟨⟨_, .stmt ds' dr'⟩,
      List.mem_filterMap.mpr ⟨SRes.items (ItemsD.stmt ds' dr'), ?_, rfl⟩, rfl⟩
    exact List.mem_flatMap.mpr ⟨_, List.mem_filterMap.mpr ⟨_, h, rfl⟩, List.mem_map.mpr ⟨_, hr, rfl⟩⟩
  | _, _, _, _, .unchecked db drest => by
    obtain ⟨db', h⟩ := exists_items (items_complete db)
    obtain ⟨dr', hr⟩ := exists_items (items_complete drest)
    refine List.mem_map.mpr ⟨⟨_, .unchecked db' dr'⟩,
      List.mem_filterMap.mpr ⟨SRes.items (ItemsD.unchecked db' dr'), ?_, rfl⟩, rfl⟩
    refine List.mem_flatMap.mpr ⟨_, List.mem_filterMap.mpr ⟨SRes.block db', ?_, rfl⟩,
      List.mem_map.mpr ⟨_, hr, rfl⟩⟩
    exact List.mem_map.mpr ⟨_, h, rfl⟩

end

/-- **The statement checker decides `StmtOK`.** -/
theorem stmtOK_iff {C : Ctx} {k : SCtx} {L : Locals} {s : Syn (.stmt k)} {L' : Locals} :
    StmtOK C L s L' ↔ L' ∈ stmtLocals C s L :=
  ⟨fun ⟨d⟩ => stmt_complete d, fun h => (exists_stmt h).elim fun d _ => ⟨d⟩⟩

/-- **The block checker decides `ItemsOK`.** -/
theorem itemsOK_iff {C : Ctx} {k : SCtx} {L : Locals} {b : Syn (.list (.item k))} {L' : Locals} :
    ItemsOK C L b L' ↔ L' ∈ itemsLocals C b L :=
  ⟨fun ⟨d⟩ => items_complete d, fun h => (exists_items h).elim fun d _ => ⟨d⟩⟩

end Solidity.Frontend.Static
