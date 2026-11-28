import Solidity.Theory.Progress.Program
import Solidity.Theory.Progress.Leaves
import Solidity.Source.SoundnessExamples


namespace Solidity.Theory.Progress.Controls

open Solidity.Source Solidity.Source.Progress Solidity.Source.SemanticsExamples Solidity.Theory.Progress EM

def pairDeclAt (k : SCtx) : RStmt E0 [] false k [] [.bool, .bool] :=
  .declTuple [some .bool, none, some .bool] (.tuple (.cons (.bool true) (.cons (.bool false) (.cons (.bool true) .nil))))
    (by decide)

abbrev pairDecl : RStmt E0 [] false .body [] [.bool, .bool] := pairDeclAt .body

theorem pairDeclAt_frag (k : SCtx) : SFrag (StmtExt.none E0) (fun _ => False) (pairDeclAt k) :=
  .declTuple _ _ _
    (.lit _ (.cons (.checked _ trivial trivial) (.cons (.checked _ trivial trivial)
      (.cons (.checked _ trivial trivial) .nil))))
    ⟨rfl, .inl rfl, rfl, .inl rfl, trivial⟩

theorem pairDecl_not_valFrag : ¬ RStmt.ValFragC (fun _ => False) pairDecl := fun h => h

theorem pairDecl_ends (p : Roadmap.Pipeline) (n : Nat) (x : Locals E0.layout [] × St E0) :
    Ends ((execS (G0 p) F0 n 0 none pairDecl .nil).run x).1 :=
  tuple_stmt_progress (G0 p) F0 n 0 none pairDecl .nil (pairDeclAt_frag _)
    (by simp only [pairDeclAt, RStmt.OpsOK, RExpr.OpsOK, RArgs.OpsOK, and_self]) ⟨[], [], rfl, rfl⟩ x

theorem pairDecl_run :
    ((execS (G0 .legacy) F0 10 0 none pairDecl .nil).run (.nil, s0)).1 =
      .ok (.normal (.cons (.bool true) (.cons (.bool true) .nil))) := by
  rfl

theorem pairDecl_timeout :
    ((execS (G0 .legacy) F0 5 0 none pairDecl .nil).run (.nil, s0)).1 = .error .timeout := by
  rfl

def loopDecl : RStmt E0 [] false .body [] [] :=
  .whileLoop (u := false) (.bool true) (.block (.stmt (pairDeclAt ⟨true, false⟩) .nil))

theorem loopDecl_frag : SFrag (StmtExt.none E0) (fun _ => False) loopDecl :=
  .whileLoop _ _ trivial (.block _ (.stmt _ _ (pairDeclAt_frag _) .nil))

theorem loopDecl_ends (p : Roadmap.Pipeline) (n : Nat) (x : Locals E0.layout [] × St E0) :
    Ends ((execS (G0 p) F0 n 0 none loopDecl .nil).run x).1 :=
  tuple_stmt_progress (G0 p) F0 n 0 none loopDecl .nil loopDecl_frag
    (by simp only [loopDecl, pairDeclAt, RStmt.OpsOK, RItems.OpsOK, RExpr.OpsOK, RArgs.OpsOK, and_self])
    ⟨[], [], rfl, rfl⟩ x

theorem loopDecl_timeout :
    ((execS (G0 .legacy) F0 8 0 none loopDecl .nil).run (.nil, s0)).1 = .error .timeout := by
  rfl


theorem stuck_not_ends : ¬ Ends (.error (.stuck "no local") : Except Halt Unit) :=
  not_ends_stuck _

theorem retPair_unframed_in_frag :
    SFrag (StmtExt.none E0) (fun _ => False) (SoundnessExamples.retPair (Γ := [])) ∧
      (SoundnessExamples.retPair (Γ := [])).OpsOK :=
  ⟨.base _ ⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩), trivial, rfl, .inr (.inl ⟨_, rfl⟩), trivial⟩,
    ⟨trivial, trivial, trivial⟩⟩

theorem retPair_unframed_not_ends :
    ¬ Ends ((execS (G0 .viaIR) F0 5 0 none (SoundnessExamples.retPair (Γ := [])) .nil).run
      (.nil, s0)).1 := by
  rw [SoundnessExamples.retPair_unframed_stuck]
  exact not_ends_stuck _

def StmtExt.all (E : Env) : StmtExt E := ⟨fun _ _ => True⟩

theorem all_unsound : ¬ (StmtExt.all E0).Sound (G0 .legacy) (fun _ => False) (fun _ => True) := by
  intro hS
  have h := hS _ (fun _ _ h => h) 0 (stmtNSAtX_zero _ _ _ _)
    (fun m hm F _ => by rw [Nat.le_zero.1 hm]; exact exprNSAt_zero _ _ F) F0 trivial 0 none
    (RStmt.placeholder (R := []) (M := true) (k := .body) (Γ := []) rfl) [] .nil trivial (fun _ h => nomatch h)
    trivial ⟨[], [], rfl, rfl⟩
  exact h (.nil, s0)

theorem slotsOK_refuses_reference :
    slotsFit E0.isBase E0.mapFree [some (.string .memory)] [.stringLit [97]] = true ∧
      ¬ SlotsOK [some (.string .memory)] [.stringLit [97]] :=
  ⟨by decide, fun h => nomatch h.1⟩

theorem no_tuple_local {D : Layout} {σs : List STy} {Γ : RCtx} (l : Locals D (.tuple σs :: Γ)) : False := by
  cases l with
  | cons v _ => exact Val.not_tuple v


def assertAt (Γ : RCtx) (b : Bool) : RStmt E0 [] false .body Γ Γ :=
  .expr (.builtin .assert (.cons (.bool b) .nil) rfl)

def blockDecl : RStmt E0 [] false .body [] [] :=
  .block (.stmt pairDecl (.stmt (assertAt _ false) .nil))

theorem blockDecl_frag : SFrag (leafExt (fun _ => False)) (fun _ => False) blockDecl :=
  .block _ (.stmt _ _ (SFrag.mono (X := StmtExt.none E0) (fun _ _ h => False.elim h) (pairDeclAt_frag _))
    (.stmt _ _ (.ext _ [] (Or.inr (Or.inr (.mk _ _ _ (.assert _ (.cons (.checked _ trivial trivial) .nil)))))
      (fun _ h => nomatch h)) .nil))

theorem blockDecl_ends (p : Roadmap.Pipeline) (n : Nat) (x : Locals E0.layout [] × St E0) :
    Ends ((execS (G0 p) F0 n 0 none blockDecl .nil).run x).1 :=
  stmt_progress (c := F0.contract) (callsOKX_none _ _ _) (leafExt_sound_callFree _ _) F0 rfl n 0 none
    blockDecl .nil blockDecl_frag
    (by simp only [blockDecl, assertAt, pairDeclAt, RStmt.OpsOK, RItems.OpsOK, RExpr.OpsOK, RArgs.OpsOK, and_self])
    ⟨[], [], rfl, rfl⟩ x

theorem blockDecl_run :
    ((execS (G0 .legacy) F0 12 0 none blockDecl .nil).run (.nil, s0)).1 = .error (.revert (panicData .assert)) := by
  rfl

theorem blockDecl_panics : Ends ((execS (G0 .legacy) F0 12 0 none blockDecl .nil).run (.nil, s0)).1 := by
  rw [blockDecl_run]
  exact .panics .assert


theorem elaborated_declTuple_frag :
    SFrag (StmtExt.none _) (fun _ => False) TypingExamples.w_declTuple.toR :=
  StmtD.declTuple_frag _ _ _
    (.lit _ (.cons (.checked _ ⟨rfl, rfl, .inl rfl⟩ trivial) (.cons (.checked _ ⟨rfl, rfl, .inl rfl⟩ trivial) .nil)))
    ⟨rfl, .inl rfl, trivial⟩

theorem elaborated_declTuple_ends (G : Glob TypingExamples.Γ.env) (F : Fr) (n : Nat)
    (l : Locals TypingExamples.Γ.env.layout (tysOf TypingExamples.Γ.locals))
    (x : Locals TypingExamples.Γ.env.layout [] × St TypingExamples.Γ.env) :
    Ends ((execS G F n 1 none TypingExamples.w_declTuple.toR l).run x).1 :=
  tuple_stmt_progress G F n 1 none _ l elaborated_declTuple_frag (StmtD.toR_opsOK _)
    ⟨[.address false, .bool], [.bytes .calldata], rfl, rfl⟩ x


inductive BlockNode {E : Env} {R : List STy} {M : Bool} :
    {k : SCtx} → {Γ Γ' : RCtx} → RStmt E R M k Γ Γ' → List (Blk E R M) → Prop where
  | mk {k : SCtx} {Γ Γ₁ : RCtx} (b : RItems E R M k Γ Γ₁) : BlockNode (.block b) [⟨k, Γ, Γ₁, b⟩]

def blockExt (E : Env) : StmtExt E := ⟨BlockNode⟩

theorem blockExt_sound {E : Env} (G : Glob E) (A : Decl → Prop) (Q : String → Prop) : (blockExt E).Sound G A Q := by
  intro Z _ n ih _ F hP nps ph R M k Γ Γ' s bs l hs hbs ho hfr
  cases hs with
  | mk b =>
    have hb : IFrag Z A b := hbs _ (List.mem_singleton_self _)
    simp only [execS]
    obtain ⟨ys, rfl⟩ := RItems.ext b
    exact NSP.bind (ih.execItems F hP nps ph b l hb ho hfr) fun o h =>
      NSP.weaken (Out.close_esc ys o) fun _ h' => ⟨fun h0 => h0.elim, fun hk => h'.trans (h hk)⟩

def nestedDecl : RStmt E0 [] false .body [] [] :=
  .block (.stmt (.block (.stmt pairDecl .nil)) .nil)

theorem nestedDecl_frag : SFrag (blockExt E0) (fun _ => False) nestedDecl := by
  have inner : SFrag (blockExt E0) (fun _ => False)
      (RStmt.block (R := []) (M := false) (k := .body) (RItems.stmt pairDecl .nil)) :=
    .ext _ _ (.mk _) fun b hb => by
      rw [List.mem_singleton.1 hb]
      exact .stmt _ _ (SFrag.mono (X := StmtExt.none E0) (fun _ _ h => False.elim h) (pairDeclAt_frag _)) .nil
  exact .ext _ _ (.mk _) fun b hb => by
    rw [List.mem_singleton.1 hb]
    exact .stmt _ _ inner .nil

theorem nestedDecl_ends (p : Roadmap.Pipeline) (n : Nat) (x : Locals E0.layout [] × St E0) :
    Ends ((execS (G0 p) F0 n 0 none nestedDecl .nil).run x).1 :=
  stmt_progress (c := F0.contract) (callsOKX_none _ _ _) (blockExt_sound _ _ _) F0 rfl n 0 none
    nestedDecl .nil nestedDecl_frag
    (by simp only [nestedDecl, pairDeclAt, RStmt.OpsOK, RItems.OpsOK, RExpr.OpsOK, RArgs.OpsOK, and_self])
    ⟨[], [], rfl, rfl⟩ x

end Solidity.Theory.Progress.Controls
