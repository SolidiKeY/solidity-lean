import Solidity.Theory.Progress.Program
import Solidity.Theory.Progress.Leaves
import Solidity.Source.SoundnessExamples

/-!
# Witnesses and negative controls for progress (S4.1, S4.2)

Over the toy environment of `Source/SemanticsExamples.lean` (`E0`, `G0`,
`F0`, `s0`):

* **Witnesses**: `(bool a, , bool b) = (true, false, true);` is in the
  extended fragment (`pairDeclAt_frag`), so `tuple_stmt_progress` applies
  (`pairDecl_ends`); its actual run pushes `true` and `true`
  (`pairDecl_run`) and at a short horizon runs out of fuel
  (`pairDecl_timeout`). A tuple declaration inside a `while` body and a
  block (`loopDecl_ends`, `loopDecl_timeout`) uses the structural cases.
  With the leaf extensions, a block declaring a tuple then running
  `assert(false)` ends (`blockDecl_ends`), by the panic `Panic(0x01)`
  (`blockDecl_run`, `blockDecl_panics`).
* **Negative controls**: the premises are needed. `return (1, 2);` is in
  the fragment and in the operations' domains (`retPair_unframed_in_frag`)
  but, without its return slots (no `BodyFrame`), stuck, so it does not
  end (`retPair_unframed_not_ends`); `Ends` refuses `stuck`
  (`stuck_not_ends`); an extension admitting a `_` outside a modifier is
  not sound (`all_unsound`), so `StmtExt.Sound` is a real obligation.
* **The extension shape with sub-blocks**: blocks admitted through the hook
  (`blockExt`, `blockExt_sound`), nested, around a tuple declaration
  (`nestedDecl_frag`, `nestedDecl_ends`).
* **Boundaries** (facts, not controls): `SlotsOK` refuses a declared
  reference-type slot `slotsFit` admits (`slotsOK_refuses_reference`); no
  locals hold a tuple (`no_tuple_local`); the elaboration of S01's
  `w_declTuple` is in the closure and ends (`elaborated_declTuple_frag`,
  `elaborated_declTuple_ends`).
-/

namespace Solidity.Theory.Progress.Controls

open Solidity.Source Solidity.Source.Progress Solidity.Source.SemanticsExamples Solidity.Theory.Progress EM

/-- `(bool a, , bool b) = (true, false, true);`, in any statement context. -/
def pairDeclAt (k : SCtx) : RStmt E0 [] false k [] [.bool, .bool] :=
  .declTuple [some .bool, none, some .bool] (.tuple (.cons (.bool true) (.cons (.bool false) (.cons (.bool true) .nil))))
    (by decide)

/-- The declaration in a function body. -/
abbrev pairDecl : RStmt E0 [] false .body [] [.bool, .bool] := pairDeclAt .body

/-- **Witness**: the declaration is in the extended fragment. -/
theorem pairDeclAt_frag (k : SCtx) : SFrag (StmtExt.none E0) (fun _ => False) (pairDeclAt k) :=
  .declTuple _ _ _
    (.lit _ (.cons (.checked _ trivial trivial) (.cons (.checked _ trivial trivial)
      (.cons (.checked _ trivial trivial) .nil))))
    ⟨rfl, .inl rfl, rfl, .inl rfl, trivial⟩

/-- The original value fragment refuses it: it has no tuple declarations. -/
theorem pairDecl_not_valFrag : ¬ RStmt.ValFragC (fun _ => False) pairDecl := fun h => h

/-- **Witness**: the declaration ends at every horizon, from every state. -/
theorem pairDecl_ends (p : Roadmap.Pipeline) (n : Nat) (x : Locals E0.layout [] × St E0) :
    Ends ((execS (G0 p) F0 n 0 none pairDecl .nil).run x).1 :=
  tuple_stmt_progress (G0 p) F0 n 0 none pairDecl .nil (pairDeclAt_frag _)
    (by simp only [pairDeclAt, RStmt.OpsOK, RExpr.OpsOK, RArgs.OpsOK, and_self]) ⟨[], [], rfl, rfl⟩ x

/-- **Witness**: the actual run pushes `a = true`, then `b = true`. -/
theorem pairDecl_run :
    ((execS (G0 .legacy) F0 10 0 none pairDecl .nil).run (.nil, s0)).1 =
      .ok (.normal (.cons (.bool true) (.cons (.bool true) .nil))) := by
  rfl

/-- **Witness**: at horizon 5 the tuple's components are not all evaluated
(each consumes fuel): out of fuel. -/
theorem pairDecl_timeout :
    ((execS (G0 .legacy) F0 5 0 none pairDecl .nil).run (.nil, s0)).1 = .error .timeout := by
  rfl

/-- `while (true) { (bool a, , bool b) = (true, false, true); }`: the
structural cases of the closure. -/
def loopDecl : RStmt E0 [] false .body [] [] :=
  .whileLoop (u := false) (.bool true) (.block (.stmt (pairDeclAt ⟨true, false⟩) .nil))

/-- **Witness**: the loop is in the extended fragment. -/
theorem loopDecl_frag : SFrag (StmtExt.none E0) (fun _ => False) loopDecl :=
  .whileLoop _ _ trivial (.block _ (.stmt _ _ (pairDeclAt_frag _) .nil))

/-- **Witness**: the loop never gets stuck; it runs out of fuel. -/
theorem loopDecl_ends (p : Roadmap.Pipeline) (n : Nat) (x : Locals E0.layout [] × St E0) :
    Ends ((execS (G0 p) F0 n 0 none loopDecl .nil).run x).1 :=
  tuple_stmt_progress (G0 p) F0 n 0 none loopDecl .nil loopDecl_frag
    (by simp only [loopDecl, pairDeclAt, RStmt.OpsOK, RItems.OpsOK, RExpr.OpsOK, RArgs.OpsOK, and_self])
    ⟨[], [], rfl, rfl⟩ x

/-- **Witness**: and it does run out of fuel. -/
theorem loopDecl_timeout :
    ((execS (G0 .legacy) F0 8 0 none loopDecl .nil).run (.nil, s0)).1 = .error .timeout := by
  rfl

/-! ## Negative controls -/

/-- **Negative control**: `Ends` refuses a stuck result. -/
theorem stuck_not_ends : ¬ Ends (.error (.stuck "no local") : Except Halt Unit) :=
  not_ends_stuck _

/-- `return (1, 2);` over no locals is in the fragment and in the
operations' domains: only its frame is missing. -/
theorem retPair_unframed_in_frag :
    SFrag (StmtExt.none E0) (fun _ => False) (SoundnessExamples.retPair (Γ := [])) ∧
      (SoundnessExamples.retPair (Γ := [])).OpsOK :=
  ⟨.base _ ⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩), trivial, rfl, .inr (.inl ⟨_, rfl⟩), trivial⟩,
    ⟨trivial, trivial, trivial⟩⟩

/-- **Negative control** (the `BodyFrame` premise): `return (1, 2);` over
locals without its return slots is stuck, so it does not end. -/
theorem retPair_unframed_not_ends :
    ¬ Ends ((execS (G0 .viaIR) F0 5 0 none (SoundnessExamples.retPair (Γ := [])) .nil).run
      (.nil, s0)).1 := by
  rw [SoundnessExamples.retPair_unframed_stuck]
  exact not_ends_stuck _

/-- Every statement, admitted. -/
def StmtExt.all (E : Env) : StmtExt E := ⟨fun _ _ => True⟩

/-- **Negative control** (the extension lemma is an obligation): admitting
every statement is not sound, since `_` outside a modifier is stuck. -/
theorem all_unsound : ¬ (StmtExt.all E0).Sound (G0 .legacy) (fun _ => False) (fun _ => True) := by
  intro hS
  have h := hS _ (fun _ _ h => h) 0 (stmtNSAtX_zero _ _ _ _)
    (fun m hm F _ => by rw [Nat.le_zero.1 hm]; exact exprNSAt_zero _ _ F) F0 trivial 0 none
    (RStmt.placeholder (R := []) (M := true) (k := .body) (Γ := []) rfl) [] .nil trivial (fun _ h => nomatch h)
    trivial ⟨[], [], rfl, rfl⟩
  exact h (.nil, s0)

/-- **Boundary** (`SlotsOK`): a declared `string memory` slot is refused,
though the typing rule's `slotsFit` admits it. -/
theorem slotsOK_refuses_reference :
    slotsFit E0.isBase E0.mapFree [some (.string .memory)] [.stringLit [97]] = true ∧
      ¬ SlotsOK [some (.string .memory)] [.stringLit [97]] :=
  ⟨by decide, fun h => nomatch h.1⟩

/-- **Boundary** (`Val.not_tuple`): no locals hold a tuple, so a tuple's
components never come from a plain value. -/
theorem no_tuple_local {D : Layout} {σs : List STy} {Γ : RCtx} (l : Locals D (.tuple σs :: Γ)) : False := by
  cases l with
  | cons v _ => exact Val.not_tuple v

/-! ## Leaf extensions: a builtin statement after a tuple declaration -/

/-- `assert(b);` over locals `Γ`. -/
def assertAt (Γ : RCtx) (b : Bool) : RStmt E0 [] false .body Γ Γ :=
  .expr (.builtin .assert (.cons (.bool b) .nil) rfl)

/-- `{ (bool a, , bool b) = (true, false, true); assert(false); }` -/
def blockDecl : RStmt E0 [] false .body [] [] :=
  .block (.stmt pairDecl (.stmt (assertAt _ false) .nil))

/-- **Witness**: the block is in the closure with the leaf extensions:
the tuple declaration by `declTuple`, the `assert` by `builtinExt`. -/
theorem blockDecl_frag : SFrag (leafExt (fun _ => False)) (fun _ => False) blockDecl :=
  .block _ (.stmt _ _ (SFrag.mono (X := StmtExt.none E0) (fun _ _ h => False.elim h) (pairDeclAt_frag _))
    (.stmt _ _ (.ext _ [] (Or.inr (Or.inr (.mk _ _ _ (.assert _ (.cons (.checked _ trivial trivial) .nil)))))
      (fun _ h => nomatch h)) .nil))

/-- **Witness**: the block ends, at every horizon, from every state. -/
theorem blockDecl_ends (p : Roadmap.Pipeline) (n : Nat) (x : Locals E0.layout [] × St E0) :
    Ends ((execS (G0 p) F0 n 0 none blockDecl .nil).run x).1 :=
  stmt_progress (c := F0.contract) (callsOKX_none _ _ _) (leafExt_sound_callFree _ _) F0 rfl n 0 none
    blockDecl .nil blockDecl_frag
    (by simp only [blockDecl, assertAt, pairDeclAt, RStmt.OpsOK, RItems.OpsOK, RExpr.OpsOK, RArgs.OpsOK, and_self])
    ⟨[], [], rfl, rfl⟩ x

/-- **Witness**: it ends by the panic `assert` raises (`Panic(0x01)`), the
`panics` case of `Ends`. -/
theorem blockDecl_run :
    ((execS (G0 .legacy) F0 12 0 none blockDecl .nil).run (.nil, s0)).1 = .error (.revert (panicData .assert)) := by
  rfl

/-- **Witness**: the block's ending is the `panics` case. -/
theorem blockDecl_panics : Ends ((execS (G0 .legacy) F0 12 0 none blockDecl .nil).run (.nil, s0)).1 := by
  rw [blockDecl_run]
  exact .panics .assert

/-! ## An elaborated tuple declaration -/

/-- **Witness** (an S01 derivation): the elaboration of
`(uint256 p, ) = (a, b);` (`TypingExamples.w_declTuple`) is in the closure. -/
theorem elaborated_declTuple_frag :
    SFrag (StmtExt.none _) (fun _ => False) TypingExamples.w_declTuple.toR :=
  StmtD.declTuple_frag _ _ _
    (.lit _ (.cons (.checked _ ⟨rfl, rfl, .inl rfl⟩ trivial) (.cons (.checked _ ⟨rfl, rfl, .inl rfl⟩ trivial) .nil)))
    ⟨rfl, .inl rfl, trivial⟩

/-- **Witness**: so it ends, in every program, at every horizon, from
every state, in its function's frame (`a`, `b`, `o` above the return slot
and the `bytes calldata` parameter). -/
theorem elaborated_declTuple_ends (G : Glob TypingExamples.Γ.env) (F : Fr) (n : Nat)
    (l : Locals TypingExamples.Γ.env.layout (tysOf TypingExamples.Γ.locals))
    (x : Locals TypingExamples.Γ.env.layout [] × St TypingExamples.Γ.env) :
    Ends ((execS G F n 1 none TypingExamples.w_declTuple.toR l).run x).1 :=
  tuple_stmt_progress G F n 1 none _ l elaborated_declTuple_frag (StmtD.toR_opsOK _)
    ⟨[.address false, .bool], [.bytes .calldata], rfl, rfl⟩ x

/-! ## The extension shape with sub-blocks -/

/-- A block as an extension node that hands its body to the closure: the
pattern a `try` (success and catch blocks) follows. -/
inductive BlockNode {E : Env} {R : List STy} {M : Bool} :
    {k : SCtx} → {Γ Γ' : RCtx} → RStmt E R M k Γ Γ' → List (Blk E R M) → Prop where
  | mk {k : SCtx} {Γ Γ₁ : RCtx} (b : RItems E R M k Γ Γ₁) : BlockNode (.block b) [⟨k, Γ, Γ₁, b⟩]

/-- Blocks through the extension hook. -/
def blockExt (E : Env) : StmtExt E := ⟨BlockNode⟩

/-- **Witness of the shape**: the extension is sound, its sub-block run by
the induction hypothesis over the enclosing closure. -/
theorem blockExt_sound {E : Env} (G : Glob E) (A : Decl → Prop) (Q : String → Prop) : (blockExt E).Sound G A Q := by
  intro Z _ n ih _ F hP nps ph R M k Γ Γ' s bs l hs hbs ho hfr
  cases hs with
  | mk b =>
    have hb : IFrag Z A b := hbs _ (List.mem_singleton_self _)
    simp only [execS]
    obtain ⟨ys, rfl⟩ := RItems.ext b
    exact NSP.bind (ih.execItems F hP nps ph b l hb ho hfr) fun o h =>
      NSP.weaken (Out.close_esc ys o) fun _ h' => ⟨fun h0 => h0.elim, fun hk => h'.trans (h hk)⟩

/-- `{ { (bool a, , bool b) = (true, false, true); } }` -/
def nestedDecl : RStmt E0 [] false .body [] [] :=
  .block (.stmt (.block (.stmt pairDecl .nil)) .nil)

/-- **Witness**: both blocks are judged by the extension, the tuple
declaration inside them by the closure (`declTuple`). -/
theorem nestedDecl_frag : SFrag (blockExt E0) (fun _ => False) nestedDecl := by
  have inner : SFrag (blockExt E0) (fun _ => False)
      (RStmt.block (R := []) (M := false) (k := .body) (RItems.stmt pairDecl .nil)) :=
    .ext _ _ (.mk _) fun b hb => by
      rw [List.mem_singleton.1 hb]
      exact .stmt _ _ (SFrag.mono (X := StmtExt.none E0) (fun _ _ h => False.elim h) (pairDeclAt_frag _)) .nil
  exact .ext _ _ (.mk _) fun b hb => by
    rw [List.mem_singleton.1 hb]
    exact .stmt _ _ inner .nil

/-- **Witness**: so the nested blocks end. -/
theorem nestedDecl_ends (p : Roadmap.Pipeline) (n : Nat) (x : Locals E0.layout [] × St E0) :
    Ends ((execS (G0 p) F0 n 0 none nestedDecl .nil).run x).1 :=
  stmt_progress (c := F0.contract) (callsOKX_none _ _ _) (blockExt_sound _ _ _) F0 rfl n 0 none
    nestedDecl .nil nestedDecl_frag
    (by simp only [nestedDecl, pairDeclAt, RStmt.OpsOK, RItems.OpsOK, RExpr.OpsOK, RArgs.OpsOK, and_self])
    ⟨[], [], rfl, rfl⟩ x

end Solidity.Theory.Progress.Controls
