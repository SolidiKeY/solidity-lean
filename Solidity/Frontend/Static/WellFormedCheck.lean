import Solidity.Source.WellFormed
import Solidity.Frontend.Static.InferStmtComplete
import Solidity.Frontend.Static.Units

/-!
# Deciding S01's well-formedness (G13)

`wellFormedB r` checks every field of S01's `WellFormed`
(`Solidity/Source/WellFormed.lean`): bases and linearization, clashes,
pragmas, declared types, placement, constant initializers (typed by `infer`)
and every body (typed by `inferS`).  `wellFormed_iff` proves it decides
`WellFormed` exactly; `inProfileSyntaxB_iff` does the same for S00's
syntax verdict.  Together they are the per-unit metadata stage of G05
(`Solidity/Frontend/Static/Certificates.lean`).
-/

namespace Solidity.Frontend.Static

open Solidity.Source

/-- Pairwise, decided. -/
def pairwiseB {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => true
  | a :: l => l.all (p a) && pairwiseB p l

theorem pairwiseB_iff {α : Type} (p : α → α → Bool) :
    ∀ l : List α, pairwiseB p l = true ↔ l.Pairwise fun a b => p a b = true
  | [] => by simp only [pairwiseB, List.Pairwise.nil]
  | a :: l => by
    simp only [pairwiseB, Bool.and_eq_true, List.all_eq_true, List.pairwise_cons, pairwiseB_iff p l]

/-- The initializer check: some type `infer` finds converts to the declared
type. -/
def initOK (E : Env) (d : Decl) : Bool :=
  match d.init? with
  | Option.none => true
  | Option.some e =>
    match d.varTy E with
    | Option.some τ => (inferTys (Ctx.forInit E d.scope) e).any (·.implicit (Ctx.forInit E d.scope).isBase τ)
    | Option.none => false

/-- The body check: the frame elaborates, its names are distinct, and its
statements are typed (some derivation found by `inferS`). -/
def bodyOK (E : Env) (d : Decl) : Bool :=
  !d.hasBody ||
    match d.frame? E with
    | Option.some f => nodupB ((f.names ++ f.rnames).filterMap id) &&
        !(itemsLocals (f.ctx E d.scope) f.body f.locals).isEmpty
    | Option.none => false

/-- **The well-formedness check.** -/
def wellFormedB (r : Resolution) : Bool :=
  r.env.basesOK &&
  r.unit.decls.all (fun d => !(d.kind == .contract || d.kind == .interface) ||
    (r.env.linearize d.name).isSome) &&
  pairwiseB (fun d d' => !d.clash r.env d') r.unit.decls &&
  r.unit.pragmas.all knownPragma &&
  decide (r.unit.abicoderPragmas ≤ 1) &&
  r.unit.decls.all (·.typesOK r.env) &&
  r.unit.decls.all (·.placementOK r.env) &&
  r.unit.decls.all (fun d => !d.isConst || d.init?.isSome) &&
  r.unit.decls.all (initOK r.env) &&
  r.unit.decls.all (bodyOK r.env)

theorem initOK_iff {E : Env} {d : Decl} : initOK E d = true ↔ ∀ e, d.init? = Option.some e →
    ∃ τ σ, d.varTy E = Option.some τ ∧ HasType (Ctx.forInit E d.scope) e σ ∧
      σ.implicit (Ctx.forInit E d.scope).isBase τ = true := by
  unfold initOK
  cases hi : d.init? with
  | none => simp only [true_iff]; intro e h; cases h
  | some e =>
    simp only [Option.some.injEq, forall_eq']
    cases hv : d.varTy E with
    | none => simp only [Bool.false_eq_true, reduceCtorEq, false_and, exists_false]
    | some τ =>
      simp only [List.any_eq_true, Option.some.injEq, exists_and_left, exists_eq_left']
      constructor
      · intro ⟨σ, hm, hc⟩
        obtain ⟨d', _⟩ := exists_expr hm
        exact ⟨σ, ⟨d'⟩, hc⟩
      · intro ⟨σ, ⟨d'⟩, hc⟩
        exact ⟨σ, typed_complete d', hc⟩

theorem bodyOK_iff {E : Env} {d : Decl} : bodyOK E d = true ↔ (d.hasBody = true →
    ∃ f L', d.frame? E = Option.some f ∧ f.distinct ∧ ItemsOK (f.ctx E d.scope) f.locals f.body L') := by
  unfold bodyOK
  cases hb : d.hasBody with
  | false => simp only [Bool.not_false, Bool.true_or, Bool.false_eq_true, false_implies]
  | true =>
    simp only [Bool.not_true, Bool.false_or, forall_const]
    cases hf : d.frame? E with
    | none => simp only [Bool.false_eq_true, reduceCtorEq, false_and, exists_false]
    | some f =>
      simp only [Bool.and_eq_true, nodupB_iff, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem,
        Option.some.injEq, exists_and_left, exists_eq_left']
      constructor
      · intro ⟨hn, L', hL⟩
        exact ⟨hn, L', itemsOK_iff.mpr hL⟩
      · intro ⟨hn, L', hL⟩
        exact ⟨hn, L', itemsOK_iff.mp hL⟩

/-- **The check decides S01's well-formedness.** -/
theorem wellFormed_iff {r : Resolution} : wellFormedB r = true ↔ WellFormed r := by
  simp only [wellFormedB, Bool.and_eq_true, List.all_eq_true, pairwiseB_iff, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro ⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hl⟩, hc⟩, hp⟩, ho⟩, ht⟩, hpl⟩, hci⟩, hi⟩, hbo⟩
    refine ⟨hb, ?_, ?_, hp, ho, ht, hpl, ?_, ?_, ?_⟩
    · intro d hd hk
      rcases hl d hd with h | h
      · rcases hk with e | e <;> simp only [e, beq_self_eq_true, Bool.true_or, Bool.or_true,
          reduceCtorEq] at h
      · exact h
    · exact List.Pairwise.imp (fun h => by simpa only [Bool.not_eq_true'] using h) hc
    · intro d hd hcst
      rcases hci d hd with h | h
      · rw [hcst] at h; cases h
      · exact h
    · intro d hd e he
      exact initOK_iff.mp (hi d hd) e he
    · intro d hd hbd
      exact bodyOK_iff.mp (hbo d hd) hbd
  · intro w
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨w.bases, ?_⟩, ?_⟩, w.pragmas⟩, w.oneCoder⟩, w.types⟩, w.placement⟩, ?_⟩, ?_⟩, ?_⟩
    · intro d hd
      by_cases hk : (d.kind == .contract || d.kind == .interface) = true
      · right
        apply w.linearizes d hd
        simp only [Bool.or_eq_true, beq_iff_eq] at hk
        exact hk
      · left
        simpa only [Bool.not_eq_true] using hk
    · exact List.Pairwise.imp (fun h => by simpa only [Bool.not_eq_true'] using h) w.noClash
    · intro d hd
      cases hcst : d.isConst with
      | false => exact .inl rfl
      | true => exact .inr (w.constInit d hd hcst)
    · intro d hd
      exact initOK_iff.mpr (w.inits d hd)
    · intro d hd
      exact bodyOK_iff.mpr (w.bodies d hd)

/-- S00's syntax verdict, decided. -/
def inProfileSyntaxB (r : Resolution) : Bool := r.unit.rejections.isEmpty

theorem inProfileSyntaxB_iff {r : Resolution} : inProfileSyntaxB r = true ↔ InProfileSyntax r := by
  simp only [inProfileSyntaxB, List.isEmpty_iff, InProfileSyntax]

end Solidity.Frontend.Static
