import Solidity.Syntax.Elab.CallOutput

/-!
# Callback agreement for the elaborator's helpers

The totalization of the knot of `Syntax/Elab/Stmt.lean` by a well-founded cut
needs, for every arm, that the arm's result at an input and a scope does not
change when its recursive callbacks are replaced by callbacks that agree with
them at the arguments and scopes the arm invokes them at.  This module states
that property at run level, scope by scope (`Agree`), with the arguments an
invocation may take described by the successful outputs of the computations
before it (`Out`), and proves it for the helpers below `Syntax/Elab/Stmt.lean`
that take a callback: `elabStmtsPWith`, `hoistArgsWith`, `hoistPairWith`,
`hoistBinopWith`, `eagerArgsWith`, `hoistCallArgsWith` and `inlinedBody`.
No measure is fixed here: each lemma names the invocations themselves.
-/

namespace Solidity.ElabAgree

open Solidity Semantics

/-- `a` is a successful output of `x` at the scope `sc`, from some state. -/
def Out {α : Type} (sc : ElabScope) (x : ElabM α) (a : α) : Prop :=
  ∃ st m st' m', x sc st m = .ok ((a, st'), m')

/-- `x` and `y` run alike at the scope `sc`, from every state. -/
def Agree {α : Type} (sc : ElabScope) (x y : ElabM α) : Prop :=
  ∀ st m, x sc st m = y sc st m

theorem agree_refl {α : Type} (sc : ElabScope) (x : ElabM α) : Agree sc x x :=
  fun _ _ => rfl

theorem Agree.symm {α : Type} {sc : ElabScope} {x y : ElabM α} (h : Agree sc x y) :
    Agree sc y x := fun st m => (h st m).symm

theorem Agree.trans {α : Type} {sc : ElabScope} {x y z : ElabM α} (h : Agree sc x y)
    (k : Agree sc y z) : Agree sc x z := fun st m => (h st m).trans (k st m)

/-- Agreement at every scope is equality. -/
theorem eq_of_agree {α : Type} {x y : ElabM α} (h : ∀ sc, Agree sc x y) : x = y := by
  funext sc st m
  exact h sc st m

/-- Outputs transfer along agreement. -/
theorem Out.of_agree {α : Type} {sc : ElabScope} {x y : ElabM α} {a : α}
    (h : Agree sc x y) (ha : Out sc x a) : Out sc y a := by
  obtain ⟨st, m, st', m', hr⟩ := ha
  exact ⟨st, m, st', m', (h st m).symm.trans hr⟩

/-- A bind's stages agree: the first, then the continuations at each of its
successful outputs. -/
theorem agree_bind {α β : Type} {sc : ElabScope} {x y : ElabM α} {f g : α → ElabM β}
    (hx : Agree sc x y) (hf : ∀ a, Out sc x a → Agree sc (f a) (g a)) :
    Agree sc (x >>= f) (y >>= g) := by
  intro st m
  change (do let ((a, s), n) ← x sc st m; f a sc s n) =
    (do let ((a, s), n) ← y sc st m; g a sc s n)
  rw [← hx st m]
  cases he : x sc st m with
  | error err => rfl
  | ok v =>
    rcases v with ⟨⟨a, s⟩, n⟩
    exact hf a ⟨st, m, s, n, he⟩ s n

/-- A changed scope: agreement there. -/
theorem agree_withReader {α : Type} {sc : ElabScope} {x y : ElabM α}
    (f : ElabScope → ElabScope) (h : Agree (f sc) x y) :
    Agree sc (withReader f x) (withReader f y) :=
  fun st m => h st m

/-- A list loop whose bodies agree at the list's elements. -/
theorem agree_forIn {α β : Type} {sc : ElabScope} (xs : List α) (init : β)
    (f g : α → β → ElabM (ForInStep β))
    (h : ∀ a ∈ xs, ∀ b, Agree sc (f a b) (g a b)) :
    Agree sc (forIn xs init f) (forIn xs init g) := by
  induction xs generalizing init with
  | nil => exact agree_refl _ _
  | cons a as ih =>
    simp only [List.forIn_cons]
    apply agree_bind (h a (by simp) init)
    intro r _
    cases r with
    | done b => exact agree_refl _ _
    | yield b => exact ih b fun x hx => h x (by simp [hx])

/-- A conditional whose branches agree. -/
theorem agree_ite {α : Type} {sc : ElabScope} {c : Prop} [Decidable c] {x y x' y' : ElabM α}
    (ht : c → Agree sc x x') (he : ¬c → Agree sc y y') :
    Agree sc (if c then x else y) (if c then x' else y') := by
  split
  · exact ht ‹_›
  · exact he ‹_›

/-- One step of an agreement proof over two computations of the same shape. -/
macro "agree_step" : tactic => `(tactic| first
  | (with_reducible exact agree_refl _ _)
  | (with_reducible assumption)
  | (with_reducible apply agree_withReader)
  | (with_reducible refine agree_ite (fun _ => ?_) (fun _ => ?_))
  | (with_reducible refine agree_bind ?_ (fun _ _ => ?_))
  | (dsimp only)
  | split)

variable (C : Contract) [FreshNames]

omit [FreshNames] in
/-- A block invokes its statement callback at its own statements. -/
theorem elabStmtsPWith_agree (stmt stmt' : RawStmt → ElabM (SProg C)) (sc : ElabScope)
    (ss : List RawStmt) (h : ∀ s ∈ ss, Agree sc (stmt s) (stmt' s)) :
    Agree sc (elabStmtsPWith C stmt ss) (elabStmtsPWith C stmt' ss) := by
  induction ss with
  | nil => exact agree_refl _ _
  | cons s ss ih =>
    simp only [elabStmtsPWith]
    apply agree_bind (h s (by simp))
    intro P _
    apply agree_bind (ih fun t ht => h t (by simp [ht]))
    intro Q _
    exact agree_refl _ _

/-- Argument hoisting invokes its callback at the list's members. -/
theorem hoistArgsWith_agree (H K : RawExpr → ElabM (SProg C × RawExpr)) (sc : ElabScope)
    (xs : List RawExpr) (h : ∀ a ∈ xs, Agree sc (H a) (K a)) :
    Agree sc (hoistArgsWith C H xs) (hoistArgsWith C K xs) := by
  induction xs with
  | nil => exact agree_refl _ _
  | cons a as ih =>
    have ha := h a (by simp)
    have has := ih fun x hx => h x (by simp [hx])
    simp only [hoistArgsWith]
    repeat' agree_step

/-- A pair's hoisting invokes its callback at the two operands. -/
theorem hoistPairWith_agree (H K : RawExpr → ElabM (SProg C × RawExpr)) (sc : ElabScope)
    (a b : RawExpr) (ha : Agree sc (H a) (K a)) (hb : Agree sc (H b) (K b)) :
    Agree sc (hoistPairWith C H a b) (hoistPairWith C K a b) := by
  unfold hoistPairWith
  repeat' agree_step

/-- A binary operator's hoisting invokes its callback at the two operands. -/
theorem hoistBinopWith_agree (H K : RawExpr → ElabM (SProg C × RawExpr)) (sc : ElabScope)
    (op : BinOp) (a b : RawExpr) (ha : Agree sc (H a) (K a)) (hb : Agree sc (H b) (K b)) :
    Agree sc (hoistBinopWith C H op a b) (hoistBinopWith C K op a b) := by
  have hab := hoistPairWith_agree C H K sc a b ha hb
  have hba := hoistPairWith_agree C H K sc b a hb ha
  unfold hoistBinopWith
  repeat' agree_step

/-- Eager argument evaluation invokes its callback at the list's members. -/
theorem eagerArgsWith_agree (H K : RawExpr → ElabM (SProg C × RawExpr)) (sc : ElabScope)
    (args : List RawExpr) (discard : Bool) (expected : List (Option PrimTy))
    (h : ∀ a ∈ args, Agree sc (H a) (K a)) :
    Agree sc (eagerArgsWith C H args discard expected)
      (eagerArgsWith C K args discard expected) := by
  unfold eagerArgsWith
  apply agree_bind
  · apply agree_forIn
    rintro ⟨a, i⟩ hm b
    have ha : Agree sc (H a) (K a) := h a (by
      have hz := List.of_mem_zip (l₁ := args) (l₂ := List.range' 0 args.length)
        (by simpa [List.zipIdx_eq_zip_range'] using hm)
      exact hz.1)
    repeat' agree_step
  · intro _ _
    exact agree_refl _ _

/-- Call-argument preparation invokes its expression callback at the
arguments and its statement callback at the late copies it declares. -/
theorem hoistCallArgsWith_agree (H K : RawExpr → ElabM (SProg C × RawExpr))
    (stmt stmt' : RawStmt → ElabM (SProg C)) (sc : ElabScope) (f : String)
    (args : List RawExpr) (h : ∀ a ∈ args, Agree sc (H a) (K a))
    (hs : ∀ T y x, Agree sc (stmt (.declMemory T y (some (.name x))))
      (stmt' (.declMemory T y (some (.name x))))) :
    Agree sc (hoistCallArgsWith C H stmt f args) (hoistCallArgsWith C K stmt' f args) := by
  have hargs := hoistArgsWith_agree C H K sc args h
  unfold hoistCallArgsWith
  repeat' first
    | (exact h _ (List.of_mem_zip ‹_›).2)
    | (with_reducible apply agree_forIn; intro _ _ _)
    | (with_reducible apply elabStmtsPWith_agree; intro s hm;
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; subst hm; exact hs _ _ _)
    | agree_step

/-- An inlined body invokes the block callback at the callee's prepared body,
in the callee's scope. -/
theorem inlinedBody_agree (rc rc' : ElabRec C) (sc : ElabScope) (f : String) (d : FunDecl)
    (ρ : List (String × String)) (shared ctor selfFrame : Bool)
    (scope : List (Name × FunDecl)) (k₀ : Nat) (Γ Γf : ECtx)
    (h : ∀ body k₁, Out sc (calleeBody C d ρ ctor selfFrame Γf) body →
      Agree { sc with funs := scope, top := false, selfFrame := selfFrame, unchecked := false,
                      inlined := (k₀, k₁) :: sc.inlined }
        (rc.elabStmtsP body) (rc'.elabStmtsP body)) :
    Agree sc (inlinedBody C rc f d ρ shared ctor selfFrame scope k₀ Γ Γf)
      (inlinedBody C rc' f d ρ shared ctor selfFrame scope k₀ Γ Γf) := by
  unfold inlinedBody
  repeat' first
    | (exact h _ _ ‹_›)
    | agree_step

end Solidity.ElabAgree
