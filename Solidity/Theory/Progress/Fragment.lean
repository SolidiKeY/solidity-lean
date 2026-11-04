import Solidity.Theory.Progress.Tuple
import Solidity.Theory.Progress.Outcome

/-!
# The extensible progress fragment (S4.1, S4.2)

`Solidity/Source/StmtProgress.lean` proves that the statement value
fragment (`RStmt.ValFragC`) with internal calls is never `stuck`
(`fragAt`). Its fragment is a recursive predicate with no room for new
node kinds. This module closes a larger fragment under the same structure,
and leaves a hook for node kinds later lanes add:

* `SFrag X A s` / `IFrag X A b`: a statement (block) whose every node is
  of the existing fragment (`base`), a **tuple declaration**
  (`declTuple`, `Theory/Progress/Tuple.lean`), a node admitted by an
  extension `X` (`ext`), or a block, `if`, loop or `for` built from such
  statements and fragment expressions.
* `StmtExt.Sound X G A Q`: **the extension lemma shape**. An extension
  supplies, for its node predicate `X.P`, the one-node step: given the
  induction hypothesis at horizon `n` (`StmtNSAtX`, which covers every
  sub-statement of the closure) and expression progress at every horizon
  up to `n`, a node `X.P` admits is never `stuck` at `n + 1`, completes
  normally when it is a simple statement, and lets no `break`/`continue`
  escape outside a loop. A construct lane X adds proves exactly this and
  gets progress inside every block, loop and called body for free
  (`fragXAt`). `StmtExt.none` (no extra nodes) is sound, and two sound
  extensions combine (`StmtExt.or`, `StmtExt.Sound.or`).
* `CallsOKX`: the program premise, `CallsOK` with bodies in `IFrag`; every
  program `CallsOK` admits is admitted (`CallsOK.toX`), so the checked
  elaborated programs of `Source/Progress/CheckedPrograms.lean` carry over.

The structural cases repeat `execS_nsStep`'s proof over the larger
predicate; a `base` node is discharged by `execS_nsStep` itself, through
`StmtNSAtX.toBase`.
-/

namespace Solidity.Theory.Progress

open Solidity.Source Solidity.Source.Progress EM

variable {E : Env}

/-- **A statement extension**: the node kinds a later lane admits. -/
structure StmtExt (E : Env) where
  P : ∀ {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}, RStmt E R M k Γ Γ' → Prop

/-- No extra nodes. -/
def StmtExt.none (E : Env) : StmtExt E := ⟨fun _ => False⟩

/-- The nodes either extension admits. -/
def StmtExt.or (X Y : StmtExt E) : StmtExt E := ⟨fun s => X.P s ∨ Y.P s⟩

mutual

/-- **The extended statement fragment.** -/
inductive SFrag (X : StmtExt E) (A : Decl → Prop) {R : List STy} {M : Bool} :
    {k : SCtx} → {Γ Γ' : RCtx} → RStmt E R M k Γ Γ' → Prop where
  | base {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') : RStmt.ValFragC A s → SFrag X A s
  | ext {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') : X.P s → SFrag X A s
  | declTuple {k : SCtx} {Γ : RCtx} {σs : List STy} (slots : List (Option STy)) (e : RExpr E Γ (.tuple σs))
      (h : slotsFit E.isBase slots σs = true) : TupleInit A e → SlotsOK slots σs →
      SFrag X A (RStmt.declTuple (R := R) (M := M) (k := k) slots e h)
  | block {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') : IFrag X A b → SFrag X A (.block b)
  | ifThen {k : SCtx} {Γ Γ₁ : RCtx} (c : RExpr E Γ .bool) (s : RStmt E R M k Γ Γ₁) :
      RExpr.ValFragC A c → SFrag X A s → SFrag X A (.ifThen c s)
  | ifElse {k : SCtx} {Γ Γ₁ Γ₂ : RCtx} (c : RExpr E Γ .bool) (s : RStmt E R M k Γ Γ₁) (t : RStmt E R M k Γ Γ₂) :
      RExpr.ValFragC A c → SFrag X A s → SFrag X A t → SFrag X A (.ifElse c s t)
  | whileLoop {l u : Bool} {Γ Γ₁ : RCtx} (c : RExpr E Γ .bool) (s : RStmt E R M ⟨true, u⟩ Γ Γ₁) :
      RExpr.ValFragC A c → SFrag X A s → SFrag X A (RStmt.whileLoop (l := l) c s)
  | doWhile {l u : Bool} {Γ Γ₁ : RCtx} (s : RStmt E R M ⟨true, u⟩ Γ Γ₁) (c : RExpr E Γ .bool) :
      SFrag X A s → RExpr.ValFragC A c → SFrag X A (RStmt.doWhile (l := l) s c)
  | forLoop {l u : Bool} {Γ Γ₁ Γ₂ : RCtx} (i : RStmt E R M ⟨true, u⟩ Γ Γ₁) (c : ROptBool E Γ₁)
      (p : ROptExpr E Γ₁) (s : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) :
      i.Simple → SFrag X A i → ROptBool.ValFragC A c → ROptExpr.ValFragC A p → SFrag X A s →
      SFrag X A (RStmt.forLoop (l := l) i c p s)

/-- **The extended block fragment.** -/
inductive IFrag (X : StmtExt E) (A : Decl → Prop) {R : List STy} {M : Bool} :
    {k : SCtx} → {Γ Γ' : RCtx} → RItems E R M k Γ Γ' → Prop where
  | base {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') : RItems.ValFragC A b → IFrag X A b
  | nil {k : SCtx} {Γ : RCtx} : IFrag X A (RItems.nil (k := k) (Γ := Γ))
  | stmt {k : SCtx} {Γ Γ₁ Γ₂ : RCtx} (s : RStmt E R M k Γ Γ₁) (rest : RItems E R M k Γ₁ Γ₂) :
      SFrag X A s → IFrag X A rest → IFrag X A (.stmt s rest)
  | unchecked {l : Bool} {Γ Γ₁ Γ₂ : RCtx} (b : RItems E R M ⟨l, true⟩ Γ Γ₁) (rest : RItems E R M ⟨l, false⟩ Γ Γ₂) :
      IFrag X A b → IFrag X A rest → IFrag X A (.unchecked b rest)

end

section
variable (G : Glob E)

/-- **The induction hypothesis** at horizon `n`, over the extended
fragment; the postconditions are `StmtNSAt`'s. -/
structure StmtNSAtX (X : StmtExt E) (A : Decl → Prop) (Q : String → Prop) (n : Nat) : Prop where
  execS : ∀ (F : Fr), Q F.contract → ∀ (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ), SFrag X A s → s.OpsOK → BodyFrame nps R Γ →
    NSP (execS G F n nps ph s l) (fun o => (s.Simple → ∃ l', o = .normal l') ∧ (k.loop = false → o.esc = false))
  execItems : ∀ (F : Fr), Q F.contract → ∀ (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ), IFrag X A b → b.OpsOK → BodyFrame nps R Γ →
    NSP (execItems G F n nps ph b l) (fun o => k.loop = false → o.esc = false)
  forIter : ∀ (F : Fr), Q F.contract → ∀ (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool} {Γ₁ Γ₂ : RCtx}
    (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁),
    ROptBool.ValFragC A c → c.OpsOK → ROptExpr.ValFragC A post → post.OpsOK → SFrag X A body →
      body.OpsOK → BodyFrame nps R Γ₁ →
    NSP (forIter G F n nps ph c post body l) (fun o => (∃ l', o = .normal l') ∨ (∃ l', o = .ret l'))

/-- The hypothesis over the extended fragment gives the original one. -/
theorem StmtNSAtX.toBase {X : StmtExt E} {A : Decl → Prop} {Q : String → Prop} {n : Nat}
    (ih : StmtNSAtX G X A Q n) : StmtNSAt G A Q n where
  execS F hP nps ph _ _ _ _ _ s l hf ho hfr := ih.execS F hP nps ph s l (.base s hf) ho hfr
  execItems F hP nps ph _ _ _ _ _ b l hf ho hfr := ih.execItems F hP nps ph b l (.base b hf) ho hfr
  forIter F hP nps ph _ _ _ _ _ c post body l hc hc' hp hp' hb hb' hfr :=
    ih.forIter F hP nps ph c post body l hc hc' hp hp' (.base body hb) hb' hfr

theorem stmtNSAtX_zero (X : StmtExt E) (A : Decl → Prop) (Q : String → Prop) : StmtNSAtX G X A Q 0 where
  execS _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by rw [execS.eq_1]; exact NSP.halt' trivial
  execItems _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by rw [execItems.eq_1]; exact NSP.halt' trivial
  forIter _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by rw [forIter.eq_1]; exact NSP.halt' trivial

end

/-- **The extension lemma shape**: the one-node step an extension proves.
From the induction hypothesis at `n` and expression progress at every
horizon up to `n`, a node `X` admits is never `stuck` at `n + 1`, with the
statement postcondition. -/
def StmtExt.Sound (X : StmtExt E) (G : Glob E) (A : Decl → Prop) (Q : String → Prop) : Prop :=
  ∀ n, StmtNSAtX G X A Q n → (∀ m, m ≤ n → ∀ F, Q F.contract → ExprNSAt A G F m) →
    ∀ (F : Fr), Q F.contract → ∀ (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx}
      {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ), X.P s → s.OpsOK → BodyFrame nps R Γ →
      NSP (execS G F (n + 1) nps ph s l)
        (fun o => (s.Simple → ∃ l', o = .normal l') ∧ (k.loop = false → o.esc = false))

/-- No extra nodes: nothing to prove. -/
theorem StmtExt.none_sound (G : Glob E) (A : Decl → Prop) (Q : String → Prop) : (StmtExt.none E).Sound G A Q :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ => h.elim

mutual

/-- The closure only grows with the extension. -/
theorem SFrag.mono {X Y : StmtExt E} {A : Decl → Prop} (hXY : ∀ {R M k Γ Γ'} (s : RStmt E R M k Γ Γ'), X.P s → Y.P s) :
    ∀ {R M k Γ Γ'} {s : RStmt E R M k Γ Γ'}, SFrag X A s → SFrag Y A s
  | _, _, _, _, _, _, .base s h => .base s h
  | _, _, _, _, _, _, .ext s h => .ext s (hXY s h)
  | _, _, _, _, _, _, .declTuple slots e h hi hs => .declTuple slots e h hi hs
  | _, _, _, _, _, _, .block b hb => .block b (IFrag.mono hXY hb)
  | _, _, _, _, _, _, .ifThen c s hc hs => .ifThen c s hc (SFrag.mono hXY hs)
  | _, _, _, _, _, _, .ifElse c s t hc hs ht => .ifElse c s t hc (SFrag.mono hXY hs) (SFrag.mono hXY ht)
  | _, _, _, _, _, _, .whileLoop c s hc hs => .whileLoop c s hc (SFrag.mono hXY hs)
  | _, _, _, _, _, _, .doWhile s c hs hc => .doWhile s c (SFrag.mono hXY hs) hc
  | _, _, _, _, _, _, .forLoop i c p s hi hi' hc hp hs =>
    .forLoop i c p s hi (SFrag.mono hXY hi') hc hp (SFrag.mono hXY hs)

theorem IFrag.mono {X Y : StmtExt E} {A : Decl → Prop} (hXY : ∀ {R M k Γ Γ'} (s : RStmt E R M k Γ Γ'), X.P s → Y.P s) :
    ∀ {R M k Γ Γ'} {b : RItems E R M k Γ Γ'}, IFrag X A b → IFrag Y A b
  | _, _, _, _, _, _, .base b h => .base b h
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .stmt s rest hs hr => .stmt s rest (SFrag.mono hXY hs) (IFrag.mono hXY hr)
  | _, _, _, _, _, _, .unchecked b rest hb hr => .unchecked b rest (IFrag.mono hXY hb) (IFrag.mono hXY hr)

end

/-- The hypothesis for a larger extension gives it for a smaller one. -/
theorem StmtNSAtX.restrict {G : Glob E} {X Y : StmtExt E} {A : Decl → Prop} {Q : String → Prop} {n : Nat}
    (hXY : ∀ {R M k Γ Γ'} (s : RStmt E R M k Γ Γ'), X.P s → Y.P s) (ih : StmtNSAtX G Y A Q n) :
    StmtNSAtX G X A Q n where
  execS F hP nps ph _ _ _ _ _ s l hf ho hfr := ih.execS F hP nps ph s l (SFrag.mono hXY hf) ho hfr
  execItems F hP nps ph _ _ _ _ _ b l hf ho hfr := ih.execItems F hP nps ph b l (IFrag.mono hXY hf) ho hfr
  forIter F hP nps ph _ _ _ _ _ c post body l hc hc' hp hp' hb hb' hfr :=
    ih.forIter F hP nps ph c post body l hc hc' hp hp' (SFrag.mono hXY hb) hb' hfr

/-- **Sound extensions combine**: the cases two lanes add separately are
sound together. -/
theorem StmtExt.Sound.or {G : Glob E} {X Y : StmtExt E} {A : Decl → Prop} {Q : String → Prop}
    (hX : X.Sound G A Q) (hY : Y.Sound G A Q) : (X.or Y).Sound G A Q := by
  intro n ih hE F hP nps ph R M k Γ Γ' s l hs ho hfr
  rcases hs with hs | hs
  · exact hX n (ih.restrict (fun _ h => Or.inl h)) hE F hP nps ph s l hs ho hfr
  · exact hY n (ih.restrict (fun _ h => Or.inr h)) hE F hP nps ph s l hs ho hfr

/-! ## The step -/

section
variable {X : StmtExt E} {A : Decl → Prop} {Q : String → Prop} {G : Glob E} {n : Nat}

theorem execSX_step (ih : StmtNSAtX G X A Q n) (hX : ∀ m, m ≤ n → ∀ F, Q F.contract → ExprNSAt A G F m)
    (hS : X.Sound G A Q) (F : Fr) (hP : Q F.contract) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) (hf : SFrag X A s) (ho : s.OpsOK)
    (hfr : BodyFrame nps R Γ) :
    NSP (execS G F (n + 1) nps ph s l) (fun o => (s.Simple → ∃ l', o = .normal l') ∧ (k.loop = false → o.esc = false)) := by
  have hXn : ∀ F, Q F.contract → ExprNSAt A G F n := hX n (Nat.le_refl n)
  have hsub : ∀ {Γ₀ τ} {l₀ : Locals E.layout Γ₀} (e : RExpr E Γ₀ τ), RExpr.ValFragC A e → e.OpsOK →
      NSP (sub (Γ := []) l₀ (evalE G F n e)) (fun _ => True) :=
    fun e hf ho => NSP.sub' (NSP.weaken (NSP.of_ns ((hXn F hP).val e hf ho)) fun _ _ _ => trivial)
  have hclose : ∀ {Γ₁} {t : RStmt E R M k Γ Γ₁} (l₁ : Locals E.layout Γ), SFrag X A t → t.OpsOK →
      NSP (do lift (← execS G F n nps ph t l₁).close)
        (fun (o : Source.Out E.layout Γ Γ) => k.loop = false → o.esc = false) := by
    intro Γ₁ t l₁ ht ho'
    obtain ⟨ys, rfl⟩ := RStmt.ext t
    exact NSP.bind (ih.execS F hP nps ph t l₁ ht ho' hfr) fun o h =>
      NSP.weaken (Out.close_esc ys o) fun _ h' hk => h'.trans (h.2 hk)
  have hf0 := hf
  cases hf with
  | base s h => exact execS_nsStep ih.toBase hXn F hP nps ph s l h ho hfr
  | ext s h => exact hS n ih hX F hP nps ph s l h ho hfr
  | declTuple slots e h hi hs =>
    exact NSP.weaken (declTuple_ns G F n (fun m hm => hX m hm F hP) nps ph slots e h l hi hs)
      fun o ⟨l', hl'⟩ => ⟨fun _ => ⟨l', hl'⟩, fun _ => by rw [hl']; rfl⟩
  | block b hb =>
    simp only [execS]
    obtain ⟨ys, rfl⟩ := RItems.ext b
    exact NSP.bind (ih.execItems F hP nps ph b l hb ho hfr) fun o h =>
      NSP.weaken (Out.close_esc ys o) fun _ h' => ⟨fun h0 => h0.elim, fun hk => h'.trans (h hk)⟩
  | ifThen c t hc ht =>
    simp only [execS]
    refine NSP.bind (hsub c hc ho.1) fun p _ => NSP.bind (NSP.of_ns (getV_ns rfl p.1)) fun x _ => ?_
    split
    · exact NSP.weaken (hclose p.2 ht ho.2) fun _ h => ⟨fun h0 => h0.elim, h⟩
    · exact NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
  | ifElse c t f hc ht hf' =>
    simp only [execS]
    refine NSP.bind (hsub c hc ho.1) fun p _ => NSP.bind (NSP.of_ns (getV_ns rfl p.1)) fun x _ => ?_
    split
    · exact NSP.weaken (hclose p.2 ht ho.2.1) fun _ h => ⟨fun h0 => h0.elim, h⟩
    · exact NSP.weaken (hclose p.2 hf' ho.2.2) fun _ h => ⟨fun h0 => h0.elim, h⟩
  | whileLoop c body hc hb =>
    have hf := hf0
    simp only [execS]
    obtain ⟨ys, rfl⟩ := RStmt.ext body
    refine NSP.bind (hsub c hc ho.1) fun p _ => NSP.bind (NSP.of_ns (getV_ns rfl p.1)) fun x _ => ?_
    split
    · refine NSP.bind (ih.execS F hP nps ph body p.2 hb ho.2 hfr) fun o _ => ?_
      cases o with
      | normal l2 =>
        exact NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun l3 _ =>
          NSP.weaken (ih.execS F hP nps ph _ l3 hf ho hfr) fun _ h => ⟨fun h0 => h0.elim, h.2⟩
      | cont l2 => exact NSP.weaken (ih.execS F hP nps ph _ l2 hf ho hfr) fun _ h => ⟨fun h0 => h0.elim, h.2⟩
      | brk _ => exact NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
      | ret _ => exact NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
    · exact NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
  | @doWhile lp u0 _ _ body c hb hc =>
    have hf := hf0
    simp only [execS]
    obtain ⟨ys, rfl⟩ := RStmt.ext body
    have tail : ∀ l₂ : Locals E.layout Γ, NSP (do
        let __discr ← sub l₂ (evalE G F n c)
        let __do_lift ← getV __discr.fst
        match __do_lift with
          | Val.bool true => execS G F n nps ph (body.doWhile c) __discr.snd
          | _ => pure (Out.normal __discr.snd))
        (fun o => lp = false → o.esc = false) := fun l₂ =>
      NSP.bind (hsub c hc ho.2) fun p _ => NSP.bind (NSP.of_ns (getV_ns rfl p.1)) fun x _ => by
        split
        · exact NSP.weaken (ih.execS F hP nps ph _ p.2 hf ho hfr) fun _ h => h.2
        · exact NSP.pure' fun _ => rfl
    refine NSP.bind (ih.execS F hP nps ph body l hb ho.1 hfr) fun o _ => ?_
    cases o with
    | normal l2 =>
      refine NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun l3 _ => ?_
      exact NSP.weaken (tail l3) fun _ h => ⟨fun h0 => h0.elim, h⟩
    | cont l2 =>
      refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l3 _ => ?_
      exact NSP.weaken (tail l3) fun _ h => ⟨fun h0 => h0.elim, h⟩
    | brk _ => exact NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
    | ret _ => exact NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
  | forLoop init c post body hsi hi hc hp hb =>
    simp only [execS]
    obtain ⟨ys, rfl⟩ := RStmt.ext init
    refine NSP.bind (ih.execS F hP nps ph init l hi ho.1 hfr) fun o ho1 => ?_
    obtain ⟨l1, rfl⟩ := ho1.1 hsi
    refine NSP.bind (ih.forIter F hP nps ph c post body l1 hc ho.2.1 hp ho.2.2.1 hb ho.2.2.2 (hfr.ext ys))
      fun o2 h2 => ?_
    rcases h2 with ⟨l2, rfl⟩ | ⟨l2, rfl⟩
    · exact NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun _ _ => NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
    · exact NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun _ _ => NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩

theorem execItemsX_step (ih : StmtNSAtX G X A Q n) (hX : ∀ m, m ≤ n → ∀ F, Q F.contract → ExprNSAt A G F m)
    (F : Fr) (hP : Q F.contract) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) (hf : IFrag X A b) (ho : b.OpsOK)
    (hfr : BodyFrame nps R Γ) : NSP (execItems G F (n + 1) nps ph b l) (fun o => k.loop = false → o.esc = false) := by
  cases hf with
  | base b h => exact execItems_nsStep ih.toBase (hX n (Nat.le_refl n)) F hP nps ph b l h ho hfr
  | nil => exact NSP.pure' fun _ => rfl
  | stmt s rest hs hr =>
    simp only [execItems]
    obtain ⟨ys, rfl⟩ := RStmt.ext s
    refine NSP.bind (ih.execS F hP nps ph s l hs ho.1 hfr) fun o h => ?_
    cases o with
    | normal l1 =>
      exact NSP.bind (ih.execItems F hP nps ph rest l1 hr ho.2 (hfr.ext ys)) fun o' h' =>
        NSP.weaken (Out.up_esc ys o') fun _ h'' hk => h''.trans (h' hk)
    | brk _ => exact NSP.pure' fun hk => h.2 hk
    | cont _ => exact NSP.pure' fun hk => h.2 hk
    | ret _ => exact NSP.pure' fun _ => rfl
  | unchecked inner rest hb hr =>
    simp only [execItems]
    obtain ⟨ys, rfl⟩ := RItems.ext inner
    refine NSP.bind (ih.execItems { F with checked := false } hP nps ph inner l hb ho.1 hfr) fun o h => ?_
    cases o with
    | normal l1 =>
      exact NSP.bind (NSP.lift_ok (Locals.restore_ok ys l1)) fun l2 _ => ih.execItems F hP nps ph rest l2 hr ho.2 hfr
    | brk _ => exact NSP.pure' fun hk => h hk
    | cont _ => exact NSP.pure' fun hk => h hk
    | ret _ => exact NSP.pure' fun _ => rfl

theorem forIterX_step (ih : StmtNSAtX G X A Q n) (hX : ∀ F, Q F.contract → ExprNSAt A G F n) (F : Fr) (hP : Q F.contract) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool}
    {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂)
    (l : Locals E.layout Γ₁) (hc : ROptBool.ValFragC A c) (hc' : c.OpsOK) (hp : ROptExpr.ValFragC A post)
    (hp' : post.OpsOK) (hb : SFrag X A body) (hb' : body.OpsOK) (hfr : BodyFrame nps R Γ₁) :
    NSP (forIter G F (n + 1) nps ph c post body l) (fun o => (∃ l', o = .normal l') ∨ (∃ l', o = .ret l')) := by
  simp only [forIter]
  obtain ⟨ys, rfl⟩ := RStmt.ext body
  cases c with
  | none =>
    refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun y _ => ?_
    split
    · exact NSP.pure' (.inl ⟨_, rfl⟩)
    · refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun _ _ => ?_
      refine NSP.bind (ih.execS F hP nps ph body y.2 hb hb' hfr) fun o _ => ?_
      cases o with
      | normal l2 =>
        refine NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun l3 _ => ?_
        cases post with
        | none =>
          exact NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
            ih.forIter F hP nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
        | some pe =>
          exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
            (NSP.of_ns ((hX F hP).val pe hp.1 hp')) fun _ _ _ => trivial)) fun q _ =>
            NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
              ih.forIter F hP nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
      | cont l2 =>
        refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l3 _ => ?_
        cases post with
        | none =>
          exact NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
            ih.forIter F hP nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
        | some pe =>
          exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
            (NSP.of_ns ((hX F hP).val pe hp.1 hp')) fun _ _ _ => trivial)) fun q _ =>
            NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
              ih.forIter F hP nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
      | brk _ => exact NSP.pure' (.inl ⟨_, rfl⟩)
      | ret _ => exact NSP.pure' (.inr ⟨_, rfl⟩)
  | some ce =>
    refine NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns ((hX F hP).val ce hc hc')) fun _ _ _ => trivial)) fun p _ =>
      NSP.bind (NSP.of_ns (getV_ns rfl p.1)) fun x _ => ?_
    obtain ⟨b, rfl⟩ := Val.eq_bool x
    refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun y _ => ?_
    split
    · exact NSP.pure' (.inl ⟨_, rfl⟩)
    · refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun _ _ => ?_
      refine NSP.bind (ih.execS F hP nps ph body y.2 hb hb' hfr) fun o _ => ?_
      cases o with
      | normal l2 =>
        refine NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun l3 _ => ?_
        cases post with
        | none =>
          exact NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
            ih.forIter F hP nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
        | some pe =>
          exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
            (NSP.of_ns ((hX F hP).val pe hp.1 hp')) fun _ _ _ => trivial)) fun q _ =>
            NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
              ih.forIter F hP nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
      | cont l2 =>
        refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l3 _ => ?_
        cases post with
        | none =>
          exact NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
            ih.forIter F hP nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
        | some pe =>
          exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
            (NSP.of_ns ((hX F hP).val pe hp.1 hp')) fun _ _ _ => trivial)) fun q _ =>
            NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
              ih.forIter F hP nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
      | brk _ => exact NSP.pure' (.inl ⟨_, rfl⟩)
      | ret _ => exact NSP.pure' (.inr ⟨_, rfl⟩)

end

end Solidity.Theory.Progress
