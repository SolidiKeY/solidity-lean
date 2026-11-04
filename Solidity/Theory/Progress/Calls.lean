import Solidity.Theory.Progress.Fragment

/-!
# Progress with internal calls over the extended fragment (S4.1)

The joint induction of `Solidity/Source/StmtProgress.lean` (`FragAt`,
`fragAt`) over the extended fragment of `Theory/Progress/Fragment.lean`:
expressions (with internal calls to the allowed declarations `A`),
statements and blocks of `SFrag X A`, bodies without modifiers and
internal calls are never `stuck`, at every horizon, from every state, for
a program whose allowed functions are bodies of the extended fragment
(`CallsOKX`) and an extension whose node step is proved
(`StmtExt.Sound`).

Expression progress is kept at every horizon up to `n` (`FragXAt.expr`),
which the tuple literal of a tuple declaration needs (its components are
evaluated at the lower horizons `evalArgs` steps through).
-/

namespace Solidity.Theory.Progress

open Solidity.Source Solidity.Source.Progress EM

variable {E : Env}

/-- **The program premise**: every function `A` allows, dispatched from
contract `c`, is a body without modifiers in the extended fragment, in the
operations' domains, whose locals are the frame the call builds and whose
return types have defaults. `CallsOK` with `IFrag` for `ValFragC`. -/
def CallsOKX (X : StmtExt E) (A : Decl → Prop) (G : Glob E) (c : String) : Prop :=
  ∀ (d : Decl) {ps rs : List STy}, d.fnSig E = some (ps, rs) → A d →
    ∃ b, G.prog.body (G.dispatchFn c d) = some b ∧ b.mods = [] ∧
      rs.reverseAux (ps.reverseAux []) = b.locals ∧ b.rs = rs ∧ b.ps.length = ps.length ∧
      (∀ τ ∈ rs, (Val.default E.layout τ).isSome = true) ∧ IFrag X A b.items ∧ b.items.OpsOK

/-- Every program the original fragment admits is admitted. -/
theorem CallsOK.toX {A : Decl → Prop} {G : Glob E} {c : String} (h : CallsOK A G c) (X : StmtExt E) :
    CallsOKX X A G c := by
  intro d ps rs hs hA
  obtain ⟨b, hb, hm, hl, hr, hp, hz, hf, ho⟩ := h d hs hA
  exact ⟨b, hb, hm, hl, hr, hp, hz, .base b.items hf, ho⟩

/-- **The joint induction hypothesis** at horizon `n`, for frames of
contract `c`. -/
structure FragXAt (X : StmtExt E) (A : Decl → Prop) (G : Glob E) (c : String) (n : Nat) : Prop where
  expr : ∀ m, m ≤ n → ∀ F, F.contract = c → ExprNSAt A G F m
  stmt : StmtNSAtX G X A (· = c) n
  mods : ∀ (F : Fr), F.contract = c → ∀ (b : RBody E) (l : Locals E.layout b.locals), IFrag X A b.items →
    b.items.OpsOK → BodyFrame b.ps.length b.rs b.locals → NS (runMods G F n b [] l)
  call : ∀ F, F.contract = c → CallNS A G F n

/-- At horizon `0` everything times out. -/
theorem fragXAt_zero (X : StmtExt E) (A : Decl → Prop) (G : Glob E) (c : String) : FragXAt X A G c 0 where
  expr m hm F _ := by
    rw [Nat.le_zero.1 hm]
    exact exprNSAt_zero A G F
  stmt := stmtNSAtX_zero G X A _
  mods _ _ _ _ _ _ _ := by rw [runMods.eq_1]; exact NS.halt' fun _ e => by cases e
  call _ _ _ _ _ _ _ _ := by rw [callInternal.eq_1]; exact NS.halt' fun _ e => by cases e

section
variable {X : StmtExt E} {A : Decl → Prop} {Q : String → Prop} {G : Glob E} {c : String} {n : Nat}

/-- The statement step over the extended fragment. -/
theorem stmtNSAtX_step (ih : StmtNSAtX G X A Q n) (hX : ∀ m, m ≤ n → ∀ F, Q F.contract → ExprNSAt A G F m)
    (hS : X.Sound G A Q) : StmtNSAtX G X A Q (n + 1) where
  execS F hP nps ph _ _ _ _ _ s l hf ho hfr := execSX_step ih hX hS F hP nps ph s l hf ho hfr
  execItems F hP nps ph _ _ _ _ _ b l hf ho hfr := execItemsX_step ih hX F hP nps ph b l hf ho hfr
  forIter F hP nps ph _ _ _ _ _ c post body l hc hc' hp hp' hb hb' hfr :=
    forIterX_step ih (hX n (Nat.le_refl n)) F hP nps ph c post body l hc hc' hp hp' hb hb' hfr

/-- **A modifier-free body** of the extended fragment, one step up. -/
theorem modsX_step (ih : FragXAt X A G c n) (F : Fr) (hc : F.contract = c) (b : RBody E)
    (l : Locals E.layout b.locals) (hf : IFrag X A b.items) (ho : b.items.OpsOK)
    (hfr : BodyFrame b.ps.length b.rs b.locals) : NS (runMods G F (n + 1) b [] l) := by
  simp only [runMods]
  obtain ⟨ys, hys⟩ := RItems.ext b.items
  refine NSP.ns (NSP.bind (R := fun _ => True)
    (NSP.weaken (ih.stmt.execItems F hc b.ps.length none b.items l hf ho hfr) fun _ h => h rfl) fun o ho' => ?_)
  cases o with
  | normal l' => exact NSP.of_ns (NS.lift' (Locals.restore_ok' ys hys l'))
  | ret l' => exact NSP.pure' trivial
  | brk _ => exact nomatch ho'
  | cont _ => exact nomatch ho'

/-- **An internal call** to an allowed function, one step up. -/
theorem callX_step (hG : CallsOKX X A G c) (ih : FragXAt X A G c n) (F : Fr) (hc : F.contract = c) :
    CallNS A G F (n + 1) := by
  intro d ps rs hs hA vs
  subst hc
  obtain ⟨b, hb, hmods, hloc, hrs, hps, hz, hf, ho⟩ := hG d hs hA
  have hl : b.locals = rs.reverse ++ ps.reverse := by
    rw [← hloc, List.reverseAux_eq, List.reverseAux_eq, List.append_nil]
  simp only [callInternal, hb]
  refine NS.bind (zeroVals_ns n rs hz) fun rv => ?_
  rw [dif_pos hloc, hmods]
  refine NS.bind (ih.mods { F with checked := true } rfl b _ hf ho ⟨[], ps.reverse, ?_, ?_⟩) fun l' =>
    NS.bind (NS.lift' (retVals_ok l' rs (hl.trans rfl))) fun _ => NS.pure' _
  · rw [hl, hrs, List.nil_append]
  · rw [List.length_reverse, hps]

end

/-- **The joint progress induction** over the extended fragment. -/
theorem fragXAt {X : StmtExt E} {A : Decl → Prop} {G : Glob E} {c : String} (hG : CallsOKX X A G c)
    (hS : X.Sound G A (· = c)) : ∀ n, FragXAt X A G c n
  | 0 => fragXAt_zero X A G c
  | n + 1 =>
    have ih : FragXAt X A G c n := fragXAt hG hS n
    { expr := fun m hm F hc => by
        rcases Nat.lt_or_eq_of_le hm with hm | rfl
        · exact ih.expr m (Nat.le_of_lt_succ hm) F hc
        · exact exprNSAt_step (ih.expr n (Nat.le_refl n) F hc) (ih.call F hc)
      stmt := stmtNSAtX_step ih.stmt ih.expr hS
      mods := fun F hc b l hf ho hfr => modsX_step ih F hc b l hf ho hfr
      call := fun F hc => callX_step hG ih F hc }

end Solidity.Theory.Progress
