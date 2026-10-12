import Solidity.Calculus.TermLib
import Solidity.Calculus.SeqRewrite
import Solidity.Calculus.StateFacts

/-!
# The term laws at an update's right-hand sides, scoped

solkey's term laws, read on the scoped terms `Tm C Γ s` (`Calculus/Fml.lean`)
and the scoped updates `Upd C Γ Δ`, over `State C Γ`: what makes each exact
inside an update's right-hand sides, under either modality.  A law `t ⇝ t'`
rewrites there when the right side returns what the left side does
(`Tm.EvalRefinesAt`), and, wherever the update returns, the left side
returns what the right side does: the update holds the write the law reads
back.  `LawCov` bundles the two with the syntactic check that gives the
second, decided by `rfl`.

* **The literal laws** (`LitLaw`): KeY's `*_literals` taclets, exact
  everywhere (`LitLaw.exact`).
* **A storage law onto a literal** (`Upd.covers`): `find(save(s, p, 10), p)`
  over `storage := save(s, p, 10)`, a word at or below a deleted node over
  `storage := delAt(s, p)`, each read member-wise too (`Tm.baseAny`).
* **The frame and delete-value laws** (`TermTaclet.RefLaw`,
  `Upd.coversRef`): their storage operation held by the update.
* **Two member-wise forms of one read** (`Tm.sameBase`): they return alike
  in every state (`Tm.sameBase_eval`).
* **The memory laws** (`EvalLaw`, `Upd.coversEval`): KeY's
  `readOnWrite`, `readAddEqual`, … with their side conditions
  (`Tm.freshPath?`, `Tm.boundedIn`, `Tm.apart?`).

A scoped term's symbols are read on the state's global part (`State.globE`),
so the reasoning is about `Semantics.State` and its lemmas.

**Kernel-checked side conditions.**  Every `Bool` a law's side condition or
a cover check calls is written by structural recursion on the inductive,
generic in the sort where it recurses, so it reduces by `rfl` on closed
terms (the pins at the end).
-/

namespace Solidity

open Semantics SemanticsProperties
open Solidity (Srt Op0 Op1 Op2 Op3)

variable {C : Contract} {Γ : Ctx}

/-! ## Refinement of evaluation -/

/-- Where `t` returns, `t'` returns the same, in every state (at any sort). -/
def Tm.EvalRefinesAt {u : Srt} (t t' : Tm C Γ u) : Prop :=
  ∀ σ : State C Γ, Srt.Le u (t.evalT σ) (t'.evalT σ)

/-- **A Theory equation onto a literal refines evaluation**, at any scope
(`Tm.EvalRefines.of_theq`): where `t` returns `x` it denotes `x`
(`Tm.denoteT_evalT`), and the literal returns what it denotes. -/
theorem Tm.evalRefinesAt_of_theq {t t' : Tm C Γ .val} (h : Tm.Theq t t') (ht : t'.isLit = true) :
    Tm.EvalRefinesAt t t' := fun σ x hx => by
  have e := h σ
  rw [Tm.denoteT_evalT σ t x hx] at e
  match t', ht, e with
  | .app0 (.lit v), _, e =>
    cases Theory.StValue.Equiv.prim_iff.1 e
    rfl

/-! ## The literal laws -/

/-- KeY's `*_literals` taclets, as the interpreter computes them.  Hover a
constructor for the taclet. -/
inductive LitLaw : Tm C Γ .val → Tm C Γ .val → Prop
  /-- **`add_literals`**: `a + b ⇝ a + b` folded, in `uint` range. -/
  | add_literals {a b : Int} (h : 0 ≤ a + b ∧ a + b < uintBound := by decide) :
      LitLaw (.app2 (.binop .add .uint) (Tm.lit (.int a)) (Tm.lit (.int b))) (Tm.lit (.int (a + b)))
  /-- **`sub_literals`**: `a - b ⇝ a - b` folded, in `uint` range. -/
  | sub_literals {a b : Int} (h : 0 ≤ a - b ∧ a - b < uintBound := by decide) :
      LitLaw (.app2 (.binop .sub .uint) (Tm.lit (.int a)) (Tm.lit (.int b))) (Tm.lit (.int (a - b)))
  /-- **`leq_literals`**: `a <= b ⇝ true` or `false`. -/
  | leq_literals {a b : Int} :
      LitLaw (.app2 (.binop .le .uint) (Tm.lit (.int a)) (Tm.lit (.int b)))
        (Tm.lit (.bool (decide (a ≤ b))))
  /-- **`less_literals`**: `a < b ⇝ true` or `false`. -/
  | less_literals {a b : Int} :
      LitLaw (.app2 (.binop .lt .uint) (Tm.lit (.int a)) (Tm.lit (.int b)))
        (Tm.lit (.bool (decide (a < b))))
  /-- **`greater_literals`**: `a > b ⇝ true` or `false`. -/
  | greater_literals {a b : Int} :
      LitLaw (.app2 (.binop .gt .uint) (Tm.lit (.int a)) (Tm.lit (.int b)))
        (Tm.lit (.bool (decide (b < a))))
  /-- **`geq_literals`**: `a >= b ⇝ true` or `false`. -/
  | geq_literals {a b : Int} :
      LitLaw (.app2 (.binop .ge .uint) (Tm.lit (.int a)) (Tm.lit (.int b)))
        (Tm.lit (.bool (decide (b ≤ a))))
  /-- **`div_literals`**: `a / b ⇝ a / b` folded (truncated, as Solidity divides), the divisor not
  zero and the quotient in `uint` range. -/
  | div_literals {a b : Int} (h : b ≠ 0 ∧ 0 ≤ a.tdiv b ∧ a.tdiv b < uintBound := by decide) :
      LitLaw (.app2 (.binop .div .uint) (Tm.lit (.int a)) (Tm.lit (.int b))) (Tm.lit (.int (a.tdiv b)))

/-- An operation on two integer literals is the interpreter's, applied and
range-checked. -/
theorem LitLaw.binop_lit_eval (op : BinOp) (a b : Int) (σ : State C Γ) :
    (Tm.app2 (.binop op .uint) (Tm.lit (.int a)) (Tm.lit (.int b)) : Tm C Γ .val).evalT σ =
      (do checkArith (op.retTy (.prim .uint)) (← applyBinOp op (.int a) (.int b))) := by
  cases op <;> rfl

/-- **A literal law is exact**: its right side is a literal, which its left
side returns in every state. -/
theorem LitLaw.exact {t t' : Tm C Γ .val} :
    LitLaw t t' → ∃ v, t' = Tm.lit v ∧ ∀ σ : State C Γ, t.evalT σ = .ok v
  | @LitLaw.add_literals _ _ a b h => ⟨_, rfl, fun σ => by
      rw [LitLaw.binop_lit_eval]
      show (if 0 ≤ a + b ∧ a + b < uintBound then (Except.ok (Value.int (a + b)) : Res Value)
        else .error .revert) = _
      rw [if_pos h]⟩
  | @LitLaw.sub_literals _ _ a b h => ⟨_, rfl, fun σ => by
      rw [LitLaw.binop_lit_eval]
      show (if 0 ≤ a - b ∧ a - b < uintBound then (Except.ok (Value.int (a - b)) : Res Value)
        else .error .revert) = _
      rw [if_pos h]⟩
  | .leq_literals => ⟨_, rfl, fun σ => by rw [LitLaw.binop_lit_eval]; rfl⟩
  | .less_literals => ⟨_, rfl, fun σ => by rw [LitLaw.binop_lit_eval]; rfl⟩
  | .greater_literals => ⟨_, rfl, fun σ => by rw [LitLaw.binop_lit_eval]; rfl⟩
  | .geq_literals => ⟨_, rfl, fun σ => by rw [LitLaw.binop_lit_eval]; rfl⟩
  | @LitLaw.div_literals _ _ a b h => ⟨_, rfl, fun σ => by
      rw [LitLaw.binop_lit_eval]
      show (if b = 0 then (Except.error .revert : Res Value) else .ok (Value.int (a.tdiv b))) >>=
        checkArith (.prim .uint) = _
      rw [if_neg h.1]
      show (if 0 ≤ a.tdiv b ∧ a.tdiv b < uintBound then (Except.ok (Value.int (a.tdiv b)) : Res Value)
        else .error .revert) = _
      rw [if_pos h.2]⟩

/-- The two sides of a literal law evaluate alike in every state. -/
theorem LitLaw.evalEq {t t' : Tm C Γ .val} (r : LitLaw t t') (σ : State C Γ) :
    t.evalT σ = t'.evalT σ := by
  obtain ⟨v, rfl, hv⟩ := r.exact
  rw [hv σ]
  rfl

/-- The two sides of a literal law denote alike in the Theory. -/
theorem LitLaw.theq {t t' : Tm C Γ .val} (r : LitLaw t t') : Tm.Theq t t' := by
  obtain ⟨v, rfl, hv⟩ := r.exact
  intro σ
  rw [Tm.denoteT_evalT σ t v (hv σ)]
  exact Theory.StValue.Equiv.refl _

/-! ## What an update's elements read -/

/-- The storage terms an element writes the storage with. -/
def UpdElem.storTerms {Δ : Ctx} : UpdElem C Γ Δ → List (Tm C Γ .st)
  | .storage s => [s]
  | _ => []

/-- The memory terms an element writes the memory with. -/
def UpdElem.memTerms {Δ : Ctx} : UpdElem C Γ Δ → List (Tm C Γ .mem)
  | .memory m => [m]
  | _ => []

/-- The right-hand sides of an update's `storage :=` elements. -/
def Upd.storTerms : {Δ : Ctx} → Upd C Γ Δ → List (Tm C Γ .st)
  | _, .nil => []
  | _, .snoc U e => U.storTerms ++ e.storTerms
  | _, .decl U _ _ => U.storTerms
  | _, .pop U _ => U.storTerms
  | _, .drop U _ => U.storTerms

/-- The right-hand sides of an update's `memory :=` elements. -/
def Upd.memTerms : {Δ : Ctx} → Upd C Γ Δ → List (Tm C Γ .mem)
  | _, .nil => []
  | _, .snoc U e => U.memTerms ++ e.memTerms
  | _, .decl U _ _ => U.memTerms
  | _, .pop U _ => U.memTerms
  | _, .drop U _ => U.memTerms

/-- Where an update returns, the state before each of its elements. -/
theorem Upd.globT_ok_prefix {σ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    {τ : Semantics.State} → U.globT σ = .ok τ → (∀ s ∈ U.storTerms, ∃ τ', s.evalT σ = .ok τ') ∧
      (∀ m ∈ U.memTerms, ∃ μ, m.evalT σ = .ok μ)
  | _, .nil, _, _ => ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  | _, .snoc U e, τ, h => by
    obtain ⟨ρ, hU, hw⟩ := bind_ok_inv h
    obtain ⟨ihs, ihm⟩ := Upd.globT_ok_prefix U hU
    refine ⟨fun s hs => ?_, fun m hm => ?_⟩
    · rcases List.mem_append.1 hs with hs | hs
      · exact ihs s hs
      · cases e with
        | storage s' =>
          simp only [UpdElem.storTerms, List.mem_singleton] at hs
          subst hs
          obtain ⟨τ', hs', -⟩ := bind_ok_inv hw
          exact ⟨τ', hs'⟩
        | _ => nomatch hs
    · rcases List.mem_append.1 hm with hm | hm
      · exact ihm m hm
      · cases e with
        | memory m' =>
          simp only [UpdElem.memTerms, List.mem_singleton] at hm
          subst hm
          obtain ⟨μ, hm', -⟩ := bind_ok_inv hw
          exact ⟨μ, hm'⟩
        | _ => nomatch hm
  | _, .decl U _ _, τ, h => by
    obtain ⟨ρ, hU, -⟩ := bind_ok_inv h
    exact Upd.globT_ok_prefix U hU
  | _, .pop U _, τ, h | _, .drop U _, τ, h => by
    exact Upd.globT_ok_prefix U h

/-- **A storage write that is an element of an update that returns, returns.** -/
theorem Upd.storage_eval_of_globT {Δ : Ctx} {U : Upd C Γ Δ} {σ : State C Γ}
    {τ : Semantics.State} (h : U.globT σ = .ok τ) {s : Tm C Γ .st} (hs : s ∈ U.storTerms) :
    ∃ τ' : Semantics.State, s.evalT σ = .ok τ' :=
  (Upd.globT_ok_prefix U h).1 s hs

/-- **A memory write that is an element of an update that returns, returns.** -/
theorem Upd.memory_eval_of_globT {Δ : Ctx} {U : Upd C Γ Δ} {σ : State C Γ}
    {τ : Semantics.State} (h : U.globT σ = .ok τ) {m : Tm C Γ .mem} (hm : m ∈ U.memTerms) :
    ∃ μ : Semantics.State, m.evalT σ = .ok μ :=
  (Upd.globT_ok_prefix U h).2 m hm

/-! ## A storage term read first

`s` is read before anything else of `t` (`t.onSpine s`): `t` is `s`, or a
storage operation whose storage argument has `s` on its spine.  So `t` halts
wherever `s` does (`Tm.onSpine_error`); the memory twin is `Tm.onMemSpine`. -/

/-- `f` of each storage term on `t`'s spine.  Generic in the sort. -/
def Tm.spineAny (f : Tm C Γ .st → Bool) : {u : Srt} → Tm C Γ u → Bool
  | _, .app1 (.select r) h a => f (.app1 (.select r) h a) || a.spineAny f
  | _, .app2 .delAt a p => f (.app2 .delAt a p) || a.spineAny f
  | _, .app2 (.pushSlot E) a p => f (.app2 (.pushSlot E) a p) || a.spineAny f
  | _, .app2 .pop a p => f (.app2 .pop a p) || a.spineAny f
  | _, .app2 .shrink a p => f (.app2 .shrink a p) || a.spineAny f
  | _, .app2 (.extend E) a p => f (.app2 (.extend E) a p) || a.spineAny f
  | _, .app3 .save a p v => f (.app3 .save a p v) || a.spineAny f
  | _, .app3 .push a p v => f (.app3 .push a p v) || a.spineAny f
  | .st, t => f t
  | _, _ => false

@[inherit_doc Tm.spineAny]
def Tm.onSpine (t s : Tm C Γ .st) : Bool := t.spineAny (·.beqR s)

/-- A term on the spine of `s` halts wherever `s` does. -/
theorem Tm.onSpine_error {s : Tm C Γ .st} {σ : State C Γ} {e : Halt} (hs : s.evalT σ = .error e) :
    (t : Tm C Γ .st) → t.onSpine s = true → ∃ e', t.evalT σ = .error e'
  | .app1 (.select r) h a, ht => by
    simp only [Tm.onSpine, Tm.spineAny, Bool.or_eq_true] at ht
    rcases ht with ht | ht
    · rw [Tm.eq_of_beqR ht]; exact ⟨e, hs⟩
    · obtain ⟨e', ha⟩ := Tm.onSpine_error hs a ht
      exact ⟨e', by show Op1.eval _ _ (a.evalT σ) = _; rw [ha]; rfl⟩
  | .app2 .delAt a p, ht | .app2 (.pushSlot _) a p, ht | .app2 .pop a p, ht
  | .app2 .shrink a p, ht | .app2 (.extend _) a p, ht => by
    simp only [Tm.onSpine, Tm.spineAny, Bool.or_eq_true] at ht
    rcases ht with ht | ht
    · rw [Tm.eq_of_beqR ht]; exact ⟨e, hs⟩
    · obtain ⟨e', ha⟩ := Tm.onSpine_error hs a ht
      exact ⟨e', by show Op2.eval _ _ (a.evalT σ) (p.evalT σ) = _; rw [ha]; rfl⟩
  | .app3 .save a p v, ht => by
    simp only [Tm.onSpine, Tm.spineAny, Bool.or_eq_true] at ht
    rcases ht with ht | ht
    · rw [Tm.eq_of_beqR ht]; exact ⟨e, hs⟩
    · obtain ⟨e', ha⟩ := Tm.onSpine_error hs a ht
      show ∃ e'', Op3.eval _ _ (a.evalT σ) (p.evalT σ) (v.evalT σ) = _
      rw [ha]
      cases v.evalT σ <;> exact ⟨_, rfl⟩
  | .app3 .push a p v, ht => by
    simp only [Tm.onSpine, Tm.spineAny, Bool.or_eq_true] at ht
    rcases ht with ht | ht
    · rw [Tm.eq_of_beqR ht]; exact ⟨e, hs⟩
    · obtain ⟨e', ha⟩ := Tm.onSpine_error hs a ht
      exact ⟨e', by show Op3.eval _ _ (a.evalT σ) (p.evalT σ) (v.evalT σ) = _; rw [ha]; rfl⟩
  | .pvS _, ht | .app0 .storage, ht | .app0 (.mtSt _), ht => by
    simp only [Tm.onSpine, Tm.spineAny] at ht
    rw [Tm.eq_of_beqR ht]; exact ⟨e, hs⟩

/-- `f` of each memory term on `t`'s memory spine.  Generic in the sort. -/
def Tm.memSpineAny (f : Tm C Γ .mem → Bool) : {u : Srt} → Tm C Γ u → Bool
  | _, .app1 (.addM R) h a => f (.app1 (.addM R) h a) || a.memSpineAny f
  | _, .app2 .copySt a v => f (.app2 .copySt a v) || a.memSpineAny f
  | _, .app3 .write a p v => f (.app3 .write a p v) || a.memSpineAny f
  | .mem, t => f t
  | _, _ => false

@[inherit_doc Tm.memSpineAny]
def Tm.onMemSpine (t s : Tm C Γ .mem) : Bool := t.memSpineAny (·.beqR s)

/-- A term on the memory spine of `s` halts wherever `s` does. -/
theorem Tm.onMemSpine_error {s : Tm C Γ .mem} {σ : State C Γ} {e : Halt}
    (hs : s.evalT σ = .error e) : (t : Tm C Γ .mem) → t.onMemSpine s = true → ∃ e', t.evalT σ = .error e'
  | .app1 (.addM _) _ a, ht => by
    simp only [Tm.onMemSpine, Tm.memSpineAny, Bool.or_eq_true] at ht
    rcases ht with ht | ht
    · rw [Tm.eq_of_beqR ht]; exact ⟨e, hs⟩
    · obtain ⟨e', ha⟩ := Tm.onMemSpine_error hs a ht
      exact ⟨e', by show Op1.eval _ _ (a.evalT σ) = _; rw [ha]; rfl⟩
  | .app2 .copySt a v, ht => by
    simp only [Tm.onMemSpine, Tm.memSpineAny, Bool.or_eq_true] at ht
    rcases ht with ht | ht
    · rw [Tm.eq_of_beqR ht]; exact ⟨e, hs⟩
    · obtain ⟨e', ha⟩ := Tm.onMemSpine_error hs a ht
      show ∃ e'', Op2.eval _ _ (a.evalT σ) (v.evalT σ) = _
      rw [ha]
      cases v.evalT σ <;> exact ⟨_, rfl⟩
  | .app3 .write a p v, ht => by
    simp only [Tm.onMemSpine, Tm.memSpineAny, Bool.or_eq_true] at ht
    rcases ht with ht | ht
    · rw [Tm.eq_of_beqR ht]; exact ⟨e, hs⟩
    · obtain ⟨e', ha⟩ := Tm.onMemSpine_error hs a ht
      show ∃ e'', Op3.eval _ _ (a.evalT σ) (p.evalT σ) (v.evalT σ) = _
      rw [ha]
      cases v.evalT σ <;> exact ⟨_, rfl⟩
  | .app0 .memory, ht => by
    simp only [Tm.onMemSpine, Tm.memSpineAny] at ht
    rw [Tm.eq_of_beqR ht]; exact ⟨e, hs⟩

/-! ## A storage law onto a literal

`{ storage := save(storage, p, 10) ‖ x := find(save(storage, p, 10), p) }`
halts exactly where `save(storage, p, 10)` does, and so does
`{ storage := save(storage, p, 10) ‖ x := 10 }`: the read returns wherever the
write it reads back does, and the write is an element of the update.
`Upd.covers` is the syntactic side of it. -/

section StorageEval

variable (σ : State C Γ)

/-- `find(s, p)` read in `σ`: `s`, then `p`, then the slot. -/
theorem Tm.find_eval (s : Tm C Γ .st) (p : Tm C Γ .path) :
    (Tm.app2 .find s p).evalT σ = (do
      let τ ← s.evalT σ
      let (r, segs) ← p.evalT σ
      (← τ.findStorage r segs).asValue) := rfl

/-- `s[p].length` read in `σ`. -/
theorem Tm.len_eval (s : Tm C Γ .st) (p : Tm C Γ .path) :
    (Tm.app2 .len s p).evalT σ = (do
      let τ ← s.evalT σ
      let (r, segs) ← p.evalT σ
      arrayLen τ r segs) := rfl

/-- `delAt(s, p)` read in `σ`: the slot read, then written to its default. -/
theorem Tm.delAt_eval (s : Tm C Γ .st) (p : Tm C Γ .path) :
    (Tm.app2 .delAt s p).evalT σ = (do
      let τ ← s.evalT σ
      let (r, segs) ← p.evalT σ
      τ.delAtAt r segs) := rfl

/-- `save(s, p, v)` read in `σ`: the value, the storage, the path, the write. -/
theorem Tm.save_eval (s : Tm C Γ .st) (p : Tm C Γ .path) (v : Tm C Γ .sv) :
    (Tm.app3 .save s p v).evalT σ = (do
      let sv ← v.evalT σ
      let τ ← s.evalT σ
      let (r, segs) ← p.evalT σ
      τ.writeStorage r segs sv) := rfl

/-- `select(s, r)` read in `σ`: the frame at the root `r` of what `s` returns. -/
theorem Tm.select_eval (s : Tm C Γ .st) (r : Name) (h : (Op1.select r).named = false) :
    (Tm.app1 (.select r) h s).evalT σ = (s.evalT σ >>= State.selectRoot r) := rfl

/-- `p.f` read in `σ`. -/
theorem Tm.field_eval (p : Tm C Γ .path) (f : Name) (h : (Op1.field f).named = false) :
    (Tm.app1 (.field f) h p).evalT σ = (do
      let (r, segs) ← p.evalT σ
      pure (r, segs ++ [.field f])) := rfl

end StorageEval

/-- `save(s, p, v)` returned: the storage it returned reads `v` at `p`. -/
theorem Tm.save_lit_eval {s : Tm C Γ .st} {p : Tm C Γ .path} {v : Value}
    {h : (Op1.sval).named = false} {σ : State C Γ} {τ : Semantics.State}
    (he : (Tm.app3 .save s p (.app1 .sval h (Tm.lit v))).evalT σ = .ok τ) :
    ∃ r segs, p.evalT σ = .ok (r, segs) ∧ τ.findStorage r segs = .ok v.toSVal := by
  rw [Tm.save_eval] at he
  obtain ⟨sv, hsv, he⟩ := bind_ok_inv he
  have hsv' : v.toSVal = sv := Except.ok.inj (hsv : (Except.ok v.toSVal : Res Semantics.SVal) = .ok sv)
  subst hsv'
  obtain ⟨τs, -, he⟩ := bind_ok_inv he
  obtain ⟨⟨r, segs⟩, hp, he⟩ := bind_ok_inv he
  change τs.writeStorage r segs v.toSVal = .ok τ at he
  rw [State.writeStorage_toSVal] at he
  exact ⟨r, segs, hp, State.findStorage_saveStorage_same he⟩

section Paths

variable {σ : State C Γ}

/-- Two paths whose shapes diverge, where both resolve, have different roots
or divergent tails. -/
theorem Tm.diverges_eval {p q : Tm C Γ .path} {r r' : Name} {segs segs' : List Seg}
    (hd : p.diverges q = true) (hp : p.evalT σ = .ok (r, segs)) (hq : q.evalT σ = .ok (r', segs')) :
    r' ≠ r ∨ Close.Diverge segs segs' := by
  have hd' := Tm.diverges_denote σ hd
  rw [Tm.denoteT_evalT σ p r segs hp, Tm.denoteT_evalT σ q r' segs' hq] at hd'
  rcases Diverge_of_diverges _ _ hd' with h | h
  · exact Or.inl fun e => h (by rw [e])
  · exact Or.inr h

/-- Paths of the same segments, their checks aside, resolve alike where both
resolve. -/
theorem Tm.sameSegs_eval {p q : Tm C Γ .path} {r r' : Name} {segs segs' : List Seg}
    (heq : p.sameSegs q = true) (hp : p.evalT σ = .ok (r, segs)) (hq : q.evalT σ = .ok (r', segs')) :
    r = r' ∧ segs = segs' := by
  have heq' := Tm.sameSegs_denote σ heq
  rw [Tm.denoteT_evalT σ p r segs hp, Tm.denoteT_evalT σ q r' segs' hq] at heq'
  exact ⟨Seg.field.inj (List.cons.inj heq').1, (List.cons.inj heq').2⟩

/-- `q` leaving `p.length`, where both resolve: the write at `q` is at another
root or not above `p`. -/
theorem Tm.divergesLen_eval {q p : Tm C Γ .path} {r r' : Name} {segs segs' : List Seg}
    (hd : q.divergesLen p = true) (hq : q.evalT σ = .ok (r, segs)) (hp : p.evalT σ = .ok (r', segs')) :
    r' ≠ r ∨ ¬ Close.Prefix segs segs' := by
  have hd' := Tm.divergesLen_denote σ hd
  rw [Tm.denoteT_evalT σ q r segs hq, Tm.denoteT_evalT σ p r' segs' hp] at hd'
  rcases Diverge_of_diverges _ _ hd' with h | h
  · exact Or.inl fun e => h (by rw [e])
  · exact Or.inr fun hp' => h.not_prefix (hp'.right_append [.field "length"])

end Paths

/-- `f` of some path on the way down to `t`'s root through members only.
Generic in the sort. -/
def Tm.fieldsBelowAny (f : Tm C Γ .path → Bool) : {u : Srt} → Tm C Γ u → Bool
  | _, .app1 (.field _) _ q => f q || q.fieldsBelowAny f
  | _, _ => false

/-- `q` is `p` with one or more member selectors after it: a read below `p`
that no index check can halt. -/
def Tm.fieldsBelow (q p : Tm C Γ .path) : Bool := q.fieldsBelowAny (·.beqR p)

/-- `q.fieldsBelow p` in a run: `q` resolves wherever `p` does, to `p`'s
segments and some members. -/
theorem Tm.fieldsBelow_eval {p : Tm C Γ .path} {σ : State C Γ} {r : Name} {segs : List Seg}
    (hp : p.evalT σ = .ok (r, segs)) :
    (q : Tm C Γ .path) → q.fieldsBelow p = true →
      ∃ tail, tail ≠ [] ∧ tail.all Seg.isField = true ∧ q.evalT σ = .ok (r, segs ++ tail)
  | .app1 (.field f) hf q, h => by
    simp only [Tm.fieldsBelow, Tm.fieldsBelowAny, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain rfl := Tm.eq_of_beqR h
      refine ⟨[.field f], List.cons_ne_nil _ _, rfl, ?_⟩
      rw [Tm.field_eval, hp]
      rfl
    · obtain ⟨tail, -, hall, hq⟩ := Tm.fieldsBelow_eval hp q h
      refine ⟨tail ++ [.field f], fun e => List.cons_ne_nil _ _ (List.append_eq_nil_iff.1 e).2, ?_, ?_⟩
      · simp only [List.all_append, hall, List.all_cons, List.all_nil, Seg.isField, Bool.and_self]
      · rw [Tm.field_eval, hq]
        show Except.ok (r, (segs ++ tail) ++ [Seg.field f]) = _
        rw [List.append_assoc]
  | .pvP _, h | .app0 (.root _), h | .app1 .next _ _, h | .app2 .at _ _, h
  | .app2 .nextIn _ _, h | .app3 .atIn _ _ _, h => nomatch h

/-- `q` is `p`, or goes on below it through members: a read at or below `p`
that no index check can halt. -/
def Tm.atOrBelow (q p : Tm C Γ .path) : Bool := q.beqR p || q.fieldsBelow p

theorem Tm.atOrBelow_eval {p : Tm C Γ .path} {σ : State C Γ} {r : Name} {segs : List Seg}
    (hp : p.evalT σ = .ok (r, segs)) (q : Tm C Γ .path) (h : q.atOrBelow p = true) :
    ∃ tail, tail.all Seg.isField = true ∧ q.evalT σ = .ok (r, segs ++ tail) := by
  unfold Tm.atOrBelow at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · obtain rfl := Tm.eq_of_beqR h
    exact ⟨[], rfl, by rw [List.append_nil]; exact hp⟩
  · obtain ⟨tail, -, hf, hq⟩ := Tm.fieldsBelow_eval hp q h
    exact ⟨tail, hf, hq⟩

/-- The word read off the writes (`Tm.findLitBy`) is the word a run reads. -/
theorem Tm.findLitBy_eval {q : Tm C Γ .path} {σ : State C Γ} {r : Name} {sq : List Seg}
    (eq : q.evalT σ = .ok (r, sq)) :
    (s : Tm C Γ .st) → {w : Value} → s.findLitBy (·.sameSegs q) (·.diverges q) = some w →
      ∀ {τ : Semantics.State}, s.evalT σ = .ok τ → τ.findStorage r sq = .ok w.toSVal
  | .app3 .save s p v, w, h, τ, hs => by
    simp only [Tm.findLitBy] at h
    split at h
    · rename_i hpq
      obtain rfl := Tm.svLit?_eq h
      obtain ⟨r', segs', ep, hf⟩ := Tm.save_lit_eval hs
      obtain ⟨rfl, rfl⟩ := Tm.sameSegs_eval hpq ep eq
      exact hf
    · split at h
      · rename_i hd
        rw [Tm.save_eval] at hs
        obtain ⟨sv, -, hs⟩ := bind_ok_inv hs
        obtain ⟨τs, hτs, hs⟩ := bind_ok_inv hs
        obtain ⟨⟨r'', segs''⟩, ep, hs⟩ := bind_ok_inv hs
        change τs.writeStorage r'' segs'' sv = .ok τ at hs
        obtain ⟨x, hs⟩ := State.writeStorage_ok hs
        rw [Close.findStorage_saveStorage_apart hs (Tm.diverges_eval hd ep eq)]
        exact Tm.findLitBy_eval eq s h hτs
      · nomatch h
  | .pvS _, _, h, _, _ | .app0 _, _, h, _, _ | .app1 _ _ _, _, h, _, _ | .app2 _ _ _, _, h, _, _ =>
    nomatch h
  | .app3 .push _ _ _, _, h, _, _ => nomatch h

theorem Tm.findLit?_eval {s : Tm C Γ .st} {q : Tm C Γ .path} {w : Value} (h : s.findLit? q = some w)
    {σ : State C Γ} {τ : Semantics.State} (hs : s.evalT σ = .ok τ) {r : Name} {sq : List Seg}
    (eq : q.evalT σ = .ok (r, sq)) : τ.findStorage r sq = .ok w.toSVal := by
  unfold Tm.findLit? at h
  split at h
  · exact Tm.findLitBy_eval eq s h hs
  · nomatch h

/-- A word at or below a deleted node, in a run: the storage before the
delete reads the word there (`Tm.findLit?_eval`), so the reset node, which
keeps its members (`SVal.find_defaultOf_prim`), reads a word there. -/
theorem Tm.delAtBelow_eval {s : Tm C Γ .st} {p q : Tm C Γ .path} {w : Value}
    (hb : q.atOrBelow p = true) (hw : s.findLit? q = some w) {σ : State C Γ} {τ'' : Semantics.State}
    (hd : (Tm.app2 .delAt s p).evalT σ = .ok τ'') :
    ∃ y, (Tm.app2 .find (.app2 .delAt s p) q).evalT σ = .ok y := by
  have hd' := hd
  rw [Tm.delAt_eval] at hd'
  obtain ⟨τ', hs, hd'⟩ := bind_ok_inv hd'
  obtain ⟨⟨r, segs⟩, hp, hd'⟩ := bind_ok_inv hd'
  obtain ⟨cur, hcur, hsave⟩ := bind_ok_inv hd'
  obtain ⟨tail, hfields, hq⟩ := Tm.atOrBelow_eval hp q hb
  have hread : τ'.findStorage r (segs ++ tail) = Except.ok (Value.toSVal w) :=
    Tm.findLit?_eval hw hs hq
  rw [State.findStorage_append, hcur] at hread
  simp only [bind, Except.bind] at hread
  obtain ⟨x, hx⟩ : ∃ x : PrimVal, Value.toSVal w = Semantics.SVal.prim x := by cases w <;> exact ⟨_, rfl⟩
  rw [hx] at hread
  obtain ⟨y, hy⟩ := SVal.find_defaultOf_prim tail hfields cur hread
  have hfind : τ''.findStorage r (segs ++ tail) = Except.ok (Semantics.SVal.prim y) := by
    rw [State.findStorage_append, State.findStorage_saveStorage_same hsave]
    exact hy
  cases y with
  | int n =>
    refine ⟨.int n, ?_⟩
    rw [Tm.find_eval, hd, hq]
    simp only [bind, Except.bind, hfind]
    rfl
  | bool b =>
    refine ⟨.bool b, ?_⟩
    rw [Tm.find_eval, hd, hq]
    simp only [bind, Except.bind, hfind]
    rfl

/-! ## Reading member-wise

solkey reads a path from its head (`findMemberCons`, `selectOnSaveMember`,
`selectOnDelAtMember`): `find(save(storage, alice.age, 42), alice.age)`
becomes `find(select(save(storage, alice.age, 42), alice), age)`, then
`find(save(select(storage, alice), age, 42), age)`, then `42`.  In the
interpreter `select(s, r)` is the state `s` leaves with the struct at its
root `r` for its storage (`State.selectRoot`), so a storage term read
member-wise runs as the term it reads, in that frame (`Tm.baseAny`,
`Tm.baseAny_eval`), and a read of it returns exactly where the read of the
base does (`Tm.base_eval`).  Two member-wise forms of one read have one
base (`Tm.sameBase`), so a law between them rewrites an update's right-hand
side under any modality; the read of a write, member-wise, is covered as
the write it reads back is (`Upd.covers`). -/

/-- The root of a path: `alice` of `alice.account.balance`; `none` through an
alias.  Generic in the sort. -/
def Tm.rootName? : {u : Srt} → Tm C Γ u → Option Name
  | _, .app0 (.root r) => some r
  | _, .app1 (.field _) _ p => p.rootName?
  | _, .app1 .next _ p => p.rootName?
  | _, .app2 .at p _ => p.rootName?
  | _, _ => none

/-- A path of a root and members only: no alias, no index, no push slot.
Generic in the sort. -/
def Tm.isFields : {u : Srt} → Tm C Γ u → Bool
  | _, .app0 (.root _) => true
  | _, .app1 (.field _) _ p => p.isFields
  | _, _ => false

/-- A member path resolves in every state, to its root and its members. -/
theorem Tm.isFields_eval (σ : State C Γ) : (p : Tm C Γ .path) → p.isFields = true →
    ∃ f segs, p.evalT σ = .ok (f, segs) ∧ segs.all Seg.isField = true
  | .app0 (.root f), _ => ⟨f, [], rfl, rfl⟩
  | .app1 (.field g) _ p, h => by
    obtain ⟨f, segs, hp, hf⟩ := Tm.isFields_eval σ p h
    refine ⟨f, segs ++ [.field g], ?_, ?_⟩
    · rw [Tm.field_eval, hp]; rfl
    · simp only [List.all_append, hf, List.all_cons, List.all_nil, Seg.isField, Bool.and_self]
  | .pvP _, h | .app1 .next _ _, h | .app2 .at _ _, h | .app2 .nextIn _ _, h
  | .app3 .atIn _ _ _, h => nomatch h

/-- The path under the root `r`: `age` under `alice` is `alice.age`.  A path
through an alias is left as it is.  Generic in the sort. -/
def Tm.prefixRoot (r : Name) : {u : Srt} → Tm C Γ u → Tm C Γ u
  | _, .app0 (.root f) => .app1 (.field f) rfl (.app0 (.root r))
  | _, .app1 (.field f) h p => .app1 (.field f) h (p.prefixRoot r)
  | _, .app2 .at p i => .app2 .at (p.prefixRoot r) i
  | _, t => t

theorem Tm.prefixRoot_isFields (r : Name) : (p : Tm C Γ .path) → p.isFields = true →
    (p.prefixRoot r).isFields = true
  | .app0 (.root _), _ => rfl
  | .app1 (.field _) _ p, h => Tm.prefixRoot_isFields r p h
  | .pvP _, h | .app1 .next _ _, h | .app2 .at _ _, h | .app2 .nextIn _ _, h
  | .app3 .atIn _ _ _, h => nomatch h

/-- `r.p` resolves as the member path `p` does, one segment on. -/
theorem Tm.prefixRoot_eval {σ : State C Γ} (r : Name) : (p : Tm C Γ .path) → p.isFields = true →
    ∀ {f : Name} {segs : List Seg}, p.evalT σ = .ok (f, segs) →
      (p.prefixRoot r).evalT σ = .ok (r, .field f :: segs)
  | .app0 (.root g), _, f, segs, h => by
    have h' : ((g, []) : Name × List Seg) = (f, segs) := Except.ok.inj h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    rfl
  | .app1 (.field g) hg p, hf, f, segs, h => by
    rw [Tm.field_eval] at h
    cases hp : p.evalT σ with
    | error e => rw [hp] at h; cases h
    | ok fs =>
      obtain ⟨f', segs'⟩ := fs
      rw [hp] at h
      have h' : ((f', segs' ++ [Seg.field g]) : Name × List Seg) = (f, segs) := Except.ok.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      show (Tm.app1 (.field g) hg (p.prefixRoot r)).evalT σ = _
      rw [Tm.field_eval, Tm.prefixRoot_eval r p hf hp]
      rfl
  | .pvP _, hf, _, _, _ | .app1 .next _ _, hf, _, _, _ | .app2 .at _ _, hf, _, _, _
  | .app2 .nextIn _ _, hf, _, _, _ | .app3 .atIn _ _ _, hf, _, _, _ => nomatch hf

/-- The member path `p` under the frame `F`: `p` itself at the top, else
`F.p`, which resolves as `p` does in the frame.  `none` for a path through
an alias or an index, or at the `length` member, which an array could tell
apart from `p` in the frame (`Tm.base_eval`). -/
def Tm.under? (F : List Name) (p : Tm C Γ .path) : Option (Tm C Γ .path) :=
  match F with
  | [] => some p
  | _ :: _ =>
    if p.isFields && (p.rootName? != some "length") then
      some (F.foldr (fun r t => t.prefixRoot r) p)
    else none

/-- `F.p` resolves to `F`'s members, then `p`'s root and members. -/
theorem Tm.foldr_prefixRoot_eval {σ : State C Γ} (p : Tm C Γ .path) (hf : p.isFields = true)
    {f : Name} {segs : List Seg} (hp : p.evalT σ = .ok (f, segs)) :
    (F : List Name) → ∃ r rest, (F.foldr (fun r t => t.prefixRoot r) p).evalT σ = .ok (r, rest) ∧
      (Seg.field r :: rest) = F.map Seg.field ++ (Seg.field f :: segs)
  | [] => ⟨f, segs, hp, rfl⟩
  | r :: F => by
    obtain ⟨r', rest', h, e⟩ := Tm.foldr_prefixRoot_eval p hf hp F
    have hf' : (F.foldr (fun r t => t.prefixRoot r) p).isFields = true := by
      clear h e
      induction F with
      | nil => exact hf
      | cons r F ih => exact Tm.prefixRoot_isFields r _ ih
    refine ⟨r, .field r' :: rest', ?_, ?_⟩
    · exact Tm.prefixRoot_eval r _ hf' h
    · simp only [List.map_cons, List.cons_append, e]

/-- A storage term read member-wise, as the term it reads and the frame it
reads it in: `save(select(s, r), p, v)` reads `save(s, r.p, v)` in the frame
`[r]`; `s` alone reads itself at the top.  Generic in the sort. -/
def Tm.baseAny : {u : Srt} → Tm C Γ u → Option (Tm C Γ u × List Name)
  | _, .app1 (.select r) _ s => s.baseAny.map fun bF => (bF.1, bF.2 ++ [r])
  | _, .app3 .save s p v =>
    s.baseAny.bind fun bF => (Tm.under? bF.2 p).map fun p' => (.app3 .save bF.1 p' v, bF.2)
  | _, .app2 .delAt s p =>
    s.baseAny.bind fun bF => (Tm.under? bF.2 p).map fun p' => (.app2 .delAt bF.1 p', bF.2)
  | _, s => some (s, [])

/-- A read, member-wise, as the read it is: `find(select(s, r), p)` is
`find(s, r.p)`. -/
def Tm.base? : Tm C Γ .val → Option (Tm C Γ .val)
  | .app2 .find s q => s.baseAny.bind fun bF => (Tm.under? bF.2 q).map fun q' => .app2 .find bF.1 q'
  | _ => none

/-- A member path's root. -/
theorem Tm.rootName?_eval {σ : State C Γ} : (p : Tm C Γ .path) → p.isFields = true →
    ∀ {f : Name} {segs : List Seg}, p.evalT σ = .ok (f, segs) → p.rootName? = some f
  | .app0 (.root g), _, f, segs, h => by
    have h' : ((g, []) : Name × List Seg) = (f, segs) := Except.ok.inj h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, -⟩ := h'
    rfl
  | .app1 (.field g) _ p, hf, f, segs, h => by
    rw [Tm.field_eval] at h
    cases hp : p.evalT σ with
    | error e => rw [hp] at h; cases h
    | ok fs =>
      obtain ⟨f', segs'⟩ := fs
      rw [hp] at h
      have h' : ((f', segs' ++ [Seg.field g]) : Name × List Seg) = (f, segs) := Except.ok.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, -⟩ := h'
      exact Tm.rootName?_eval p hf hp
  | .pvP _, hf, _, _, _ | .app1 .next _ _, hf, _, _, _ | .app2 .at _ _, hf, _, _, _
  | .app2 .nextIn _ _, hf, _, _, _ | .app3 .atIn _ _ _, hf, _, _, _ => nomatch hf

/-- The frame `F` of `F.p` and `p`: where `p` resolves, `F.p` resolves to the
frame's members, then `p`'s. -/
theorem Tm.under?_eval {σ : State C Γ} {r₁ : Name} {F' : List Name} {p p' : Tm C Γ .path}
    (h : Tm.under? (r₁ :: F') p = some p') :
    ∃ g segs, p.evalT σ = .ok (g, segs) ∧ g ≠ "length" ∧
      p'.evalT σ = .ok (r₁, F'.map Seg.field ++ (.field g :: segs)) := by
  simp only [Tm.under?] at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    obtain ⟨hf, hl⟩ := hc
    obtain ⟨g, segs, hpe, -⟩ := Tm.isFields_eval σ p hf
    have hroot := Tm.rootName?_eval p hf hpe
    refine ⟨g, segs, hpe, fun e => hl (by rw [hroot, e]), ?_⟩
    obtain ⟨r, rest, hp'e, he⟩ := Tm.foldr_prefixRoot_eval p hf hpe (r₁ :: F')
    simp only [List.map_cons, List.cons_append, List.cons.injEq, Seg.field.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hp'e
  · nomatch h

/-- **A storage term read member-wise runs as the term it reads, in its
frame**. -/
theorem Tm.baseAny_eval : (s : Tm C Γ .st) → {b : Tm C Γ .st} → {F : List Name} →
    s.baseAny = some (b, F) → ∀ σ : State C Γ, Res.OkEq (s.evalT σ) (b.evalT σ >>= State.frameOf F)
  | .app1 (.select r) hr s, b, F, h, σ => by
    simp only [Tm.baseAny, Option.map_eq_some_iff] at h
    obtain ⟨⟨b₀, F₀⟩, hb, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [Tm.select_eval]
    refine Res.OkEq.trans (Res.OkEq.bind (Tm.baseAny_eval s hb σ) fun _ => Res.OkEq.refl _) ?_
    rw [Res.bind_assoc]
    refine Res.OkEq.of_eq (congrArg _ (funext fun τ => ?_))
    rw [State.frameOf_append]
    simp only [State.frameOf, Res.bind_pure_ok]
  | .app3 .save s p v, b, F, h, σ => by
    simp only [Tm.baseAny, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨b₀, F₀⟩, hb, p', hp, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have ih := Tm.baseAny_eval s hb σ
    rw [Tm.save_eval, Tm.save_eval]
    cases F₀ with
    | nil =>
      simp only [Tm.under?, Option.some.injEq] at hp
      subst hp
      simp only [State.frameOf, Res.bind_pure_ok] at ih ⊢
      exact Res.OkEq.bind (Res.OkEq.refl _) fun sv => Res.OkEq.bind ih fun τ => Res.OkEq.refl _
    | cons r₁ F' =>
      obtain ⟨g, segs, hpe, -, hp'e⟩ := Tm.under?_eval (σ := σ) hp
      rw [hpe, hp'e]
      simp only [Res.ok_bind', Res.bind_assoc]
      refine Res.OkEq.bind (Res.OkEq.refl _) fun sv => ?_
      refine Res.OkEq.trans (Res.OkEq.bind ih fun _ => Res.OkEq.refl _) ?_
      simp only [Res.bind_assoc]
      refine Res.OkEq.bind (Res.OkEq.refl _) fun τb => ?_
      exact (State.frameOf_writeStorage r₁ g segs sv F' τb).symm
  | .app2 .delAt s p, b, F, h, σ => by
    simp only [Tm.baseAny, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨b₀, F₀⟩, hb, p', hp, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have ih := Tm.baseAny_eval s hb σ
    rw [Tm.delAt_eval, Tm.delAt_eval]
    cases F₀ with
    | nil =>
      simp only [Tm.under?, Option.some.injEq] at hp
      subst hp
      simp only [State.frameOf, Res.bind_pure_ok] at ih ⊢
      exact Res.OkEq.bind ih fun τ => Res.OkEq.refl _
    | cons r₁ F' =>
      obtain ⟨g, segs, hpe, -, hp'e⟩ := Tm.under?_eval (σ := σ) hp
      rw [hpe, hp'e]
      simp only [Res.ok_bind', Res.bind_assoc]
      refine Res.OkEq.trans (Res.OkEq.bind ih fun _ => Res.OkEq.refl _) ?_
      simp only [Res.bind_assoc]
      refine Res.OkEq.bind (Res.OkEq.refl _) fun τb => ?_
      exact (State.frameOf_delAtAt r₁ g segs F' τb).symm
  | .pvS _, b, F, h, σ | .app0 _, b, F, h, σ | .app2 (.pushSlot _) _ _, b, F, h, σ
  | .app2 .pop _ _, b, F, h, σ | .app2 .shrink _ _, b, F, h, σ | .app2 (.extend _) _ _, b, F, h, σ
  | .app3 .push _ _ _, b, F, h, σ => by
    simp only [Tm.baseAny, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [State.frameOf, Res.bind_pure_ok]
    exact Res.OkEq.refl _

/-- **A read, member-wise, returns where the read it is returns**, the same
value. -/
theorem Tm.base_eval : (t : Tm C Γ .val) → {t' : Tm C Γ .val} → t.base? = some t' →
    ∀ σ : State C Γ, Res.OkEq (t.evalT σ) (t'.evalT σ)
  | .app2 .find s q, t', h, σ => by
    simp only [Tm.base?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨b, F⟩, hb, q', hq, rfl⟩ := h
    have ih := Tm.baseAny_eval s hb σ
    rw [Tm.find_eval, Tm.find_eval]
    cases F with
    | nil =>
      simp only [Tm.under?, Option.some.injEq] at hq
      subst hq
      simp only [State.frameOf, Res.bind_pure_ok] at ih
      exact Res.OkEq.bind ih fun τ => Res.OkEq.refl _
    | cons r₁ F' =>
      obtain ⟨g, segs, hqe, hg, hq'e⟩ := Tm.under?_eval (σ := σ) hq
      rw [hqe, hq'e]
      simp only [Res.ok_bind']
      refine Res.OkEq.trans (Res.OkEq.bind ih fun _ => Res.OkEq.refl _) ?_
      simp only [Res.bind_assoc]
      refine Res.OkEq.bind (Res.OkEq.refl _) fun τb => ?_
      rw [← Res.bind_assoc]
      exact Res.OkEq.bind (State.frameOf_findStorage r₁ g segs hg F' τb) fun _ => Res.OkEq.refl _
  | .pvV _, _, h, _ | .netOf _ _, _, h, _ | .app0 _, _, h, _ | .app1 _ _ _, _, h, _
  | .app3 _ _ _ _, _, h, _ | .app2 (.binop _ _) _ _, _, h, _ | .app2 .len _ _, _, h, _
  | .app2 .read _ _, _, h, _ | .app2 .mlen _ _, _, h, _ => nomatch h

/-- The two value terms are one read member-wise: they have one base
(`Tm.base?`), compared by `Tm.beqR`. -/
def Tm.sameBase (t t' : Tm C Γ .val) : Bool :=
  match t.base?, t'.base? with
  | some b, some b' => b.beqR b'
  | _, _ => false

/-- **Two member-wise forms of one read return alike**: where one returns,
the other returns the same value, in every state.  Not equal outcomes: a
read in a frame and the read outside it may halt differently. -/
theorem Tm.sameBase_eval {t t' : Tm C Γ .val} (h : Tm.sameBase t t' = true) (σ : State C Γ) :
    Res.OkEq (t.evalT σ) (t'.evalT σ) := by
  unfold Tm.sameBase at h
  split at h
  · rename_i b b' hb hb'
    obtain rfl := Tm.eq_of_beqR h
    exact (Tm.base_eval t hb σ).trans (Tm.base_eval t' hb' σ).symm
  · nomatch h

/-- A save read member-wise returns where the save it reads returns. -/
theorem Tm.save_returns_of_base {s : Tm C Γ .st} {p : Tm C Γ .path} {v : Tm C Γ .sv}
    {b : Tm C Γ .st} {F : List Name} (h : (Tm.app3 .save s p v).baseAny = some (b, F))
    {σ : State C Γ} {τ₁ : Semantics.State} (hb : b.evalT σ = .ok τ₁) :
    ∃ τ, (Tm.app3 .save s p v).evalT σ = .ok τ := by
  have e := Tm.baseAny_eval _ h σ
  have h' := h
  simp only [Tm.baseAny, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h'
  obtain ⟨⟨b₀, F₀⟩, -, p', hp, he⟩ := h'
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hres : ∃ τ, ((Tm.app3 .save b₀ p' v).evalT σ >>= State.frameOf F₀) = .ok τ := by
    rw [hb, Res.ok_bind']
    cases F₀ with
    | nil => exact ⟨τ₁, rfl⟩
    | cons r₁ F' =>
      obtain ⟨g, segs, -, -, hp'e⟩ := Tm.under?_eval (σ := σ) hp
      rw [Tm.save_eval] at hb
      obtain ⟨sv, -, hb⟩ := bind_ok_inv hb
      obtain ⟨τb, -, hb⟩ := bind_ok_inv hb
      rw [hp'e] at hb
      simp only [Res.ok_bind'] at hb
      exact State.frameOf_of_writeStorage hb
  obtain ⟨τ, hτ⟩ := hres
  exact ⟨τ, (e τ).2 hτ⟩

/-- A delete read member-wise returns where the delete it reads returns. -/
theorem Tm.delAt_returns_of_base {s : Tm C Γ .st} {p : Tm C Γ .path} {b : Tm C Γ .st}
    {F : List Name} (h : (Tm.app2 .delAt s p).baseAny = some (b, F)) {σ : State C Γ}
    {τ₁ : Semantics.State} (hb : b.evalT σ = .ok τ₁) :
    ∃ τ, (Tm.app2 .delAt s p).evalT σ = .ok τ := by
  have e := Tm.baseAny_eval _ h σ
  have h' := h
  simp only [Tm.baseAny, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h'
  obtain ⟨⟨b₀, F₀⟩, -, p', hp, he⟩ := h'
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hres : ∃ τ, ((Tm.app2 .delAt b₀ p').evalT σ >>= State.frameOf F₀) = .ok τ := by
    rw [hb, Res.ok_bind']
    cases F₀ with
    | nil => exact ⟨τ₁, rfl⟩
    | cons r₁ F' =>
      obtain ⟨g, segs, -, -, hp'e⟩ := Tm.under?_eval (σ := σ) hp
      rw [Tm.delAt_eval] at hb
      obtain ⟨τb, -, hb⟩ := bind_ok_inv hb
      rw [hp'e] at hb
      simp only [Res.ok_bind'] at hb
      exact State.frameOf_of_delAtAt hb
  obtain ⟨τ, hτ⟩ := hres
  exact ⟨τ, (e τ).2 hτ⟩

/-! ## The storage writes an update holds -/

/-- `U` writes the storage with a term on whose spine the write `w` reads
member-wise lies (`Tm.baseAny`): `w` returns wherever `U` does. -/
def Upd.holdsWrite {Δ : Ctx} (U : Upd C Γ Δ) (w : Tm C Γ .st) : Bool :=
  match w.baseAny with
  | some (b, _) => U.storTerms.any (·.onSpine b)
  | none => false

theorem Upd.holdsWrite_eval {Δ : Ctx} {U : Upd C Γ Δ} {w : Tm C Γ .st} (h : U.holdsWrite w = true)
    {σ : State C Γ} {τ : Semantics.State} (hU : U.globT σ = .ok τ) :
    ∃ b F, w.baseAny = some (b, F) ∧ ∃ τ₁ : Semantics.State, b.evalT σ = .ok τ₁ := by
  unfold Upd.holdsWrite at h
  split at h
  · rename_i b F hb
    obtain ⟨S, hS, hs⟩ := List.any_eq_true.1 h
    obtain ⟨τ', hS'⟩ := Upd.storage_eval_of_globT hU hS
    refine ⟨b, F, hb, ?_⟩
    cases hbe : b.evalT σ with
    | ok τ₁ => exact ⟨τ₁, rfl⟩
    | error e' =>
      obtain ⟨e'', hS''⟩ := Tm.onSpine_error hbe S hs
      rw [hS''] at hS'
      cases hS'
  · nomatch h

/-- `U` returns only where the rewrite `q` is exact: `q.1` reads back a
storage write `U` holds (`Upd.holdsWrite`) — `find(save(s, p, v), p)` over
`storage := save(s, p, v)`, or a word at or below a deleted node where the
storage deleted writes the word at the path read (`Tm.findLit?`), over
`storage := delAt(s, p)` — each read member-wise too — so `q.1` returns
wherever `U` does.  Syntactic, so that `rfl` decides it. -/
def Upd.covers {Δ : Ctx} (U : Upd C Γ Δ) : Tm C Γ .val × Tm C Γ .val → Bool
  | (.app2 .find (.app3 .save s p (.app1 .sval h (.app0 (.lit v)))) p', _) =>
    p'.beqR p && U.holdsWrite (.app3 .save s p (.app1 .sval h (.app0 (.lit v))))
  | (.app2 .find (.app2 .delAt s p) q, _) =>
    U.holdsWrite (.app2 .delAt s p) && q.atOrBelow p && (s.findLit? q).isSome
  | _ => false

/-- Where the update returns, the term a covered rewrite replaces returns. -/
theorem Upd.covers_eval {Δ : Ctx} {q : Tm C Γ .val × Tm C Γ .val} {U : Upd C Γ Δ}
    (hc : U.covers q = true) {σ : State C Γ} {τ : Semantics.State} (hU : U.globT σ = .ok τ) :
    ∃ y, q.1.evalT σ = .ok y := by
  unfold Upd.covers at hc
  split at hc
  · rename_i s p hv v p' t'
    simp only [Bool.and_eq_true] at hc
    obtain ⟨hpp, hw⟩ := hc
    obtain rfl := Tm.eq_of_beqR hpp
    obtain ⟨b, F, hb, τ₁, hbe⟩ := Upd.holdsWrite_eval hw hU
    obtain ⟨τ', hs⟩ := Tm.save_returns_of_base hb hbe
    obtain ⟨r, segs, hp, hf⟩ := Tm.save_lit_eval hs
    refine ⟨v, ?_⟩
    rw [Tm.find_eval, hs, hp]
    simp only [bind, Except.bind, hf]
    cases v <;> rfl
  · rename_i s p q' t'
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hc
    obtain ⟨⟨hwr, hb⟩, w, hw⟩ := hc
    obtain ⟨b, F, hbase, τ₁, hbe⟩ := Upd.holdsWrite_eval hwr hU
    obtain ⟨τ'', hd⟩ := Tm.delAt_returns_of_base hbase hbe
    exact Tm.delAtBelow_eval hb hw hd
  · nomatch hc

/-- **Where the update returns, a covered rewrite is exact**: its
replacement returns what the replaced term returns. -/
theorem Upd.covers_le {Δ : Ctx} {q : Tm C Γ .val × Tm C Γ .val}
    (hq : ∀ σ : State C Γ, Res.Le (q.1.evalT σ) (q.2.evalT σ)) {U : Upd C Γ Δ}
    (hc : U.covers q = true) {σ : State C Γ} {τ : Semantics.State} (hU : U.globT σ = .ok τ) :
    Res.Le (q.2.evalT σ) (q.1.evalT σ) := fun x hx => by
  obtain ⟨y, hy⟩ := Upd.covers_eval hc hU
  rw [hq σ y hy] at hx
  obtain rfl := Except.ok.inj hx
  exact hy

/-! ## The frame and delete-value laws

The frame and delete-value laws may leave a storage read on their right.
That read is not total, but once the update returns its storage operation
has returned, and the two sides then evaluate identically. -/

section RefEval

variable {σ : State C Γ}

/-- A length read away from a returned write evaluates as the read before
the write. -/
theorem Tm.len_save_frame_eval {s : Tm C Γ .st} {q p : Tm C Γ .path} {v : Tm C Γ .sv}
    {τ : Semantics.State} (hd : q.divergesLen p = true) (he : (Tm.app3 .save s q v).evalT σ = .ok τ) :
    (Tm.app2 .len (.app3 .save s q v) p).evalT σ = (Tm.app2 .len s p).evalT σ := by
  have hterm := he
  rw [Tm.save_eval] at he
  obtain ⟨sv, -, he⟩ := bind_ok_inv he
  obtain ⟨τs, hs, he⟩ := bind_ok_inv he
  obtain ⟨⟨r, segs⟩, hq, hsave⟩ := bind_ok_inv he
  obtain ⟨x, hsave'⟩ := State.writeStorage_ok hsave
  rw [Tm.len_eval, Tm.len_eval, hterm, hs, Res.ok_bind', Res.ok_bind']
  cases hp : p.evalT σ with
  | error _ => rfl
  | ok rp =>
    obtain ⟨r', segs'⟩ := rp
    simp only [bind, Except.bind]
    rw [Close.arrayLen_saveStorage_frame hsave' (Tm.divergesLen_eval hd hq hp)]

/-- A length read away from a returned delete evaluates as the read before
the delete. -/
theorem Tm.len_delAt_frame_eval {s : Tm C Γ .st} {q p : Tm C Γ .path} {τ : Semantics.State}
    (hd : q.divergesLen p = true) (he : (Tm.app2 .delAt s q).evalT σ = .ok τ) :
    (Tm.app2 .len (.app2 .delAt s q) p).evalT σ = (Tm.app2 .len s p).evalT σ := by
  have hterm := he
  rw [Tm.delAt_eval] at he
  obtain ⟨τs, hs, he⟩ := bind_ok_inv he
  obtain ⟨⟨r, segs⟩, hq, he⟩ := bind_ok_inv he
  unfold State.delAtAt at he
  obtain ⟨cur, -, hsave⟩ := bind_ok_inv he
  rw [Tm.len_eval, Tm.len_eval, hterm, hs, Res.ok_bind', Res.ok_bind']
  cases hp : p.evalT σ with
  | error _ => rfl
  | ok rp =>
    obtain ⟨r', segs'⟩ := rp
    simp only [bind, Except.bind]
    rw [Close.arrayLen_saveStorage_frame hsave (Tm.divergesLen_eval hd hq hp)]

/-- A read away from a returned delete evaluates as the read before the
delete. -/
theorem Tm.find_delAt_frame_eval {s : Tm C Γ .st} {p q : Tm C Γ .path} {τ : Semantics.State}
    (hd : p.diverges q = true) (he : (Tm.app2 .delAt s p).evalT σ = .ok τ) :
    (Tm.app2 .find (.app2 .delAt s p) q).evalT σ = (Tm.app2 .find s q).evalT σ := by
  have hterm := he
  rw [Tm.delAt_eval] at he
  obtain ⟨τs, hs, he⟩ := bind_ok_inv he
  obtain ⟨⟨r, segs⟩, hp, he⟩ := bind_ok_inv he
  unfold State.delAtAt at he
  obtain ⟨cur, -, hsave⟩ := bind_ok_inv he
  rw [Tm.find_eval, Tm.find_eval, hterm, hs, Res.ok_bind', Res.ok_bind']
  cases hq : q.evalT σ with
  | error _ => rfl
  | ok rq =>
    obtain ⟨r', segs'⟩ := rq
    simp only [bind, Except.bind]
    rw [Close.findStorage_saveStorage_apart hsave (Tm.diverges_eval hd hp hq)]

/-- A read away from a returned write evaluates as the read before the
write. -/
theorem Tm.find_save_frame_eval {s : Tm C Γ .st} {p q : Tm C Γ .path} {v : Tm C Γ .sv}
    {τ : Semantics.State} (hd : p.diverges q = true) (he : (Tm.app3 .save s p v).evalT σ = .ok τ) :
    (Tm.app2 .find (.app3 .save s p v) q).evalT σ = (Tm.app2 .find s q).evalT σ := by
  have hterm := he
  rw [Tm.save_eval] at he
  obtain ⟨sv, -, he⟩ := bind_ok_inv he
  obtain ⟨τs, hs, he⟩ := bind_ok_inv he
  obtain ⟨⟨r, segs⟩, hp, hsave⟩ := bind_ok_inv he
  obtain ⟨x, hsave'⟩ := State.writeStorage_ok hsave
  rw [Tm.find_eval, Tm.find_eval, hterm, hs, Res.ok_bind', Res.ok_bind']
  cases hq : q.evalT σ with
  | error _ => rfl
  | ok rq =>
    obtain ⟨r', segs'⟩ := rq
    simp only [bind, Except.bind]
    rw [Close.findStorage_saveStorage_apart hsave' (Tm.diverges_eval hd hp hq)]

/-- A read at a returned delete evaluates as the primitive default of the
word before the delete, even when its path carries another check. -/
theorem Tm.find_delAt_value_eval {s : Tm C Γ .st} {p q : Tm C Γ .path} {τ : Semantics.State}
    {h : (Op1.delValue).named = false}
    (heq : p.sameSegs q = true) (he : (Tm.app2 .delAt s p).evalT σ = .ok τ) :
    (Tm.app2 .find (.app2 .delAt s p) q).evalT σ =
      (Tm.app1 .delValue h (.app2 .find s q)).evalT σ := by
  have hterm := he
  rw [Tm.delAt_eval] at he
  obtain ⟨τs, hs, he⟩ := bind_ok_inv he
  obtain ⟨⟨r, segs⟩, hp, he⟩ := bind_ok_inv he
  unfold State.delAtAt at he
  obtain ⟨cur, hcur, hsave⟩ := bind_ok_inv he
  show _ = (do pure (Theory.StValue.primDefault (← (Tm.app2 .find s q).evalT σ)))
  rw [Tm.find_eval, Tm.find_eval, hterm, hs, Res.ok_bind', Res.ok_bind']
  cases hq : q.evalT σ with
  | error _ => rfl
  | ok rq =>
    obtain ⟨r', segs'⟩ := rq
    obtain ⟨rfl, rfl⟩ := Tm.sameSegs_eval heq hp hq
    simp only [bind, Except.bind]
    rw [State.findStorage_saveStorage_same hsave, hcur]
    change cur.defaultOf.asValue = (do pure (Theory.StValue.primDefault (← cur.asValue)))
    exact SVal.defaultOf_asValue_primDefault cur

end RefEval

/-- The storage laws whose two sides evaluate alike once their storage
operation returns.  These are the laws that may
rewrite a covered update under either modality though their right side is
not total. -/
inductive TermTaclet.RefLaw : {t t' : Tm C Γ .val} → TermTaclet t t' → Prop where
  | findOnSaveFrame {s : Tm C Γ .st} {p q : Tm C Γ .path} {v : Tm C Γ .sv}
      (hd : p.diverges q = true := by rfl) :
      RefLaw (TermTaclet.findOnSaveFrame (s := s) (p := p) (q := q) (v := v) hd)
  | findOnDelAtValue {s : Tm C Γ .st} {p q : Tm C Γ .path} (hp : p.hasSeg = true := by rfl)
      (hq : p.sameSegs q = true := by first | rfl | exact Tm.sameSegs_refl _) :
      RefLaw (TermTaclet.findOnDelAtValue (s := s) (p := p) (q := q) hp hq)
  | findOnDelAtFrame {s : Tm C Γ .st} {p q : Tm C Γ .path} (hd : p.diverges q = true := by rfl) :
      RefLaw (TermTaclet.findOnDelAtFrame (s := s) (p := p) (q := q) hd)
  | lenOnSaveFrame {s : Tm C Γ .st} {q p : Tm C Γ .path} {v : Tm C Γ .sv}
      (hd : q.divergesLen p = true := by rfl) :
      RefLaw (TermTaclet.lenOnSaveFrame (s := s) (q := q) (p := p) (v := v) hd)
  | lenOnDelAtFrame {s : Tm C Γ .st} {q p : Tm C Γ .path} (hd : q.divergesLen p = true := by rfl) :
      RefLaw (TermTaclet.lenOnDelAtFrame (s := s) (q := q) (p := p) hd)

/-- **A reference law keeps every value its left side returns.** -/
theorem TermTaclet.RefLaw.evalRefines {t t' : Tm C Γ .val} {r : TermTaclet t t'} :
    RefLaw r → Tm.EvalRefinesAt t t'
  | .findOnSaveFrame hd => fun σ x hx => by
      have hx' := hx
      rw [Tm.find_eval] at hx
      obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
      rw [Tm.find_save_frame_eval hd hτ] at hx'
      exact hx'
  | .findOnDelAtValue _ hq => fun σ x hx => by
      have hx' := hx
      rw [Tm.find_eval] at hx
      obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
      rw [Tm.find_delAt_value_eval hq hτ] at hx'
      exact hx'
  | .findOnDelAtFrame hd => fun σ x hx => by
      have hx' := hx
      rw [Tm.find_eval] at hx
      obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
      rw [Tm.find_delAt_frame_eval hd hτ] at hx'
      exact hx'
  | .lenOnSaveFrame hd => fun σ x hx => by
      have hx' := hx
      rw [Tm.len_eval] at hx
      obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
      rw [Tm.len_save_frame_eval hd hτ] at hx'
      exact hx'
  | .lenOnDelAtFrame hd => fun σ x hx => by
      have hx' := hx
      rw [Tm.len_eval] at hx
      obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
      rw [Tm.len_delAt_frame_eval hd hτ] at hx'
      exact hx'

/-- A covered reference law's storage operation is held by the update. -/
def Upd.coversRef {Δ : Ctx} (U : Upd C Γ Δ) : Tm C Γ .val × Tm C Γ .val → Bool
  | (.app2 .find (.app3 .save s p v) _, _) => U.holdsWrite (.app3 .save s p v)
  | (.app2 .find (.app2 .delAt s p) _, _) => U.holdsWrite (.app2 .delAt s p)
  | (.app2 .len (.app3 .save s p v) _, _) => U.holdsWrite (.app3 .save s p v)
  | (.app2 .len (.app2 .delAt s p) _, _) => U.holdsWrite (.app2 .delAt s p)
  | _ => false

/-- **Wherever a covered update returns, a reference law refines back.** -/
theorem TermTaclet.RefLaw.back {t t' : Tm C Γ .val} {r : TermTaclet t t'} (hr : RefLaw r)
    {Δ : Ctx} {U : Upd C Γ Δ} (hc : U.coversRef (t, t') = true) {σ : State C Γ}
    {τ : Semantics.State} (hU : U.globT σ = .ok τ) : Res.Le (t'.evalT σ) (t.evalT σ) := by
  cases hr with
  | findOnSaveFrame hd =>
      simp only [Upd.coversRef] at hc
      obtain ⟨b, F, hb, τ₁, hbe⟩ := Upd.holdsWrite_eval hc hU
      obtain ⟨τ', hs⟩ := Tm.save_returns_of_base hb hbe
      rw [Tm.find_save_frame_eval hd hs]
      exact Res.Le.refl _
  | findOnDelAtValue _ hq =>
      simp only [Upd.coversRef] at hc
      obtain ⟨b, F, hb, τ₁, hbe⟩ := Upd.holdsWrite_eval hc hU
      obtain ⟨τ', hs⟩ := Tm.delAt_returns_of_base hb hbe
      rw [Tm.find_delAt_value_eval hq hs]
      exact Res.Le.refl _
  | findOnDelAtFrame hd =>
      simp only [Upd.coversRef] at hc
      obtain ⟨b, F, hb, τ₁, hbe⟩ := Upd.holdsWrite_eval hc hU
      obtain ⟨τ', hs⟩ := Tm.delAt_returns_of_base hb hbe
      rw [Tm.find_delAt_frame_eval hd hs]
      exact Res.Le.refl _
  | lenOnSaveFrame hd =>
      simp only [Upd.coversRef] at hc
      obtain ⟨b, F, hb, τ₁, hbe⟩ := Upd.holdsWrite_eval hc hU
      obtain ⟨τ', hs⟩ := Tm.save_returns_of_base hb hbe
      rw [Tm.len_save_frame_eval hd hs]
      exact Res.Le.refl _
  | lenOnDelAtFrame hd =>
      simp only [Upd.coversRef] at hc
      obtain ⟨b, F, hb, τ₁, hbe⟩ := Upd.holdsWrite_eval hc hU
      obtain ⟨τ', hs⟩ := Tm.delAt_returns_of_base hb hbe
      rw [Tm.len_delAt_frame_eval hd hs]
      exact Res.Le.refl _

/-! ## The laws of memory reads

A memory read (`read`, `copyMem`, `copySt`) denotes its run (`Op2.opaque`),
so a law of one is no Theory equation (`TermTaclet`) but a refinement of the
interpreter: where the read returns, its replacement returns the same
(`Tm.EvalRefinesAt`, `EvalLaw.sound`).  Inside an update over any modality
the replacement may halt where the read did not, so the update has to hold
the write the law reads back (`Upd.coversEval`, as `Upd.covers` for the
storage laws): then the two return alike wherever the update returns
(`EvalLaw.back`). -/

section MemEval

variable (σ : State C Γ)

theorem Tm.lit_eval (v : Value) : (Tm.lit v : Tm C Γ .val).evalT σ = .ok v := rfl
theorem Tm.read_eval (m : Tm C Γ .mem) (a : Tm C Γ .addr) : (Tm.app2 .read m a).evalT σ = (do
    let τ ← m.evalT σ
    let ad ← a.evalT σ
    (← readAddr τ ad).asValue) := rfl
theorem Tm.write_eval (m : Tm C Γ .mem) (a : Tm C Γ .addr) (v : Tm C Γ .mv) :
    (Tm.app3 .write m a v).evalT σ = (do
      let mv ← v.evalT σ
      let τ ← m.evalT σ
      let ad ← a.evalT σ
      writeAddr τ mv ad) := rfl
theorem Tm.mval_eval (t : Tm C Γ .val) (h : (Op1.mval).named = false) :
    (Tm.app1 .mval h t).evalT σ = (do pure (← t.evalT σ).toMVal) := rfl
theorem Tm.copyMem_eval (m : Tm C Γ .mem) (i : Tm C Γ .ident) : (Tm.app2 .copyMem m i).evalT σ = (do
    let τ ← m.evalT σ
    let id ← i.evalT σ
    Semantics.copyMem τ (.ref id)) := rfl
theorem Tm.copySt_eval (m : Tm C Γ .mem) (v : Tm C Γ .sv) : (Tm.app2 .copySt m v).evalT σ = (do
    let sv ← v.evalT σ
    let τ ← m.evalT σ
    return (← copyStToM τ sv).1) := rfl
theorem Tm.copy_eval (m : Tm C Γ .mem) (v : Tm C Γ .sv) : (Tm.app2 .copy m v).evalT σ = (do
    let sv ← v.evalT σ
    let τ ← m.evalT σ
    (← copyStToM τ sv).2.asRef) := rfl
theorem Tm.mfield_eval (i : Tm C Γ .ident) (f : Name) (h : (Op1.mfield f).named = false) :
    (Tm.app1 (.mfield f) h i).evalT σ = (do pure (.memoryField (← i.evalT σ) f)) := rfl
theorem Tm.sfind_eval (s : Tm C Γ .st) (p : Tm C Γ .path) : (Tm.app2 .sfind s p).evalT σ = (do
    let τ ← s.evalT σ
    let (r, segs) ← p.evalT σ
    τ.findStorage r segs) := rfl
theorem Tm.alloc_eval (m : Tm C Γ .mem) (R : RefTy) (h : (Op1.alloc R).named = false) :
    (Tm.app1 (.alloc R) h m).evalT σ = (do
      let τ ← m.evalT σ
      return (← allocDefault τ R).2) := rfl
theorem Tm.addM_eval (m : Tm C Γ .mem) (R : RefTy) (h : (Op1.addM R).named = false) :
    (Tm.app1 (.addM R) h m).evalT σ = (do
      let τ ← m.evalT σ
      return (← allocDefault τ R).1) := rfl
theorem Tm.iread_eval (m : Tm C Γ .mem) (a : Tm C Γ .addr) : (Tm.app2 .iread m a).evalT σ = (do
    let τ ← m.evalT σ
    let ad ← a.evalT σ
    (← readAddr τ ad).asRef) := rfl
theorem Tm.mat_eval (i : Tm C Γ .ident) (k : Tm C Γ .val) : (Tm.app2 .mat i k).evalT σ = (do
    let id ← i.evalT σ
    pure (.memoryIndex id (← (← k.evalT σ).asInt))) := rfl
theorem Tm.ref_eval (i : Tm C Γ .ident) (h : (Op1.ref).named = false) :
    (Tm.app1 .ref h i).evalT σ = (do pure (.ref (← i.evalT σ))) := rfl

end MemEval

/-! ### The side conditions of the memory laws

A read below a fresh allocation `addM(m, R)` resolves syntactically: the
path at which the address reads below the fresh root (`Tm.freshPath?`)
names the member, and the declared type at that path (`RefTy.memberTy`)
says what the default copy holds there (`copyStToM_default_readPath`).  A
read that does not look into the fresh object is one whose identity was
allocated strictly earlier on the memory spine (`Tm.boundedIn`), and a read
past a write at an address that never meets it (`Tm.apart?`).  Each is a
`Bool`, so that `rfl` decides it where a law is applied. -/

/-- The path at which a term reads below the root `addM(m, R)` allocates:
`freshId(addM(m, R))` is the root, `read(addM(m, R), i.f)` the member `f` of
what `i` reads, `i.f` and `i[k]` (a literal `k`) the path one step down.
Generic in the sort. -/
def Tm.freshPath? : {u : Srt} → Tm C Γ u → Tm C Γ .mem → RefTy → Option (List Seg)
  | _, .app1 (.alloc R') _ m', m, R => if m'.beqR m && R' == R then some [] else none
  | _, .app2 .iread M a, m, R =>
    if M.beqR (Tm.app1 (.addM R) rfl m) then a.freshPath? m R else none
  | _, .app1 (.mfield f) _ i, m, R => (i.freshPath? m R).map (· ++ [.field f])
  | _, .app2 .mat i (.app0 (.lit (.int k))), m, R => (i.freshPath? m R).map (· ++ [.at k])
  | _, _, _, _ => none

/-- What a term at a fresh path reads, by sort: an identity is what the path
reads in the fresh object, and it reads where the declared type is a
reference; an address reads what the path reads, and it reads where the
path is declared (`FreshRead`). -/
def Tm.FreshRead (σ : State C Γ) (μ₁ : Semantics.State) (root : Nat) (R : RefTy) (p : List Seg) :
    {u : Srt} → Tm C Γ u → Prop
  | .ident, t => (∀ id, t.evalT σ = .ok id → μ₁.readPath root p = .ok (.ref id)) ∧
      (∀ R', (Ty.ref R).memberTy p = some (.ref R') → ∃ id, t.evalT σ = .ok id)
  | .addr, t => (∀ ad, t.evalT σ = .ok ad → readAddr μ₁ ad = μ₁.readPath root p) ∧
      (∀ T', (Ty.ref R).memberTy p = some T' → ∃ ad, t.evalT σ = .ok ad)
  | _, _ => True

theorem Tm.freshPath_eval {m : Tm C Γ .mem} {R : RefTy} {σ : State C Γ}
    {μ₀ μ₁ : Semantics.State} {root : Nat}
    (hm : m.evalT σ = .ok μ₀) (ha : allocDefault μ₀ R = .ok (μ₁, root)) {u : Srt} (t : Tm C Γ u) :
    ∀ {p : List Seg}, t.freshPath? m R = some p → Tm.FreshRead σ μ₁ root R p t := by
  induction t with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ | app0 _ | app3 _ _ _ _ =>
    intro p h
    nomatch h
  | app1 o ho a ih =>
    intro p h
    cases o with
    | alloc R' =>
      simp only [Tm.freshPath?] at h
      split at h
      · rename_i hmR
        simp only [Bool.and_eq_true, beq_iff_eq] at hmR
        obtain ⟨hmm, rfl⟩ := hmR
        obtain rfl := Tm.eq_of_beqR hmm
        cases h
        refine ⟨fun id hid => ?_, fun R' _ => ?_⟩
        · rw [Tm.alloc_eval, hm, Res.ok_bind', ha] at hid
          cases hid
          rfl
        · exact ⟨root, by rw [Tm.alloc_eval, hm, Res.ok_bind', ha]; rfl⟩
      · nomatch h
    | mfield f =>
      simp only [Tm.freshPath?, Option.map_eq_some_iff] at h
      obtain ⟨p', hp', rfl⟩ := h
      obtain ⟨ih1, ih2⟩ := ih hp'
      refine ⟨fun ad had => ?_, fun T' hT' => ?_⟩
      · rw [Tm.mfield_eval] at had
        obtain ⟨id, hid, had⟩ := bind_ok_inv had
        simp only [pure, Except.pure, Except.ok.injEq] at had
        subst had
        have h1 : MVal.readPath μ₁ (.ref root) p' = .ok (.ref id) := ih1 id hid
        simp only [State.readPath, MVal.readPath_snoc, h1, Res.ok_bind']
        rfl
      · obtain ⟨R'', hR''⟩ := Ty.memberTy_snoc_some hT'
        obtain ⟨id, hid⟩ := ih2 R'' hR''
        exact ⟨_, by rw [Tm.mfield_eval, hid]; rfl⟩
    | _ => nomatch h
  | app2 o a b iha ihb =>
    intro p h
    cases o with
    | iread =>
      simp only [Tm.freshPath?] at h
      split at h
      · rename_i hM
        obtain rfl := Tm.eq_of_beqR hM
        obtain ⟨ih1, ih2⟩ := ihb h
        have hμ : (Tm.app1 (.addM R) rfl m).evalT σ = .ok μ₁ := by
          rw [Tm.addM_eval, hm, Res.ok_bind', ha]; rfl
        refine ⟨fun id hid => ?_, fun R' hR' => ?_⟩
        · rw [Tm.iread_eval, hμ, Res.ok_bind'] at hid
          obtain ⟨ad, had, hid⟩ := bind_ok_inv hid
          rw [ih1 ad had] at hid
          obtain ⟨mv, hmv, hid⟩ := bind_ok_inv hid
          cases mv with
          | prim _ => nomatch hid
          | ref id' =>
            simp only [MVal.asRef, pure, Except.pure, Except.ok.injEq] at hid
            subst hid
            exact hmv
        · obtain ⟨ad, had⟩ := ih2 _ hR'
          obtain ⟨mv', hmv', hd⟩ :=
            (copyStToM_default_readPath p (Close.allocDefault_copy ha) (State.HeapExt.refl μ₁)).2 _ hR'
          obtain ⟨id, rfl, -⟩ := hd
          refine ⟨id, ?_⟩
          rw [Tm.iread_eval, hμ, Res.ok_bind', had, Res.ok_bind', ih1 ad had]
          simp only [State.readPath]
          rw [hmv']
          rfl
      · nomatch h
    | mat =>
      cases b with
      | app0 o' =>
        cases o' with
        | lit v =>
          cases v with
          | int k =>
            simp only [Tm.freshPath?, Option.map_eq_some_iff] at h
            obtain ⟨p', hp', rfl⟩ := h
            obtain ⟨ih1, ih2⟩ := iha hp'
            refine ⟨fun ad had => ?_, fun T' hT' => ?_⟩
            · rw [Tm.mat_eval] at had
              obtain ⟨id, hid, had⟩ := bind_ok_inv had
              simp only [Tm.lit_eval, Res.ok_bind', Value.asInt, pure, Except.pure,
                Except.ok.injEq] at had
              subst had
              have h1 : MVal.readPath μ₁ (.ref root) p' = .ok (.ref id) := ih1 id hid
              simp only [State.readPath, MVal.readPath_snoc, h1, Res.ok_bind']
              rfl
            · obtain ⟨R'', hR''⟩ := Ty.memberTy_snoc_some hT'
              obtain ⟨id, hid⟩ := ih2 R'' hR''
              exact ⟨_, by rw [Tm.mat_eval, hid]; rfl⟩
          | bool _ => nomatch h
        | env _ => nomatch h
      | pvV _ | netOf _ _ | app1 _ _ _ | app2 _ _ _ | app3 _ _ _ _ => nomatch h
    | _ => nomatch h

/-- A memory term on the memory spine of `t` leaves a counter `t` only advances. -/
theorem Tm.onMemSpine_nextId_le {s : Tm C Γ .mem} {σ : State C Γ} {μs : Semantics.State}
    (hs : s.evalT σ = .ok μs) :
    (t : Tm C Γ .mem) → t.onMemSpine s = true → ∀ {μt : Semantics.State}, t.evalT σ = .ok μt →
      μs.nextId ≤ μt.nextId
  | .app1 (.addM R) _ a, h, μt, ht => by
    simp only [Tm.onMemSpine, Tm.memSpineAny, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain rfl := Tm.eq_of_beqR h
      rw [hs] at ht; cases ht; exact Nat.le_refl _
    · rw [Tm.addM_eval] at ht
      obtain ⟨τ, hτ, ht⟩ := bind_ok_inv ht
      obtain ⟨⟨μ', id⟩, hal, ht⟩ := bind_ok_inv ht
      cases ht
      exact Nat.le_trans (Tm.onMemSpine_nextId_le hs a h hτ) (allocDefault_nextId hal)
  | .app2 .copySt a v, h, μt, ht => by
    simp only [Tm.onMemSpine, Tm.memSpineAny, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain rfl := Tm.eq_of_beqR h
      rw [hs] at ht; cases ht; exact Nat.le_refl _
    · rw [Tm.copySt_eval] at ht
      obtain ⟨sv, -, ht⟩ := bind_ok_inv ht
      obtain ⟨τ, hτ, ht⟩ := bind_ok_inv ht
      obtain ⟨⟨μ', mv⟩, hc, ht⟩ := bind_ok_inv ht
      cases ht
      exact Nat.le_trans (Tm.onMemSpine_nextId_le hs a h hτ) (copyStToM_nextId τ sv _ _ hc)
  | .app3 .write a p v, h, μt, ht => by
    simp only [Tm.onMemSpine, Tm.memSpineAny, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain rfl := Tm.eq_of_beqR h
      rw [hs] at ht; cases ht; exact Nat.le_refl _
    · rw [Tm.write_eval] at ht
      obtain ⟨mv, -, ht⟩ := bind_ok_inv ht
      obtain ⟨τ, hτ, ht⟩ := bind_ok_inv ht
      obtain ⟨ad, -, ht⟩ := bind_ok_inv ht
      rw [Close.writeAddr_nextId ht]
      exact Tm.onMemSpine_nextId_le hs a h hτ
  | .app0 .memory, h, μt, ht => by
    simp only [Tm.onMemSpine, Tm.memSpineAny] at h
    obtain rfl := Tm.eq_of_beqR h
    rw [hs] at ht; cases ht; exact Nat.le_refl _

/-- The identity a term reads is allocated strictly earlier on `M`'s memory
spine: a root `freshId(addM(m₀, R₀))` or `freshId(copySt(m₀, v))` whose
allocation `M` performs, or a reference member of a fresh root read out of
that allocation; an address is bounded where its identity is.  Generic in
the sort. -/
def Tm.boundedIn : {u : Srt} → Tm C Γ u → Tm C Γ .mem → Bool
  | _, .app1 (.alloc R₀) _ m₀, M => M.onMemSpine (.app1 (.addM R₀) rfl m₀)
  | _, .app2 .copy m₀ v, M => M.onMemSpine (.app2 .copySt m₀ v)
  | _, .app2 .iread (.app1 (.addM R₀) _ m₀) (.app1 (.mfield _) _ i), M =>
    M.onMemSpine (.app1 (.addM R₀) rfl m₀) && (i.freshPath? m₀ R₀).isSome
  | _, .app2 .iread (.app1 (.addM R₀) _ m₀) (.app2 .mat i _), M =>
    M.onMemSpine (.app1 (.addM R₀) rfl m₀) && (i.freshPath? m₀ R₀).isSome
  | _, .app1 (.mfield _) _ i, M => i.boundedIn M
  | _, .app2 .mat i _, M => i.boundedIn M
  | _, _, _ => false

/-- What a bounded term reads, by sort: an identity below the counter `M`
leaves (`BoundedRead`). -/
def Tm.BoundedRead (σ : State C Γ) (μ : Semantics.State) : {u : Srt} → Tm C Γ u → Prop
  | .ident, t => ∀ id, t.evalT σ = .ok id → id < μ.nextId
  | .addr, t => ∀ ad, t.evalT σ = .ok ad → ad.id < μ.nextId
  | _, _ => True

/-- A reference member of a fresh root, read out of the allocation, is below
the counter the allocation leaves. -/
theorem Tm.freshRoot_read_lt {m₀ : Tm C Γ .mem} {R₀ : RefTy} {i : Tm C Γ .ident} {σ : State C Γ}
    {μ₁ : Semantics.State} (hp : (i.freshPath? m₀ R₀).isSome = true)
    (hμ : (Tm.app1 (.addM R₀) rfl m₀).evalT σ = .ok μ₁)
    {id₀ : Nat} (hi : i.evalT σ = .ok id₀) {s : Seg} {id : Nat}
    (hr : readAddr μ₁ (.ofSeg id₀ s) = .ok (.ref id)) : id < μ₁.nextId := by
  rw [Tm.addM_eval] at hμ
  obtain ⟨μ₀, hm, hμ⟩ := bind_ok_inv hμ
  obtain ⟨⟨μ₁', root⟩, ha, hμ⟩ := bind_ok_inv hμ
  cases hμ
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hp
  have h1 := (Tm.freshPath_eval hm ha i hp).1 id₀ hi
  have hpath : μ₁'.readPath root (p ++ [s]) = .ok (.ref id) := by
    simp only [State.readPath, MVal.readPath_snoc] at h1 ⊢
    rw [h1, Res.ok_bind']
    exact hr
  obtain ⟨T', -, hd⟩ :=
    (copyStToM_default_readPath (p ++ [s]) (Close.allocDefault_copy ha) (State.HeapExt.refl μ₁')).1 _ hpath
  cases T' with
  | prim q => cases q <;> simp only [DefaultMVal, Value.toMVal, PrimTy.default, reduceCtorEq] at hd
  | ref _ =>
    obtain ⟨id', hid', hlt⟩ := hd
    cases hid'
    exact hlt

theorem Tm.boundedIn_eval {M : Tm C Γ .mem} {σ : State C Γ} {μ : Semantics.State}
    (hM : M.evalT σ = .ok μ) {u : Srt} (t : Tm C Γ u) :
    t.boundedIn M = true → Tm.BoundedRead σ μ t := by
  induction t with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ | app0 _ | app3 _ _ _ _ =>
    intro h
    nomatch h
  | app1 o ho a ih =>
    intro h
    cases o with
    | alloc R₀ =>
      intro id hid
      simp only [Tm.boundedIn] at h
      rw [Tm.alloc_eval] at hid
      obtain ⟨μ₀, hm, hid⟩ := bind_ok_inv hid
      obtain ⟨⟨μ₁, id'⟩, ha, hid⟩ := bind_ok_inv hid
      cases hid
      have hμ₁ : (Tm.app1 (.addM R₀) rfl a).evalT σ = .ok μ₁ := by
        rw [Tm.addM_eval, hm, Res.ok_bind', ha]; rfl
      exact Nat.lt_of_lt_of_le (allocDefault_id_lt ha) (Tm.onMemSpine_nextId_le hμ₁ M h hM)
    | mfield f =>
      intro ad had
      simp only [Tm.boundedIn] at h
      rw [Tm.mfield_eval] at had
      obtain ⟨id, hi, had⟩ := bind_ok_inv had
      simp only [pure, Except.pure, Except.ok.injEq] at had
      subst had
      exact ih h id hi
    | _ => nomatch h
  | app2 o a b iha ihb =>
    intro h
    cases o with
    | copy =>
      intro id hid
      simp only [Tm.boundedIn] at h
      rw [Tm.copy_eval] at hid
      obtain ⟨sv, hv, hid⟩ := bind_ok_inv hid
      obtain ⟨μ₀, hm, hid⟩ := bind_ok_inv hid
      obtain ⟨⟨μ₁, mv⟩, hc, hid⟩ := bind_ok_inv hid
      cases mv with
      | prim _ => nomatch hid
      | ref id' =>
        simp only [MVal.asRef, pure, Except.pure, Except.ok.injEq] at hid
        subst hid
        have hμ₁ : (Tm.app2 .copySt a b).evalT σ = .ok μ₁ := by
          rw [Tm.copySt_eval, hv, Res.ok_bind', hm, Res.ok_bind', hc]; rfl
        exact Nat.lt_of_lt_of_le (copyStToM_ref_lt hc) (Tm.onMemSpine_nextId_le hμ₁ M h hM)
    | mat =>
      intro ad had
      simp only [Tm.boundedIn] at h
      rw [Tm.mat_eval] at had
      obtain ⟨id, hi, had⟩ := bind_ok_inv had
      obtain ⟨kv, -, had⟩ := bind_ok_inv had
      obtain ⟨kn, -, had⟩ := bind_ok_inv had
      simp only [pure, Except.pure, Except.ok.injEq] at had
      subst had
      exact iha h id hi
    | iread =>
      intro id hid
      cases a with
      | app1 o₁ ho₁ m₀ =>
        cases o₁ with
        | addM R₀ =>
          rw [Tm.iread_eval] at hid
          obtain ⟨μ₁, hμ₁, hid⟩ := bind_ok_inv hid
          obtain ⟨ad, had, hid⟩ := bind_ok_inv hid
          obtain ⟨mv, hmv, hid⟩ := bind_ok_inv hid
          cases mv with
          | prim _ => nomatch hid
          | ref id' =>
            simp only [MVal.asRef, pure, Except.pure, Except.ok.injEq] at hid
            subst hid
            cases b with
            | app0 o₀ => nomatch o₀
            | app3 o₃ _ _ _ => nomatch o₃
            | app1 o₂ ho₂ i =>
              cases o₂ with
              | mfield f =>
                simp only [Tm.boundedIn, Bool.and_eq_true] at h
                rw [Tm.mfield_eval] at had
                obtain ⟨id₀, hi, had⟩ := bind_ok_inv had
                simp only [pure, Except.pure, Except.ok.injEq] at had
                subst had
                exact Nat.lt_of_lt_of_le (Tm.freshRoot_read_lt h.2 hμ₁ hi (s := .field f) hmv)
                  (Tm.onMemSpine_nextId_le hμ₁ M h.1 hM)
            | app2 o₂ i k =>
              cases o₂ with
              | mat =>
                simp only [Tm.boundedIn, Bool.and_eq_true] at h
                rw [Tm.mat_eval] at had
                obtain ⟨id₀, hi, had⟩ := bind_ok_inv had
                obtain ⟨kv, -, had⟩ := bind_ok_inv had
                obtain ⟨kn, -, had⟩ := bind_ok_inv had
                simp only [pure, Except.pure, Except.ok.injEq] at had
                subst had
                exact Nat.lt_of_lt_of_le (Tm.freshRoot_read_lt h.2 hμ₁ hi (s := .at kn) hmv)
                  (Tm.onMemSpine_nextId_le hμ₁ M h.1 hM)
        | _ => nomatch h
      | app0 _ | app2 _ _ _ | app3 _ _ _ _ => nomatch h
    | _ => nomatch h

/-- Two memory addresses that never meet: different members, a member and
an element, elements of one object at different literal indices
(`MAddr.apart?`). -/
def Tm.apart? : Tm C Γ .addr → Tm C Γ .addr → Bool
  | .app1 (.mfield f) _ _, .app1 (.mfield g) _ _ => f != g
  | .app1 (.mfield _) _ _, .app2 .mat _ _ => true
  | .app2 .mat _ _, .app1 (.mfield _) _ _ => true
  | .app2 .mat i (.app0 (.lit (.int k))), .app2 .mat j (.app0 (.lit (.int k'))) => i.beqR j && k != k'
  | _, _ => false

theorem Tm.apart?_eval {σ : State C Γ} (a b : Tm C Γ .addr) (h : a.apart? b = true) {ad bd : Addr}
    (ha : a.evalT σ = .ok ad) (hb : b.evalT σ = .ok bd) : Close.Apart ad bd := by
  unfold Tm.apart? at h
  split at h
  · rename_i f _ _ g _ _
    simp only [bne_iff_ne, ne_eq] at h
    rw [Tm.mfield_eval] at ha hb
    obtain ⟨id, -, ha⟩ := bind_ok_inv ha
    obtain ⟨id', -, hb⟩ := bind_ok_inv hb
    simp only [pure, Except.pure, Except.ok.injEq] at ha hb
    subst ha hb
    exact Or.inr fun h' => h h'.symm
  · rw [Tm.mfield_eval] at ha
    rw [Tm.mat_eval] at hb
    obtain ⟨id, -, ha⟩ := bind_ok_inv ha
    obtain ⟨id', -, hb⟩ := bind_ok_inv hb
    obtain ⟨kv, -, hb⟩ := bind_ok_inv hb
    obtain ⟨kn, -, hb⟩ := bind_ok_inv hb
    simp only [pure, Except.pure, Except.ok.injEq] at ha hb
    subst ha hb
    trivial
  · rw [Tm.mat_eval] at ha
    rw [Tm.mfield_eval] at hb
    obtain ⟨id, -, ha⟩ := bind_ok_inv ha
    obtain ⟨kv, -, ha⟩ := bind_ok_inv ha
    obtain ⟨kn, -, ha⟩ := bind_ok_inv ha
    obtain ⟨id', -, hb⟩ := bind_ok_inv hb
    simp only [pure, Except.pure, Except.ok.injEq] at ha hb
    subst ha hb
    trivial
  · rename_i i k j k'
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hij, hk⟩ := h
    obtain rfl := Tm.eq_of_beqR hij
    rw [Tm.mat_eval] at ha hb
    obtain ⟨id, hi, ha⟩ := bind_ok_inv ha
    obtain ⟨id', hi', hb⟩ := bind_ok_inv hb
    rw [hi] at hi'
    cases hi'
    simp only [Tm.lit_eval, Res.ok_bind', Value.asInt, pure, Except.pure, Except.ok.injEq] at ha hb
    subst ha hb
    exact Or.inr fun h' => hk h'.symm
  · nomatch h

/-- A law of a memory read, at the value or the identity sort: where the
read returns, the replacement returns the same (`EvalLaw.sound`). -/
inductive EvalLaw : {u : Srt} → Tm C Γ u → Tm C Γ u → Prop
  /-- **`readOnWrite`**: `read(write(m, a, v), a) ⇝ v` (`readAddr_writeAddr_same`). -/
  | readOnWrite {m : Tm C Γ .mem} {a : Tm C Γ .addr} {v : Value} :
      EvalLaw tm{ read(write(m, a, lit(v)), a) } tm{ lit(v) }
  /-- **`findCopyMem`**: a member read out of a memory object copied into
  storage is read out of memory,
  `find(save(s, p, copyMem(mtSt, m, i)), p.f) ⇝ read(m, i, f)` (`copyMem_member`). -/
  | findCopyMem {s : Tm C Γ .st} {p : Tm C Γ .path} {m : Tm C Γ .mem} {i : Tm C Γ .ident} {f : Name}
      (hf : (f == "length") = false := by rfl) :
      EvalLaw tm{ find(save(s, p, copyMem(mtSt, m, i)), p.f) } tm{ read(m, i, f) }
  /-- **`readCopySt`**: a member read out of a copy of a storage struct is
  read out of storage,
  `read(copySt(m, find(s, p)), freshId(copySt(m, find(s, p))), f) ⇝ find(s, p.f)`
  (`copyStToM_member`). -/
  | readCopySt {m : Tm C Γ .mem} {s : Tm C Γ .st} {p : Tm C Γ .path} {f : Name}
      (hf : (f == "length") = false := by rfl) :
      EvalLaw tm{ read(copySt(m, find(s, p)), freshId(copySt(m, find(s, p))), f) }
        tm{ find(s, p.f) }
  /-- **`readAddEqual`**: a primitive member or fixed element of a fresh
  object holds its type's default, `read(addM(m, R), a) ⇝ default`, where
  `a` reads at a fresh path of the allocation whose declared type is the
  primitive (`copyStToM_default_readPath`). -/
  | readAddEqual {m : Tm C Γ .mem} {R : RefTy} {a : Tm C Γ .addr} {q : PrimTy}
      (h : (a.freshPath? m R).bind (Ty.ref R).memberTy = some (.prim q) := by rfl) :
      EvalLaw (Tm.app2 .read (Tm.app1 (.addM R) rfl m) a) (Tm.lit (PrimTy.default q))
  /-- **`readAddDifferent`**: an allocation leaves every object allocated
  before it, `read(addM(m, R), a) ⇝ read(m, a)` where `a`'s identity is
  allocated strictly earlier on `m`'s spine (`Tm.boundedIn`, `readAddr_heapExt`). -/
  | readAddDifferent {m : Tm C Γ .mem} {R : RefTy} {a : Tm C Γ .addr}
      (h : a.boundedIn m = true := by rfl) :
      EvalLaw (Tm.app2 .read (Tm.app1 (.addM R) rfl m) a) (Tm.app2 .read m a)
  /-- **`readAddDifferentIdentity`**: `readAddDifferent` at the identity sort. -/
  | readAddDifferentIdentity {m : Tm C Γ .mem} {R : RefTy} {a : Tm C Γ .addr}
      (h : a.boundedIn m = true := by rfl) :
      EvalLaw (Tm.app2 .iread (Tm.app1 (.addM R) rfl m) a) (Tm.app2 .iread m a)
  /-- **`readWriteDifferent`**: a write leaves every other address,
  `read(write(m, a, v), b) ⇝ read(m, b)` where `a` and `b` never meet
  (`Tm.apart?`, `writeAddr_setObj`). -/
  | readWriteDifferent {m : Tm C Γ .mem} {a b : Tm C Γ .addr} {v : Tm C Γ .mv}
      (h : a.apart? b = true := by rfl) :
      EvalLaw tm{ read(write(m, a, v), b) } tm{ read(m, b) }
  /-- **`readWriteDifferentIdentity`**: `readWriteDifferent` at the identity sort. -/
  | readWriteDifferentIdentity {m : Tm C Γ .mem} {a b : Tm C Γ .addr} {v : Tm C Γ .mv}
      (h : a.apart? b = true := by rfl) :
      EvalLaw (Tm.app2 .iread (.app3 .write m a v) b) (Tm.app2 .iread m b)
  /-- **`readOnWriteIdentity`**: `readOnWrite` at the identity sort,
  `read(write(m, a, ref(i)), a) ⇝ i` (`readAddr_writeAddr_same`). -/
  | readOnWriteIdentity {m : Tm C Γ .mem} {a : Tm C Γ .addr} {i : Tm C Γ .ident} :
      EvalLaw (Tm.app2 .iread (.app3 .write m a (.app1 .ref rfl i)) a) i

section EvalLawSound

variable {σ : State C Γ}

theorem EvalLaw.readOnWrite_le {m : Tm C Γ .mem} {a : Tm C Γ .addr} {v : Value}
    {τ : Semantics.State} (hw : (Tm.app3 .write m a (.app1 .mval rfl (Tm.lit v))).evalT σ = .ok τ) :
    (Tm.app2 .read (.app3 .write m a (.app1 .mval rfl (Tm.lit v))) a).evalT σ = .ok v := by
  rw [Tm.read_eval, hw, Res.ok_bind']
  rw [Tm.write_eval, Tm.mval_eval, Tm.lit_eval] at hw
  simp only [Res.ok_bind', pure, Except.pure] at hw
  obtain ⟨τ₀, -, hw⟩ := bind_ok_inv hw
  obtain ⟨ad, had, hw⟩ := bind_ok_inv hw
  rw [had, Res.ok_bind', Close.readAddr_writeAddr_same hw, Res.ok_bind', Value.toMVal_asValue]

theorem EvalLaw.findCopyMem_eval {s : Tm C Γ .st} {p : Tm C Γ .path} {m : Tm C Γ .mem}
    {i : Tm C Γ .ident} {f : Name} (hf : (f == "length") = false) {τ : Semantics.State}
    (hw : (Tm.app3 .save s p (.app2 .copyMem m i)).evalT σ = .ok τ) :
    Res.Le ((Tm.app2 .find (.app3 .save s p (.app2 .copyMem m i)) (.app1 (.field f) rfl p)).evalT σ)
        ((Tm.app2 .read m (.app1 (.mfield f) rfl i)).evalT σ) ∧
      Res.Le ((Tm.app2 .read m (.app1 (.mfield f) rfl i)).evalT σ)
        ((Tm.app2 .find (.app3 .save s p (.app2 .copyMem m i)) (.app1 (.field f) rfl p)).evalT σ) := by
  have hf' : f ≠ "length" := fun e => by rw [e] at hf; nomatch hf
  rw [Tm.find_eval, hw, Res.ok_bind', Tm.field_eval]
  rw [Tm.save_eval, Tm.copyMem_eval] at hw
  obtain ⟨sv, hsv, hw⟩ := bind_ok_inv hw
  obtain ⟨τm, hm, hsv⟩ := bind_ok_inv hsv
  obtain ⟨id, hi, hsv⟩ := bind_ok_inv hsv
  obtain ⟨τs, -, hw⟩ := bind_ok_inv hw
  obtain ⟨⟨r, segs⟩, hp, hw⟩ := bind_ok_inv hw
  rw [hp, Tm.read_eval, hm, Res.ok_bind', Tm.mfield_eval, hi]
  simp only [Res.ok_bind', pure, Except.pure]
  rw [State.writeStorage_find_field hw f, Close.copyMem_member hsv hf']
  cases readAddr τm (.memoryField id f) with
  | error _ => exact ⟨Res.Le.refl _, Res.Le.refl _⟩
  | ok mv =>
    simp only [Res.ok_bind']
    exact ⟨fun x hx => (Close.copyLeaf_asValue τm id mv x).1 hx,
      fun x hx => (Close.copyLeaf_asValue τm id mv x).2 hx⟩

theorem EvalLaw.readCopySt_eval {m : Tm C Γ .mem} {s : Tm C Γ .st} {p : Tm C Γ .path} {f : Name}
    (hf : (f == "length") = false) {μ : Semantics.State}
    (hw : (Tm.app2 .copySt m (.app2 .sfind s p)).evalT σ = .ok μ) :
    Res.Le ((Tm.app2 .read (.app2 .copySt m (.app2 .sfind s p))
          (.app1 (.mfield f) rfl (.app2 .copy m (.app2 .sfind s p)))).evalT σ)
        ((Tm.app2 .find s (.app1 (.field f) rfl p)).evalT σ) ∧
      Res.Le ((Tm.app2 .find s (.app1 (.field f) rfl p)).evalT σ)
        ((Tm.app2 .read (.app2 .copySt m (.app2 .sfind s p))
          (.app1 (.mfield f) rfl (.app2 .copy m (.app2 .sfind s p)))).evalT σ) := by
  have hf' : f ≠ "length" := fun e => by rw [e] at hf; nomatch hf
  rw [Tm.read_eval, hw, Res.ok_bind', Tm.mfield_eval, Tm.copy_eval]
  rw [Tm.copySt_eval] at hw
  obtain ⟨sv, hsv, hw⟩ := bind_ok_inv hw
  obtain ⟨τm, hm, hw⟩ := bind_ok_inv hw
  obtain ⟨⟨τc, mv⟩, hc, hw⟩ := bind_ok_inv hw
  simp only [pure, Except.pure, Except.ok.injEq] at hw
  subst hw
  rw [hsv, Res.ok_bind', hm, Res.ok_bind', hc, Res.ok_bind']
  rw [Tm.sfind_eval] at hsv
  obtain ⟨τs, hs, hsv⟩ := bind_ok_inv hsv
  obtain ⟨⟨r, segs⟩, hp, hsv⟩ := bind_ok_inv hsv
  dsimp only at hsv
  rw [Tm.find_eval, hs, Res.ok_bind', Tm.field_eval, hp]
  simp only [Res.ok_bind', pure, Except.pure]
  rw [State.findStorage_append, hsv, Res.ok_bind']
  cases mv with
  | prim q =>
    constructor
    · intro x hx
      simp only [MVal.asRef, bind, Except.bind] at hx
      nomatch hx
    · intro x hx
      exfalso
      cases sv with
      | prim _ => simp only [bind, Except.bind, Semantics.SVal.find, reduceCtorEq] at hx
      | map _ _ => nomatch hc
      | struct fields =>
        rw [copyStToM] at hc
        rcases hcf : copyStFields τm fields with _ | ⟨s', mf⟩ <;>
          simp only [bind, Except.bind, hcf, State.alloc_id, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
            and_false] at hc
      | array elems _ _ =>
        rw [copyStToM] at hc
        rcases hcf : copyStElems τm elems with _ | ⟨s', me⟩ <;>
          simp only [bind, Except.bind, hcf, State.alloc_id, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
            and_false] at hc
  | ref id =>
    have this := Close.copyStToM_member hc hf'
    simp only [Close.readVal] at this
    simp only [MVal.asRef, Res.ok_bind', pure, Except.pure]
    have this' : (readAddr τc (.memoryField id f) >>= fun mv => mv.asValue) =
        (sv.find [.field f] >>= Semantics.SVal.asValue) := this
    rw [this']
    exact ⟨Res.Le.refl _, Res.Le.refl _⟩

theorem EvalLaw.readAddEqual_eval {m : Tm C Γ .mem} {R : RefTy} {a : Tm C Γ .addr} {q : PrimTy}
    (h : (a.freshPath? m R).bind (Ty.ref R).memberTy = some (.prim q)) {μ₁ : Semantics.State}
    (hw : (Tm.app1 (.addM R) rfl m).evalT σ = .ok μ₁) :
    (Tm.app2 .read (.app1 (.addM R) rfl m) a).evalT σ = .ok (PrimTy.default q) := by
  have hμ := hw
  rw [Tm.addM_eval] at hw
  obtain ⟨μ₀, hm, hw⟩ := bind_ok_inv hw
  obtain ⟨⟨μ₁', root⟩, ha, hw⟩ := bind_ok_inv hw
  cases hw
  cases hp : a.freshPath? m R with
  | none => rw [hp] at h; nomatch h
  | some p =>
    simp only [hp, Option.bind] at h
    obtain ⟨h1, h2⟩ := Tm.freshPath_eval hm ha a hp
    obtain ⟨ad, had⟩ := h2 _ h
    obtain ⟨mv', hmv', hd⟩ :=
      (copyStToM_default_readPath p (Close.allocDefault_copy ha) (State.HeapExt.refl _)).2 _ h
    simp only [DefaultMVal] at hd
    subst hd
    rw [Tm.read_eval, hμ, Res.ok_bind', had, Res.ok_bind', h1 ad had]
    simp only [State.readPath]
    rw [hmv', Res.ok_bind', Value.toMVal_asValue]

theorem EvalLaw.readAddDifferent_eval {m : Tm C Γ .mem} {R : RefTy} {a : Tm C Γ .addr}
    (h : a.boundedIn m = true) {μ₁ : Semantics.State} (hw : (Tm.app1 (.addM R) rfl m).evalT σ = .ok μ₁) :
    (Tm.app2 .read (.app1 (.addM R) rfl m) a).evalT σ = (Tm.app2 .read m a).evalT σ := by
  have hμ := hw
  rw [Tm.addM_eval] at hw
  obtain ⟨μ₀, hm, hw⟩ := bind_ok_inv hw
  obtain ⟨⟨μ₁', root⟩, ha, hw⟩ := bind_ok_inv hw
  cases hw
  rw [Tm.read_eval, Tm.read_eval, hμ, hm, Res.ok_bind', Res.ok_bind']
  cases had : a.evalT σ with
  | error _ => rfl
  | ok ad =>
    simp only [Res.ok_bind']
    rw [readAddr_heapExt (allocDefault_heapExt ha) (Tm.boundedIn_eval hm a h ad had)]

theorem EvalLaw.readAddDifferentIdentity_eval {m : Tm C Γ .mem} {R : RefTy} {a : Tm C Γ .addr}
    (h : a.boundedIn m = true) {μ₁ : Semantics.State} (hw : (Tm.app1 (.addM R) rfl m).evalT σ = .ok μ₁) :
    (Tm.app2 .iread (.app1 (.addM R) rfl m) a).evalT σ = (Tm.app2 .iread m a).evalT σ := by
  have hμ := hw
  rw [Tm.addM_eval] at hw
  obtain ⟨μ₀, hm, hw⟩ := bind_ok_inv hw
  obtain ⟨⟨μ₁', root⟩, ha, hw⟩ := bind_ok_inv hw
  cases hw
  rw [Tm.iread_eval, Tm.iread_eval, hμ, hm, Res.ok_bind', Res.ok_bind']
  cases had : a.evalT σ with
  | error _ => rfl
  | ok ad =>
    simp only [Res.ok_bind']
    rw [readAddr_heapExt (allocDefault_heapExt ha) (Tm.boundedIn_eval hm a h ad had)]

theorem EvalLaw.readWriteDifferent_eval {m : Tm C Γ .mem} {a b : Tm C Γ .addr} {v : Tm C Γ .mv}
    (h : a.apart? b = true) {τ : Semantics.State} (hw : (Tm.app3 .write m a v).evalT σ = .ok τ) :
    (Tm.app2 .read (.app3 .write m a v) b).evalT σ = (Tm.app2 .read m b).evalT σ := by
  have hμ := hw
  rw [Tm.write_eval] at hw
  obtain ⟨mv, hv, hw⟩ := bind_ok_inv hw
  obtain ⟨μ, hm, hw⟩ := bind_ok_inv hw
  obtain ⟨ad, had, hw⟩ := bind_ok_inv hw
  rw [Tm.read_eval, Tm.read_eval, hμ, hm, Res.ok_bind', Res.ok_bind']
  cases hbd : b.evalT σ with
  | error _ => rfl
  | ok bd =>
    simp only [Res.ok_bind']
    obtain ⟨-, -, -, hfr⟩ := Close.writeAddr_setObj hw
    rw [hfr bd (Tm.apart?_eval a b h had hbd)]

theorem EvalLaw.readWriteDifferentIdentity_eval {m : Tm C Γ .mem} {a b : Tm C Γ .addr}
    {v : Tm C Γ .mv} (h : a.apart? b = true) {τ : Semantics.State}
    (hw : (Tm.app3 .write m a v).evalT σ = .ok τ) :
    (Tm.app2 .iread (.app3 .write m a v) b).evalT σ = (Tm.app2 .iread m b).evalT σ := by
  have hμ := hw
  rw [Tm.write_eval] at hw
  obtain ⟨mv, hv, hw⟩ := bind_ok_inv hw
  obtain ⟨μ, hm, hw⟩ := bind_ok_inv hw
  obtain ⟨ad, had, hw⟩ := bind_ok_inv hw
  rw [Tm.iread_eval, Tm.iread_eval, hμ, hm, Res.ok_bind', Res.ok_bind']
  cases hbd : b.evalT σ with
  | error _ => rfl
  | ok bd =>
    simp only [Res.ok_bind']
    obtain ⟨-, -, -, hfr⟩ := Close.writeAddr_setObj hw
    rw [hfr bd (Tm.apart?_eval a b h had hbd)]

theorem EvalLaw.readOnWriteIdentity_eval {m : Tm C Γ .mem} {a : Tm C Γ .addr} {i : Tm C Γ .ident}
    {τ : Semantics.State} (hw : (Tm.app3 .write m a (.app1 .ref rfl i)).evalT σ = .ok τ) :
    (Tm.app2 .iread (.app3 .write m a (.app1 .ref rfl i)) a).evalT σ = i.evalT σ := by
  have hμ := hw
  rw [Tm.write_eval, Tm.ref_eval] at hw
  obtain ⟨mv, hmv, hw⟩ := bind_ok_inv hw
  obtain ⟨id, hi, hmv⟩ := bind_ok_inv hmv
  simp only [pure, Except.pure, Except.ok.injEq] at hmv
  subst hmv
  obtain ⟨μ, hm, hw⟩ := bind_ok_inv hw
  obtain ⟨ad, had, hw⟩ := bind_ok_inv hw
  rw [Tm.iread_eval, hμ, Res.ok_bind', had, Res.ok_bind', Close.readAddr_writeAddr_same hw, hi]
  rfl

/-- **A law of a memory read refines evaluation**: where the read returns,
its replacement returns the same. -/
theorem EvalLaw.sound {u : Srt} {t t' : Tm C Γ u} : EvalLaw t t' → Tm.EvalRefinesAt t t'
  | .readOnWrite => fun σ x hx => by
    have hx0 := hx
    rw [Tm.read_eval] at hx
    obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
    rw [EvalLaw.readOnWrite_le hτ] at hx0
    obtain rfl := Except.ok.inj hx0
    rfl
  | .findCopyMem hf => fun σ x hx => by
    have hx0 := hx
    rw [Tm.find_eval] at hx
    obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
    exact (EvalLaw.findCopyMem_eval hf hτ).1 x hx0
  | .readCopySt hf => fun σ x hx => by
    have hx0 := hx
    rw [Tm.read_eval] at hx
    obtain ⟨μ, hμ, -⟩ := bind_ok_inv hx
    exact (EvalLaw.readCopySt_eval hf hμ).1 x hx0
  | .readAddEqual h => fun σ x hx => by
    have hx0 := hx
    rw [Tm.read_eval] at hx
    obtain ⟨μ₁, hμ, -⟩ := bind_ok_inv hx
    rw [EvalLaw.readAddEqual_eval h hμ] at hx0
    exact hx0.symm ▸ rfl
  | .readAddDifferent h => fun σ x hx => by
    have hx0 := hx
    rw [Tm.read_eval] at hx
    obtain ⟨μ₁, hμ, -⟩ := bind_ok_inv hx
    rwa [EvalLaw.readAddDifferent_eval h hμ] at hx0
  | .readAddDifferentIdentity h => fun σ x hx => by
    have hx0 := hx
    rw [Tm.iread_eval] at hx
    obtain ⟨μ₁, hμ, -⟩ := bind_ok_inv hx
    rwa [EvalLaw.readAddDifferentIdentity_eval h hμ] at hx0
  | .readWriteDifferent h => fun σ x hx => by
    have hx0 := hx
    rw [Tm.read_eval] at hx
    obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
    rwa [EvalLaw.readWriteDifferent_eval h hτ] at hx0
  | .readWriteDifferentIdentity h => fun σ x hx => by
    have hx0 := hx
    rw [Tm.iread_eval] at hx
    obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
    rwa [EvalLaw.readWriteDifferentIdentity_eval h hτ] at hx0
  | .readOnWriteIdentity => fun σ x hx => by
    have hx0 := hx
    rw [Tm.iread_eval] at hx
    obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
    rwa [EvalLaw.readOnWriteIdentity_eval hτ] at hx0

end EvalLawSound

/-- `U` writes the memory with a term on whose spine the write `w` lies: `w`
returns wherever `U` does. -/
def Upd.holdsMem {Δ : Ctx} (U : Upd C Γ Δ) (w : Tm C Γ .mem) : Bool :=
  U.memTerms.any (·.onMemSpine w)

theorem Upd.holdsMem_eval {Δ : Ctx} {U : Upd C Γ Δ} {w : Tm C Γ .mem} (h : U.holdsMem w = true)
    {σ : State C Γ} {τ : Semantics.State} (hU : U.globT σ = .ok τ) :
    ∃ μ : Semantics.State, w.evalT σ = .ok μ := by
  obtain ⟨M, hM, hs⟩ := List.any_eq_true.1 h
  obtain ⟨μ', hM'⟩ := Upd.memory_eval_of_globT hU hM
  cases hw : w.evalT σ with
  | ok μ => exact ⟨μ, rfl⟩
  | error e' =>
    obtain ⟨e'', hM''⟩ := Tm.onMemSpine_error hw M hs
    rw [hM''] at hM'
    cases hM'

/-- `U` returns only where the memory law is exact: `q.1` reads back a
write `U` holds — the memory write or allocation the read looks past
(`Upd.holdsMem`), the storage write of `findCopyMem` (`Upd.holdsWrite`).
By the sort of the law, then the shape of its read.  Syntactic, so that
`rfl` decides it. -/
def Upd.coversEval {Δ : Ctx} (U : Upd C Γ Δ) : {u : Srt} → Tm C Γ u × Tm C Γ u → Bool
  | .val, (.app2 .read (.app3 .write m a v) _, _) => U.holdsMem (.app3 .write m a v)
  | .val, (.app2 .find (.app3 .save s p (.app2 .copyMem m i)) (.app1 (.field _) _ p'), _) =>
    p'.beqR p && U.holdsWrite (.app3 .save s p (.app2 .copyMem m i))
  | .val, (.app2 .read (.app2 .copySt m v) (.app1 (.mfield _) _ (.app2 .copy m' v')), _) =>
    m.beqR m' && v.beqR v' && U.holdsMem (.app2 .copySt m v)
  | .val, (.app2 .read (.app1 (.addM R) h m) _, _) => U.holdsMem (.app1 (.addM R) h m)
  | .ident, (.app2 .iread (.app3 .write m a v) _, _) => U.holdsMem (.app3 .write m a v)
  | .ident, (.app2 .iread (.app1 (.addM R) h m) _, _) => U.holdsMem (.app1 (.addM R) h m)
  | _, _ => false

/-- **Where the update returns, a covered memory law is exact**: its
replacement returns what the replaced term returns. -/
theorem EvalLaw.back {u : Srt} {t t' : Tm C Γ u} (r : EvalLaw t t') {Δ : Ctx} {U : Upd C Γ Δ}
    (hc : U.coversEval (t, t') = true) {σ : State C Γ} {τ : Semantics.State} (hU : U.globT σ = .ok τ) :
    Srt.Le u (t'.evalT σ) (t.evalT σ) := by
  cases r with
  | readOnWrite =>
    obtain ⟨τw, hw⟩ := Upd.holdsMem_eval (w := .app3 .write _ _ _) hc hU
    intro x hx
    cases hx
    exact EvalLaw.readOnWrite_le hw
  | readAddEqual h =>
    obtain ⟨μ₁, hw⟩ := Upd.holdsMem_eval (w := .app1 (.addM _) _ _) hc hU
    intro x hx
    cases hx
    exact EvalLaw.readAddEqual_eval h hw
  | readAddDifferent h =>
    obtain ⟨μ₁, hw⟩ := Upd.holdsMem_eval (w := .app1 (.addM _) _ _) hc hU
    rw [EvalLaw.readAddDifferent_eval h hw]
    exact Res.Le.refl _
  | readAddDifferentIdentity h =>
    obtain ⟨μ₁, hw⟩ := Upd.holdsMem_eval (w := .app1 (.addM _) _ _) hc hU
    rw [EvalLaw.readAddDifferentIdentity_eval h hw]
    exact Res.Le.refl _
  | readWriteDifferent h =>
    obtain ⟨τw, hw⟩ := Upd.holdsMem_eval (w := .app3 .write _ _ _) hc hU
    rw [EvalLaw.readWriteDifferent_eval h hw]
    exact Res.Le.refl _
  | readWriteDifferentIdentity h =>
    obtain ⟨τw, hw⟩ := Upd.holdsMem_eval (w := .app3 .write _ _ _) hc hU
    rw [EvalLaw.readWriteDifferentIdentity_eval h hw]
    exact Res.Le.refl _
  | readOnWriteIdentity =>
    obtain ⟨τw, hw⟩ := Upd.holdsMem_eval (w := .app3 .write _ _ _) hc hU
    rw [EvalLaw.readOnWriteIdentity_eval hw]
    exact Res.Le.refl _
  | findCopyMem hf =>
    have hc' : (_ && U.holdsWrite (.app3 .save _ _ (.app2 .copyMem _ _))) = true := hc
    rw [Bool.and_eq_true] at hc'
    obtain ⟨b, F, hb, τ₁, hbe⟩ := Upd.holdsWrite_eval hc'.2 hU
    obtain ⟨τ', hs⟩ := Tm.save_returns_of_base hb hbe
    exact (EvalLaw.findCopyMem_eval hf hs).2
  | readCopySt hf =>
    have hc' : (_ && U.holdsMem (.app2 .copySt _ _)) = true := hc
    rw [Bool.and_eq_true] at hc'
    obtain ⟨μ, hw⟩ := Upd.holdsMem_eval hc'.2 hU
    exact (EvalLaw.readCopySt_eval hf hw).2

/-! ## The laws, bundled -/

/-- A law at an update's right-hand sides, scoped: the right side returns what the
left side does (`fwd`), and wherever an update the check `chk` accepts returns, the
left side returns what the right side does (`back`). -/
structure LawCov (C : Contract) (Γ : Ctx) (u : Srt) (t t' : Tm C Γ u) where
  chk : {Δ : Ctx} → Upd C Γ Δ → Bool
  fwd : Tm.EvalRefinesAt t t'
  back : ∀ {Δ : Ctx} (U : Upd C Γ Δ) (σ : State C Γ) (τ : Semantics.State), chk U = true →
    U.globT σ = .ok τ → Srt.Le u (t'.evalT σ) (t.evalT σ)

/-- A term taclet onto a literal, where the update holds the storage write
its left side reads back (`Upd.covers`). -/
def LawCov.covered {t t' : Tm C Γ .val} (r : TermTaclet t t') (ht : t'.isLit = true) :
    LawCov C Γ .val t t' where
  chk U := U.covers (t, t')
  fwd := Tm.evalRefinesAt_of_theq r.sound ht
  back _ _ _ hc hU := Upd.covers_le (q := (t, t')) (Tm.evalRefinesAt_of_theq r.sound ht) hc hU

/-- A frame or delete-value law, where the update holds its storage
operation (`Upd.coversRef`). -/
def LawCov.ref {t t' : Tm C Γ .val} {r : TermTaclet t t'} (hr : TermTaclet.RefLaw r) :
    LawCov C Γ .val t t' where
  chk U := U.coversRef (t, t')
  fwd := hr.evalRefines
  back _ _ _ hc hU := hr.back hc hU

/-- Two member-wise forms of one read, under any update. -/
def LawCov.eqv {t t' : Tm C Γ .val} (h : Tm.sameBase t t' = true) : LawCov C Γ .val t t' where
  chk _ := true
  fwd σ := (Tm.sameBase_eval h σ).le
  back _ σ _ _ _ := (Tm.sameBase_eval h σ).ge

/-- A memory law, where the update holds the write it reads back
(`Upd.coversEval`). -/
def LawCov.eval {u : Srt} {t t' : Tm C Γ u} (r : EvalLaw t t') : LawCov C Γ u t t' where
  chk U := U.coversEval (t, t')
  fwd := r.sound
  back _ _ _ hc hU := r.back hc hU

/-! ## A premise about closed terms, at any scope -/

/-- `KindFreeAt` of closed terms holds at any scope they are read in: a
chain's hypothesis about terms at the empty scope (`st!{ … }`, `pt!{ … }`)
gives a law's premise at an update's scope. -/
theorem Tm.KindFreeAt.ofNil {s : Tm C Γ .st} {p : Tm C Γ .path} {s₀ : Tm C [] .st}
    {p₀ : Tm C [] .path} (h : Tm.KindFreeAt s₀ p₀) (hs : s.toNil? = some s₀)
    (hp : p.toNil? = some p₀) : Tm.KindFreeAt s p := fun σ => by
  rw [Tm.denoteT_toNilS σ s hs, Tm.denoteT_toNilS σ p hp]
  exact h σ.toNil

/-! ## Pins: the checks decide by `rfl` -/

section Pins

/-- `alice.age`. -/
private abbrev aliceAge : Tm StandardExample [] .path := .app1 (.field "age") rfl (.app0 (.root "alice"))
/-- `alice.name`. -/
private abbrev aliceName : Tm StandardExample [] .path := .app1 (.field "name") rfl (.app0 (.root "alice"))
/-- `age`, a path below the root `alice` once it is selected. -/
private abbrev age : Tm StandardExample [] .path := .app0 (.root "age")
/-- `select(storage, alice)`. -/
private abbrev aliceSt : Tm StandardExample [] .st := .app1 (.select "alice") rfl (.app0 .storage)
/-- `uint[3]`. -/
private abbrev uints : RefTy := .fixed (.prim .uint) 3
/-- `freshId(addM(memory, uint[3]))`. -/
private abbrev fresh : Tm StandardExample [] .ident := .app1 (.alloc uints) rfl (.app0 .memory)
/-- `addM(memory, uint[3])`. -/
private abbrev added : Tm StandardExample [] .mem := .app1 (.addM uints) rfl (.app0 .memory)

/-- The update holding `storage := save(storage, alice.age, 42)`. -/
private abbrev Usave : Upd StandardExample [] [] :=
  Upd.nil.snoc (.storage tm{ save(storage, aliceAge, lit(‹.int 42›)) })

/- `find(save(storage, alice.age, 42), alice.age) ⇝ 42` is covered: the update
holds the write the read reads back, read as it is and member-wise. -/
example : Usave.covers (tm{ find(save(storage, aliceAge, lit(‹.int 42›)), aliceAge) },
    tm{ lit(‹.int 42›) }) = true := rfl

example : Usave.covers (tm{ find(save(aliceSt, age, lit(‹.int 42›)), age) }, tm{ lit(‹.int 42›) }) =
    true := rfl

/- An update that holds another write does not cover it. -/
example : Usave.covers (tm{ find(save(storage, aliceName, lit(‹.int 42›)), aliceName) },
    tm{ lit(‹.int 42›) }) = false := rfl

/- A word read at a deleted node, over `storage := delAt(save(storage, alice.age, 42), alice.age)`. -/
example : (Upd.nil.snoc (.storage tm{ delAt(save(storage, aliceAge, lit(‹.int 42›)), aliceAge) }) :
    Upd StandardExample [] []).covers
    (tm{ find(delAt(save(storage, aliceAge, lit(‹.int 42›)), aliceAge), aliceAge) },
      tm{ lit(‹.int 0›) }) = true := rfl

/- A frame law over the write it looks past. -/
example : Usave.coversRef (tm{ find(save(storage, aliceAge, lit(‹.int 42›)), aliceName) },
    tm{ find(storage, aliceName) }) = true := rfl

/- Two member-wise forms of one read. -/
example : Tm.sameBase tm{ find(aliceSt, age) } tm{ find(storage, aliceAge) } = true := rfl

example : Tm.sameBase tm{ find(aliceSt, age) } tm{ find(storage, aliceName) } = false := rfl

/- A memory law over the write it reads back. -/
example : (Upd.nil.snoc (.memory tm{ write(memory, ‹.app2 .mat fresh (Tm.lit (.int 0))›, lit(‹.int 7›)) }) :
    Upd StandardExample [] []).coversEval
    (tm{ read(write(memory, ‹.app2 .mat fresh (Tm.lit (.int 0))›, lit(‹.int 7›)),
      ‹.app2 .mat fresh (Tm.lit (.int 0))›) }, tm{ lit(‹.int 7›) }) = true := rfl

/- Each law kind elaborates with its side condition by its default. -/
example : LitLaw (C := StandardExample) (Γ := [])
    (.app2 (.binop .add .uint) (Tm.lit (.int 250)) (Tm.lit (.int 10))) (Tm.lit (.int 260)) :=
  .add_literals

example : TermTaclet.RefLaw (TermTaclet.findOnSaveFrame (s := .app0 .storage) (p := aliceAge)
    (q := aliceName) (v := .app1 .sval rfl (Tm.lit (.int 42)))) :=
  .findOnSaveFrame

example : TermTaclet.RefLaw (TermTaclet.lenOnDelAtFrame (s := .app0 .storage) (q := aliceAge)
    (p := .app0 (.root "values"))) :=
  .lenOnDelAtFrame

example : EvalLaw (Tm.app2 .read added (.app2 .mat fresh (Tm.lit (.int 0))))
    (Tm.lit (PrimTy.default .uint)) :=
  .readAddEqual

example : EvalLaw (Tm.app2 .read (.app1 (.addM uints) rfl added) (.app2 .mat fresh (Tm.lit (.int 0))))
    (Tm.app2 .read added (.app2 .mat fresh (Tm.lit (.int 0)))) :=
  .readAddDifferent

example (v : Tm StandardExample [] .mv) :
    EvalLaw (Tm.app2 .read (.app3 .write (.app0 .memory) (.app1 (.mfield "a") rfl fresh) v)
      (.app1 (.mfield "b") rfl fresh))
      (Tm.app2 .read (.app0 .memory) (.app1 (.mfield "b") rfl fresh)) :=
  .readWriteDifferent

example : EvalLaw (Tm.app2 .read (.app3 .write (.app0 .memory) (.app2 .mat fresh (Tm.lit (.int 0)))
      (.app1 .mval rfl (Tm.lit (.int 1))))
      (.app2 .mat fresh (Tm.lit (.int 1))))
      (Tm.app2 .read (.app0 .memory) (.app2 .mat fresh (Tm.lit (.int 1)))) :=
  .readWriteDifferent

end Pins

end Solidity
