import Solidity.Kernel.Measure

/-!
# The logic: continuations, hypotheses, and a sound proof system

Phase 6 of `docs/kernel-port.md`, after mini-solkey's `Ch05_Logic` and the
`Proves` judgement of `Ch06_Taclets`.

A goal is a sequent `H ⊢ k`: hypotheses `H` — the path conditions and the
updates symbolic execution has collected, in order — and a continuation `k`,
a program followed by what must hold after it.  `Proves H k` is built by the
taclets (`Taclet`), a closing rule for a postcondition, and three structural
rules; `Proves.sound` says a derivation is a proof of the program's
correctness, from every state.  This is the theorem the untyped layer's
`CalculusHolds` does not have.

**No retyping.**  An unfolding rule's statements bind scratch names and end
at a larger context than the rest of the program starts from.  The kernel
does not weaken the rest: a continuation can be read at a larger context
(`Kont.up`), so the premise is `⟨P⟩ (up ⟨ω⟩ k)`.  What makes that sound is the
frame lemma: two states that agree on everything a context can see
(`StateAgree`) run a program typed there alike (`Prog.run_frame`) and satisfy
the same continuations (`Kont.holds_frame`).

**The modalities** read a run as the kernel does throughout: a box holds
unless the run ends normally in a state that fails the continuation, a
diamond needs a normal end in a state that satisfies it.
-/

namespace Solidity
namespace Kernel

open Semantics RuleSoundness

variable {C : Contract}

/-! ## Agreement at a context -/

/-- `σ` and `τ` agree on everything a term typed at `Γ` can see: storage,
heap, ledger, balance, and every local except names fresh at `Γ`. -/
def StateAgree (C : Contract) (Γ : Ctx) (σ τ : State) : Prop :=
  ∃ ns : List Name, (∀ n ∈ ns, isFresh C Γ n = true) ∧ EnvAgreeExcept ns σ τ

theorem StateAgree.refl (Γ : Ctx) (σ : State) : StateAgree C Γ σ σ :=
  ⟨[], by simp, EnvAgreeExcept.refl _ _⟩

/-- Agreeing at a larger context is agreeing at a smaller one. -/
theorem StateAgree.of_sub {Γ Γ' : Ctx} {σ τ : State} (h : Ctx.Sub C Γ Γ') :
    StateAgree C Γ' σ τ → StateAgree C Γ σ τ
  | ⟨ns, hns, hag⟩ => ⟨ns, fun n hn => isFresh_of_sub h (hns n hn), hag⟩

/-- Two outcomes that agree at `Γ`: both normal, in agreeing states, or both
abnormal. -/
def ResAgreeAt (C : Contract) (Γ : Ctx) : Res State → Res State → Prop
  | .ok a, .ok b => StateAgree C Γ a b
  | .error _, .error _ => True
  | _, _ => False

theorem _root_.Solidity.RuleSoundness.EnvAgreeExcept.setEnv_drop {ns : List Name} {σ τ : State} (h : EnvAgreeExcept ns σ τ)
    (x : Name) (b : Binding) :
    EnvAgreeExcept (ns.filter (· ≠ x)) (σ.setEnv x b) (τ.setEnv x b) :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun m hm => by
    by_cases he : m = x
    · subst he; simp [State.setEnv]
    · have : m ∉ ns := fun hc => hm (List.mem_filter.mpr ⟨hc, by simpa using he⟩)
      simp [State.setEnv, lookupBy_setBy_ne he, h.env m this],
    h.selfBalance⟩

/-- Binding a local on both sides keeps agreement, at the context that now
has it. -/
theorem StateAgree.setEnv {Γ Γ' : Ctx} {σ τ : State} (hag : StateAgree C Γ σ τ) (x : Name)
    (b : Binding) (h : ∀ n, isFresh C Γ n = true → n ≠ x → isFresh C Γ' n = true) :
    StateAgree C Γ' (σ.setEnv x b) (τ.setEnv x b) := by
  obtain ⟨ns, hns, hag⟩ := hag
  refine ⟨ns.filter (· ≠ x), fun n hn => ?_, hag.setEnv_drop x b⟩
  obtain ⟨hm, hne⟩ := List.mem_filter.mp hn
  exact h n (hns n hm) (by simpa using hne)

/-- Saving the same value in two agreeing states ends alike. -/
theorem StateAgree.save {Γ : Ctx} {σ τ : State} (hag : StateAgree C Γ σ τ) (r : Name)
    (segs : List Seg) (v : SVal) : ResAgreeAt C Γ (σ.saveStorage r segs v) (τ.saveStorage r segs v) := by
  obtain ⟨ns, hns, hag⟩ := hag
  have := saveStorage_agree hag r segs v
  cases h₁ : σ.saveStorage r segs v <;> cases h₂ : τ.saveStorage r segs v <;>
    simp_all [ResultsAgree, ResAgreeAt]
  exact ⟨ns, hns, this⟩

theorem StateAgree.findStorage {Γ : Ctx} {σ τ : State} (hag : StateAgree C Γ σ τ) (r : Name)
    (segs : List Seg) : σ.findStorage r segs = τ.findStorage r segs := by
  obtain ⟨_, _, hag⟩ := hag; exact findStorage_congr hag r segs

/-! ## The frame lemma for programs -/

/-- A statement's context extends the one it starts from. -/
theorem Stmt.sub {Γ Γ' : Ctx} : Stmt C Γ Γ' → Ctx.Sub C Γ Γ'
  | .declLocal _ _ hx _ | .declStorage _ _ _ hx _ | .declMem _ _ hx _ _ => Ctx.Sub.fresh hx _
  | .bindPush k _ _ => k.hole.sub
  | .assign .. | .rebind .. | .assignLocal .. | .opAssign .. | .incDec .. | .assignIncDec .. | .push ..
  | .pop _ | .transfer .. | .rebindMem .. | .assignMem .. | .assignFromMem ..
  | .delete _ | .ite .. | .require _ | .assert _
  | .revert => Ctx.Sub.refl _

theorem not_fresh_of_bound {Γ : Ctx} {x : Name} {b : BTy} (h : lookupBy x Γ = some b) :
    isFresh C Γ x = false := by
  simp [isFresh, h]

mutual

/-- **Frame, for statements.**  Two states that agree at `Γ` run a statement
from `Γ` alike, and end agreeing at its context.  Binding a scratch `sp`
changes nothing `alice.age = 10;` reads or writes. -/
theorem Stmt.run_frame {Γ Γ' : Ctx} {σ τ : State} (hag : StateAgree C Γ σ τ) :
    (s : Stmt C Γ Γ') → ResAgreeAt C Γ' (s.run σ) (s.run τ)
  | .assign l r => by
    obtain ⟨ns, hns, hag'⟩ := hag
    simp only [Stmt.run, r.value_frame hag' hns, l.target_frame hag' hns]
    cases r.value τ with
    | error _ => trivial
    | ok v =>
      cases l.target τ with
      | error _ => trivial
      | ok rs => exact StateAgree.save ⟨ns, hns, hag'⟩ _ _ _
  | .opAssign op _ _ l r => by
    obtain ⟨ns, hns, hag'⟩ := hag
    simp only [Stmt.run, r.eval_frame hag' hns]
    cases r.eval τ with
    | error _ => trivial
    | ok v =>
      simp only [bind, Except.bind]
      have h := OpLoc.store_agree hag' hns op l v
      revert h
      cases l.store σ op v <;> cases l.store τ op v <;> intro h <;>
        first | trivial | exact h.elim | exact ⟨ns, hns, h⟩
  | .incDec op _ l => by
    obtain ⟨ns, hns, hag'⟩ := hag
    have h := OpLoc.bump_agree hag' hns op l
    simp only [Stmt.run]
    revert h
    cases l.bump σ op <;> cases l.bump τ op <;> intro h <;>
      first | trivial | exact h.elim | exact ⟨ns, hns, h.1⟩
  | .assignIncDec x hx op _ l _ => by
    obtain ⟨ns, hns, hag'⟩ := hag
    have h := OpLoc.bump_agree hag' hns op l
    simp only [Stmt.run]
    revert h
    cases l.bump σ op <;> cases l.bump τ op <;> intro h <;> first | trivial | exact h.elim | skip
    rename_i a b
    obtain ⟨hab, hv⟩ := h
    simp only [bind, Except.bind, pure, Except.pure, hv]
    exact StateAgree.setEnv ⟨ns, hns, hab⟩ x _ fun n hn _ => hn
  | .push (E := E) b v _ => by
    obtain ⟨ns, hns, hag'⟩ := hag
    simp only [Stmt.run, b.resolve_frame hag' hns]
    cases b.resolve τ with
    | error _ => trivial
    | ok rs =>
      have h := pushAt_agree hag' E rs.1 rs.2 (val₁ := Src.pushVal σ v) (val := Src.pushVal τ v)
        fun _ => by cases v <;> simp [Src.pushVal, Src.value_frame hag' hns]
      simp only [bind, Except.bind]
      revert h
      cases pushAt σ E rs.1 rs.2 (Src.pushVal σ v) <;> cases pushAt τ E rs.1 rs.2 (Src.pushVal τ v) <;>
        intro h <;> first | trivial | exact h.elim | exact ⟨ns, hns, h⟩
  | .transfer r a => by
    obtain ⟨ns, hns, hag'⟩ := hag
    simp only [Stmt.run, r.eval_frame hag' hns, a.eval_frame hag' hns]
    cases r.eval τ with
    | error _ => trivial
    | ok v =>
      simp only [bind, Except.bind]
      cases v.asInt with
      | error _ => trivial
      | ok addr =>
        simp only
        cases a.eval τ with
        | error _ => trivial
        | ok w =>
          simp only
          cases w.asInt with
          | error _ => trivial
          | ok amt =>
            dsimp only
            have h := transferAt_agree hag' addr amt
            revert h
            cases transferAt σ addr amt <;> cases transferAt τ addr amt <;> intro h <;>
              first | trivial | exact h.elim | exact ⟨ns, hns, h⟩
  | .bindPush (R := R) k b _ => by
    obtain ⟨ns, hns, hag'⟩ := hag
    simp only [Stmt.run, b.resolve_frame hag' hns]
    cases b.resolve τ with
    | error _ => trivial
    | ok rs =>
      have h := pushPlaceAt_agree hag' (.ref R) rs.1 rs.2
      simp only [bind, Except.bind]
      revert h
      cases pushPlaceAt σ (.ref R) rs.1 rs.2 with
      | error _ => cases pushPlaceAt τ (.ref R) rs.1 rs.2 <;> intro h <;> first | trivial | exact h.elim
      | ok a =>
        cases pushPlaceAt τ (.ref R) rs.1 rs.2 with
        | error _ => intro h; exact h.elim
        | ok b' =>
          rintro ⟨h₁, h₂⟩
          obtain ⟨σa, na⟩ := a; obtain ⟨σb, nb⟩ := b'
          simp only at h₂; subst h₂
          exact StateAgree.setEnv ⟨ns, hns, h₁⟩ k.name _ fun n hn hne => k.isFresh_out n hn hne
  | .pop b => by
    obtain ⟨ns, hns, hag'⟩ := hag
    simp only [Stmt.run, b.resolve_frame hag' hns]
    cases b.resolve τ with
    | error _ => trivial
    | ok rs =>
      have h := popAt_agree hag' rs.1 rs.2
      simp only [bind, Except.bind]
      revert h
      cases popAt σ rs.1 rs.2 <;> cases popAt τ rs.1 rs.2 <;>
        intro h <;> first | trivial | exact h.elim | exact ⟨ns, hns, h⟩
  | .declMem R x hx init _ => by
    obtain ⟨ns, hns, hag'⟩ := hag
    have hfr : ∀ n, isFresh C Γ n = true → n ≠ x → isFresh C (setBy x (.mem (.ref R)) Γ) n = true :=
      fun n hn hne => isFresh_setBy hn hne
    cases init with
    | none =>
      have h := allocDefault_agree hag' R
      simp only [Stmt.run]
      revert h
      cases allocDefault σ R <;> cases allocDefault τ R <;> intro h <;> first | trivial | exact h.elim | skip
      rename_i a b
      obtain ⟨hab, he⟩ := h
      simp only [bind, Except.bind, pure, Except.pure, he]
      exact StateAgree.setEnv ⟨ns, hns, hab⟩ x _ hfr
    | some r =>
      cases r with
      | alias p =>
        simp only [Stmt.run, MRhs.bind, p.mval_frame hag' hns]
        cases p.mval τ with
        | error _ => trivial
        | ok v =>
          simp only [bind, Except.bind]
          cases v.asRef with
          | error _ => trivial
          | ok id => exact StateAgree.setEnv ⟨ns, hns, hag'⟩ x _ hfr
      | copy p _ =>
        simp only [Stmt.run, MRhs.bind, p.resolve_frame hag' hns, findStorage_congr hag']
        cases p.resolve τ with
        | error _ => trivial
        | ok rs =>
          simp only [bind, Except.bind]
          cases τ.findStorage rs.1 rs.2 with
          | error _ => trivial
          | ok sv =>
            simp only
            have h := copyStToM_agree hag' sv
            revert h
            cases copyStToM σ sv <;> cases copyStToM τ sv <;> intro h <;>
              first | trivial | exact h.elim | skip
            rename_i a b
            obtain ⟨hab, he⟩ := h
            obtain ⟨σa, ma⟩ := a
            obtain ⟨σb, mb⟩ := b
            simp only at he hab
            subst he
            cases ma with
            | prim _ => trivial
            | ref id => exact StateAgree.setEnv ⟨ns, hns, hab⟩ x _ hfr
  | .rebindMem x h r => by
    obtain ⟨ns, hns, hag'⟩ := hag
    cases r with
    | alias p =>
      simp only [Stmt.run, MRhs.bind, p.mval_frame hag' hns]
      cases p.mval τ with
      | error _ => trivial
      | ok v =>
        simp only [bind, Except.bind]
        cases v.asRef with
        | error _ => trivial
        | ok id => exact StateAgree.setEnv ⟨ns, hns, hag'⟩ x _ fun n hn _ => hn
    | copy p _ =>
      simp only [Stmt.run, MRhs.bind, p.resolve_frame hag' hns, findStorage_congr hag']
      cases p.resolve τ with
      | error _ => trivial
      | ok rs =>
        simp only [bind, Except.bind]
        cases τ.findStorage rs.1 rs.2 with
        | error _ => trivial
        | ok sv =>
          simp only
          have h := copyStToM_agree hag' sv
          revert h
          cases copyStToM σ sv <;> cases copyStToM τ sv <;> intro h <;>
            first | trivial | exact h.elim | skip
          rename_i a b
          obtain ⟨hab, he⟩ := h
          obtain ⟨σa, ma⟩ := a
          obtain ⟨σb, mb⟩ := b
          simp only at he hab
          subst he
          cases ma with
          | prim _ => trivial
          | ref id => exact StateAgree.setEnv ⟨ns, hns, hab⟩ x _ fun n hn _ => hn
  | .assignFromMem l p => by
    obtain ⟨ns, hns, hag'⟩ := hag
    simp only [Stmt.run, p.mval_frame hag' hns, l.target_frame hag' hns]
    cases p.mval τ with
    | error _ => trivial
    | ok mv =>
      simp only [bind, Except.bind, copyMem_congr hag']
      cases copyMem τ mv with
      | error _ => trivial
      | ok sv =>
        simp only
        cases l.target τ with
        | error _ => trivial
        | ok rs => exact StateAgree.save ⟨ns, hns, hag'⟩ _ _ _
  | .assignMem l r => by
    obtain ⟨ns, hns, hag'⟩ := hag
    have hr : r.mval σ = r.mval τ := by
      cases r <;> simp [MSrc.mval, Val.eval_frame hag' hns, MPath.mval_frame hag' hns]
    simp only [Stmt.run, hr]
    cases r.mval τ with
    | error _ => trivial
    | ok mv =>
      simp only [bind, Except.bind]
      have h := MLoc.write_agree hag' hns mv l
      revert h
      cases l.write σ mv <;> cases l.write τ mv <;> intro h <;>
        first | trivial | exact h.elim | exact ⟨ns, hns, h⟩
  | .rebind x h r => by
    obtain ⟨ns, hns, hag'⟩ := hag
    simp only [Stmt.run, r.resolve_frame hag' hns]
    cases r.resolve τ with
    | error _ => trivial
    | ok rs =>
      exact StateAgree.setEnv ⟨ns, hns, hag'⟩ x _ fun n hn _ => hn
  | .assignLocal x h r => by
    obtain ⟨ns, hns, hag'⟩ := hag
    simp only [Stmt.run, r.eval_frame hag' hns]
    cases r.eval τ with
    | error _ => trivial
    | ok v => exact StateAgree.setEnv ⟨ns, hns, hag'⟩ x _ fun n hn _ => hn
  | .declLocal p x hx init => by
    obtain ⟨ns, hns, hag'⟩ := hag
    have hfr : ∀ n, isFresh C Γ n = true → n ≠ x → isFresh C (setBy x (.stack (.prim p)) Γ) n = true :=
      fun n hn hne => isFresh_setBy hn hne
    cases init with
    | none => exact StateAgree.setEnv ⟨ns, hns, hag'⟩ x _ hfr
    | some e =>
      simp only [Stmt.run, e.eval_frame hag' hns]
      cases e.eval τ with
      | error _ => trivial
      | ok v => exact StateAgree.setEnv ⟨ns, hns, hag'⟩ x _ hfr
  | .declStorage _ _ x hx init => by
    obtain ⟨ns, hns, hag'⟩ := hag
    simp only [Stmt.run, init.resolve_frame hag' hns]
    cases init.resolve τ with
    | error _ => trivial
    | ok rs =>
      exact StateAgree.setEnv ⟨ns, hns, hag'⟩ x _ fun n hn hne => isFresh_setBy hn hne
  | .delete l => by
    obtain ⟨ns, hns, hag'⟩ := hag
    simp only [Stmt.run, l.resolve_frame hag' hns, findStorage_congr hag']
    cases l.resolve τ with
    | error _ => trivial
    | ok rs =>
      simp only [bind, Except.bind]
      cases τ.findStorage rs.1 rs.2 with
      | error _ => trivial
      | ok cur => exact StateAgree.save ⟨ns, hns, hag'⟩ _ _ _
  | .ite c thn els => by
    obtain ⟨ns, hns, hag'⟩ := hag
    simp only [Stmt.run, c.eval_frame hag' hns]
    cases c.eval τ with
    | error _ => trivial
    | ok v =>
      cases v with
      | int _ => trivial
      | bool b =>
        cases b
        · exact els.run_frame ⟨ns, hns, hag'⟩
        · exact thn.run_frame ⟨ns, hns, hag'⟩
  | .require c | .assert c => by
    obtain ⟨ns, hns, hag'⟩ := hag
    simp only [Stmt.run, c.eval_frame hag' hns]
    cases c.eval τ with
    | error _ => trivial
    | ok v =>
      cases v with
      | int _ => trivial
      | bool b => cases b <;> first | trivial | exact ⟨ns, hns, hag'⟩
  | .revert => trivial

/-- **Frame, for blocks.** -/
theorem Prog.run_frame {Γ Γ' : Ctx} {σ τ : State} (hag : StateAgree C Γ σ τ) :
    (P : Prog C Γ Γ') → ResAgreeAt C Γ' (P.run σ) (P.run τ)
  | .nil => hag
  | .cons s P => by
    have hs := s.run_frame hag
    simp only [Prog.run]
    revert hs
    cases s.run σ <;> cases s.run τ <;> intro hs <;> simp only [ResAgreeAt] at hs
    all_goals first | trivial | exact hs.elim | exact P.run_frame hs

end

/-! ## Postconditions and continuations -/

/-- A postcondition: first order, over the values of a context. -/
inductive Post (C : Contract) : Ctx → Type where
  | tt {Γ : Ctx} : Post C Γ
  /-- `c` holds: it evaluates to `true`. -/
  | atom {Γ : Ctx} (c : Val C Γ .bool) : Post C Γ
  | not {Γ : Ctx} (φ : Post C Γ) : Post C Γ
  | and {Γ : Ctx} (φ ψ : Post C Γ) : Post C Γ
  | or {Γ : Ctx} (φ ψ : Post C Γ) : Post C Γ
  | imp {Γ : Ctx} (φ ψ : Post C Γ) : Post C Γ

def Post.holds {Γ : Ctx} (σ : State) : Post C Γ → Prop
  | .tt => True
  | .atom c => c.eval σ = .ok (.bool true)
  | .not φ => ¬ φ.holds σ
  | .and φ ψ => φ.holds σ ∧ ψ.holds σ
  | .or φ ψ => φ.holds σ ∨ ψ.holds σ
  | .imp φ ψ => φ.holds σ → ψ.holds σ

/-- A postcondition reads the same in agreeing states. -/
theorem Post.holds_frame {Γ : Ctx} {σ τ : State} (hag : StateAgree C Γ σ τ) :
    (φ : Post C Γ) → (φ.holds σ ↔ φ.holds τ)
  | .tt => Iff.rfl
  | .atom c => by obtain ⟨ns, hns, hag⟩ := hag; simp only [Post.holds, c.eval_frame hag hns]
  | .not φ => by simp only [Post.holds, φ.holds_frame hag]
  | .and φ ψ => by simp only [Post.holds, φ.holds_frame hag, ψ.holds_frame hag]
  | .or φ ψ => by simp only [Post.holds, φ.holds_frame hag, ψ.holds_frame hag]
  | .imp φ ψ => by simp only [Post.holds, φ.holds_frame hag, ψ.holds_frame hag]

/-- `c` is defined: it evaluates to a boolean.  Written in the language, as
`c || !c`. -/
def Post.defined {Γ : Ctx} (c : Simple C Γ .bool) : Post C Γ :=
  .atom (.binop .or rfl rfl (.simple c) (.unop .not rfl rfl (.simple c)))

theorem Post.defined_holds {Γ : Ctx} {σ : State} (c : Simple C Γ .bool) :
    (Post.defined c).holds σ ↔ ∃ b, c.eval σ = .ok (.bool b) := by
  simp only [Post.defined, Post.holds, Val.eval, unopCheck]
  cases c.eval σ with
  | error _ => simp [bind, Except.bind]
  | ok v =>
    cases v with
    | int _ => simp [bind, Except.bind, applyUnOp, Value.asBool]
    | bool b =>
      cases b <;> simp [bind, Except.bind, pure, Except.pure, applyUnOp, applyBinOp, Value.asBool,
        checkArith]

/-- What a modality says of a run. -/
def after (m : Modality) (r : Res State) (p : State → Prop) : Prop :=
  match r with
  | .ok σ => p σ
  | .error _ => m = .box

theorem after_bind (m : Modality) (r : Res State) (f : State → Res State) (p : State → Prop) :
    after m (r >>= f) p ↔ after m r (fun σ => after m (f σ) p) := by
  cases r <;> rfl

theorem after_mono {m : Modality} {r : Res State} {p q : State → Prop} (h : ∀ σ, p σ → q σ) :
    after m r p → after m r q := by
  cases r <;> simp [after] <;> exact h _

/-- What is left to prove: a postcondition, a program and then more, or a
continuation read at a larger context. -/
inductive Kont (C : Contract) : Ctx → Type where
  | post {Γ : Ctx} (ψ : Post C Γ) : Kont C Γ
  | modal {Γ Γ' : Ctx} (m : Modality) (P : Prog C Γ Γ') (k : Kont C Γ') : Kont C Γ
  | up {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') (k : Kont C Γ) : Kont C Γ'

def Kont.holds {Γ : Ctx} : Kont C Γ → State → Prop
  | .post ψ, σ => ψ.holds σ
  | .modal m P k, σ => after m (P.run σ) k.holds
  | .up _ k, σ => k.holds σ

/-- **Frame, for continuations.**  Agreeing states satisfy the same
continuations: `⟨ uint x = alice.age; ⟩ x == 10` does not see a scratch
alias. -/
theorem Kont.holds_frame {Γ : Ctx} {σ τ : State} (hag : StateAgree C Γ σ τ) :
    (k : Kont C Γ) → (k.holds σ ↔ k.holds τ)
  | .post ψ => ψ.holds_frame hag
  | .modal m P k => by
    have hP := P.run_frame hag
    simp only [Kont.holds]
    revert hP
    cases P.run σ <;> cases P.run τ <;> intro hP <;> simp only [ResAgreeAt] at hP <;>
      simp only [after]
    all_goals first | exact Iff.rfl | exact hP.elim | exact k.holds_frame hP
  | .up h k => k.holds_frame (hag.of_sub h)

/-! ## Hypotheses -/

/-- The hypotheses of a goal, in the order symbolic execution collected
them: path conditions (`c = b`) and updates, from the initial context to the
current one. -/
inductive Hyps (C : Contract) : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : Hyps C Γ Γ
  /-- A precondition on the initial state: `alice.age == 3`, or that the
  storage is `C`'s initial one. -/
  | assume {Γ : Ctx} (φ : State → Prop) : Hyps C Γ Γ
  | cond {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) (c : Simple C Γ .bool) (b : Bool) : Hyps C Γ₀ Γ
  | upd {Γ₀ Γ Γ' : Ctx} (H : Hyps C Γ₀ Γ) (m : Modality) (U : Upd C Γ) : Hyps C Γ₀ Γ'
  | shrink {Γ₀ Γ Γ' : Ctx} (H : Hyps C Γ₀ Γ') (h : Ctx.Sub C Γ Γ') : Hyps C Γ₀ Γ

/-- The hypotheses as a predicate transformer: `H.holds p σ` says `p` holds
in the state they lead to from `σ`, whenever their conditions hold. -/
def Hyps.holds {Γ₀ Γ : Ctx} : Hyps C Γ₀ Γ → (State → Prop) → State → Prop
  | .nil, p, σ => p σ
  | .assume φ, p, σ => φ σ → p σ
  | .cond H c b, p, σ => H.holds (fun σ' => c.eval σ' = .ok (.bool b) → p σ') σ
  | .upd H m U, p, σ => H.holds (fun σ' => after m (U.apply σ') p) σ
  | .shrink H _, p, σ => H.holds p σ

theorem Hyps.mono {Γ₀ Γ : Ctx} {p q : State → Prop} (h : ∀ σ, p σ → q σ) :
    (H : Hyps C Γ₀ Γ) → ∀ σ, H.holds p σ → H.holds q σ
  | .nil, σ, hp => h σ hp
  | .assume _, σ, hp => fun hφ => h σ (hp hφ)
  | .cond H c b, σ, hp =>
    H.mono (p := fun σ' => c.eval σ' = .ok (.bool b) → p σ')
      (q := fun σ' => c.eval σ' = .ok (.bool b) → q σ') (fun σ' hp' hc => h σ' (hp' hc)) σ hp
  | .upd H m U, σ, hp =>
    H.mono (p := fun σ' => after m (U.apply σ') p) (q := fun σ' => after m (U.apply σ') q)
      (fun _ => after_mono h) σ hp
  | .shrink H _, σ, hp => H.mono h σ hp

theorem Hyps.and {Γ₀ Γ : Ctx} {p q : State → Prop} :
    (H : Hyps C Γ₀ Γ) → ∀ σ, H.holds p σ → H.holds q σ → H.holds (fun σ' => p σ' ∧ q σ') σ
  | .nil, σ, hp, hq => ⟨hp, hq⟩
  | .assume _, σ, hp, hq => fun hφ => ⟨hp hφ, hq hφ⟩
  | .cond H c b, σ, hp, hq =>
    H.mono (fun σ' (h : _ ∧ _) hc => ⟨h.1 hc, h.2 hc⟩) σ (H.and σ hp hq)
  | .upd H m U, σ, hp, hq => by
    refine H.mono (fun σ' (h : _ ∧ _) => ?_) σ (H.and σ hp hq)
    cases hU : U.apply σ' <;> simp_all [after]
  | .shrink H _, σ, hp, hq => H.and σ hp hq

/-! ## The proof system -/

/-- A block, then another, runs as the first then the second. -/
theorem Prog.run_append {Γ Γ₁ Γ₂ : Ctx} (σ : State) :
    (P : Prog C Γ Γ₁) → (Q : Prog C Γ₁ Γ₂) → (P.append Q).run σ = P.run σ >>= Q.run
  | .nil, Q => by simp [Prog.append, Prog.run]
  | .cons s P, Q => by
    simp only [Prog.append, Prog.run]
    cases s.run σ with
    | error _ => rfl
    | ok σ' => exact Prog.run_append σ' P Q

/-- **The proof system.**  `Proves H k`: under the hypotheses `H`, the
continuation `k` holds.  A taclet rewrites the first statement of a modality
(`update`, `unfold`, `split`, `done`); an empty modality gives way to what
follows it; a postcondition is closed by proving it. -/
inductive Proves : {Γ₀ Γ : Ctx} → Hyps C Γ₀ Γ → Kont C Γ → Prop where
  /-- `{U} ⟨[ ω ]⟩ k` proves `⟨[ s; ω ]⟩ k`. -/
  | update {Γ₀ Γ Γ' Γe : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'} {U : Upd C Γ}
      {ω : Prog C Γ' Γe} {k : Kont C Γe} (d : Taclet C m s (.update U)) :
      Proves (H.upd m U) (.modal m ω k) → Proves H (.modal m (.cons s ω) k)
  /-- `⟨[ P ]⟩ (up ⟨[ ω ]⟩ k)` proves `⟨[ s; ω ]⟩ k`. -/
  | unfold {Γ₀ Γ Γ' Γ₁ Γe : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ns : List Name} {P : Prog C Γ Γ₁} {h : Ctx.Sub C Γ' Γ₁} {ω : Prog C Γ' Γe} {k : Kont C Γe}
      (d : Taclet C m s (.unfold ns P h)) :
      Proves H (.modal m P (.up h (.modal m ω k))) → Proves H (.modal m (.cons s ω) k)
  /-- `c = true ⟹ ⟨[ P; ω ]⟩ k` and `c = false ⟹ ⟨[ Q; ω ]⟩ k` prove
  `⟨[ s; ω ]⟩ k`; under a diamond, so does `c` being defined. -/
  | split {Γ₀ Γ Γ' Γe : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'} {c : Simple C Γ .bool}
      {P Q : Prog C Γ Γ'} {ω : Prog C Γ' Γe} {k : Kont C Γe} (d : Taclet C m s (.split c P Q)) :
      Proves (H.cond c true) (.modal m (P.append ω) k) →
      Proves (H.cond c false) (.modal m (Q.append ω) k) →
      (m = .diamond → Proves H (.post (.defined c))) →
      Proves H (.modal m (.cons s ω) k)
  /-- A revert closes a box, as far as the hypotheses allow (an update under
  a diamond that fails is false, and so is what follows it). -/
  | done {Γ₀ Γ Γ' Γe : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'} {ω : Prog C Γ' Γe}
      {k : Kont C Γe} (d : Taclet C m s (.done true)) :
      Proves H (.post .tt) → Proves H (.modal m (.cons s ω) k)
  /-- `⟨[ ]⟩ k` is `k`. -/
  | empty {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {k : Kont C Γ} :
      Proves H k → Proves H (.modal m .nil k)
  /-- A continuation read at a larger context. -/
  | up {Γ₀ Γ Γ' : Ctx} {H : Hyps C Γ₀ Γ'} {h : Ctx.Sub C Γ Γ'} {k : Kont C Γ} :
      Proves (H.shrink h) k → Proves H (.up h k)
  /-- Hypotheses no state satisfies prove anything: `x = 1, x != 1 ⊢ k`. -/
  | absurd {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {k : Kont C Γ} :
      (∀ σ, H.holds (fun _ => False) σ) → Proves H k
  /-- A postcondition, proved in every state the hypotheses allow. -/
  | close {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {ψ : Post C Γ} :
      (∀ σ, H.holds ψ.holds σ) → Proves H (.post ψ)

/-- **Soundness.**  A derivation of `H ⊢ k` proves `k` in every state `H`
allows.  From the empty hypotheses: a derivation of `⊢ ⟨ P ⟩ ψ` proves that
`P` ends normally in a state satisfying `ψ`, from every state. -/
theorem Proves.sound {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {k : Kont C Γ} (d : Proves H k) :
    ∀ σ, H.holds k.holds σ := by
  induction d with
  | update d _ ih =>
    intro σ
    refine Hyps.mono (fun σ' h => ?_) _ σ (ih σ)
    simp only [Kont.holds, Prog.run, after_bind] at h ⊢
    rw [(Taclet.sound d) σ']; exact h
  | @unfold Γ Γ' Γ₁ Γe H m s ns P h ω k d _ ih =>
    intro σ
    refine Hyps.mono (fun σ' hp => ?_) _ σ (ih σ)
    obtain ⟨hfr, hok⟩ := Taclet.sound d
    have hag := hok σ'
    simp only [Kont.holds, Prog.run, after_bind] at hp ⊢
    revert hp hag
    cases P.run σ' <;> cases s.run σ' <;> intro hp hag <;> (try simp only [SameOk] at hag) <;>
      (try simp only [after] at hp ⊢)
    all_goals first
      | exact hp
      | exact hag.elim
      | exact (Kont.holds_frame ⟨ns, hfr, hag⟩ (.modal m ω k)).mp hp
  | @split Γ Γ' Γe H m s c P Q ω k d _ _ hdef ih₁ ih₂ ihdef =>
    intro σ
    have hdef' : m = .diamond → H.holds (Post.defined c).holds σ := fun hm => ihdef hm σ
    have both := Hyps.and H σ (ih₁ σ) (ih₂ σ)
    by_cases hm : m = .diamond
    · refine Hyps.mono (fun σ' ⟨⟨h₁, h₂⟩, hd⟩ => ?_) _ σ (Hyps.and H σ both (hdef' hm))
      obtain ⟨b, hb⟩ := (Post.defined_holds c).mp hd
      show after m (s.run σ' >>= ω.run) k.holds
      rw [(Taclet.sound d) σ', hb]
      cases b
      · have := h₂ hb; simp only [Kont.holds, Prog.run_append] at this; exact this
      · have := h₁ hb; simp only [Kont.holds, Prog.run_append] at this; exact this
    · refine Hyps.mono (fun σ' ⟨h₁, h₂⟩ => ?_) _ σ both
      have hbox : m = .box := by cases m <;> simp_all
      show after m (s.run σ' >>= ω.run) k.holds
      rw [(Taclet.sound d) σ']
      cases hc : c.eval σ' with
      | error _ => exact hbox
      | ok v =>
        cases v with
        | int _ => exact hbox
        | bool b =>
          cases b
          · have := h₂ hc; simp only [Kont.holds, Prog.run_append] at this; exact this
          · have := h₁ hc; simp only [Kont.holds, Prog.run_append] at this; exact this
  | @done Γ Γ' Γe H m s ω k d _ ih =>
    intro σ
    refine Hyps.mono (fun σ' _ => ?_) H σ (ih σ)
    obtain ⟨hrev, hb⟩ := (Taclet.sound d) σ'
    show after _ (s.run σ' >>= ω.run) k.holds
    rw [hrev]
    exact hb.mp rfl
  | empty _ ih => intro σ; exact ih σ
  | up _ ih => intro σ; exact ih σ
  | absurd h => intro σ; exact Hyps.mono (p := fun _ => False) (fun _ h => h.elim) _ σ (h σ)
  | close h => exact h

end Kernel
end Solidity
