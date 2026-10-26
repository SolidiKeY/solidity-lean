import Solidity.Calculus.SolSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.SoundLoops
import Solidity.Semantics.RunFuel
import Solidity.Semantics.RunAccel
import Solidity.Tools.LazyStorage
import Solidity.Tools.Common
import Solidity.Calculus.DeclarationFacts

/-!
# Counterexamples: scoped formulas evaluated in a typed state

`holds σ φ` (`Calculus/Logic.lean`) is a `Prop`: a quantifier ranges
over `2^256` values, an update over the typed states it lands on, `{havoc}` over every storage, so it cannot be computed.
`Fml.eval3` is its three-valued shadow over the typed state
(`State`): terms are read by the typed readers and updates computed
(`Upd.applyV`), the programs under a
modality are run by the typed run with fuel (`Prog.runF`,
`Semantics/RunFuel.lean`: a loop entered at most `loopFuel`
iterations, `unknown` past them), a loop that only counts in closed form
(`Prog.runA`, `Semantics/RunAccel.lean`), a quantifier and a hidden binder are
tried on a finite domain (`ff` as soon as one instance is), an update is
read in the one typed state its end lifts to (`State.lift?`: the heap
empty, the storage and the transaction its own), and the connectives are
Kleene's.  An answer is never wrong, only sometimes missing:
`Fml.eval3_tt` and `Fml.eval3_ff` say that `tt` implies `holds σ φ` and
`ff` implies `¬ holds σ φ`.

A counterexample to a specification (`refuteSpec`) is a state in
which the stated premises (`I ∧ requires`) evaluate to `tt` and a
conjunct after the call to `ff`.  The premises that are true by
construction (`R`, `L`, `msg.value`, `Calculus/SurfaceSpec.lean`) are not
evaluated but made true by the generator: arguments are drawn in their
type's range, storages are canonical (`Typing/Reachability.lean`: every
struct member present in order, a mapping's keys unique and its default the
type's), their words in range, and `msg.value` is `0` for a function that
is not `payable`.  The candidate is typed (`Cand C`: a storage at the
contract's types, drawn by `TGen.sval`, the transaction's words `uint`s), and
its state is a typed one with no locals (`Cand.tstate`); its arguments are
typed values with their types (`Semantics.CallValue`), which the formula's
binders read at their types (`CallValue.as?`).

The search is testing: small pools of values per primitive type (the
bounds, `0`, `1`, `2`, and the spec's own literals), all-default storages
over every combination of arguments first, then random states
(`TGen.sval` over the pools, seeded, so the result is the same on every
run).  A witness found is shrunk before it is shown
(Shrinking, below).

A witness is **certified** when the kernel checks `¬ ⊨ᶠ φ` of the scoped
formula from it: `Fml.not_valid_of_eval3Peel` applied to
`Fml.eval3Peel dom vals σ₀ φ = .ff`, `φ` with its leading parameters bound
to the witness's arguments `vals` (`Fml.peel`), which the kernel decides by
evaluating `peel`, `eval3` and the typed run on closed terms, the
candidate's typed state quoted constructor by constructor (`certifyRefl`).
When a quantified declaration premise cannot evaluate to `tt`, the fallback
(`certifyDeclarations`) proves its ranges and total reads structurally
(`Calculus/DeclarationFacts.lean`) and evaluates the remaining premises and
the body. Every premise of the original obligation is proved; unsupported
premises can still leave the witness only **tested**. What the kernel runs is written by the recursor
(`Fml.eval3`, `Fml.peel`, `Prog.runA`; Gate G0 conditions 1 and 2), each
with a compiled `match` twin the search runs (`Fml.eval3C`, `Fml.peelC`,
`Prog.runAC`) and a theorem that they agree.  A witness may need an array
no search can build (Long arrays, below): the kernel alone certifies it.
-/

namespace Solidity.Tools

/-! ## Three truth values -/

/-- Kleene's truth values: `unknown` where a finite evaluation cannot
decide. -/
inductive Tri where
  | tt
  | ff
  | unknown
  deriving DecidableEq, Repr, Inhabited

namespace Tri

/-- Negation. -/
def not : Tri → Tri
  | tt => ff
  | ff => tt
  | unknown => unknown

/-- Conjunction: `ff` wins over `unknown`. -/
def and : Tri → Tri → Tri
  | ff, _ => ff
  | _, ff => ff
  | tt, tt => tt
  | _, _ => unknown

/-- Implication: `ff → _` and `_ → tt` are `tt` whatever the other side. -/
def imp : Tri → Tri → Tri
  | ff, _ => tt
  | _, tt => tt
  | tt, ff => ff
  | _, _ => unknown

end Tri

end Solidity.Tools

namespace Solidity

open Solidity.Tools (Tri)

variable {C : Contract}

/-! ## The typed state an update ends in

An update leaves a global part and the locals' values (`Upd.applyV`), and
what follows it is read in every typed state with them (`holds`,
`Upd.afterT_applyV`).  One of them is enough to refute it: `State.lift?`
reads them back as a typed state where the heap is empty and the storage
and the transaction are the starting state's (a snapshot `old := storage`
is that storage), every local a value of its type, an unset alias or
memory local, a ledger. -/

/-- The locals' values, typed over the heap typing `H`: `none` where a
memory local's identity is no object of its type there. -/
def TEnv.liftV? (H : HTy) : (Δ : Ctx) → LocsV C Δ → Option (TEnv C H Δ)
  | [], _ => some ()
  | .val _ :: Δ, ℓ => do pure (ℓ _ .here, ← TEnv.liftV? H Δ fun _ i => ℓ _ (.there i))
  | .alias _ :: Δ, ℓ => do pure (ℓ _ .here, ← TEnv.liftV? H Δ fun _ i => ℓ _ (.there i))
  | .mem R :: Δ, ℓ => match (ℓ _ .here : Option Nat) with
    | none => do pure (none, ← TEnv.liftV? H Δ fun _ i => ℓ _ (.there i))
    | some id => do
      pure (some (← HRef.ofId? H R id), ← TEnv.liftV? H Δ fun _ i => ℓ _ (.there i))
  | .old :: Δ, ℓ => do pure (ℓ _ .here, ← TEnv.liftV? H Δ fun _ i => ℓ _ (.there i))
  | .oldNet :: Δ, ℓ => do pure (ℓ _ .here, ← TEnv.liftV? H Δ fun _ i => ℓ _ (.there i))
  | .kint :: Δ, ℓ => do pure (ℓ _ .here, ← TEnv.liftV? H Δ fun _ i => ℓ _ (.there i))

theorem TEnv.liftV?_get (H : HTy) : (Δ : Ctx) → (ℓ : LocsV C Δ) → (e' : TEnv C H Δ) →
    TEnv.liftV? H Δ ℓ = some e' → ∀ {t : LTy} (i : Idx Δ t),
      LTy.VDen.ofT t (TEnv.get i e') = ℓ t i
  | [], _, (), _, _, i => nomatch i
  | .val _ :: Δ, ℓ, e', h, t, i | .alias _ :: Δ, ℓ, e', h, t, i | .old :: Δ, ℓ, e', h, t, i
  | .oldNet :: Δ, ℓ, e', h, t, i | .kint :: Δ, ℓ, e', h, t, i => by
    simp only [TEnv.liftV?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨e'', he, rfl⟩ := h
    cases i with
    | here => rfl
    | there j => exact TEnv.liftV?_get H Δ _ e'' he j
  | .mem R :: Δ, ℓ, e', h, t, i => by
    simp only [TEnv.liftV?] at h
    split at h
    · rename_i hn
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e'', he, rfl⟩ := h
      cases i with
      | here => rw [hn]; rfl
      | there j => exact TEnv.liftV?_get H Δ _ e'' he j
    · rename_i id hn
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨r, hr, e'', he, rfl⟩ := h
      cases i with
      | here =>
        rw [hn]
        show Option.map (·.id) (some r) = some id
        unfold HRef.ofId? at hr
        split at hr
        · cases hr; rfl
        · cases hr
      | there j => exact TEnv.liftV?_get H Δ _ e'' he j

/-- **A typed state with the global part and the locals `q`**: `none`
where a memory local's identity is no object of its type in the global
part's heap. -/
def State.lift? {Γ Δ : Ctx} (σ : State C Γ) (q : GlobT C σ.H × LocsV C Δ) :
    Option (State C Δ) := do
  let g := q.1.1
  let env ← TEnv.liftV? g.H Δ q.2
  pure { storage := g.storage, H := g.H, heap := g.heap, env, net := g.net,
         selfBalance := g.selfBalance, tx := g.tx }

theorem State.lift?_spec {Γ Δ : Ctx} {σ : State C Γ} {q : GlobT C σ.H × LocsV C Δ}
    {σ' : State C Δ} (h : σ.lift? q = some σ') :
    σ'.glob = q.1.1 ∧ (∀ {t : LTy} (i : Idx Δ t), σ'.getV i = q.2 t i) := by
  unfold State.lift? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨env, hlift, rfl⟩ := h
  exact ⟨rfl, fun i => TEnv.liftV?_get _ Δ q.2 env hlift i⟩

/-! ## Evaluation -/

/-- The values a quantifier over each primitive type is tried on. -/
abbrev TDom := (p : PrimTy) → List p.Denote

/-- The iterations a loop is run for, at most, each time it is entered. -/
def loopFuel : Nat := 1000

/-- The values a hidden binder of type `t` is tried on in `σ`: the domain
for a value, unset for an alias or a memory local, `σ`'s storage and ledger
for a snapshot. -/
def TDom.bind {Γ : Ctx} (dom : TDom) (σ : State C Γ) : (t : LTy) → List (t.TDenote C σ.H)
  | .val p => dom p
  | .alias _ => [none]
  | .mem _ => [none]
  | .old => [σ.storage]
  | .oldNet => [σ.net]
  | .kint => (dom .int).map (·.1)

/-- What a modality says of a typed run: of the state it ends in, a halt as
`Modality.onTHalt` says, `ff` on a panic, `unknown` on `diverge` (a loop
past `loopFuel` iterations is one). -/
def Tri.afterT {α : Type} (m : Modality) (k : α → Tri) : TRes α → Tri
  | .ok a => k a
  | .error .panic => .ff
  | .error .diverge => .unknown
  | .error .exhausted => .tt
  | .error .revert | .error (.revertWith _) => match m with
    | .box => .tt
    | .diamond => .ff

/-- The program, then its frames, run with fuel (`Prog.runFrames`), counting
loops in closed form (`Prog.runA`, `Semantics/RunAccel.lean`). -/
def Prog.runFramesF {Γ Γ₁ Γ₀ : Ctx} (n : Nat) (σ : State C Γ) (P : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) : TRes (State C Γ₀) := do
  let o ← Prog.runA n P σ
  let o' ← Frames.runA n o.st κ
  pure o'.st

theorem Prog.runFramesF_approx {Γ Γ₁ Γ₀ : Ctx} (n : Nat) (σ : State C Γ) (P : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) : TRes.Approx (Prog.runFramesF n σ P κ) (Prog.runFrames σ P κ) :=
  (Prog.runA_approx n P σ).bind fun o => (Frames.runA_approx n o.st κ).bind fun _ => .refl _

/-- **`holds`, evaluated**, compiled: `dom p` is the finite domain a
quantifier over `p` is tried on.  The twin of `Fml.eval3` (`Fml.eval3_eq`). -/
def Fml.eval3C (dom : TDom) : {Γ : Ctx} → State C Γ → Fml C Γ → Tri
  | _, _, .tt => .tt
  | _, σ, .eq a b =>
    (a.eval σ).elim .unknown fun x => (b.eval σ).elim .unknown fun y => if x = y then .tt else .ff
  | _, σ, .wellFormed t => ((Tm.app1 .wt t).eval σ).elim .ff fun _ => .tt
  | _, σ, .not φ => (φ.eval3C dom σ).not
  | _, σ, .and φ ψ => (φ.eval3C dom σ).and (ψ.eval3C dom σ)
  | _, σ, .imp φ ψ => (φ.eval3C dom σ).imp (ψ.eval3C dom σ)
  | _, σ, .upd m U φ =>
    (U.applyV σ).elim (if m = .box || U.exh σ then .tt else .ff) fun τ =>
      (σ.lift? τ).elim .unknown fun σ' => if φ.eval3C dom σ' = .ff then .ff else .unknown
  | _, σ, .modal m P κ φ => Tri.afterT m (fun τ => φ.eval3C dom τ) (Prog.runFramesF loopFuel σ P κ)
  | _, σ, .havoc φ =>
    if φ.eval3C dom σ = .ff || φ.eval3C dom (σ.havoc σ.storage []) = .ff then .ff else .unknown
  | _, σ, .all _ p φ =>
    if (dom p).any fun v => φ.eval3C dom (σ.push (t := .val p) v) = .ff then .ff else .unknown
  | _, σ, .bind _ _ t φ =>
    if (dom.bind σ t).any fun v => φ.eval3C dom (σ.push v) = .ff then .ff else .unknown
  | _, σ, .anon xs φ =>
    if φ.eval3C dom (σ.anon xs fun x => TEnv.get x.2 σ.env) = .ff then .ff else .unknown
  | _, _, .allocAll .. | _, _, .grow .. => .unknown

theorem Fml.eval3C_sound (dom : TDom) : {Γ : Ctx} → (φ : Fml C Γ) → ∀ σ : State C Γ,
    (φ.eval3C dom σ = .tt → holds σ φ) ∧ (φ.eval3C dom σ = .ff → ¬ holds σ φ)
  | _, .tt, _ => ⟨fun _ => trivial, nofun⟩
  | _, .eq a b, σ => by
    simp only [Fml.eval3C, holds]
    cases ha : a.eval σ with
    | none => simp only [Option.elim, reduceCtorEq, false_implies, and_self]
    | some x =>
    cases hb : b.eval σ with
    | none => simp only [Option.elim, reduceCtorEq, false_implies, and_self]
    | some y =>
      simp only [Option.elim]
      have hda : a.denote σ = some x := Tm.denote_eval σ a x ha
      have hdb : b.denote σ = some y := Tm.denote_eval σ b y hb
      rw [hda, hdb, Option.some.injEq]
      by_cases hxy : x = y
      · subst hxy
        simp only [if_true, reduceCtorEq, false_implies, and_true]
        exact fun _ => trivial
      · simp only [hxy, if_false, reduceCtorEq, false_implies, true_and]
        exact fun _ h => h
  | _, .wellFormed t, σ => by
    simp only [Fml.eval3C]
    rw [holds_wellFormed_eval]
    cases h : (Tm.app1 .wt t).eval σ <;> simp only [Option.elim, ne_eq, reduceCtorEq, not_false_eq_true,
      imp_self, not_true_eq_false, and_self, implies_true, false_implies, true_implies]
  | _, .not φ, σ => by
    have ih := Fml.eval3C_sound dom φ σ
    simp only [Fml.eval3C, holds]
    cases h : φ.eval3C dom σ <;> simp_all only [Tri.not, reduceCtorEq, false_implies, forall_const,
      true_and, and_true, and_self, implies_true, not_true_eq_false, not_false_eq_true,
      Classical.not_not]
  | _, .and φ ψ, σ => by
    have ih₁ := Fml.eval3C_sound dom φ σ
    have ih₂ := Fml.eval3C_sound dom ψ σ
    simp only [Fml.eval3C, holds]
    cases h₁ : φ.eval3C dom σ <;> cases h₂ : ψ.eval3C dom σ <;>
      simp_all only [Tri.and, reduceCtorEq, false_implies, forall_const, true_and, and_true,
        and_false, false_and, and_self, implies_true, not_true_eq_false, not_false_eq_true, not_and]
  | _, .imp φ ψ, σ => by
    have ih₁ := Fml.eval3C_sound dom φ σ
    have ih₂ := Fml.eval3C_sound dom ψ σ
    simp only [Fml.eval3C, holds]
    cases h₁ : φ.eval3C dom σ <;> cases h₂ : ψ.eval3C dom σ <;>
      simp_all only [Tri.imp, reduceCtorEq, false_implies, forall_const, true_and, and_true,
        and_self, implies_true, not_true_eq_false, not_false_eq_true, not_imp]
  | _, .upd m U φ, σ => by
    simp only [Fml.eval3C]
    show (_ → U.afterT m σ (holds · φ)) ∧ (_ → ¬ U.afterT m σ (holds · φ))
    rw [Upd.afterT_applyV]
    cases hU : U.applyV σ with
    | none =>
      cases m <;> cases U.exh σ <;> simp only [Option.elim, Modality.onHalt, reduceCtorEq, imp_self,
        not_true_eq_false, not_false_eq_true, and_self, true_implies, false_implies, if_true,
        if_false, Bool.or_true, Bool.or_false, Bool.true_or, Bool.false_or, decide_true,
        decide_false, true_or, or_true, false_or, or_false, Bool.false_eq_true, ↓reduceIte,
        not_false_eq_true, Tri.noConfusion, implies_true]
    | some τ =>
      simp only [Option.elim]
      cases hl : σ.lift? τ with
      | none => exact ⟨fun h => Tri.noConfusion h, fun h => Tri.noConfusion h⟩
      | some σ' =>
        simp only
        split
        · rename_i hff
          obtain ⟨hg, hl'⟩ := State.lift?_spec hl
          exact ⟨fun h => Tri.noConfusion h,
            fun _ hall => (Fml.eval3C_sound dom φ σ').2 hff (hall σ' hg hl')⟩
        · exact ⟨fun h => Tri.noConfusion h, fun h => Tri.noConfusion h⟩
  | _, .modal m P κ φ, σ => by
    simp only [Fml.eval3C, holds]
    have happ := Prog.runFramesF_approx loopFuel σ P κ
    cases hr : Prog.runFramesF loopFuel σ P κ with
    | ok τ =>
      rw [hr] at happ
      rw [← happ.eq nofun]
      have ih := Fml.eval3C_sound dom φ τ
      simp only [Tri.afterT, Modality.afterRunTR]
      exact ⟨fun h => ⟨ih.1 h, nofun⟩, fun h hh => ih.2 h hh.1⟩
    | error e =>
      rw [hr] at happ
      cases e with
      | diverge => exact ⟨nofun, nofun⟩
      | panic =>
        rw [← happ.eq nofun]
        simp only [Tri.afterT, Modality.afterRunTR, reduceCtorEq, ne_eq,
          not_true_eq_false, and_false, not_false_eq_true, imp_self, and_self]
      | exhausted =>
        rw [← happ.eq nofun]
        cases m <;> simp only [Tri.afterT, Modality.afterRunTR, Modality.onTHalt, ne_eq,
          Except.error.injEq, reduceCtorEq, not_false_eq_true, and_self, implies_true,
          false_implies]
      | revert =>
        rw [← happ.eq nofun]
        cases m <;> simp only [Tri.afterT, Modality.afterRunTR, Modality.onTHalt, ne_eq,
          Except.error.injEq, reduceCtorEq, not_false_eq_true, and_self, implies_true,
          and_true, not_true_eq_false, imp_self]
      | revertWith _ =>
        rw [← happ.eq nofun]
        cases m <;> simp only [Tri.afterT, Modality.afterRunTR, Modality.onTHalt, ne_eq,
          Except.error.injEq, reduceCtorEq, not_false_eq_true, and_self, implies_true,
          and_true, not_true_eq_false, imp_self]
  | _, .havoc φ, σ => by
    simp only [Fml.eval3C, holds]
    split
    · rename_i h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      refine ⟨nofun, fun _ hall => ?_⟩
      rcases h with h | h
      · exact (Fml.eval3C_sound dom φ σ).2 h
          (by simpa only [State.havoc_self] using hall σ.storage σ.net σ.selfBalance)
      · exact (Fml.eval3C_sound dom φ _).2 h (hall _ _ σ.selfBalance)
    · exact ⟨nofun, nofun⟩
  | _, .all _ p φ, σ => by
    simp only [Fml.eval3C, holds]
    split
    · rename_i h
      obtain ⟨v, _, hff⟩ := List.any_eq_true.mp h
      exact ⟨nofun, fun _ hall => (Fml.eval3C_sound dom φ _).2 (of_decide_eq_true hff) (hall v)⟩
    · exact ⟨nofun, nofun⟩
  | _, .bind m _ t φ, σ => by
    simp only [Fml.eval3C, holds]
    split
    · rename_i h
      obtain ⟨v, _, hff⟩ := List.any_eq_true.mp h
      exact ⟨nofun, fun _ hall => (Fml.eval3C_sound dom φ _).2 (of_decide_eq_true hff) (hall v)⟩
    · exact ⟨nofun, nofun⟩
  | _, .anon xs φ, σ => by
    simp only [Fml.eval3C, holds]
    split
    · rename_i h
      exact ⟨nofun, fun _ hall => (Fml.eval3C_sound dom φ _).2 h (hall _)⟩
    · exact ⟨nofun, nofun⟩
  | _, .allocAll .., _ => ⟨nofun, nofun⟩
  | _, .grow _, _ => ⟨fun h => by simp only [Fml.eval3C, reduceCtorEq] at h,
      fun h => by simp only [Fml.eval3C, reduceCtorEq] at h⟩

/-- **`holds`, evaluated**, by its recursor (Gate G0 conditions 1 and 2):
what the kernel runs in a certificate.  Compiled as `Fml.eval3C`. -/
@[implemented_by Fml.eval3C]
def Fml.eval3 (dom : TDom) {Γ : Ctx} (σ : State C Γ) (φ : Fml C Γ) : Tri :=
  Fml.rec (motive := fun Γ _ => State C Γ → Tri)
    (fun _ => .tt)
    (fun a b σ => (a.eval σ).elim .unknown fun x =>
      (b.eval σ).elim .unknown fun y => if x = y then .tt else .ff)
    (fun t σ => ((Tm.app1 .wt t).eval σ).elim .ff fun _ => .tt)
    (fun _ ih σ => (ih σ).not)
    (fun _ _ ih₁ ih₂ σ => (ih₁ σ).and (ih₂ σ))
    (fun _ _ ih₁ ih₂ σ => (ih₁ σ).imp (ih₂ σ))
    (fun m U _ ih σ => (U.applyV σ).elim (if m = .box || U.exh σ then .tt else .ff) fun τ =>
      (σ.lift? τ).elim .unknown fun σ' => if ih σ' = .ff then .ff else .unknown)
    (fun m P κ _ ih σ => Tri.afterT m (fun τ => ih τ) (Prog.runFramesF loopFuel σ P κ))
    (fun _ ih σ => if ih σ = .ff || ih (σ.havoc σ.storage []) = .ff then .ff else .unknown)
    (fun _ p _ ih σ =>
      if (dom p).any fun v => ih (σ.push (t := .val p) v) = .ff then .ff else .unknown)
    (fun _ _ t _ ih σ => if (dom.bind σ t).any fun v => ih (σ.push v) = .ff then .ff else .unknown)
    (fun xs _ ih σ =>
      if ih (σ.anon xs fun x => TEnv.get x.2 σ.env) = .ff then .ff else .unknown)
    (fun _ _ _ _ _ => .unknown)
    (fun _ _ _ => .unknown)
    φ σ

theorem Fml.eval3_eq (dom : TDom) : {Γ : Ctx} → (φ : Fml C Γ) → ∀ σ : State C Γ,
    φ.eval3 dom σ = φ.eval3C dom σ
  | _, .tt, _ | _, .eq .., _ | _, .wellFormed _, _ => rfl
  | _, .not φ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ]; rfl
  | _, .and φ ψ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ, ← Fml.eval3_eq dom ψ]; rfl
  | _, .imp φ ψ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ, ← Fml.eval3_eq dom ψ]; rfl
  | _, .upd _ _ φ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ]; rfl
  | _, .modal _ _ _ φ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ]; rfl
  | _, .havoc φ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ]; rfl
  | _, .all _ _ φ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ]; rfl
  | _, .bind _ _ _ φ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ]; rfl
  | _, .anon _ φ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ]; rfl
  | _, .allocAll .., _ | _, .grow .., _ => rfl

theorem Fml.eval3_sound (dom : TDom) {Γ : Ctx} (φ : Fml C Γ) (σ : State C Γ) :
    (φ.eval3 dom σ = .tt → holds σ φ) ∧ (φ.eval3 dom σ = .ff → ¬ holds σ φ) := by
  rw [Fml.eval3_eq]
  exact Fml.eval3C_sound dom φ σ

/-- **A `tt` is a truth**: `φ` holds in `σ`. -/
theorem Fml.eval3_tt {dom : TDom} {Γ : Ctx} {σ : State C Γ} {φ : Fml C Γ}
    (h : φ.eval3 dom σ = .tt) : holds σ φ :=
  (Fml.eval3_sound dom φ σ).1 h

/-- **An `ff` is a counterexample**: `φ` does not hold in `σ`. -/
theorem Fml.eval3_ff {dom : TDom} {Γ : Ctx} {σ : State C Γ} {φ : Fml C Γ}
    (h : φ.eval3 dom σ = .ff) : ¬ holds σ φ :=
  (Fml.eval3_sound dom φ σ).2 h

end Solidity

namespace Solidity.Tools

open Semantics (uintBound intBound lookupBy)

variable {C : Contract}

/-! ## The values tried -/

/-- The integer literals a clause mentions. -/
def specNums : SpecExpr → List Int
  | .num n | .uintLit n => [n]
  | .old e | .net e | .field e _ | .unop _ e | .all _ _ e | .ex _ _ e => specNums e
  | .index a b | .binop _ a b | .imp a b | .iff a b => specNums a ++ specNums b
  | .member _ key items => specNums key ++ items.flatMap specNums
  | .bool _ | .name _ | .result => []

/-- The integer literals a location's keys mention. -/
def locNums : SpecLoc → List Int
  | .root _ => []
  | .field l _ | .all l => locNums l
  | .index l e => locNums l ++ specNums e

/-- The `uint`s tried: `0`, `1`, `2`, each literal `n` of the specification
with `n ± 1`, and the two largest, in that order: a combination of small
arguments is tried first. -/
def uintPool (lits : List Int) : List Int :=
  (([0, 1, 2] ++ lits.flatMap (fun n => [n, n + 1, n - 1]) ++ [uintBound - 1, uintBound - 2]).filter
    fun n => decide (0 ≤ n ∧ n < uintBound)).eraseDups

/-- The `int`s tried: `0`, `±1`, the bounds, and each literal with its
negation and neighbours. -/
def intPool (lits : List Int) : List Int :=
  (([0, 1, -1] ++ lits.flatMap (fun n => [n, -n, n + 1, n - 1]) ++ [-intBound, intBound - 1]).filter
    fun n => decide (-intBound ≤ n ∧ n < intBound)).eraseDups

/-- **The domain a quantifier and a hidden binder are tried on**: the pools
of `lits` (`uintPool`, `intPool`) read at their types. -/
def poolDom (lits : List Int) : TDom
  | .bool => [true, false]
  | .uint => (uintPool lits).filterMap (PrimTy.ofInt? .uint)
  | .int => (intPool lits).filterMap (PrimTy.ofInt? .int)

/-- The pool arguments are drawn from, each with its type. -/
def poolVals (lits : List Int) (p : PrimTy) : List Semantics.CallValue :=
  (poolDom lits p).map .ofTyped

/-! ## Random states

A candidate's storage is drawn typed by `TGen.sval` (`Tools/Common.lean`):
canonical (`Typing/Reachability.lean`: every struct member in order, a
mapping's keys unique over the type's default, no shadow), its words from
the pools. -/

/-- Every combination, the first list's element first. -/
def products {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: rest => xs.flatMap fun x => (products rest).map (x :: ·)

/-- Enumerate only when the complete Cartesian product fits `limit`. Check
cardinality before allocating combinations; an empty factor produces no
combinations even when the preceding factors would exceed the limit. -/
def productsWithin {α : Type} (limit : Nat) (domains : List (List α)) : List (List α) := Id.run do
  if limit == 0 || domains.any List.isEmpty then return []
  let mut count := 1
  for xs in domains do
    if xs.length > limit / count then return []
    count := count * xs.length
  return products domains

/-- A candidate: the storage, the arguments, the transaction, the ledger
and the funds a call starts from, the arguments each with its type, which
the formula's binders read at theirs (`Fml.peel`). -/
structure Cand (C : Contract) where
  st : Solidity.Storage C
  args : List (String × Semantics.CallValue)
  tx : TTx := { msgSender := PrimTy.ofIntD .uint 1 }
  net : Ledger := []
  bal : PrimTy.uint.Denote := PrimTy.dflt .uint

/-- **The typed state a candidate starts in**, with no locals: its
arguments are the formula's binders. -/
def Cand.tstate (C : Contract) (c : Cand C) : Solidity.State C [] :=
  { storage := c.st, H := [], heap := Heap.empty, env := (), net := c.net,
    selfBalance := c.bal, tx := c.tx }

/-- A random candidate: arguments of the types `ps`, a sender, a storage of
`C`'s layout whose mapping keys include the arguments and the sender. -/
def genCandidate (C : Contract) (lits : List Int) (ps : List (String × PrimTy))
    (payable : Bool) : Gen (Cand C) := do
  let dom := poolVals lits
  let args ← ps.mapM fun (n, p) => do pure (n, ← pickD (.ofTyped (PrimTy.dflt p)) (dom p))
  let sender ← pickD 1 ([1, 2] ++ uintPool lits)
  let argInts := args.filterMap fun (_, v) => v.num?
  let keys : (p : PrimTy) → List p.Denote := fun
    | .bool => ([false, true] : List Bool)
    | .uint => (uintPool lits ++ (sender :: argInts).filter (0 ≤ ·)).eraseDups.filterMap
        (PrimTy.ofInt? .uint)
    | .int => (intPool lits ++ sender :: argInts).eraseDups.filterMap (PrimTy.ofInt? .int)
  let g : TGen :=
    { shadow := 2
      prim := fun p => pickD (PrimTy.dflt p) (poolDom lits p)
      key := fun K => match keys K with
        | [] => none
        | k :: _ => some (pickD k (keys K)) }
  let st ← g.storage C
  let value ← if payable then pickD 0 (uintPool lits) else pure 0
  let time ← pickD 0 (uintPool lits)
  let paid ← pickD 0 (uintPool lits)
  let net : Ledger ← pickD [] [[], [(PrimTy.ofIntD .uint sender, paid)]]
  let bal ← pickD 0 [0, 1, uintBound - 1]
  let u := PrimTy.ofIntD .uint
  pure { st, args, tx := { msgSender := u sender, msgValue := u value, timestamp := u time }, net,
         bal := u bal }

/-! ## Shrinking

A witness found at random is shrunk before it is shown: the ledger emptied,
the funds and the timestamp zeroed, the sender `1`, a state variable reset to its default,
a mapping entry dropped, and a large number renamed to a small one unused
elsewhere, everywhere it occurs (arguments, sender, keys, words), so that
the equalities the witness relies on survive.  A step is kept when the
candidate is still a counterexample.  The storage is shrunk typed: each step
is a fold (`Fold`) or a walk of the roots. -/

/-- The integers a storage value holds, keys included. -/
def intsFold : Fold where
  V _ := List Int
  F _ := List Int
  L _ := List Int
  W _ _ := List Int
  M _ _ := List Int
  prim v := (PrimTy.num? v).toList
  struct _ r := r
  array _ _ _ w l := w ++ l
  fixed _ w := w
  map _ _ m d := m ++ d
  fnil := []
  fcons _ _ v r := v ++ r
  lnil := []
  lcons _ _ v r := v ++ r
  wnil := []
  wcons _ _ v r := v ++ r
  mnil := []
  mcons k _ _ v r := PrimTy.key k :: v ++ r

/-- `v` renamed `s`, keys and words alike (a word only where `s` is in its
type's range). -/
def renameFold (v s : Int) : Fold where
  V := Solidity.SVal
  F := SFields
  L := SList
  W := SVec
  M := SMap
  prim {p} x := .prim (if PrimTy.num? x = some v then (PrimTy.ofInt? p s).getD x else x)
  struct _ r := .struct r
  array _ _ h w l := .array w l h
  fixed _ w := .fixed w
  map _ _ m d := .map m d
  fnil := .nil
  fcons _ _ x r := .cons x r
  lnil := .nil
  lcons _ _ x r := .cons x r
  wnil := .nil
  wcons _ _ x r := .cons x r
  mnil := .nil
  mcons {K _} k _ _ x r := .cons (if PrimTy.num? k = some v then (PrimTy.ofInt? K s).getD k else k) x r

/-- A mapping with each of its entries dropped in turn. -/
def SMap.drops {K : PrimTy} {V : Ty} : SMap K V → List (SMap K V)
  | .nil => []
  | .cons k x rest => rest :: (SMap.drops rest).map (.cons k x)

/-- A value with one mapping entry dropped, each in turn: none but at a
mapping. -/
def SVal.dropEntries : {T : Ty} → Solidity.SVal T → List (Solidity.SVal T)
  | _, .map es d => (SMap.drops es).map (.map · d)
  | _, _ => []

/-- The roots with one of them reset to its default, each in turn (none
already there). -/
def SFields.resets : {fs : List (Name × Ty)} → SFields fs → List (SFields fs)
  | _, .nil => []
  | _, .cons (T := T) x rest =>
    (if x = Solidity.SVal.dflt T then [] else [.cons (Solidity.SVal.dflt T) rest]) ++
      (SFields.resets rest).map (.cons x)

/-- The roots with one mapping entry dropped, each in turn. -/
def SFields.drops : {fs : List (Name × Ty)} → SFields fs → List (SFields fs)
  | _, .nil => []
  | _, .cons x rest =>
    (SVal.dropEntries x).map (.cons · rest) ++ (SFields.drops rest).map (.cons x)

/-- The integers a candidate mentions. -/
def Cand.ints (c : Cand C) : List Int :=
  (c.args.filterMap (fun (_, v) => v.num?) ++
    c.tx.msgSender.1 :: c.st.fold intsFold).eraseDups

/-- An argument's number renamed by `f`, where the result is in its type's
range. -/
def renameArg (f : Int → Int) : Semantics.CallValue → Semantics.CallValue
  | .bool b => .bool b
  | .uint n => .uint ((PrimTy.ofInt? .uint (f n.1)).getD n)
  | .int n => .int ((PrimTy.ofInt? .int (f n.1)).getD n)

/-- `v` renamed `s` everywhere in a candidate. -/
def Cand.rename (c : Cand C) (v s : Int) : Cand C :=
  let r (n : Int) : Int := if n = v then s else n
  { c with
    st := c.st.fold (renameFold v s)
    args := c.args.map fun (x, a) => (x, renameArg r a)
    tx := { c.tx with msgSender := (PrimTy.ofInt? .uint (r c.tx.msgSender.1)).getD c.tx.msgSender }
    net := c.net.map fun (a, b) => ((PrimTy.ofInt? .uint (r a.1)).getD a, b) }

/-- The candidates one shrinking step away, simplest first. -/
def Cand.shrinks (c : Cand C) : List (Cand C) :=
  let small : List Int := [0, 1, 2, 3]
  let ints := c.ints
  let renames := (ints.filter (fun v => !small.contains v)).flatMap fun v =>
    (small.filter (!ints.contains ·)).map (c.rename v)
  let resets := (SFields.resets c.st).map fun st => { c with st }
  let drops := (SFields.drops c.st).map fun st => { c with st }
  let u := PrimTy.ofIntD .uint
  (if c.net.isEmpty then [] else [{ c with net := [] }]) ++
  (if c.bal.1 = 0 then [] else [{ c with bal := u 0 }]) ++
  (if c.tx.timestamp.1 = 0 then [] else [{ c with tx := { c.tx with timestamp := u 0 } }]) ++
  (if c.tx.msgValue.1 = 0 then [] else [{ c with tx := { c.tx with msgValue := u 0 } }]) ++
  (if c.tx.msgSender.1 = 1 then [] else [{ c with tx := { c.tx with msgSender := u 1 } }]) ++
  resets ++ drops ++ renames

/-- **Shrink** `c` while `ok` holds of it, one step at a time, at most
`fuel` steps. -/
def Cand.shrink (ok : Cand C → Bool) : Nat → Cand C → Cand C
  | 0, c => c
  | fuel + 1, c =>
    match c.shrinks.find? ok with
    | some c' => Cand.shrink ok fuel c'
    | none => c


end Solidity.Tools

/-! ## Reading a scoped formula against a candidate -/

namespace Solidity

open Solidity.Tools (Tri)

variable {C : Contract}

/-- The leading parameters of a scoped formula, outermost first: its `∀`s
and the hidden binders of value type in front of it (a specification's
parameters, `Calculus/Spec.lean`). -/
def Fml.params : {Γ : Ctx} → Fml C Γ → List (Var × PrimTy)
  | _, .all x p φ => (x, p) :: Fml.params φ
  | _, .bind _ x (.val p) φ => (x, p) :: Fml.params φ
  | _, _ => []

/-- A state and a formula under it, at some context. -/
abbrev Peeled (C : Contract) := (Δ : Ctx) × State C Δ × Fml C Δ

/-- The leading parameters bound to `vals`, by name, as far as each is
given: the state and the formula under them.  Compiled; the twin of
`Fml.peel` (`Fml.peel_eq`). -/
def Fml.peelC (vals : List (Var × Semantics.CallValue)) : {Γ : Ctx} → State C Γ → Fml C Γ → Peeled C
  | _, σ, .all x p φ => match (vals.lookup x).bind (Semantics.CallValue.as? p) with
    | some w => Fml.peelC vals (σ.push (t := .val p) w) φ
    | none => ⟨_, σ, .all x p φ⟩
  | _, σ, .bind m x (.val p) φ => match (vals.lookup x).bind (Semantics.CallValue.as? p) with
    | some w => Fml.peelC vals (σ.push (t := .val p) w) φ
    | none => ⟨_, σ, .bind m x (.val p) φ⟩
  | _, σ, φ => ⟨_, σ, φ⟩

/-- The leading parameters bound to `vals`, by the recursor (Gate G0
conditions 1 and 2): what a certificate peels in the kernel.  Compiled as
`Fml.peelC`. -/
@[implemented_by Fml.peelC]
def Fml.peel (vals : List (Var × Semantics.CallValue)) {Γ : Ctx} (σ : State C Γ) (φ : Fml C Γ) :
    Peeled C :=
  Fml.rec (motive := fun Γ _ => State C Γ → Peeled C)
    (fun σ => ⟨_, σ, .tt⟩) (fun a b σ => ⟨_, σ, .eq a b⟩) (fun t σ => ⟨_, σ, .wellFormed t⟩)
    (fun φ _ σ => ⟨_, σ, .not φ⟩) (fun φ ψ _ _ σ => ⟨_, σ, .and φ ψ⟩)
    (fun φ ψ _ _ σ => ⟨_, σ, .imp φ ψ⟩) (fun m U φ _ σ => ⟨_, σ, .upd m U φ⟩)
    (fun m P κ φ _ σ => ⟨_, σ, .modal m P κ φ⟩) (fun φ _ σ => ⟨_, σ, .havoc φ⟩)
    (fun x p φ ih σ => match (vals.lookup x).bind (Semantics.CallValue.as? p) with
      | some w => ih (σ.push (t := .val p) w)
      | none => ⟨_, σ, .all x p φ⟩)
    (fun {Γ} m x t φ ih σ =>
      LTy.casesOn (motive := fun t => Fml C (t :: Γ) → (State C (t :: Γ) → Peeled C) → Peeled C) t
        (fun p φ ih => match (vals.lookup x).bind (Semantics.CallValue.as? p) with
          | some w => ih (σ.push (t := .val p) w)
          | none => ⟨_, σ, .bind m x (.val p) φ⟩)
        (fun r φ _ => ⟨_, σ, .bind m x (.alias r) φ⟩) (fun r φ _ => ⟨_, σ, .bind m x (.mem r) φ⟩)
        (fun φ _ => ⟨_, σ, .bind m x .old φ⟩) (fun φ _ => ⟨_, σ, .bind m x .oldNet φ⟩)
        (fun φ _ => ⟨_, σ, .bind m x .kint φ⟩) φ ih)
    (fun xs φ _ σ => ⟨_, σ, .anon xs φ⟩)
    (fun x A φ _ σ => ⟨_, σ, .allocAll x A φ⟩)
    (fun φ _ σ => ⟨_, σ, .grow φ⟩)
    φ σ

theorem Fml.peel_eq (vals : List (Var × Semantics.CallValue)) : {Γ : Ctx} → (φ : Fml C Γ) →
    ∀ σ : State C Γ, Fml.peel vals σ φ = Fml.peelC vals σ φ
  | _, .all _ _ φ, _ => by simp only [Fml.peelC, ← Fml.peel_eq vals φ]; rfl
  | _, .bind _ _ (.val _) φ, _ => by simp only [Fml.peelC, ← Fml.peel_eq vals φ]; rfl
  | _, .bind _ _ (.alias _) _, _ | _, .bind _ _ (.mem _) _, _ | _, .bind _ _ .old _, _
  | _, .bind _ _ .oldNet _, _ | _, .bind _ _ .kint _, _ | _, .tt, _ | _, .eq .., _
  | _, .wellFormed _, _ | _, .not _, _ | _, .and .., _ | _, .imp .., _ | _, .upd .., _
  | _, .modal .., _ | _, .havoc _, _ | _, .anon .., _ | _, .allocAll .., _ | _, .grow .., _ => rfl

/-- What fails under the peeled binders fails under the binders: each is a
`∀` (or a hidden binder, read as one) of the values it is peeled at. -/
theorem Fml.not_holds_of_peelC (vals : List (Var × Semantics.CallValue)) : {Γ : Ctx} → (σ : State C Γ) →
    (φ : Fml C Γ) → ¬ holds (Fml.peelC vals σ φ).2.1 (Fml.peelC vals σ φ).2.2 → ¬ holds σ φ
  | _, σ, .all x p φ, h => by
    cases hw : (vals.lookup x).bind (Semantics.CallValue.as? p) with
    | none => rw [Fml.peelC, hw] at h; exact h
    | some w =>
      rw [Fml.peelC, hw] at h
      exact fun hall => Fml.not_holds_of_peelC vals _ φ h (hall w)
  | _, σ, .bind m x (.val p) φ, h => by
    cases hw : (vals.lookup x).bind (Semantics.CallValue.as? p) with
    | none => rw [Fml.peelC, hw] at h; exact h
    | some w =>
      rw [Fml.peelC, hw] at h
      exact fun hall => Fml.not_holds_of_peelC vals _ φ h (hall w)
  | _, _, .bind _ _ (.alias _) _, h | _, _, .bind _ _ (.mem _) _, h | _, _, .bind _ _ .old _, h
  | _, _, .bind _ _ .oldNet _, h | _, _, .bind _ _ .kint _, h | _, _, .tt, h | _, _, .eq .., h
  | _, _, .wellFormed _, h
  | _, _, .not _, h | _, _, .and .., h | _, _, .imp .., h | _, _, .upd .., h
  | _, _, .modal .., h | _, _, .havoc _, h | _, _, .anon .., h | _, _, .allocAll .., h | _, _, .grow .., h => h

/-- `φ` read under its leading parameters bound to `vals` (`Fml.peel`). -/
def Fml.eval3Peel (dom : TDom) (vals : List (Var × Semantics.CallValue)) {Γ : Ctx} (σ : State C Γ)
    (φ : Fml C Γ) : Tri :=
  match Fml.peel vals σ φ with
  | ⟨_, σ', ψ⟩ => ψ.eval3 dom σ'

/-- **A certificate**: a typed state where `φ`, its leading parameters bound
to `vals`, evaluates to `ff` refutes `⊨ᶠ φ`. -/
theorem Fml.not_valid_of_eval3Peel {dom : TDom} (vals : List (Var × Semantics.CallValue)) (σ : State C [])
    {φ : Fml C []} (h : Fml.eval3Peel dom vals σ φ = .ff) : ¬ Fml.Valid φ := by
  intro hv
  have key := Fml.not_holds_of_peelC vals σ φ
  rw [← Fml.peel_eq] at key
  unfold Fml.eval3Peel at h
  generalize Fml.peel vals σ φ = q at h key
  obtain ⟨_, σ', ψ⟩ := q
  exact key (Fml.eval3_ff h) (hv σ)

/-- A proof of failure under the chosen parameters refutes the original
formula. This permits structural proofs of quantified declaration premises
alongside the finite evaluator's proof of a false consequent. -/
theorem Fml.not_valid_of_peel (vals : List (Var × Semantics.CallValue)) (σ : State C [])
    {φ : Fml C []}
    (h : ¬ holds (Fml.peel vals σ φ).2.1 (Fml.peel vals σ φ).2.2) : ¬ Fml.Valid φ := by
  intro hv
  have key := Fml.not_holds_of_peelC vals σ φ
  rw [← Fml.peel_eq] at key
  exact key h (hv σ)

/-- A true entry premise and an evaluated false body refute the implication. -/
theorem Fml.not_holds_imp_of_eval3 (dom : TDom) {Γ : Ctx} {σ : State C Γ} {pre body : Fml C Γ}
    (hp : holds σ pre) (hb : body.eval3 dom σ = .ff) : ¬ holds σ (.imp pre body) :=
  fun h => Fml.eval3_ff hb (h hp)

/-- Entry premises are proved conjunct by conjunct without dropping any. -/
theorem Fml.holds_and_intro {Γ : Ctx} {σ : State C Γ} {φ ψ : Fml C Γ}
    (hφ : holds σ φ) (hψ : holds σ ψ) : holds σ (.and φ ψ) := ⟨hφ, hψ⟩

/-- The first `n` conjuncts of `φ₁ ∧ (φ₂ ∧ …)`, the last one the rest
(`Fml.conj`'s shape). -/
def Fml.conjN {Γ : Ctx} : Nat → Fml C Γ → List (Fml C Γ)
  | 0, _ => []
  | 1, φ => [φ]
  | n + 2, .and φ ψ => φ :: Fml.conjN (n + 1) ψ
  | _ + 2, φ => [φ]

/-- What the run in front of a formula leaves, for the report: the storage
it ends with, or how it halts; under implications, a binder at its first
value, an update in the typed state it lifts to.  `none` where the run is
past its fuel or the update lifts to no typed state. -/
def Fml.outcome (dom : TDom) : {Γ : Ctx} → State C Γ →
    Fml C Γ → Option (Except THalt (Storage C))
  | _, σ, .imp _ ψ => Fml.outcome dom σ ψ
  | _, σ, .all _ p ψ => match dom p with
    | v :: _ => Fml.outcome dom (σ.push (t := .val p) v) ψ
    | [] => none
  | _, σ, .bind _ _ t ψ => match dom.bind σ t with
    | v :: _ => Fml.outcome dom (σ.push v) ψ
    | [] => none
  | _, σ, .upd _ U ψ => match U.applyV σ with
    | none => some (.error .revert)
    | some τ => match σ.lift? τ with
      | some σ' => match Fml.outcome dom σ' ψ with
        | some r => some r
        | none => some (.ok σ'.storage)
      | none => none
  | _, σ, .modal _ P κ _ => match Prog.runFramesF loopFuel σ P κ with
    | .ok τ => some (.ok τ.storage)
    | .error .diverge => none
    | .error e => some (.error e)
  | _, _, _ => none

/-- A specification's body `{U} [ P ] (φ₁ ∧ … ∧ φₙ)` read in `σ`: the halt
the run ends in, or the indices of the conjuncts that evaluate to `ff`
where it ends; `none` where the run is past its fuel or the update lifts to
no typed state. -/
def Fml.postFails (dom : TDom) (n : Nat) : {Γ : Ctx} → State C Γ →
    Fml C Γ → Option (Option THalt × List Nat)
  | _, σ, .upd _ U ψ => match U.applyV σ with
    | none => some (some .revert, [])
    | some τ => match σ.lift? τ with
      | some σ' => Fml.postFails dom n σ' ψ
      | none => none
  | _, σ, .modal _ P κ φ => match Prog.runFramesF loopFuel σ P κ with
    | .ok τ =>
      some (none, ((List.range n).zip (Fml.conjN n φ)).filterMap fun (i, ψ) =>
        if ψ.eval3 dom τ = .ff then some i else none)
    | .error .diverge => none
    | .error e => some (some e, [])
  | _, _, _ => none

end Solidity

namespace Solidity.Tools

open Semantics (lookupBy)

variable {C : Contract}

/-! ## The search -/

/-- **A counterexample**: the candidate the call starts from (`Cand C`: its
storage, transaction, ledger and funds; the arguments are the formula's
binders, not locals), the storage the typed run ends with or how it halts
(`none` for a formula with no run in front), and the indices of the
conjuncts after the call that evaluate to `ff`. -/
structure Witness (C : Contract) where
  cand : Cand C
  outcome : Option (Except THalt (Storage C))
  failing : List Nat

/-- What a search found, among how many candidates, of which how many met
the stated premises. -/
structure Search (C : Contract) where
  witness : Option (Witness C)
  tried : Nat
  admitted : Nat

/-- The integers a candidate's arguments are, first in its domain: a
binder tries them before the pools. -/
def Cand.argInts (c : Cand C) : List Int :=
  c.args.filterMap fun (_, v) => v.num?

section Search

variable [FreshNames]

/-- The arguments of a candidate by variable, as `Fml.peel` binds them. -/
def Cand.vals (c : Cand C) : List (Var × Semantics.CallValue) := c.args.map fun (n, v) => (Var.ofName n, v)

/-- The obligation of `f` in pieces, and what the search needs of `f`: its
declaration, the scoped obligation, how many premises are met by
construction and how many stated, the conjuncts after the call (today's,
as the specification writes them), its parameters of value type, the
literals of the clauses. -/
structure SpecProblem (C : Contract) where
  decl : FunDecl
  fml : Fml C []
  assumed : Nat
  checked : Nat
  posts : List (NRead C)
  params : List (String × PrimTy)
  payable : Bool
  lits : List Int

/-- The problem of `f`: `specPieces`, the scoped obligation, the
parameters, the literals. -/
def SpecProblem.of (C : Contract) (f : String) : Except String (SpecProblem C) := do
  let (assumed, checked, _, _, posts) ← specPieces C f
  let fml ← specObligation C f
  let some d := lookupBy f C.funs | throw s!"{f} is not a function of the contract"
  let params := d.params.filterMap fun (n, T) => match T with
    | .prim p => some (n, p)
    | _ => none
  let lits := (C.inv ++ d.spec.requires ++ d.spec.ensures).flatMap specNums ++
    (d.spec.assignable.getD []).flatMap locNums
  pure { decl := d, fml, assumed := assumed.length, checked := checked.length, posts, params,
         payable := d.payable, lits }

/-- The literals a candidate's domain is drawn from: its arguments, then
the specification's. -/
def SpecProblem.domLits (P : SpecProblem C) (c : Cand C) : List Int := c.argInts ++ P.lits

/-- A candidate tried: `none` unless the stated premises evaluate to `tt`;
then the conjuncts that evaluate to `ff`, if any.  A run that panics (an
`assert` failed) refutes the box whatever follows it, so it is a
counterexample with no conjunct blamed: the witness's outcome names it.
The update and the call run once (the typed run, with fuel), and each
conjunct is read in the state they leave. -/
def SpecProblem.try (P : SpecProblem C) (c : Cand C) : Option (Option (Witness C)) :=
  let dom := poolDom (P.domLits c)
  let ⟨_, σ, ψ⟩ := Fml.peel c.vals (c.tstate C) P.fml
  match ψ with
  | .imp pre body =>
    let pres := (Fml.conjN (P.assumed + P.checked) pre).drop P.assumed
    if !pres.all (fun φ => φ.eval3 dom σ = .tt) then none else
    match Fml.postFails dom P.posts.length σ body with
    | none => some none
    | some (some .panic, _) =>
      some (some { cand := c, failing := [], outcome := some (.error .panic) })
    | some (some _, _) => some none
    | some (none, []) => some none
    | some (none, failing) =>
      some (some { cand := c, failing, outcome := Fml.outcome dom σ body })
  | _ => none

/-- Whether a candidate is a counterexample. -/
def SpecProblem.refutes (P : SpecProblem C) (c : Cand C) : Bool :=
  match P.try c with
  | some (some _) => true
  | _ => false

/-- **The search for a counterexample to `f`'s specification**: the
all-default storage with every combination of pooled arguments first (when
there are at most half the budget of them), then random candidates up to
`budget`; what is found is shrunk. -/
def SpecProblem.search (P : SpecProblem C) (budget : Nat) : Search C := Id.run do
  let dom := poolVals P.lits
  let combos := productsWithin (budget / 2) (P.params.map fun (_, p) => dom p)
  let cands := combos.map fun vs =>
    ({ st := Storage.init C, args := P.params.map (·.1) |>.zip vs } : Cand C)
  let mut admitted := 0
  let mut tried := 0
  let mut g := mkStdGen 2026
  let mut found : Option (Cand C) := none
  for c in cands do
    tried := tried + 1
    match P.try c with
    | none => pure ()
    | some none => admitted := admitted + 1
    | some (some _) => found := some c; break
  if found.isNone then
    for _ in [0:budget - tried] do
      let (c, g') := (genCandidate C P.lits P.params P.payable).run g
      g := g'
      tried := tried + 1
      match P.try c with
      | none => pure ()
      | some none => admitted := admitted + 1
      | some (some _) => found := some c; break
  let some c := found | return { witness := none, tried, admitted }
  let c := c.shrink P.refutes 64
  return { witness := (P.try c).join, tried, admitted := admitted + 1 }

/-- **A counterexample to a closed scoped formula**: its parameters bound to
pooled `uint`s (every combination first), the storage all-default, then
random storages of `C`'s layout; what is found is shrunk.  A candidate is
one where the formula under its arguments evaluates to `ff`. -/
def searchFml (C : Contract) (φ : Fml C []) (budget : Nat := 2000) : Search C := Id.run do
  let ps := (Fml.params φ).filterMap fun (x, p) => match x with
    | .user n => some (n, p)
    | .fresh .. => none
  -- the candidate's arguments bound, so that the witness is what refutes
  let refutes (c : Cand C) : Bool :=
    Fml.eval3Peel (poolDom c.argInts) c.vals (c.tstate C) φ = .ff
  let combos := productsWithin (budget / 2) (ps.map fun (_, p) => poolVals [] p)
  let mut tried := 0
  let mut g := mkStdGen 2026
  let mut found : Option (Cand C) := none
  for vs in combos do
    tried := tried + 1
    let c : Cand C := { st := Storage.init C, args := ps.map (·.1) |>.zip vs }
    if refutes c then found := some c; break
  if found.isNone then
    for _ in [0:budget - tried] do
      let (c, g') := (genCandidate C [] ps true).run g
      g := g'
      tried := tried + 1
      if refutes c then found := some c; break
  let some c := found | return { witness := none, tried, admitted := tried }
  let c := c.shrink refutes 64
  let ⟨_, σ, ψ⟩ := Fml.peel c.vals (c.tstate C) φ
  return { witness := some { cand := c, failing := [],
                             outcome := Fml.outcome (poolDom c.argInts) σ ψ },
           tried, admitted := tried }

/-! ## Printing a witness -/

/-- A witness, one fact per line: the arguments and the transaction
(`fmtTx`), the storage before, and after the run (or how it halted), over
the typed state. -/
def Witness.lines (C : Contract) (w : Witness C) : List String :=
  let σ := w.cand.tstate C
  let args := w.cand.args.map fun (n, v) => s!"{n} = {CallValue.fmt v}"
  let after := match w.outcome with
    | none => []
    | some (.error h) => [s!"after: {fmtHalt h}"]
    | some (.ok st) => ["after: " ++ fmtStorageLine C st]
  [", ".intercalate (args ++ fmtTx σ), "before: " ++ fmtStorageLine C σ.storage true] ++
    after

/-! ## Certificates -/

section Meta

open Lean Meta

/-- A typed primitive as a closed term: a `uint` or an `int` as
`PrimTy.ofIntD`, which the kernel reads back. -/
def quotePrim : (p : PrimTy) → p.Denote → Expr
  | .bool, b => toExpr (show Bool from b)
  | .uint, n => mkApp2 (mkConst ``PrimTy.ofIntD) (toExpr PrimTy.uint) (toExpr n.1)
  | .int, n => mkApp2 (mkConst ``PrimTy.ofIntD) (toExpr PrimTy.int) (toExpr n.1)

instance : ToExpr PrimTy.uint.Denote where
  toExpr := quotePrim .uint
  toTypeExpr := mkApp (mkConst ``PrimTy.Denote) (toExpr PrimTy.uint)

instance : ToExpr Semantics.CallValue where
  toExpr
    | .bool b => mkApp (mkConst ``Semantics.CallValue.bool) (toExpr b)
    | .uint n => mkApp (mkConst ``Semantics.CallValue.uint) (quotePrim .uint n)
    | .int n => mkApp (mkConst ``Semantics.CallValue.int) (quotePrim .int n)
  toTypeExpr := mkConst ``Semantics.CallValue

deriving instance ToExpr for Semantics.ExtKey

deriving instance ToExpr for Semantics.ExtResult

/-- A typed storage value as a closed term, constructor by constructor, an
array's bound as `SVal.arrayOf`'s check. -/
def quoteFold : Fold where
  V _ := Expr
  F _ := Expr
  L _ := Expr
  W _ _ := Expr
  M _ _ := Expr
  prim {p} v := mkApp2 (mkConst ``Solidity.SVal.prim) (toExpr p) (quotePrim p v)
  struct {s} _ r := mkApp2 (mkConst ``Solidity.SVal.struct) (toExpr s) r
  array {E n} _ _ _ w l := mkApp4 (mkConst ``Solidity.SVal.arrayOf) (toExpr E) (toExpr n) w l
  fixed {E n} _ w := mkApp3 (mkConst ``Solidity.SVal.fixed) (toExpr E) (toExpr n) w
  map {K U} _ _ m d := mkApp4 (mkConst ``Solidity.SVal.map) (toExpr K) (toExpr U) m d
  fnil := mkConst ``SFields.nil
  fcons {f T fs} _ _ v r :=
    mkAppN (mkConst ``SFields.cons) #[toExpr f, toExpr T, toExpr fs, v, r]
  lnil {E} := mkApp (mkConst ``SList.nil) (toExpr E)
  lcons {E} _ _ v r := mkApp3 (mkConst ``SList.cons) (toExpr E) v r
  wnil {E} := mkApp (mkConst ``SVec.nil) (toExpr E)
  wcons {E n} _ _ v r := mkApp4 (mkConst ``SVec.cons) (toExpr E) (toExpr n) v r
  mnil {K U} := mkApp2 (mkConst ``SMap.nil) (toExpr K) (toExpr U)
  mcons {K U} k _ _ v r := mkApp5 (mkConst ``SMap.cons) (toExpr K) (toExpr U) (quotePrim K k) v r

/-- A candidate as a closed term of `Cand C`, `cE` naming `C`, its storage
the term `stE`. -/
def Cand.quoteWith (cE stE : Expr) (c : Cand C) : Expr :=
  let u (n : PrimTy.uint.Denote) : Expr := quotePrim .uint n
  let txE := mkAppN (mkConst ``TTx.mk)
    #[u c.tx.msgSender, u c.tx.selfAddress, u c.tx.msgValue, u c.tx.timestamp, toExpr c.tx.ext]
  mkAppN (mkConst ``Cand.mk) #[cE, stE, toExpr c.args, txE, toExpr c.net, u c.bal]

/-- A candidate as a closed term of `Cand C`, `cE` naming `C`. -/
def Cand.quote (cE : Expr) (c : Cand C) : Expr := c.quoteWith cE (c.st.fold quoteFold)

/-- **The certificate**: the kernel checks `¬ ⊨ᶠ φ` of the scoped `φ` as
`Fml.not_valid_of_eval3Peel` at the typed state of the candidate `c`
(`Cand.tstate`, quoted by `Cand.quote`), its leading parameters bound to
the witness's arguments `vals` (`Fml.peel`, as the search read it),
deciding `Fml.eval3Peel (poolDom lits) vals _ φ = .ff` by evaluation: the
typed run and the formula under the parameters.  The kernel runs under
`heartbeats` (thousands), half the default, and the declaration is
checked, never added. -/
def certifyRefl (cE φE : Expr) (lits : List Int) (vals : List (Var × Semantics.CallValue))
    (c : Cand C) (heartbeats : Nat := 100000) : MetaM Bool := do
  let domE := mkApp (mkConst ``poolDom) (toExpr lits)
  let σE := mkApp2 (mkConst ``Cand.tstate) cE (c.quote cE)
  let valsE := toExpr vals
  let ev ← mkAppM ``Fml.eval3Peel #[domE, valsE, σE, φE]
  let eq ← mkEq ev (mkConst ``Tri.ff)
  let h ← mkDecideProof eq
  let type := mkNot (← mkAppM ``Fml.Valid #[φE])
  let value ← mkAppM ``Fml.not_valid_of_eval3Peel #[valsE, σE, h]
  let decl := Declaration.thmDecl {
    name := `_counterexample_certificate, levelParams := [], type, value }
  let opts := maxHeartbeats.set (← getOptions) heartbeats
  match Kernel.Environment.addDecl (← getEnv).toKernelEnv opts decl with
  | .ok _ => pure true
  | .error _ => pure false

/-- Prove each entry premise by the typed declaration laws or by its finite
evaluation. The shared budget bounds conjunction traversal; a universal
formula can only be accepted through an actual proof of that formula. -/
private partial def certifyPremise (domE : Expr) (g : MVarId) : StateRefT Nat MetaM Unit := do
  let n ← get
  if n == 0 then throwError "counterexample: entry-premise budget exhausted"
  set (n - 1)
  g.withContext do
    let ty ← g.getType
    let_expr holds _ _ σ φ := ty | throwError "counterexample: expected an entry premise"
    let saved ← saveState
    try
      let proof ← liftM <| DeclarationFacts.prove φ (conjunctions := false)
      g.assign (mkApp proof σ)
      return
    catch _ => saved.restore
    -- Split mixed premises before evaluation or further structural search:
    -- otherwise each successive tail would re-traverse the declaration prefix.
    let saved ← saveState
    let conjunction ← try
      pure (some (← g.apply (← mkConstWithFreshMVarLevels ``Fml.holds_and_intro)))
    catch _ => saved.restore; pure none
    if let some goals := conjunction then
      for next in goals do certifyPremise domE next
      return
    let saved ← saveState
    try
      let ev ← mkAppM ``Fml.eval3 #[domE, σ, φ]
      let eq ← mkEq ev (mkConst ``Tri.tt)
      unless ← isDefEq (← mkDecide eq) (mkConst ``Bool.true) do
        throwError "counterexample: finite evaluator did not establish the entry premise"
      let h ← mkDecideProof eq
      g.assign (← mkAppM ``Fml.eval3_tt #[h])
      return
    catch _ => saved.restore
    throwError "counterexample: entry premise is not certified"

/-- Certify the original scoped obligation with structural declaration
facts. This is a fallback when a mapping's universal layout makes the
finite evaluator return `unknown`; the kernel checks the complete proof. -/
def certifyDeclarations (cE φE : Expr) (lits : List Int)
    (vals : List (Var × Semantics.CallValue)) (c : Cand C)
    (heartbeats : Nat := 100000) : MetaM Bool := do
  let saved ← saveState
  let result ← tryCatchRuntimeEx (withCurrHeartbeats do
    let domE := mkApp (mkConst ``poolDom) (toExpr lits)
    let σE := mkApp2 (mkConst ``Cand.tstate) cE (c.quote cE)
    let type := mkNot (← mkAppM ``Solidity.Fml.Valid #[φE])
    let goal ← mkFreshExprMVar type
    let peel ← mkAppM ``Fml.not_valid_of_peel #[toExpr vals, σE]
    let [failure] ← goal.mvarId!.apply peel | return false
    let rule := mkApp2 (mkConst ``Fml.not_holds_imp_of_eval3) cE domE
    let [pre, body] ← failure.apply rule | return false
    (certifyPremise domE pre).run' 1024
    let h ← mkDecideProof (← body.getType)
    body.assign h
    let value ← instantiateMVars goal
    if value.hasSorry || value.hasMVar then return false
    let decl := Declaration.thmDecl {
      name := `_counterexample_declaration_certificate, levelParams := [], type, value }
    let opts := maxHeartbeats.set (← getOptions) heartbeats
    let result := match Kernel.Environment.addDecl (← getEnv).toKernelEnv opts decl with
      | .ok _ => true
      | .error _ => false
    return result) fun _ => do
      pure false
  saved.restore
  pure result

/-! ### Long arrays

A counterexample may need a dynamic array longer than any storage the
search can build: `2^255` elements, at which a counting loop bounded by
the length overflows (`Semantics/RunAccel.lean`).  Its storage is quoted
with that root `N` copies of its element type's default (`SVec.rep`,
`Tools/LazyStorage.lean`), which the kernel never unfolds: the run reads
the length, and the loop runs in closed form (`Prog.runA`).  The premise
`wt(storage)` is not evaluated, which would visit every element, but proved
(`holds_wt_of`): the long root by `SVal.allB_arrayOf_rep`, every other
root by evaluation.  No compiled evaluator can hold such a storage, so the
search proposes these candidates to the kernel directly, each under a
heartbeat budget of its own, after the ordinary candidates fail. -/

/-- A long-array candidate: the `k`-th root `root`, a dynamic array of
`E`s, `n` long. -/
structure LongCand where
  root : String
  k : Nat
  E : Ty
  n : Nat

/-- The lengths tried: where a `uint` counter stepped once per element
overflows when it steps by two (`2^255`), and the longest array
(`2^256 - 1`). -/
def longLengths : List Nat := [2 ^ 255, 2 ^ 256 - 1]

/-- The long-array candidates of `C`: each root that is a dynamic array
whose element default is well-formed (`Ty.defaultOkS`, which `wt` asks of a
non-empty array), at each of `longLengths`. -/
def longCands (C : Contract) : List LongCand :=
  (C.vars.zipIdx.filterMap fun ((r, T), k) => match T with
    | .ref (.array E) => if E.defaultOkS then some (r, k, E) else none
    | _ => none).flatMap fun (r, k, E) => longLengths.map fun n => { root := r, k, E, n }

/-- A length as it is printed. -/
def fmtLength (n : Nat) : String :=
  if n = 2 ^ 255 then "2^255" else if n = 2 ^ 256 - 1 then "2^256 - 1" else toString n

/-- `n` copies of `E`'s default as a quoted array (`SVal.arrayOf` over
`SVec.rep`, no slot past its end). -/
def lazyArray (E : Ty) (n : Nat) : Expr :=
  let vE := (SVal.dflt E).fold quoteFold
  mkAppN (mkConst ``SVal.arrayOf) #[toExpr E, toExpr n,
    mkAppN (mkConst ``SVec.rep) #[toExpr E, vE, toExpr n], mkApp (mkConst ``SList.nil) (toExpr E)]

/-- The quoted members `e` with the `k`-th replaced by `v`. -/
def replaceMember : Expr → Nat → Expr → Option Expr
  | e, k, v =>
    if e.isAppOfArity ``SFields.cons 5 then
      let args := e.getAppArgs
      match k with
      | 0 => some (mkAppN (mkConst ``SFields.cons) (args.set! 3 v))
      | k + 1 => (replaceMember args[4]! k v).map fun r =>
        mkAppN (mkConst ``SFields.cons) (args.set! 4 r)
    else none

/-- Whether a quoted value holds a long array. -/
def hasRep (e : Expr) : Bool := (e.find? (·.isConstOf ``SVec.rep)).isSome

/-- `lhs = true` by evaluation, left to the kernel. -/
def rflTrue (lhs : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) (← mkEq lhs (mkConst ``Bool.true))

/-- A proof of `SFields.allB B e = true` for quoted members `e`: the long
array by `SVal.allB_arrayOf_rep`, the rest by evaluation. -/
partial def proveMembersAllB (B e : Expr) : MetaM Expr := do
  let fs := (← whnfR (← inferType e)).appArg!
  if !hasRep e then return ← rflTrue (mkAppN (mkConst ``SFields.allB) #[B, fs, e])
  unless e.isAppOfArity ``SFields.cons 5 do throwError "counterexample: unexpected storage"
  let args := e.getAppArgs
  let (f, T, fs', v, r) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  let pv ← if hasRep v then do
      unless v.isAppOfArity ``SVal.arrayOf 4 do throwError "counterexample: unexpected array"
      let a := v.getAppArgs
      let lem := mkAppN (mkConst ``SVal.allB_arrayOf_rep) #[B, a[0]!, a[2]!.getAppArgs[1]!, a[1]!]
      let ty ← inferType lem
      let hn ← mkDecideProof ty.bindingDomain!
      let hv ← mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) ty.bindingBody!.bindingDomain!
      let ha ← mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true))
        ty.bindingBody!.bindingBody!.bindingDomain!
      pure (mkAppN lem #[hn, hv, ha])
    else rflTrue (mkAppN (mkConst ``SVal.allB) #[B, T, v])
  let pr ← proveMembersAllB B r
  pure (mkAppN (mkConst ``SFields.allB_cons_true) #[B, f, T, fs', v, r, pv, pr])

/-- The leading parameters of `φ` at their defaults: what a long-array
candidate binds them to. -/
def dfltVals (φ : Fml C []) : List (Var × Semantics.CallValue) :=
  (Fml.params φ).map fun (x, p) => (x, match p with
    | .bool => .bool false
    | .uint => .uint (PrimTy.dflt .uint)
    | .int => .int (PrimTy.dflt .int))

/-- The weak head normal form of `e` by the kernel, which reads no
`maxRecDepth` (the elaborator's unifier unfolding a peeled formula passes
it): bounded by the stack, and by no heartbeats, so only for a reduction
as short as one down a formula's leading binders; `none` where it fails. -/
def kernelWhnf? (e : Expr) : MetaM (Option Expr) := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok r => return some r
  | .error _ => return none

/-- **The certificate of a long-array candidate**: `¬ ⊨ᶠ φ` for `φ`, its
leading parameters bound to `vals`, of the shape `wt(storage) → ψ`, from the
candidate's typed state: the premise by `holds_wt_of`, `ψ` evaluated to
`ff` (`Fml.not_holds_imp_of_eval3`).  The peeled formula is read by the
kernel (`kernelWhnf?`) and the proof built with its arguments written, so
nothing is unified at the formula's depth: the default `maxRecDepth`
suffices.  `none` when the formula is not of that shape or the kernel does
not check it within `heartbeats`. -/
def certifyLong (cE φE : Expr) (vals : List (Var × Semantics.CallValue)) (lc : LongCand)
    (heartbeats : Nat := 100000) : MetaM (Option Expr) := do
  let C ← unsafe evalExpr Contract (mkConst ``Contract) cE
  let saved ← saveState
  let result ← tryCatchRuntimeEx (withCurrHeartbeats do
    let some stE := replaceMember ((Storage.init C).fold quoteFold) lc.k (lazyArray lc.E lc.n)
      | return none
    let c0 : Cand C := { st := Storage.init C, args := [] }
    let σE := mkApp2 (mkConst ``Cand.tstate) cE (c0.quoteWith cE stE)
    let domE := mkApp (mkConst ``poolDom) (toExpr ([] : List Int))
    let type := mkNot (← mkAppM ``Fml.Valid #[φE])
    let ΓE := (← whnfR (← inferType φE)).appArg!
    let valsE := toExpr vals
    -- the peeled state and formula, `⟨Δ, σ', pre → body⟩`, by the kernel
    let some pk ← kernelWhnf? (mkAppN (mkConst ``Fml.peel) #[cE, valsE, ΓE, σE, φE]) | return none
    unless pk.isAppOfArity ``Sigma.mk 4 do return none
    let Δ := pk.getArg! 2
    let some pr ← kernelWhnf? (pk.getArg! 3) | return none
    unless pr.isAppOfArity ``Prod.mk 4 do return none
    let σ' := pr.getArg! 2
    let some ψ ← kernelWhnf? (pr.getArg! 3) | return none
    unless ψ.isAppOfArity ``Fml.imp 4 do return none
    let (pre, body) := (ψ.getArg! 2, ψ.getArg! 3)
    unless ← isDefEq pre (mkAppN (mkConst ``Fml.wt) #[cE, Δ]) do return none
    let h1 ← proveMembersAllB (mkConst ``canonHB) stE
    let h2 ← proveMembersAllB (mkConst ``tightHB) stE
    let hp := mkAppN (mkConst ``holds_wt_of) #[cE, Δ, σ', h1, h2]
    let ev := mkAppN (mkConst ``Fml.eval3) #[cE, domE, Δ, σ', body]
    let hb ← mkDecideProof (← mkEq ev (mkConst ``Tri.ff))
    let h := mkAppN (mkConst ``Fml.not_holds_imp_of_eval3) #[cE, domE, Δ, σ', pre, body, hp, hb]
    let value := mkAppN (mkConst ``Fml.not_valid_of_peel) #[cE, valsE, σE, φE, h]
    if value.hasSorry || value.hasMVar then return none
    let decl := Declaration.thmDecl {
      name := `_counterexample_long_certificate, levelParams := [], type, value }
    let opts := maxHeartbeats.set (← getOptions) heartbeats
    match Kernel.Environment.addDecl (← getEnv).toKernelEnv opts decl with
    | .ok _ => return some value
    | .error _ => return none) fun _ => pure none
  saved.restore
  pure result

/-- The first long-array candidate the kernel certifies, with its proof of
`¬ ⊨ᶠ φ`. -/
def refuteLong (C : Contract) (cE φE : Expr) (φ : Fml C []) :
    MetaM (Option (LongCand × Expr)) := do
  for lc in longCands C do
    if let some pf ← certifyLong cE φE (dfltVals φ) lc then return some (lc, pf)
  return none

/-- A long-array witness, one fact per line. -/
def LongCand.lines (C : Contract) (vals : List (Var × Semantics.CallValue)) (lc : LongCand) :
    List String :=
  let args := vals.map fun (x, v) => match x with
    | .user n => s!"{n} = {CallValue.fmt v}"
    | .fresh b k => s!"{b}{k} = {CallValue.fmt v}"
  let σ := ({ st := Storage.init C, args := [] } : Cand C).tstate C
  [", ".intercalate (args ++ fmtTx σ),
   s!"before: {lc.root}.length = {fmtLength lc.n}, each element its default; " ++
     "every other root its default"]

/-- A refutation: the witness, printed (`Witness.lines`), whether the
kernel certified it, and the conjuncts it fails. -/
structure Refutation where
  witness : List String
  certified : Bool
  fails : List MessageData

/-- The `i`-th conjunct owed after the call of `d`, `φ`: an invariant or an
`ensures` as written, a conjunct of the frame of `assignable` as the
formula it is, read where the snapshots `old` and `oldNet` are in scope
and closed over them by hidden binders (quoted against the contract `cE`). -/
def postLabel (C : Contract) (d : FunDecl) (cE : Expr) (i : Nat) (φ : NRead C) : MessageData :=
  if h : i < C.inv.length then m!"invariant {SpecExpr.fmt C.inv[i]}"
  else if h' : i - C.inv.length < d.spec.ensures.length then
    m!"ensures {SpecExpr.fmt d.spec.ensures[i - C.inv.length]}"
  else
    let locs := (d.spec.assignable.getD []).map SpecLoc.fmt
    let Γ : NCtx := [(oldNetVar, .oldNet), (oldVar, .old)]
    let shown : MessageData := match φ Γ with
      | .ok ψ => m!"{Fml.quote cE (Fml.closeN false Γ ψ)}"
      | .error e => m!"{e}"
    m!"assignable {if locs.isEmpty then "\\nothing" else ", ".intercalate locs}: {shown}"

/-- **Refute `f`'s specification**: search, then certify what was found
against the scoped obligation.  `n` names the contract `C`. -/
def refuteSpec (n : Lean.Name) (C : Contract) (f : String) (budget : Nat := 2000) :
    MetaM (Except String (Search C × Option Refutation)) := do
  match SpecProblem.of C f with
  | .error e => pure (.error e)
  | .ok P =>
    let s := P.search budget
    let some w := s.witness | pure (.ok (s, none))
    let cE := mkConst n
    let c := w.cand
    let lits := P.domLits c
    -- the kernel is asked only what the evaluator already answered
    let direct ← if Fml.eval3Peel (poolDom lits) c.vals (c.tstate C)
        P.fml = .ff then certifyRefl cE (Fml.quote cE P.fml) lits c.vals c
      else pure false
    let certified ← if direct then pure true else
      certifyDeclarations cE (Fml.quote cE P.fml) lits c.vals c
    let fails := w.failing.map fun i => postLabel C P.decl cE i (P.posts.getD i NRead.tt)
    pure (.ok (s, some { witness := w.lines C, certified, fails }))

/-- The report of a refutation: the witness and the conjuncts it fails. -/
def Refutation.lines (r : Refutation) : List MessageData :=
  r.witness.map toMessageData ++ r.fails.map fun l => m!"fails: {l}"

/-- The head line of a refutation of `f`, as `#verify` and
`#counterexample` print it: `✗ f (certified):`. -/
def Refutation.head (f : String) (r : Refutation) : MessageData :=
  m!"✗ {f} ({if r.certified then "certified" else "tested"}):"

/-- The report of the search for a counterexample to `f`'s specification. -/
def searchReport (f : String) : Search C × Option Refutation → MessageData
  | (_, some r) => reportMsg (r.head f) r.lines
  | (s, none) =>
    m!"no counterexample to {f} found in {s.tried} candidates ({s.admitted} met the premises)"

end Meta

end Search

/-! ## `#counterexample` -/

/-- `#counterexample C.f`: a counterexample to the specification of the
function `f` of the contract `C`; `#counterexample C`: to each of its
functions with an obligation; `#counterexample φ`: to the closed scoped
formula `φ : Fml C []` (`dl!{ … }` under `open scoped
Solidity.Scoped`, or `cdl!{ … }`). -/
syntax (name := counterexampleCmd) "#counterexample " term : command

open Lean Elab Command Term Meta in
/-- `#counterexample`: a function's specification, a contract's, or a
formula. -/
@[command_elab counterexampleCmd]
def elabCounterexample : Lean.Elab.Command.CommandElab := fun stx => liftTermElabM do
  let t := stx[1]
  let target ← if t.isIdent then resolveTarget? "#counterexample" t.getId else pure none
  let one (c : Lean.Name) (C : Contract) (f : String) : TermElabM Unit := do
    match ← refuteSpec c C f with
    | .error e => throwError "#counterexample: {e}"
    | .ok r => logInfo (searchReport f r)
  match target with
  | some (.function c C f) => one c C f
  | some (.contract c C) =>
    let fs := C.funs.filter fun (_, d) => hasObligation C d
    if fs.isEmpty then logInfo m!"{c} has no function with a specification"
    for (f, _) in fs do one c C f
  | none =>
    let φE ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let φE ← instantiateMVars φE
    let ty ← whnf (← inferType φE)
    let closed ← if ty.isAppOfArity ``Fml 2 then (·.isAppOf ``List.nil) <$> whnfR ty.appArg!
      else pure false
    unless closed do
      throwError "#counterexample: not a closed scoped formula `Fml C []` (`cdl!\{ … }`, or \
        `dl!\{ … }` under `open scoped Solidity.Scoped`){indentExpr φE}"
    if φE.hasFVar || φE.hasMVar then
      throwError "#counterexample: the formula is not closed{indentExpr φE}"
    let cE := ty.appFn!.appArg!
    unless (← whnfR cE).isConst do throwError "#counterexample: not a named contract: {cE}"
    let C ← unsafe evalExpr Contract (Lean.mkConst ``Contract) cE
    -- an obligation declared without code (`solc_scoped_problems … decl`)
    -- is evaluated by its value, as `sol_prove` reads it
    let φ ← unsafe evalExpr (Fml C []) ty (← Solidity.Symex.evaluable φE)
    let s := searchFml C φ
    let some w := s.witness | do
      let some (lc, _) ← refuteLong C cE φE φ
        | logInfo m!"no counterexample found in {s.tried} candidates"
      logReport m!"counterexample (certified):" ((lc.lines C (dfltVals φ)).map toMessageData)
    let c := w.cand
    let certified ← if Fml.eval3Peel (poolDom c.argInts) c.vals
        (c.tstate C) φ = .ff then certifyRefl cE φE c.argInts c.vals c
      else pure false
    logReport m!"counterexample ({if certified then "certified" else "tested"}):"
      ((w.lines C).map toMessageData)

/-! ## `sol_refute`

A goal `¬ ⊢ φ` or `¬ ⊨ᶠ φ`, `φ` closed, by a counterexample: the search of
`#counterexample` (`searchFml`), its witness certified as there
(`Fml.not_valid_of_eval3Peel`, the kernel evaluating the formula at the
witness), and `¬ ⊢ φ` by the soundness of `⊢` read backwards
(`Proves.not_of_not_valid`).  The obligations of an import that are false
in the model are refuted so (`N.f.refuted`, `#solkey_obligations`). -/

/-- A sequent with no context that is not valid is not derivable. -/
theorem _root_.Solidity.Proves.not_of_not_valid {R : RuleSet} {φ : Fml C []}
    (h : ¬ Fml.Valid φ) : ¬ Proves C R [] .nil φ :=
  fun d => h d.fmlValid

/-- `sol_refute`: `¬ ⊢ φ` or `¬ ⊨ᶠ φ` by a certified counterexample.  Fails
when the search finds none. -/
syntax (name := solRefute) "sol_refute" : tactic

open Lean Elab Tactic Meta in
@[tactic solRefute]
def evalSolRefute : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some body := ty.consumeMData.not? | throwError "sol_refute: the goal is not a negation"
  let (cE, φE, wrap) ← match body.consumeMData.getAppFnArgs with
    | (``Proves, #[cE, R, Γ₀, _, H, φE]) =>
      unless (← whnfR Γ₀).isAppOf ``List.nil && (← whnfR H).isAppOf ``Hyps.nil do
        throwError "sol_refute: a sequent with hypotheses"
      pure (cE, φE, fun nv => mkAppN (mkConst ``Proves.not_of_not_valid) #[cE, R, φE, nv])
    | (``Fml.Valid, #[cE, φE]) => pure (cE, φE, id)
    | _ => throwError "sol_refute: not `¬ ⊢ φ` or `¬ ⊨ᶠ φ`"
  if φE.hasFVar || φE.hasMVar then throwError "sol_refute: the formula is not closed"
  unless (← whnfR cE).isConst do throwError "sol_refute: not a named contract: {cE}"
  let C ← unsafe evalExpr Contract (mkConst ``Contract) cE
  let φ ← unsafe evalExpr (Fml C []) (← inferType φE) (← Solidity.Symex.evaluable φE)
  let s := searchFml C φ
  let some w := s.witness | do
    -- no candidate the search can build: a long array, certified by the kernel alone
    let some (_, pf) ← refuteLong C cE φE φ
      | throwError "sol_refute: no counterexample found in {s.tried} candidates"
    g.assign (wrap pf)
    replaceMainGoal []
  let c := w.cand
  -- the kernel is asked only what the evaluator already answered
  unless Fml.eval3Peel (poolDom c.argInts) c.vals (c.tstate C) φ = .ff do
    throwError "sol_refute: the counterexample found is not certified"
  let domE := mkApp (mkConst ``poolDom) (toExpr c.argInts)
  let σE := mkApp2 (mkConst ``Cand.tstate) cE (c.quote cE)
  let valsE := toExpr c.vals
  let ev ← mkAppM ``Fml.eval3Peel #[domE, valsE, σE, φE]
  let h ← mkDecideProof (← mkEq ev (mkConst ``Tri.ff))
  g.assign (wrap (mkAppN (mkConst ``Fml.not_valid_of_eval3Peel) #[cE, domE, valsE, σE, φE, h]))
  replaceMainGoal []

end Solidity.Tools
