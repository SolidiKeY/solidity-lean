import Solidity.Roadmap.Contracts

/-! H64: one behaviour type and one constructive refinement relation.
A behaviour fixes a typed program, retaining all environments, resources,
consistent prefixes, Event/Outcome observations, Forward and Guard predicates.
This changes no syntax, state, frozen lane interface or observation. -/
namespace Solidity.Roadmap.G49Final

/-- A complete observation family for one typed program. -/
structure Behaviour where
  Env : Type
  Res : Type
  resLE : LE Res
  Allowed : Env → Prop
  Admissible : Res → Prop
  Forward : Env → Res → Prop
  Guard : Env → Res → Prop
  observe : Env → Res → Prefix Event Outcome
  consistent : ∀ e, @Prefixes.Consistent Res Event Outcome resLE (observe e)

/-- One source-end run condition; intermediate instances are derived. -/
def Behaviour.Ready (b : Behaviour) (e : b.Env) (r : b.Res) : Prop :=
  b.Admissible r ∧ b.Forward e r ∧ b.Guard e r

/-- The single proof-relevant refinement relation preserves explicit bounds,
environment soundness/surjectivity and full guards. No backward Forward
condition or bound-monotonicity requirement is added to the frozen Cert. -/
structure PassCorrect (source target : Behaviour) where
  envAbs : target.Env → source.Env
  envSound : ∀ e, target.Allowed e → source.Allowed (envAbs e)
  envOnto : ∀ e, source.Allowed e → ∃ e', target.Allowed e' ∧ envAbs e' = e
  need : target.Env → source.Res → target.Res
  need_ok : ∀ e r, target.Allowed e → source.Ready (envAbs e) r →
    target.Ready e (need e r) ∧ (source.observe (envAbs e) r).Le (target.observe e (need e r))
  back : ∀ e r, target.Allowed e → target.Admissible r → target.Guard e r →
    ∃ r', source.Admissible r' ∧ source.Guard (envAbs e) r' ∧
      (target.observe e r).Le (source.observe (envAbs e) r')

/-- Identity preserves all observations and the same bound. -/
def PassCorrect.refl (b : Behaviour) : PassCorrect b b where
  envAbs := id
  envSound := fun _ h => h
  envOnto := fun e h => ⟨e, h, rfl⟩
  need := fun _ r => r
  need_ok := fun _ _ _ h => ⟨h, Prefix.Le.refl _⟩
  back := fun _ r _ ha hg => ⟨r, ha, hg, Prefix.Le.refl _⟩

/-- Constructive transitivity carries intermediate conditions instead of
requesting another source no-failure/well-formedness premise. -/
def PassCorrect.trans {a b c : Behaviour} (ab : PassCorrect a b)
    (bc : PassCorrect b c) : PassCorrect a c where
  envAbs e := ab.envAbs (bc.envAbs e)
  envSound e h := ab.envSound _ (bc.envSound e h)
  envOnto e h := by
    obtain ⟨eb, hb, hab⟩ := ab.envOnto e h
    obtain ⟨ec, hc, hbc⟩ := bc.envOnto eb hb
    exact ⟨ec, hc, (congrArg ab.envAbs hbc).trans hab⟩
  need e r := bc.need e (ab.need (bc.envAbs e) r)
  need_ok e r h ready := by
    have first := ab.need_ok (bc.envAbs e) r (bc.envSound e h) ready
    have second := bc.need_ok e _ h first.1
    exact ⟨second.1, first.2.trans second.2⟩
  back e r h ha hg := by
    obtain ⟨rb, hb, gb, cb⟩ := bc.back e r h ha hg
    obtain ⟨ra, ha, ga, ba⟩ := ab.back (bc.envAbs e) rb (bc.envSound e h) hb gb
    exact ⟨ra, ha, ga, cb.trans ba⟩

/-- Intrinsically matching endpoints prevent silent changes of observations,
environments or resource predicates between adjacent list entries. -/
inductive PassList : Behaviour → Behaviour → Type 1 where
  | nil (b : Behaviour) : PassList b b
  | cons {a b c : Behaviour} (head : PassCorrect a b) (tail : PassList b c) : PassList a c

/-- Fold only the one refinement relation, using the recursor per Gate G0. -/
def PassList.fold {a b : Behaviour} (passes : PassList a b) : PassCorrect a b :=
  PassList.casesOn (motive := fun a b _ => PassCorrect a b) passes
    (fun b => PassCorrect.refl b)
    (fun head tail => head.trans (PassList.fold tail))
termination_by structural passes

/-- Public end-to-end refinement is stated against the fold. One source Ready
proof suffices for forward execution; reverse prefixes independently retain
admissibility and their own hash guard, including failing executions.
This semantic fold alone does not prove other G01 PublicCorrectness fields. -/
theorem public_end_to_end {a b : Behaviour} (passes : PassList a b)
    (e : b.Env) (allowed : b.Allowed e) (r : a.Res)
    (source : a.Ready (passes.fold.envAbs e) r) :
    (b.Ready e (passes.fold.need e r) ∧
      (a.observe (passes.fold.envAbs e) r).Le (b.observe e (passes.fold.need e r))) ∧
    (∀ rt, b.Admissible rt → b.Guard e rt →
      ∃ rs, a.Admissible rs ∧ a.Guard (passes.fold.envAbs e) rs ∧
        (b.observe e rt).Le (a.observe (passes.fold.envAbs e) rs)) :=
  ⟨passes.fold.need_ok e r allowed source, fun rt ha hg => passes.fold.back e rt allowed ha hg⟩

end Solidity.Roadmap.G49Final
