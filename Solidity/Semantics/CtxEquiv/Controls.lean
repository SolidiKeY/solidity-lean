import Solidity.Semantics.CtxEquiv.Unify
import Solidity.Semantics.CtxEquiv.StorageObs
import Solidity.Roadmap.Controls

/-!
# Witnesses and negative controls for contextual equivalence (S1.1, S1.2)

On G07's toy source and EVM (`Solidity/Roadmap/Controls.lean`), against
the G50 adversary type:

- **Inhabited.**  `succeed d` and `quiet d` differ only in what they hash,
  which is not an observation: they are contextually equivalent
  (`succeed_quiet_ctxEquiv`), so the relation is not syntactic equality.
  A loop contextually refines a revert (`loop_ctxRefines_fail`): a side
  with fewer completions refines.  The toy compiler's public theorem gives
  both contextual refinements (`toy_ctxRefines_back`, `toy_ctxRefines_forward`),
  the identity pass certificate gives backward refinement
  (`idCert_ctxRefines_back`), D6 holds of the hashing-only change
  (`dropHash_preserves`, `idCert_preserves`), a computable T07 check
  validates the toy compiler's output (`toyValidator_ctxRefines`),
  sequencing composes
  (`seq_shows_continuation`), and two storage mappings with implicit and
  explicit defaults are contextually equivalent against path adversaries
  (`mapping_defaults_ctxEquiv`).
- **Negative.**  Different revert data is observed
  (`fail_not_ctxEquiv`, `not_mangle_preserves`); no validator accepts
  altered bytes (`validator_rejects_altered`); refinement is not symmetric
  (`fail_not_ctxRefines_loop`); an artifact appending a byte to the return
  data fails backward refinement (`altered_not_ctxRefines_back`), one erasing
  revert data fails forward refinement (`erased_not_ctxRefines_forward`);
  sequencing observes the continuation (`seq_continuation_observed`);
  different stored booleans are not equivalent (`bool_not_ctxEquiv`).
- **Documented consequence.**  A data-free revert and a loop are equivalent
  where every bound may fail (`failEmpty_ctxEquiv_loop`).

The toy language ignores its environment and emits no events, so these
controls test outcomes only; `Solidity/Semantics/CtxEquiv/AdversaryControls.lean` exercises requests,
callbacks and events.
-/

namespace Solidity.CtxEquiv.Controls

open Solidity.Roadmap
open Solidity.Roadmap.Controls
open Solidity.CtxEquiv

/-- A toy program deployed against G50 adversaries. -/
def toyC (t : Toy) : Contract := Deployed.mk' toyLang t id

theorem toyC_behav (t : Toy) (s : SessionEnv) (π : Prefix Event Outcome) :
    (toyC t).behav s π ↔ ∃ b : Bound, t.run b.exhausted = π :=
  ⟨fun ⟨b, _, h⟩ => ⟨b, h⟩, fun ⟨b, h⟩ => ⟨b, trivial, h⟩⟩

/-- Equal runs at every exhaustion choice give equal behaviours. -/
theorem toyC_eq {t u : Toy} (h : ∀ b, t.run b = u.run b) (s : SessionEnv) :
    (toyC t).behav s = (toyC u).behav s := by
  funext π
  apply propext
  rw [toyC_behav, toyC_behav]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, (h _).symm.trans hb⟩, fun ⟨b, hb⟩ => ⟨b, (h _).trans hb⟩⟩

/-- Prefixes with different final observations differ. -/
theorem prefix_ne_of_final {a b : Prefix Event Outcome} (h : a.final ≠ b.final) : a ≠ b :=
  fun e => h (by rw [e])

/-! ## S1.1 -/

theorem succeed_quiet_run (d : Bytes) (b : Bool) : (Toy.succeed d).run b = (Toy.quiet d).run b := by
  cases b <;> rfl

/-- **Inhabited, not syntactic**: hashing is unobservable. -/
theorem succeed_quiet_ctxEquiv (d : Bytes) : CtxEquiv (toyC (.succeed d)) (toyC (.quiet d)) := by
  refine ⟨fun s _ => ?_, fun s _ => ?_⟩
  · rw [toyC_eq (succeed_quiet_run d) s]; exact Behav.Below.refl _
  · rw [toyC_eq (succeed_quiet_run d) s]; exact Behav.Below.refl _

/-- **Inhabited strict refinement**: a loop refines a revert. -/
theorem loop_ctxRefines_fail (d : Bytes) : CtxRefines (toyC .loop) (toyC (.fail d)) := by
  intro s _ π ⟨⟨hz, x⟩, _, hb⟩
  refine ⟨(Toy.fail d).run x, ⟨⟨hz, x⟩, trivial, rfl⟩, ?_⟩
  change Toy.loop.run x = π at hb
  subst hb
  cases x
  · exact ⟨List.prefix_refl _, .inl rfl⟩
  · exact Prefix.Le.refl _

theorem fail_done (d : Bytes) (s : SessionEnv) : ((toyC (.fail d)).behav s).Done [] (.revert d) :=
  ⟨⟨0, false⟩, trivial, rfl⟩

theorem not_done_revert {t : Toy} {d : Bytes} (s : SessionEnv)
    (h : ∀ b, (t.run b).final ≠ some (.revert d)) : ¬ ((toyC t).behav s).Done [] (.revert d) := by
  rintro ⟨b, _, hb⟩
  have hb' : t.run b.exhausted = ⟨[], some (.revert d)⟩ := hb
  exact h b.exhausted (by rw [hb'])

/-- **Negative control**: revert data is observed. -/
theorem fail_not_ctxEquiv : ¬ CtxEquiv (toyC (.fail [1])) (toyC (.fail [2])) :=
  not_ctxEquivOn_of_done quietEnv_allowed (fail_done [1] quietEnv)
    (not_done_revert quietEnv fun b => by cases b <;> decide)

/-- **Negative control**: refinement is not symmetric. -/
theorem fail_not_ctxRefines_loop : ¬ CtxRefines (toyC (.fail [1])) (toyC .loop) :=
  not_ctxRefinesOn_of_done quietEnv_allowed (fail_done [1] quietEnv)
    (not_done_revert quietEnv fun b => by cases b <;> decide)

/-- Refinement does not imply equivalence. -/
theorem ctxRefines_not_ctxEquiv : CtxRefines (toyC .loop) (toyC (.fail [1])) ∧
    ¬ CtxEquiv (toyC .loop) (toyC (.fail [1])) :=
  ⟨loop_ctxRefines_fail [1], fun h => fail_not_ctxRefines_loop h.2⟩

/-- Callback-free environments are a special case, and inhabited. -/
theorem succeed_quiet_noCallback (d : Bytes) :
    CtxEquivOn (fun e => e.Allowed ∧ e.NoCallback) (toyC (.succeed d)) (toyC (.quiet d)) ∧
      quietEnv.withoutCallbacks.Allowed ∧ quietEnv.withoutCallbacks.NoCallback :=
  ⟨(succeed_quiet_ctxEquiv d).noCallback, withoutCallbacks_adm quietEnv_allowed⟩

/-! ### Sequencing -/

/-- A continuation reverting with `d` after anything. -/
def revertK (d : Bytes) : SessionEnv → List Event → Outcome → Behav Event Outcome :=
  fun s _ _ => (toyC (.fail d)).behav s

/-- **Inhabited**: a success followed by a revert shows the revert. -/
theorem seq_shows_continuation :
    (toyC (.quiet [5])).seqBehav (revertK [2]) quietEnv ⟨[], some (.revert [2])⟩ :=
  .inr (.inr ⟨⟨[], some (.success [5])⟩, .success [5], ⟨[], some (.revert [2])⟩,
    ⟨⟨0, false⟩, trivial, rfl⟩, rfl, ⟨⟨0, false⟩, trivial, rfl⟩, rfl⟩)

/-- Sequencing congruence applied: the hashing difference stays unobserved
after a continuation. -/
theorem seq_congr_witness (d e : Bytes) :
    ∀ s, s.Allowed → ((toyC (.succeed d)).seqBehav (revertK e) s).Below
      ((toyC (.quiet d)).seqBehav (revertK e) s) :=
  CtxRefinesOn.seq (succeed_quiet_ctxEquiv d).1 fun _ _ _ _ => Behav.Below.refl _

/-- **Negative control**: sequencing observes the continuation's revert
data. -/
theorem seq_continuation_observed :
    ¬ ((toyC (.quiet [5])).seqBehav (revertK [2]) quietEnv).Below
      ((toyC (.quiet [5])).seqBehav (revertK [3]) quietEnv) := by
  intro h
  have hd := h.completes seq_shows_continuation rfl
  rcases hd with ⟨_, hn⟩ | ⟨a, o, _, _, he⟩ | ⟨a, o, k, ha, _, hk, he⟩
  · cases hn
  · exact prefix_ne_of_final (fun h => by cases h) he
  · obtain ⟨⟨_, x⟩, _, hb⟩ := ha
    obtain ⟨⟨_, y⟩, _, hc⟩ := hk
    change Toy.run _ x = a at hb
    change Toy.run _ y = k at hc
    subst hb hc
    cases x <;> cases y <;> exact prefix_ne_of_final (by decide) he

/-! ## S1.2 -/

/-- The toy compiler's artifact for `1 7` (revert with `[7]`). -/
theorem toy_admitted : toySource.Admitted ({ text := [1, 7] } : ToyInput) ⟨.fail [7], .legacy, .v2⟩ :=
  (admitted_iff _ _).2 rfl

/-- **Inhabited (G49/G50 → backward contextual refinement).** -/
theorem toy_ctxRefines_back :
    CtxRefines (toyEvm.contractGuarded (artOf (Toy.fail [7]).text))
      (toySource.contract (toySource.meaning ⟨.fail [7], .legacy, .v2⟩ trivial trivial
        (artOf (Toy.fail [7]).text))) :=
  toy_publicCorrectness.ctxRefines_back toy_admitted trivial trivial rfl

/-- **Inhabited (G49/G50 → forward contextual refinement).** -/
theorem toy_ctxRefines_forward :
    CtxRefines (toySource.contractForward (toySource.meaning ⟨.fail [7], .legacy, .v2⟩ trivial
        trivial (artOf (Toy.fail [7]).text)))
      (toyEvm.contract (artOf (Toy.fail [7]).text)) :=
  toy_publicCorrectness.ctxRefines_forward toy_admitted trivial trivial rfl

/-- Specification transfer re-derived through contextual refinement, on the
toy instance. -/
theorem toy_transfer' : SpecTransfer toySource toyEvm toyCompiler id :=
  toy_publicCorrectness.transfer'

/-- **Negative control**: bytes returning one more byte than the source fail
backward contextual refinement. -/
theorem altered_not_ctxRefines_back :
    ¬ CtxRefines (toyEvm.contractGuarded (artOf (Toy.succeed [0]).text))
      (toySource.contract (Toy.succeed [])) := by
  refine not_ctxRefinesOn_of_done (evs := []) (o := .success [0]) quietEnv_allowed
    ⟨⟨0, fun _ => 0⟩, ⟨trivial, toy_premise (.succeed [0])⟩, rfl⟩ ?_
  rintro ⟨⟨_, x⟩, _, hb⟩
  change Toy.run (.succeed []) x = _ at hb
  cases x <;> exact prefix_ne_of_final (by decide) hb

/-- **Negative control**: bytes erasing revert data fail forward contextual
refinement (adequacy). -/
theorem erased_not_ctxRefines_forward :
    ¬ CtxRefines (toySource.contractForward (Toy.fail [7]))
      (toyEvm.contract (artOf (Toy.fail []).text)) := by
  refine not_ctxRefinesOn_of_done (evs := []) (o := .revert [7]) quietEnv_allowed
    ⟨⟨0, false⟩, ⟨trivial, toy_forward _ _ _⟩, rfl⟩ ?_
  rintro ⟨b, _, hb⟩
  change (decode (mainRuntime (artOf (Toy.fail []).text))).run false = _ at hb
  exact prefix_ne_of_final (by decide) hb

/-- **Inhabited (pass certificate → contextual refinement).** -/
theorem idCert_ctxRefines_back (t : Toy) :
    CtxRefinesOn SessionEnv.Allowed (idPass.tgtGuarded t trivial id) (idPass.src t id) :=
  idCert.ctxRefines_back t trivial id fun _ h => h

/-- **Inhabited (D6 stub)**: every certified pass preserves. -/
theorem idCert_preserves (t : Toy) : Preserves idPass t trivial := idCert.preserves t trivial

/-- A pass dropping a success's hashing. -/
def dropHash : Pass toyLang toyLang where
  Dom := fun _ => True
  run := fun t _ => match t with
    | .succeed d => .quiet d
    | t => t
  envAbs := id

/-- **Inhabited (D6 stub)**: dropping an unobservable hash preserves, under
the premises, with no certificate. -/
theorem dropHash_preserves (d : Bytes) : Preserves dropHash (.succeed d) trivial := fun _ _ =>
  ⟨fun rs _ _ _ => ⟨rs, trivial, by
      show ((Toy.succeed d).run rs.exhausted).Le ((Toy.quiet d).run rs.exhausted)
      rw [succeed_quiet_run]; exact Prefix.Le.refl _⟩,
    fun rt _ _ => ⟨rt, trivial, by
      show ((Toy.quiet d).run rt.exhausted).Le ((Toy.succeed d).run rt.exhausted)
      rw [succeed_quiet_run]; exact Prefix.Le.refl _⟩⟩

/-- A pass appending a byte to revert data. -/
def mangle : Pass toyLang toyLang where
  Dom := fun _ => True
  run := fun t _ => match t with
    | .fail d => .fail (d ++ [0])
    | t => t
  envAbs := id

/-- **Negative control (D6 stub)**: changing revert data does not preserve. -/
theorem not_mangle_preserves : ¬ Preserves mangle (.fail [1]) trivial := by
  intro h
  obtain ⟨⟨hz, x⟩, _, hl⟩ := (h quietEnv quietEnv_allowed).2 ⟨0, false⟩ trivial (toy_premise _)
  have he := hl.final_eq (o := .revert [1, 0]) rfl
  change (Toy.fail [1]).run x = (Toy.fail [1, 0]).run false at he
  cases x <;> exact prefix_ne_of_final (by decide) he

/-- **Inhabited (T07 stub)**: a computable check, comparing the artifact's
runtime bytes with the admitted program's text, is a validator.  Sound only
because the toy EVM loads the main runtime and nothing else. -/
def toyValidator : Validator toySource toyEvm where
  validate := fun i art => match accept i with
    | some r => mainRuntime art == r.prog.text
    | none => false
  sound := fun i art hv r adm w p => by
    have ha : accept i = some r := (admitted_iff i r).1 adm
    rw [ha] at hv
    have hm : mainRuntime art = r.prog.text := beq_iff_eq.1 hv
    have hc : toyCompiler i = some (artOf r.prog.text) := by
      simp only [toyCompiler, compilerWith, ha, Option.map_some, id]
    have pub := toy_publicCorrectness.artifactRefines adm w p hc
    intro e he
    have := pub e he
    revert this
    show RefinesUnder _ _ _ _ (fun _ => HashPremise toyFixed
        (Toy.hashes (decode (mainRuntime (artOf r.prog.text)))) []) _
        (fun _ => (decode (mainRuntime (artOf r.prog.text))).run false) →
      RefinesUnder _ _ _ _ (fun _ => HashPremise toyFixed (Toy.hashes (decode (mainRuntime art)))
        []) _ (fun _ => (decode (mainRuntime art)).run false)
    rw [hm, mainRuntime_artOf]
    exact id

theorem toyValidator_accepts : toyValidator.validate { text := [1, 7] } (artOf (Toy.fail [7]).text) = true :=
  rfl

theorem toyValidator_ctxRefines :
    CtxRefines (toyEvm.contractGuarded (artOf (Toy.fail [7]).text))
      (toySource.contract (toySource.meaning ⟨.fail [7], .legacy, .v2⟩ trivial trivial
        (artOf (Toy.fail [7]).text))) :=
  toyValidator.ctxRefines_back toyValidator_accepts toy_admitted trivial trivial

/-- **Negative control (T07 stub)**: no validator accepts bytes returning one
more byte than the source. -/
theorem validator_rejects_altered (T : Validator toySource toyEvm) :
    T.validate { text := [0] } (artOf (Toy.succeed [0]).text) = false := by
  cases hv : T.validate { text := [0] } (artOf (Toy.succeed [0]).text)
  · rfl
  · exact absurd (T.ctxRefines_back hv (r := ⟨.succeed [], .legacy, .v2⟩) ((admitted_iff _ _).2 rfl)
      trivial trivial) altered_not_ctxRefines_back

/-! ### May-equivalence over failure points -/

/-- **Documented consequence**: where every bound may fail, a data-free
revert and a loop are contextually equivalent (refinement is prefix
simulation; the loop's unfinished prefix lies below the revert). -/
theorem failEmpty_ctxEquiv_loop : CtxEquiv (toyC (.fail [])) (toyC .loop) := by
  refine ⟨fun s _ π ⟨⟨hz, x⟩, _, hb⟩ => ?_, fun s _ π ⟨⟨hz, x⟩, _, hb⟩ => ?_⟩
  · change (Toy.fail []).run x = π at hb
    subst hb
    refine ⟨Toy.loop.run true, ⟨⟨0, true⟩, trivial, rfl⟩, ?_⟩
    cases x <;> exact Prefix.Le.refl _
  · change Toy.loop.run x = π at hb
    subst hb
    refine ⟨(Toy.fail []).run x, ⟨⟨hz, x⟩, trivial, rfl⟩, ?_⟩
    cases x
    · exact ⟨List.prefix_refl _, .inl rfl⟩
    · exact Prefix.Le.refl _

theorem toyC_faithful (t : Toy) : (toyC t).Faithful := ⟨fun _ h => h, id, fun _ => rfl⟩

/-! ### Storage observations -/

/-- A schema without declarations. -/
def schema0 : TypeGraph.Schema 0 where
  origin := ""
  declId := fun i => i.elim0
  declId_injective := fun i => i.elim0
  name := fun i => i.elim0
  fields := fun i => i.elim0
  rank := fun i => i.elim0
  nonempty := fun i => i.elim0
  distinct := fun i => i.elim0
  guarded := fun i => i.elim0

/-- **Inhabited**: implicit and explicit mapping defaults are contextually
equivalent against path adversaries. -/
theorem mapping_defaults_ctxEquiv {n : Nat} {G : TypeGraph.Schema n} {K : PrimTy}
    {V : TypeGraph.Ty n} :
    CtxEquivOn (fun _ => True)
      (storageContract (TypeGraph.Value.mapping (fun _ : K.Denote =>
        (TypeGraph.Slot.absent : TypeGraph.Slot G V))))
      (storageContract (.mapping (fun _ => .present (TypeGraph.Value.dflt V)))) :=
  (obsEq_iff_ctxEquiv _ _).1 TypeGraph.Value.mapping_defaults_obsEq

/-- **Negative control**: different stored booleans are observed. -/
theorem bool_not_ctxEquiv :
    ¬ CtxEquivOn (fun _ => True)
      (storageContract (TypeGraph.Value.prim (G := schema0) (p := .bool) true))
      (storageContract (TypeGraph.Value.prim (G := schema0) (p := .bool) false)) := by
  intro h
  have := (obsEq_iff_ctxEquiv _ _).2 h TypeGraph.Path.nil
  simp only [TypeGraph.Value.observe, TypeGraph.Value.find, TypeGraph.Path.read] at this
  cases this

end Solidity.CtxEquiv.Controls


/-! ## Axiom guards: only the standard axioms. -/
/-- info: 'Solidity.CtxEquiv.Behav.Below.seq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Behav.Below.seq
/-- info: 'Solidity.CtxEquiv.CtxEquiv.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.CtxEquiv.trans
/-- info: 'Solidity.CtxEquiv.CtxRefinesOn.seq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.CtxRefinesOn.seq
/-- info: 'Solidity.CtxEquiv.CtxRefines.noCallback' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.CtxEquiv.CtxRefines.noCallback
/-- info: 'Solidity.CtxEquiv.refines_iff' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.CtxEquiv.refines_iff
/-- info: 'Solidity.CtxEquiv.refinesUnder_iff' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.CtxEquiv.refinesUnder_iff
/-- info: 'Solidity.CtxEquiv.ctxEquivOn_iff_refines' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.CtxEquiv.ctxEquivOn_iff_refines
/-- info: 'Solidity.Roadmap.Cert.ctxEquiv' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Cert.ctxEquiv
/-- info: 'Solidity.Roadmap.Cert.preserves' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.Cert.preserves
/-- info: 'Solidity.CtxEquiv.preserves_iff' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.CtxEquiv.preserves_iff
/-- info: 'Solidity.CtxEquiv.Preserves.ctxEquiv' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Preserves.ctxEquiv
/-- info: 'Solidity.Roadmap.PublicCorrectness.ctx_succeeds' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.PublicCorrectness.ctx_succeeds
/-- info: 'Solidity.CtxEquiv.Controls.dropHash_preserves' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Controls.dropHash_preserves
/-- info: 'Solidity.CtxEquiv.Controls.not_mangle_preserves' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Controls.not_mangle_preserves
/-- info: 'Solidity.CtxEquiv.Controls.validator_rejects_altered' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Controls.validator_rejects_altered
/-- info: 'Solidity.CtxEquiv.Controls.failEmpty_ctxEquiv_loop' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Controls.failEmpty_ctxEquiv_loop
/-- info: 'Solidity.CtxEquiv.CtxRefinesOn.of_empty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.CtxEquiv.CtxRefinesOn.of_empty
/-- info: 'Solidity.CtxEquiv.CtxRefinesOn.safety' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.CtxEquiv.CtxRefinesOn.safety
/-- info: 'Solidity.CtxEquiv.CtxEquivOn.done_iff' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.CtxEquiv.CtxEquivOn.done_iff
/-- info: 'Solidity.CtxEquiv.artifactRefines_iff' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.artifactRefines_iff
/-- info: 'Solidity.Roadmap.PublicCorrectness.ctxRefines_back' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.PublicCorrectness.ctxRefines_back
/-- info: 'Solidity.Roadmap.PublicCorrectness.ctxRefines_forward' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.PublicCorrectness.ctxRefines_forward
/-- info: 'Solidity.Roadmap.PublicCorrectness.transfer'' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.PublicCorrectness.transfer'
/-- info: 'Solidity.CtxEquiv.Validator.ctxRefines_back' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Validator.ctxRefines_back
/-- info: 'Solidity.CtxEquiv.obsEq_iff_ctxEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.obsEq_iff_ctxEquiv
/-- info: 'Solidity.CtxEquiv.Controls.succeed_quiet_ctxEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Controls.succeed_quiet_ctxEquiv
/-- info: 'Solidity.CtxEquiv.Controls.fail_not_ctxEquiv' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Controls.fail_not_ctxEquiv
/-- info: 'Solidity.CtxEquiv.Controls.ctxRefines_not_ctxEquiv' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Controls.ctxRefines_not_ctxEquiv
/-- info: 'Solidity.CtxEquiv.Controls.seq_continuation_observed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Controls.seq_continuation_observed
/-- info: 'Solidity.CtxEquiv.Controls.toy_ctxRefines_back' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Controls.toy_ctxRefines_back
/-- info: 'Solidity.CtxEquiv.Controls.altered_not_ctxRefines_back' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Controls.altered_not_ctxRefines_back
/-- info: 'Solidity.CtxEquiv.Controls.erased_not_ctxRefines_forward' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Controls.erased_not_ctxRefines_forward
/-- info: 'Solidity.CtxEquiv.Controls.toyValidator_ctxRefines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Controls.toyValidator_ctxRefines
/-- info: 'Solidity.CtxEquiv.Controls.bool_not_ctxEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Controls.bool_not_ctxEquiv
/-- info: 'Solidity.CtxEquiv.Controls.mapping_defaults_ctxEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.Controls.mapping_defaults_ctxEquiv
