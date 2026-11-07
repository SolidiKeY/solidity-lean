import Solidity.Lowering.P8.FrozenInterface
import Solidity.Lowering.P8b.Domain
import Solidity.Roadmap.Controls
import Solidity.Source.FailureResources

/-!
# An inhabited frozen P8a `Producer` (H60)

The frozen `P8a.Producer` was uninhabited over every source whose resource
embeds in `Nat` (P8-SPEC-LAW1, `ResourceContractLaw1`): `FailureProjection`
demands a retraction from the abstract failures onto *every* EVM failure plan.
This module removes the obstruction at its source, not by weakening the
contract: the resource of `planSource` carries a full `Evm.FailurePoints`
plan, the abstract failures ARE those plans, and the transaction's first
frame failure point drives the semantics (an exhausted frame reverts with no
data, as in G07).

`planProducer` then inhabits the UNCHANGED frozen type
`P8a.Producer planSource planReference planOrigins planRoots`, every field
proved in the kernel: failure projection with full plan coverage, operational
realization, exact root/feature extraction, a checked frontend with Lean
certificates, exact admission, unambiguity, the approved readings, both
pipelines and non-vacuity (success, success after hashing, revert,
divergence). `planLowering` inhabits the frozen P8b output for the same
source with the real P8b `assemble`/`pass`/`dom`/`agrees` and a G01 `Cert`.

Scope (not overstated). The programs are G07's toy programs and the
reference is a MODEL reference: `planReference.Executes` decodes the toy
program from the deployed contract name of a `Source.SrcProg` whose program
is EMPTY (no declarations, no contracts; the name denotes no contract) and
runs the G07 toy machine under the plan, ignoring the environment and the
horizon. It is defined below from `decode` alone, but it is not
`Source.sessionAt`. The origins coincide with the realization's program map
(`meaning_origin` is `rfl`), so they are not independent of the producer.
The root model has one execution root per program and features listed per
toy program, and the toy profile is everything, so extraction is exact by
construction rather than evidence of a real feature scan. Resources are
ordered only within one plan, which makes consistency immediate. This is a satisfiability witness for the
frozen interface (H60, H62 (2)); it is NOT actual-Source adequacy, G15 or
S05 completion, and it does not make any statement about Solidity programs.
-/
namespace Solidity.Lowering.P8.PlanWitness
open Solidity.Roadmap Solidity.Roadmap.Controls P8a

/-! ## Resources carrying the full failure plan -/

/-- A source bound: a horizon and the full G06 failure plan. -/
structure PlanBound where
  horizon : Nat
  plan : Evm.FailurePoints

instance : LE PlanBound := ⟨fun a b => a.horizon ≤ b.horizon ∧ a.plan = b.plan⟩

/-- The transaction's frame fails as if out of gas exactly when the plan
makes the first frame fail after `0` of its events (G06: `frame k = some n`
fails the frame after `n` events). Toy runs emit no events, so a later failure
point never fires. Request fates (`tx`) are not read by the toy machine: it
models one transaction frame, not dropped requests or request-level failure
points; they enter only through `NoFail`. -/
def PlanBound.exhausted (r : PlanBound) : Bool := decide (r.plan.frame 0 = some 0)

/-- A plan without resource failures: the EXISTING G06 reading
`Source.FailureResources.NoFail` (every request runs without a failure point,
no frame has one), not an alternative definition. -/
abbrev PlanNoFail (f : Evm.FailurePoints) : Prop := Source.FailureResources.NoFail f

/-- The failure-free plan: every request runs with balance 0, no frame fails. -/
def quietPlan : Evm.FailurePoints := ⟨fun _ => .runs 0 none, fun _ => none⟩

theorem quietPlan_noFail : PlanNoFail quietPlan := ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩

theorem exhausted_false_of_noFail {r : PlanBound} (h : PlanNoFail r.plan) :
    r.exhausted = false := by
  simp only [PlanBound.exhausted, h.2 0, reduceCtorEq, decide_false]

/-! ## The plan-carrying source -/

/-- G07's toy programs, run under the plan's first frame failure point. -/
def planLang : Lang Event Outcome where
  Prog := Toy
  Env := SessionEnv
  Res := PlanBound
  resLE := inferInstanceAs (LE PlanBound)
  Allowed := SessionEnv.Allowed
  Admissible := fun _ => True
  sem := fun p _ r => p.run r.exhausted
  consistent := fun p _ r r' h => by
    show (p.run r.exhausted).Le (p.run r'.exhausted)
    have hx : r.exhausted = r'.exhausted := by simp only [PlanBound.exhausted, h.2]
    rw [hx]
    exact Prefix.Le.refl _
  Forward := fun p _ r => PlanNoFail r.plan ∧ distinctCount (Toy.hashes p) < hashBound
  Guard := fun p _ _ => HashPremise toyFixed (Toy.hashes p) []

/-- G07's toy frontend and settings, with `Failures` the full EVM plans. -/
def planSource : SourceSpec :=
  { toySource with
    lang := planLang
    meaning := fun r _ _ _ => r.prog
    inhabited := ⟨quietEnv, quietEnv_allowed⟩
    Failures := Evm.FailurePoints
    failures := PlanBound.plan
    withFailures := fun r x => { r with plan := x }
    failures_with := fun _ _ => rfl
    NoFail := PlanNoFail
    hashed := fun p _ _ => Toy.hashes p
    hashed_consistent := fun _ _ _ _ _ => List.prefix_refl _
    slotHashed := fun _ _ _ => []
    slotHashed_sub := fun _ _ _ _ h => nomatch h
    forward_iff := fun _ _ _ => Iff.rfl
    guard_iff := fun _ _ _ => Iff.rfl }

/-- Admission is G07's, unchanged: the computed `accept`. -/
theorem admitted_iff (i : ToyInput) (r : ToyRes) :
    planSource.Admitted i r ↔ accept i = some r :=
  Controls.admitted_iff i r

theorem plan_forward (t : Toy) (e : SessionEnv) (h : Nat) :
    planSource.lang.Forward t e ⟨h, quietPlan⟩ ∧ planSource.lang.Guard t e ⟨h, quietPlan⟩ :=
  ⟨⟨quietPlan_noFail, toy_count t⟩, toy_premise t⟩

theorem plan_no_event {p : Toy} {b : Bool} {x : Event} (hm : x ∈ (Toy.run p b).events) : False := by
  rw [Toy.run_events] at hm
  cases hm

/-- The four G01 non-vacuity witnesses, at the failure-free plan. -/
theorem planSource_nonVacuous : planSource.NonVacuous := by
  refine ⟨⟨{ text := [3, 1] }, ⟨.quiet [1], .legacy, .v2⟩, trivial, trivial, quietEnv,
      ⟨0, quietPlan⟩, [1], (admitted_iff _ _).2 rfl, quietEnv_allowed, trivial,
      List.cons_ne_nil _ _, fun _ => ⟨(plan_forward _ _ _).1, (plan_forward _ _ _).2, rfl⟩⟩,
    ⟨{ text := [0, 1] }, ⟨.succeed [1], .legacy, .v2⟩, trivial, trivial, quietEnv,
      ⟨0, quietPlan⟩, [1], (admitted_iff _ _).2 rfl, quietEnv_allowed, trivial,
      fun _ => ⟨List.cons_ne_nil _ _, (plan_forward _ _ _).1, (plan_forward _ _ _).2, rfl⟩⟩,
    ⟨{ text := [1, 7] }, ⟨.fail [7], .legacy, .v2⟩, trivial, trivial, quietEnv,
      ⟨0, quietPlan⟩, [7], (admitted_iff _ _).2 rfl, quietEnv_allowed, trivial,
      fun _ => ⟨(plan_forward _ _ _).1, (plan_forward _ _ _).2, rfl⟩⟩,
    ⟨{ text := [2] }, ⟨.loop, .legacy, .v2⟩, trivial, trivial, quietEnv,
      (admitted_iff _ _).2 rfl, quietEnv_allowed, fun _ _ _ => rfl, fun _ rs ⟨_, hno⟩ => ?_⟩⟩
  show (Toy.run .loop rs.exhausted).final = none
  rw [exhausted_false_of_noFail hno]
  rfl

/-- The approved readings. The settings, link-map and region parts are
G07's own proofs (they read only the frontend); the event parts hold since no
toy run emits an event, whatever the plan. -/
theorem planSource_approved : planSource.Approved := by
  refine ⟨fun _ => trivial, fun p _ r _ _ _ _ hm _ => plan_no_event hm,
    fun p _ r _ _ _ _ _ hm => (plan_no_event hm).elim, fun p _ r h _ _ _ _ _ _ hm => ?_,
    toySource_approved.2.2.2.2.1, toySource_approved.2.2.2.2.2.1, toyFixed_sane⟩
  have hm' : h ++ _ <+: (Toy.run p r.exhausted).events := hm
  rw [Toy.run_events] at hm'
  have := hm'.length_le
  simp only [List.length_append, List.length_singleton, List.length_nil] at this
  omega

theorem planSource_unambiguous : planSource.Unambiguous := by
  refine ⟨fun i s s' ⟨_, hs⟩ ⟨_, hs'⟩ => ?_, fun s r r' hr hr' => ?_⟩
  · rw [hs] at hs'
    exact Option.some.inj hs'
  · exact hr.trans hr'.symm

theorem planSource_allPipelines : planSource.AllPipelines := by
  rintro i q ⟨r, hr⟩
  have h := (admitted_iff i r).1 hr
  simp only [accept] at h
  split at h
  · rename_i hl
    cases hp : parse i.text with
    | none => rw [hp] at h; cases h
    | some t =>
      have ha : accept { i with pipeline := q } =
          some ⟨t, q, ToyInput.coder { i with pipeline := q }⟩ := by
        simp only [accept, hl, if_true, hp, Option.map_some]
      exact ⟨_, (admitted_iff _ _).2 ha⟩
  · cases h

/-! ## The checked frontend and admission -/

deriving instance DecidableEq for ToyRes

/-- The certificate is the parsed toy program; the checker recomputes the
parse, the empty link map and the recorded settings. -/
def planChecked : CheckedFrontend planSource where
  Cert := Toy
  produce := fun i => (accept i).map fun r => (r, r.prog)
  check := fun i r t => decide (accept i = some r ∧ r.prog = t)
  checked := fun i r t h => (admitted_iff i r).2 (of_decide_eq_true h).1
  accepted := fun i r t h => by
    cases ha : accept i with
    | none => simp only [ha, Option.map_none, reduceCtorEq] at h
    | some r' =>
      simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact decide_eq_true ⟨rfl, rfl⟩
  complete := fun i r h => ⟨r.prog, by simp only [(admitted_iff i r).1 h, Option.map_some]⟩

def planAdmission : Admission planSource where
  frontend := accept
  sound := fun i r h => (admitted_iff i r).2 h
  complete := fun i r h => (admitted_iff i r).1 h

theorem plan_frontend_agrees (i : planSource.Input) :
    planAdmission.frontend i = (planChecked.produce i).map Prod.fst := by
  show accept i = ((accept i).map fun r => (r, r.prog)).map Prod.fst
  cases accept i <;> rfl

/-! ## Root model and exact extraction -/

/-- The language features a toy program's single execution root uses. -/
def toyFeatures : Toy → List Language.Feature
  | .succeed _ => [.functions, .keccakBuiltin, .returnStatement]
  | .quiet _ => [.functions, .returnStatement]
  | .fail _ => [.functions, .revertStatement]
  | .loop => [.functions, .whileStatement]

/-- One execution root per resolution (its program), no separate observation
root; every feature combination is in the toy profile, which is `True`. -/
def planRoots : RootModel planSource where
  Root := Toy
  executionRoot := fun r root => root = r.prog
  observationRoot := fun _ _ => False
  featureAt := fun r root f => root = r.prog ∧ f ∈ toyFeatures root
  classify := fun _ _ => true

def planExtractor : Extractor planRoots where
  extract := fun r =>
    { roots := [r.prog]
      features := toyFeatures r.prog
      roots_exact := fun root => by
        show root ∈ [r.prog] ↔ root = r.prog ∨ False
        simp only [List.mem_singleton, or_false]
      features_exact := fun f => by
        show f ∈ toyFeatures r.prog ↔ ∃ root ∈ [r.prog], root = r.prog ∧ f ∈ toyFeatures root
        simp only [List.mem_singleton, exists_eq_left, true_and]
      classification_exact := ⟨fun _ => trivial, fun _ => rfl⟩ }

/-! ## Failure projection with full plan coverage -/

/-- The projection is the identity: every EVM plan is an abstract failure,
which is exactly what P8-SPEC-LAW1 shows a `Nat` resource cannot supply. -/
def planFailures : FailureProjection planSource where
  points := id
  ofPoints := id
  points_ofPoints := fun _ => rfl
  noFail_requests := fun _ h => h.1
  noFail_frames := fun _ h => h.2

/-! ## The model operational reference and source origins -/

/-- The empty intrinsic Source environment and program. -/
def emptyEnv : Source.Env := ⟨[]⟩

def emptyProgram : Source.Program emptyEnv where
  body := fun _ => none
  consts := fun _ => none
  inits := fun _ => []
  ctor := fun _ => none
  ctorLocals := fun _ => []
  baseArgs := fun _ => []
  contracts := []

/-- Bytes as a contract name, one character per byte. -/
def nameOf (b : Bytes) : String := String.mk (b.map fun x => Char.ofNat x.toNat)

/-- The inverse reading of a contract name as bytes. -/
def bytesOf (s : String) : Bytes := s.toList.map fun c => c.toNat.toUInt8

theorem byte_char (x : UInt8) : (Char.ofNat x.toNat).toNat.toUInt8 = x := by
  have h : x.toNat < 256 := x.toBitVec.isLt
  have hv : Nat.isValidChar x.toNat := Or.inl (by omega)
  have hc : (Char.ofNat x.toNat).toNat = x.toNat := by
    simp only [Char.ofNat, hv, dite_true, Char.ofNatAux, Char.toNat]
    rfl
  rw [hc]
  exact UInt8.ofNat_toNat

theorem bytesOf_nameOf (b : Bytes) : bytesOf (nameOf b) = b := by
  show List.map (fun c => c.toNat.toUInt8) (List.map (fun x => Char.ofNat x.toNat) b) = b
  induction b with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, byte_char, List.cons.injEq, true_and]
    exact ih

/-- A toy program as an intrinsic Source program with an EMPTY program over the empty
environment, deploying the contract named by its text. -/
def sourceOf (t : Toy) : SourceProgram :=
  ⟨emptyEnv, ⟨emptyProgram, .legacy, toyFixed, nameOf t.text⟩⟩

/-- The MODEL reference: it decodes the toy program from the deployed
contract name and runs G07's machine under the plan. It is defined from
`decode` alone, not from any field of the producer below. -/
def planReference : OperationalReference where
  Resource := PlanBound
  points := PlanBound.plan
  Executes := fun sp _ r out => Toy.run (decode (bytesOf sp.2.main)) r.exhausted = out

theorem decode_sourceOf (t : Toy) : decode (bytesOf (sourceOf t).2.main) = t := by
  show decode (bytesOf (nameOf t.text)) = t
  rw [bytesOf_nameOf, decode_text]

/-- Source origins: each admitted meaning is the Source program of its toy. -/
def planOrigins : SourceOrigins planSource where
  meaning := fun r _ _ _ => sourceOf r.prog

def planRealization : SourceRealization planReference planOrigins planFailures where
  program := sourceOf
  resource := id
  exact := fun p e r out => by
    show Toy.run (decode (bytesOf (sourceOf p).2.main)) r.exhausted = out ↔
      Toy.run p r.exhausted = out
    rw [decode_sourceOf]
  meaning_origin := fun _ _ _ _ => rfl
  resource_points := fun _ => rfl

/-! ## The inhabitant -/

/-- **An inhabitant of the unchanged frozen `P8a.Producer`.** -/
def planProducer : Producer planSource planReference planOrigins planRoots where
  failures := planFailures
  realization := planRealization
  extraction := planExtractor
  checkedFrontend := planChecked
  admission := planAdmission
  frontend_agrees := plan_frontend_agrees
  unambiguous := planSource_unambiguous
  approved := planSource_approved
  allPipelines := planSource_allPipelines
  nonVacuous := planSource_nonVacuous

theorem producer_inhabited :
    Nonempty (Producer planSource planReference planOrigins planRoots) :=
  ⟨planProducer⟩

/-! ## The P8b lowering for the same source -/

/-- The intrinsic layer: the plan language itself. -/
def planIntrinsic : IntrinsicSpec where
  World := Toy
  lang := planLang
  ofWorld := id
  worlds := fun _ _ _ => []
  fixed := toyFixed
  session := id
  ofSession := id
  session_of := fun _ => rfl
  of_session := fun _ => rfl
  allowed_iff := fun _ => Iff.rfl
  NoFail := fun r => PlanNoFail r.plan
  hashed := fun p _ _ => Toy.hashes p
  slotHashed := fun _ _ _ => []
  forward_iff := fun _ _ _ => Iff.rfl
  guard_iff := fun _ _ _ => Iff.rfl

/-- The G01 certificate of P8b's structural pass with the identity emitter:
the bound function is literally the identity (no choice). -/
def planCert : Cert (P8b.pass planSource planIntrinsic id) where
  envSound := P8b.envSound planSource planIntrinsic
  envOnto := P8b.envOnto planSource planIntrinsic
  need := fun _ _ _ r => r
  need_ok := fun _ _ _ _ _ _ hf hg => ⟨trivial, hf, hg, Prefix.Le.refl _⟩
  back := fun _ _ _ r _ _ hg => ⟨r, trivial, hg, Prefix.Le.refl _⟩

/-- The frozen P8b `Lowering`, assembled by P8b's own `assemble`. -/
def planLowering : Lowering planSource planIntrinsic :=
  P8b.assemble planSource planIntrinsic id planCert

/-- info: 'Solidity.Lowering.P8.PlanWitness.producer_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms producer_inhabited
/-- info: 'Solidity.Lowering.P8.PlanWitness.planLowering' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms planLowering

end Solidity.Lowering.P8.PlanWitness
