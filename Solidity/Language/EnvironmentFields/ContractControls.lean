import Solidity.Language.EnvironmentFields.Contracts

/-! Inhabited and falsifying controls for the provisional G01 interfaces.
These are independent toy models, not Source/EVM producer certificates.
Every positive contract has a reachable, nonempty execution; negative controls
change a required observation or obligation while retaining live domains. -/
namespace Solidity.Roadmap.FullScope.Controls
open Solidity.Roadmap Solidity.Roadmap.FullScope

structure AssemblyState where
  pointer : Nat
  bytes : Bytes

def memOK (s : AssemblyState) : Prop := s.pointer = 128

def assembly (before after : AssemblyState) : Prop :=
  after = ⟨before.pointer+3, before.bytes++[0xaa]⟩

def writeback (s : AssemblyState) : AssemblyState := ⟨128,s.bytes⟩

def corresponds (before after : AssemblyState) : Prop := before.bytes=after.bytes

theorem unsafe_writeback : UnsafeWriteback AssemblyState memOK assembly writeback corresponds :=
  ⟨fun _ _ _ => rfl,fun _ _ _ => rfl⟩

def dirtyBefore : AssemblyState := ⟨7,[0,0xff]⟩
def dirtyAfter : AssemblyState := ⟨10,[0,0xff,0xaa]⟩

theorem unsafe_live : assembly dirtyBefore dirtyAfter ∧ ¬memOK dirtyBefore ∧
    ¬memOK dirtyAfter ∧ memOK (writeback dirtyAfter) ∧
    (writeback dirtyAfter).bytes=[0,0xff,0xaa] := by
  refine ⟨rfl,?_,?_,rfl,rfl⟩
  · change ¬(7 : Nat)=128
    decide
  · change ¬(10 : Nat)=128
    decide

theorem unrecovered_writeback_refused :
    ¬UnsafeWriteback AssemblyState memOK assembly id corresponds := by
  intro h
  have impossible : (10 : Nat)=128 := h.recovers dirtyBefore dirtyAfter rfl
  omega

theorem erasing_writeback_refused :
    ¬UnsafeWriteback AssemblyState memOK assembly (fun _ => ⟨128,[]⟩) corresponds := by
  intro h
  have impossible : ([0,0xff,0xaa] : Bytes)=[] := h.corresponds dirtyBefore dirtyAfter rfl
  cases impossible

def optimize (block : Bool × Bytes) : Bool × Bytes :=
  if block.1 then block else (false,block.2++[0])

def isUnsafe (block : Bool × Bytes) : Prop := block.1=true

theorem opaque_preservation : Opaque optimize isUnsafe := by
  intro block h
  simp only [optimize,isUnsafe] at *
  rw [h]
  rfl

theorem opaque_live : isUnsafe (true,[0x60,1]) ∧
    optimize (true,[0x60,1])=(true,[0x60,1]) ∧
    optimize (false,[1])=(false,[1,0]) := ⟨rfl,rfl,rfl⟩

theorem changed_unsafe_refused :
    ¬Opaque (fun block : Bool × Bytes => (block.1,block.2++[0])) isUnsafe := by
  intro h
  have impossible : ([1,0] : Bytes)=[1] := congrArg Prod.snd (h (true,[1]) rfl)
  cases impossible

def trace (bytes : Bytes) (gas : Word) (env : Bool) : Prefix Observation Outcome :=
  ⟨[.code Address.zero bytes,.scalar .gasleft gas,.memory 0 (if env then 0xaa else 0x55)],
    some (.success bytes)⟩

def reverted (bytes : Bytes) (gas : Word) (env : Bool) : Prefix Observation Outcome :=
  ⟨(trace bytes gas env).events,some (.revert [])⟩

abbrev model : Lang Observation Outcome where
  Prog := Bytes
  Env := Bool
  Res := Nat
  resLE := inferInstance
  Allowed := fun _ => True
  Admissible := fun _ => True
  sem := fun bytes env _ => trace bytes 5 env
  consistent := fun _ _ _ _ _ => Prefix.Le.refl _

def identityPass : Pass model model := ⟨fun _ => True,fun p _ => p,id⟩

def identityCertificate : Cert identityPass where
  envSound := fun _ _ => trivial
  envOnto := fun e _ => ⟨e,trivial,rfl⟩
  need := fun _ _ _ r => r
  need_ok := fun _ _ _ _ _ _ _ _ => ⟨trivial,trivial,trivial,Prefix.Le.refl _⟩
  back := fun _ _ _ r _ _ _ => ⟨r,trivial,trivial,Prefix.Le.refl _⟩

def exact : Exact model model := ⟨identityPass,identityCertificate,fun _ => trivial⟩

theorem exact_live : exact.pass.Dom [1,2] ∧ model.Allowed true ∧ model.Admissible 7 ∧
    model.Forward [1,2] true 7 ∧ model.Guard [1,2] true 7 ∧
    (model.sem [1,2] true 7).events.length=3 ∧
    (model.sem [1,2] true 7).final=some (.success [1,2]) :=
  ⟨trivial,trivial,trivial,trivial,trivial,rfl,rfl⟩

abbrev revertingModel : Lang Observation Outcome :=
  {model with sem := fun bytes env _ => reverted bytes 5 env
              consistent := fun _ _ _ _ _ => Prefix.Le.refl _}

theorem reverting_exact_refused : ¬Nonempty (Exact model revertingModel) := by
  rintro ⟨h⟩
  have hprefix := (h.certificate.need_ok [1] (h.total [1]) true 7
    trivial trivial trivial trivial).2.2.2
  rcases hprefix.2 with unfinished | same
  · cases unfinished
  · have impossible := congrArg Prefix.final same
    change (some (.revert []) : Option Outcome) = some (.success [1]) at impossible
    cases impossible

def exactRefinement : RefinesUnder model.Admissible model.Admissible
    (model.Forward [1,2] true) (model.Guard [1,2] true) (model.Guard [1,2] true)
    (model.sem [1,2] true) (model.sem [1,2] true) :=
  identityCertificate.refines [1,2] trivial true trivial

theorem optimizer_from_refinement : Optimizes model.Admissible model.Admissible
    (model.Forward [1,2] true) (model.Guard [1,2] true) (model.Guard [1,2] true)
    (model.sem [1,2] true) (model.sem [1,2] true) :=
  optimizes_of_refines exactRefinement

theorem optimizer_live : ∃ rt, model.Admissible rt ∧
    (eraseGas (model.sem [1,2] true 7)).Le (eraseGas (model.sem [1,2] true rt)) :=
  optimizer_from_refinement.1 7 trivial trivial trivial

theorem reverting_optimizer_refused : ¬Optimizes model.Admissible revertingModel.Admissible
    (model.Forward [1,2] true) (model.Guard [1,2] true) (revertingModel.Guard [1,2] true)
    (model.sem [1,2] true) (revertingModel.sem [1,2] true) := by
  intro h
  obtain ⟨rt,_,hprefix⟩ := h.1 7 trivial trivial trivial
  rcases hprefix.2 with unfinished | same
  · cases unfinished
  · have impossible := congrArg Prefix.final same
    change (some (.revert []) : Option Outcome) = some (.success [1,2]) at impossible
    cases impossible

def compiled (bytes : Bytes) : Artifact := ⟨[⟨bytes,bytes,[]⟩],0⟩

def readerValue (art : Artifact) (oracle : Oracle art) : Word :=
  if h : 0<art.contracts.length then
    oracle ⟨⟨⟨0,h⟩,.runtime⟩,0,.gasleft⟩ else 0

abbrev oracleModel : Lang Observation Outcome where
  Prog := Bytes × Word
  Env := Bool
  Res := Word
  resLE := ⟨fun a b => a=b⟩
  Allowed := fun _ => True
  Admissible := fun _ => True
  sem := fun p e _ => trace p.1 p.2 e
  consistent := fun _ _ _ _ _ => Prefix.Le.refl _

abbrev source : Source where
  Resolved := Bytes
  lang := oracleModel
  meaning := fun _ input => (input.artifact.initcode 0,readerValue input.artifact input.oracle)

abbrev target : Target where
  lang := {
    Prog := Artifact
    Env := Bool
    Res := Word
    resLE := ⟨fun a b => a=b⟩
    Allowed := fun _ => True
    Admissible := fun _ => True
    sem := fun art e r => trace (art.initcode 0) (readerValue art (fun _ => r)) e
    consistent := by intro art e r r' same;cases same;exact Prefix.Le.refl _ }
  load := id
  read := fun _ _ r _ => r

theorem artifact_sound : ArtifactSound source target compiled id := by
  intro resolved env rt allowed admissible
  dsimp only
  intro guard
  exact ⟨rt,trivial,Prefix.Le.refl _⟩

def gasQuery : Query (compiled [0x60,1]) := ⟨⟨⟨0,by decide⟩,.runtime⟩,3,.gasleft⟩

theorem artifact_sound_live : target.lang.Allowed true ∧ target.lang.Admissible 5 ∧
    target.lang.Guard (target.load (compiled [0x60,1])) true 5 ∧
    (target.lang.sem (target.load (compiled [0x60,1])) true 5).events=
      [.code Address.zero [0x60,1],.scalar .gasleft 5,.memory 0 0xaa] ∧
    (target.lang.sem (target.load (compiled [0x60,1])) true 5).final=some (.success [0x60,1]) :=
  ⟨trivial,trivial,trivial,rfl,rfl⟩

theorem oracle_agreement : OracleAgreement (compiled [0x60,1])
    (fun _ => 5) (target.read (compiled [0x60,1]) true 5) :=
  fun _ => rfl

theorem oracle_query_live : target.read (compiled [0x60,1]) true 5 gasQuery=5 ∧
    target.read (compiled [0x60,1]) true 6 gasQuery=6 := ⟨rfl,rfl⟩

theorem changed_oracle_refused : ¬OracleAgreement (compiled [0x60,1])
    (target.read (compiled [0x60,1]) true 5) (target.read (compiled [0x60,1]) true 6) := by
  intro h
  exact (by decide : (5 : Word)≠6) (h gasQuery)

abbrev revertingTarget : Target where
  lang := {target.lang with
    sem := fun art e r => reverted (art.initcode 0) (readerValue art (fun _ => r)) e
    consistent := by intro art e r r' same;cases same;exact Prefix.Le.refl _}
  load := id
  read := fun _ _ r _ => r

theorem reverting_artifact_sound_refused : ¬ArtifactSound source revertingTarget compiled id := by
  intro h
  obtain ⟨rs,_,hprefix⟩ := h [0x60,1] true 5 trivial trivial trivial
  rcases hprefix.2 with unfinished | same
  · cases unfinished
  · have impossible := congrArg Prefix.final same
    change (some (.success [0x60,1]) : Option Outcome) = some (.revert []) at impossible
    cases impossible

#print axioms unsafe_writeback
#print axioms unsafe_live
#print axioms unrecovered_writeback_refused
#print axioms erasing_writeback_refused
#print axioms opaque_preservation
#print axioms opaque_live
#print axioms changed_unsafe_refused
#print axioms exact
#print axioms exact_live
#print axioms reverting_exact_refused
#print axioms optimizer_from_refinement
#print axioms optimizer_live
#print axioms reverting_optimizer_refused
#print axioms artifact_sound
#print axioms artifact_sound_live
#print axioms oracle_agreement
#print axioms oracle_query_live
#print axioms changed_oracle_refused
#print axioms reverting_artifact_sound_refused
end Solidity.Roadmap.FullScope.Controls
