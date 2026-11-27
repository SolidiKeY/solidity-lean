import Solidity.Theory.Mutability.View
import Solidity.SpecSyntax


namespace Solidity.Theory.Mutability

open Solidity

variable {C : Contract}

def locRoot : SpecLoc → Name
  | .root r => r
  | .field l _ | .index l _ | .all l => locRoot l

def assignableRoots (locs : List SpecLoc) : List Name := locs.map locRoot

structure Frames {Γ Δ : Ctx} (L : List Name) (σ : State C Γ) (τ : State C Δ) : Prop where
  find : ∀ {U : Ty} (r : SRef C U), r.root ∉ L → τ.storage.find r = σ.storage.find r
  net : τ.net = σ.net
  selfBalance : τ.selfBalance = σ.selfBalance

theorem Frames.nothing {Γ Δ : Ctx} {σ : State C Γ} {τ : State C Δ} (h : Frames [] σ τ)
    {U : Ty} (r : SRef C U) : τ.storage.find r = σ.storage.find r :=
  h.find r List.not_mem_nil

theorem Frames.mono {Γ Δ : Ctx} {L M : List Name} (hLM : ∀ r ∈ L, r ∈ M) {σ : State C Γ}
    {τ : State C Δ} (h : Frames L σ τ) : Frames M σ τ :=
  ⟨fun r hr => h.find r fun hl => hr (hLM _ hl), h.net, h.selfBalance⟩

theorem Frames.of_globals {Γ Δ : Ctx} (L : List Name) {σ : State C Γ} {τ : State C Δ}
    (h : globals τ = globals σ) : Frames L σ τ := by
  have hs : τ.storage = σ.storage := congrArg Globals.storage h
  have hn : τ.net = σ.net := congrArg Globals.net h
  have hb : τ.selfBalance = σ.selfBalance := congrArg Globals.selfBalance h
  exact ⟨fun r _ => by rw [hs], hn, hb⟩

theorem Prog.frames_readOnly {μ : Mutability} {Γ Γ' : Ctx} {P : Prog C Γ Γ'}
    (hw : Prog.within μ P = true) (hμ : μ ≠ .nonpayable) (L : List Name) {σ : State C Γ}
    {o : Out C σ.H Γ'} (h : Prog.run σ P = .ok o) : Frames L σ o.st :=
  Frames.of_globals L (frame_globals (Prog.run_frame P hw 0 h).1 hμ)

theorem Prog.storage_readOnly {μ : Mutability} {Γ Γ' : Ctx} {P : Prog C Γ Γ'}
    (hw : Prog.within μ P = true) (hμ : μ ≠ .nonpayable) {σ : State C Γ}
    {o : Out C σ.H Γ'} (h : Prog.run σ P = .ok o) {U : Ty} (r : SRef C U) :
    o.st.storage.find r = σ.storage.find r :=
  (Prog.frames_readOnly hw hμ [] h).nothing r

theorem Prog.frames_of_storeAt {Γ Γ' : Ctx} {P : Prog C Γ Γ'} {M L : List Name}
    (hs : Prog.storeAt P = some M) (hML : ∀ r ∈ M, r ∈ L) {σ : State C Γ}
    {o : Out C σ.H Γ'} (h : Prog.run σ P = .ok o) : Frames L σ o.st := by
  have hk := Prog.run_keeps P h
  rw [hs] at hk
  obtain ⟨hf, hn, hb⟩ := hk
  exact ⟨fun r hr => Storage.Framed.find_eq (hf.mono hML) hr, hn, hb⟩

def assignableCheck {Γ Γ' : Ctx} (P : Prog C Γ Γ') (locs : List SpecLoc) : Bool :=
  Prog.within .view P ||
    match Prog.storeAt P with
    | some M => M.all fun r => (assignableRoots locs).contains r
    | none => false

theorem assignableCheck_sound {Γ Γ' : Ctx} {P : Prog C Γ Γ'} {locs : List SpecLoc}
    (hc : assignableCheck P locs = true) {σ : State C Γ} {o : Out C σ.H Γ'}
    (h : Prog.run σ P = .ok o) : Frames (assignableRoots locs) σ o.st := by
  unfold assignableCheck at hc
  rw [Bool.or_eq_true] at hc
  rcases hc with hv | hm
  · exact Prog.frames_readOnly hv view_ne_nonpayable _ h
  · cases hs : Prog.storeAt P with
    | none => rw [hs] at hm; cases hm
    | some M =>
      rw [hs] at hm
      refine Prog.frames_of_storeAt hs (fun r hr => ?_) h
      have := List.all_eq_true.1 hm r hr
      simpa only [List.contains_iff_mem] using this

def CommittedFrames {Γ Γ' : Ctx} (L : List Name) (σ : State C Γ) :
    TRes (Out C σ.H Γ') → Prop
  | .ok o => Frames L σ o.st
  | .error _ => True

theorem committed_frames {Γ Γ' : Ctx} {P : Prog C Γ Γ'} {locs : List SpecLoc}
    (hc : assignableCheck P locs = true) (σ : State C Γ) :
    CommittedFrames (assignableRoots locs) σ (Prog.run σ P) := by
  cases h : Prog.run σ P with
  | error e => trivial
  | ok o => exact assignableCheck_sound hc h

end Solidity.Theory.Mutability
