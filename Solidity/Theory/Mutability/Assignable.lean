import Solidity.Theory.Mutability.View
import Solidity.SpecSyntax

/-!
# `assignable` is sound (S3.2)

`docs/feature-work/semantics-extensions.md`, S3.2: the frame of
`docs/function-specs.md` (`assignable l₁, …;`,
`A` of the obligation) follows from the mutability theorem.

`A` (`assignableFml`, `Calculus/SurfaceSpec.lean`) owes, after the call,
`find(storage, p) = find(old, p)` for every word `p` no listed location
covers, and the ledger and balance where nothing books them.  Its semantic
content here is `Frames L σ τ`, at the granularity of the state variables
`L` the clause names (`assignableRoots`): every storage word of a root
outside `L` reads in `τ` as in `σ`, and the ledger and the balance are kept.

Two sources of the frame:

* **mutability** (S3.1): a `view` or `pure` body changes no storage word
  at all, so it meets every clause, `\nothing` included, word by word
  (`Prog.frames_readOnly`, `Prog.storage_readOnly`);
* **the modifies set**: a body whose written roots (`Prog.storeAt`) the
  clause names meets it (`Prog.frames_of_storeAt`), through the frame theorem
  `Prog.run_keeps` (`Semantics/RunFrame.lean`).

`assignableCheck` decides the two premises; `assignableCheck_sound` is the
theorem a caller uses.  Every result also holds of the committed state in
every outcome (`committed_frames`): a halt commits the entry state.

Finer clauses (`s.f`, `m[e]`) cover less than their root; at those roots
`Frames` owes nothing, so the check is sound but coarser there than `A`.
-/

namespace Solidity.Theory.Mutability

open Solidity

variable {C : Contract}

/-- The state variable an `assignable` location starts at: `x`, `s.f`,
`m[e]`, `m[*]` all at their root. -/
def locRoot : SpecLoc → Name
  | .root r => r
  | .field l _ | .index l _ | .all l => locRoot l

/-- The roots an `assignable` clause names (`\nothing` is `[]`). -/
def assignableRoots (locs : List SpecLoc) : List Name := locs.map locRoot

/-- **The frame of `assignable`, semantically**: every storage word of a root
outside `L` reads in `τ` as in `σ`; the ledger and the balance are kept. -/
structure Frames {Γ Δ : Ctx} (L : List Name) (σ : State C Γ) (τ : State C Δ) : Prop where
  find : ∀ {U : Ty} (r : SRef C U), r.root ∉ L → τ.storage.find r = σ.storage.find r
  net : τ.net = σ.net
  selfBalance : τ.selfBalance = σ.selfBalance

/-- `\nothing`'s frame is the whole storage, word by word. -/
theorem Frames.nothing {Γ Δ : Ctx} {σ : State C Γ} {τ : State C Δ} (h : Frames [] σ τ)
    {U : Ty} (r : SRef C U) : τ.storage.find r = σ.storage.find r :=
  h.find r List.not_mem_nil

/-- A larger clause frames less. -/
theorem Frames.mono {Γ Δ : Ctx} {L M : List Name} (hLM : ∀ r ∈ L, r ∈ M) {σ : State C Γ}
    {τ : State C Δ} (h : Frames L σ τ) : Frames M σ τ :=
  ⟨fun r hr => h.find r fun hl => hr (hLM _ hl), h.net, h.selfBalance⟩

/-- Unchanged globals frame every clause. -/
theorem Frames.of_globals {Γ Δ : Ctx} (L : List Name) {σ : State C Γ} {τ : State C Δ}
    (h : globals τ = globals σ) : Frames L σ τ := by
  have hs : τ.storage = σ.storage := congrArg Globals.storage h
  have hn : τ.net = σ.net := congrArg Globals.net h
  have hb : τ.selfBalance = σ.selfBalance := congrArg Globals.selfBalance h
  exact ⟨fun r _ => by rw [hs], hn, hb⟩

/-- **S3.2 from S3.1**: a read-only (`view` or `pure`) body meets every
`assignable` clause: `function get() view returns (uint) { return x; }`
under `assignable \nothing;`. -/
theorem Prog.frames_readOnly {μ : Mutability} {Γ Γ' : Ctx} {P : Prog C Γ Γ'}
    (hw : Prog.within μ P = true) (hμ : μ ≠ .nonpayable) (L : List Name) {σ : State C Γ}
    {o : Out C σ.H Γ'} (h : Prog.run σ P = .ok o) : Frames L σ o.st :=
  Frames.of_globals L (frame_globals (Prog.run_frame P hw 0 h).1 hμ)

/-- A read-only body changes no storage word, covered or not. -/
theorem Prog.storage_readOnly {μ : Mutability} {Γ Γ' : Ctx} {P : Prog C Γ Γ'}
    (hw : Prog.within μ P = true) (hμ : μ ≠ .nonpayable) {σ : State C Γ}
    {o : Out C σ.H Γ'} (h : Prog.run σ P = .ok o) {U : Ty} (r : SRef C U) :
    o.st.storage.find r = σ.storage.find r :=
  (Prog.frames_readOnly hw hμ [] h).nothing r

/-- **S3.2 from the modifies set**: a body that writes only roots the clause
names meets it (`uint a; uint b; function f() { a = 1; }` under `assignable
a;` keeps every word of `b`). -/
theorem Prog.frames_of_storeAt {Γ Γ' : Ctx} {P : Prog C Γ Γ'} {M L : List Name}
    (hs : Prog.storeAt P = some M) (hML : ∀ r ∈ M, r ∈ L) {σ : State C Γ}
    {o : Out C σ.H Γ'} (h : Prog.run σ P = .ok o) : Frames L σ o.st := by
  have hk := Prog.run_keeps P h
  rw [hs] at hk
  obtain ⟨hf, hn, hb⟩ := hk
  exact ⟨fun r hr => Storage.Framed.find_eq (hf.mono hML) hr, hn, hb⟩

/-- **The `assignable` check**: the body is read-only, or its modifies set
lies in the clause's roots. -/
def assignableCheck {Γ Γ' : Ctx} (P : Prog C Γ Γ') (locs : List SpecLoc) : Bool :=
  Prog.within .view P ||
    match Prog.storeAt P with
    | some M => M.all fun r => (assignableRoots locs).contains r
    | none => false

/-- **`assignable` is sound**: a body that passes `assignableCheck` frames
its clause in every successful run. -/
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

/-- What a run commits frames the clause in every outcome: a halt commits
the entry's globals. -/
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
