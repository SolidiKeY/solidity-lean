import Solidity.Correctness.Lowering.Sim.Session.Binding.Initial
import Solidity.Correctness.Lowering.Sim.Session.Binding.Agreement

/-!
# The session lift: what needs no machine (ls2s, lane binding)

The parts of `Shrink.Lowering.SessionLift Sim.diagram`
(`Goals/LoweringSession.lean`) that mention neither session machine.

* `envSound`, `envOnto`: `envAbs` in the shapes `lang_passCorrect` takes.
* `bodiesBound`: from `Sim.diagram.Total`, every fragment production run at a
  callee site of a function of the compilation is associated with the resolved
  body of the Source function of that name. `Total` gives a body with the same
  production input; `Assoc.rebind` moves the association to a body with that
  input reading the same spelled program; the production association
  `SpelledBody` says that program is the resolved body.
* Initial matching: `Binding/Initial.lean`; agreement: `Binding/Agreement.lean`.

## Limitations (stated, not hidden)

* `SpelledBody` holds today because no callee request spells anything
  (`not_spells_callee`: `Total.Spells` is for plain requests), so `bodiesBound`
  has no instance yet: `Total` refutes every fragment production run at a
  callee site (`no_callee_run`). Once `Total.Spells` reads callee requests,
  `spelledBody` needs a link the goal does not state: `Compilation.Names`
  binds raw functions to Source functions by name only, so nothing relates a
  raw declaration's body to the resolved items of the Source function.
* `Sim.diagram.Total` is a hypothesis, not proved here.
-/
namespace Solidity.Correctness.Lowering.Sim.Session

open Solidity.Goals.Shrink.Lowering
open Solidity.Correctness.Lowering.Sim
open Solidity.Lowering.V07 (ContextMap)
open Solidity.Roadmap (SessionEnv)
open Solidity.Semantics.IntrinsicSession (spec)

/-- `envAbs` is sound: `lang_passCorrect`'s `envSound`. -/
theorem envSound (F : Roadmap.Fixed) (E : Source.Env) :
    ∀ e, (spec F).lang.Allowed e → (Source.sourceLangEvents E).Allowed (envAbs e) :=
  envAbs_sound F

/-- `envAbs` is onto the allowed Source environments: `lang_passCorrect`'s `envOnto`. -/
theorem envOnto (F : Roadmap.Fixed) (E : Source.Env) :
    ∀ e, (Source.sourceLangEvents E).Allowed e → ∃ e', (spec F).lang.Allowed e' ∧ envAbs e' = e :=
  envAbs_onto F

/-- The request of a body reads its production input only. -/
theorem request_congr {b' b : Body} (same : b'.SameInput b) (u : Emitted) :
    request b' u = request b u := by
  obtain ⟨site, raw, slots, scope, before⟩ := same
  simp only [request, site, raw, slots, scope, before]

/-- The program a body reads starts in the body's context. -/
theorem Reads.before {b : Body} {s : Total.SourceProgram} (h : Reads b s) : s.before = b.ctx := by
  unfold Reads at h
  split at h
  · rw [h]; rfl
  · obtain ⟨_, _, _, rfl⟩ := h; rfl

/-- **The association moves along the production input**, to a body with the
same input that reads the spelled programs the first one reads. -/
theorem Assoc.rebind {b' b : Body} {u : Emitted} {m : ContextMap b'.ctx u.Γ} (h : Assoc b' u m)
    (same : b'.SameInput b)
    (reads : ∀ s, Total.Spells (request b u) s → Reads b' s → Reads b s) :
    ∃ m' : ContextMap b.ctx u.Γ, Assoc b u m' := by
  obtain ⟨context, names, aligned, s, spells, read⟩ := h
  rw [request_congr same] at context names spells
  have read' := reads s spells read
  have ctx : b'.ctx = b.ctx := (Reads.before read).symm.trans (Reads.before read')
  obtain ⟨E', R', M', k', Γ', input', site'⟩ := b'
  dsimp only at ctx m aligned
  subst ctx
  exact ⟨m, context, names, aligned, s, spells, read'⟩

variable {E : Source.Env}

/-- The Source program of a resolved function body. -/
def bodyProgram (rb : Source.RBody E) : Total.SourceProgram :=
  ⟨E, rb.rs, rb.inModifier, .body, rb.locals, rb.out, rb.items⟩

/-- A body of a resolved function at a callee site reads that function's program. -/
theorem reads_ofResolved (rb : Source.RBody E) (raw : List RawStmt)
    (returnSlots : Option (List String)) (scope : ElabScope)
    (before : Solidity.Correctness.Lowering.Checker.Snapshot) {site : Site}
    (callee : site ≠ .loop) :
    Reads (Body.ofResolved rb raw returnSlots scope before site) (bodyProgram rb) := by
  cases site with
  | loop => exact absurd rfl callee
  | callee | recursive => exact ⟨_, rb.items, rfl, rfl⟩

/-- A site that calls a function is a callee's. -/
theorem calls_callee {C : Contract} {f : String} {site : Site} (h : site.Calls C f) :
    site ≠ .loop := by
  rintro rfl
  exact h

variable [FreshNames]

/-- **The production association**: the program a request at a callee site of
a function of the compilation spells is that Source function's resolved body. -/
def SpelledBody (P : Source.SrcProg E) (c : Compilation) : Prop :=
  ∀ d rb, SrcFun P d rb →
    ∀ raw returnSlots scope before site (u : Emitted) (s : Total.SourceProgram), u.C = c.C →
      site.Calls c.C d.name →
      Total.Spells (request (Body.ofResolved rb raw returnSlots scope before site) u) s →
        s = bodyProgram rb

omit [FreshNames] in
/-- No request at a callee site spells a program (`Total.Decode.plain`). -/
theorem not_spells_callee {b : Body} {u : Emitted} {s : Total.SourceProgram}
    (callee : b.site ≠ .loop) : ¬ Total.Spells (request b u) s := by
  rintro ⟨plain, -⟩
  cases site : b.site with
  | loop => exact callee site
  | callee | recursive =>
    simp only [Total.Decode.plain, request, site, siteCallee, Option.isNone_some, Bool.false_and]
      at plain
    cases plain

omit [FreshNames] in
/-- The production association holds today: no callee request spells a program. -/
theorem spelledBody (P : Source.SrcProg E) (c : Compilation) : SpelledBody P c :=
  fun _ _ _ _ _ _ _ _ _ _ _ calls spells => absurd spells (not_spells_callee (calls_callee calls))

/-- **The binding from the production association**, under `Sim.diagram.Total`. -/
theorem bodiesBound_of (total : diagram.Total) (P : Source.SrcProg E) (c : Compilation)
    (spelled : SpelledBody P c) : BodiesBound diagram P c := by
  intro d rb fn raw returnSlots scope before site u contract calls production accepted
  obtain ⟨b', same, m, assoc⟩ := total _ u production accepted
  have assoc : Assoc b' u m := assoc
  exact Assoc.rebind assoc same fun s spells _ =>
    spelled d rb fn raw returnSlots scope before site u s contract calls spells ▸
      reads_ofResolved rb raw returnSlots scope before (calls_callee calls)

/-- **The program-to-body binding** of the session lift, from `Sim.diagram.Total`. -/
theorem bodiesBound (total : diagram.Total) (P : Source.SrcProg E) (c : Compilation) :
    BodiesBound diagram P c :=
  bodiesBound_of total P c (spelledBody P c)

/-- With `Sim.Assoc` as it stands, `Sim.diagram.Total` leaves no fragment
production run at a callee site: the binding above has no instance yet. -/
theorem no_callee_run (total : diagram.Total) {b : Body} {u : Emitted} (callee : b.site ≠ .loop)
    (production : Production b u) (accepted : Accepted u) : False := by
  obtain ⟨b', same, m, assoc⟩ := total b u production accepted
  have assoc : Assoc b' u m := assoc
  obtain ⟨-, -, -, s, spells, -⟩ := assoc
  exact not_spells_callee (same.1 ▸ callee) spells

end Solidity.Correctness.Lowering.Sim.Session
