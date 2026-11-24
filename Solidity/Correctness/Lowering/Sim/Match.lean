import Solidity.Correctness.Lowering.Sim.Match.Relations

/-!
# The lowering diagram

`diagram : Shrink.Lowering.Diagram`, the candidate simulation for
`loweringBySimulation` (`Goals/LoweringSim.lean`), and what does not depend on
the producers' recursion: the three relation-only conjuncts of
`Diagram.Simulates` (`diagram_relations`), total initial matching
(`initial_matching`) and `caller_bound`. Neither `diagram.Simulates` nor
`diagram.Total` is proved here, and with the goal vocabulary as it stands
neither is provable for this value: see "Limitations".

## The association

`Assoc b u m` reads the body and the emitted program as a request of the
decoder vocabulary (`request`, `Total.Request`) and asks that

* the emitted program is placed in the caller's context under the caller's
  names;
* `m` is `Aligned`: positional, with a related model local for every Source
  local;
* the request spells a Source program (`Total.Spells`: the raw input spells a
  block typed in the canonical unit of the contract, from the caller's
  locals) which the body's resolved statement `Reads`: that statement itself
  at a standalone loop, the block of the program's items at a function body.

`Assoc` uses the spelling relation only; no decoder is written or run here.
It does not contain `Production`: both `Diagram.Simulates` and `Diagram.Total`
supply it, and the elaborator is `partial`, so no closed run has a kernel proof.

## Limitations

* **`diagram.Total` is not provable, even at standalone loops.** `Production`
  leaves `u.Γ` and `u.output.names` free (`Lowered` and `Threaded` mention
  neither; `SProg.chain` places under any names and context), while `Assoc`
  requires them to be the caller's, as the simulation needs. `Total` ranges
  over every such `u`. Closing this needs a goal-side change: `Production`
  (or `Threaded`) fixing `u.Γ` and `u.output.names` from the elaboration's
  locals, as `Checker.StateThreading` does.
* `Total.Spells` holds for plain requests only (`Total.Decode.plain`: no
  callee, no return slots, checked scope) in contracts the canonical unit
  covers (`Total.Decode.unit`: primitive state variables, no functions).
  A function body is in `Reads`, and `request` passes the callee to the
  decoder vocabulary, but until that vocabulary reads callee requests no
  callee or recursive site is associated.
* **The forward clause of `diagram.Simulates` is not provable as stated.**
  `Diagram.Simulates` quantifies over every Source frame, and `globRel` has no
  frame; see `frameRel`.
-/
namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap IntValueRel integerPrim)

/-- The callee of a site, in the decoder vocabulary: none at a standalone
loop, the declaration and its frame at an inlined or recursive callee. -/
def siteCallee : Site → Option Total.CalleeRequest
  | .loop => none
  | .callee d ρ ctor selfFrame Γf funs k₀ | .recursive d ρ ctor selfFrame Γf funs k₀ _ _ =>
    some ⟨d, ρ, ctor, selfFrame, Γf, funs, k₀⟩

/-- A body and the contract of an emitted program as a request of the
decoder vocabulary, under the production fresh-name policy. -/
def request (b : Body) (u : Emitted) : Total.Request :=
  ⟨u.C, ⟨productionNames, b.input.returnSlots, b.input.raw, b.input.scope, b.input.before⟩,
    siteCallee b.site⟩

/-- The body's resolved statement is the Source program: the statement itself
at a standalone loop (its raw input is that one statement), the block of the
program's items at a function body (its raw input is the declared body). -/
def Reads (b : Body) (s : Total.SourceProgram) : Prop :=
  match b.site with
  | .loop => s = .ofStmt b.input.resolved
  | _ => ∃ (Δ : Source.RCtx) (items : Source.RItems b.E b.returns b.modifier b.control b.ctx Δ),
      b.input.resolved = .block items ∧ s = ⟨_, _, _, _, _, _, items⟩

theorem Reads.env {b : Body} {s : Total.SourceProgram} (h : Reads b s) : s.env = b.E := by
  unfold Reads at h
  split at h
  · rw [h]; rfl
  · obtain ⟨_, _, _, rfl⟩ := h; rfl

/-- **The association** of a resolved Source body with an emitted program
under a context map. -/
def Assoc (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ) : Prop :=
  u.Γ = (request b u).context.ctx ∧ u.output.names = (request b u).context.names ∧
  Aligned m ∧ ∃ s, Total.Spells (request b u) s ∧ Reads b s

/-- **The diagram.** A model loop runs as many iterations as its Source
loop, or one more for a lowered first pass, and a Source horizon bounds the
iterations of every loop it completes; the transport is generous, since more
model fuel never changes a completed run (`Prog.runF_approx`). -/
def diagram : Diagram where
  fuel n := 2 * n + 2
  Assoc := Assoc
  valRel := valRel
  globRel := globRel

/-- **The relation-only conjuncts of `Diagram.Simulates`**: Boolean
reflection, integer reflection and a monotone transport. -/
theorem diagram_relations :
    (∀ {Dl : Source.Layout} {C : Contract} {H : HTy} (v : Source.Val Dl .bool) (b : Bool),
      diagram.valRel (C := C) (H := H) .bool (.val .bool) v b → v = .bool b) ∧
    (∀ {Dl : Source.Layout} {C : Contract} {H : HTy} (t : Source.IntTy)
      (v : Source.Val Dl (.int t)) (x : (integerPrim t).Denote),
      diagram.valRel (C := C) (H := H) (.int t) (.val (integerPrim t)) v x → IntValueRel t v x) ∧
    (∀ n n', n ≤ n' → diagram.fuel n ≤ diagram.fuel n') :=
  ⟨@fun _ C H v b h => valRel_bool (C := C) (H := H) v b h,
    @fun _ C H t v x h => valRel_int (C := C) (H := H) t v x h,
    fun _ _ h => Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 2⟩

/-- An associated body's environment types the contract's storage. -/
theorem Assoc.storageTyped {b : Body} {u : Emitted} {m : ContextMap b.ctx u.Γ}
    (h : Assoc b u m) : StorageTyped b.E u.C := by
  obtain ⟨_, _, _, s, ⟨_, Cx, L, t, L', d, hC, _, _, rfl⟩, reads⟩ := h
  have hE : Cx.env = b.E := reads.env
  change Total.Decode.context (request b u) = some Cx at hC
  simp only [Total.Decode.context, Option.map_eq_some_iff] at hC
  obtain ⟨un, hu, rfl⟩ := hC
  have hu' := hu
  unfold Total.Decode.unit at hu'
  split at hu'
  · simp only [Option.map_eq_some_iff] at hu'
    obtain ⟨parts, hparts, _⟩ := hu'
    intro x T mem
    obtain ⟨p, rfl⟩ := Total.Simulation.stateVars_prim _ _ hparts x T mem
    exact ⟨p, rfl, hE ▸ Total.Decode.unit_cellTy hu
      (Total.Simulation.lookup_of_mem _ u.C.vars_nodup x _ mem)⟩
  · cases hu'

/-- **Total initial matching** (the second obligation of `Diagram.Simulates`):
every Source state of an associated body has a related model state, so neither
relation of the diagram is empty there. -/
theorem initial_matching (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ)
    (h : diagram.Assoc b u m) (src : Source.EMState b.E b.ctx) :
    ∃ tgt : State u.C u.Γ,
      m.Related (fun τ v => diagram.valRel τ v) src.1 tgt.env ∧ diagram.globRel src.2 tgt := by
  have h : Assoc b u m := h
  obtain ⟨env, related⟩ := h.2.2.1.locals b.E.layout u.C [] src.1
  obtain ⟨storage, funds, glob⟩ := globRel_total h.storageTyped src.2 env
  exact ⟨_, related, glob⟩

/-- **The callers are bound**: `calleeBody` is renaming, then `lowerAt` into
the return slots, then `callerTail`; for every fresh-name policy, so for the
production one. -/
theorem caller_bound [FreshNames] : CallerBound := by
  intro C d ρ ctor selfFrame Γf
  simp only [calleeBody, lowerAt, callerTail, returnSlots, bind_assoc]

end Solidity.Correctness.Lowering.Sim
