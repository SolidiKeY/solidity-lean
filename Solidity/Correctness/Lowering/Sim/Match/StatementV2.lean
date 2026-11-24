import Solidity.Correctness.Lowering.Sim.Match.CasesV2

/-!
# The statement-level relation, v2 (ls3v-p1-statement-v2, contract)

An additive prerequisite for `Solidity.Goals.loweringBySimulation`. The v1
and v2 site obligations (`SiteSim`, `SiteSim₂`) tie an elaborator output to a
whole body, so they say nothing of captures followed by a statement, of a
block's concatenation or of a declaration extending the context
(`Sim/Match/CasesV2.lean`). This module states the relation for a part.

**Contract only: unreviewed.** The definitions are the proposal; the
composition laws are stated as propositions (`SeqLaw`, `RefinesLaw`,
`MapExt.Laws`, `ChainAppendLaw`), not proved. Only bridges that do not depend
on the choice are proved.

* `SrcRun E Γs Δs`: a horizon-indexed Source computation, the Source side of
  a part. A semantic object, not Source syntax: a capture and a lowered
  statement have no resolved Source statement. `SrcRun.ofStmt`,
  `SrcRun.ofItems` read the Source syntax; `seq` composes at one horizon;
  `settled` reads a `return` as normal completion (a body's last outcome).
* `SrcRun.Refines κ κ'`: `κ'` completes with the result of `κ` wherever `κ`
  completes, completes nowhere else, and `κ` is stable.
* `SegFinal`, `SegSim fuel κ p m m'`: the three run clauses of `RunSim₂` for a
  target part `p : Prog C Γ Γ'`, from the map `m` to an output map `m'` on the
  part's output contexts. Normal completion keeps `frameRel` (the intermediate
  state is aligned for the next part); a `return`, `break` or `continue`
  matches nothing (parts of a lowered body are jump-free).
* `MapExt m emb m'`: the output map, with the Source scope restored, is the
  input map weakened along the target thinning.

## Limitations

* Nothing here produces a `SrcRun` for raw input; `CompositionV2.lean`
  takes that reading as a parameter.
* The fuel transport is a parameter of `SegSim`; that `diagram.fuel` suits
  every part is not shown.
-/
namespace Solidity.Correctness.Lowering.Sim.StatementV2

open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)

/-! ## Source computations -/

/-- The result of a Source computation from `Γs` to `Δs`. -/
abbrev SrcRes (E : Source.Env) (Γs Δs : Source.RCtx) :=
  Except Source.Halt (Source.Out E.layout Γs Δs) × (Source.Locals E.layout [] × Source.St E)

/-- **A Source computation** from the locals `Γs` to the locals `Δs`: its
result at every record, frame, horizon, parameter count, placeholder and state. -/
abbrev SrcRun (E : Source.Env) (Γs Δs : Source.RCtx) :=
  Source.Glob E → Source.Fr → Nat → Nat → Option (Source.Ph E) → Source.EMState E Γs →
    SrcRes E Γs Δs

namespace SrcRun

variable {E : Source.Env} {Γs Γ₁ Δs : Source.RCtx}

/-- The run of a resolved statement. -/
def ofStmt {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (s : Source.RStmt E R M k Γs Δs) : SrcRun E Γs Δs :=
  fun G F n nps ph src => (Source.execS G F n nps ph s src.1).run (.nil, src.2)

/-- The run of resolved items. -/
def ofItems {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (b : Source.RItems E R M k Γs Δs) : SrcRun E Γs Δs :=
  fun G F n nps ph src => (Source.execItems G F n nps ph b src.1).run (.nil, src.2)

/-- The empty computation. -/
def skip : SrcRun E Γs Γs := fun _ _ _ _ _ src => (.ok (.normal src.1), .nil, src.2)

/-- **Sequence**, both parts at the same horizon: the second from the normal
outcome of the first, its outcome moved to the first's input context
(`Source.Out.up`, as `Source.execItems`); any other outcome of the first ends it. -/
def seq (κ₁ : SrcRun E Γs Γ₁) (κ₂ : SrcRun E Γ₁ Δs) : SrcRun E Γs Δs :=
  fun G F n nps ph src =>
    match κ₁ G F n nps ph src with
    | (.ok (.normal l), _, st) =>
      match κ₂ G F n nps ph (l, st) with
      | (.ok o, rest) => (o.up Γs, rest)
      | (.error h, rest) => (.error h, rest)
    | (.ok (.brk l), rest) => (.ok (.brk l), rest)
    | (.ok (.cont l), rest) => (.ok (.cont l), rest)
    | (.ok (.ret l), rest) => (.ok (.ret l), rest)
    | (.error h, rest) => (.error h, rest)

/-- A `return` read as normal completion: what `Diagram.Final` observes of a
body, whose `return`s the production lowering turns into slot writes. -/
def settled (κ : SrcRun E Γs Γs) : SrcRun E Γs Γs :=
  fun G F n nps ph src =>
    match κ G F n nps ph src with
    | (.ok (.ret l), rest) => (.ok (.normal l), rest)
    | r => r

/-- **Refinement**: at every horizon at which `κ` completes, `κ'` has the same
result; `κ` is stable under larger horizons; every completed result of `κ'` is
one of `κ`. -/
def Refines (κ κ' : SrcRun E Γs Δs) : Prop :=
  ∀ G F nps ph src,
    (∀ n, (κ G F n nps ph src).1 ≠ .error .timeout →
      κ' G F n nps ph src = κ G F n nps ph src) ∧
    (∀ n n', n ≤ n' → (κ G F n nps ph src).1 ≠ .error .timeout →
      κ G F n' nps ph src = κ G F n nps ph src) ∧
    (∀ j, (κ' G F j nps ph src).1 ≠ .error .timeout →
      ∃ n, κ G F n nps ph src = κ' G F j nps ph src)

end SrcRun

/-- **Bridge**: the Source run of a body (`sourceRun`) is the run of its
resolved statement. -/
theorem sourceRun_eq (b : Body) (G : Source.Glob b.E) (F : Source.Fr) (n nps : Nat)
    (ph : Option (Source.Ph b.E)) (src : Source.EMState b.E b.ctx) :
    sourceRun b G F n nps ph src = SrcRun.ofStmt b.input.resolved G F n nps ph src := rfl

/-! ## The relation -/

/-- **Final matching of a part**: normal completion reaches a target state
related under the output map, with the global and frame relations; halts
correspond (`HaltMatch`); nothing else matches. -/
def SegFinal {E : Source.Env} {Γs Δs : Source.RCtx} {C : Contract} {Γ' : Ctx} {H : HTy}
    (m' : ContextMap Δs Γ') (G : Source.Glob E) (F : Source.Fr) (src : SrcRes E Γs Δs)
    (tgt : TRes (Out C H Γ')) : Prop :=
  match src.1, tgt with
  | .ok (.normal ls), .ok o =>
    m'.Related (fun τ u => diagram.valRel τ u) ls o.st.env ∧ diagram.globRel src.2.2 o.st ∧
      frameRel G F o.st
  | .error h, .error t => HaltMatch h t
  | _, _ => False

/-- **The statement-level relation**: from Source and target states related
under `m`, with the global and frame relations, the run clauses of `RunSim₂`
for the Source computation `κ` and the target part `p`, with `SegFinal` under
the output map `m'`, at the fuel transport `fuel`. -/
def SegSim (fuel : Nat → Nat) {E : Source.Env} {Γs Δs : Source.RCtx} (κ : SrcRun E Γs Δs)
    {C : Contract} {Γ Γ' : Ctx} (p : Prog C Γ Γ') (m : ContextMap Γs Γ)
    (m' : ContextMap Δs Γ') : Prop :=
  ∀ (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    (src : Source.EMState E Γs) (tgt : State C Γ),
    m.Related (fun τ v => diagram.valRel τ v) src.1 tgt.env → diagram.globRel src.2 tgt →
    frameRel G F tgt →
    (∀ n, (κ G F n nps ph src).1 ≠ .error .timeout →
      SegFinal m' G F (κ G F n nps ph src) (p.runF (fuel n) tgt)) ∧
    (∀ n n', n ≤ n' → (κ G F n nps ph src).1 ≠ .error .timeout →
      κ G F n' nps ph src = κ G F n nps ph src) ∧
    (∀ n, p.runF n tgt ≠ .error .diverge →
      ∃ j, SegFinal m' G F (κ G F j nps ph src) (p.runF n tgt))

/-- **Declaration-context extension**: `m'` maps the locals a part leaves
(Source `Δs`, target `Γ'`); with the Source scope restored to `Γs`, values
related under `m'` are related under `m` weakened along `emb`. -/
def MapExt {Γs Δs : Source.RCtx} {Γ Γ' : Ctx} (m : ContextMap Γs Γ) (emb : Thin Γ Γ')
    (m' : ContextMap Δs Γ') : Prop :=
  ∀ {D : Source.Layout} {C : Contract} {H : HTy}
    (R : (τ : Source.STy) → (u : LTy) → Source.Val D τ → u.TDenote C H → Prop)
    (ls : Source.Locals D Δs) (ls₀ : Source.Locals D Γs) (env : TEnv C H Γ'),
    ls.restore Γs = .ok ls₀ → m'.Related R ls env → (m.wk emb).Related R ls₀ env

/-- **Bridge**: where the Source context is unchanged and restoring is the
identity, a part's final matching under an extension of `m` is the diagram's
final matching of the settled result, along the same thinning. -/
theorem SegFinal.final {E : Source.Env} {Γs : Source.RCtx} {C : Contract} {Γ Γ' : Ctx} {H : HTy}
    {m : ContextMap Γs Γ} {emb : Thin Γ Γ'} {m' : ContextMap Γs Γ'} (ext : MapExt m emb m')
    (same : ∀ ls : Source.Locals E.layout Γs, ls.restore Γs = .ok ls)
    {G : Source.Glob E} {F : Source.Fr} {src : SrcRes E Γs Γs} {tgt : TRes (Out C H Γ')}
    (h : SegFinal m' G F src tgt) : diagram.Final m emb src tgt := by
  obtain ⟨res, rest⟩ := src
  cases res with
  | error e => cases tgt with
    | error t => exact h
    | ok o => exact h
  | ok out => cases tgt with
    | error t => cases out <;> exact h.elim
    | ok o => cases out with
      | normal ls => exact ⟨ext _ ls ls o.st.env (same ls) h.1, h.2.1⟩
      | brk ls | cont ls | ret ls => exact h.elim

/-! ## Laws (statements; proved after review) -/

/-- **Sequencing**: parts compose along the intermediate map. -/
def SeqLaw : Prop :=
  ∀ (fuel : Nat → Nat) {E : Source.Env} {Γs Γ₁ Δs : Source.RCtx} (κ₁ : SrcRun E Γs Γ₁)
    (κ₂ : SrcRun E Γ₁ Δs) {C : Contract} {Γ Γ' Γ'' : Ctx} (p₁ : Prog C Γ Γ')
    (p₂ : Prog C Γ' Γ'') (m : ContextMap Γs Γ) (m₁ : ContextMap Γ₁ Γ') (m₂ : ContextMap Δs Γ''),
    SegSim fuel κ₁ p₁ m m₁ → SegSim fuel κ₂ p₂ m₁ m₂ →
    SegSim fuel (κ₁.seq κ₂) (p₁.join p₂) m m₂

/-- **Refinement transfers the relation** to the refined computation. -/
def RefinesLaw : Prop :=
  ∀ (fuel : Nat → Nat) {E : Source.Env} {Γs Δs : Source.RCtx} (κ κ' : SrcRun E Γs Δs)
    {C : Contract} {Γ Γ' : Ctx} (p : Prog C Γ Γ') (m : ContextMap Γs Γ) (m' : ContextMap Δs Γ'),
    κ.Refines κ' → SegSim fuel κ' p m m' → SegSim fuel κ p m m'

/-- **Source blocks are sequences**: the items `s; rest` refine the sequence
of their runs (the block spends one horizon step more). -/
def ItemsLaw : Prop :=
  ∀ {E : Source.Env} {R : List Source.STy} {M : Bool} {k : Source.SCtx} {Γs Γ₁ Δs : Source.RCtx}
    (s : Source.RStmt E R M k Γs Γ₁) (rest : Source.RItems E R M k Γ₁ Δs),
    (SrcRun.ofItems (.stmt s rest)).Refines ((SrcRun.ofStmt s).seq (SrcRun.ofItems rest))

/-- **Context extension**: the identity, composition along the thinnings, a
target-only binder (a capture) and a declared pair of locals. -/
def MapExt.Laws : Prop :=
  (∀ {Γs : Source.RCtx} {Γ : Ctx} (m : ContextMap Γs Γ), MapExt m .refl m) ∧
  (∀ {Γs Γ₁ Δs : Source.RCtx} {Γ Γ' Γ'' : Ctx} (m : ContextMap Γs Γ) (e₁ : Thin Γ Γ')
    (m₁ : ContextMap Γ₁ Γ') (e₂ : Thin Γ' Γ'') (m₂ : ContextMap Δs Γ''),
    (∃ pre, Γ₁ = pre ++ Γs) → (∃ pre, Δs = pre ++ Γ₁) →
    MapExt m e₁ m₁ → MapExt m₁ e₂ m₂ → MapExt m (e₁.trans e₂) m₂) ∧
  (∀ {Γs Δs : Source.RCtx} {Γ Γ' Γ'' : Ctx} (m : ContextMap Γs Γ) (emb : Thin Γ Γ')
    (m' : ContextMap Δs Γ') (e : Thin Γ' Γ''),
    MapExt m emb m' → MapExt m (emb.trans e) (m'.wk e)) ∧
  (∀ {Γs Δs : Source.RCtx} {Γ Γ' : Ctx} (m : ContextMap Γs Γ) (emb : Thin Γ Γ')
    (m' : ContextMap Δs Γ') (τ : Source.STy) (u : LTy),
    (∃ pre, Δs = pre ++ Γs) → MapExt m emb m' → MapExt m (.drop emb) (m'.cons τ u))

/-- **Block concatenation**: the placement of `P ++ Q` (`SProg.chain`) is the
placement of `P`, then of `Q` where `P` leaves, joined. -/
def ChainAppendLaw [FreshNames] : Prop :=
  ∀ {C : Contract} (ns : List Var) (Γ : Ctx) (P Q : SProg C) (b : Blk C Γ),
    SProg.chain ns Γ (P ++ Q) = .ok b ↔
      ∃ (Γ' : Ctx) (p : Prog C Γ Γ') (Γ'' : Ctx) (q : Prog C Γ' Γ''),
        SProg.chain ns Γ P = .ok ⟨Γ', p⟩ ∧ SProg.chain (p.outNames ns) Γ' Q = .ok ⟨Γ'', q⟩ ∧
        b = ⟨Γ'', p.join q⟩

end Solidity.Correctness.Lowering.Sim.StatementV2
