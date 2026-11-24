import Solidity.Correctness.Lowering.Sim.Match.CasesV2

/-!
# The statement-level relation, v2 (ls3v-p1-statement-v2, contract)

An additive prerequisite for `Solidity.Goals.loweringBySimulation`: where
`SiteSim₂` ties an elaborator output to a whole body, the relation for a part.
**Contract only**: the laws (`SeqLaw`, `RefinesLaw`, `MonoLaw`, `MapExt.Laws`,
`ChainAppendLaw`) are propositions, not theorems; only a bridge to
`Diagram.Final` is proved.

* The Source side of a part is resolved Source syntax (`Source.RItems`; user
  decision H1422, option B), run by `Source.execItems` (`SrcRun.ofItems`).
  Parts are sequenced by `append`.
* `SrcRun.Refines κ κ' c`: `κ'` has the result of `κ`, at most `c` horizon
  steps later, and completes nowhere else; `κ` is stable. It relates a
  statement to its hoisted form, and a body to its lowered items.
* `SegSim fuel a p m m'`: the run clauses of `RunSim₂` for the items `a` and a
  target part `p`, from the map `m` to a map `m'` on the contexts the part
  leaves. Normal completion keeps `frameRel`; `return`, `break` and `continue`
  match nothing (the parts of a lowered body are jump-free).
* `MapExt m emb m'`: over a base Source context that both maps' contexts
  extend, the base locals keep their target slots along the thinning.

## Limitations

* Captures and lowered statements must be given as Source items: nothing
  here produces them.
* Refinement costs horizon; that the parts' fuel fits `diagram.fuel` is not shown.
-/
namespace Solidity.Correctness.Lowering.Sim.StatementV2

open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)

/-- The result of a Source computation from `Γs` to `Δs`. -/
abbrev SrcRes (E : Source.Env) (Γs Δs : Source.RCtx) :=
  Except Source.Halt (Source.Out E.layout Γs Δs) × (Source.Locals E.layout [] × Source.St E)

/-- **A Source computation** from the locals `Γs` to the locals `Δs`. -/
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
    (a : Source.RItems E R M k Γs Δs) : SrcRun E Γs Δs :=
  fun G F n nps ph src => (Source.execItems G F n nps ph a src.1).run (.nil, src.2)

/-- A `return` read as normal completion, as `Diagram.Final` observes a body. -/
def settled (κ : SrcRun E Γs Γs) : SrcRun E Γs Γs :=
  fun G F n nps ph src =>
    match κ G F n nps ph src with
    | (.ok (.ret l), rest) => (.ok (.normal l), rest)
    | r => r

/-- **Refinement** within `c` horizon steps: where `κ` completes, `κ'` has the
same result `c` steps later; `κ` is stable under larger horizons; every
completed result of `κ'` is one of `κ`. -/
def Refines (κ κ' : SrcRun E Γs Δs) (c : Nat) : Prop :=
  ∀ G F nps ph src,
    (∀ n, (κ G F n nps ph src).1 ≠ .error .timeout →
      κ' G F (n + c) nps ph src = κ G F n nps ph src) ∧
    (∀ n n', n ≤ n' → (κ G F n nps ph src).1 ≠ .error .timeout →
      κ G F n' nps ph src = κ G F n nps ph src) ∧
    (∀ j, (κ' G F j nps ph src).1 ≠ .error .timeout →
      ∃ n, κ G F n nps ph src = κ' G F j nps ph src)

end SrcRun

/-- **Source sequence**: the items `a`, then the items `b`. -/
def append {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γs Γ₁ Δs : Source.RCtx} → Source.RItems E R M k Γs Γ₁ →
    Source.RItems E R M k Γ₁ Δs → Source.RItems E R M k Γs Δs
  | _, _, _, _, .nil, b => b
  | _, _, _, _, .stmt s rest, b => .stmt s (append rest b)
  | _, _, _, _, .unchecked inner rest, b => .unchecked inner (append rest b)

/-- **Final matching of a part**: normal completion under the output map, with
the global and frame relations; halts by `HaltMatch`; nothing else. -/
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
for the Source items `a` and the target part `p`, with `SegFinal` under the
output map `m'`, at the fuel transport `fuel`. -/
def SegSim (fuel : Nat → Nat) {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γs Δs : Source.RCtx} (a : Source.RItems E R M k Γs Δs)
    {C : Contract} {Γ Γ' : Ctx} (p : Prog C Γ Γ') (m : ContextMap Γs Γ)
    (m' : ContextMap Δs Γ') : Prop :=
  ∀ (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    (src : Source.EMState E Γs) (tgt : State C Γ),
    m.Related (fun τ v => diagram.valRel τ v) src.1 tgt.env → diagram.globRel src.2 tgt →
    frameRel G F tgt →
    (∀ n, (SrcRun.ofItems a G F n nps ph src).1 ≠ .error .timeout →
      SegFinal m' G F (SrcRun.ofItems a G F n nps ph src) (p.runF (fuel n) tgt)) ∧
    (∀ n n', n ≤ n' → (SrcRun.ofItems a G F n nps ph src).1 ≠ .error .timeout →
      SrcRun.ofItems a G F n' nps ph src = SrcRun.ofItems a G F n nps ph src) ∧
    (∀ n, p.runF n tgt ≠ .error .diverge →
      ∃ j, SegFinal m' G F (SrcRun.ofItems a G F j nps ph src) (p.runF n tgt))

/-- A local of the base context, under the locals `pre` pushed over it. -/
def liftIdx {base : Source.RCtx} {τ : Source.STy} :
    (pre : Source.RCtx) → Source.Idx base τ → Source.Idx (pre ++ base) τ
  | [], i => i
  | _ :: pre, i => .there (liftIdx pre i)

/-- **Declaration-context extension** over the base context `base`: `m` maps
the locals `pre ++ base` a part starts from, `m'` the locals `pre' ++ base` it
leaves; every base local has in `m'` its slot of `m`, weakened along `emb`. -/
def MapExt {base pre pre' : Source.RCtx} {Γ Γ' : Ctx} (m : ContextMap (pre ++ base) Γ)
    (emb : Thin Γ Γ') (m' : ContextMap (pre' ++ base) Γ') : Prop :=
  ∀ {τ : Source.STy} (i : Source.Idx base τ),
    m'.slot (liftIdx pre' i) = (m.wk emb).slot (liftIdx pre i)

/-- **Bridge**: where nothing is pushed over the base on either side, a
part's final matching under an extension of `m` is the diagram's final
matching, along the same thinning. -/
theorem SegFinal.final {E : Source.Env} {Γs : Source.RCtx} {C : Contract} {Γ Γ' : Ctx} {H : HTy}
    {m : ContextMap Γs Γ} {emb : Thin Γ Γ'} {m' : ContextMap Γs Γ'}
    (ext : MapExt (base := Γs) (pre := []) (pre' := []) m emb m')
    {G : Source.Glob E} {F : Source.Fr} {src : SrcRes E Γs Γs} {tgt : TRes (Out C H Γ')}
    (h : SegFinal m' G F src tgt) : diagram.Final m emb src tgt := by
  have same : m' = m.wk emb := ContextMap.ext _ _ fun i => ext i
  subst same
  obtain ⟨res, rest⟩ := src
  cases res with
  | error e => cases tgt <;> exact h
  | ok out => cases tgt with
    | error t => cases out <;> exact h.elim
    | ok o => cases out with
      | normal ls => exact ⟨h.1, h.2.1⟩
      | brk ls | cont ls | ret ls => exact h.elim

/-- **Sequencing**: parts compose along the intermediate map, at a monotone
fuel transport. -/
def SeqLaw : Prop :=
  ∀ (fuel : Nat → Nat) {E : Source.Env} {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    {Γs Γ₁ Δs : Source.RCtx} (a : Source.RItems E R M k Γs Γ₁) (b : Source.RItems E R M k Γ₁ Δs)
    {C : Contract} {Γ Γ' Γ'' : Ctx} (p₁ : Prog C Γ Γ') (p₂ : Prog C Γ' Γ'')
    (m : ContextMap Γs Γ) (m₁ : ContextMap Γ₁ Γ') (m₂ : ContextMap Δs Γ''),
    (∀ n n', n ≤ n' → fuel n ≤ fuel n') → SegSim fuel a p₁ m m₁ → SegSim fuel b p₂ m₁ m₂ →
    SegSim fuel (append a b) (p₁.join p₂) m m₂

/-- **Refinement transfers the relation** to the refined items, at the fuel
of the later horizon. -/
def RefinesLaw : Prop :=
  ∀ (fuel : Nat → Nat) (c : Nat) {E : Source.Env} {R R' : List Source.STy} {M M' : Bool}
    {k k' : Source.SCtx} {Γs Δs : Source.RCtx} (a : Source.RItems E R M k Γs Δs)
    (b : Source.RItems E R' M' k' Γs Δs) {C : Contract} {Γ Γ' : Ctx} (p : Prog C Γ Γ')
    (m : ContextMap Γs Γ) (m' : ContextMap Δs Γ'),
    (SrcRun.ofItems a).Refines (SrcRun.ofItems b) c → SegSim fuel b p m m' →
    SegSim (fun n => fuel (n + c)) a p m m'

/-- **More fuel keeps the relation.** -/
def MonoLaw : Prop :=
  ∀ (f g : Nat → Nat) {E : Source.Env} {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    {Γs Δs : Source.RCtx} (a : Source.RItems E R M k Γs Δs) {C : Contract} {Γ Γ' : Ctx}
    (p : Prog C Γ Γ') (m : ContextMap Γs Γ) (m' : ContextMap Δs Γ'),
    (∀ n, f n ≤ g n) → SegSim f a p m m' → SegSim g a p m m'

/-- **Context extension**: the identity; composition along the thinnings; a
target-only binder (a capture); a declared pair of locals. -/
def MapExt.Laws : Prop :=
  (∀ {base pre : Source.RCtx} {Γ : Ctx} (m : ContextMap (pre ++ base) Γ),
    MapExt (base := base) m .refl m) ∧
  (∀ {base pre₀ pre₁ pre₂ : Source.RCtx} {Γ Γ' Γ'' : Ctx} (m : ContextMap (pre₀ ++ base) Γ)
    (e₁ : Thin Γ Γ') (m₁ : ContextMap (pre₁ ++ base) Γ') (e₂ : Thin Γ' Γ'')
    (m₂ : ContextMap (pre₂ ++ base) Γ''),
    MapExt m e₁ m₁ → MapExt m₁ e₂ m₂ → MapExt m (e₁.trans e₂) m₂) ∧
  (∀ {base pre pre' : Source.RCtx} {Γ Γ' Γ'' : Ctx} (m : ContextMap (pre ++ base) Γ)
    (emb : Thin Γ Γ') (m' : ContextMap (pre' ++ base) Γ') (e : Thin Γ' Γ''),
    MapExt m emb m' → MapExt m (emb.trans e) (m'.wk e)) ∧
  (∀ {base pre pre' : Source.RCtx} {Γ Γ' : Ctx} (m : ContextMap (pre ++ base) Γ)
    (emb : Thin Γ Γ') (m' : ContextMap (pre' ++ base) Γ') (τ : Source.STy) (u : LTy),
    MapExt m emb m' →
      MapExt (pre' := τ :: pre') m (.drop emb (t := u)) (m'.cons τ u))

/-- **Block concatenation**: the placement of `P ++ Q` (`SProg.chain`) is the
placement of `P`, then of `Q` where `P` leaves, joined. -/
def ChainAppendLaw [FreshNames] : Prop :=
  ∀ {C : Contract} (ns : List Var) (Γ : Ctx) (P Q : SProg C) (b : Blk C Γ),
    SProg.chain ns Γ (P ++ Q) = .ok b ↔
      ∃ (Γ' : Ctx) (p : Prog C Γ Γ') (Γ'' : Ctx) (q : Prog C Γ' Γ''),
        SProg.chain ns Γ P = .ok ⟨Γ', p⟩ ∧ SProg.chain (p.outNames ns) Γ' Q = .ok ⟨Γ'', q⟩ ∧
        b = ⟨Γ'', p.join q⟩

end Solidity.Correctness.Lowering.Sim.StatementV2
