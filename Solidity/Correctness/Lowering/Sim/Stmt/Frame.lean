import Solidity.Correctness.Lowering.Sim.Match.Cases
import Solidity.Correctness.Lowering.Unchecked.SourceOne

/-!
# Statement cases: the frame obstruction

`RunSim` (`Sim/Match/Cases.lean`) quantifies its forward clause over every
Source record `G` and frame `F`, while the emitted program's run mentions
neither. So a body with `RunSim` completes or halts alike at every frame
(`RunSim.frame_blind`). A Source body that reads its frame does not:

* `one_not_runSim`: no body whose resolved statement is `x++`, `x--`,
  `x += 1` or `x -= 1` at an integer local (`Unchecked.SourceOneAssociation`)
  has `RunSim`, whatever was emitted for it. At the bound of the type the
  Source run panics in a checked frame and wraps in an unchecked one
  (`Unchecked.sourceOne_runV2`), and no target result matches both.

Consequence for `StmtCases`: its `incDec` and `opAssign` conjuncts hold only if
no production run in the fragment is associated with such a body, and
`Total.Spells` spells them (`Spells.Simple.incDec`, `.opAssign`). The same
reading applies to every family whose Source run evaluates checked
arithmetic (`Source.binVal F.checked`), writes the state (`Source.applyOp`
refuses in a static frame) or reads a state variable (`globRel` relates the
account of some address, the Source reads `F.this`). The frame is not a
parameter of `Diagram.Simulates`, so the repair is in the goal vocabulary
(`frameRel` of `Sim/Match/Relations.lean` as a premise of the forward clause).
-/

namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)
open Solidity.Correctness.Lowering.Unchecked (RawOneInput SourceOneAssociation sourceOne_runV2)

/-- A matched pair completes on both sides or halts on both. -/
theorem final_ok_iff {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ Γ' : Ctx} {H : HTy}
    {m : ContextMap srcΓ Γ} {emb : Thin Γ Γ'}
    {src : Except Source.Halt (Source.Out E.layout srcΓ srcΓ) ×
      (Source.Locals E.layout [] × Source.St E)}
    {tgt : TRes (Out C H Γ')} (h : diagram.Final m emb src tgt) :
    (∃ x, src.1 = .ok x) ↔ ∃ o, tgt = .ok o := by
  unfold Diagram.Final at h
  split at h <;> simp_all

/-- **A simulated body is blind to its frame**: under `RunSim`, at one Source
state and horizon, the Source run completes at every record and frame or
halts at every one (where it does not time out). -/
theorem RunSim.frame_blind {b : Body} {u : Emitted} {m : ContextMap b.ctx u.Γ}
    (sim : RunSim b u m) (G G' : Source.Glob b.E) (F F' : Source.Fr) (nps nps' : Nat)
    (ph ph' : Option (Source.Ph b.E)) (src : Source.EMState b.E b.ctx) (n : Nat)
    (done : (sourceRun b G F n nps ph src).1 ≠ .error .timeout)
    (done' : (sourceRun b G' F' n nps' ph' src).1 ≠ .error .timeout) :
    (∃ x, (sourceRun b G F n nps ph src).1 = .ok x) ↔
      ∃ x, (sourceRun b G' F' n nps' ph' src).1 = .ok x := by
  obtain ⟨_, initial, emb, runs⟩ := sim
  obtain ⟨tgt, related, glob⟩ := initial src
  exact (final_ok_iff ((runs G F nps ph src tgt related glob).1 n done)).trans
    (final_ok_iff ((runs G' F' nps' ph' src tgt related glob).1 n done')).symm

/-- A local reads what was set at its position. -/
theorem locals_get_set {D : Source.Layout} : {Γ : Source.RCtx} → {τ : Source.STy} →
    (ls : Source.Locals D Γ) → (i : Source.Idx Γ τ) → (v : Source.Val D τ) →
    (ls.set i v).get i = v
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ r, .there i, v => locals_get_set r i v

/-- **No simulation of a local increment.** A body whose resolved statement
is an increment, a decrement or a compound `± 1` of an integer local has
`RunSim` with no emitted program: with the local at the bound of its type,
the Source run at horizon `3` panics in a checked frame and completes in an
unchecked one. -/
theorem one_not_runSim {input : RawStmt} (context : Source.Ctx) (raw : RawOneInput input)
    {k : Source.SCtx}
    (statement : Source.RStmt context.env context.rets context.inModifier k context.tys context.tys)
    (certificate : SourceOneAssociation context raw statement) (raws : List RawStmt)
    (slots : Option (List String)) (scope : ElabScope)
    (before : Solidity.Correctness.Lowering.Checker.Snapshot) (site : Site) (u : Emitted)
    (m : ContextMap context.tys u.Γ) (G : Source.Glob context.env) (F : Source.Fr)
    (src : Source.EMState context.env context.tys) :
    ¬ RunSim ⟨context.env, context.rets, context.inModifier, k, context.tys,
      ⟨raws, statement, slots, scope, before⟩, site⟩ u m := by
  intro sim
  have bounds := certificate.type.wrap_mem 0
  let edge : Int := if raw.inc then certificate.type.hi else certificate.type.lo
  have inside : certificate.type.lo ≤ edge ∧ edge ≤ certificate.type.hi := by
    dsimp only [edge]; split <;> omega
  have outside : ¬ (certificate.type.lo ≤ (if raw.inc then edge + 1 else edge - 1) ∧
      (if raw.inc then edge + 1 else edge - 1) ≤ certificate.type.hi) := by
    dsimp only [edge]; split <;> omega
  let ls := src.1.set certificate.slot (.int edge inside)
  have value (checked : Bool) : Source.incDecVal checked raw.inc (ls.get certificate.slot) =
      Source.intRes certificate.type checked (if raw.inc then edge + 1 else edge - 1) := by
    rw [locals_get_set]; rfl
  have run (checked : Bool) := sourceOne_runV2 context raw statement certificate G
    { F with checked := checked } 3 0 none none true ls src.2
  simp only [value] at run
  have blind := sim.frame_blind G G { F with checked := true } { F with checked := false } 0 0
    none none (ls, src.2) 3
  simp only [sourceRun] at blind
  have checked := run true
  have unchecked := run false
  rw [Source.intRes_overflow _ _ outside] at checked
  simp only [Source.intRes, outside, dif_neg, not_false_eq_true] at unchecked
  erw [checked, unchecked] at blind
  simp [Source.panic, pure, Except.pure] at blind

end Solidity.Correctness.Lowering.Sim
