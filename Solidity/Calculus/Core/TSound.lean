import Solidity.Calculus.Core.TSoundStep
import Solidity.Calculus.Core.TSoundCalls
import Solidity.Calculus.Core.TSoundLoops

/-!
# Every rule of `Stmt.step` over the typed state

The arms (`Stmt.tstepSound_arms`, `Calculus/Core/TSoundStep.lean`) and the
blocks' (`Stmt.tsound_call`, `Stmt.tsound_tryCall`, `Stmt.tsound_loop`),
assembled: `Stmt.tstepSound`, every rule sound in every typed state where
its statement meets `Stmt.TArmOk`.

Decisions 15 and 16 took two conditions away (a push at the bound is
exhausted, which both modalities accept; no struct repeats a member name).
One is left, and decision 17 could not take it (`docs/intrinsic.md`,
"Decisions 15–17, implemented"): `T memory mv = r;` at an allocating `r`
under the box, in a heap with no object of the local's type.  The rule's
premise `∀ mv. [mv = r; ω] φ` is vacuous there, and no typed reading of the
binder makes it say what the conclusion needs: the instance that does is
the reference `r` is about to allocate, a dangling one, which a typed state
cannot hold (M3's untyped binder takes it).  So `Stmt.TSound C` is reduced
to exactly that arm in those states (`Stmt.TResidual`): under the diamond
it holds outright (`Stmt.tsound_diamond`), and `Proves.tvalid_of_residual`
is `Proves.tvalid` given it.  The residual is false (`Stmt.not_tresidual`:
`[uint[] memory m = new uint[](1);] false` from an empty heap), so
`Stmt.TSound` is too (`Stmt.not_tsound`), and `Proves.tvalid` waits on a
typed reading that can name an object not yet allocated.
-/

namespace Solidity.Core

open Solidity (Modality RuleSet)

variable {C : Contract}

/-- **Every rule of `Stmt.step` is sound over the typed state**, where the
statement meets its arm's condition (`Stmt.TArmOk`: only the box
`memoryLocalDeclInitDrop` at an allocating initializer asks one). -/
theorem Stmt.tstepSound (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') :
    Stmt.TStepSound k m s := by
  intro σ p hp hok
  cases s with
  | call f args ret body => exact Stmt.tsound_call k m f args ret body σ p hp
  | tryCall call rets ok err code pnc other =>
    exact Stmt.tsound_tryCall k m call rets ok err code pnc other σ p hp
  | loop a c body => exact Stmt.tsound_loop k m a c body σ p hp
  | _ => exact Stmt.tstepSound_arms k m _ rfl σ p hp hok

/-- An arm's condition holds under the diamond. -/
theorem Stmt.tarmOk_diamond {Γ Γ' : Ctx} (σ : TState C Γ) (s : Stmt C Γ Γ') :
    s.TArmOk .diamond σ := by
  cases s with
  | declMem R x init hd hm =>
    cases init with
    | none => trivial
    | some r => cases r <;> first | trivial | exact nofun
  | _ => trivial

/-- **Every rule is sound under the diamond**, in every typed state. -/
theorem Stmt.tsound_diamond (k : Nat) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (p : Premise C Γ Γ')
    (hp : s.step k .diamond = some p) (σ : TState C Γ) : Premise.TSound .diamond s p σ :=
  Stmt.tstepSound k .diamond s σ p hp (Stmt.tarmOk_diamond σ s)

/-- **What `Stmt.TSound C` asks beyond the arms**: each rule sound in the
states where its statement fails its arm's condition, which is only the box
`memoryLocalDeclInitDrop` at an allocating initializer, over a heap with no
object of the local's type. -/
def Stmt.TResidual (C : Contract) : Prop :=
  ∀ (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (p : Premise C Γ Γ'),
    s.step k m = some p → ∀ σ : TState C Γ, ¬ s.TArmOk m σ → Premise.TSound m s p σ

/-- `Stmt.TSound C` is the residual arm. -/
theorem Stmt.tsound_iff_residual : Stmt.TSound C ↔ Stmt.TResidual C := by
  constructor
  · intro h k m _ _ s p hp σ _
    exact h k m s p hp σ
  · intro h k m _ _ s p hp σ
    by_cases hok : s.TArmOk m σ
    · exact Stmt.tstepSound k m s σ p hp hok
    · exact h k m s p hp σ hok

/-- **A goal proved with an empty context is valid over the typed state**,
given the residual arm. -/
theorem Proves.tvalid_of_residual (h : Stmt.TResidual C) {R : RuleSet} {φ : Fml C []}
    (d : Proves C R [] .nil φ) : TValid φ :=
  Proves.tvalid (Stmt.tsound_iff_residual.2 h) d

/-- **The residual is false**, so it is a gap in the typed reading, not in
the proof: `[uint[] memory m = new uint[](1);] false` fails from a state with
an empty heap, where `memoryLocalDeclInitDrop`'s premise
`∀ m. [m = new uint[](1);] false` holds, its binder having no value. -/
theorem Stmt.not_tresidual : ¬ Stmt.TResidual StandardExample := by
  intro h
  let s : Stmt StandardExample [] [.mem (.array .uint)] :=
    .declMem (.array .uint) (.user "m") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl
  have hempty : ∀ v : (LTy.mem (.array .uint)).TDenote StandardExample
      (TState.init StandardExample).H, False := fun v => by
    have := v.get?
    simp only [TState.init, List.getElem?_nil, reduceCtorEq] at this
  have hc := h 0 .box s _ rfl (TState.init StandardExample) (fun hok => (hok rfl).elim hempty)
    (Prog.nil : Prog StandardExample _ _) .nil (.not .tt) (fun v => (hempty v).elim)
  have hok : (Prog.trunFrames (TState.init StandardExample) (.cons s .nil) .nil).halt? = none := by
    decide +kernel
  obtain ⟨h₁, _⟩ := hc
  revert h₁ hok
  cases Prog.trunFrames (TState.init StandardExample) (.cons s .nil) .nil with
  | ok _ => exact fun _ h₁ => h₁ trivial
  | error _ => exact fun h _ => nomatch h

/-- So `Stmt.TSound` is false: `Proves.tvalid`'s hypothesis cannot be met
until the typed reading changes (decision 17). -/
theorem Stmt.not_tsound : ¬ Stmt.TSound StandardExample :=
  fun h => Stmt.not_tresidual (Stmt.tsound_iff_residual.1 h)

end Solidity.Core
