import Solidity.Kernel.Logic

/-!
# The symbolic executor

`Kont.vc n H k` runs the calculus: at each modality it takes the rule
`Stmt.step` picks, and what is left are the goals no rule decides — a
postcondition under the hypotheses the run collected, a branch the
hypotheses rule out, a diamond condition's definedness.  `Kont.vc_sound`
turns a proof of them into a derivation of `Proves`, so a program is proved
by stating the goals it leaves and discharging them.

`n` is fuel, one unit per rule application; the termination measure
(`Taclet.smaller`) says a program's size is enough for its own statements.
-/

namespace Solidity
namespace Kernel

open Semantics

variable {C : Contract}

/-- The goals `H ⊢ k` leaves once every statement is run, with `n` rule
applications to spend (`False` when they run out).  `ψ` under `H` is a goal;
a `revert` under a box closes as far as `H` allows, and under a diamond only
where `H` is false. -/
def Kont.vc : Nat → {Γ₀ Γ : Ctx} → Hyps C Γ₀ Γ → Kont C Γ → Prop
  | 0, _, _, _, _ => False
  | _ + 1, _, _, H, .post ψ => ∀ σ, H.holds ψ.holds σ
  | n + 1, _, _, H, .up h k => Kont.vc n (H.shrink h) k
  | n + 1, _, _, H, .modal m P k =>
    match P with
    | .nil => Kont.vc n H k
    | .cons s ω =>
      match (s.step m).1 with
      | .update U => Kont.vc n (H.upd m U) (.modal m ω k)
      | .unfold _ P h => Kont.vc n H (.modal m P (.up h (.modal m ω k)))
      | .split c P Q =>
        Kont.vc n (H.cond c true) (.modal m (P.append ω) k) ∧
        Kont.vc n (H.cond c false) (.modal m (Q.append ω) k) ∧
        (m = .diamond → ∀ σ, H.holds (Post.defined c).holds σ)
      | .done b => ∀ σ, H.holds (fun _ => b = true) σ

/-- **The executor is sound**: the goals it leaves prove the continuation.
`⟨ uint x = 1; ⟩ x == 1` follows from `{x := 1} x == 1`. -/
theorem Kont.vc_sound : (n : Nat) → {Γ₀ Γ : Ctx} → (H : Hyps C Γ₀ Γ) → (k : Kont C Γ) →
    k.vc n H → Proves H k
  | 0, _, _, _, _, h => h.elim
  | _ + 1, _, _, _, .post _, h => .close h
  | n + 1, _, _, _, .up _ k, h => .up (Kont.vc_sound n _ k h)
  | n + 1, _, _, H, .modal m P k, h => by
    cases P with
    | nil => exact .empty (Kont.vc_sound n H k h)
    | cons s ω =>
      simp only [Kont.vc] at h
      have d := (s.step m).2
      revert h d
      generalize (s.step m).1 = pr
      intro h d
      cases pr with
      | update U => exact .update d (Kont.vc_sound n _ _ h)
      | unfold ns P h' => exact .unfold d (Kont.vc_sound n _ _ h)
      | split c P Q =>
        exact .split d (Kont.vc_sound n _ _ h.1) (Kont.vc_sound n _ _ h.2.1)
          (fun hm => .close (h.2.2 hm))
      | done b =>
        cases b with
        | true => exact .done d (.close fun σ => Hyps.mono (fun _ _ => trivial) _ σ (h σ))
        | false => exact .absurd fun σ => Hyps.mono (fun _ h => Bool.false_ne_true h) _ σ (h σ)

/-- **A proved program runs correctly**: if the executor's goals for
`⟨ P ⟩ ψ` hold from the precondition `φ`, then from every state satisfying
`φ`, `P` ends normally in a state satisfying `ψ`; for `[ P ] ψ`, it may also
fail.  Stated over the untyped interpreter, `execBlock`: from a state whose
storage is `alice.age = 0`, `alice.age = 10; assert(alice.age == 10);`
does not revert. -/
theorem Prog.correct {Γ Γ' : Ctx} (m : Modality) (P : Prog C Γ Γ') (ψ : Post C Γ') (n : Nat)
    (φ : State → Prop) (h : (Kont.modal m P (.post ψ)).vc n (.assume φ)) (σ : State) (hσ : φ σ) :
    after m (execBlock σ P.erase) ψ.holds := by
  rw [Prog.run_eq]; exact (Kont.vc_sound n _ _ h).sound σ hσ

/-! ## Tactics -/

open Lean Meta Simp in
/-- A scratch name at a closed context is a string: `freshName C [se] "se"`
is `"se1"`.  Evaluated, then checked by the kernel by reduction. -/
dsimproc reduceFreshName (freshName _ _ _) := fun e => do
  unless e.isAppOfArity ``freshName 3 do return .continue
  if e.hasFVar || e.hasMVar then return .continue
  let s ← unsafe evalExpr String (mkConst ``String) e
  return .done (toExpr s)

/-- `symex`: run the executor on a goal `k.vc n H`, stepping through every
statement and splitting every branch, until what is left are the goals
`∀ σ, H.holds ψ σ` (or `False`, when the fuel runs out). -/
macro "symex" : tactic => `(tactic| repeat' (first
  | (rw [Kont.vc]; try simp only [Stmt.step, localStep, assignStep, rebindStep, deleteStep,
      binopRightStep, shortCircuitStep, copyStep, Hole.unfoldStep, Prog.append, Val.weaken,
      Simple.weaken, Loc.weaken, SPath.weaken, Src.weaken, Val.isSimple, SPath.isSimple,
      SPath.isBindable, dite_true, dite_false, Bool.false_eq_true, reduceFreshName])
  | constructor))

/-- `symex_close [lemmas]`: discharge a goal `symex` leaves by evaluating the
hypotheses' updates and conditions, the precondition's facts among them;
`lemmas` unfold what the precondition names (a contract's initial
storage). -/
syntax "symex_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| symex_close) => `(tactic| symex_close [])
  | `(tactic| symex_close [$args,*]) =>
    `(tactic| (simp only [Hyps.holds]; intros; simp_all [Upd.apply, after, Val.eval, Simple.eval,
      PrimTy.defaultSimple, Post.holds, Post.defined, getEnv_setEnv_ne, bind, Except.bind, pure,
      Except.pure, applyBinOp, applyUnOp, unopCheck, checkArith, BinOp.retTy, Value.asInt,
      Value.asBool, Value.toSVal, BinOp.isArith, uintBound, intBound, reduceFreshName, Src.value,
      Loc.target, Loc.resolve, SPath.resolve, Simple.new, envPath, State.saveStorage,
      State.findStorage, State.setEnv, State.getEnv, SVal.save, SVal.find, SVal.asValue,
      SVal.defaultOf, defaultForRef, defaultForTy, defaultForFields, structDef, Functor.map,
      Except.map, lookupBy, setBy, SemanticsProperties.lookupBy_setBy_self,
      SemanticsProperties.lookupBy_setBy_ne, $args,*]))

/-! ## Examples

A specification is a diamond ending in `assert`s: `⟨ P; assert(c); ⟩ true`
says `P` does not fail and ends where `c` holds. -/

section Examples

local instance : InContract := ⟨StandardExample⟩

def exAdd := ksol{ uint x = 1; x = x + 2; assert(x == 3); }
def exIf := ksol{ uint x = 1; if (x == 1) { x = 2; } else { x = 3; }; assert(x == 2); }
def exStore := ksol{ alice.age = 10; assert(alice.age == 10); }
def exBad := ksol{ uint x = 1; x = x + 2; assert(x == 4); }

example : (Kont.modal .diamond exAdd (.post .tt)).vc 30 .nil := by
  unfold exAdd; symex <;> symex_close

/-- Both branches run; the `else` one is ruled out by its condition. -/
example : (Kont.modal .diamond exIf (.post .tt)).vc 60 .nil := by
  unfold exIf; symex <;> symex_close

/-- From the initial storage, and no locals, `alice.age = 10;` makes
`alice.age == 10` hold. -/
theorem exStore_vc : (Kont.modal .diamond exStore (.post .tt)).vc 60
    (.assume fun σ => σ.storage = StandardExample.initStorage ∧ σ.env = []) := by
  unfold exStore; symex <;> symex_close [initStorage_standardExample, State.exampleStore]

/-- A false specification leaves a goal no evaluation closes. -/
example : True := by
  fail_if_success
    have : (Kont.modal .diamond exBad (.post .tt)).vc 30 .nil := by
      unfold exBad; symex <;> symex_close
  trivial

/-- **The interpreter agrees**: from `StandardExample`'s initial storage,
`alice.age = 10; bool se = alice.age == 10; assert(se);` runs without
reverting. -/
theorem exStore_runs (σ : State) (hs : σ.storage = StandardExample.initStorage) (he : σ.env = []) :
    ∃ τ, execBlock σ exStore.erase = .ok τ := by
  have := Prog.correct .diamond exStore .tt 60 _ exStore_vc σ ⟨hs, he⟩
  revert this; cases execBlock σ exStore.erase <;> simp [after]

end Examples

end Kernel
end Solidity
