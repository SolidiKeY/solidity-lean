import Solidity.Calculus.Core.SoundCapture

/-!
# Soundness of the storage arms

`Calculus/Core/Arms.lean`'s `assignStep`, `copyStep`, `assignFromMemStep`,
`deleteStep`, `pushStep` and `popStep`, each sound in the shape of
`Calculus/Core/SoundKit.lean`.  A rule that captures several parts
(`T se = e; T storage sp = b; T ie = i; sp[ie] = se;`) runs them as a block
(`Prog.run_declLocal_cons` and its kin), its statement read on the pushed
states by the push lemmas, one push at a time.  Where the rule captures
the target before the source the statement reads the other way round, and
the two halt alike (`Res.Sim`).
-/

namespace Solidity.Core

open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic)
open Semantics (Value SVal MVal Seg Halt Res)

variable {C : Contract}

/-! ## Blocks of captures -/

section Blocks

variable {Γ : Ctx} (σ : State C Γ)

theorem Prog.run_declLocal_cons {Γ' : Ctx} (p : PrimTy) (x : Var) (e : Val C Γ p)
    (P : Prog C (.val p :: Γ) Γ') :
    Prog.run σ (.cons (.declLocal p x (some e)) P) = e.eval σ >>= fun v => Prog.run (σ.push v) P := by
  rw [Prog.run_cons, Stmt.run_declLocal]
  simp only [Run.declLocal]
  cases e.eval σ <;> rfl

theorem Prog.run_declStorage_cons {Γ' : Ctx} {R : RefTy} (x : Var) (b : SPath C Γ (.ref R))
    (P : Prog C (.alias R :: Γ) Γ') :
    Prog.run σ (.cons (.declStorage R x (some (.path b))) P) =
      b.resolve σ >>= fun q => Prog.run (σ.push (t := .alias R) (some q)) P := by
  rw [Prog.run_cons, Stmt.run_declStorage]
  simp only [Run.declStorage, ARhs.eval, bind_assoc, pure_bind]
  cases b.resolve σ <;> rfl

theorem Prog.run_declMem_cons {Γ' : Ctx} {R : RefTy} (x : Var) (b : MPath C Γ (.ref R))
    (hm : (Ty.ref R).mapFree = true) (P : Prog C (.mem R :: Γ) Γ') :
    Prog.run σ (.cons (.declMem R x (some (.alias b)) rfl hm) P) =
      (do (← b.mval σ).asRef) >>= fun id => Prog.run (σ.push (t := .mem R) id) P := by
  rw [Prog.run_cons, Stmt.run_declMem]
  simp only [Run.declMem, MRhs.eval, bind_assoc, pure_bind]
  cases b.mval σ with
  | error => rfl
  | ok mv => simp only [Res.bind_ok]; cases mv.asRef <;> rfl

theorem pushed2_drop {t u : LTy} (w : t.Denote C) (w' : u.Denote C) (r : Res (State C Γ)) :
    (pushed (Γ := t :: Γ) w' (pushed w r)).map (State.drop (.push (.push .refl))) = r := by
  cases r <;> rfl

theorem pushed3_drop {t u v : LTy} (w : t.Denote C) (w' : u.Denote C) (w'' : v.Denote C)
    (r : Res (State C Γ)) :
    (pushed (Γ := u :: t :: Γ) w'' (pushed (Γ := t :: Γ) w' (pushed w r))).map
      (State.drop (.push (.push (.push .refl)))) = r := by
  cases r <;> rfl

/-- A halt alike to `h` from a run that does not panic and does not end. -/
theorem Res.Sim.err_of_not_ok {α : Type} {h : Halt} (hh : h ≠ .panic) {r : Res α} (hr : NoPanic r)
    (hn : ∀ a, r ≠ .ok a) : Res.Sim (.error h) r := by
  cases r with
  | ok a => exact absurd rfl (hn a)
  | error e => exact ⟨fun e' => absurd e' hh, fun e' => absurd (congrArg Except.error e') hr⟩

theorem Src.value_noPanic {T : Ty} (r : Src C Γ T) : NoPanic (r.value σ) := by
  cases r with
  | val v =>
    have := Val.eval_noPanic σ v
    simp only [Src.value]
    exact NoPanic.bind this fun _ _ => NoPanic.pure _
  | copy p hm =>
    simp only [Src.value]
    exact NoPanic.bind (SPath.resolve_noPanic σ p) fun _ _ => Solidity.State.findStorage_noPanic _ _ _

end Blocks

end Solidity.Core
