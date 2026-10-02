import Solidity.Calculus.SoundUpdate
import Solidity.Calculus.SoundUnfold
import Solidity.Theory.Bridge.Denote

/-!
# The taclets are sound

`Taclet.sound`: every rule's premise is correct for the statement it
rewrites (`Premise.Correct`), against the interpreter `Stmt.run`, from every
state, with no hypothesis but that the rule's fresh names are fresh for the
statement.  An update has the statement's effect; new statements have its
effect off the fresh names; a branch runs the goal its condition picks, and
halts where neither condition holds; a closed goal is a halt, closed as the
modality says.

The five premise kinds are proved apart: `SoundUpdate.lean`,
`SoundUnfold.lean`, and the branches and closed goals here.  The rules solkey
does not have are `LeanTaclet.sound`, and `Rule.sound` is both lists.
-/

namespace Solidity

open Semantics

variable {C : Contract}


/-- A simple value denotes exactly what it evaluates to, a halt as `st mtSt`:
its term has no storage in it, so `denote` is `eval` read through `Res.toSt`. -/
theorem Simple.lower_denote (σ : State) {p : PrimTy} (se : Simple C p) :
    se.lower.denote σ = Res.toSt (se.lower.eval σ) := by
  cases se with
  | lit n h => rfl
  | bool b => rfl
  | «local» x =>
    simp only [Simple.lower, tm_denote, tm_eval, bind, Except.bind]
    rcases σ.getEnv x with _ | (_ | _ | _ | _ | _) <;> rfl
  | env k h => rfl

/-- A result reads as a primitive exactly when it returns it. -/
theorem Res.toSt_eq_prim {r : Res Value} {v : Value} :
    Res.toSt r = .prim v ↔ r = .ok v := by
  cases r with
  | error e => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | ok w => exact ⟨fun h => (by cases h; rfl), fun h => (by cases h; rfl)⟩

theorem Taclet.sound_split {k : Nat} {m : Modality} {s : Stmt C} {c c' : Fml C} {P Q : Prog C}
    (d : Taclet C k m s (.split c c' P Q)) :
    ∀ σ, (holds σ c → SameOk (freshVars k) (Prog.run σ P) (s.run σ)) ∧
      (holds σ c' → SameOk (freshVars k) (Prog.run σ Q) (s.run σ)) ∧
      (¬ holds σ c → ¬ holds σ c' → ∃ e, s.run σ = .error e) := by
  cases d <;> intro σ <;>
    simp only [holds, tm_denote, Theory.StValue.Equiv.prim_iff, Simple.lower_denote, Res.toSt_eq_prim, Simple.lower_eval, Stmt.run, Val.eval, guardOk, Prog.run, bind, Except.bind, pure, Except.pure] <;>
    (rename_i se; cases se.eval σ with
      | error e => simp
      | ok v =>
        simp only
        rcases v with _ | (_ | _) <;> simp [SameOk.self])

/-- `0 <= se`, the guard of a transfer: `se` is a word. -/
theorem holds_amount {σ : State} (se : Simple C .uint) :
    holds σ (.eqD (.binop .le .uint (.lit (.int 0)) se.lower) (.lit (.bool true))) ↔
      ∃ n : Int, se.lower.eval σ = .ok (.int n) ∧ 0 ≤ n := by
  rw [holds_eqD_iff]
  cases h : se.lower.eval σ with
  | error e =>
    simp only [tm_eval, bind, Except.bind, pure, Except.pure, evalBinop, h, reduceCtorEq,
      false_and, exists_false]
  | ok v =>
    rcases v with _ | (_ | _) <;>
      simp only [tm_eval, bind, Except.bind, pure, Except.pure, evalBinop, h, applyBinOp, Value.asInt, checkArith, Except.ok.injEq, exists_eq_left', PrimVal.bool.injEq, true_eq_decide_iff, PrimVal.int.injEq, reduceCtorEq, false_and, exists_false]

/-- `transferNoCallback`: where the amount is a word the booking is the
transfer, where it is not it halts. -/
theorem Taclet.guard_run {k : Nat} {m : Modality} {s : Stmt C} {c : Fml C} {U : Upd C}
    (d : Taclet C k m s (.guard c U)) (σ : State) :
    (holds σ c → U.apply σ = s.run σ) ∧ (¬ holds σ c → ∃ e, s.run σ = .error e) := by
  cases d with
  | transferNoCallback =>
    rename_i sadr se
    rw [holds_amount]
    simp only [Simple.lower_eval]
    constructor
    · rintro ⟨n, hn, h0⟩
      have hn0 : ¬ n < 0 := Int.not_lt.2 h0
      simp only [Upd.apply, List.foldlM_cons, List.foldlM_nil, UpdElem.write, Stmt.run, Val.eval,
        Simple.lower_eval, hn, transferAt, hn0, if_false, bind, Except.bind, pure,
        Except.pure, Value.asInt]
      cases sadr.eval σ with
      | error => rfl
      | ok w =>
        rcases w with a | _
        · simp only [IntOp.apply, State.setNet]
        · rfl
    · intro hn
      simp only [Stmt.run, Val.eval]
      rcases sadr.eval σ with e | (a | b) <;> rcases hs : se.eval σ with e' | (n | b') <;>
        simp only [bind, Except.bind, Value.asInt, transferAt, Except.error.injEq, exists_eq']
      by_cases h0 : n < 0
      · exact ⟨_, if_pos h0⟩
      exact absurd ⟨n, hs, Int.not_lt.1 h0⟩ hn

theorem Taclet.sound_guard {k : Nat} {m : Modality} {s : Stmt C} {c : Fml C} {U : Upd C}
    (d : Taclet C k m s (.guard c U)) :
    ∀ σ, (holds σ c → SameOk [] (U.apply σ) (s.run σ)) ∧
      (¬ holds σ c → ∃ e, s.run σ = .error e) := fun σ =>
  ⟨fun hc => by rw [(d.guard_run σ).1 hc]; exact SameOk.self _ _, (d.guard_run σ).2⟩

theorem Taclet.sound_done {k : Nat} {m : Modality} {s : Stmt C} {b : Bool}
    (d : Taclet C k m s (.done b)) :
    b = true → m = .box ∧ ∀ σ, ∃ e, s.run σ = .error e := by
  cases d <;> simp [Stmt.run]

/-- `tryCallNoCallbackBox`: the run of a `try` is the run of one of its
clauses, from the state with the locals its outcome binds, or it halts. -/
theorem Taclet.sound_branches {k : Nat} {m : Modality} {s : Stmt C}
    {bs : List (List (PrimTy × Var) × Prog C)} (d : Taclet C k m s (.branches bs)) :
    ∀ σ, (m = .box ∧ ∃ e, s.run σ = .error e) ∨
      ∃ b ∈ bs, ∃ σ', Binds b.1 σ σ' ∧ Prog.run σ' b.2 = s.run σ := by
  cases d with
  | tryCallNoCallbackBox =>
    rename_i call rets ok err code pnc other
    intro σ
    have halt : ∀ e, (Stmt.tryCall call rets ok err code pnc other).run σ = .error e →
        (Modality.box = .box ∧ ∃ e, (Stmt.tryCall call rets ok err code pnc other).run σ = .error e) ∨
        ∃ b ∈ [(rets, ok), ([], err), (codeBinders code, pnc), ([], other)], ∃ σ', Binds b.1 σ σ' ∧
          Prog.run σ' b.2 = (Stmt.tryCall call rets ok err code pnc other).run σ :=
      fun e he => .inl ⟨rfl, e, he⟩
    cases hk : call.key σ with
    | error e => exact halt e (by simp [Stmt.run, hk, bind, Except.bind])
    | ok key =>
      cases hl : lookupBy key σ.tx.ext with
      | none => exact halt .revert (by simp [Stmt.run, hk, hl, bind, Except.bind])
      | some r =>
        cases r with
        | ok vs =>
          cases hb : bindData rets vs σ with
          | error e => exact halt e (by simp [Stmt.run, hk, hl, hb, bind, Except.bind])
          | ok σ' => exact .inr ⟨_, List.mem_cons_self, σ', ⟨vs, hb⟩,
              by simp [Stmt.run, hk, hl, hb, bind, Except.bind]⟩
        | error => exact .inr ⟨([], err), by simp, σ, ⟨[], rfl⟩,
              by simp [Stmt.run, hk, hl, bind, Except.bind]⟩
        | panic c =>
          cases hb : bindData (codeBinders code) [c] σ with
          | error e => exact halt e (by simp [Stmt.run, hk, hl, hb, bind, Except.bind])
          | ok σ' => exact .inr ⟨(codeBinders code, pnc), by simp, σ', ⟨[c], hb⟩,
              by simp [Stmt.run, hk, hl, hb, bind, Except.bind]⟩
        | other => exact .inr ⟨([], other), by simp, σ, ⟨[], rfl⟩,
              by simp [Stmt.run, hk, hl, bind, Except.bind]⟩

/-- **The taclets are sound.**  `alice.age = 10;` is `storageFieldWriteSave`,
and its update saves `10` at `alice.age` as running the statement does;
`people[i].age = 10;` is `storageFieldWrite_unfold_leftFst`, whose three
statements run as it does except on the fresh `se` and `sp`. -/
theorem Taclet.sound {k : Nat} {m : Modality} {s : Stmt C} {pr : Premise C}
    (d : Taclet C k m s pr) (hs : Avoids s.vars (freshVars k)) : pr.Correct k m s := by
  cases pr with
  | update U => exact Taclet.sound_update d
  | unfold P => exact Taclet.sound_unfold d hs
  | split c c' P Q => exact Taclet.sound_split d
  | guard c U => exact Taclet.sound_guard d
  | done b => exact Taclet.sound_done d
  | branches bs => exact Taclet.sound_branches d

/-- The rules solkey does not have are sound: `functionCallArgCapture` reads
the argument where the call would (`Stmt.call_capture_sound`). -/
theorem LeanTaclet.sound {k : Nat} {m : Modality} {s : Stmt C} {pr : Premise C}
    (d : LeanTaclet C k m s pr) (hs : Avoids s.vars (freshVars k)) : pr.Correct k m s := by
  cases d with
  | functionCallArgCapture h => exact Stmt.call_capture_sound h hs
  | tryCallDiamond => exact fun h => nomatch h

/-- **Every rule of the calculus is sound**, solkey's and the ones it lacks. -/
theorem Rule.sound {k : Nat} {m : Modality} {s : Stmt C} {pr : Premise C}
    (d : Rule C k m s pr) (hs : Avoids s.vars (freshVars k)) : pr.Correct k m s := by
  cases d with
  | key d => exact d.sound hs
  | lean d => exact d.sound hs

end Solidity
