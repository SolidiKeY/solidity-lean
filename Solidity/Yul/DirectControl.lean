import Solidity.Yul.DirectUpdates

/-! Direct execution evidence for a stated constructor family of the actual
intrinsic Stmt AST. This is not a replacement AST or a full-fragment coverage
claim: binders, switch, loops and function groups remain outside this family. -/
namespace Solidity.Yul.DirectControl
open Closed

inductive Basic (X : List ExternalType) :
    {c : Control} → {n : Nat} → Stmt [] X c n → Type where
  | skip {c n} : Basic X (Stmt.skip (c := c) (n := n))
  | seq {c n} {a b : Stmt [] X c n} : Basic X a → Basic X b → Basic X (.seq a b)
  | assign {c n r} (targets : Fin r → Target X n) (rhs : Expr [] X n r) :
      Basic X (Stmt.assign (c := c) targets rhs)
  | discard {c n} (rhs : Expr [] X n 0) : Basic X (Stmt.discard (c := c) rhs)
  | if_ {c n} (condition : Expr [] X n 1) {body : Stmt [] X c n} :
      Basic X body → Basic X (.if_ condition body)
  | leave {l n} : Basic X (Stmt.leave (l := l) (n := n))
  | break_ {f n} : Basic X (Stmt.break_ (f := f) (n := n))
  | continue_ {f n} : Basic X (Stmt.continue_ (f := f) (n := n))

def eval (fuel : Nat) {X c n} {code : Stmt [] X c n} (proof : Basic X code) :
    Policy.StmtP .A code → WordState X n → Option (WordAdapter.Outcome X c n) :=
  match fuel with
  | 0 => fun _ _ => none
  | k+1 => by
    apply Basic.casesOn (motive := fun {c n} code _ =>
      Policy.StmtP .A code → WordState X n → Option (WordAdapter.Outcome X c n)) proof
    case skip =>
      intro c n
      exact fun _ state => some ⟨state,.normal⟩
    case seq =>
      intro c n a b first second
      exact fun policy state => do
        let result ← eval k first policy.1 state
        match result.flow with
        | .normal => eval k second policy.2 result.state
        | _ => pure result
    case assign =>
      intro c n r targets rhs
      exact fun policy state =>
        (DirectUpdates.assign (k+1) targets rhs policy state).map
          (fun final => ⟨final,.normal⟩)
    case discard =>
      intro c n rhs
      exact fun policy state => do
        let _ ← DirectWords.eval k rhs policy state
        pure ⟨state,.normal⟩
    case if_ =>
      intro c n condition body proof
      exact fun policy state => do
        let values ← DirectWords.eval k condition policy.1 state
        if (values 0).val = 0 then pure ⟨state,.normal⟩
        else eval k proof policy.2 state
    case leave =>
      intro l n
      exact fun _ state => some ⟨state,.leave_ rfl⟩
    case break_ =>
      intro f n
      exact fun _ state => some ⟨state,.break_ rfl⟩
    case continue_ =>
      intro f n
      exact fun _ state => some ⟨state,.continue_ rfl⟩
termination_by structural fuel

theorem agrees (fuel : Nat) {X c n} {code : Stmt [] X c n}
    (proof : Basic X code) (policy : Policy.StmtP .A code) (state : WordState X n) :
    (eval fuel proof policy state).map WordAdapter.Outcome.encode =
      evalStmt fuel .nil True.intro
        (WordAdapter.statement code policy (Fin.castAdd (wordCellCount X))
          (fun cell => Fin.natAdd n cell.slot)).code
        (WordAdapter.statement code policy (Fin.castAdd (wordCellCount X))
          (fun cell => Fin.natAdd n cell.slot)).words state.pack := by
  induction fuel generalizing c n code with
  | zero => rfl
  | succ fuel ih =>
    cases proof with
    | skip => rfl
    | assign targets rhs =>
      change ((DirectUpdates.assign (fuel+1) targets rhs policy state).map
        (fun final => (⟨final,.normal⟩ : WordAdapter.Outcome X c n))).map
          WordAdapter.Outcome.encode = _
      simpa only [Option.map_map,Function.comp_def,WordAdapter.Outcome.encode] using
        DirectUpdates.assign_agrees (fuel+1) targets rhs policy state
    | discard rhs =>
      change (do
        let _ ← DirectWords.eval fuel rhs policy state
        pure (⟨state,.normal⟩ : WordAdapter.Outcome X c n)).map WordAdapter.Outcome.encode = _
      rw [WordAdapter.statement,evalStmt_discard,←DirectWords.packed_agrees]
      cases DirectWords.eval fuel rhs policy state <;> rfl
    | @seq c n a b first second =>
      rw [WordAdapter.statement]
      change (do
        let result ← eval fuel first policy.1 state
        match result.flow with
        | .normal => eval fuel second policy.2 result.state
        | _ => pure result).map WordAdapter.Outcome.encode =
        (do
          let result ← evalStmt fuel .nil True.intro
            (WordAdapter.statement a policy.1 (Fin.castAdd (wordCellCount X))
              (fun cell => Fin.natAdd n cell.slot)).code
            (WordAdapter.statement a policy.1 (Fin.castAdd (wordCellCount X))
              (fun cell => Fin.natAdd n cell.slot)).words state.pack
          match result.flow with
          | .normal =>
              evalStmt fuel .nil True.intro
                (WordAdapter.statement b policy.2 (Fin.castAdd (wordCellCount X))
                  (fun cell => Fin.natAdd n cell.slot)).code
                (WordAdapter.statement b policy.2 (Fin.castAdd (wordCellCount X))
                  (fun cell => Fin.natAdd n cell.slot)).words result.vars
          | _ => pure result)
      rw [←ih first policy.1 state]
      cases firstRun : eval fuel first policy.1 state with
      | none => rfl
      | some result =>
        cases result with
        | mk middle flow =>
          cases flow with
          | normal => exact ih second policy.2 middle
          | leave_ legal => rfl
          | break_ legal => rfl
          | continue_ legal => rfl
    | @if_ c n condition body bodyProof =>
      rw [WordAdapter.statement]
      change (do
        let values ← DirectWords.eval fuel condition policy.1 state
        if (values 0).val = 0 then pure (⟨state,.normal⟩ : WordAdapter.Outcome X c n)
        else eval fuel bodyProof policy.2 state).map WordAdapter.Outcome.encode =
        (do
          let values ← evalExpr fuel .nil True.intro
            (WordAdapter.expression condition policy.1 (Fin.castAdd (wordCellCount X))
              (fun cell => Fin.natAdd n cell.slot)).code
            (WordAdapter.expression condition policy.1 (Fin.castAdd (wordCellCount X))
              (fun cell => Fin.natAdd n cell.slot)).words state.pack
          if (values 0).val = 0 then pure (⟨state.pack,.normal⟩ : Closed.Outcome c (n+wordCellCount X))
          else
            evalStmt fuel .nil True.intro
              (WordAdapter.statement body policy.2 (Fin.castAdd (wordCellCount X))
                (fun cell => Fin.natAdd n cell.slot)).code
              (WordAdapter.statement body policy.2 (Fin.castAdd (wordCellCount X))
                (fun cell => Fin.natAdd n cell.slot)).words state.pack)
      rw [←DirectWords.packed_agrees]
      cases conditionRun : DirectWords.eval fuel condition policy.1 state with
      | none => rfl
      | some values =>
        change (if (values 0).val = 0
          then some (⟨state,.normal⟩ : WordAdapter.Outcome X c n)
          else eval fuel bodyProof policy.2 state).map WordAdapter.Outcome.encode =
          (if (values 0).val = 0
           then some (⟨state.pack,.normal⟩ : Closed.Outcome c (n+wordCellCount X))
           else evalStmt fuel .nil True.intro
             (WordAdapter.statement body policy.2 (Fin.castAdd (wordCellCount X))
               (fun cell => Fin.natAdd n cell.slot)).code
             (WordAdapter.statement body policy.2 (Fin.castAdd (wordCellCount X))
               (fun cell => Fin.natAdd n cell.slot)).words state.pack)
        by_cases zero : (values 0).val = 0
        · rw [if_pos zero,if_pos zero]
          rfl
        · rw [if_neg zero,if_neg zero]
          exact ih bodyProof policy.2 state
    | leave => rfl
    | break_ => rfl
    | continue_ => rfl


/-- This concrete composition retains the complete original raw outcome. -/
theorem run_agrees (fuel : Nat) {X c n} {code : Stmt [] X c n}
    (proof : Basic X code) (policy : Policy.StmtP .A code) (state : WordState X n) :
    eval fuel proof policy state = WordAdapter.run code policy fuel state := by
  apply (Option.map_inj_right (f := WordAdapter.Outcome.encode (X := X) (c := c) (n := n)) (fun one two same => by
    have decoded := congrArg (WordAdapter.Outcome.decode (X := X) (c := c) (n := n)) same
    simpa only [WordAdapter.Outcome.decode_encode] using decoded)).mp
  exact (agrees fuel proof policy state).trans (WordAdapter.run_encode code policy fuel state).symm

theorem stable {lo hi : Nat} (bound : lo ≤ hi) {X c n} {code : Stmt [] X c n}
    (proof : Basic X code) (policy : Policy.StmtP .A code) (state : WordState X n)
    {result : WordAdapter.Outcome X c n} (done : eval lo proof policy state = some result) :
    eval hi proof policy state = some result := by
  rw [run_agrees] at done ⊢
  exact WordAdapter.run_stable code policy state bound done

theorem evidence_independent {X c n} {code : Stmt [] X c n}
    (one two : Basic X code) (policy : Policy.StmtP .A code) (fuel : Nat) (state : WordState X n) :
    eval fuel one policy state = eval fuel two policy state := by
  rw [run_agrees,run_agrees]

end Solidity.Yul.DirectControl
