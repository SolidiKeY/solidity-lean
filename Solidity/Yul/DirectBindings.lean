import Solidity.Yul.CoordinateControl

/-! Direct actual-AST binder family. Existing Basic evidence is retained;
binders are executed with actual extended raw locals and the same external
cells. Switch/loops/functions remain outside this explicit family. -/
namespace Solidity.Yul.DirectBindings
open Closed

inductive Supported (X : List ExternalType) :
    {c : Control} → {n : Nat} → Stmt [] X c n → Type where
  | base {c n} {code : Stmt [] X c n} : DirectControl.Basic X code → Supported X code
  | seq {c n} {a b : Stmt [] X c n} : Supported X a → Supported X b → Supported X (.seq a b)
  | if_ {c n} (condition : Expr [] X n 1) {body : Stmt [] X c n} :
      Supported X body → Supported X (.if_ condition body)
  | let_ {c n r} (rhs : Expr [] X n r) {body : Stmt [] X c (r+n)} :
      Supported X body → Supported X (.let_ r rhs body)
  | zero {c n} (r : Nat) {body : Stmt [] X c (r+n)} :
      Supported X body → Supported X (.zero r body)

def eval (fuel : Nat) {X c n} {code : Stmt [] X c n} (proof : Supported X code) :
    Policy.StmtP .A code → WordState X n → Option (WordAdapter.Outcome X c n) :=
  match fuel with
  | 0 => fun _ _ => none
  | k+1 => by
    apply Supported.casesOn (motive := fun {n} code _ =>
      Policy.StmtP .A code → WordState X n → Option (WordAdapter.Outcome X c n)) proof
    case base =>
      intro n code proof
      exact fun policy state => DirectControl.eval (k+1) proof policy state
    case seq =>
      intro n a b first second
      exact fun policy state => do
        let result ← eval k first policy.1 state
        match result.flow with
        | .normal => eval k second policy.2 result.state
        | _ => pure result
    case if_ =>
      intro n condition body proof
      exact fun policy state => do
        let values ← DirectWords.eval k condition policy.1 state
        if (values 0).val = 0 then pure ⟨state,.normal⟩
        else eval k proof policy.2 state
    case let_ =>
      intro n r rhs body proof
      exact fun policy state => do
        let values ← DirectWords.eval k rhs policy.1 state
        let result ← eval k proof policy.2 (state.extend values)
        pure ⟨result.state.drop r,result.flow⟩
    case zero =>
      intro n r body proof
      exact fun policy state => do
        let result ← eval k proof policy (state.extend (fun _ : Fin r => word 0))
        pure ⟨result.state.drop r,result.flow⟩
termination_by structural fuel

theorem agrees (fuel : Nat) {X c n m} (coordinates : Coordinates X n m)
    {code : Stmt [] X c n} (proof : Supported X code)
    (policy : Policy.StmtP .A code) (state : WordState X n) :
    (eval fuel proof policy state).map (Coordinates.encodeOutcome coordinates) =
      evalStmt fuel .nil True.intro
        (WordAdapter.statement code policy coordinates.locals coordinates.cells).code
        (WordAdapter.statement code policy coordinates.locals coordinates.cells).words
        (coordinates.pack state) := by
  induction fuel generalizing c n m code with
  | zero => rfl
  | succ fuel ih =>
    cases proof with
    | base proof =>
      change (DirectControl.eval (fuel+1) proof policy state).map
        (Coordinates.encodeOutcome coordinates) = _
      exact Coordinates.control_agrees (fuel+1) coordinates proof policy state
    | @seq n a b first second =>
      rw [WordAdapter.statement]
      change (do
        let result ← eval fuel first policy.1 state
        match result.flow with
        | .normal => eval fuel second policy.2 result.state
        | _ => pure result).map (Coordinates.encodeOutcome coordinates) =
        (do
          let result ← evalStmt fuel .nil True.intro
            (WordAdapter.statement a policy.1 coordinates.locals
              coordinates.cells).code
            (WordAdapter.statement a policy.1 coordinates.locals
              coordinates.cells).words (coordinates.pack state)
          match result.flow with
          | .normal =>
              evalStmt fuel .nil True.intro
                (WordAdapter.statement b policy.2 coordinates.locals
                  coordinates.cells).code
                (WordAdapter.statement b policy.2 coordinates.locals
                  coordinates.cells).words result.vars
          | _ => pure result)
      rw [←ih coordinates first policy.1 state]
      cases firstRun : eval fuel first policy.1 state with
      | none => rfl
      | some result =>
        cases result with
        | mk middle flow =>
          cases flow with
          | normal => exact ih coordinates second policy.2 middle
          | leave_ legal => rfl
          | break_ legal => rfl
          | continue_ legal => rfl
    | @if_ n condition body bodyProof =>
      rw [WordAdapter.statement]
      change (do
        let values ← DirectWords.eval fuel condition policy.1 state
        if (values 0).val = 0 then pure (⟨state,.normal⟩ : WordAdapter.Outcome X c n)
        else eval fuel bodyProof policy.2 state).map (Coordinates.encodeOutcome coordinates) =
        (do
          let values ← evalExpr fuel .nil True.intro
            (WordAdapter.expression condition policy.1 coordinates.locals
              coordinates.cells).code
            (WordAdapter.expression condition policy.1 coordinates.locals
              coordinates.cells).words (coordinates.pack state)
          if (values 0).val = 0 then pure (⟨(coordinates.pack state),.normal⟩ : Closed.Outcome c m)
          else
            evalStmt fuel .nil True.intro
              (WordAdapter.statement body policy.2 coordinates.locals
                coordinates.cells).code
              (WordAdapter.statement body policy.2 coordinates.locals
                coordinates.cells).words (coordinates.pack state))
      rw [←Coordinates.expression_agrees fuel coordinates]
      cases conditionRun : DirectWords.eval fuel condition policy.1 state with
      | none => rfl
      | some values =>
        change (if (values 0).val = 0
          then some (⟨state,.normal⟩ : WordAdapter.Outcome X c n)
          else eval fuel bodyProof policy.2 state).map (Coordinates.encodeOutcome coordinates) =
          (if (values 0).val = 0
           then some (⟨(coordinates.pack state),.normal⟩ : Closed.Outcome c m)
           else evalStmt fuel .nil True.intro
             (WordAdapter.statement body policy.2 coordinates.locals
               coordinates.cells).code
             (WordAdapter.statement body policy.2 coordinates.locals
               coordinates.cells).words (coordinates.pack state))
        by_cases zero : (values 0).val = 0
        · rw [if_pos zero,if_pos zero]
          rfl
        · rw [if_neg zero,if_neg zero]
          exact ih coordinates bodyProof policy.2 state
    | @let_ n r rhs body bodyProof =>
      let term := WordAdapter.expression rhs policy.1 coordinates.locals coordinates.cells
      let rest := WordAdapter.statement body policy.2
        (coordinates.prepend r).locals (coordinates.prepend r).cells
      rw [WordAdapter.statement]
      change (do
        let values ← DirectWords.eval fuel rhs policy.1 state
        let result ← eval fuel bodyProof policy.2 (state.extend values)
        pure (⟨result.state.drop r,result.flow⟩ : WordAdapter.Outcome X c n)).map
          (Coordinates.encodeOutcome coordinates) =
        (do
          let values ← evalExpr fuel .nil True.intro term.code term.words (coordinates.pack state)
          let result ← evalStmt fuel .nil True.intro rest.code rest.words
            (Closed.extendValues values (coordinates.pack state))
          pure (⟨Closed.dropValues r result.vars,result.flow⟩ : Closed.Outcome c m))
      rw [←Coordinates.expression_agrees fuel coordinates]
      cases rhsRun : DirectWords.eval fuel rhs policy.1 state with
      | none => rfl
      | some values =>
        change ((eval fuel bodyProof policy.2 (state.extend values)).bind (fun result =>
          some (⟨result.state.drop r,result.flow⟩ : WordAdapter.Outcome X c n))).map
            (Coordinates.encodeOutcome coordinates) =
          ((evalStmt fuel .nil True.intro rest.code rest.words
            (Closed.extendValues values (coordinates.pack state))).bind (fun result =>
              some (⟨Closed.dropValues r result.vars,result.flow⟩ : Closed.Outcome c m)))
        rw [←Coordinates.pack_prefix coordinates values state]
        rw [←ih (coordinates.prepend r) bodyProof policy.2 (state.extend values)]
        cases bodyRun : eval fuel bodyProof policy.2 (state.extend values) with
        | none => rfl
        | some result =>
          change some (⟨coordinates.pack (result.state.drop r),result.flow⟩ : Closed.Outcome c m) =
            some ⟨Closed.dropValues r ((coordinates.prepend r).pack result.state),result.flow⟩
          rw [Coordinates.pack_drop]
    | @zero n r body bodyProof =>
      let initial : Closed.Values r := fun _ => word 0
      let rest := WordAdapter.statement body policy
        (coordinates.prepend r).locals (coordinates.prepend r).cells
      rw [WordAdapter.statement]
      change ((eval fuel bodyProof policy (state.extend initial)).bind (fun result =>
        some (⟨result.state.drop r,result.flow⟩ : WordAdapter.Outcome X c n))).map
          (Coordinates.encodeOutcome coordinates) =
        ((evalStmt fuel .nil True.intro rest.code rest.words
          (Closed.extendValues initial (coordinates.pack state))).bind (fun result =>
            some (⟨Closed.dropValues r result.vars,result.flow⟩ : Closed.Outcome c m)))
      rw [←Coordinates.pack_prefix coordinates initial state]
      rw [←ih (coordinates.prepend r) bodyProof policy (state.extend initial)]
      cases bodyRun : eval fuel bodyProof policy (state.extend initial) with
      | none => rfl
      | some result =>
        change some (⟨coordinates.pack (result.state.drop r),result.flow⟩ : Closed.Outcome c m) =
          some ⟨Closed.dropValues r ((coordinates.prepend r).pack result.state),result.flow⟩
        rw [Coordinates.pack_drop]


/-- The concrete canonical instance discharges all logical-coordinate fields. -/
theorem run_agrees (fuel : Nat) {X c n} {code : Stmt [] X c n}
    (proof : Supported X code) (policy : Policy.StmtP .A code) (state : WordState X n) :
    eval fuel proof policy state = WordAdapter.run code policy fuel state := by
  have packed := agrees fuel (Coordinates.canonical X n) proof policy state
  have encoding : Coordinates.encodeOutcome (Coordinates.canonical X n) (c := c) =
      WordAdapter.Outcome.encode := by
    funext result
    exact Coordinates.canonical_encode result
  rw [encoding,Coordinates.canonical_pack] at packed
  apply (Option.map_inj_right (f := WordAdapter.Outcome.encode (X := X) (c := c) (n := n))
    (fun one two same => by
      have decoded := congrArg (WordAdapter.Outcome.decode (X := X) (c := c) (n := n)) same
      simpa only [WordAdapter.Outcome.decode_encode] using decoded)).mp
  exact packed.trans (WordAdapter.run_encode code policy fuel state).symm

theorem stable {lo hi : Nat} (bound : lo ≤ hi) {X c n} {code : Stmt [] X c n}
    (proof : Supported X code) (policy : Policy.StmtP .A code) (state : WordState X n)
    {result : WordAdapter.Outcome X c n} (done : eval lo proof policy state = some result) :
    eval hi proof policy state = some result := by
  rw [run_agrees] at done ⊢
  exact WordAdapter.run_stable code policy state bound done

theorem evidence_independent {X c n} {code : Stmt [] X c n}
    (one two : Supported X code) (policy : Policy.StmtP .A code) (fuel : Nat) (state : WordState X n) :
    eval fuel one policy state = eval fuel two policy state := by
  rw [run_agrees,run_agrees]

end Solidity.Yul.DirectBindings
