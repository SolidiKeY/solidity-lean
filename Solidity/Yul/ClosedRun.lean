
import Solidity.Yul.ClosedProfile
import Init.Data.Fin.Lemmas

/-! Fuelled execution for the explicitly no-Solidity-externals word backfill.
None is an exhausted horizon, not a DIV/MOD exception. Profile evidence is erased
and the original AST/environment determine computation. ClosedHorizon proves
completion stability; source prefix/dirty embedding and admission remain open. -/
namespace Solidity.Yul.Closed
abbrev Values (n : Nat) := Fin n → Word

inductive Flow (control : Control) where
  | normal
  | leave_ : control.function = true → Flow control
  | break_ : control.loop = true → Flow control
  | continue_ : control.loop = true → Flow control

structure Outcome (control : Control) (n : Nat) where
  vars : Values n
  flow : Flow control

def Flow.isNormal {c} : Flow c → Bool
  | .normal => true
  | .leave_ _ | .break_ _ | .continue_ _ => false

def extendValues {a n} (front : Values a) (back : Values n) : Values (a + n) :=
  Fin.addCases front back

def dropValues (a : Nat) {n} (values : Values (a + n)) : Values n :=
  fun i => values (Fin.natAdd a i)

def collectValues : (a : Nat) → (Fin a → Option Word) → Option (Values a)
  | 0, _ => some Fin.elim0
  | a + 1, get => do
    let last ← get (Fin.last a)
    let rest ← collectValues a (fun i => get i.castSucc)
    pure (Fin.lastCases last rest)

/-- RHS values have already been computed, before any target is written. -/
def writeTarget {n} (target : Target [] n) (value : Word) (vars : Values n) : Values n :=
  match target with
  | .«local» position => fun i => if i = position then value else vars i
  | .external reference => False.elim (by cases reference.index)

def writeValues {n} : (a : Nat) → (Fin a → Target [] n) → Values a → Values n → Values n
  | 0, _, _, vars => vars
  | a + 1, targets, values, vars =>
    let vars := writeTarget (targets (Fin.last a)) (values (Fin.last a)) vars
    writeValues a (fun i => targets i.castSucc) (fun i => values i.castSucc) vars


/-- Internal generalized-recursion result. Only X=[] has an execution API;
other contexts produce no execution result and are not modelled by this helper. -/
def StmtRunResult (F : List Sig) (X : List ExternalType) (c : Control) (n : Nat)
    (s : Stmt F X c n) : Type :=
  match X with
  | [] => (environment : FunctionEnv F) → EnvWordP environment →
      StmtWordP s → Values n → Option (Outcome c n)
  | _ :: _ => Unit

def CasesRunResult (F : List Sig) (X : List ExternalType) (c : Control) (n : Nat)
    (arms : Cases F X c n) : Type :=
  match X with
  | [] => (environment : FunctionEnv F) → EnvWordP environment →
      CasesWordP arms → Word → Values n → Option (Option (Outcome c n))
  | _ :: _ => Unit

/-- Typed application boundaries for arrows inside the generalized result.
They are definitionally transparent kernel functions; noinline retains the actual application
in compiled recursive calls. Execution/fuel/profile premises are unchanged. -/
@[noinline] def applyStmtRun {F c n} {s : Stmt F [] c n}
    (run : (environment : FunctionEnv F) → EnvWordP environment →
      StmtWordP s → Values n → Option (Outcome c n))
    (environment : FunctionEnv F) (he : EnvWordP environment)
    (hs : StmtWordP s) (vars : Values n) : Option (Outcome c n) :=
  run environment he hs vars

@[noinline] def applyCasesRun {F c n} {arms : Cases F [] c n}
    (run : (environment : FunctionEnv F) → EnvWordP environment →
      CasesWordP arms → Word → Values n → Option (Option (Outcome c n)))
    (environment : FunctionEnv F) (he : EnvWordP environment)
    (hs : CasesWordP arms) (selector : Word) (vars : Values n) :
    Option (Option (Outcome c n)) :=
  run environment he hs selector vars

mutual
def evalExpr (fuel : Nat) {F n r} (environment : FunctionEnv F) (he : EnvWordP environment)
    (e : Expr F [] n r) : ExprWordP e → Values n → Option (Values r) :=
  match fuel with
  | 0 => fun _ _ => none
  | k + 1 => by
    apply Expr.casesOn (motive := fun r e => ExprWordP e → Values n → Option (Values r)) e
    case literal =>
      intro value
      exact fun _ _ => some (fun _ => value)
    case «local» =>
      intro position
      exact fun _ vars => some (fun _ => vars position)
    case external =>
      intro reference
      exact fun h _ => False.elim h
    case builtin =>
      intro a r builtin args
      exact fun h vars => do
        let inputs ← collectValues a (fun i =>
          (evalExpr k environment he (args i) (h.2 i) vars).map (fun result => result 0))
        match hb : checkWordBuiltin builtin with
        | some d => pure (d.eval inputs)
        | none => False.elim (by have bad := h.1; rw [hb] at bad; cases bad)
    case call =>
      intro sig function args
      exact fun h vars => do
        let inputs ← collectValues sig.args (fun i =>
          (evalExpr k environment he (args i) (h i) vars).map (fun result => result 0))
        let closure := lookup environment function
        have hc : ClosureWordP closure := lookup_profile environment he function
        let initial := extendValues inputs (fun _ : Fin sig.rets => word 0)
        let result ← applyStmtRun (evalStmtNode k closure.body) closure.environment hc.1 hc.2 initial
        pure (dropValues sig.args result.vars)
termination_by structural fuel

def evalStmtNode (fuel : Nat) {F X c n} (s : Stmt F X c n) : StmtRunResult F X c n s :=
  match fuel with
  | 0 => by
      cases X with
      | nil => exact fun _ _ _ _ => none
      | cons _ _ => exact ()
  | k + 1 => by
      apply Stmt.casesOn (motive_1 := fun F X c n s => StmtRunResult F X c n s) s
      case skip =>
        intro F X c n
        cases X with
        | nil => exact fun _ _ _ vars => some ⟨vars, .normal⟩
        | cons _ _ => exact ()
      case seq =>
        intro F X c n first second
        cases X with
        | nil =>
          exact fun environment he h vars => do
            let result ← applyStmtRun (evalStmtNode k first) environment he h.1 vars
            match result.flow with
            | .normal => applyStmtRun (evalStmtNode k second) environment he h.2 result.vars
            | _ => pure result
        | cons _ _ => exact ()
      case assign =>
        intro F X c n r targets expression
        cases X with
        | nil =>
          exact fun environment he h vars => do
            let values ← evalExpr k environment he expression h.2 vars
            pure ⟨writeValues r targets values vars, .normal⟩
        | cons _ _ => exact ()
      case discard =>
        intro F X c n expression
        cases X with
        | nil =>
          exact fun environment he h vars => do
            let _ ← evalExpr k environment he expression h vars
            pure ⟨vars, .normal⟩
        | cons _ _ => exact ()
      case let_ =>
        intro F X c n r expression body
        cases X with
        | nil =>
          exact fun environment he h vars => do
            let values ← evalExpr k environment he expression h.1 vars
            let result ← applyStmtRun (evalStmtNode k body) environment he h.2 (extendValues values vars)
            pure ⟨dropValues r result.vars, result.flow⟩
        | cons _ _ => exact ()
      case zero =>
        intro F X c n r body
        cases X with
        | nil =>
          exact fun environment he h vars => do
            let result ← applyStmtRun (evalStmtNode k body) environment he h (extendValues (fun _ : Fin r => word 0) vars)
            pure ⟨dropValues r result.vars, result.flow⟩
        | cons _ _ => exact ()
      case if_ =>
        intro F X c n expression body
        cases X with
        | nil =>
          exact fun environment he h vars => do
            let condition ← evalExpr k environment he expression h.1 vars
            if (condition 0).val = 0 then pure ⟨vars, .normal⟩
            else applyStmtRun (evalStmtNode k body) environment he h.2 vars
        | cons _ _ => exact ()
      case switch =>
        intro F X c n expression arms fallback
        cases X with
        | nil =>
          exact fun environment he h vars => do
            let selector ← evalExpr k environment he expression h.1 vars
            let selected ← applyCasesRun (evalCasesNode k arms) environment he h.2.1 (selector 0) vars
            match selected with
            | some result => pure result
            | none => applyStmtRun (evalStmtNode k fallback) environment he h.2.2 vars
        | cons _ _ => exact ()
      case for_ =>
        intro F X c n pre condition post body
        cases X with
        | nil =>
          exact fun environment he h vars => do
            let result ← applyStmtRun (evalStmtNode k pre) environment he h.1 vars
            match result.flow with
            | .normal =>
              evalLoop k environment he condition h.2.1 post h.2.2.1 body h.2.2.2 result.vars
            | .leave_ hf => pure ⟨result.vars, .leave_ hf⟩
            | .break_ impossible => False.elim (by cases impossible)
            | .continue_ impossible => False.elim (by cases impossible)
        | cons _ _ => exact ()
      case leave =>
        intro F X loop n
        cases X with
        | nil => exact fun _ _ _ vars => some ⟨vars, .leave_ rfl⟩
        | cons _ _ => exact ()
      case break_ =>
        intro F X function n
        cases X with
        | nil => exact fun _ _ _ vars => some ⟨vars, .break_ rfl⟩
        | cons _ _ => exact ()
      case continue_ =>
        intro F X function n
        cases X with
        | nil => exact fun _ _ _ vars => some ⟨vars, .continue_ rfl⟩
        | cons _ _ => exact ()
      case functions =>
        intro F X c n signatures bodies rest
        cases X with
        | nil =>
          exact fun environment he h vars =>
            applyStmtRun (evalStmtNode k rest) (.group signatures environment bodies) ⟨he, h.1⟩ h.2 vars
        | cons _ _ => exact ()
termination_by structural fuel

def evalCasesNode (fuel : Nat) {F X c n} (arms : Cases F X c n) :
    CasesRunResult F X c n arms :=
  match fuel with
  | 0 => by
      cases X with
      | nil => exact fun _ _ _ _ _ => none
      | cons _ _ => exact ()
  | k + 1 => by
      apply Cases.casesOn (motive_2 := fun F X c n arms => CasesRunResult F X c n arms) arms
      case nil =>
        intro F X c n
        cases X with
        | nil => exact fun _ _ _ _ _ => some none
        | cons _ _ => exact ()
      case cons =>
        intro F X c n value body rest
        cases X with
        | nil =>
          exact fun environment he h selector vars =>
            if selector = value then
              (applyStmtRun (evalStmtNode k body) environment he h.1 vars).map some
            else applyCasesRun (evalCasesNode k rest) environment he h.2 selector vars
        | cons _ _ => exact ()
termination_by structural fuel

def evalLoop (fuel : Nat) {F c n} (environment : FunctionEnv F) (he : EnvWordP environment)
    (condition : Expr F [] n 1) (hc : ExprWordP condition)
    (post : Stmt F [] ⟨c.function, false⟩ n) (hp : StmtWordP post)
    (body : Stmt F [] ⟨c.function, true⟩ n) (hb : StmtWordP body) (vars : Values n) :
    Option (Outcome c n) :=
  match fuel with
  | 0 => none
  | k + 1 => do
      let value ← evalExpr k environment he condition hc vars
      if (value 0).val = 0 then pure ⟨vars, .normal⟩
      else
        let afterBody := fun vars => do
          let result ← applyStmtRun (evalStmtNode k post) environment he hp vars
          match result.flow with
          | .normal => evalLoop k environment he condition hc post hp body hb result.vars
          | .leave_ hf => pure ⟨result.vars, .leave_ hf⟩
          | .break_ impossible => False.elim (by cases impossible)
          | .continue_ impossible => False.elim (by cases impossible)
        let result ← applyStmtRun (evalStmtNode k body) environment he hb vars
        match result.flow with
        | .normal => afterBody result.vars
        | .continue_ _ => afterBody result.vars
        | .break_ _ => pure ⟨result.vars, .normal⟩
        | .leave_ hf => pure ⟨result.vars, .leave_ hf⟩
termination_by structural fuel
end

def evalStmt (fuel : Nat) {F c n} (environment : FunctionEnv F) (he : EnvWordP environment)
    (s : Stmt F [] c n) (h : StmtWordP s) (vars : Values n) : Option (Outcome c n) :=
  evalStmtNode fuel s environment he h vars


theorem evalExpr_proof_irrel (fuel : Nat) {F n r} (environment : FunctionEnv F)
    (he he' : EnvWordP environment) (e : Expr F [] n r) (h h' : ExprWordP e) (vars : Values n) :
    evalExpr fuel environment he e h vars = evalExpr fuel environment he' e h' vars := rfl

theorem evalStmt_proof_irrel (fuel : Nat) {F c n} (environment : FunctionEnv F)
    (he he' : EnvWordP environment) (s : Stmt F [] c n) (h h' : StmtWordP s) (vars : Values n) :
    evalStmt fuel environment he s h vars = evalStmt fuel environment he' s h' vars := rfl



def evalCases (fuel : Nat) {F c n} (environment : FunctionEnv F) (he : EnvWordP environment)
    (arms : Cases F [] c n) (h : CasesWordP arms) (selector : Word) (vars : Values n) :
    Option (Option (Outcome c n)) := evalCasesNode fuel arms environment he h selector vars

theorem evalExpr_zero {F n r} (environment : FunctionEnv F) (he : EnvWordP environment)
    (e : Expr F [] n r) (h : ExprWordP e) (vars : Values n) :
    evalExpr 0 environment he e h vars = none := rfl

theorem evalStmt_zero {F c n} (environment : FunctionEnv F) (he : EnvWordP environment)
    (s : Stmt F [] c n) (h : StmtWordP s) (vars : Values n) :
    evalStmt 0 environment he s h vars = none := rfl

theorem evalExpr_builtin (fuel : Nat) {F n a r} (environment : FunctionEnv F)
    (he : EnvWordP environment) (b : Builtin a r) (d : WordBuiltinD b)
    (args : Fin a → Expr F [] n 1) (h : ExprWordP (.builtin b args)) (vars : Values n) :
    evalExpr (fuel + 1) environment he (.builtin b args) h vars =
      (do let inputs ← collectValues a (fun i =>
            (evalExpr fuel environment he (args i) (h.2 i) vars).map (fun result => result 0))
          pure (d.eval inputs)) := by
  cases d <;> rfl

theorem evalExpr_call (fuel : Nat) {F n sig} (environment : FunctionEnv F)
    (he : EnvWordP environment) (function : Member F sig) (args : Fin sig.args → Expr F [] n 1)
    (h : ExprWordP (.call function args)) (vars : Values n) :
    evalExpr (fuel + 1) environment he (.call function args) h vars =
      (do let inputs ← collectValues sig.args (fun i =>
            (evalExpr fuel environment he (args i) (h i) vars).map (fun result => result 0))
          let closure := lookup environment function
          have hc : ClosureWordP closure := lookup_profile environment he function
          let result ← evalStmt fuel closure.environment hc.1 closure.body hc.2
            (extendValues inputs (fun _ : Fin sig.rets => word 0))
          pure (dropValues sig.args result.vars)) := rfl

theorem evalStmt_discard (fuel : Nat) {F c n} (environment : FunctionEnv F)
    (he : EnvWordP environment) (e : Expr F [] n 0) (h : StmtWordP (Stmt.discard (c := c) e))
    (vars : Values n) :
    evalStmt (fuel + 1) environment he (Stmt.discard (c := c) e) h vars =
      (do let _ ← evalExpr fuel environment he e h vars
          pure ⟨vars, .normal⟩) := rfl

/-- Completion refinement: increasing a horizon preserves every old completion. -/
def Refines {α : Type} (old new : Option α) : Prop :=
  ∀ result, old = some result → new = some result

theorem Refines.refl {α} (value : Option α) : Refines value value := fun _ h => h

theorem Refines.none {α} (value : Option α) : Refines none value := by
  intro result h
  cases h

theorem Refines.bind {α β} {old new : Option α} {first second : α → Option β}
    (h : Refines old new) (next : ∀ value, Refines (first value) (second value)) :
    Refines (old.bind first) (new.bind second) := by
  intro result hr
  cases ho : old with
  | none => rw [ho] at hr; cases hr
  | some value =>
      have hn : new = some value := h value ho
      rw [ho] at hr
      rw [hn]
      exact next value result hr

theorem Refines.map {α β} {old new : Option α} (h : Refines old new) (f : α → β) :
    Refines (old.map f) (new.map f) := by
  intro result hr
  cases ho : old with
  | none => rw [ho] at hr; cases hr
  | some value =>
      have hn : new = some value := h value ho
      rw [ho] at hr
      rw [hn]
      exact hr

theorem collectValues_refines (a : Nat) (old new : Fin a → Option Word)
    (h : ∀ i, Refines (old i) (new i)) :
    Refines (collectValues a old) (collectValues a new) := by
  induction a with
  | zero => exact Refines.refl _
  | succ a ih =>
      apply Refines.bind (h (Fin.last a))
      intro last
      apply Refines.bind (ih (fun i => old i.castSucc) (fun i => new i.castSucc)
        (fun i => h i.castSucc))
      intro rest
      exact Refines.refl _


end Solidity.Yul.Closed
