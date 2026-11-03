import Solidity.Yul.OpenFunctions

/-! Direct tier-A execution of the actual full intrinsic Yul AST. This runner
retains source bodies/lexical environments, raw external cells and exact arities.
No expression/statement is lowered in execution. None is horizon exhaustion.
The lowering/correspondence proofs live separately. -/
namespace Solidity.Yul.OpenRun
open Closed
open OpenFunctions (PureEnvironment)

@[noinline] def applyStmt {F X c n} {code : Stmt F X c n}
    (run : PureEnvironment F → Policy.StmtP .A code → WordState X n →
      Option (WordAdapter.Outcome X c n))
    (environment : PureEnvironment F) (policy : Policy.StmtP .A code) (state : WordState X n) :
    Option (WordAdapter.Outcome X c n) := run environment policy state

@[noinline] def applyCases {F X c n} {code : Cases F X c n}
    (run : PureEnvironment F → Policy.CasesP .A code → Word → WordState X n →
      Option (Option (WordAdapter.Outcome X c n)))
    (environment : PureEnvironment F) (policy : Policy.CasesP .A code)
    (selector : Word) (state : WordState X n) : Option (Option (WordAdapter.Outcome X c n)) :=
  run environment policy selector state

mutual
def expression (fuel : Nat) {F X n r} (environment : PureEnvironment F) (code : Expr F X n r) :
    Policy.ExprP .A code → WordState X n → Option (Values r) :=
  match fuel with
  | 0 => fun _ _ => none
  | k+1 => by
    apply Expr.casesOn (motive := fun r code =>
      Policy.ExprP .A code → WordState X n → Option (Values r)) code
    case literal => intro value; exact fun _ _ => some (fun _ => value)
    case «local» => intro index; exact fun _ state => some (fun _ => state.locals index)
    case external =>
      intro ref
      exact fun policy state => some (fun _ => DirectWords.read (ref.wordRead policy) state.cells)
    case builtin =>
      intro a r builtin args
      exact fun policy state => do
        let inputs ← collectValues a (fun i =>
          (expression k environment (args i) (policy.2 i) state).map (fun values => values 0))
        match found : checkWordBuiltin builtin with
        | some operation => pure (operation.eval inputs)
        | none => False.elim (by
            have supported := (checkWordBuiltin_iff builtin).mpr
              ((Policy.builtin_iff .A builtin).mpr policy.1)
            rw [found] at supported
            cases supported)
    case call =>
      intro sig function args
      exact fun policy state => do
        let inputs ← collectValues sig.args (fun i =>
          (expression k environment (args i) (policy i) state).map (fun values => values 0))
        let closure := OpenFunctions.lookup environment function
        let initial : WordState (globals closure.externals) (sig.args+sig.rets) :=
          ⟨Closed.extendValues inputs (fun _ : Fin sig.rets => word 0),
            OpenFunctions.globalCells closure.externals⟩
        let result ← applyStmt (statementNode k closure.body) closure.environment closure.policy initial
        pure (Closed.dropValues sig.args result.state.locals)
termination_by structural fuel

def statementNode (fuel : Nat) {F X c n} (code : Stmt F X c n) :
    PureEnvironment F → Policy.StmtP .A code → WordState X n → Option (WordAdapter.Outcome X c n) :=
  match fuel with
  | 0 => fun _ _ _ => none
  | k+1 => by
    apply Stmt.casesOn (motive_1 := fun F X c n code =>
      PureEnvironment F → Policy.StmtP .A code → WordState X n →
        Option (WordAdapter.Outcome X c n)) code
    case skip =>
      intro F X c n
      exact fun _ _ state => some ⟨state,.normal⟩
    case seq =>
      intro F X c n first second
      exact fun environment policy state => do
        let result ← applyStmt (statementNode k first) environment policy.1 state
        match result.flow with
        | .normal => applyStmt (statementNode k second) environment policy.2 result.state
        | _ => pure result
    case assign =>
      intro F X c n r targets rhs
      exact fun environment policy state => do
        let values ← expression k environment rhs policy.2 state
        pure ⟨DirectUpdates.writeValues r targets policy.1 values state,.normal⟩
    case discard =>
      intro F X c n rhs
      exact fun environment policy state => do
        let _ ← expression k environment rhs policy state
        pure ⟨state,.normal⟩
    case let_ =>
      intro F X c n r rhs body
      exact fun environment policy state => do
        let values ← expression k environment rhs policy.1 state
        let result ← applyStmt (statementNode k body) environment policy.2 (state.extend values)
        pure ⟨result.state.drop r,result.flow⟩
    case zero =>
      intro F X c n r body
      exact fun environment policy state => do
        let result ← applyStmt (statementNode k body) environment policy (state.extend (fun _ : Fin r => word 0))
        pure ⟨result.state.drop r,result.flow⟩
    case if_ =>
      intro F X c n condition body
      exact fun environment policy state => do
        let values ← expression k environment condition policy.1 state
        if (values 0).val = 0 then pure ⟨state,.normal⟩
        else applyStmt (statementNode k body) environment policy.2 state
    case switch =>
      intro F X c n selector arms fallback
      exact fun environment policy state => do
        let values ← expression k environment selector policy.1 state
        let selected ← applyCases (casesNode k arms) environment policy.2.1 (values 0) state
        match selected with
        | some result => pure result
        | none => applyStmt (statementNode k fallback) environment policy.2.2 state
    case for_ =>
      intro F X c n pre condition post body
      exact fun environment policy state => do
        let result ← applyStmt (statementNode k pre) environment policy.1 state
        match result.flow with
        | .normal => loop k environment condition policy.2.1 post policy.2.2.1 body policy.2.2.2 result.state
        | .leave_ legal => pure ⟨result.state,.leave_ legal⟩
        | .break_ impossible => False.elim (by cases impossible)
        | .continue_ impossible => False.elim (by cases impossible)
    case leave =>
      intro F X l n
      exact fun _ _ state => some ⟨state,.leave_ rfl⟩
    case break_ =>
      intro F X f n
      exact fun _ _ state => some ⟨state,.break_ rfl⟩
    case continue_ =>
      intro F X f n
      exact fun _ _ state => some ⟨state,.continue_ rfl⟩
    case functions =>
      intro F X c n signatures bodies rest
      exact fun environment policy state =>
        applyStmt (statementNode k rest) (.group signatures environment bodies policy.1) policy.2 state
termination_by structural fuel

def casesNode (fuel : Nat) {F X c n} (code : Cases F X c n) :
    PureEnvironment F → Policy.CasesP .A code → Word → WordState X n →
      Option (Option (WordAdapter.Outcome X c n)) :=
  match fuel with
  | 0 => fun _ _ _ _ => none
  | k+1 => by
    apply Cases.casesOn (motive_2 := fun F X c n code =>
      PureEnvironment F → Policy.CasesP .A code → Word → WordState X n →
        Option (Option (WordAdapter.Outcome X c n))) code
    case nil =>
      intro F X c n
      exact fun _ _ _ _ => some none
    case cons =>
      intro F X c n label body rest
      exact fun environment policy selector state =>
        if selector = label then
          (applyStmt (statementNode k body) environment policy.1 state).map some
        else applyCases (casesNode k rest) environment policy.2 selector state
termination_by structural fuel

def loop (fuel : Nat) {F X c n} (environment : PureEnvironment F)
    (condition : Expr F X n 1) (hc : Policy.ExprP .A condition)
    (post : Stmt F X ⟨c.function,false⟩ n) (hp : Policy.StmtP .A post)
    (body : Stmt F X ⟨c.function,true⟩ n) (hb : Policy.StmtP .A body)
    (state : WordState X n) : Option (WordAdapter.Outcome X c n) :=
  match fuel with
  | 0 => none
  | k+1 => do
      let values ← expression k environment condition hc state
      if (values 0).val = 0 then pure ⟨state,.normal⟩
      else
        let afterBody := fun next => do
          let result ← applyStmt (statementNode k post) environment hp next
          match result.flow with
          | .normal => loop k environment condition hc post hp body hb result.state
          | .leave_ legal => pure ⟨result.state,.leave_ legal⟩
          | .break_ impossible => False.elim (by cases impossible)
          | .continue_ impossible => False.elim (by cases impossible)
        let result ← applyStmt (statementNode k body) environment hb state
        match result.flow with
        | .normal => afterBody result.state
        | .continue_ _ => afterBody result.state
        | .break_ _ => pure ⟨result.state,.normal⟩
        | .leave_ legal => pure ⟨result.state,.leave_ legal⟩
termination_by structural fuel
end

def statement (fuel : Nat) {F X c n} (environment : PureEnvironment F)
    (code : Stmt F X c n) (policy : Policy.StmtP .A code) (state : WordState X n) :
    Option (WordAdapter.Outcome X c n) :=
  applyStmt (statementNode fuel code) environment policy state

def casesRun (fuel : Nat) {F X c n} (environment : PureEnvironment F)
    (code : Cases F X c n) (policy : Policy.CasesP .A code) (selector : Word) (state : WordState X n) :
    Option (Option (WordAdapter.Outcome X c n)) :=
  applyCases (casesNode fuel code) environment policy selector state

end Solidity.Yul.OpenRun
