import Solidity.Yul.BlockScope
import Solidity.Yul.DeclarationScope
import Solidity.Yul.PlacementCheck

/-! Shared intrinsic block typing across concrete closed/scoped namespaces.
All locals/functions reuse BlockEnvironment. Scope.function advances globals
without an abstract environment/agreement hypothesis. This is static typing,
not Source admission, occurrence provenance, physical/dirty execution or policy. -/
namespace Solidity.Yul.ScopedBlockTyping
open Solidity.Source (Syn Cat)
open Solidity.Yul.BlockTyping (Env)
open Solidity.Yul.BlockScope (Scope)

inductive InitializerD {X F n} (scope : Scope X) (E : Env F n) (count : Nat) :
    Syn (.opt .yulExpr) → Type where
  | zero : InitializerD scope E count .none
  | value {expression} : BlockScope.ExpressionD scope E expression count →
      InitializerD scope E count (.some expression)

mutual
inductive BlockD : {X : List ExternalType} → Scope X →
    {F : List Sig} → {n : Nat} → Env F n → Control → Syn (.list .yulStmt) → Type where
  | intro {X scope F n E c body headers m final} : HeadersD body headers →
      WalkD (F := headers.map Prod.snd ++ F) (n := n)
        scope (Env.hoist E headers) c body (m := m) final →
      BlockD (X := X) (F := F) scope E c body

inductive WalkD : {X : List ExternalType} → Scope X →
    {F : List Sig} → {n : Nat} → Env F n → Control →
    Syn (.list .yulStmt) → {m : Nat} → Env F m → Type where
  | nil {X scope F n E c} : WalkD (X := X) (F := F) (n := n) scope E c .nil E
  | cons {X scope F n E c first rest m next k final} :
      StatementD (X := X) (F := F) (n := n) scope E c first (m := m) next →
      WalkD scope next c rest (m := k) final →
      WalkD scope E c (.cons first rest) final

inductive StatementD : {X : List ExternalType} → Scope X →
    {F : List Sig} → {n : Nat} → Env F n → Control →
    Syn .yulStmt → {m : Nat} → Env F m → Type where
  | block {X scope F n E c body} : BlockD (X := X) (F := F) (n := n) scope E c body →
      StatementD scope E c (.yulBlock body) E
  | declaration {X scope F n E c first rest value} :
      InitializerD (X := X) (F := F) (n := n) scope E (first :: rest).length value →
      StatementD scope E c (.yulLet first rest value) (E.extend (first :: rest))
  | assignment {X scope F n E c first rest value} :
      BlockScope.AssignmentD (X := X) (F := F) (n := n) scope E (first :: rest) value →
      StatementD scope E c (.yulAssign first rest value) E
  | expression {X scope F n E c value} : BlockScope.ExpressionD (X := X) (F := F) (n := n) scope E value 0 →
      StatementD scope E c (.yulExprStmt value) E
  | if_ {X scope F n E c condition body} :
      BlockScope.ExpressionD (X := X) (F := F) (n := n) scope E condition 1 →
      BlockD scope E c body → StatementD scope E c (.yulIf condition body) E
  | for_ {X scope F n E c pre condition post body m initFinal} :
      HeadersD pre [] →
      WalkD (X := X) (F := F) (n := n) scope E ⟨c.function, false⟩ pre (m := m) initFinal →
      BlockScope.ExpressionD scope initFinal condition 1 →
      BlockD scope initFinal ⟨c.function, false⟩ post →
      BlockD scope initFinal ⟨c.function, true⟩ body →
      StatementD scope E c (.yulFor pre condition post body) E
  | switch {X scope F n E c value cases fallback labels} :
      BlockScope.ExpressionD (X := X) (F := F) (n := n) scope E value 1 →
      CasesD scope E c cases labels → labels.Nodup → DefaultD scope E c fallback →
      StatementD scope E c (.yulSwitch value cases fallback) E
  | leave {X scope F n E c} : c.function = true →
      StatementD (X := X) (F := F) (n := n) scope E c .yulLeave E
  | break_ {X scope F n E c} : c.loop = true →
      StatementD (X := X) (F := F) (n := n) scope E c .yulBreak E
  | continue_ {X scope F n E c} : c.loop = true →
      StatementD (X := X) (F := F) (n := n) scope E c .yulContinue E
  | function {X scope F n E c name args rets body} :
      BlockD (F := F) (n := args.length + rets.length) scope.function (Env.frame E args rets)
        ⟨true, false⟩ body →
      StatementD (X := X) (F := F) (n := n) scope E c (.yulFun name args rets body) E

inductive CaseD : {X : List ExternalType} → Scope X →
    {F : List Sig} → {n : Nat} → Env F n → Control → Syn .yulCase → Word → Type where
  | case_ {X scope F n E c literal body w} : LiteralD literal w →
      BlockD (X := X) (F := F) (n := n) scope E c body →
      CaseD scope E c (.yulCase literal body) w

inductive CasesD : {X : List ExternalType} → Scope X →
    {F : List Sig} → {n : Nat} → Env F n → Control → Syn (.list .yulCase) → List Word → Type where
  | nil {X scope F n E c} : CasesD (X := X) (F := F) (n := n) scope E c .nil []
  | cons {X scope F n E c first rest w words} :
      CaseD (X := X) (F := F) (n := n) scope E c first w →
      CasesD scope E c rest words → CasesD scope E c (.cons first rest) (w :: words)

inductive DefaultD : {X : List ExternalType} → Scope X →
    {F : List Sig} → {n : Nat} → Env F n → Control → Syn (.opt (.list .yulStmt)) → Type where
  | none {X scope F n E c} : DefaultD (X := X) (F := F) (n := n) scope E c .none
  | some {X scope F n E c body} : BlockD (X := X) (F := F) (n := n) scope E c body →
      DefaultD scope E c (.some body)
end

variable {X : List ExternalType} (scope : Scope X)

abbrev StatementCheck (term : Syn .yulStmt) :=
  {F : List Sig} → {n : Nat} → (E : Env F n) → (c : Control) →
    Option ((m : Nat) × (final : Env F m) × StatementD scope E c term final)
abbrev WalkCheck (term : Syn (.list .yulStmt)) :=
  {F : List Sig} → {n : Nat} → (E : Env F n) → (c : Control) →
    Option ((m : Nat) × (final : Env F m) × WalkD scope E c term final)

def blockWith {body : Syn (.list .yulStmt)} (walk : WalkCheck scope body)
    {F n} (E : Env F n) (c : Control) : Option (BlockD scope E c body) := do
  let headers := collectHeaders body
  let ⟨_, _, d⟩ ← walk (E.hoist headers) c
  pure (.intro (collectHeaders_sound body) d)

def checkExpr {F n} (E : Env F n) (count : Nat) (expression : Syn .yulExpr) :
    Option (BlockScope.ExpressionD scope E expression count) :=
  BlockScope.checkExpression scope E expression count

theorem checkExpr_complete {X scope F n E expression count}
    (d : @BlockScope.ExpressionD X F n scope E expression count) :
    checkExpr scope E count expression = some d :=
  BlockScope.expression_complete d

def Result (category : Cat) (term : Syn category) : Type :=
  match category with
  | .yulStmt => StatementCheck scope term
  | .list .yulStmt => WalkCheck scope term
  | .yulCase => {F : List Sig} → {n : Nat} → (E : Env F n) → (c : Control) →
      Option ((w : Word) × CaseD scope E c term w)
  | .list .yulCase => {F : List Sig} → {n : Nat} → (E : Env F n) → (c : Control) →
      Option ((words : List Word) × CasesD scope E c term words)
  | .opt (.list .yulStmt) => {F : List Sig} → {n : Nat} → (E : Env F n) →
      (c : Control) → Option (DefaultD scope E c term)
  | .opt .yulExpr => {F : List Sig} → {n : Nat} → (E : Env F n) →
      (count : Nat) → Option (InitializerD scope E count term)
  | _ => Unit

private def nilResult (category : Cat) : Result scope (.list category) .nil := by
  cases category with
  | yulStmt => exact fun _ _ => some ⟨_, _, .nil⟩
  | yulCase => exact fun _ _ => some ⟨[], .nil⟩
  | _ => exact ()

private def consResult {category : Cat} {first : Syn category} {rest : Syn (.list category)}
    (head : Result scope category first) (tail : Result scope (.list category) rest) :
    Result scope (.list category) (.cons first rest) := by
  cases category with
  | yulStmt => exact fun E c => do
      let ⟨_, next, ds⟩ ← head E c
      let ⟨m, final, dt⟩ ← tail next c
      pure ⟨m, final, .cons ds dt⟩
  | yulCase => exact fun E c => do
      let ⟨w, d⟩ ← head E c
      let ⟨words, ds⟩ ← tail E c
      pure ⟨w :: words, .cons d ds⟩
  | _ => exact ()

private def noneResult (category : Cat) : Result scope (.opt category) .none := by
  cases category with
  | yulExpr => exact fun _ _ => some .zero
  | list category =>
      cases category with
      | yulStmt => exact fun _ _ => some .none
      | _ => exact ()
  | _ => exact ()

private def someResult {category : Cat} {body : Syn category} (child : Result scope category body) :
    Result scope (.opt category) (.some body) := by
  revert body child
  apply Cat.casesOn (motive := fun category =>
    (body : Syn category) → Result scope category body → Result scope (.opt category) (.some body)) category
  case yulExpr =>
    intro body child
    exact fun E count => (checkExpr scope E count body).map InitializerD.value
  case list =>
    intro category
    apply Cat.casesOn (motive := fun category =>
      (body : Syn (.list category)) → Result scope (.list category) body →
        Result scope (.opt (.list category)) (.some body)) category
    case yulStmt =>
      intro body child
      exact fun E c => (blockWith scope child E c).map DefaultD.some
    all_goals intros; exact ()
  all_goals intros; exact ()

/-- Keep the environment and count outside the category-dependent result.
This fixed-result executable helper avoids the compiler dropping applications
of arrows hidden inside Result scope at a recursive declaration call. -/
private def InitializerResult {F n} (E : Env F n) (count : Nat)
    (category : Cat) (term : Syn category) : Type :=
  match category with
  | .opt .yulExpr => Option (InitializerD scope E count term)
  | _ => Unit

private def initializerNone {F n} (E : Env F n) (count : Nat) (category : Cat) :
    InitializerResult scope E count (.opt category) .none := by
  apply Cat.casesOn (motive := fun category =>
    InitializerResult scope E count (.opt category) .none) category
  case yulExpr => exact some .zero
  all_goals intros; exact ()

private def initializerSome {F n} (E : Env F n) (count : Nat)
    {category : Cat} (body : Syn category) :
    InitializerResult scope E count (.opt category) (.some body) := by
  revert body
  apply Cat.casesOn (motive := fun category => (body : Syn category) →
    InitializerResult scope E count (.opt category) (.some body)) category
  case yulExpr =>
    intro body
    exact (checkExpr scope E count body).map InitializerD.value
  all_goals intros; exact ()

def checkInitializer {F n} (E : Env F n) (count : Nat)
    (term : Syn (.opt .yulExpr)) : Option (InitializerD scope E count term) := by
  apply Syn.casesOn (motive := fun category term => InitializerResult scope E count category term) term
  case none => intro category; exact initializerNone scope E count category
  case some => intro category body; exact initializerSome scope E count body
  all_goals intros; exact ()

/-- Explicit applications keep arrows hidden in the category-dependent Result scope
visible to the executable compiler. The kernel equations are definitionally
unchanged; noinline preserves the application boundary in generated code. -/
@[noinline] private def applyWalk {body : Syn (.list .yulStmt)}
    (walk : WalkCheck scope body) {F n} (E : Env F n) (c : Control) :
    Option ((m : Nat) × (final : Env F m) × WalkD scope E c body final) :=
  walk E c

@[noinline] private def applyCases {body : Syn (.list .yulCase)}
    (check : {F : List Sig} → {n : Nat} → (E : Env F n) → (c : Control) →
      Option ((labels : List Word) × CasesD scope E c body labels))
    {F n} (E : Env F n) (c : Control) :
    Option ((labels : List Word) × CasesD scope E c body labels) :=
  check E c

@[noinline] private def applyDefault {body : Syn (.opt (.list .yulStmt))}
    (check : {F : List Sig} → {n : Nat} → (E : Env F n) → (c : Control) →
      Option (DefaultD scope E c body))
    {F n} (E : Env F n) (c : Control) : Option (DefaultD scope E c body) :=
  check E c

/-- Original syntax, generalized in its category. New contexts are computed
before checking each original child; no raw intermediate representation exists. -/
def checkNode {X : List ExternalType} (scope : Scope X) {category : Cat} (term : Syn category) : Result scope category term := by
  apply Syn.casesOn (motive := fun category term => Result scope category term) term
  case nil => intro category; exact nilResult scope category
  case cons => intro category first rest
               exact consResult scope (checkNode scope first) (checkNode scope rest)
  case none => intro category; exact noneResult scope category
  case some => intro category body; exact someResult scope (checkNode scope body)
  case yulBlock =>
    intro body
    exact fun E c => do pure ⟨_, E, .block (← blockWith scope (checkNode scope body) E c)⟩
  case yulLet =>
    intro first rest value
    exact fun E c => do
      let d ← checkInitializer scope E (first :: rest).length value
      pure ⟨_, E.extend (first :: rest), .declaration d⟩
  case yulAssign =>
    intro first rest value
    exact fun E c => do
      let d ← BlockScope.checkAssignment scope E (first :: rest) value
      pure ⟨_, E, .assignment d⟩
  case yulExprStmt =>
    intro value
    exact fun E c => do pure ⟨_, E, .expression (← checkExpr scope E 0 value)⟩
  case yulIf =>
    intro condition body
    exact fun E c => do
      let dc ← checkExpr scope E 1 condition
      let db ← blockWith scope (checkNode scope body) E c
      pure ⟨_, E, .if_ dc db⟩
  case yulFor =>
    intro pre condition post body
    exact fun E c =>
      if h : collectHeaders pre = [] then do
        let ⟨_, initFinal, dp⟩ ← applyWalk scope (checkNode scope pre) E ⟨c.function, false⟩
        let dc ← checkExpr scope initFinal 1 condition
        let ds ← blockWith scope (checkNode scope post) initFinal ⟨c.function, false⟩
        let db ← blockWith scope (checkNode scope body) initFinal ⟨c.function, true⟩
        pure ⟨_, E, .for_ (h ▸ collectHeaders_sound pre) dp dc ds db⟩
      else none
  case yulSwitch =>
    intro value cases fallback
    exact fun E c => do
      let dv ← checkExpr scope E 1 value
      let ⟨labels, ds⟩ ← applyCases scope (checkNode scope cases) E c
      if hn : labels.Nodup then
        let dd ← applyDefault scope (checkNode scope fallback) E c
        pure ⟨_, E, .switch dv ds hn dd⟩
      else none
  case yulCase =>
    intro literal body
    exact fun E c => do
      let ⟨w, dl⟩ ← inferLiteral literal
      let db ← blockWith scope (checkNode scope body) E c
      pure ⟨w, .case_ dl db⟩
  case yulLeave =>
    exact fun E c =>
      if h : c.function = true then some ⟨_, E, .leave h⟩ else none
  case yulBreak =>
    exact fun E c =>
      if h : c.loop = true then some ⟨_, E, .break_ h⟩ else none
  case yulContinue =>
    exact fun E c =>
      if h : c.loop = true then some ⟨_, E, .continue_ h⟩ else none
  case yulFun =>
    intro name args rets body
    exact fun E c => do
      let db ← blockWith scope.function (checkNode scope.function body) (E.frame args rets) ⟨true, false⟩
      pure ⟨_, E, .function db⟩
  all_goals intros; exact ()
termination_by structural term

def checkBlock {F n} (E : Env F n) (c : Control) (body : Syn (.list .yulStmt)) :=
  blockWith scope (checkNode scope body) E c

/-- Traversal helper; containing-block function hoisting is a separate entry step. -/
def checkWalk {F n} (E : Env F n) (c : Control) (body : Syn (.list .yulStmt)) :=
  checkNode scope body E c

def checkStatement {F n} (E : Env F n) (c : Control) (term : Syn .yulStmt) :=
  checkNode scope term E c

theorem InitializerD.complete {X scope F n E count term}
    (d : @InitializerD X F n scope E count term) : checkNode scope term E count = some d := by
  cases d with
  | zero => rfl
  | value de =>
      change (checkExpr scope E count _).map _ = _
      rw [checkExpr_complete de]
      rfl

/-- Definitional agreement with the existing initializer judgement/checker;
the compiled declaration path uses the fixed-result helper above. -/
theorem checkInitializer_agrees {F n} (E : Env F n) (count : Nat)
    (term : Syn (.opt .yulExpr)) :
    checkInitializer scope E count term = checkNode scope term E count := by
  cases term <;> rfl

theorem InitializerD.fixed_complete {X scope F n E count term}
    (d : @InitializerD X F n scope E count term) : checkInitializer scope E count term = some d := by
  rw [checkInitializer_agrees, d.complete]

theorem blockWith_complete {X scope F n E c body headers m final}
    (headersD : HeadersD body headers) (walk : WalkCheck scope body)
    (d : @WalkD X scope (headers.map Prod.snd ++ F) n (Env.hoist E headers) c body m final)
    (hw : walk (E.hoist headers) c = some ⟨m, final, d⟩) :
    blockWith scope walk E c = some (.intro headersD d) := by
  have he : collectHeaders body = headers := headersD.complete
  subst headers
  unfold blockWith
  dsimp only
  rw [hw]
  rfl

mutual
theorem BlockD.complete {X scope F n E c body} (d : @BlockD X scope F n E c body) :
    checkBlock scope E c body = some d := by
  apply BlockD.casesOn (motive_1 := fun {X} scope {F} {n} E c body d =>
    checkBlock scope (F := F) (n := n) E c body = some d) d
  intro X scope F n E c body headers m final hd dw
  exact blockWith_complete hd (checkNode scope body) dw dw.complete
termination_by structural d

theorem WalkD.complete {X scope F n E c body m final}
    (d : @WalkD X scope F n E c body m final) :
    checkWalk scope E c body = some ⟨m, final, d⟩ := by
  apply WalkD.casesOn (motive_2 := fun {X} scope {F} {n} E c body {m} final d =>
    checkWalk scope (F := F) (n := n) E c body = some ⟨m, final, d⟩) d
  case nil => intros; rfl
  case cons =>
    intro X scope F n E c first rest m next k final ds dt
    change (do
      let ⟨_, next, ds⟩ ← checkStatement scope E c first
      let ⟨k, final, dt⟩ ← checkWalk scope next c rest
      pure ⟨k, final, WalkD.cons ds dt⟩ :
      Option ((k : Nat) × (out : Env F k) × WalkD scope E c (.cons first rest) out)) = _
    rw [ds.complete]
    change (checkWalk scope next c rest).bind _ = _
    rw [dt.complete]
    rfl
termination_by structural d

theorem StatementD.complete {X scope F n E c term m final}
    (d : @StatementD X scope F n E c term m final) :
    checkStatement scope E c term = some ⟨m, final, d⟩ := by
  apply StatementD.casesOn (motive_3 := fun {X} scope {F} {n} E c term {m} final d =>
    checkStatement scope (F := F) (n := n) E c term = some ⟨m, final, d⟩) d
  case block =>
    intro X scope F n E c body db
    change (do pure ⟨n, E, StatementD.block (← checkBlock scope E c body)⟩ :
      Option ((k : Nat) × (out : Env F k) × StatementD scope E c (.yulBlock body) out)) = _
    rw [db.complete]
    rfl
  case declaration =>
    intro X scope F n E c first rest value di
    change (do
      let di ← checkInitializer scope E (first :: rest).length value
      pure ⟨_, E.extend (first :: rest), StatementD.declaration di⟩ :
      Option ((k : Nat) × (out : Env F k) × StatementD scope E c (.yulLet first rest value) out)) = _
    rw [di.fixed_complete]
    rfl
  case assignment =>
    intro X scope F n E c first rest value da
    change (do pure ⟨n, E, StatementD.assignment
      (← BlockScope.checkAssignment scope E (first :: rest) value)⟩ :
      Option ((k : Nat) × (out : Env F k) × StatementD scope E c (.yulAssign first rest value) out)) = _
    rw [BlockScope.assignment_complete da]
    rfl
  case expression =>
    intro X scope F n E c value de
    change (do pure ⟨n, E, StatementD.expression (← checkExpr scope E 0 value)⟩ :
      Option ((k : Nat) × (out : Env F k) × StatementD scope E c (.yulExprStmt value) out)) = _
    rw [checkExpr_complete de]
    rfl
  case if_ =>
    intro X scope F n E c condition body dc db
    change (do
      let dc ← checkExpr scope E 1 condition
      let db ← checkBlock scope E c body
      pure ⟨n, E, StatementD.if_ dc db⟩ :
      Option ((k : Nat) × (out : Env F k) × StatementD scope E c (.yulIf condition body) out)) = _
    rw [checkExpr_complete dc]
    change (checkBlock scope E c body).bind _ = _
    rw [db.complete]
    rfl
  case for_ =>
    intro X scope F n E c pre condition post body m initFinal hp dp dc ds db
    change (if h : collectHeaders pre = [] then do
      let ⟨_, initFinal, dp⟩ ← checkWalk scope E ⟨c.function, false⟩ pre
      let dc ← checkExpr scope initFinal 1 condition
      let ds ← checkBlock scope initFinal ⟨c.function, false⟩ post
      let db ← checkBlock scope initFinal ⟨c.function, true⟩ body
      pure ⟨n, E, StatementD.for_ (h ▸ collectHeaders_sound pre) dp dc ds db⟩
      else none : Option ((k : Nat) × (out : Env F k) ×
        StatementD scope E c (.yulFor pre condition post body) out)) = _
    rw [dif_pos hp.complete, dp.complete]
    change (checkExpr scope initFinal 1 condition).bind _ = _
    rw [checkExpr_complete dc]
    change (checkBlock scope initFinal ⟨c.function, false⟩ post).bind _ = _
    rw [ds.complete]
    change (checkBlock scope initFinal ⟨c.function, true⟩ body).bind _ = _
    rw [db.complete]
    rfl
  case switch =>
    intro X scope F n E c value cases fallback labels dv ds hn dd
    change (do
      let dv ← checkExpr scope E 1 value
      let ⟨labels, ds⟩ ← checkNode scope cases E c
      if hn : labels.Nodup then
        let dd ← checkNode scope fallback E c
        pure ⟨n, E, StatementD.switch dv ds hn dd⟩
      else none : Option ((k : Nat) × (out : Env F k) ×
        StatementD scope E c (.yulSwitch value cases fallback) out)) = _
    rw [checkExpr_complete dv]
    change (checkNode scope cases E c).bind _ = _
    rw [ds.complete]
    change (if hn : labels.Nodup then
      do
        let dd ← checkNode scope fallback E c
        pure (⟨n, E, StatementD.switch dv ds hn dd⟩ :
          (k : Nat) × (out : Env F k) × StatementD scope E c (.yulSwitch value cases fallback) out)
      else none) = _
    rw [dif_pos hn, dd.complete]
    rfl
  case leave =>
    intro X scope F n E c h
    exact dif_pos h
  case break_ =>
    intro X scope F n E c h
    exact dif_pos h
  case continue_ =>
    intro X scope F n E c h
    exact dif_pos h
  case function =>
    intro X scope F n E c name args rets body db
    change (do pure ⟨n, E, StatementD.function
      (← checkBlock scope.function (E.frame args rets) ⟨true, false⟩ body)⟩ :
      Option ((k : Nat) × (out : Env F k) × StatementD scope E c (.yulFun name args rets body) out)) = _
    rw [db.complete]
    rfl
termination_by structural d

theorem CaseD.complete {X scope F n E c term w} (d : @CaseD X scope F n E c term w) :
    checkNode scope term E c = some ⟨w, d⟩ := by
  apply CaseD.casesOn (motive_4 := fun {X} scope {F} {n} E c term w d =>
    checkNode scope term (F := F) (n := n) E c = some ⟨w, d⟩) d
  intro X scope F n E c literal body w dl db
  change (do
    let ⟨w, dl⟩ ← inferLiteral literal
    let db ← checkBlock scope E c body
    pure ⟨w, CaseD.case_ dl db⟩ : Option ((value : Word) × CaseD scope E c (.yulCase literal body) value)) = _
  rw [dl.complete]
  change (checkBlock scope E c body).bind _ = _
  rw [db.complete]
  rfl
termination_by structural d

theorem CasesD.complete {X scope F n E c term words} (d : @CasesD X scope F n E c term words) :
    checkNode scope term E c = some ⟨words, d⟩ := by
  apply CasesD.casesOn (motive_5 := fun {X} scope {F} {n} E c term words d =>
    checkNode scope term (F := F) (n := n) E c = some ⟨words, d⟩) d
  case nil => intros; rfl
  case cons =>
    intro X scope F n E c first rest w words df dr
    change (do
      let ⟨w, d⟩ ← checkNode scope first E c
      let ⟨words, ds⟩ ← checkNode scope rest E c
      pure ⟨w :: words, CasesD.cons d ds⟩ : Option ((values : List Word) × CasesD scope E c (.cons first rest) values)) = _
    rw [df.complete]
    change (checkNode scope rest E c).bind _ = _
    rw [dr.complete]
    rfl
termination_by structural d

theorem DefaultD.complete {X scope F n E c term} (d : @DefaultD X scope F n E c term) :
    checkNode scope term E c = some d := by
  apply DefaultD.casesOn (motive_6 := fun {X} scope {F} {n} E c term d =>
    checkNode scope term (F := F) (n := n) E c = some d) d
  case none => intros; rfl
  case some =>
    intro X scope F n E c body db
    change (checkBlock scope E c body).map DefaultD.some = _
    rw [db.complete]
    rfl
termination_by structural d
end

theorem checkBlock_iff {F n} (E : Env F n) (c : Control) (body : Syn (.list .yulStmt)) :
    (checkBlock scope E c body).isSome = true ↔ Nonempty (BlockD scope E c body) := by
  constructor
  · intro h
    cases hc : checkBlock scope E c body with
    | none => simp only [hc, Option.isSome] at h; cases h
    | some d => exact ⟨d⟩
  · rintro ⟨d⟩
    rw [d.complete]
    rfl

/-- The same scoped input determines the complete packed typing result,
including the final local count, intrinsic environment and derivation. -/
theorem StatementD.result_unique : ∀ (X : List Solidity.Yul.ExternalType) (scope : Solidity.Yul.BlockScope.Scope X)
 (F : List Solidity.Yul.Sig) (n : Nat) (E : Solidity.Yul.BlockTyping.Env F n)
 (control : Solidity.Yul.Control) (tree : Solidity.Source.Syn .yulStmt) (firstCount secondCount : Nat)
 (firstEnv : Solidity.Yul.BlockTyping.Env F firstCount)
 (secondEnv : Solidity.Yul.BlockTyping.Env F secondCount)
 (first : Solidity.Yul.ScopedBlockTyping.StatementD scope E control tree firstEnv)
 (second : Solidity.Yul.ScopedBlockTyping.StatementD scope E control tree secondEnv),
 (⟨firstCount,firstEnv,first⟩ : (count : Nat) × (final : Solidity.Yul.BlockTyping.Env F count) ×
 Solidity.Yul.ScopedBlockTyping.StatementD scope E control tree final) = ⟨secondCount,secondEnv,second⟩ := by
  intro X scope F n E control tree firstCount secondCount firstEnv secondEnv first second
  exact Option.some.inj ((StatementD.complete first).symm.trans (StatementD.complete second))

/-- The same scoped input determines the complete packed typing result,
including the final local count, intrinsic environment and derivation. -/
theorem WalkD.result_unique : ∀ (X : List Solidity.Yul.ExternalType) (scope : Solidity.Yul.BlockScope.Scope X)
 (F : List Solidity.Yul.Sig) (n : Nat) (E : Solidity.Yul.BlockTyping.Env F n)
 (control : Solidity.Yul.Control) (tree : Solidity.Source.Syn (.list .yulStmt)) (firstCount secondCount : Nat)
 (firstEnv : Solidity.Yul.BlockTyping.Env F firstCount)
 (secondEnv : Solidity.Yul.BlockTyping.Env F secondCount)
 (first : Solidity.Yul.ScopedBlockTyping.WalkD scope E control tree firstEnv)
 (second : Solidity.Yul.ScopedBlockTyping.WalkD scope E control tree secondEnv),
 (⟨firstCount,firstEnv,first⟩ : (count : Nat) × (final : Solidity.Yul.BlockTyping.Env F count) ×
 Solidity.Yul.ScopedBlockTyping.WalkD scope E control tree final) = ⟨secondCount,secondEnv,second⟩ := by
  intro X scope F n E control tree firstCount secondCount firstEnv secondEnv first second
  exact Option.some.inj ((WalkD.complete first).symm.trans (WalkD.complete second))

/-- The same scoped case syntax determines its packed labels and derivation.
This is result determinism, not a distinct-label assertion. -/
theorem CaseD.result_unique : ∀ (X : List Solidity.Yul.ExternalType) (scope : Solidity.Yul.BlockScope.Scope X)
 (F : List Solidity.Yul.Sig) (n : Nat) (E : Solidity.Yul.BlockTyping.Env F n)
 (control : Solidity.Yul.Control) (tree : Solidity.Source.Syn .yulCase) (firstValue secondValue : Solidity.Yul.Word)
 (first : Solidity.Yul.ScopedBlockTyping.CaseD scope E control tree firstValue)
 (second : Solidity.Yul.ScopedBlockTyping.CaseD scope E control tree secondValue),
 (⟨firstValue,first⟩ : (value : Solidity.Yul.Word) × Solidity.Yul.ScopedBlockTyping.CaseD scope E control tree value) = ⟨secondValue,second⟩ := by
  intro X scope F n E control tree firstValue secondValue first second
  exact Option.some.inj ((CaseD.complete first).symm.trans (CaseD.complete second))

/-- The same scoped case syntax determines its packed labels and derivation.
This is result determinism, not a distinct-label assertion. -/
theorem CasesD.result_unique : ∀ (X : List Solidity.Yul.ExternalType) (scope : Solidity.Yul.BlockScope.Scope X)
 (F : List Solidity.Yul.Sig) (n : Nat) (E : Solidity.Yul.BlockTyping.Env F n)
 (control : Solidity.Yul.Control) (tree : Solidity.Source.Syn (.list .yulCase)) (firstValue secondValue : List Solidity.Yul.Word)
 (first : Solidity.Yul.ScopedBlockTyping.CasesD scope E control tree firstValue)
 (second : Solidity.Yul.ScopedBlockTyping.CasesD scope E control tree secondValue),
 (⟨firstValue,first⟩ : (value : List Solidity.Yul.Word) × Solidity.Yul.ScopedBlockTyping.CasesD scope E control tree value) = ⟨secondValue,second⟩ := by
  intro X scope F n E control tree firstValue secondValue first second
  exact Option.some.inj ((CasesD.complete first).symm.trans (CasesD.complete second))

/-- The fixed scoped checker input determines its entire derivation.
All syntax and context indices remain explicit. -/
theorem DefaultD.unique : ∀ (X : List Solidity.Yul.ExternalType) (scope : Solidity.Yul.BlockScope.Scope X)
 (F : List Solidity.Yul.Sig) (n : Nat) (E : Solidity.Yul.BlockTyping.Env F n) (control : Solidity.Yul.Control) (tree : Solidity.Source.Syn (.opt (.list .yulStmt)))
 (first second : Solidity.Yul.ScopedBlockTyping.DefaultD scope E control tree), first = second := by
  intro X scope F n E index tree first second
  exact Option.some.inj ((DefaultD.complete first).symm.trans (DefaultD.complete second))

/-- The fixed scoped checker input determines its entire derivation.
All syntax and context indices remain explicit. -/
theorem InitializerD.unique : ∀ (X : List Solidity.Yul.ExternalType) (scope : Solidity.Yul.BlockScope.Scope X)
 (F : List Solidity.Yul.Sig) (n : Nat) (E : Solidity.Yul.BlockTyping.Env F n) (count : Nat) (tree : Solidity.Source.Syn (.opt .yulExpr))
 (first second : Solidity.Yul.ScopedBlockTyping.InitializerD scope E count tree), first = second := by
  intro X scope F n E index tree first second
  exact Option.some.inj ((InitializerD.fixed_complete first).symm.trans (InitializerD.fixed_complete second))

/-- Exact reconstruction makes the independent typing certificate unique.
This is about BlockTyping certificates, not the older separate ClosedPure
certificate-uniqueness draft. -/
theorem BlockD.unique {X scope F n E c body} (first second : @BlockD X scope F n E c body) :
    first = second :=
  Option.some.inj (first.complete.symm.trans second.complete)

end Solidity.Yul.ScopedBlockTyping
