import Solidity.Yul.ScopedBlockTyping

/-! Static typing sites observed from the ACTUAL existing block derivation.
These are dependent metadata retaining original syntax and typing certificates,
not a new program AST or checker. Expression/assignment sites are not yet
individual variable leaves, JSON positions, metadata accounting or admission. -/
namespace Solidity.Yul.TypingSites
open Solidity.Source (Syn)
open Solidity.Yul.BlockTyping (Env)
open Solidity.Yul.BlockScope (Scope)
open Solidity.Yul.ScopedBlockTyping

inductive Edge where
  | blockBody | first | rest | initializer | assignment | expression
  | condition | body | pre | post | selector | cases | fallback | functionBody | caseBody
  deriving DecidableEq, Repr

/-- Every payload retains its actual scope, local/function environment,
original grammar subtree and existing intrinsic typing certificate. -/
inductive Site where
  | expression {X F n} (scope : Scope X) (environment : Env F n)
      (tree : Syn .yulExpr) (arity : Nat) (typed : BlockScope.ExpressionD scope environment tree arity)
  | assignment {X F n} (scope : Scope X) (environment : Env F n)
      (paths : List (List String)) (rhs : Syn .yulExpr)
      (typed : BlockScope.AssignmentD scope environment paths rhs)

abbrev Path := List Edge
abbrev Trace := List (Path × Site)

def All (predicate : Path → Site → Prop) (trace : Trace) : Prop :=
  ∀ entry ∈ trace, predicate entry.1 entry.2

private theorem all_nil (predicate : Path → Site → Prop) : All predicate [] ↔ True := by
  constructor
  · intro _; exact True.intro
  · intro _ entry impossible; cases impossible

private theorem all_one (predicate : Path → Site → Prop) (path : Path) (site : Site) :
    All predicate [(path,site)] ↔ predicate path site := by
  constructor
  · intro all; exact all (path,site) List.mem_cons_self
  · intro yes entry present
    rcases List.mem_cons.mp present with same | impossible
    · cases same; exact yes
    · cases impossible

private theorem all_append (predicate : Path → Site → Prop) (left right : Trace) :
    All predicate (left++right) ↔ All predicate left ∧ All predicate right := by
  constructor
  · intro all
    exact ⟨fun entry present => all entry (List.mem_append_left _ present),
      fun entry present => all entry (List.mem_append_right _ present)⟩
  · rintro ⟨leftAll,rightAll⟩ entry present
    rcases List.mem_append.mp present with fromLeft | fromRight
    · exact leftAll entry fromLeft
    · exact rightAll entry fromRight

mutual
def initializer {X F n scope E count term} (d : @InitializerD X F n scope E count term) : Path → Trace := by
  apply InitializerD.casesOn (motive := fun term _ => Path → Trace) d
  case zero =>
    intro  path
    exact []
  case value =>
    intro expression typed path
    exact [(path++[.initializer],.expression scope E expression count typed)]

def block {X scope F n E c body} (d : @BlockD X scope F n E c body) : Path → Trace := by
  apply BlockD.casesOn (motive_1 := fun {X} scope {F} {n} E c body _ => Path → Trace) d
  intro X scope F n E c body headers m final hd dw path
  exact walk dw (path++[.blockBody])
termination_by structural d

def walk {X scope F n E c body m final} (d : @WalkD X scope F n E c body m final) : Path → Trace := by
  apply WalkD.casesOn (motive_2 := fun {X} scope {F} {n} E c body {m} final _ => Path → Trace) d
  case nil =>
    intro X scope F n E c path
    exact []
  case cons =>
    intro X scope F n E c first rest m next k final ds dt path
    exact statement ds (path++[.first]) ++ walk dt (path++[.rest])
termination_by structural d

def statement {X scope F n E c term m final} (d : @StatementD X scope F n E c term m final) : Path → Trace := by
  apply StatementD.casesOn (motive_3 := fun {X} scope {F} {n} E c term {m} final _ => Path → Trace) d
  case block =>
    intro X scope F n E c body db path
    exact block db (path++[.body])
  case declaration =>
    intro X scope F n E c first rest value di path
    exact initializer di path
  case assignment =>
    intro X scope F n E c first rest value da path
    exact [(path++[.assignment],.assignment scope E (first::rest) value da)]
  case expression =>
    intro X scope F n E c value de path
    exact [(path++[.expression],.expression scope E value 0 de)]
  case if_ =>
    intro X scope F n E c condition body dc db path
    exact [(path++[.condition],.expression scope E condition 1 dc)] ++ block db (path++[.body])
  case for_ =>
    intro X scope F n E c pre condition post body m initFinal hp dp dc ds db path
    exact walk dp (path++[.pre]) ++ [(path++[.condition],.expression scope initFinal condition 1 dc)] ++ block ds (path++[.post]) ++ block db (path++[.body])
  case switch =>
    intro X scope F n E c value cases fallback labels dv ds hn dd path
    exact [(path++[.selector],.expression scope E value 1 dv)] ++ casesTrace ds (path++[.cases]) ++ defaultTrace dd (path++[.fallback])
  case leave =>
    intro X scope F n E c permitted path
    exact []
  case break_ =>
    intro X scope F n E c permitted path
    exact []
  case continue_ =>
    intro X scope F n E c permitted path
    exact []
  case function =>
    intro X scope F n E c name args rets body df path
    exact block df (path++[.functionBody])
termination_by structural d

def caseTrace {X scope F n E c term w} (d : @CaseD X scope F n E c term w) : Path → Trace := by
  apply CaseD.casesOn (motive_4 := fun {X} scope {F} {n} E c term w _ => Path → Trace) d
  intro X scope F n E c literal body w dl db path
  exact block db (path++[.caseBody])
termination_by structural d

def casesTrace {X scope F n E c terms words} (d : @CasesD X scope F n E c terms words) : Path → Trace := by
  apply CasesD.casesOn (motive_5 := fun {X} scope {F} {n} E c terms words _ => Path → Trace) d
  case nil =>
    intro X scope F n E c path
    exact []
  case cons =>
    intro X scope F n E c first rest w words ds dt path
    exact caseTrace ds (path++[.first]) ++ casesTrace dt (path++[.rest])
termination_by structural d

def defaultTrace {X scope F n E c term} (d : @DefaultD X scope F n E c term) : Path → Trace := by
  apply DefaultD.casesOn (motive_6 := fun {X} scope {F} {n} E c term _ => Path → Trace) d
  case none =>
    intro X scope F n E c path
    exact []
  case some =>
    intro X scope F n E c body db path
    exact block db (path++[.body])
termination_by structural d

end

mutual
def everyInitializer {X F n scope E count term} (d : @InitializerD X F n scope E count term) : Path → (Path → Site → Prop) → Prop := by
  apply InitializerD.casesOn (motive := fun term _ => Path → (Path → Site → Prop) → Prop) d
  case zero =>
    intro  path predicate
    exact True
  case value =>
    intro expression typed path predicate
    exact predicate (path++[.initializer]) (.expression scope E expression count typed)

def everyBlock {X scope F n E c body} (d : @BlockD X scope F n E c body) : Path → (Path → Site → Prop) → Prop := by
  apply BlockD.casesOn (motive_1 := fun {X} scope {F} {n} E c body _ => Path → (Path → Site → Prop) → Prop) d
  intro X scope F n E c body headers m final hd dw path predicate
  exact everyWalk dw (path++[.blockBody]) predicate
termination_by structural d

def everyWalk {X scope F n E c body m final} (d : @WalkD X scope F n E c body m final) : Path → (Path → Site → Prop) → Prop := by
  apply WalkD.casesOn (motive_2 := fun {X} scope {F} {n} E c body {m} final _ => Path → (Path → Site → Prop) → Prop) d
  case nil =>
    intro X scope F n E c path predicate
    exact True
  case cons =>
    intro X scope F n E c first rest m next k final ds dt path predicate
    exact everyStatement ds (path++[.first]) predicate ∧ everyWalk dt (path++[.rest]) predicate
termination_by structural d

def everyStatement {X scope F n E c term m final} (d : @StatementD X scope F n E c term m final) : Path → (Path → Site → Prop) → Prop := by
  apply StatementD.casesOn (motive_3 := fun {X} scope {F} {n} E c term {m} final _ => Path → (Path → Site → Prop) → Prop) d
  case block =>
    intro X scope F n E c body db path predicate
    exact everyBlock db (path++[.body]) predicate
  case declaration =>
    intro X scope F n E c first rest value di path predicate
    exact everyInitializer di path predicate
  case assignment =>
    intro X scope F n E c first rest value da path predicate
    exact predicate (path++[.assignment]) (.assignment scope E (first::rest) value da)
  case expression =>
    intro X scope F n E c value de path predicate
    exact predicate (path++[.expression]) (.expression scope E value 0 de)
  case if_ =>
    intro X scope F n E c condition body dc db path predicate
    exact predicate (path++[.condition]) (.expression scope E condition 1 dc) ∧ everyBlock db (path++[.body]) predicate
  case for_ =>
    intro X scope F n E c pre condition post body m initFinal hp dp dc ds db path predicate
    exact ((everyWalk dp (path++[.pre]) predicate ∧ predicate (path++[.condition]) (.expression scope initFinal condition 1 dc)) ∧ everyBlock ds (path++[.post]) predicate) ∧ everyBlock db (path++[.body]) predicate
  case switch =>
    intro X scope F n E c value cases fallback labels dv ds hn dd path predicate
    exact (predicate (path++[.selector]) (.expression scope E value 1 dv) ∧ everyCases ds (path++[.cases]) predicate) ∧ everyDefault dd (path++[.fallback]) predicate
  case leave =>
    intro X scope F n E c permitted path predicate
    exact True
  case break_ =>
    intro X scope F n E c permitted path predicate
    exact True
  case continue_ =>
    intro X scope F n E c permitted path predicate
    exact True
  case function =>
    intro X scope F n E c name args rets body df path predicate
    exact everyBlock df (path++[.functionBody]) predicate
termination_by structural d

def everyCase {X scope F n E c term w} (d : @CaseD X scope F n E c term w) : Path → (Path → Site → Prop) → Prop := by
  apply CaseD.casesOn (motive_4 := fun {X} scope {F} {n} E c term w _ => Path → (Path → Site → Prop) → Prop) d
  intro X scope F n E c literal body w dl db path predicate
  exact everyBlock db (path++[.caseBody]) predicate
termination_by structural d

def everyCases {X scope F n E c terms words} (d : @CasesD X scope F n E c terms words) : Path → (Path → Site → Prop) → Prop := by
  apply CasesD.casesOn (motive_5 := fun {X} scope {F} {n} E c terms words _ => Path → (Path → Site → Prop) → Prop) d
  case nil =>
    intro X scope F n E c path predicate
    exact True
  case cons =>
    intro X scope F n E c first rest w words ds dt path predicate
    exact everyCase ds (path++[.first]) predicate ∧ everyCases dt (path++[.rest]) predicate
termination_by structural d

def everyDefault {X scope F n E c term} (d : @DefaultD X scope F n E c term) : Path → (Path → Site → Prop) → Prop := by
  apply DefaultD.casesOn (motive_6 := fun {X} scope {F} {n} E c term _ => Path → (Path → Site → Prop) → Prop) d
  case none =>
    intro X scope F n E c path predicate
    exact True
  case some =>
    intro X scope F n E c body db path predicate
    exact everyBlock db (path++[.body]) predicate
termination_by structural d

end

mutual
theorem all_initializer {X F n scope E count term} (d : @InitializerD X F n scope E count term) (path : Path)
    (predicate : Path → Site → Prop) :
    All predicate (initializer d path) ↔ everyInitializer d path predicate := by
  revert path
  apply InitializerD.casesOn (motive := fun term d => ∀ path, All predicate (initializer d path) ↔ everyInitializer d path predicate) d
  case zero =>
    intro  path
    change All predicate ([]) ↔ True
    simp only [all_nil]
  case value =>
    intro expression typed path
    change All predicate ([(path++[.initializer],.expression scope E expression count typed)]) ↔ predicate (path++[.initializer]) (.expression scope E expression count typed)
    simp only [all_one]

theorem all_block {X scope F n E c body} (d : @BlockD X scope F n E c body) (path : Path)
    (predicate : Path → Site → Prop) :
    All predicate (block d path) ↔ everyBlock d path predicate := by
  revert path
  apply BlockD.casesOn (motive_1 := fun {X} scope {F} {n} E c body d => ∀ path, All predicate (block d path) ↔ everyBlock d path predicate) d
  intro X scope F n E c body headers m final hd dw path
  change All predicate (walk dw (path++[.blockBody])) ↔ everyWalk dw (path++[.blockBody]) predicate
  simp only [all_walk dw (path++[.blockBody]) predicate]
termination_by structural d

theorem all_walk {X scope F n E c body m final} (d : @WalkD X scope F n E c body m final) (path : Path)
    (predicate : Path → Site → Prop) :
    All predicate (walk d path) ↔ everyWalk d path predicate := by
  revert path
  apply WalkD.casesOn (motive_2 := fun {X} scope {F} {n} E c body {m} final d => ∀ path, All predicate (walk d path) ↔ everyWalk d path predicate) d
  case nil =>
    intro X scope F n E c path
    change All predicate ([]) ↔ True
    simp only [all_nil]
  case cons =>
    intro X scope F n E c first rest m next k final ds dt path
    change All predicate (statement ds (path++[.first]) ++ walk dt (path++[.rest])) ↔ everyStatement ds (path++[.first]) predicate ∧ everyWalk dt (path++[.rest]) predicate
    simp only [all_append,all_statement ds (path++[.first]) predicate,all_walk dt (path++[.rest]) predicate]
termination_by structural d

theorem all_statement {X scope F n E c term m final} (d : @StatementD X scope F n E c term m final) (path : Path)
    (predicate : Path → Site → Prop) :
    All predicate (statement d path) ↔ everyStatement d path predicate := by
  revert path
  apply StatementD.casesOn (motive_3 := fun {X} scope {F} {n} E c term {m} final d => ∀ path, All predicate (statement d path) ↔ everyStatement d path predicate) d
  case block =>
    intro X scope F n E c body db path
    change All predicate (block db (path++[.body])) ↔ everyBlock db (path++[.body]) predicate
    simp only [all_block db (path++[.body]) predicate]
  case declaration =>
    intro X scope F n E c first rest value di path
    change All predicate (initializer di path) ↔ everyInitializer di path predicate
    simp only [all_initializer di path predicate]
  case assignment =>
    intro X scope F n E c first rest value da path
    change All predicate ([(path++[.assignment],.assignment scope E (first::rest) value da)]) ↔ predicate (path++[.assignment]) (.assignment scope E (first::rest) value da)
    simp only [all_one]
  case expression =>
    intro X scope F n E c value de path
    change All predicate ([(path++[.expression],.expression scope E value 0 de)]) ↔ predicate (path++[.expression]) (.expression scope E value 0 de)
    simp only [all_one]
  case if_ =>
    intro X scope F n E c condition body dc db path
    change All predicate ([(path++[.condition],.expression scope E condition 1 dc)] ++ block db (path++[.body])) ↔ predicate (path++[.condition]) (.expression scope E condition 1 dc) ∧ everyBlock db (path++[.body]) predicate
    simp only [all_append,all_one,all_block db (path++[.body]) predicate]
  case for_ =>
    intro X scope F n E c pre condition post body m initFinal hp dp dc ds db path
    change All predicate (walk dp (path++[.pre]) ++ [(path++[.condition],.expression scope initFinal condition 1 dc)] ++ block ds (path++[.post]) ++ block db (path++[.body])) ↔ ((everyWalk dp (path++[.pre]) predicate ∧ predicate (path++[.condition]) (.expression scope initFinal condition 1 dc)) ∧ everyBlock ds (path++[.post]) predicate) ∧ everyBlock db (path++[.body]) predicate
    simp only [all_append,all_one,and_assoc,all_walk dp (path++[.pre]) predicate,all_block ds (path++[.post]) predicate,all_block db (path++[.body]) predicate]
  case switch =>
    intro X scope F n E c value cases fallback labels dv ds hn dd path
    change All predicate ([(path++[.selector],.expression scope E value 1 dv)] ++ casesTrace ds (path++[.cases]) ++ defaultTrace dd (path++[.fallback])) ↔ (predicate (path++[.selector]) (.expression scope E value 1 dv) ∧ everyCases ds (path++[.cases]) predicate) ∧ everyDefault dd (path++[.fallback]) predicate
    simp only [all_append,all_one,and_assoc,all_casesTrace ds (path++[.cases]) predicate,all_defaultTrace dd (path++[.fallback]) predicate]
  case leave =>
    intro X scope F n E c permitted path
    change All predicate ([]) ↔ True
    simp only [all_nil]
  case break_ =>
    intro X scope F n E c permitted path
    change All predicate ([]) ↔ True
    simp only [all_nil]
  case continue_ =>
    intro X scope F n E c permitted path
    change All predicate ([]) ↔ True
    simp only [all_nil]
  case function =>
    intro X scope F n E c name args rets body df path
    change All predicate (block df (path++[.functionBody])) ↔ everyBlock df (path++[.functionBody]) predicate
    simp only [all_block df (path++[.functionBody]) predicate]
termination_by structural d

theorem all_caseTrace {X scope F n E c term w} (d : @CaseD X scope F n E c term w) (path : Path)
    (predicate : Path → Site → Prop) :
    All predicate (caseTrace d path) ↔ everyCase d path predicate := by
  revert path
  apply CaseD.casesOn (motive_4 := fun {X} scope {F} {n} E c term w d => ∀ path, All predicate (caseTrace d path) ↔ everyCase d path predicate) d
  intro X scope F n E c literal body w dl db path
  change All predicate (block db (path++[.caseBody])) ↔ everyBlock db (path++[.caseBody]) predicate
  simp only [all_block db (path++[.caseBody]) predicate]
termination_by structural d

theorem all_casesTrace {X scope F n E c terms words} (d : @CasesD X scope F n E c terms words) (path : Path)
    (predicate : Path → Site → Prop) :
    All predicate (casesTrace d path) ↔ everyCases d path predicate := by
  revert path
  apply CasesD.casesOn (motive_5 := fun {X} scope {F} {n} E c terms words d => ∀ path, All predicate (casesTrace d path) ↔ everyCases d path predicate) d
  case nil =>
    intro X scope F n E c path
    change All predicate ([]) ↔ True
    simp only [all_nil]
  case cons =>
    intro X scope F n E c first rest w words ds dt path
    change All predicate (caseTrace ds (path++[.first]) ++ casesTrace dt (path++[.rest])) ↔ everyCase ds (path++[.first]) predicate ∧ everyCases dt (path++[.rest]) predicate
    simp only [all_append,all_caseTrace ds (path++[.first]) predicate,all_casesTrace dt (path++[.rest]) predicate]
termination_by structural d

theorem all_defaultTrace {X scope F n E c term} (d : @DefaultD X scope F n E c term) (path : Path)
    (predicate : Path → Site → Prop) :
    All predicate (defaultTrace d path) ↔ everyDefault d path predicate := by
  revert path
  apply DefaultD.casesOn (motive_6 := fun {X} scope {F} {n} E c term d => ∀ path, All predicate (defaultTrace d path) ↔ everyDefault d path predicate) d
  case none =>
    intro X scope F n E c path
    change All predicate ([]) ↔ True
    simp only [all_nil]
  case some =>
    intro X scope F n E c body db path
    change All predicate (block db (path++[.body])) ↔ everyBlock db (path++[.body]) predicate
    simp only [all_block db (path++[.body]) predicate]
termination_by structural d

end

/-- Executable context metadata for controls and consumers. It cannot execute a
program or erase a typed site's original derivation. -/
structure View where
  locals : List (String × Nat)
  functions : List String
  slots : Nat
  externalTypes : Nat
  arity : Nat
  write : Bool
  /-- ExternalScope projection only: closed function bodies remain closed. -/
  externalFunctionScope : Bool
  deriving DecidableEq, Repr

def scopeFunction {X} (scope : Scope X) : Bool := by
  apply Scope.casesOn (motive := fun _ _ => Bool) scope
  case closed => exact false
  case external => intro root X decls input original; exact original.inFunction

def Site.view (site : Site) : View :=
  match site with
  | .expression (X := X) (n := n) scope E _ arity _ =>
      ⟨E.locals.map (fun binding => (binding.1,binding.2.val)),
        E.functions.map Prod.fst,n,X.length,arity,false,scopeFunction scope⟩
  | .assignment (X := X) (n := n) scope E paths _ _ =>
      ⟨E.locals.map (fun binding => (binding.1,binding.2.val)),
        E.functions.map Prod.fst,n,X.length,paths.length,true,scopeFunction scope⟩

def Site.accepted (site : Site) : Bool :=
  match site with
  | .expression scope E tree arity _ =>
      (BlockScope.checkExpression scope E tree arity).isSome
  | .assignment scope E paths rhs _ =>
      (BlockScope.checkAssignment scope E paths rhs).isSome

theorem Site.accepted_true (site : Site) : site.accepted = true := by
  cases site with
  | expression scope E tree arity typed =>
      simp only [Site.accepted,BlockScope.expression_complete typed,Option.isSome_some]
  | assignment scope E paths rhs typed =>
      simp only [Site.accepted,BlockScope.assignment_complete typed,Option.isSome_some]

end Solidity.Yul.TypingSites
