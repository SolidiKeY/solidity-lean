import Solidity.Yul.BlockTyping

/-!
# Intrinsic extraction of shared scoped Yul typing

The source derivation is indexed by concrete external scopes, actual local/
function contexts and original syntax. The closed entry points specialize the
same implementation; they do not maintain a second extractor.
Every result below is the existing context/control/arity-indexed Yul AST.
Continuation splicing keeps loop-init binders around the loop, not in its
context-preserving pre field. Empty continuations/functions do not add dummy
sequence/function nodes. No Source execution or compiler correspondence is
asserted by constructing this intrinsic code.
-/
namespace Solidity.Yul.BlockTyping
open Solidity.Source (Syn)

structure ControlMap (source target : Control) : Prop where
  sameFunction : source.function = target.function
  loop : source.loop = true → target.loop = true

def ControlMap.refl (c : Control) : ControlMap c c := ⟨rfl, id⟩
def ControlMap.init {source target} (h : ControlMap source target) :
    ControlMap ⟨source.function, false⟩ target :=
  ⟨h.sameFunction, fun bad => Bool.noConfusion bad⟩
def ControlMap.post {source target} (h : ControlMap source target) :
    ControlMap ⟨source.function, false⟩ ⟨target.function, false⟩ :=
  ⟨h.sameFunction, fun bad => Bool.noConfusion bad⟩
def ControlMap.body {source target} (h : ControlMap source target) :
    ControlMap ⟨source.function, true⟩ ⟨target.function, true⟩ :=
  ⟨h.sameFunction, fun _ => rfl⟩

end Solidity.Yul.BlockTyping

namespace Solidity.Yul.ScopedBlockTyping
open Solidity.Source (Syn)
open Solidity.Yul.BlockTyping (ControlMap)

def leaveAt {F X n} (c : Control) (h : c.function = true) : Stmt F X c n := by
  cases c with
  | mk f l =>
      cases f with
      | false => cases h
      | true => exact .leave
def breakAt {F X n} (c : Control) (h : c.loop = true) : Stmt F X c n := by
  cases c with
  | mk f l =>
      cases l with
      | false => cases h
      | true => exact .break_
def continueAt {F X n} (c : Control) (h : c.loop = true) : Stmt F X c n := by
  cases c with
  | mk f l =>
      cases l with
      | false => cases h
      | true => exact .continue_

/-- Option is continuation metadata over the EXISTING intrinsic AST. None is
the absence of subsequent executable syntax, never an unknown program. -/
def appendCode {F X c n} (first : Stmt F X c n) :
    Option (Stmt F X c n) → Option (Stmt F X c n)
  | none => some first
  | some rest => some (.seq first rest)

/-- Empty lexical function groups require no runtime administrative node. -/
def closeFunctions {F X c n} (signatures : List Sig) :
    Bodies (signatures ++ F) (globals X) signatures →
      Stmt (signatures ++ F) X c n → Stmt F X c n :=
  match signatures with
  | [] => fun _ code => code
  | first :: rest => fun bodies code => .functions (first :: rest) bodies code

def InitializerD.prefix {X scope F n E count term}
    (d : @InitializerD X F n scope E count term) (c : Control) :
    Stmt F X c (count + n) → Stmt F X c n := by
  apply InitializerD.casesOn (motive := fun _ _ =>
    Stmt F X c (count + n) → Stmt F X c n) d
  case zero => exact fun rest => .zero count rest
  case value => intro expression de; exact fun rest => .let_ count (BlockScope.expressionTerm de) rest

mutual
/-- Real bodies are extracted in exact source-header order. -/
def BlockD.codeAt {X scope F n E c body} (d : @BlockD X scope F n E c body) (target : Control)
    (h : ControlMap c target) : Stmt F X target n := by
  revert target h
  apply BlockD.casesOn (motive_1 := fun {X} scope {F} {n} E c body _ =>
    (target : Control) → ControlMap c target → Stmt F X target n) d
  intro X scope F n E c body headers m final hd dw target h
  have same : collectHeaders body = headers := hd.complete
  let definitions : Bodies (headers.map Prod.snd ++ F) (globals X) (headers.map Prod.snd) :=
    same ▸ dw.bodies
  exact closeFunctions (headers.map Prod.snd) definitions
    ((dw.splice target h none).getD .skip)
termination_by structural d

/-- Declared locals own the remaining continuation. The typed final context is
the continuation's context, including all DIRECT loop-init declarations. -/
def WalkD.splice {X scope F n E c body m final} (d : @WalkD X scope F n E c body m final)
    (target : Control) (h : ControlMap c target) :
    Option (Stmt F X target m) → Option (Stmt F X target n) := by
  revert target h
  apply WalkD.casesOn (motive_2 := fun {X} scope {F} {n} E c body {m} final _ =>
    (target : Control) → ControlMap c target →
      Option (Stmt F X target m) → Option (Stmt F X target n)) d
  case nil => intro X scope F n E c target h rest; exact rest
  case cons =>
    intro X scope F n E c first rest m next k final ds dt target h continuation
    exact ds.splice target h (dt.splice target h continuation)
termination_by structural d

def StatementD.splice {X scope F n E c term m final} (d : @StatementD X scope F n E c term m final)
    (target : Control) (h : ControlMap c target) :
    Option (Stmt F X target m) → Option (Stmt F X target n) := by
  revert target h
  apply StatementD.casesOn (motive_3 := fun {X} scope {F} {n} E c term {m} final _ =>
    (target : Control) → ControlMap c target →
      Option (Stmt F X target m) → Option (Stmt F X target n)) d
  case block =>
    intro X scope F n E c body db target h rest
    exact appendCode (db.codeAt target h) rest
  case declaration =>
    intro X scope F n E c first rest value di target h continuation
    exact some (di.prefix target (continuation.getD .skip))
  case assignment =>
    intro X scope F n E c first rest value da target h continuation
    exact appendCode (BlockScope.assignmentStatement da target) continuation
  case expression =>
    intro X scope F n E c value de target h rest
    exact appendCode (.discard (BlockScope.expressionTerm de)) rest
  case if_ =>
    intro X scope F n E c condition body dc db target h rest
    exact appendCode (.if_ (BlockScope.expressionTerm dc) (db.codeAt target h)) rest
  case for_ =>
    intro X scope F n E c pre condition post body m initFinal hp dp dc ds db target h rest
    let loop : Stmt F X target m :=
      .for_ .skip (BlockScope.expressionTerm dc)
        (ds.codeAt ⟨target.function, false⟩ h.post)
        (db.codeAt ⟨target.function, true⟩ h.body)
    -- A nonempty loop continuation is never dropped; splice_some below proves
    -- the getD default here unreachable. This is not a prerequisite stub.
    let started : Stmt F X target n :=
      (dp.splice target h.init (some loop)).getD .skip
    exact appendCode started rest
  case switch =>
    intro X scope F n E c value cases fallback labels dv ds hn dd target h rest
    exact appendCode (.switch (BlockScope.expressionTerm dv) (ds.codeAt target h) (dd.codeAt target h)) rest
  case leave =>
    intro X scope F n E c hl target h rest
    exact appendCode (leaveAt target (h.sameFunction.symm.trans hl)) rest
  case break_ =>
    intro X scope F n E c hb target h rest
    exact appendCode (breakAt target (h.loop hb)) rest
  case continue_ =>
    intro X scope F n E c hc target h rest
    exact appendCode (continueAt target (h.loop hc)) rest
  case function =>
    intro X scope F n E c name args rets body db target h rest
    exact rest
termination_by structural d

def WalkD.bodies {X scope F n E c body m final} (d : @WalkD X scope F n E c body m final) :
    Bodies F (globals X) ((collectHeaders body).map Prod.snd) := by
  apply WalkD.casesOn (motive_2 := fun {X} scope {F} {n} E c body {m} final _ =>
    Bodies F (globals X) ((collectHeaders body).map Prod.snd)) d
  case nil => intros; exact .nil
  case cons =>
    intro X scope F n E c first rest m next k final ds dt
    exact ds.prependBodies rest dt.bodies
termination_by structural d

/-- Only direct functions prepend a body. Nested function groups are closed
inside their own block and never added to this block's signatures. -/
def StatementD.prependBodies {X scope F n E c term m final}
    (d : @StatementD X scope F n E c term m final) (rest : Syn (.list .yulStmt)) :
    Bodies F (globals X) ((collectHeaders rest).map Prod.snd) →
      Bodies F (globals X) ((collectHeaders (.cons term rest)).map Prod.snd) := by
  apply StatementD.casesOn (motive_3 := fun {X} scope {F} {n} E c term {m} final _ =>
    (rest : Syn (.list .yulStmt)) →
      Bodies F (globals X) ((collectHeaders rest).map Prod.snd) →
        Bodies F (globals X) ((collectHeaders (.cons term rest)).map Prod.snd)) d
  case block => intros; assumption
  case declaration => intros; assumption
  case assignment => intros; assumption
  case expression => intros; assumption
  case if_ => intros; assumption
  case for_ => intros; assumption
  case switch => intros; assumption
  case leave => intros; assumption
  case break_ => intros; assumption
  case continue_ => intros; assumption
  case function =>
    intro X scope F n E c name args rets body db rest definitions
    exact .cons (db.codeAt ⟨true, false⟩ (ControlMap.refl _)) definitions
termination_by structural d

def CaseD.codeAt {X scope F n E c term w} (d : @CaseD X scope F n E c term w) (target : Control)
    (h : ControlMap c target) : Word × Stmt F X target n := by
  revert target h
  apply CaseD.casesOn (motive_4 := fun {X} scope {F} {n} E c term w _ =>
    (target : Control) → ControlMap c target → Word × Stmt F X target n) d
  intro X scope F n E c literal body w dl db target h
  exact (w, db.codeAt target h)
termination_by structural d

def CasesD.codeAt {X scope F n E c term words} (d : @CasesD X scope F n E c term words) (target : Control)
    (h : ControlMap c target) : Cases F X target n := by
  revert target h
  apply CasesD.casesOn (motive_5 := fun {X} scope {F} {n} E c term words _ =>
    (target : Control) → ControlMap c target → Cases F X target n) d
  case nil => intros; exact .nil
  case cons =>
    intro X scope F n E c first rest w words df dr target h
    let arm := df.codeAt target h
    exact .cons arm.1 arm.2 (dr.codeAt target h)
termination_by structural d

def DefaultD.codeAt {X scope F n E c term} (d : @DefaultD X scope F n E c term) (target : Control)
    (h : ControlMap c target) : Stmt F X target n := by
  revert target h
  apply DefaultD.casesOn (motive_6 := fun {X} scope {F} {n} E c term _ =>
    (target : Control) → ControlMap c target → Stmt F X target n) d
  case none => intros; exact .skip
  case some =>
    intro X scope F n E c body db target h
    exact db.codeAt target h
termination_by structural d
end

def BlockD.code {X scope F n E c body} (d : @BlockD X scope F n E c body) : Stmt F X c n :=
  d.codeAt c (ControlMap.refl c)

/-- A real continuation produces nonempty extracted code for every constructor.
Function declarations add no executable node; their REAL bodies are carried
by prependBodies, not discarded from the surrounding lexical group. -/
theorem StatementD.splice_some {X scope F n E c term m final}
    (d : @StatementD X scope F n E c term m final) (target : Control)
    (h : ControlMap c target) (tail : Stmt F X target m) :
    ∃ code, d.splice target h (some tail) = some code := by
  revert target h tail
  apply StatementD.casesOn (motive_3 := fun {X} scope {F} {n} E c term {m} final d =>
    ∀ (target : Control) (h : ControlMap c target) (tail : Stmt F X target m),
      ∃ code, d.splice target h (some tail) = some code) d
  all_goals intros; exact ⟨_, rfl⟩

/-- Splicing a nonempty initializer continuation NEVER yields None. This proof
is structural on the actual derivation and assumes no execution completion.
It does not prove continuation execution/order/once-only behavior. -/
theorem WalkD.splice_some {X scope F n E c body m final}
    (d : @WalkD X scope F n E c body m final) (target : Control)
    (h : ControlMap c target) (tail : Stmt F X target m) :
    ∃ code, d.splice target h (some tail) = some code := by
  revert target h tail
  apply WalkD.casesOn (motive_2 := fun {X} scope {F} {n} E c body {m} final d =>
    ∀ (target : Control) (h : ControlMap c target) (tail : Stmt F X target m),
      ∃ code, d.splice target h (some tail) = some code) d
  case nil =>
    intro X scope F n E c target h tail
    exact ⟨tail, rfl⟩
  case cons =>
    intro X scope F n E c first rest m next k final ds dt target h tail
    rcases dt.splice_some target h tail with ⟨nextCode, hn⟩
    change ∃ code, ds.splice target h (dt.splice target h (some tail)) = some code
    rw [hn]
    exact ds.splice_some target h nextCode
termination_by structural d

/-- Thus the loop-init getD in extraction returns its ACTUAL spliced code;
its default is unreachable, rather than an assumed/stub prerequisite. -/
theorem WalkD.splice_getD {X scope F n E c body m final}
    (d : @WalkD X scope F n E c body m final) (target : Control)
    (h : ControlMap c target) (tail : Stmt F X target m) :
    d.splice target h (some tail) =
      some ((d.splice target h (some tail)).getD .skip) := by
  rcases d.splice_some target h tail with ⟨code, hc⟩
  rw [hc]
  rfl

/-- Exact reconstruction makes the independent typing certificate unique.
This is about BlockTyping certificates, not the older separate ClosedPure
certificate-uniqueness draft. -/
theorem BlockD.unique {X scope F n E c body} (first second : @BlockD X scope F n E c body) :
    first = second :=
  Option.some.inj (first.complete.symm.trans second.complete)

theorem BlockD.codeAt_unique {X scope F n E c body}
    (first second : @BlockD X scope F n E c body) (target : Control)
    (h₁ h₂ : ControlMap c target) :
    first.codeAt target h₁ = second.codeAt target h₂ := by
  cases first.unique second
  rfl

theorem closeFunctions_nil {F X c n} (bodies : Bodies F (globals X) []) (code : Stmt F X c n) :
    closeFunctions [] bodies code = code := rfl

theorem appendCode_end {F X c n} (code : Stmt F X c n) :
    appendCode code none = some code := rfl

end Solidity.Yul.ScopedBlockTyping

/-! Concrete closed compatibility entry points retain the earlier signatures. -/
namespace Solidity.Yul.BlockTyping
open Solidity.Source (Syn)

def leaveAt {F n} (c : Control) (h : c.function = true) : Stmt F [] c n :=
  ScopedBlockTyping.leaveAt c h

def breakAt {F n} (c : Control) (h : c.loop = true) : Stmt F [] c n :=
  ScopedBlockTyping.breakAt c h

def continueAt {F n} (c : Control) (h : c.loop = true) : Stmt F [] c n :=
  ScopedBlockTyping.continueAt c h

def appendCode {F c n} (first : Stmt F [] c n) :
    Option (Stmt F [] c n) → Option (Stmt F [] c n) :=
  ScopedBlockTyping.appendCode first

def closeFunctions {F c n} (signatures : List Sig) :
    Bodies (signatures ++ F) [] signatures →
      Stmt (signatures ++ F) [] c n → Stmt F [] c n :=
  ScopedBlockTyping.closeFunctions (X := []) (F := F) (c := c) (n := n) signatures

def InitializerD.prefix {F n E count term}
    (d : @InitializerD F n E count term) (c : Control) :
    Stmt F [] c (count + n) → Stmt F [] c n :=
  ScopedBlockTyping.InitializerD.prefix d c

def BlockD.codeAt {F n E c body} (d : @BlockD F n E c body) (target : Control)
    (h : ControlMap c target) : Stmt F [] target n :=
  ScopedBlockTyping.BlockD.codeAt d target h

def WalkD.splice {F n E c body m final} (d : @WalkD F n E c body m final)
    (target : Control) (h : ControlMap c target) :
    Option (Stmt F [] target m) → Option (Stmt F [] target n) :=
  ScopedBlockTyping.WalkD.splice d target h

def StatementD.splice {F n E c term m final} (d : @StatementD F n E c term m final)
    (target : Control) (h : ControlMap c target) :
    Option (Stmt F [] target m) → Option (Stmt F [] target n) :=
  ScopedBlockTyping.StatementD.splice d target h

def WalkD.bodies {F n E c body m final} (d : @WalkD F n E c body m final) :
    Bodies F [] ((collectHeaders body).map Prod.snd) :=
  ScopedBlockTyping.WalkD.bodies d

def StatementD.prependBodies {F n E c term m final}
    (d : @StatementD F n E c term m final) (rest : Syn (.list .yulStmt)) :
    Bodies F [] ((collectHeaders rest).map Prod.snd) →
      Bodies F [] ((collectHeaders (.cons term rest)).map Prod.snd) :=
  ScopedBlockTyping.StatementD.prependBodies d rest

def CaseD.codeAt {F n E c term w} (d : @CaseD F n E c term w) (target : Control)
    (h : ControlMap c target) : Word × Stmt F [] target n :=
  ScopedBlockTyping.CaseD.codeAt d target h

def CasesD.codeAt {F n E c term words} (d : @CasesD F n E c term words) (target : Control)
    (h : ControlMap c target) : Cases F [] target n :=
  ScopedBlockTyping.CasesD.codeAt d target h

def DefaultD.codeAt {F n E c term} (d : @DefaultD F n E c term) (target : Control)
    (h : ControlMap c target) : Stmt F [] target n :=
  ScopedBlockTyping.DefaultD.codeAt d target h

def BlockD.code {F n E c body} (d : @BlockD F n E c body) : Stmt F [] c n :=
  ScopedBlockTyping.BlockD.code d

theorem StatementD.splice_some {F n E c term m final}
    (d : @StatementD F n E c term m final) (target : Control)
    (h : ControlMap c target) (tail : Stmt F [] target m) :
    ∃ code, d.splice target h (some tail) = some code :=
  ScopedBlockTyping.StatementD.splice_some d target h tail

theorem WalkD.splice_some {F n E c body m final}
    (d : @WalkD F n E c body m final) (target : Control)
    (h : ControlMap c target) (tail : Stmt F [] target m) :
    ∃ code, d.splice target h (some tail) = some code :=
  ScopedBlockTyping.WalkD.splice_some d target h tail

theorem WalkD.splice_getD {F n E c body m final}
    (d : @WalkD F n E c body m final) (target : Control)
    (h : ControlMap c target) (tail : Stmt F [] target m) :
    d.splice target h (some tail) =
      some ((d.splice target h (some tail)).getD .skip) :=
  ScopedBlockTyping.WalkD.splice_getD d target h tail

theorem BlockD.unique {F n E c body} (first second : @BlockD F n E c body) :
    first = second :=
  ScopedBlockTyping.BlockD.unique first second

theorem BlockD.codeAt_unique {F n E c body}
    (first second : @BlockD F n E c body) (target : Control)
    (h₁ h₂ : ControlMap c target) :
    first.codeAt target h₁ = second.codeAt target h₂ :=
  ScopedBlockTyping.BlockD.codeAt_unique first second target h₁ h₂

theorem closeFunctions_nil {F c n} (bodies : Bodies F [] []) (code : Stmt F [] c n) :
    closeFunctions [] bodies code = code :=
  ScopedBlockTyping.closeFunctions_nil (X := []) bodies code

theorem appendCode_end {F c n} (code : Stmt F [] c n) :
    appendCode code none = some code :=
  ScopedBlockTyping.appendCode_end code

end Solidity.Yul.BlockTyping
