import Solidity.Yul.DeclarationCheck

/-!
# Declaration visibility over complete Yul blocks

This is the declaration component of Y02, over the existing indexed source
grammar. It constructs each visible namespace instead of asking callers for
a namespace at every occurrence. Function headers are hoisted once per block;
variables extend subsequent siblings only. The loop-init block's final
namespace is shared by its condition/post/body and discarded on loop exit.

This component checks declaration legality and no-shadowing, not expression
references, capture, arity, placement or admission. In particular initializer
references still require expression checking in the PRE-declaration namespace.
The root YUL visible namespace and the distinct outside-Solidity namespace
remain inputs with Source/JSON provenance obligations. Outside Solidity names
forbid let declarations only, including inside functions. They do not forbid
function headers, parameters or returns; those still cannot shadow YUL names.
-/
namespace Solidity.Yul.DeclarationScope
open Solidity.Source (Syn Cat)

mutual
/-- Independent block-entry semantics: collect ALL direct function headers,
check their names, then process source-order declarations. -/
inductive BlockD (outside : List String) : List String → Syn (.list .yulStmt) → List String → Type where
  | intro {visible body headers final} :
      LegalHeadersD visible body headers →
      WalkD outside (headers.map Prod.fst ++ visible) body final →
      BlockD outside visible body final

/-- Source-order declaration traversal. Only a let extends later siblings.
Nested scopes and function parameters never escape their statement. -/
inductive WalkD (outside : List String) : List String → Syn (.list .yulStmt) → List String → Type where
  | nil {visible} : WalkD outside visible .nil visible
  | cons {visible first rest next final} :
      StatementD outside visible first next → WalkD outside next rest final →
      WalkD outside visible (.cons first rest) final

inductive StatementD (outside : List String) : List String → Syn .yulStmt → List String → Type where
  | block {visible body final} : BlockD outside visible body final →
      StatementD outside visible (.yulBlock body) visible
  | declaration {visible first rest value} :
      NamesD (visible ++ outside) (first :: rest) →
      StatementD outside visible (.yulLet first rest value) ((first :: rest) ++ visible)
  | assignment {visible first rest value} :
      StatementD outside visible (.yulAssign first rest value) visible
  | expression {visible value} : StatementD outside visible (.yulExprStmt value) visible
  | if_ {visible condition body final} : BlockD outside visible body final →
      StatementD outside visible (.yulIf condition body) visible
  | for_ {visible pre condition post body initFinal postFinal bodyFinal} :
      BlockD outside visible pre initFinal →
      BlockD outside initFinal post postFinal → BlockD outside initFinal body bodyFinal →
      StatementD outside visible (.yulFor pre condition post body) visible
  | switch {visible value cases fallback} :
      CasesD outside visible cases → DefaultD outside visible fallback →
      StatementD outside visible (.yulSwitch value cases fallback) visible
  | leave {visible} : StatementD outside visible .yulLeave visible
  | break_ {visible} : StatementD outside visible .yulBreak visible
  | continue_ {visible} : StatementD outside visible .yulContinue visible
  | function {visible name args rets body final} :
      NamesD visible (args ++ rets) → BlockD outside ((args ++ rets) ++ visible) body final →
      StatementD outside visible (.yulFun name args rets body) visible

inductive CaseD (outside : List String) : List String → Syn .yulCase → Type where
  | case_ {visible literal body final} : BlockD outside visible body final →
      CaseD outside visible (.yulCase literal body)

inductive CasesD (outside : List String) : List String → Syn (.list .yulCase) → Type where
  | nil {visible} : CasesD outside visible .nil
  | cons {visible first rest} : CaseD outside visible first → CasesD outside visible rest →
      CasesD outside visible (.cons first rest)

inductive DefaultD (outside : List String) : List String → Syn (.opt (.list .yulStmt)) → Type where
  | none {visible} : DefaultD outside visible .none
  | some {visible body final} : BlockD outside visible body final →
      DefaultD outside visible (.some body)
end

abbrev StatementCheck (outside : List String) (term : Syn .yulStmt) :=
  (visible : List String) → Option ((final : List String) × StatementD outside visible term final)
abbrev WalkCheck (outside : List String) (term : Syn (.list .yulStmt)) :=
  (visible : List String) → Option ((final : List String) × WalkD outside visible term final)
abbrev BlockCheck (outside : List String) (term : Syn (.list .yulStmt)) :=
  (visible : List String) → Option ((final : List String) × BlockD outside visible term final)

/-- Nonrecursive entry wrapper. Its walk argument is computed on this original
source node; the wrapper creates no second syntax or intermediate program. -/
def blockWith (outside : List String) {body : Syn (.list .yulStmt)} (walk : WalkCheck outside body) : BlockCheck outside body :=
  fun visible => do
    let headers := collectHeaders body
    if h : checkNames visible (headers.map Prod.fst) = true then
      let ⟨final, d⟩ ← walk (headers.map Prod.fst ++ visible)
      pure ⟨final, .intro ⟨collectHeaders_sound body, (checkNames_iff _ _).mp h⟩ d⟩
    else none

def Result (outside : List String) (category : Cat) (term : Syn category) : Type :=
  match category with
  | .yulStmt => StatementCheck outside term
  | .list .yulStmt => WalkCheck outside term
  | .yulCase => (visible : List String) → Option (CaseD outside visible term)
  | .list .yulCase => (visible : List String) → Option (CasesD outside visible term)
  | .opt (.list .yulStmt) => (visible : List String) → Option (DefaultD outside visible term)
  | _ => Unit

private def nilResult (outside : List String) (category : Cat) : Result outside (.list category) .nil := by
  cases category with
  | yulStmt => exact fun _ => some ⟨_, .nil⟩
  | yulCase => exact fun _ => some .nil
  | _ => exact ()

private def consResult (outside : List String) {category : Cat} {first : Syn category} {rest : Syn (.list category)}
    (head : Result outside category first) (tail : Result outside (.list category) rest) :
    Result outside (.list category) (.cons first rest) := by
  cases category with
  | yulStmt =>
      exact fun visible => do
        let ⟨next, d⟩ ← head visible
        let ⟨final, ds⟩ ← tail next
        pure ⟨final, .cons d ds⟩
  | yulCase =>
      exact fun visible => do pure (.cons (← head visible) (← tail visible))
  | _ => exact ()

private def noneResult (outside : List String) (category : Cat) : Result outside (.opt category) .none := by
  cases category with
  | list category =>
      cases category with
      | yulStmt => exact fun _ => some .none
      | _ => exact ()
  | _ => exact ()

private def someResult (outside : List String) {category : Cat} {body : Syn category} (d : Result outside category body) :
    Result outside (.opt category) (.some body) := by
  cases category with
  | list category =>
      cases category with
      | yulStmt => exact fun visible => do
          let ⟨_, db⟩ ← blockWith outside d visible
          pure (.some db)
      | _ => exact ()
  | _ => exact ()

/-- Retain the actual application of a category-dependent recursive result
in generated code. These transparent boundaries do not change the judgement. -/
@[noinline] private def applyCases {outside body}
    (check : (visible : List String) → Option (CasesD outside visible body))
    (visible : List String) : Option (CasesD outside visible body) :=
  check visible

@[noinline] private def applyDefault {outside body}
    (check : (visible : List String) → Option (DefaultD outside visible body))
    (visible : List String) : Option (DefaultD outside visible body) :=
  check visible

/-- G0: the source category is generalized in the executable recursor.
Every recursive call is on an ORIGINAL syntax child, with any newly computed
namespace passed to that child's checking function. -/
def checkNode (outside : List String) {category : Cat} (term : Syn category) : Result outside category term := by
  apply Syn.casesOn (motive := fun category term => Result outside category term) term
  case nil => intro category; exact nilResult outside category
  case cons => intro category first rest
               exact consResult outside (checkNode outside first) (checkNode outside rest)
  case none => intro category; exact noneResult outside category
  case some => intro category body; exact someResult outside (checkNode outside body)
  case yulBlock =>
    intro body
    exact fun visible => do
      let ⟨_, db⟩ ← blockWith outside (checkNode outside body) visible
      pure ⟨visible, .block db⟩
  case yulLet =>
    intro first rest value
    exact fun visible =>
      if h : checkNames (visible ++ outside) (first :: rest) = true then
        some ⟨(first :: rest) ++ visible, .declaration ((checkNames_iff _ _).mp h)⟩
      else none
  case yulAssign => intros; exact fun visible => some ⟨visible, .assignment⟩
  case yulExprStmt => intros; exact fun visible => some ⟨visible, .expression⟩
  case yulIf =>
    intro condition body
    exact fun visible => do
      let ⟨_, db⟩ ← blockWith outside (checkNode outside body) visible
      pure ⟨visible, .if_ db⟩
  case yulFor =>
    intro pre condition post body
    exact fun visible => do
      let ⟨initFinal, dp⟩ ← blockWith outside (checkNode outside pre) visible
      let ⟨_, ds⟩ ← blockWith outside (checkNode outside post) initFinal
      let ⟨_, db⟩ ← blockWith outside (checkNode outside body) initFinal
      pure ⟨visible, .for_ dp ds db⟩
  case yulSwitch =>
    intro value cases fallback
    exact fun visible => do
      pure ⟨visible, .switch (← applyCases (checkNode outside cases) visible) (← applyDefault (checkNode outside fallback) visible)⟩
  case yulCase =>
    intro literal body
    exact fun visible => do
      let ⟨_, db⟩ ← blockWith outside (checkNode outside body) visible
      pure (.case_ db)
  case yulLeave => exact fun visible => some ⟨visible, .leave⟩
  case yulBreak => exact fun visible => some ⟨visible, .break_⟩
  case yulContinue => exact fun visible => some ⟨visible, .continue_⟩
  case yulFun =>
    intro name args rets body
    exact fun visible =>
      if h : checkNames visible (args ++ rets) = true then do
        let ⟨_, db⟩ ← blockWith outside (checkNode outside body) ((args ++ rets) ++ visible)
        pure ⟨visible, .function ((checkNames_iff _ _).mp h) db⟩
      else none
  all_goals intros; exact ()
termination_by structural term

/-- Internal traversal API: requires the enclosing block header pass.
It does not independently validate function header names. -/
def checkWalk (outside visible : List String) (body : Syn (.list .yulStmt)) :=
  checkNode outside body visible

def checkBlock (outside visible : List String) (body : Syn (.list .yulStmt)) :=
  blockWith outside (checkNode outside body) visible

/-- Internal statement traversal API: function-name validity is established
by containing-block headers, not by this standalone helper. -/
def checkStatement (outside visible : List String) (term : Syn .yulStmt) :=
  checkNode outside term visible

/-- Entry reconstruction uses the real independent header and walk premises;
the public completeness theorem below discharges the walk premise recursively. -/
theorem blockWith_complete {outside visible body headers final}
    (h : LegalHeadersD visible body headers) (walk : WalkCheck outside body)
    (d : WalkD outside (headers.map Prod.fst ++ visible) body final)
    (hw : walk (headers.map Prod.fst ++ visible) = some ⟨final, d⟩) :
    blockWith outside walk visible = some ⟨final, .intro h d⟩ := by
  have he : collectHeaders body = headers := h.collected.complete
  subst headers
  unfold blockWith
  dsimp only
  rw [dif_pos ((checkNames_iff _ _).mpr h.names), hw]
  rfl

mutual
/-- Complete exact reconstruction from the independent whole-block judgement. -/
theorem BlockD.complete {outside visible body final}
    (d : BlockD outside visible body final) :
    checkBlock outside visible body = some ⟨final, d⟩ := by
  apply BlockD.casesOn (motive_1 := fun visible body final d =>
    checkBlock outside visible body = some ⟨final, d⟩) d
  intro visible body headers final h w
  exact blockWith_complete h (checkNode outside body) w w.complete
termination_by structural d

theorem WalkD.complete {outside visible body final}
    (d : WalkD outside visible body final) :
    checkWalk outside visible body = some ⟨final, d⟩ := by
  apply WalkD.casesOn (motive_2 := fun visible body final d =>
    checkWalk outside visible body = some ⟨final, d⟩) d
  case nil => intro visible; rfl
  case cons =>
      intro visible first rest next final head tail
      change (do
        let ⟨next, ds⟩ ← checkStatement outside visible first
        let ⟨final, dt⟩ ← checkWalk outside next rest
        pure ⟨final, WalkD.cons ds dt⟩ : Option ((out : List String) × WalkD outside visible (.cons first rest) out)) = _
      rw [head.complete]
      change (checkWalk outside next rest).bind _ = _
      rw [tail.complete]
      rfl
termination_by structural d

theorem StatementD.complete {outside visible term final}
    (d : StatementD outside visible term final) :
    checkStatement outside visible term = some ⟨final, d⟩ := by
  apply StatementD.casesOn (motive_3 := fun visible term final d =>
    checkStatement outside visible term = some ⟨final, d⟩) d
  case block =>
      intro visible body final db
      change (do
        let ⟨_, d⟩ ← checkBlock outside visible _
        pure ⟨visible, StatementD.block d⟩ : Option ((out : List String) × StatementD outside visible (.yulBlock body) out)) = _
      rw [db.complete]
      rfl
  case declaration =>
      intro visible first rest value hn
      change (if h : checkNames (visible ++ outside) (first :: rest) = true then
        some ⟨(first :: rest) ++ visible, StatementD.declaration ((checkNames_iff _ _).mp h)⟩ else none : Option ((out : List String) × StatementD outside visible (.yulLet first rest value) out)) = _
      rw [dif_pos ((checkNames_iff _ _).mpr hn)]
  case assignment => intros; rfl
  case expression => intros; rfl
  case if_ =>
      intro visible condition body final db
      change (do
        let ⟨_, d⟩ ← checkBlock outside visible _
        pure ⟨visible, StatementD.if_ d⟩ : Option ((out : List String) × StatementD outside visible (.yulIf condition body) out)) = _
      rw [db.complete]
      rfl
  case for_ =>
      intro visible pre condition post body initFinal postFinal bodyFinal dp ds db
      change (do
        let ⟨iv, di⟩ ← checkBlock outside visible pre
        let ⟨_, dt⟩ ← checkBlock outside iv post
        let ⟨_, de⟩ ← checkBlock outside iv body
        pure ⟨visible, StatementD.for_ di dt de⟩ : Option ((out : List String) × StatementD outside visible (.yulFor pre condition post body) out)) = _
      rw [dp.complete]
      change (checkBlock outside initFinal post).bind _ = _
      rw [ds.complete]
      change (checkBlock outside initFinal body).bind _ = _
      rw [db.complete]
      rfl
  case switch =>
      intro visible value cases fallback dc dd
      change (do pure ⟨visible, StatementD.switch
        (← checkNode outside cases visible) (← checkNode outside fallback visible)⟩ : Option ((out : List String) × StatementD outside visible (.yulSwitch value cases fallback) out)) = _
      rw [dc.complete]
      change (checkNode outside fallback visible).bind _ = _
      rw [dd.complete]
      rfl
  case leave => intros; rfl
  case break_ => intros; rfl
  case continue_ => intros; rfl
  case function =>
      intro visible name args rets body final hn db
      change (if h : checkNames visible (args ++ rets) = true then do
        let ⟨_, d⟩ ← checkBlock outside ((args ++ rets) ++ visible) body
        pure ⟨visible, StatementD.function ((checkNames_iff _ _).mp h) d⟩
        else none : Option ((out : List String) × StatementD outside visible (.yulFun name args rets body) out)) = _
      rw [dif_pos ((checkNames_iff _ _).mpr hn), db.complete]
      rfl
termination_by structural d

theorem CaseD.complete {outside visible term} (d : CaseD outside visible term) :
    checkNode outside term visible = some d := by
  apply CaseD.casesOn (motive_4 := fun visible term d =>
    checkNode outside term visible = some d) d
  intro visible literal body final db
  change (do
    let ⟨_, d⟩ ← checkBlock outside visible body
    pure (CaseD.case_ d)) = _
  rw [db.complete]
  rfl
termination_by structural d

theorem CasesD.complete {outside visible term} (d : CasesD outside visible term) :
    checkNode outside term visible = some d := by
  apply CasesD.casesOn (motive_5 := fun visible term d =>
    checkNode outside term visible = some d) d
  case nil => intro visible; rfl
  case cons =>
      intro visible first rest df dr
      change (do pure (CasesD.cons (← checkNode outside first visible)
        (← checkNode outside rest visible))) = _
      rw [df.complete]
      change (checkNode outside rest visible).bind _ = _
      rw [dr.complete]
      rfl
termination_by structural d

theorem DefaultD.complete {outside visible term} (d : DefaultD outside visible term) :
    checkNode outside term visible = some d := by
  apply DefaultD.casesOn (motive_6 := fun visible term d =>
    checkNode outside term visible = some d) d
  case none => intro visible; rfl
  case some =>
      intro visible body final db
      change (do
        let ⟨_, d⟩ ← checkBlock outside visible body
        pure (DefaultD.some d)) = _
      rw [db.complete]
      rfl
termination_by structural d
end

/-- Soundness is carried by the intrinsic output. These equivalences do not
assume successful checking, a namespace at each child or a fuel bound. -/
theorem checkBlock_iff (outside visible : List String) (body : Syn (.list .yulStmt)) :
    (checkBlock outside visible body).isSome = true ↔
      ∃ final, Nonempty (BlockD outside visible body final) := by
  constructor
  · intro h
    cases hc : checkBlock outside visible body with
    | none => simp only [hc, Option.isSome] at h; cases h
    | some value => exact ⟨value.1, ⟨value.2⟩⟩
  · rintro ⟨final, ⟨d⟩⟩
    rw [d.complete]
    rfl

theorem checkBlock_sound {outside visible body final d}
    (_h : checkBlock outside visible body = some ⟨final, d⟩) :
    Nonempty (BlockD outside visible body final) := ⟨d⟩

/-- The computed final namespace is unique, even though certificates are
Type-valued and are not assumed proof irrelevant. -/
theorem BlockD.final_unique {outside visible body a b}
    (da : BlockD outside visible body a) (db : BlockD outside visible body b) : a = b := by
  have h := da.complete.symm.trans db.complete
  exact congrArg Sigma.fst (Option.some.inj h)

end Solidity.Yul.DeclarationScope
