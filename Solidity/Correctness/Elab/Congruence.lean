import Solidity.Syntax.Elab.CallOutput

/-!
# Callback agreement for the elaborator's helpers

The well-founded cut of the knot of `Syntax/Elab/Stmt.lean` needs each arm's
result at an input and scope to be the same over callbacks that agree at the
arguments and scopes the arm invokes them at.  Stated at run level, scope by
scope (`Agree`), the arguments described by the outputs of the stages before
(`Out`); proved for the callback-taking helpers below `Stmt.lean` and the call
arm, measure-free.  `agree_run` walks two computations of the same shape and
leaves the invocations at which they differ.
-/

namespace Solidity.ElabAgree

open Solidity Semantics

/-- `a` is a successful output of `x` at the scope `sc`, from some state. -/
def Out {α : Type} (sc : ElabScope) (x : ElabM α) (a : α) : Prop :=
  ∃ st m st' m', x sc st m = .ok ((a, st'), m')

/-- `x` and `y` run alike at the scope `sc`, from every state. -/
def Agree {α : Type} (sc : ElabScope) (x y : ElabM α) : Prop :=
  ∀ st m, x sc st m = y sc st m

theorem agree_refl {α : Type} (sc : ElabScope) (x : ElabM α) : Agree sc x x :=
  fun _ _ => rfl

/-- A bind: its first stage, then the continuations at its outputs. -/
theorem agree_bind {α β : Type} {sc : ElabScope} {x y : ElabM α} {f g : α → ElabM β}
    (hx : Agree sc x y) (hf : ∀ a, Out sc x a → Agree sc (f a) (g a)) :
    Agree sc (x >>= f) (y >>= g) := by
  intro st m
  change (do let ((a, s), n) ← x sc st m; f a sc s n) =
    (do let ((a, s), n) ← y sc st m; g a sc s n)
  rw [← hx st m]
  cases he : x sc st m with
  | error err => rfl
  | ok v =>
    rcases v with ⟨⟨a, s⟩, n⟩
    exact hf a ⟨st, m, s, n, he⟩ s n

/-- A list loop whose bodies agree at the list's elements. -/
theorem agree_forIn {α β : Type} {sc : ElabScope} (xs : List α) (init : β)
    (f g : α → β → ElabM (ForInStep β))
    (h : ∀ a ∈ xs, ∀ b, Agree sc (f a b) (g a b)) :
    Agree sc (forIn xs init f) (forIn xs init g) := by
  induction xs generalizing init with
  | nil => exact agree_refl _ _
  | cons a as ih =>
    simp only [List.forIn_cons]
    apply agree_bind (h a (by simp) init)
    intro r _
    cases r with
    | done b => exact agree_refl _ _
    | yield b => exact ih b fun x hx => h x (by simp [hx])

/-- A conditional whose branches agree. -/
theorem agree_ite {α : Type} {sc : ElabScope} {c : Prop} [Decidable c] {x y x' y' : ElabM α}
    (ht : c → Agree sc x x') (he : ¬c → Agree sc y y') :
    Agree sc (if c then x else y) (if c then x' else y') := by
  split
  · exact ht ‹_›
  · exact he ‹_›

/-- A dependent conditional whose branches agree. -/
theorem agree_dite {α : Type} {sc : ElabScope} {c : Prop} [Decidable c]
    {x x' : c → ElabM α} {y y' : ¬c → ElabM α}
    (ht : ∀ h, Agree sc (x h) (x' h)) (he : ∀ h, Agree sc (y h) (y' h)) :
    Agree sc (if h : c then x h else y h) (if h : c then x' h else y' h) := by
  split
  · exact ht _
  · exact he _

/-- The scope read is the scope run at. -/
theorem agree_read_bind {β : Type} {sc : ElabScope} {f g : ElabScope → ElabM β}
    (h : Agree sc (f sc) (g sc)) : Agree sc (read >>= f) (read >>= g) :=
  fun st m => h st m

/-- A pure stage passes its value on. -/
theorem agree_pure_bind {α β : Type} {sc : ElabScope} (a : α) {f g : α → ElabM β}
    (h : Agree sc (f a) (g a)) : Agree sc (pure a >>= f) (pure a >>= g) :=
  fun st m => h st m

/-- A failing stage has no continuation. -/
theorem agree_throw_bind {α β : Type} {sc : ElabScope} (e : String) (f g : α → ElabM β) :
    Agree sc ((throw e : ElabM α) >>= f) (throw e >>= g) :=
  fun _ _ => rfl

namespace Engine
open Lean Meta Elab Tactic

/-- The parts `(α, sc, x, y)` of a goal `Agree sc x y`. -/
def parts? (t : Expr) : Option (Expr × Expr × Expr × Expr) :=
  if t.isAppOfArity ``Solidity.ElabAgree.Agree 4 then
    let a := t.getAppArgs
    some (a[0]!, a[1]!, a[2]!, a[3]!)
  else none

def mkAgree (α sc x y : Expr) : Expr := mkApp4 (mkConst ``Solidity.ElabAgree.Agree) α sc x y

/-- A hypothesis `∀ as, Agree sc (f as) (g as)` for the local `f` heading `x`. -/
def localAgree? (x y : Expr) : MetaM (Option Expr) := do
  let f := x.getAppFn
  unless f.isFVar do return none
  let args := x.getAppArgs
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let body := ty.getForallBody
    if let some (_, _, l, r) := parts? body then
      let n := args.size
      let bound (e : Expr) : Bool := e.getAppNumArgs == n &&
        (List.range n).all fun i => e.getAppArgs[i]! == .bvar (n - 1 - i)
      if l.getAppFn == f && ty.getForallBinderNames.length == n && bound l && bound r &&
          y == mkAppN r.getAppFn args then
        return some (mkAppN d.toExpr args)
  return none

/-- Prove `Agree sc x y` for two computations of the same shape, returning
the goals it leaves: the invocations at which the two differ. -/
partial def run (inl : List Nat) (cnt : IO.Ref Nat) (g : MVarId) :
    MetaM (List MVarId) := g.withContext do
  let t ← g.getType
  let some (α, sc, x, y) := parts? t | return [g]
  if x == y then
    g.assign (mkApp3 (mkConst ``Solidity.ElabAgree.agree_refl) α sc x)
    return []
  let retarget (x' y' : Expr) : MetaM (List MVarId) := do
    run inl cnt (← g.replaceTargetDefEq (mkAgree α sc x' y'))
  match x, y with
  | .letE n tL vL bL _, .letE _ tR vR bR _ =>
    if tL == tR && vL == vR then
      let (xv, g2) ← (← g.define n tL vL).intro1
      let g3 ← g2.replaceTargetDefEq
        (mkAgree α sc (bL.instantiate1 (mkFVar xv)) (bR.instantiate1 (mkFVar xv)))
      return ← run inl cnt g3
    let idx ← cnt.modifyGet fun k => (k, if vL.isLambda then k + 1 else k)
    if vL.isLambda && inl.contains idx then
      return ← retarget (bL.instantiate1 vL) (bR.instantiate1 vR)
    let jp? ← (do
      unless tL == tR && vL.isLambda && vR.isLambda do return none
      let r ← withLocalDeclD n tL fun xL => withLocalDeclD n tL fun xR => do
        let hyp ← forallTelescope tL fun as _ => do
          mkForallFVars as (← mkAppM ``Solidity.ElabAgree.Agree #[sc, mkAppN xL as, mkAppN xR as])
        let side ← forallTelescope tL fun as _ => do
          mkForallFVars as (← mkAppM ``Solidity.ElabAgree.Agree
            #[sc, (mkAppN vL as).headBeta, (mkAppN vR as).headBeta])
        pure (← mkLambdaFVars #[xL, xR] hyp, side)
      pure (some r) : MetaM (Option (Expr × Expr))) <|> pure none
    match jp? with
    | some (hypOf, side) =>
      let ms ← mkFreshExprSyntheticOpaqueMVar side
      let g1 ← g.assert `hside side ms
      let (hs, g2) ← g1.intro1
      let (xL, g4) ← (← g2.define n tL vL).intro1
      let (xR, g6) ← (← g4.define n tL vR).intro1
      let g9 ← g6.withContext do
        let hyp := hypOf.beta #[mkFVar xL, mkFVar xR]
        let g7 ← g6.assert `hjp hyp (mkFVar hs)
        let (_, g8) ← g7.intro1
        g8.replaceTargetDefEq (mkAgree α sc (bL.instantiate1 (mkFVar xL)) (bR.instantiate1 (mkFVar xR)))
      let (_, ms') ← ms.mvarId!.intros
      return (← run inl cnt ms') ++ (← run inl cnt g9)
    | none =>
      if tL == tR && vL.isLambda && vR.isLambda then
        let me ← mkFreshExprSyntheticOpaqueMVar (← mkEq vL vR)
        let m ← mkFreshExprSyntheticOpaqueMVar (.forallE n tL (mkAgree α sc bL bR) .default)
        let motive := Expr.lam n tL (mkAgree α sc (bL.instantiate1 vL) bR) .default
        g.assign (← mkAppOptM ``Eq.subst #[none, motive, vL, vR, me, mkApp m vL])
        let (_, m') ← m.mvarId!.intro n
        return me.mvarId! :: (← run inl cnt m')
      return ← retarget (bL.instantiate1 vL) (bR.instantiate1 vR)
  | _, _ => pure ()
  if x.isAppOfArity ``Bind.bind 6 && y.isAppOfArity ``Bind.bind 6 then
    let xa := x.getAppArgs
    let ya := y.getAppArgs
    if xa[2]! == ya[2]! then
      let (α₁, x₁, f, y₁, k) := (xa[2]!, xa[4]!, xa[5]!, ya[4]!, ya[5]!)
      if x₁ == y₁ then
        if x₁.isAppOf ``MonadReader.read || x₁.isAppOf ``MonadReaderOf.read then
          let m ← mkFreshExprSyntheticOpaqueMVar (mkAgree α sc (f.beta #[sc]) (k.beta #[sc]))
          g.assign (mkAppN (mkConst ``Solidity.ElabAgree.agree_read_bind) #[α, sc, f, k, m])
          return ← run inl cnt m.mvarId!
        if x₁.isAppOfArity ``Pure.pure 4 then
          let a := x₁.appArg!
          let m ← mkFreshExprSyntheticOpaqueMVar (mkAgree α sc (f.beta #[a]) (k.beta #[a]))
          g.assign (mkAppN (mkConst ``Solidity.ElabAgree.agree_pure_bind) #[α₁, α, sc, a, f, k, m])
          return ← run inl cnt m.mvarId!
        if x₁.isAppOfArity ``MonadExcept.throw 5 || x₁.isAppOfArity ``throw 5 then
          g.assign (mkAppN (mkConst ``Solidity.ElabAgree.agree_throw_bind) #[α₁, α, sc, x₁.appArg!, f, k])
          return []
      let mx ← mkFreshExprSyntheticOpaqueMVar (mkAgree α₁ sc x₁ y₁)
      let fty ← withLocalDeclD `a α₁ fun a =>
        withLocalDeclD `ha (mkApp4 (mkConst ``Solidity.ElabAgree.Out) α₁ sc x₁ a) fun h =>
          mkForallFVars #[a, h] (mkAgree α sc (f.beta #[a]) (k.beta #[a]))
      let mf ← mkFreshExprSyntheticOpaqueMVar fty
      g.assign (mkAppN (mkConst ``Solidity.ElabAgree.agree_bind) #[α₁, α, sc, x₁, y₁, f, k, mx, mf])
      let (_, mf') ← mf.mvarId!.introN 2
      return (← run inl cnt mx.mvarId!) ++ (← run inl cnt mf')
  if x.isAppOfArity ``ite 5 && y.isAppOfArity ``ite 5 then
    let xa := x.getAppArgs
    let ya := y.getAppArgs
    if xa[1]! == ya[1]! then
      let c := xa[1]!
      let mt ← mkFreshExprSyntheticOpaqueMVar (← mkArrow c (mkAgree α sc xa[3]! ya[3]!))
      let me ← mkFreshExprSyntheticOpaqueMVar (← mkArrow (mkNot c) (mkAgree α sc xa[4]! ya[4]!))
      g.assign (mkAppN (mkConst ``Solidity.ElabAgree.agree_ite)
        #[α, sc, c, xa[2]!, xa[3]!, xa[4]!, ya[3]!, ya[4]!, mt, me])
      let (_, mt') ← mt.mvarId!.intro1
      let (_, me') ← me.mvarId!.intro1
      return (← run inl cnt mt') ++ (← run inl cnt me')
  if x.isAppOfArity ``dite 5 && y.isAppOfArity ``dite 5 then
    let xa := x.getAppArgs
    let ya := y.getAppArgs
    if xa[1]! == ya[1]! then
      let c := xa[1]!
      let tty ← withLocalDeclD `h c fun h =>
        mkForallFVars #[h] (mkAgree α sc (xa[3]!.beta #[h]) (ya[3]!.beta #[h]))
      let ety ← withLocalDeclD `h (mkNot c) fun h =>
        mkForallFVars #[h] (mkAgree α sc (xa[4]!.beta #[h]) (ya[4]!.beta #[h]))
      let mt ← mkFreshExprSyntheticOpaqueMVar tty
      let me ← mkFreshExprSyntheticOpaqueMVar ety
      g.assign (mkAppN (mkConst ``Solidity.ElabAgree.agree_dite)
        #[α, sc, c, xa[2]!, xa[3]!, ya[3]!, xa[4]!, ya[4]!, mt, me])
      let (_, mt') ← mt.mvarId!.intro1
      let (_, me') ← me.mvarId!.intro1
      return (← run inl cnt mt') ++ (← run inl cnt me')
  if x.isAppOfArity ``forIn 9 && y.isAppOfArity ``forIn 9 then
    let xa := x.getAppArgs
    let ya := y.getAppArgs
    if xa[1]!.isAppOf ``List && xa[6]! == ya[6]! && xa[7]! == ya[7]! then
      let (el, st, xs, f, k) := (xa[2]!, xa[4]!, xa[6]!, xa[8]!, ya[8]!)
      let ty ← withLocalDeclD `a el fun a => do
        withLocalDeclD `hm (← mkAppM ``Membership.mem #[xs, a]) fun hm =>
          withLocalDeclD `b st fun b => do
            mkForallFVars #[a, hm, b]
              (mkAgree (← inferType (f.beta #[a, b])).appArg! sc (f.beta #[a, b]) (k.beta #[a, b]))
      let m ← mkFreshExprSyntheticOpaqueMVar ty
      g.assign (mkAppN (mkConst ``Solidity.ElabAgree.agree_forIn) #[el, st, sc, xs, xa[7]!, f, k, m])
      let (_, m') ← m.mvarId!.introN 3
      return ← run inl cnt m'
  if let some pf ← localAgree? x y then
    g.assign pf
    return []
  if x.getAppFn.isFVar && y.getAppFn.isFVar then
    if let some vL ← x.getAppFn.fvarId!.getValue? then
      if let some vR ← y.getAppFn.fvarId!.getValue? then
        return ← retarget (vL.beta x.getAppArgs) (vR.beta y.getAppArgs)
  let x' ← withConfig (fun c => { c with zeta := false }) (whnfCore x)
  let y' ← withConfig (fun c => { c with zeta := false }) (whnfCore y)
  if x' != x || y' != y then return ← retarget x' y'
  if let some app ← matchMatcherApp? x then
    for d in app.discrs do
      if d.isFVar then
        let g ← (do
          let some v ← d.fvarId!.getValue? | pure g
          let g1 ← g.assert `hdef (← mkEq d v) (← mkEqRefl d)
          pure (← g1.intro1).2 : MetaM MVarId) <|> pure g
        let r ← (do pure (some (← g.cases d.fvarId!)) : MetaM _) <|> pure none
        if let some subs := r then
          let mut out := []
          for s in subs do out := out ++ (← run inl cnt s.mvarId)
          return out
    let r ← (do pure (some (← Split.splitMatch g x)) : MetaM (Option (List MVarId))) <|> pure none
    if let some subs := r then
      let mut out := []
      for s in subs do out := out ++ (← run inl cnt s)
      return out
  return [g]

/-- Reduce an `Agree` goal to the invocations at which its two sides differ. -/
elab "agree_run" inl:(num)* : tactic => do
  let gs ← run (inl.toList.map (·.getNat)) (← IO.mkRef 0) (← getMainGoal)
  replaceMainGoal gs

end Engine

section StatePassing

variable {σ : Type}

/-- Agreement of two state-passing computations at a scope, from every state. -/
def AgreeS {α : Type} (sc : ElabScope) (x y : StateT σ ElabM α) : Prop :=
  ∀ P, Agree sc (x.run P) (y.run P)

theorem agreeS_refl {α : Type} (sc : ElabScope) (x : StateT σ ElabM α) : AgreeS sc x x :=
  fun _ => agree_refl _ _

theorem agreeS_bind {α β : Type} {sc : ElabScope} {x y : StateT σ ElabM α}
    {f g : α → StateT σ ElabM β} (hx : AgreeS sc x y) (hf : ∀ a, AgreeS sc (f a) (g a)) :
    AgreeS sc (x >>= f) (y >>= g) := by
  intro P
  simp only [StateT.run_bind]
  exact agree_bind (hx P) fun a _ => hf a.1 a.2

theorem agreeS_map {α β : Type} {sc : ElabScope} {x y : StateT σ ElabM α} (k : α → β)
    (hx : AgreeS sc x y) : AgreeS sc (k <$> x) (k <$> y) := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact agreeS_bind hx fun _ => agreeS_refl _ _

theorem agreeS_listMapM {α β : Type} {sc : ElabScope} (f g : α → StateT σ ElabM β)
    (as : List α) (h : ∀ e ∈ as, AgreeS sc (f e) (g e)) :
    AgreeS sc (as.mapM f) (as.mapM g) := by
  induction as with
  | nil => exact agreeS_refl _ _
  | cons a as ih =>
    simp only [List.mapM_cons]
    exact agreeS_bind (h a (by simp)) fun _ =>
      agreeS_bind (ih fun e he => h e (by simp [he])) fun _ => agreeS_refl _ _

theorem agreeS_optMapM {α β : Type} {sc : ElabScope} (f g : α → StateT σ ElabM β)
    (i : Option α) (h : ∀ e ∈ i, AgreeS sc (f e) (g e)) :
    AgreeS sc (i.mapM f) (i.mapM g) := by
  cases i with
  | none => exact agreeS_refl _ _
  | some e => exact agreeS_map _ (h e rfl)

/-- **A statement's own expressions**: the statement map invokes its callback at
`RawStmt.exprs`, and at the target of a declaring `send`. -/
theorem mapExprsM_agree {sc : ElabScope} (f g : RawExpr → StateT σ ElabM RawExpr) (s : RawStmt)
    (h : ∀ e ∈ s.exprs, AgreeS sc (f e) (g e))
    (hs : ∀ T x r a b, s = .send (some T) x r a b → AgreeS sc (f x) (g x)) :
    AgreeS sc (s.mapExprsM f) (s.mapExprsM g) := by
  cases s <;> try cases ‹Option RawTy›
  all_goals simp only [RawStmt.mapExprsM, RawLoopSpec.mapM, bind_pure_comp, RawStmt.exprs] at h ⊢
  all_goals repeat' first
    | exact agreeS_refl _ _
    | exact hs _ _ _ _ _ rfl
    | exact h _ (Option.mem_toList.mpr ‹_›)
    | (apply h; simp [RawLoopSpec.exprs, *]; done)
    | (apply h; simp_all [RawLoopSpec.exprs, Option.mem_def]; done)
    | (apply h; simp only [List.mem_append, List.mem_filterMap, id]; exact Or.inl ⟨_, ‹_ ∈ _›, ‹_›⟩)
    | (refine agreeS_bind ?_ fun _ => ?_)
    | (refine agreeS_map _ ?_)
    | (refine agreeS_listMapM _ _ _ fun e he => ?_)
    | (refine agreeS_optMapM _ _ _ fun e he => ?_)
end StatePassing

variable (C : Contract) [FreshNames]

omit [FreshNames] in
/-- A block invokes its statement callback at its own statements. -/
theorem elabStmtsPWith_agree (stmt stmt' : RawStmt → ElabM (SProg C)) (sc : ElabScope)
    (ss : List RawStmt) (h : ∀ s ∈ ss, Agree sc (stmt s) (stmt' s)) :
    Agree sc (elabStmtsPWith C stmt ss) (elabStmtsPWith C stmt' ss) := by
  induction ss with
  | nil => exact agree_refl _ _
  | cons s ss ih =>
    simp only [elabStmtsPWith]
    apply agree_bind (h s (by simp))
    intro P _
    apply agree_bind (ih fun t ht => h t (by simp [ht]))
    intro Q _
    exact agree_refl _ _

/-- Argument hoisting invokes its callback at the list's members. -/
theorem hoistArgsWith_agree (H K : RawExpr → ElabM (SProg C × RawExpr)) (sc : ElabScope)
    (xs : List RawExpr) (h : ∀ a ∈ xs, Agree sc (H a) (K a)) :
    Agree sc (hoistArgsWith C H xs) (hoistArgsWith C K xs) := by
  induction xs with
  | nil => exact agree_refl _ _
  | cons a as ih =>
    simp only [hoistArgsWith]
    agree_run
    · exact h a (by simp)
    all_goals exact ih fun x hx => h x (by simp [hx])

/-- A pair's hoisting invokes its callback at the two operands. -/
theorem hoistPairWith_agree (H K : RawExpr → ElabM (SProg C × RawExpr)) (sc : ElabScope)
    (a b : RawExpr) (ha : Agree sc (H a) (K a)) (hb : Agree sc (H b) (K b)) :
    Agree sc (hoistPairWith C H a b) (hoistPairWith C K a b) := by
  unfold hoistPairWith
  agree_run <;> assumption

/-- A binary operator's hoisting invokes its callback at the two operands. -/
theorem hoistBinopWith_agree (H K : RawExpr → ElabM (SProg C × RawExpr)) (sc : ElabScope)
    (op : BinOp) (a b : RawExpr) (ha : Agree sc (H a) (K a)) (hb : Agree sc (H b) (K b)) :
    Agree sc (hoistBinopWith C H op a b) (hoistBinopWith C K op a b) := by
  unfold hoistBinopWith
  agree_run
  · exact hoistPairWith_agree C H K sc a b ha hb
  · exact hoistPairWith_agree C H K sc b a hb ha

/-- Eager argument evaluation invokes its callback at the list's members. -/
theorem eagerArgsWith_agree (H K : RawExpr → ElabM (SProg C × RawExpr)) (sc : ElabScope)
    (args : List RawExpr) (discard : Bool) (expected : List (Option PrimTy))
    (h : ∀ a ∈ args, Agree sc (H a) (K a)) :
    Agree sc (eagerArgsWith C H args discard expected)
      (eagerArgsWith C K args discard expected) := by
  unfold eagerArgsWith
  agree_run
  exact h _ (List.of_mem_zip (l₂ := List.range' 0 args.length)
    (by simpa [List.zipIdx_eq_zip_range'] using ‹_ ∈ args.zipIdx›)).1

/-- Call-argument preparation: the arguments, and the late copies it declares. -/
theorem hoistCallArgsWith_agree (H K : RawExpr → ElabM (SProg C × RawExpr))
    (stmt stmt' : RawStmt → ElabM (SProg C)) (sc : ElabScope) (f : String)
    (args : List RawExpr) (h : ∀ a ∈ args, Agree sc (H a) (K a))
    (hs : ∀ T y x, Agree sc (stmt (.declMemory T y (some (.name x))))
      (stmt' (.declMemory T y (some (.name x))))) :
    Agree sc (hoistCallArgsWith C H stmt f args) (hoistCallArgsWith C K stmt' f args) := by
  unfold hoistCallArgsWith
  agree_run
  all_goals first
    | exact hoistArgsWith_agree C H K sc args h
    | exact h _ (List.of_mem_zip ‹_›).2
    | (apply elabStmtsPWith_agree; intro s hm
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; subst hm; exact hs _ _ _)

/-- An inlined body: the callee's prepared body, in the callee's scope. -/
theorem inlinedBody_agree (rc rc' : ElabRec C) (sc : ElabScope) (f : String) (d : FunDecl)
    (ρ : List (String × String)) (shared ctor selfFrame : Bool)
    (scope : List (Name × FunDecl)) (k₀ : Nat) (Γ Γf : ECtx)
    (h : ∀ body k₁, Out sc (calleeBody C d ρ ctor selfFrame Γf) body →
      Agree { sc with funs := scope, top := false, selfFrame := selfFrame, unchecked := false,
                      inlined := (k₀, k₁) :: sc.inlined }
        (rc.elabStmtsP body) (rc'.elabStmtsP body)) :
    Agree sc (inlinedBody C rc f d ρ shared ctor selfFrame scope k₀ Γ Γf)
      (inlinedBody C rc' f d ρ shared ctor selfFrame scope k₀ Γ Γf) := by
  unfold inlinedBody
  agree_run
  all_goals exact h _ _ ‹_›

omit [FreshNames] in
/-- Agreement at a scope, through `runFrom`. -/
theorem Agree.runFrom {α : Type} {sc : ElabScope} {x y : ElabM α} (h : Agree sc x y)
    (st : ECtx × Nat) : x.runFrom sc st = y.runFrom sc st := by
  unfold ElabM.runFrom
  exact congrArg (fun r => (fun p : (α × (ECtx × Nat)) × CallMemo => p.1) <$> r) (h st {})

omit [FreshNames] in
/-- A recursive callee met outside its own frames: it is recursive and has no frame. -/
theorem frame_facts {ctor : Bool} {f : String} {recs : List RecFrame} (hc : ¬ctor = true)
    (hd : none = if ctor = true then none else recs.find? (·.name == f))
    (hr : (!ctor && ((none : Option RecFrame).isSome || isRecursiveC C f)) = true) :
    isRecursiveC C f = true ∧ recs.find? (·.name == f) = none := by
  cases ctor
  · simp only [Bool.not_false, Option.isSome_none, Bool.false_or, Bool.true_and] at hr
    simp only [Bool.false_eq_true, ↓reduceIte] at hd
    exact ⟨hr, hd.symm⟩
  · exact absurd rfl hc

omit [FreshNames] in
/-- The constructor is not recursive. -/
theorem frame_ctor {ctor b : Bool} (hc : ctor = true) (hr : (!ctor && b) = true) : False := by
  simp [hc] at hr

/-- **The call arm's invocations.**  A call through a function value goes to
the dispatch callbacks at the call's own name and arguments; otherwise the
block callback runs the callee's prepared body in the callee's scope, which
cannot deploy and is either the constructor's, a strict prefix of the
callable functions (the callee's index), or the frame of a recursive callee
that has none yet. -/
theorem elabCallRetCore_agree (rc rc' : ElabRec C) (sc : ElabScope) (f : String)
    (args : List RawExpr) (res : Option (Var × PrimTy)) (resW : Nat)
    (targets ctor resNew selfFrame : Bool)
    (hm : ∀ h ty as, (args = h :: as ∨ (h = .name f ∧ as = args)) →
      Agree sc (rc.fnMemoryDispatch h ty as) (rc'.fnMemoryDispatch h ty as))
    (hv : ∀ h as, args = h :: as →
      Agree sc (rc.callValue h as res resW resNew) (rc'.callValue h as res resW resNew))
    (hd : ∀ ty, Agree sc (rc.fnDispatch f ty args res resW resNew)
      (rc'.fnDispatch f ty args res resW resNew))
    (hin : ∀ sc' body, sc'.top = false → sc'.recs = sc.recs →
      (ctor = true ∨ ∃ i, sc.funs.findIdx? (·.1 == f) = some i ∧ sc'.funs = sc.funs.take i) →
      Agree sc' (rc.elabStmtsP body) (rc'.elabStmtsP body))
    (hfr : isRecursiveC C f = true → sc.recs.find? (·.name == f) = none →
      ∀ (rf : RecFrame) (sc' : ElabScope) body, rf.name = f → sc'.top = false →
        sc'.recs = rf :: sc.recs → Agree sc' (rc.elabStmtsP body) (rc'.elabStmtsP body)) :
    Agree sc (elabCallRetCore C rc f args res resW targets ctor resNew selfFrame)
      (elabCallRetCore C rc' f args res resW targets ctor resNew selfFrame) := by
  unfold elabCallRetCore
  agree_run 2
  all_goals first
    | exact hd _
    | exact hv _ _ rfl
    | exact hm _ _ _ (Or.inl rfl)
    | exact hm _ _ _ (Or.inr ⟨rfl, rfl⟩)
    | (apply inlinedBody_agree; intro body k₁ _; exact hin _ _ rfl rfl (Or.inl ‹ctor = true›))
    | (apply inlinedBody_agree; intro body k₁ _; exact hin _ _ rfl rfl (Or.inr ⟨_, ‹_ = some _›, rfl⟩))
    | contradiction
    | exact (frame_ctor ‹ctor = true› ‹(!ctor && _) = true›).elim
    | (obtain ⟨h1, h2⟩ := frame_facts C ‹¬ctor = true› ‹none = _› ‹(!ctor && _) = true›
       funext n bt
       dsimp only
       rw [(hfr h1 h2 _ _ _ rfl rfl rfl).runFrom])

/-- `elabCallRetWith` adds the numbering of a shared callee around the call arm. -/
theorem elabCallRetWith_agree (rc rc' : ElabRec C) (sc : ElabScope) (f : String)
    (args : List RawExpr) (res : Option (Var × PrimTy)) (resW : Nat)
    (targets ctor resNew selfFrame : Bool)
    (h : Agree sc (elabCallRetCore C rc f args res resW targets ctor resNew selfFrame)
      (elabCallRetCore C rc' f args res resW targets ctor resNew selfFrame)) :
    Agree sc (elabCallRetWith C rc f args res resW targets ctor resNew selfFrame)
      (elabCallRetWith C rc' f args res resW targets ctor resNew selfFrame) := by
  unfold elabCallRetWith
  agree_run
  exact h

end Solidity.ElabAgree
