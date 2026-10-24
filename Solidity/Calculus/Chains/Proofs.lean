import Solidity.Calculus.Chains.Strategy

/-!
# Chains: the steps' proofs and written lines

Proofs of the steps, naming the rule, written lines, past the program.

A piece of `Calculus/Chains.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Solidity (Modality)

variable {C : Contract}

namespace Chain

open Lean Meta Elab Term

/-! ## Proofs of the steps -/

/-- `a ≡ b` by the kernel's definitional equality (`Calculus/RewriteChains.lean`'s
`kernelDefEq`). -/
def kernelDefEq (a b : Expr) : MetaM Bool := do
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  if a.hasMVar || b.hasMVar then return false
  return Kernel.isDefEqGuarded (← getEnv) (← getLCtx) a b

/-- The kernel's value of a closed `Nat` term. -/
def kernelNat (e : Expr) : MetaM Nat := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok r =>
    let some n := r.rawNatLit? <|> r.nat? | throwError "sol_chain: not a number{indentExpr r}"
    return n
  | .error _ => throwError "sol_chain: cannot compute{indentExpr e}"

/-- `e = n` by `rfl`, `n` the kernel's value of `e`. -/
def natRefl (e : Expr) : MetaM (Nat × Expr) := do
  let n ← kernelNat e
  let ty ← mkEq e (toExpr n)
  return (n, ← mkExpectedTypeHint (← mkEqRefl (toExpr n)) ty)

/-- `A.maxIdx = n`: the postconditions' `Post.noFresh`, put together along
the connectives, the kernel's value of the rest. -/
partial def maxIdxProof (A : Expr) : MetaM (Nat × Expr) := do
  let A := A.consumeMData
  if isPost A then
    return (0, mkApp3 (mkConst ``Post.noFresh) (A.getArg! 0) (A.getArg! 1) A.appArg!)
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  if !hasPost A then return ← natRefl (mkApp3 (mkConst ``Fml.maxIdx) C Γ A)
  let a := A.getAppArgs
  -- a connective whose fresh index is its part's: its lemma at its
  -- arguments, the part last
  let unary? := A.getAppFn.constName?.bind fun c =>
    [(``Fml.not, ``Fml.maxIdx_not_eq), (``Fml.havoc, ``Fml.maxIdx_havoc_eq),
     (``Fml.anon, ``Fml.maxIdx_anon_eq)].lookup c
  if let some lem := unary? then
    let (n, h) ← maxIdxProof a.back!
    return (n, mkAppN (mkConst lem) (a ++ #[toExpr n, h]))
  match A.getAppFn.constName? with
  | some ``Fml.and | some ``Fml.imp =>
    let lem := if A.isAppOf ``Fml.and then ``Fml.maxIdx_and_eq else ``Fml.maxIdx_imp_eq
    let (n₁, h₁) ← maxIdxProof a[2]!
    let (n₂, h₂) ← maxIdxProof a[3]!
    return (max n₁ n₂,
      mkAppN (mkConst lem) #[C, Γ, a[2]!, a[3]!, toExpr n₁, toExpr n₂, h₁, h₂])
  | some ``Fml.upd =>
    -- `upd {C Γ Γ'} m U φ`
    let (n₁, h₁) ← natRefl (mkApp4 (mkConst ``Upd.maxIdx) C Γ a[2]! a[4]!)
    let (n₂, h₂) ← maxIdxProof a[5]!
    return (max n₁ n₂, mkAppN (mkConst ``Fml.maxIdx_upd_eq)
      #[C, Γ, a[2]!, a[3]!, a[4]!, a[5]!, toExpr n₁, toExpr n₂, h₁, h₂])
  | some ``Fml.modal =>
    -- `modal {C Γ Γ₁ Γ₀} m P κ φ`
    let pk ← mkAppM ``Max.max #[mkAppN (mkConst ``Prog.maxIdx) #[C, Γ, a[2]!, a[5]!],
      mkAppN (mkConst ``Frames.maxIdx) #[C, a[2]!, a[3]!, a[6]!]]
    let (n₁, h₁) ← natRefl pk
    let (n₂, h₂) ← maxIdxProof a[7]!
    return (max n₁ n₂, mkAppN (mkConst ``Fml.maxIdx_modal_eq)
      #[C, Γ, a[2]!, a[3]!, a[4]!, a[5]!, a[6]!, a[7]!, toExpr n₁, toExpr n₂, h₁, h₂])
  | some ``Fml.all =>
    let (n, h) ← maxIdxProof a[4]!
    let x ← kernelNat (mkApp (mkConst ``Var.idx) a[2]!)
    return (max x n, mkAppN (mkConst ``Fml.maxIdx_all_eq) #[C, Γ, a[2]!, a[3]!, a[4]!, toExpr n, h])
  | some ``Fml.bind =>
    -- `bind {C Γ} m x t φ`
    let (n, h) ← maxIdxProof a[5]!
    let x ← kernelNat (mkApp (mkConst ``Var.idx) a[3]!)
    return (max x n,
      mkAppN (mkConst ``Fml.maxIdx_bind_eq) #[C, Γ, a[2]!, a[3]!, a[4]!, a[5]!, toExpr n, h])
  | _ => throwError "sol_chain: cannot compute the fresh index of{indentExpr A}"

/-- `A.active = false`: the postconditions' `Post.inactive`, put together
along the connectives, the kernel's `rfl` where none is left below one. -/
partial def inactiveProof (A : Expr) : MetaM (Option Expr) := do
  let A := A.consumeMData
  if isPost A then
    return some (mkApp3 (mkConst ``Post.inactive) (A.getArg! 0) (A.getArg! 1) A.appArg!)
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  if !hasPost A then
    let goal := mkApp3 (mkConst ``Fml.active) C Γ A
    unless ← kernelDefEq goal (toExpr false) do return none
    return some (← mkExpectedTypeHint (← mkEqRefl (toExpr false)) (← mkEq goal (toExpr false)))
  let a := A.getAppArgs
  -- a connective of one part: its lemma at its arguments, the part last
  let unary? := A.getAppFn.constName?.bind fun c =>
    [(``Fml.not, ``Fml.active_not_false), (``Fml.havoc, ``Fml.active_havoc_false),
     (``Fml.anon, ``Fml.active_anon_false), (``Fml.upd, ``Fml.active_upd_false),
     (``Fml.all, ``Fml.active_all_false), (``Fml.bind, ``Fml.active_bind_false)].lookup c
  if let some lem := unary? then
    let some h ← inactiveProof a.back! | return none
    return some (mkAppN (mkConst lem) (a.push h))
  match A.getAppFn.constName? with
  | some ``Fml.and | some ``Fml.imp =>
    let lem := if A.isAppOf ``Fml.and then ``Fml.active_and_false else ``Fml.active_imp_false
    let some h₁ ← inactiveProof a[2]! | return none
    let some h₂ ← inactiveProof a[3]! | return none
    return some (mkAppN (mkConst lem) #[C, Γ, a[2]!, a[3]!, h₁, h₂])
  | _ => return none

/-- The type `Focus C × Fml C Γ`. -/
def pairTy (C Γ : Expr) : Expr :=
  mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``Focus) C) (mkApp2 (mkConst ``Fml) C Γ)

/-- `some (f, B)`. -/
def someFocus (C Γ f B : Expr) : Expr :=
  mkApp2 (mkConst ``Option.some [0]) (pairTy C Γ)
    (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkApp (mkConst ``Focus) C) (mkApp2 (mkConst ``Fml) C Γ) f B)

/-- Why the line after is not written under the modality `m`. -/
def modalityStop (m : Expr) : MessageData :=
  m!"depends on the modality {m}, through a rule that reads it (`revertBox`, \
    `revertDiamond`, a loop's invariant rule): go on after `cases {m}`"

/-- `lhs = rhs` by `rfl`, the kernel's; under a modality `m` that the
kernel cannot compute past, by `Modality.casesOn m`, each case by `rfl`. -/
def kernelReflOrCases (m? : Option Expr) (lhs rhs : Expr) : MetaM Expr := do
  let ty ← mkEq lhs rhs
  if ← kernelDefEq lhs rhs then
    return ← mkExpectedTypeHint (← mkEqRefl rhs) ty
  let some m := m? | throwError "sol_chain: the kernel does not compute{indentExpr lhs}\nto{indentExpr rhs}"
  let motive ← withLocalDeclD `m (mkConst ``Modality) fun x => do
    mkLambdaFVars #[x] (ty.replaceFVar m x)
  let case (μ : Lean.Name) : MetaM Expr := do
    let l := lhs.replaceFVar m (mkConst μ)
    let r := rhs.replaceFVar m (mkConst μ)
    unless ← kernelDefEq l r do
      throwError "sol_chain: the line after the step{indentExpr lhs}\n{modalityStop m}"
    mkExpectedTypeHint (← mkEqRefl r) (← mkEq l r)
  return mkAppN (mkConst ``Modality.casesOn [levelZero])
    #[motive, m, ← case ``Modality.diamond, ← case ``Modality.box]

/-- `A.stepFocusR K = some (f, B)`: along the connectives to the statement
that fires where a postcondition stands in the way (past a goal that is
done, its `Post.inactive`), the kernel's `rfl` from there. -/
partial def focusProof (m? : Option Expr) (K : Nat) (A f B : Expr) : MetaM Expr := do
  let A := A.consumeMData
  let B := B.consumeMData
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  let kE := toExpr K
  let leaf : MetaM Expr := do
    kernelReflOrCases m? (mkApp4 (mkConst ``Fml.stepFocusR) C kE Γ A) (someFocus C Γ f B)
  unless hasPost A do return ← leaf
  let a := A.getAppArgs
  let b := B.getAppArgs
  let same (n : Lean.Name) : Bool := A.isAppOf n && B.isAppOf n && a.size == b.size
  if same ``Fml.and then
    if a[2]! == b[2]! then
      let some h ← inactiveProof a[2]! |
        throwError "sol_chain: the step after{← indentLine A}\nasks whether a goal is done, \
          which the kernel does not compute"
      let h₀ := mkAppN (mkConst ``Fml.stepFocusR_eq_none) #[C, kE, Γ, a[2]!, h]
      return mkAppN (mkConst ``Fml.stepFocusR_and_right)
        #[C, kE, Γ, a[2]!, a[3]!, b[3]!, f, h₀, ← focusProof m? K a[3]! f b[3]!]
    return mkAppN (mkConst ``Fml.stepFocusR_and_left)
      #[C, kE, Γ, a[2]!, a[3]!, b[2]!, f, ← focusProof m? K a[2]! f b[2]!]
  -- a connective of one part: its lemma at its arguments, the parts last
  for (c, lem) in [(``Fml.imp, ``Fml.stepFocusR_imp), (``Fml.upd, ``Fml.stepFocusR_upd),
      (``Fml.havoc, ``Fml.stepFocusR_havoc), (``Fml.all, ``Fml.stepFocusR_all),
      (``Fml.bind, ``Fml.stepFocusR_bind), (``Fml.anon, ``Fml.stepFocusR_anon)] do
    if same c then
      return mkAppN (mkConst lem) (#[C, kE, Γ] ++ a.extract 2 a.size ++
        #[b.back!, f, ← focusProof m? K a.back! f b.back!])
  leaf

/-- `A.fresh = K`. -/
def freshProof (A : Expr) (K : Nat) : MetaM Expr := do
  let (n, h) ← maxIdxProof A
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  let rootExpr ← mkAppM ``Contract.rootMaxIdx #[C]
  let rootValue ← withTransparency .all (whnf rootExpr)
  let some r ← (evalNat rootValue).run
    | throwError "sol_chain: cannot compute the contract's reserved root indices"
  unless max n r + 1 = K do
    throwError "sol_chain: the fresh index of{← indentLine A}\nis {max n r + 1}, not {K}"
  return mkAppN (mkConst ``Fml.fresh_eq)
    #[C, Γ, A, toExpr n, toExpr r, h, ← mkEqRefl rootExpr]

/-- `A ~> B` along the computed line `B`. -/
def oneStepProof (sp : Splice) (A : Expr) (B : Line) : MetaM Expr := do
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  return mkAppN (mkConst ``Fml.OneStep.ofFocus)
    #[C, Γ, A, B.fml, toExpr B.fresh, B.focus, ← freshProof A B.fresh,
      ← focusProof sp.modality B.fresh A B.focus B.fml]

/-- `A ~[r]~> B`, `r` a label whose focus is `B.focus`. -/
def stepByProof (sp : Splice) (r A : Expr) (B : Line) : MetaM Expr := do
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  let fr := mkApp2 (mkConst ``StepRule.focus) C r
  let h ← focusProof sp.modality B.fresh A B.focus B.fml
  let h ← mkExpectedTypeHint h (← mkEq (mkApp4 (mkConst ``Fml.stepFocusR) C (toExpr B.fresh) Γ A)
    (someFocus C Γ fr B.fml))
  return mkAppN (mkConst ``Fml.StepBy.ofFocus)
    #[C, Γ, A, B.fml, toExpr B.fresh, r, ← freshProof A B.fresh, h]

/-- `A ~*> Z` along the computed lines `ls`, `Z` the last. -/
def stepsProof (sp : Splice) (A : Expr) (ls : List Line) : MetaM Expr := do
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  let Z := (ls.getLast?.map (·.fml)).getD A
  let rec go (A : Expr) : List Line → MetaM Expr
    | [] => pure (mkApp3 (mkConst ``Fml.Steps.refl) C Γ A)
    | B :: ls => do
      let s ← oneStepProof sp A B
      pure (mkAppN (mkConst ``Fml.Steps.cons) #[C, Γ, A, B.fml, Z, s, ← go B.fml ls])
  go A ls

/-! ## Naming the rule -/

/-- The derivation of the constructor `c` (of `Taclet` or
`LeanTaclet`) on the statement `s` under `m`, fresh names at `k`: its
schema variables by unification (a hole's statement by its candidates,
`matchFind`), its side conditions by `rfl` or `decide`; the label
`StepRule.taclet k m s p d`. -/
def labelAs? (c : Lean.Name) (k m s : Expr)
    (pre : Option (List (Expr × Expr) × FindHeads) := none) : MetaM (Option Expr) := do
  let sTy ← whnfR (← inferType s)
  let C := sTy.getArg! 0
  let (cands, hs) ← match pre with
    | some p => pure p
    | none => do
      let cands ← holeCandidates s
      pure (cands, ← FindHeads.of s cands)
  unless ← mayFind c hs do return none
  let st ← saveState
  let r ← observing? do
    let some (ctor, xs, p) ← ctorAt? c C k m s cands | failure
    for x in xs do
      if (← instantiateMVars x).isMVar then
        let t := (← whnfR (← instantiateMVars (← inferType x))).unAutoParam
        if let some (_, a, b) := t.eq? then
          unless ← isDefEq a b do failure
          x.mvarId!.assign (← mkEqRefl a)
        else if ← isProp t then
          x.mvarId!.assign (← mkDecideProof t)
    let defaulted ← defaultLocalTys xs
    let d ← instantiateMVars (mkAppN ctor xs)
    let p ← instantiateMVars p
    if d.hasMVar || p.hasMVar then failure
    if defaulted then Meta.check d
    let wrap := if (`Solidity.Taclet).isPrefixOf c then ``Rule.key else ``Rule.lean
    let rule ← mkAppM wrap #[d]
    mkAppM ``StepRule.taclet #[k, m, s, p, rule]
  if r.isNone then st.restore
  return r

/-- The constructors a name may be. -/
def ruleCtors (r : Lean.Name) : MetaM (List Lean.Name) := do
  let env ← getEnv
  return [`Solidity.Taclet ++ r, `Solidity.LeanTaclet ++ r].filter env.contains

/-- The rule `Stmt.step` fires on the focus `f` (quoted), by name, and its
label: `emptyModality`, or the first constructor that derives it. -/
def labelOfFocus? (f : Expr) : MetaM (Option (Lean.Name × Expr)) := do
  if f.isAppOf ``Focus.empty then
    return some (`emptyModality, mkApp (mkConst ``StepRule.emptyModality) (f.getArg! 0))
  let a := f.getAppArgs
  unless a.size == 6 do return none
  let cands ← holeCandidates a[5]!
  let pre := (cands, ← FindHeads.of a[5]! cands)
  for c in ← ruleTableCtors do
    if let some l ← labelAs? c a[1]! a[2]! a[5]! pre then return some (lastName c, l)
  return none

/-- The label of `~[r]~>` on the focus `f`: the constructor `r` must derive it. -/
def labelFor (r : Lean.Name) (f : Expr) (where_ : Expr) : MetaM Expr := do
  -- printed only for an error: a line's print is a delaboration
  let at_ : MetaM MessageData := indentLine where_
  if r == `emptyModality then
    unless f.isAppOf ``Focus.empty do
      throwError "~[{r}]~>: the program of{← at_}\nis not done"
    return mkApp (mkConst ``StepRule.emptyModality) (f.getArg! 0)
  let a := f.getAppArgs
  unless a.size == 6 do throwError "~[{r}]~>: the step on{← at_}\nends a program"
  for c in ← ruleCtors r do
    if let some l ← labelAs? c a[1]! a[2]! a[5]! then return l
  let found := match ← labelOfFocus? f with
    | some (n, _) => m!"{n}"
    | none => m!"no rule of the table"
  throwError "~[{r}]~>: the rule for{← at_}\nis {found}, not {r}"

/-- A derivation, with the auxiliary lemmas the elaborator abstracted it into
unfolded, down to a constructor. -/
partial def tacletHead (d : Expr) : MetaM Expr := do
  let d ← whnfCore d
  let .const c us := d.getAppFn | return d
  if (`Solidity.Taclet).isPrefixOf c || (`Solidity.LeanTaclet).isPrefixOf c then return d
  match ← getConstInfo c with
  | info@(.thmInfo _) => tacletHead ((← instantiateValueLevelParams info us).beta d.getAppArgs)
  | _ => return d

/-- The name `~[r]~>` shows for a label. -/
def ruleName? (r : Expr) : MetaM (Option Lean.Name) := do
  let r ← whnfR (← instantiateMVars r)
  if r.isAppOf ``StepRule.emptyModality then return some `emptyModality
  unless r.isAppOf ``StepRule.taclet do return none
  let rule ← whnfCore r.appArg!
  unless rule.isAppOf ``Rule.key || rule.isAppOf ``Rule.lean do return none
  let d ← tacletHead rule.appArg!
  return d.getAppFn.constName?.map lastName

/-! ## Written lines -/

/-- A written line: left to be found (`_`), a formula in `dl`'s text, or a
term. -/
inductive Written where
  | hole
  | text (c : Lean.Term) (m? : Option Lean.Term) (φ : TSyntax `dl_fml)
  | term (t : Lean.Term)

/-- The `}` items of a modality's program dropped: `core_item`'s text read
as the statements it holds. -/
partial def dropBlockEnds (stx : Syntax) : Syntax :=
  let stx := stx.setArgs (stx.getArgs.map dropBlockEnds)
  match (⟨stx⟩ : TSyntax `dl_fml) with
  | `(dl_fml| ⟨ $[$ss;]* } $items* ⟩ $φ:dl_fml) =>
    let ss' := ss ++ items.filterMap fun i => match i with
      | `(core_item| $s:sol_stmt ;) => some s
      | _ => none
    Unhygienic.run `(dl_fml| ⟨ $[$ss';]* ⟩ $φ) |>.raw
  | `(dl_fml| ⟨[ $[$ss;]* } $items* ]⟩ $φ:dl_fml) =>
    let ss' := ss ++ items.filterMap fun i => match i with
      | `(core_item| $s:sol_stmt ;) => some s
      | _ => none
    Unhygienic.run `(dl_fml| ⟨[ $[$ss';]* ]⟩ $φ) |>.raw
  | `(dl_fml| [ $[$ss;]* } $items* ] $φ:dl_fml) =>
    let ss' := ss ++ items.filterMap fun i => match i with
      | `(core_item| $s:sol_stmt ;) => some s
      | _ => none
    Unhygienic.run `(dl_fml| [ $[$ss';]* ] $φ) |>.raw
  | _ => stx

/-- How a line is written. -/
def Written.of (stx : Syntax) : Written :=
  if stx.isOfKind ``Lean.Parser.Term.hole || stx.isOfKind ``Lean.Parser.Term.syntheticHole then .hole
  else
    let dlf (φ : TSyntax `dl_fml) : TSyntax `dl_fml := ⟨dropBlockEnds φ⟩
    match (⟨stx⟩ : Lean.Term) with
    | `(cdl![ $m ]{ $φ:dl_fml }) => .text (Unhygienic.run `(InContract.contract)) (some m) (dlf φ)
    | `(cdl!{ $φ:dl_fml }) => .text (Unhygienic.run `(InContract.contract)) none (dlf φ)
    | `(cdl[ $c, $m ]{ $φ:dl_fml }) => .text c (some m) (dlf φ)
    | `(cdl[ $c ]{ $φ:dl_fml }) => .text c none (dlf φ)
    | `(dl![ $m ]{ $φ:dl_fml }) => .text (Unhygienic.run `(InContract.contract)) (some m) (dlf φ)
    | `(dl!{ $φ:dl_fml }) => .text (Unhygienic.run `(InContract.contract)) none (dlf φ)
    | `(dl[ $c, $m ]{ $φ:dl_fml }) => .text c (some m) (dlf φ)
    | `(dl[ $c ]{ $φ:dl_fml }) => .text c none (dlf φ)
    | t => .term t

/-- The holes of a written formula, elaborated: each a Lean term. -/
def holeTerms (φ : TSyntax `dl_fml) : TermElabM (Array Syntax × Array Expr) := do
  let holes := fmlHoles φ
  let es ← holes.mapM fun h => do
    let some t := fmlHole? h | throwError "dl: not a formula hole"
    withRef h do
      let e ← withoutAutoBoundImplicit <| elabTerm t none
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
  return (holes, es)

/-- The `i` of a slot's key (`LineKey.slot i`, quoted). -/
def keySlot? (e : Expr) : Option Nat := do
  guard (e.isAppOfArity ``LineKey.slot 1)
  e.appArg!.rawNatLit? <|> e.appArg!.nat?

/-- The readings of a written formula, its Lean formulas in slots (the
`j`th hole's `LineKey.slot j`), each its key, quoted: the scoped reading
with its parameters open (`elabDlOpen`, `Fml.lineKey`), or with no modality
the line read by name (`elabKeyQ`).  At the diamond and at the box when `m`
is a variable, once otherwise. -/
def readings (c : Lean.Term) (m? : Option Expr) (holes : Array Syntax) (φ : TSyntax `dl_fml) :
    TermElabM (Array Expr) := do
  let μs : Array (Option Lean.Name) := match m? with
    | some m =>
      if m.isConstOf ``Modality.diamond || m.isConstOf ``Modality.box then #[m.constName?]
      else #[``Modality.diamond, ``Modality.box]
    | none => #[none]
  -- `elabAgainst`'s evaluation, both readings in one (each evaluation compiles
  -- its term), with no kernel check of the throwaway definition
  -- (`evalQuoted`): the readings are compared with the computed lines'
  let reads ← μs.mapM fun μ => do
    let raw ← liftMacroM (expandFml { either := μ.map fun n => (mkCIdent n : Lean.Term), holes } φ)
    -- applications built directly: in a quotation `$a $b` reads `$b` as a chain arrow
    if rawHasModal raw then
      let rd : Lean.Term := Syntax.mkApp (mkCIdent ``elabDlOpen) #[c, raw]
      pure (Syntax.mkApp (mkCIdent ``Except.map) #[mkCIdent ``Fml.openKeyQ, rd])
    else
      -- with no modality, read by name (`elabKeyQ`): a line past the program
      -- need not declare a memory local it no longer writes
      pure (Syntax.mkApp (mkCIdent ``elabKeyQ) #[c, raw])
  let ty := mkApp (mkConst ``List [0]) (mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String)
    (mkConst ``Lean.Expr))
  let e ← elabTermEnsuringType (← `([$reads,*])) ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let rs ← unsafe evalQuoted (List (Except String Lean.Expr)) ty e
  rs.toArray.mapM fun
    | .ok r => pure r
    | .error msg => throwError "Solidity elaboration failed: {msg}"

/-- A key with each slot read as the written formula's: `LineKey.slot j`,
`j` the hole of the postcondition in slot `i`. -/
def toWrittenSlots (sp : Splice) (holes : Array Expr) (e : Expr) : Expr :=
  e.replace fun x => do
    let i ← keySlot? x
    let p ← sp.posts[i]?
    let j ← holes.findIdx? fun h => h == p.appArg! || h == p
    pure (mkApp (mkConst ``LineKey.slot) (toExpr j))

/-- A key and the keys under its leading `∀`s. -/
partial def underAlls (e : Expr) : List Expr :=
  if e.isAppOfArity ``LineKey.all 3 then e :: underAlls e.appArg! else [e]

/-- The written text `φ` read (`readings`), with its holes elaborated; none
when its modality is not the chain's. -/
def readWritten (sp : Splice) (c : Lean.Term) (m? : Option Lean.Term) (φ : TSyntax `dl_fml) :
    TermElabM (Option (Array Expr × Array Expr)) := do
  let m? ← m?.mapM fun m => do instantiateMVars (← elabTermEnsuringType m (mkConst ``Modality))
  -- the written modality is the chain's
  if let (some m, some m') := (m?, sp.modality) then
    unless m == m' do return none
  let (hs, es) ← holeTerms φ
  let rs ← readings c (m?.orElse fun _ => sp.modality) hs φ
  return some (es, rs)

/-- Whether the readings `rs` of a written text, its holes `es`, are the
computed line whose keys are `keys` (once per modality run). -/
def readingMatches (sp : Splice) (es rs keys : Array Expr) : Bool :=
  let es' := keys.map (toWrittenSlots sp es)
  -- the written text may leave out the parameters `cdl!` binds outermost
  let same (r e : Expr) : Bool := (underAlls e).contains r
  if rs.size == es'.size then (rs.zip es').all fun (r, e) => same r e
  -- a constant modality read once against both runs: the run's own
  else es'.any (same rs[0]! ·)

/-- Whether the written line `w` is the computed line whose keys are
`keys` (once per modality run), the formulas of the computed lines `sp`. -/
def matchWritten (sp : Splice) (w : Written) (B : Expr) (keys : Array Expr) :
    TermElabM Bool := do
  match w with
  | .hole => return true
  | .term t =>
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    return e == B || (← withReducible (isDefEq e B))
  | .text c m? φ =>
    let some (es, rs) ← readWritten sp c m? φ | return false
    return readingMatches sp es rs keys

/-- `matchWritten w` against many computed lines (a `~*>`'s, a `~~>`'s, the
merges): the written text read once, on the first line it is checked
against, since its reading (two evaluations under a modality variable) does
not depend on the line. -/
def writtenMatcher (w : Written) :
    TermElabM (Splice → Expr → Array Expr → TermElabM Bool) := do
  match w with
  | .text c m? φ =>
    let memo ← IO.mkRef (none : Option (Option Expr × Option (Array Expr × Array Expr)))
    return fun sp _ keys => do
      let r ← match ← memo.get with
        | some (μ, r) => if μ == sp.modality then pure r else readWritten sp c m? φ
        | none =>
          let r ← readWritten sp c m? φ
          memo.set (some (sp.modality, r))
          pure r
      let some (es, rs) := r | return false
      return readingMatches sp es rs keys
  | _ => return fun sp B keys => matchWritten sp w B keys

/-- `first`, then each computed line after the rule that reached it,
printed by `pp`. -/
def showLinesBy (pp : Expr → MetaM MessageData) (first : MessageData) (lines : List Line) :
    MetaM MessageData := do
  let mut out := first
  for l in lines do
    let r := match ← labelOfFocus? l.focus with
      | some (n, _) => toString n
      | none => "?"
    out := out ++ m!"\n  ~[{r}]~>{← pp l.fml}"
  return out

/-- The computed line, shown (`#derivation`). -/
def showLines (φ : Expr) (lines : List Line) : MetaM MessageData := do
  showLinesBy indentLine (← indentLine φ) lines

/-- The computed lines, shown for an error as today's `sol_chain` shows them
(as today's chains' `notReached` did): every line with the rule that
reached it. -/
def showLinesErr (φ : Expr) (lines : List Line) : MetaM MessageData := do
  showLinesBy (fun ψ => return m!"\n    {← showLine ψ}") m!"    {← showLine φ}" lines

def modalStopNote (run : Run) : MessageData :=
  match run.modalStop, run.splice.modality with
  | true, some m => m!"\n  (the line after {modalityStop m})"
  | _, _ => m!""

/-! ## Past the program: the line written -/

/-- The identifiers of a piece of syntax, in order. -/
partial def synIdents : Syntax → List String
  | .ident _ _ n _ => [n.eraseMacroScopes.toString]
  | .node _ _ args => args.toList.flatMap synIdents
  | _ => []

/-- The line written `w`, read where it stands (`cdl[c, m]{ … }`), as a scoped
formula, its postcondition at the context it stands in: with the
parameters it reads before anything binds them, or, where its
postcondition then stands at another context, with one of its names kept
a parameter (`elabDlCN`'s `keep`: a local an update assigns past the
program, `{ … ‖ v := 0 }`, that the first line reads as a parameter). -/
def writtenFml (w : Written) : TermElabM Expr := do
  match w with
  | .hole => throwError "the line written is `_`"
  | .term t =>
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  | .text c m? φ =>
    let names := synIdents φ.raw
    for keep in [] :: names.eraseDups.map ([·]) do
      let s ← saveState
      try
        let e ← instantiateMVars (← withoutErrToSorry (elabCdlAt c m? φ (keep := keep)))
        if e.hasSyntheticSorry then throwError "not read"
        Meta.check e
        return e
      catch _ => s.restore
    throwError "the line written does not read where it stands"

/-- The line written `w` in a message: read where it stands, or as text. -/
def writtenMsg (w : Written) : TermElabM MessageData := do
  let s ← saveState
  try indentLine (← writtenFml w)
  catch _ => s.restore; pure m!" the line written"

/-- The rewrites `~~>` tries on a line while its program is open, after the
merges: KeY's names, no law (a law is named, `~[r]~>`). -/
def openRwNames : List Lean.Name :=
  [`sequentialToParallel, `applyOnRigid, `applyOnPV, `concrete, `simplifyUpdate]

/-- One rewrite of a line while its program is open: the line it leaves,
that line's splice and keys, the KeY name a chain writes it by, its
link (`Link.merge`, `Link.rw`), and the proof of `L ~~> it`, built when
asked. -/
structure OpenStep where
  fml : Expr
  splice : Splice
  keys : Array Expr
  name : Lean.Name
  link : Expr
  proof : TermElabM Expr

/-- The rewrites of the line `L` while its program is open: the merges of
its spine, then `openRwNames`. -/
def openRwSteps (L : Expr) : TermElabM (List OpenStep) := do
  let run ← runChain L
  unless run.isOpen do return []
  let (C, Γ) ← lineType L
  let fml := mkApp2 (mkConst ``Fml) C Γ
  let mut out := []
  let (sp, ms) ← mergeCands L
  for c in ms do
    let pf : TermElabM Expr := do
      let lhs := mkAppN (mkConst ``Fml.mergeRun) #[C, Γ, toExpr c.k, toExpr c.n, L]
      let h ← kernelReflOrCases sp.modality lhs (mkApp2 (mkConst ``Option.some [0]) fml c.fml)
      mkAppM ``Fml.mergeRun_leads #[toExpr c.k, toExpr c.n, L, h]
    let lnk := mkApp3 (mkConst ``Link.merge) C (toExpr c.k) (toExpr c.n)
    out := out ++ [OpenStep.mk c.fml sp c.keys `sequentialToParallel lnk pf]
  for n in openRwNames do
    let (sp, cs, _) ← scopedRwCands L (.table n)
    for c in cs do
      let pf : TermElabM Expr := do
        let lhs := mkAppN (mkConst ``FmlRw.apply) #[C, c.rw, Γ, L]
        let h ← kernelReflOrCases sp.modality lhs (mkApp2 (mkConst ``Option.some [0]) fml c.fml)
        mkExpectedTypeHint (mkAppN (mkConst ``FmlRw.sound) #[C, c.rw, Γ, L, c.fml, h])
          (mkApp4 (mkConst ``Fml.Leads) C Γ L c.fml)
      let lnk := mkApp3 (mkConst ``Link.rw) C (toExpr n.toString) c.rw
      out := out ++ [OpenStep.mk c.fml sp c.keys n lnk pf]
  return out

/-- How many rewrites `~~>` looks for while the program is open. -/
def openRwDepth : Nat := 3

/-- How many lines `openRwPath` expands at most. -/
def openRwNodes : Nat := 48

/-- At most `depth` rewrites of the line `L` while its program is open
(`openRwSteps`), breadth first, each line expanded once and at most
`openRwNodes` of them, each with its own heartbeats: the rewrites to the
first line `fits` accepts, and why the search stopped short, if it did (a
step that failed or ran out of heartbeats is a leaf). -/
def openRwPath (L : Expr) (fits : Expr → Splice → Array Expr → TermElabM Bool)
    (depth : Nat := openRwDepth) : TermElabM (Option (List OpenStep) × Option MessageData) := do
  let mut frontier : Array (Expr × List OpenStep) := #[(L, [])]
  let mut seen : Std.HashSet Expr := ({} : Std.HashSet Expr).insert L
  let mut nodes := 0
  let mut note : Option MessageData := none
  for _ in [0:depth] do
    let mut next := #[]
    for (X, path) in frontier do
      if nodes ≥ openRwNodes then
        return (none, some m!"the search stopped after {openRwNodes} lines")
      nodes := nodes + 1
      let r : Except Exception (List OpenStep) ←
        tryCatchRuntimeEx (.ok <$> withCurrHeartbeats (openRwSteps X)) fun e => pure (.error e)
      match r with
      | .error e => note := note <|> some m!"a step of the search failed: {e.toMessageData}"
      | .ok steps =>
        for st in steps do
          if ← fits st.fml st.splice st.keys then return (some (path ++ [st]), none)
        for st in steps do
          unless seen.contains st.fml do
            seen := seen.insert st.fml
            next := next.push (st.fml, path ++ [st])
    frontier := next
  return (none, note)

/-- The proof of `L ~~> B` along the rewrites `path` from `L`. -/
def OpenStep.leads (L : Expr) : List OpenStep → TermElabM Expr
  | [] => mkAppM ``Fml.Leads.self #[L]
  | [st] => st.proof
  | st :: rest => do mkAppM ``Fml.Leads.comp #[← st.proof, ← OpenStep.leads st.fml rest]

/-- Whether a line written may keep a program: a rewrite while the program
is open keeps it, so a line written with none (no program brackets, no
term escape, no formula variable but a postcondition) is not looked for
among them (`openRwPath`), and reads past the program. -/
partial def Written.mayBeOpen (w : Written) : TermElabM Bool := do
  match w with
  | .text _ _ φ => go φ.raw
  | _ => return true
where
  go (s : Syntax) : TermElabM Bool := do
    match s with
    | .atom _ v => return v == "⟨" || v == "[" || v == "‹"
    | .node _ k args =>
      if k == ``Solidity.dlFmlVar then
        let some d := (← getLCtx).findFromUserName? s[0].getId | return true
        let ty ← whnfR (← instantiateMVars d.type)
        return !(ty.isAppOf ``Solidity.Post)
      args.anyM go
    | _ => return false

end Chain

end Solidity
