import Solidity.Calculus.Chains.Proofs

/-!
# Chains, elaborated

The chain elaborated, `φ ~~> ψ` on scoped lines, `sol_chain`, printing.

A piece of `Calculus/Chains.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Solidity (Modality)

variable {C : Contract}

namespace Chain

open Lean Meta Elab Term

/-! ## The chain, elaborated -/

/-- `Link.one`, `Link.many`, `Link.rule r` and the pair type of a chain. -/
def linkTy (C : Expr) : Expr := mkApp (mkConst ``Link) C

/-- Why no rewrite past the program gives the line written `w` after `L`:
the rewrite applies nowhere (and why: a side condition, a modality), or
what it gives; `~=>`, what each rewrite that applies gives. -/
def pastRefusal (L : Expr) (w : Written) (rw? : Option (Option (Ident × RwArrow))) :
    TermElabM MessageData := do
  let written : TermElabM MessageData := writtenMsg w
  match rw? with
  | some (some (r, a)) =>
    let n := r.getId
    let (sp, cands, failed) ← scopedRwCands L a (past := true)
    if cands.isEmpty then
      if n == `simplifyUpdate && !sp.posts.isEmpty then
        return m!"~[{n}]~>: on{← indentLine L}\nit looks at the line's modality or postcondition, \
          which are not known: state the line for a concrete one"
      let note := match failed with
        | some m => m!"\n({m})"
        | none => m!""
      return m!"~[{n}]~>: {n} does not apply to{← indentLine L}{note}"
    let ls ← cands.mapM fun c => indentLine c.fml
    return m!"~[{n}]~>: on{← indentLine L}\nit gives{MessageData.joinSep ls ""}\nnot{← written}"
  | _ =>
    let mut gives : Array MessageData := #[]
    let arrows := (← rwAnyArrows).toArray
    let (_, rs) ← scopedRwCandsMany L (arrows.map (·.2)) (past := true)
    for ((n, _), (cands, _)) in arrows.zip rs do
      if let some c := cands.head? then
        gives := gives.push m!"{n} gives{← indentLine c.fml}"
    let note := if gives.isEmpty then m!"\nno rewrite applies to it" else
      m!"\n{MessageData.joinSep gives.toList "\n"}"
    return m!"~=>: no rewrite gives{← written}\nfrom{← indentLine L}{note}"

/-- A written chain whose first line `A` is a scoped formula: every line
after it computed, checked against its text (`matchWritten`), past the
program by `Calculus/RewritePast.lean`'s and `Calculus/RewriteLaws.lean`'s
rewrites. -/
def elabCoreChain (stx : Syntax) (A : Expr) : TermElabM Expr := do
  let (C, Γ) ← lineType A
  let fml := mkApp2 (mkConst ``Fml) C Γ
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (linkTy C) fml
  let mk (l B : Expr) : Expr := mkAppN (mkConst ``Prod.mk [0, 0]) #[linkTy C, fml, l, B]
  let mut cur := A
  let mut ws : Array Expr := #[]
  let mut single : Option Expr := none
  let links := stx[1].getArgs
  for h : i in [0:links.size] do
    let l := links[i]
    let w := Written.of l[1]
    let arrow : TSyntax `chain_arrow := ⟨l[0]⟩
    let rw? ← match arrow with
      | `(chain_arrow| ~[ $r:ident ]~>) => do
        if !(← ruleCtors r.getId).isEmpty then pure none
        else pure ((← rwArrow? r).map fun a => (some (r, a)))
      | `(chain_arrow| ~=>) => pure (some none)
      | _ => pure none
    -- a merge or rewrite of the scoped line, while its program is open and
    -- past it (`Calculus/RewriteScoped.lean`, `Calculus/RewritePast.lean`,
    -- `Calculus/RewriteLaws.lean`)
    let isOpen ← if rw?.isSome then (·.isOpen) <$> runChain cur else pure false
    let onScoped := rw?.isSome
    -- past the program a written line the scoped reading refuses fits no rewrite
    let fitsS (fits : Splice → Expr → Array Expr → TermElabM Bool) (sp : Splice) (B : Expr)
        (er : Array Expr) : TermElabM Bool := do
      if isOpen then return ← fits sp B er
      let s ← saveState
      try Term.withoutErrToSorry (fits sp B er) catch _ => s.restore; pure false
    if let some (some (r, .table `sequentialToParallel)) := rw? then
      if onScoped then
        -- past the program the merges are `FmlRw.mergePast`'s (`scopedRwCands`)
        let (sp, cands) ← if isOpen then mergeCands cur else pure ({}, [])
        let fits ← writtenMatcher w
        if let some c ← cands.findM? fun c => fitsS fits sp c.fml c.keys then
          let lnk := mkApp3 (mkConst ``Link.merge) C (toExpr c.k) (toExpr c.n)
          ws := ws.push (mk lnk c.fml)
          if links.size == 1 then
            single := some (mkAppN (mkConst ``Fml.MergeBy) #[C, Γ, toExpr c.k, toExpr c.n, cur, c.fml])
          cur := c.fml
          continue
        -- over a state write, under a branch (`FmlRw.stateMerge`, `FmlRw.mergeIn`)
        let (sp', below, _) ← scopedRwCands cur (.table `sequentialToParallel)
          (branches := isOpen) (past := !isOpen)
        if let some c ← below.findM? fun c => fitsS fits sp' c.fml c.keys then
          let n := toExpr r.getId.toString
          ws := ws.push (mk (mkApp3 (mkConst ``Link.rw) C n c.rw) c.fml)
          if links.size == 1 then
            single := some (mkAppN (mkConst ``Fml.RwBy) #[C, Γ, n, c.rw, cur, c.fml])
          cur := c.fml
          continue
        if isOpen then
          if cands.isEmpty && below.isEmpty then
            throwError "~[{r}]~>: {r} does not apply to{← indentLine cur}"
          throwError "~[{r}]~>: no merge of the update spine of{← indentLine cur}\n\
            is the line written{indentD (.ofSyntax l[1])}\n\
            The merges:{← (cands.map (·.fml) ++ below.map (·.fml)).foldlM (fun acc c => do
              pure (acc ++ m!"\n  ~[sequentialToParallel]~>{← indentLine c}")) m!""}"
    if let some (some (r, a)) := rw? then
      if onScoped then
        let run ← runChain cur
        let (sp, cands, failed) ← scopedRwCands cur a (past := !isOpen)
        let fits ← writtenMatcher w
        if let some c ← cands.findM? fun c => fitsS fits sp c.fml c.keys then
          let n := toExpr r.getId.toString
          ws := ws.push (mk (mkApp3 (mkConst ``Link.rw) C n c.rw) c.fml)
          if links.size == 1 then
            single := some (mkAppN (mkConst ``Fml.RwBy) #[C, Γ, n, c.rw, cur, c.fml])
          cur := c.fml
          continue
        if isOpen then
          let note := match failed with
            | some m => m!"\n({m})"
            | none => m!""
          if cands.isEmpty then
            throwError "~[{r}]~>: {r} does not apply to{← indentLine cur}\n\
              while the program is open{note}"
          throwError "~[{r}]~>: no rewrite by {r} of{← indentLine cur}\n\
            is the line written{indentD (.ofSyntax l[1])}\n\
            It gives:{← cands.foldlM (fun acc c => do
              pure (acc ++ m!"\n  ~[{r}]~>{← indentLine c.fml}")) m!""}"
    if let some none := rw? then
      if onScoped then
        -- `~=>`: the first merge or rewrite of the scoped line that gives the
        -- line written (`openRwSteps`)
        let fits ← writtenMatcher w
        if let some st ← (← openRwSteps cur).findM?
            fun st => fitsS fits st.splice st.fml st.keys then
          ws := ws.push (mk st.link st.fml)
          cur := st.fml
          continue
        if isOpen then
          throwError "~=>: no merge nor rewrite ({", ".intercalate (openRwNames.map toString)}) \
            of{← indentLine cur}\nis the line written{indentD (.ofSyntax l[1])}\n\
            while the program is open"
        -- past the program: the first rewrite of `rwAnyArrows`, in order,
        -- that gives the line written
        let run ← runChain cur
        let arrows := (← rwAnyArrows).toArray
        let (sp, rs) ← scopedRwCandsMany cur (arrows.map (·.2)) (past := true)
        let mut found := none
        for ((n, _), (cands, _)) in arrows.zip rs do
          if let some c ← cands.findM? fun c => fitsS fits sp c.fml c.keys then
            found := some (n, c)
            break
        if let some (n, c) := found then
          ws := ws.push (mk (mkApp3 (mkConst ``Link.rw) C (toExpr n) c.rw) c.fml)
          cur := c.fml
          continue
    if onScoped && !isOpen then
      throwError (← pastRefusal cur w rw?)
    let run ← runChain cur
    -- the line written, as a line prints where it elaborates alone (no
    -- hole, no postcondition of the line before), else its text; lazily, so
    -- that an error a search catches costs nothing
    let written : TermElabM MessageData := do
      let stx := l[1]
      return indentD <| .ofLazyM do
        let shown? ← (Term.withoutErrToSorry do
          try
            let e ← elabTerm stx none
            synthesizeSyntheticMVarsNoPostponing
            let e ← instantiateMVars e
            if e.hasMVar then return none
            return some (← showLine e)
          catch _ => return none : TermElabM _).run'
        return shown?.getD (.ofSyntax stx)
    let notReached (ls : List Line) : TermElabM Unit := do
      throwError "sol_chain: the derivation of{← indentLine cur}\ndoes not reach{← written}\n\
        Its lines:\n{← showLinesErr cur ls}{modalStopNote run}"
    match arrow with
    | `(chain_arrow| ~*>) =>
      -- a line given as a term is the relation's, unchecked here (`∃ ψ, φ ~*> ψ`)
      if let .term t := w then
        let B ← elabTermEnsuringType t fml
        ws := ws.push (mk (mkApp (mkConst ``Link.many) C) B)
        if links.size == 1 then single := some (mkAppN (mkConst ``Fml.Steps) #[C, Γ, cur, B])
        cur := B
        continue
      let cands : List (Expr × Array Expr) := (cur, run.keys) :: run.lines.map fun l => (l.fml, l.keys)
      let pick ← match w with
        | .hole => pure (cands.getLast?.map (·.1))
        | _ => do
          let fits ← writtenMatcher w
          cands.findSomeM? fun (B, er) => do
            if ← fits run.splice B er then pure (some B) else pure none
      let some B := pick | notReached run.lines
      ws := ws.push (mk (mkApp (mkConst ``Link.many) C) B)
      if links.size == 1 then single := some (mkAppN (mkConst ``Fml.Steps) #[C, Γ, cur, B])
      cur := B
    | `(chain_arrow| ~>) =>
      -- a line given as a term is the relation's, unchecked here (`∃ ψ, φ ~> ψ`)
      if let .term t := w then
        let B ← elabTermEnsuringType t fml
        ws := ws.push (mk (mkApp (mkConst ``Link.one) C) B)
        if links.size == 1 then single := some (mkAppN (mkConst ``Fml.OneStep) #[C, Γ, cur, B])
        cur := B
        continue
      let some B := run.lines.head? |
        match run.modalStop, run.splice.modality with
        | true, some m => throwError "sol_chain: the line after{← indentLine cur}\n{modalityStop m}"
        | _, _ => throwError "sol_chain: no rule applies to{← indentLine cur}"
      unless ← matchWritten run.splice w B.fml B.keys do notReached [B]
      ws := ws.push (mk (mkApp (mkConst ``Link.one) C) B.fml)
      if links.size == 1 then single := some (mkAppN (mkConst ``Fml.OneStep) #[C, Γ, cur, B.fml])
      cur := B.fml
    | _ =>
      let some B := run.lines.head? |
        match run.modalStop, run.splice.modality with
        | true, some m => throwError "sol_chain: the line after{← indentLine cur}\n{modalityStop m}"
        | _, _ => throwError "sol_chain: no rule applies to{← indentLine cur}"
      unless ← matchWritten run.splice w B.fml B.keys do notReached [B]
      match arrow with
      | `(chain_arrow| ~[ $r:ident ]~>) =>
        let lbl ← labelFor r.getId B.focus cur
        ws := ws.push (mk (mkApp2 (mkConst ``Link.rule) C lbl) B.fml)
        if links.size == 1 then single := some (mkAppN (mkConst ``Fml.StepBy) #[C, Γ, lbl, cur, B.fml])
      | _ =>
        ws := ws.push (mk (mkApp (mkConst ``Link.one) C) B.fml)
        if links.size == 1 then single := some (mkAppN (mkConst ``Fml.OneStep) #[C, Γ, cur, B.fml])
      cur := B.fml
  if let some e := single then return e
  return mkAppN (mkConst ``Fml.Via) #[C, Γ, A, ← mkListLit pairTy ws.toList]

/-- A chain, read here when its first line is a scoped formula, and by
`Calculus/RewriteChains.lean` otherwise. -/
syntax (name := chainAnyStx) "chain_any% " term : term

/-- Every chain goes through `elabChainAny`, which reads its first line once
to pick the reader. -/
@[macro Solidity.chainStx] def expandChainAny : Macro := fun stx =>
  return mkNode ``chainAnyStx #[mkAtom "chain_any% ", stx]

/-- The written lines of `calc` steps, by the metavariable that stands for the
line until `sol_chain` computes it from the line before: the text and the
rule `~[r]~>` names. -/
initialize pendingLines : EnvExtension (Std.HashMap MVarId (Syntax × Option Lean.Name)) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/-- A `calc` step `_ R B` on scoped lines: `_` the line before, which `calc`
fills in, and `B` a line computed from it, a metavariable for now that
`sol_chain` assigns (`pendingLines`), the text checked then. -/
def elabCalcStep (inner : Syntax) : TermElabM (Option Expr) := do
  let links := inner[1].getArgs
  unless links.size == 1 do return none
  let l := links[0]!
  let some b ← observing? (do
      let b ← elabTerm l[1] none
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars b) | return none
  unless ← isCoreLine b do return none
  let (C, Γ) ← lineType b
  let fml := mkApp2 (mkConst ``Fml) C Γ
  let A ← mkFreshExprMVar fml
  let B ← mkFreshExprMVar fml
  let arrow : TSyntax `chain_arrow := ⟨l[0]⟩
  let rule? : Option Lean.Name := match arrow with
    | `(chain_arrow| ~[ $r:ident ]~>) => some r.getId
    | _ => none
  let pend (key : Expr) : TermElabM Unit :=
    modifyEnv fun env => pendingLines.modifyState env (·.insert key.mvarId! (l[1], rule?))
  match arrow with
  | `(chain_arrow| ~>) => pend B; return some (mkAppN (mkConst ``Fml.OneStep) #[C, Γ, A, B])
  | `(chain_arrow| ~*>) => pend B; return some (mkAppN (mkConst ``Fml.Steps) #[C, Γ, A, B])
  | `(chain_arrow| ~[ $r:ident ]~>) =>
    if r.getId == `sequentialToParallel then
      let k ← mkFreshExprMVar (mkConst ``Nat)
      pend k
      return some (mkAppN (mkConst ``Fml.MergeBy)
        #[C, Γ, k, ← mkFreshExprMVar (mkConst ``Nat), A, B])
    if (← ruleCtors r.getId).isEmpty && r.getId != `emptyModality then
      -- a rewrite while the program is open (the line written still has it)
      let some _ ← rwArrow? r | return none
      unless (← runChain b).isOpen do return none
      let rw ← mkFreshExprMVar (mkApp (mkConst ``FmlRw) C)
      pend rw
      return some (mkAppN (mkConst ``Fml.RwBy) #[C, Γ, toExpr r.getId.toString, rw, A, B])
    let lbl ← mkFreshExprMVar (mkApp (mkConst ``StepRule) C)
    pend lbl
    return some (mkAppN (mkConst ``Fml.StepBy) #[C, Γ, lbl, A, B])
  | _ => return none

@[term_elab chainAnyStx] def elabChainAny : TermElab := fun stx expectedType? => do
  let inner := stx[1]
  -- `calc` writes the step's `_` as `(_ : T)`, `T` the type of the line before
  let isHole (s : Syntax) : Bool := s.isOfKind ``Lean.Parser.Term.hole ||
    (s.isOfKind ``Lean.Parser.Term.typeAscription && s[1].isOfKind ``Lean.Parser.Term.hole)
  if isHole inner[0] then
    if let some e ← elabCalcStep inner then return e
  let st ← saveState
  let first? ← observing? do
    let a ← elabTerm inner[0] none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars a
  if let some a := first? then
    if !a.hasMVar && (← isCoreLine a) then return ← elabCoreChain inner a
  st.restore
  elabTerm (← liftMacroM (Solidity.expandChainStx inner)) expectedType?

/-! ## `φ ~~> ψ` on scoped lines

With `open scoped Solidity.Scoped`, `A ~~> B` whose first line is scoped
reads `B` as the line of `A`'s derivation it is written as (`Fml.Leads`),
else as a scoped line with a program still open (a merged line, or one up
to `openRwDepth` merges and rewrites past a line of the derivation,
`Fml.Leads`), else past the program, the line it names (`Fml.LeadsK`,
`B` read where it stands, equal up to its binders' names to a line the
rewrites reach from the strategy's last line); where the
derivation stops on a modality variable the program is still open, and
that last reading is refused. -/

/-- `leads% A B`: `A ~~> B`, read by the first line's kind. -/
syntax (name := leadsAnyStx) "leads% " term:max term:max : term

@[term_elab leadsAnyStx] def elabLeadsAny : TermElab := fun stx _ => do
  let st ← saveState
  let first? ← observing? do
    let a ← elabTerm stx[1] none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars a
  let some A := first? | throwError "~~>: the first line is not known"
  unless !A.hasMVar && (← isCoreLine A) do
    st.restore
    throwError "~~>: the first line is a scoped formula: write it `dl!\{ … }` under \
      `open scoped Solidity.Scoped`{indentExpr A}"
  let (C, Γ) ← lineType A
  let bStx := if stx[2].isOfKind ``Lean.Parser.Term.paren then stx[2][1] else stx[2]
  let w := Written.of bStx
  let run ← runChain A
  let cands : List (Expr × Array Expr) := (A, run.keys) :: run.lines.map fun l => (l.fml, l.keys)
  let fits ← writtenMatcher w
  if let some B ← cands.findSomeM? (fun (B, er) => do
      if ← fits run.splice B er then pure (some B) else pure none) then
    return mkApp4 (mkConst ``Fml.Leads) C Γ A B
  -- a line of the derivation with its update spine merged (the program open)
  for (L, _) in cands do
    if !(← runChain L).isOpen then continue
    let (sp, ms) ← mergeCands L
    if let some c ← ms.findM? (fun c => fits sp c.fml c.keys) then
      return mkApp4 (mkConst ``Fml.Leads) C Γ A c.fml
  -- rewrites of a line whose program is still open (`Calculus/RewriteScoped.lean`)
  let mut stopped : Option MessageData := none
  if ← w.mayBeOpen then
    for (L, _) in cands do
      if !(← runChain L).isOpen then continue
      let (path?, note) ← openRwPath L (fun B sp er => fits sp B er)
      stopped := stopped <|> note
      if let some st := path?.bind (·.getLast?) then
        return mkApp4 (mkConst ``Fml.Leads) C Γ A st.fml
  let stopNote := match stopped with
    | some m => m!"\n({m})"
    | none => m!""
  unless (← whnfR Γ).isAppOf ``List.nil do
    throwError "~~>: the line after is no line of the derivation of{← indentLine A}{stopNote}"
  -- past the program the line after is `Update.lean`'s; where the derivation
  -- stops on a modality variable, the program is still open
  if run.modalStop then
    throwError "~~>: the line after is no line of the derivation of{← indentLine A}\n\
      nor reached from one by {", ".intercalate (openRwNames.map toString)} \
      (at most {openRwDepth} of them) while the program is open{modalStopNote run}{stopNote}"
  -- the line written, read where it stands: it names the line a chain of
  -- rewrites reaches, up to its binders' names (`Fml.LeadsK`)
  let L ← writtenFml w
  unless ← isDefEq (← inferType L) (mkApp2 (mkConst ``Fml) C Γ) do
    throwError "~~>: the line after is no scoped line of the contract{indentExpr L}"
  return mkAppN (mkConst ``Fml.LeadsK) #[C, A, L]

/-- `A ~~> B` on scoped lines prints as written. -/
@[app_unexpander Fml.Leads]
def unexpandLeads : PrettyPrinter.Unexpander
  | `($_ $a:term $b:term) => `($a:term ~~> $b:term)
  | _ => throw ()

/-! ## `sol_chain` on scoped chains -/

/-- The computed line `B` after `A`, its run. -/
def nextLine (A B : Expr) : MetaM (Run × Line) := do
  let run ← runChain A
  let some q := run.lines.head? | throwError "sol_chain: no rule applies to{← indentLine A}"
  if B.isMVar then
    unless ← isDefEq B q.fml do throwError "sol_chain: the line after is not{indentExpr B}"
    return (run, q)
  unless q.fml == B do
    throwError "sol_chain: the derivation of{← indentLine A}\ndoes not reach{← indentLine B}\n\
      Its lines:\n{← showLinesErr A [q]}{modalStopNote run}"
  return (run, q)

/-- Whether a goal is a scoped chain's. -/
partial def isCoreGoal (ty : Expr) : MetaM Bool := do
  let ty ← instantiateMVars ty
  if ty.isAppOf ``Fml.OneStep || ty.isAppOf ``Fml.StepBy || ty.isAppOf ``Fml.Steps ||
      ty.isAppOf ``Fml.MergeBy || ty.isAppOf ``Fml.RwBy || ty.isAppOf ``Fml.Via then return true
  if ty.isAppOfArity ``Nonempty 1 then return ← isCoreGoal ty.appArg!
  return false

/-- `sol_chain` on a scoped goal: each link by the kernel (`oneStepProof`,
`stepByProof`, `stepsProof`, `kernelReflOrCases` for a rewrite or a merge),
past the program too. -/
partial def solveCore (g : MVarId) : TermElabM Unit := do
  let ty ← instantiateMVars (← g.getType)
  -- a `calc` step: its line after computed from the line before, and checked
  -- against the text while it is a metavariable (`pendingLines`, keyed by the
  -- step's label, or by its line after for `~>`, `~*>`)
  let args := ty.getAppArgs
  let key? : Option Expr :=
    if ty.isAppOf ``Fml.StepBy || ty.isAppOf ``Fml.MergeBy then args[2]?
    else if ty.isAppOf ``Fml.RwBy then args[3]? else args.back?
  let pending := pendingLines.getState (← getEnv)
  let pend? : Option (Syntax × Option Lean.Name) := do
    let key ← key?
    guard key.isMVar
    pending[key.mvarId!]?
  if let some (wStx, rule?) := pend? then
    let A := args[args.size - 2]!
    let B := args.back!
    let w := Written.of wStx
    -- the line after: the text, while unknown; the line `calc` gave it, else
    let written ← writtenMatcher w
    let fits (B' : Expr) (sp : Splice) (er : Array Expr) : TermElabM Bool := do
      if B.isMVar then written sp B' er else isDefEq B B'
    if ty.isAppOf ``Fml.RwBy then
      let some r := rule? | throwError "sol_chain: no rewrite named"
      let some a ← rwArrow? (mkIdent r) | throwError "~[{r}]~>: no rewrite"
      let (sp, cands, _) ← scopedRwCands A a
      let some c ← cands.findM? fun c => fits c.fml sp c.keys
        | throwError "~[{r}]~>: no rewrite by {r} of{← indentLine A}\nis the line written"
      unless ← isDefEq B c.fml <&&> isDefEq args[3]! c.rw do
        throwError "sol_chain: the rewrite is not the next one"
    else if ty.isAppOf ``Fml.MergeBy then
      let (sp, cands) ← mergeCands A
      let some c ← cands.findM? fun c => fits c.fml sp c.keys
        | throwError "~[sequentialToParallel]~>: no merge of{← indentLine A}\nis the line written"
      unless ← isDefEq B c.fml <&&> isDefEq args[2]! (toExpr c.k) <&&> isDefEq args[3]! (toExpr c.n) do
        throwError "sol_chain: the merge is not the next one"
    else
      let run ← runChain A
      let cands : List (Expr × Array Expr) := if ty.isAppOf ``Fml.Steps then
          (A, run.keys) :: run.lines.map fun l => (l.fml, l.keys)
        else (run.lines.head?.map fun l => (l.fml, l.keys)).toList
      let some (B', _) ← cands.findM? fun (B', er) => fits B' run.splice er
        | throwError "sol_chain: the derivation of{← indentLine A}\ndoes not reach{indentD (.ofSyntax wStx)}\n\
            Its lines:\n{← showLines A run.lines}{modalStopNote run}"
      unless ← isDefEq B B' do throwError "sol_chain: the computed line is not the next one"
      if ty.isAppOf ``Fml.StepBy then
        let some q := run.lines.head? | throwError "sol_chain: no rule applies to{← indentLine A}"
        let some r := rule? | throwError "sol_chain: no rule named"
        let lbl ← labelFor r q.focus A
        unless ← isDefEq args[2]! lbl do throwError "sol_chain: the label does not fit"
    let ty' ← instantiateMVars ty
    if let some key := key? then
      if (← instantiateMVars key).isMVar then
        throwError "sol_chain: the `calc` step's line after is still unknown"
    return ← solveCore (← g.replaceTargetDefEq ty')
  match_expr ty with
  | Fml.OneStep _ _ A B =>
    let (run, q) ← nextLine A B
    g.assign (← oneStepProof run.splice A q)
  | Fml.StepBy _ _ r A B =>
    let (run, q) ← nextLine A B
    g.assign (← stepByProof run.splice r A q)
  | Fml.Steps _ _ A B =>
    let run ← runChain A
    -- a line left unknown (`∃ ψ, φ ~*> ψ`): the derivation's last
    if B.isMVar then
      let Z := (run.lines.getLast?.map (·.fml)).getD A
      unless ← isDefEq B Z do throwError "sol_chain: the last line is not{indentExpr B}"
      if (← instantiateMVars B).isMVar then throwError "sol_chain: the last line is unknown"
      return ← solveCore g
    let i ← if A == B then pure 0 else
      match run.lines.findIdx? (·.fml == B) with
      | some i => pure (i + 1)
      | none => throwError "sol_chain: the derivation of{← indentLine A}\ndoes not reach{← indentLine B}"
    g.assign (← stepsProof run.splice A (run.lines.take i))
  | Fml.MergeBy C Γ k n A B =>
    let sp ← collectPosts A {}
    let m? ← modalityOf? (punch C sp A)
    let lhs := mkAppN (mkConst ``Fml.mergeRun) #[C, Γ, k, n, A]
    let rhs := mkApp2 (mkConst ``Option.some [0]) (mkApp2 (mkConst ``Fml) C Γ) B
    g.assign (← kernelReflOrCases m? lhs rhs)
  | Fml.RwBy C Γ _ r A B =>
    let sp ← collectPosts A {}
    let m? ← modalityOf? (punch C sp A)
    let lhs := mkAppN (mkConst ``FmlRw.apply) #[C, r, Γ, A]
    let rhs := mkApp2 (mkConst ``Option.some [0]) (mkApp2 (mkConst ``Fml) C Γ) B
    g.assign (← kernelReflOrCases m? lhs rhs)
  | Nonempty T =>
    let t ← mkFreshExprMVar T
    solveCore t.mvarId!
    g.assign (mkApp2 (mkConst ``Nonempty.intro [1]) T t)
  | And P Q =>
    let a ← mkFreshExprMVar P
    let b ← mkFreshExprMVar Q
    solveCore a.mvarId!
    solveCore b.mvarId!
    g.assign (mkApp4 (mkConst ``And.intro) P Q a b)
  | Eq T a b =>
    unless ← kernelDefEq a b do
      throwError "sol_chain: the last scoped line, its binders' names aside, is not{indentExpr b}"
    g.assign (← mkExpectedTypeHint (← mkEqRefl b) (mkApp3 (mkConst ``Eq [1]) T a b))
  | True => g.assign (mkConst ``True.intro)
  | _ =>
    let ty' ← whnfR ty
    if ty' != ty then return ← solveCore (← g.replaceTargetDefEq ty')
    throwError "sol_chain: the goal is no chain on scoped lines{indentExpr ty}"

elab_rules : tactic
  | `(tactic| sol_chain) => Tactic.withMainContext do
    let g ← Tactic.getMainGoal
    unless ← isCoreGoal (← g.getType) do throwUnsupportedSyntax
    solveCore g
    Tactic.replaceMainGoal []

/-- Whether the term `t` is today's notation (`dl!{ … }`, `dl[C]{ … }`)
with the scope's switch off (`core_surface%`, `Calculus/Surface.lean`):
it reads as `Update.lean`'s formula, which no command here reads, so the
command refuses it without elaborating it (`notScopedNotation`;
`Tools/ProofTree.lean`'s `elabCoreFormula?` does the same). -/
def todaysNotation (t : Syntax) : TermElabM Bool := do
  let some (.atom _ v) := t.getHead? | return false
  unless v.startsWith "dl" do return false
  let flag := mkNode `Solidity.coreSurfaceFlag #[mkAtom "core_surface%"]
  let some out ← liftMacroM (expandMacro? flag) | return true
  return !(out.isIdent && out.getId.eraseMacroScopes == `true)

/-- What a command on scoped formulas says of `todaysNotation`. -/
def notScopedNotation {α : Type} (cmd : String) : TermElabM α :=
  throwError "{cmd}: not a scoped formula: write `cdl!\{ … }` or \
    `open scoped Solidity.Scoped`"

/-- `#derivation φ` for a scoped `φ`: the lines the strategy takes, each with
the rule that reached it. -/
elab_rules : command
  | `(command| #derivation $t) => Command.runTermElabM fun _ => do
    if ← todaysNotation t then notScopedNotation "#derivation"
    let φ ← instantiateMVars (← elabTerm t none)
    synthesizeSyntheticMVarsNoPostponing
    let φ ← instantiateMVars φ
    unless ← isCoreLine φ do throwUnsupportedSyntax
    let run ← runChain φ
    logInfo ((← showLines φ run.lines) ++ modalStopNote run)

/-! ## Printing -/

section Print
open PrettyPrinter Delaborator SubExpr

/-- The arrow a scoped link stands for. -/
def arrowOf (l : Expr) : MetaM (TSyntax `chain_arrow) := do
  let l ← whnfR (← instantiateMVars l)
  if l.isAppOf ``Link.one then `(chain_arrow| ~>)
  else if l.isAppOf ``Link.many then `(chain_arrow| ~*>)
  else if l.isAppOf ``Link.merge then `(chain_arrow| ~[$(mkIdent `sequentialToParallel):ident]~>)
  else if l.isAppOf ``Link.rw then
    let .lit (.strVal n) := l.getArg! 1 | failure
    `(chain_arrow| ~[$(mkIdent (.mkSimple n)):ident]~>)
  else if l.isAppOf ``Link.rule then
    let some n ← ruleName? l.appArg! | failure
    `(chain_arrow| ~[$(mkIdent n):ident]~>)
  else failure

/-- The links of a list of `(link, line)` pairs, printed. -/
def linkLines (ws : Expr) : MetaM (Array (TSyntax `chain_arrow × Lean.Term)) := do
  let some ws ← Solidity.listElems? ws | failure
  ws.mapM fun w => do
    let w ← whnfR w
    guard (w.isAppOfArity ``Prod.mk 4)
    pure (← arrowOf (w.getArg! 2), ← ppCoreLine (w.getArg! 3))

/-- A relation of one link, `A ⇝ B`, with `n` arguments, the lines its last
two, printed with the arrow `arrow` reads off it. -/
def delabLink (n : Nat) (arrow : Expr → MetaM (TSyntax `chain_arrow)) : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == n)
  return chainNode (← ppCoreLine (e.getArg! (n - 2)))
    #[(← arrow e, ← ppCoreLine (e.getArg! (n - 1)))]

@[delab app.Solidity.Fml.OneStep]
def delabOneStep : Delab := delabLink 4 fun _ => `(chain_arrow| ~>)

@[delab app.Solidity.Fml.Steps]
def delabSteps : Delab := delabLink 4 fun _ => `(chain_arrow| ~*>)

@[delab app.Solidity.Fml.StepBy]
def delabStepBy : Delab := delabLink 5 fun e => do
  let some n ← ruleName? (e.getArg! 2) | failure
  `(chain_arrow| ~[$(mkIdent n):ident]~>)

/-- `φ ~[n]~> ψ`, a rewrite of the scoped line (`Calculus/RewriteScoped.lean`). -/
@[delab app.Solidity.Fml.RwBy]
def delabRwBy : Delab := delabLink 6 fun e => do
  let .lit (.strVal n) := e.getArg! 2 | failure
  `(chain_arrow| ~[$(mkIdent (.mkSimple n)):ident]~>)

/-- `φ ~[sequentialToParallel]~> ψ`, a merge of the scoped line's spine
(`Calculus/Merge.lean`). -/
@[delab app.Solidity.Fml.MergeBy]
def delabMergeBy : Delab := delabLink 6 fun _ =>
  `(chain_arrow| ~[$(mkIdent `sequentialToParallel):ident]~>)

@[delab app.Solidity.Fml.Via]
def delabVia : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  let arrows ← linkLines (e.getArg! 3)
  guard !arrows.isEmpty
  return chainNode (← ppCoreLine (e.getArg! 2)) arrows

/-- `Fml.LeadsK A L`: `A ~~> L`, the line written `L` printed as it reads. -/
@[delab app.Solidity.Fml.LeadsK]
def delabLeadsK : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  let a ← ppCoreLine (e.getArg! 1)
  let b ← ppCoreLine (e.getArg! 2)
  `($a ~~> $b)

end Print

end Chain

namespace Scoped

scoped macro_rules
  | `($a:term ~~> $b:term) => `(leads% $a $b)

end Scoped

end Solidity
