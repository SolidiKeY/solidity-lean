import Solidity.Calculus.RuleSyntax
import Solidity.Calculus.KeyTaclets

/-!
# What a rule is made of

The parts of a taclet that outlive today's rule table (`Calculus/Rules.lean`):
where a read or a value lands (`Hole`, `MHole`, `VHole`, `NewLhs` and
their `fill`), the side conditions a taclet states and `side_cond` proves,
what a taclet leaves (`Premise`, the printers' target for the scoped
premises too: `Calculus/Core/Delab.lean` prints a scoped premise through
its erasure), solkey's branch labels (`Taclet.branchLabels`,
`Taclet.labelledBy`), and the printers of a premise and of a taclet's binders
(`ppPremise?`, `delabTacletBinders`).  Moved out of `Rules.lean`
(`docs/intrinsic.md`, W4 item 11), which keeps the rule table and its
delaborators.
-/

namespace Solidity

variable {C : Contract}

/-! ## Where a read or a value lands

A read unfolded by Step 1 lands in one of several places, and the rule is the
same for all of them: the rule writes `lhs = nsp.fld`.  A hole is that
`lhs`: a statement with a path missing. -/

/-- Where a storage path lands: `v = □` (a value read), `lsv = □` (an alias
bound), `loc = □` (a copy into a member or an entry). -/
inductive Hole (C : Contract) : Ty → Type where
  | local {p : PrimTy} (x : Var) : Hole C (.prim p)
  | rebind {R : RefTy} (x : Var) : Hole C (.ref R)
  | copy {R : RefTy} (l : Loc C (.ref R)) (h : (Ty.ref R).mapFree = true) : Hole C (.ref R)

/-- The statement, with the path in the hole. -/
def Hole.fill {T : Ty} : Hole C T → SPath C T → Stmt C
  | .local x, .loc l => .assignLocal x (.read l)
  | .rebind x, p => .rebind x (.path p)
  | .copy l h, p => .assign l (.copy p h)

/-- Where a memory location lands: `v = □` (a value read), `mv = □` (a
memory local bound), `mloc = □` (a reference written). -/
inductive MHole (C : Contract) : Ty → Type where
  | local {p : PrimTy} (x : Var) : MHole C (.prim p)
  | rebind {R : RefTy} (x : Var) : MHole C (.ref R)
  | write {R : RefTy} (l : MLoc C (.ref R)) : MHole C (.ref R)

def MHole.fill {T : Ty} : MHole C T → MLoc C T → Stmt C
  | .local x, l => .assignLocal x (.readMem l)
  | .rebind x, l => .rebindMem x (.alias (.loc l))
  | .write l', l => .assignMem l' (.ref (.loc l))

/-- Where a value lands: a local, a storage location, a memory location. -/
inductive VHole (C : Contract) : PrimTy → Type where
  | local {p : PrimTy} (x : Var) : VHole C p
  | store {p : PrimTy} (l : Loc C (.prim p)) : VHole C p
  | mem {p : PrimTy} (l : MLoc C (.prim p)) : VHole C p

def VHole.fill {p : PrimTy} : VHole C p → Val C p → Stmt C
  | .local x, v => .assignLocal x v
  | .store l, v => .assign l (.val v)
  | .mem l, v => .assignMem l (.val v)

/-- A fresh array's target written with the memory local it was bound to:
`tgt = mv`, a copy into storage or a reference written into memory. -/
def NewLhs.fill {R : RefTy} : NewLhs C R → MPath C (.ref R) → Stmt C
  | .store l, p => .assignFromMem l p
  | .mem l, p => .assignMem l (.ref p)

/-! ## Side conditions

What `Stmt.step` knows of a statement's parts when it fires a rule, read
off the schema variables (`RuleSyntax.sideConds`): besides `isSimple`
(`sp`/`nsp`, `se`/`nse`, `mv`/`nmp`), whether a write's target is ready for
its source to be unfolded, whether a value is a conditional, whether a
memory path can be written as it is. -/

/-- `total`: a state variable. -/
def Loc.isRoot {T : Ty} : Loc C T → Bool
  | .root .. => true
  | _ => false

/-- A target every part of which is simple (`total`, `sp.fld`, `sp[ie]`):
only into such a target is a copy's *source* unfolded
(`folks[1].account = folks[2].account;` unfolds its target first). -/
def Loc.isTarget {T : Ty} : Loc C T → Bool
  | .root .. => true
  | .field b _ _ => b.isSimple
  | .index _ b i => b.isSimple && i.isSimple

/-- A memory target every part of which is simple (`mv.fld`, `mv[ie]`). -/
def MLoc.isTarget {T : Ty} : MLoc C T → Bool
  | .field b _ _ => b.isSimple
  | .index _ b i => b.isSimple && i.isSimple

/-- A memory path written as it is (`mv`, `mv.fld`, `mv[ie]`): any other is
unfolded first (`m.account = n.inner.account;`). -/
def MPath.isBindable {T : Ty} : MPath C T → Bool
  | .var .. => true
  | .loc l => l.isTarget

/-- Not a conditional: a conditional written to storage or memory is lowered
to a branch (`ternaryToIf`), never captured. -/
def Val.notTernary {p : PrimTy} : Val C p → Bool
  | .ternary .. => false
  | _ => true

/-- The elements of the array `b` are mappings: `marr` in a rule, and
solkey's `Path[…,mappingElement]` (`storagePopSaveMappingElement`); `darr`
is its negation, `nonMappingElement`. -/
def SPath.elemMapping {T : Ty} (_ : SPath C T) : Bool := T.elemIsMapping

/-- The elements of the array `b` are primitive: `parr` in a rule, solkey's
`Path[…,primitiveElement]` (`storagePushLengthSave`); `rarr` is its negation,
`referenceElement`. -/
def SPath.elemPrim {T : Ty} (_ : SPath C T) : Bool := T.elemIsPrim

/-- A hole whose statement is ready for its path to be unfolded: a local, an
alias, or a copy into a target. -/
def Hole.isTarget {T : Ty} : Hole C T → Bool
  | .copy l _ => l.isTarget
  | _ => true

/-- A memory hole ready for its location to be unfolded: a local, a memory
local, or a reference written to a target. -/
def MHole.isTarget {T : Ty} : MHole C T → Bool
  | .write l => l.isTarget
  | _ => true

/-- A value hole ready for its value to be lowered: a local, any storage
location (whose receiver waits for the branch), or a memory target. -/
def VHole.isTarget {p : PrimTy} : VHole C p → Bool
  | .mem l => l.isTarget
  | _ => true

/-- Whether a call returns its values to targets after it (`CallRet.rets`):
KeY's `FunctionBodyStatement` (`fbs`, `functionBodyExpand`), the call of a
tuple assignment or of a specification's obligation; any other call is an
`InternalCall` (`ic`, `internalCallExpand`). -/
def CallRet.isRets : CallRet → Bool
  | .rets _ => true
  | _ => false

/-- The first argument that is not simple, if any (`functionCallArgCapture`
captures it; with none, `internalCallExpand` or `functionBodyExpand` inlines
the call). -/
def Arg.firstNonSimple : List (Arg C) → Option (Arg C)
  | [] => none
  | a :: as => if a.e.isSimple then Arg.firstNonSimple as else some a

/-- The arguments with the first one that is not simple replaced by the
local `se` it was captured into. -/
def Arg.captureFirst (se : Var) : List (Arg C) → List (Arg C)
  | [] => []
  | a :: as => if a.e.isSimple then a :: Arg.captureFirst se as else ⟨a.p, a.x, .simple (.local se)⟩ :: as

/-- A capture keeps a call separated: the argument it replaces is simple now. -/
theorem Arg.separatedFrom_captureFirst {se : Var} :
    {bound : List Var} → {args : List (Arg C)} → Arg.separatedFrom bound args = true →
      Arg.separatedFrom bound (Arg.captureFirst se args) = true
  | _, [], h => h
  | bound, a :: as, h => by
    simp only [Arg.separatedFrom, Bool.and_eq_true] at h
    simp only [Arg.captureFirst]
    split
    · simp only [Arg.separatedFrom, Bool.and_eq_true]
      exact ⟨h.1, Arg.separatedFrom_captureFirst h.2⟩
    · simp only [Arg.separatedFrom, Val.isSimple, Bool.true_or, Bool.true_and]
      exact h.2

macro_rules
  | `(tactic| side_cond) => `(tactic| first
      | rfl
      | assumption
      | (simp_all [SPath.isSimple, Val.isSimple, MPath.isSimple, Loc.isTarget, Loc.isRoot,
          MLoc.isTarget, MPath.isBindable, Val.notTernary, Hole.isTarget, MHole.isTarget,
          VHole.isTarget, SPath.elemMapping, SPath.elemPrim, Ty.elemIsMapping, Ty.elemIsPrim,
          Ty.isMapping, Ty.isPrimitive]; done)
      | fail "the rule's side condition does not hold: `Stmt.step` fires another rule here")

/-- The predicates a side condition is stated with. -/
def sidePreds : List Lean.Name :=
  [``SPath.isSimple, ``Val.isSimple, ``MPath.isSimple, ``Loc.isTarget, ``Loc.isRoot,
    ``MLoc.isTarget, ``MPath.isBindable, ``Val.notTernary, ``Hole.isTarget, ``MHole.isTarget,
    ``VHole.isTarget, ``SPath.elemMapping, ``SPath.elemPrim]

open Lean Elab Tactic Meta in
/-- Forget a derivation's side conditions: after `cases` on a derivation, a
proof that does not need to know which rule fires (soundness) clears them. -/
elab "clear_side" : tactic => withMainContext do
  let mut g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, lhs, _) := (← instantiateMVars d.type).eq? | continue
    if sidePreds.any lhs.isAppOf then g ← g.tryClear d.fvarId
  replaceMainGoal [g]

/-! ## Premises -/

/-- What a taclet leaves: an update in front of the rest (`{U} ⟨[ ]⟩`),
statements in its place (`⟨[ s₁; …; sₙ; ]⟩`), two goals (a branch, one
condition assumed in each: `se = true` and `se = false`), a goal and a check
(an `assert`: the rest with `se = true` assumed, and `se = true` itself,
KeY's "Holds" and "Violated" branches), or the whole
modality closed (`true`, `false`), or a goal per way an external call may
end (`try`).
A condition can be stuck (a local read
before it is bound), so a branch's two conditions need not cover every
state: a box goal is true of a stuck run anyway, and a diamond goal owes
that one of them holds (`Proves.split`). -/
inductive Premise (C : Contract) where
  | update (U : Upd C)
  | unfold (P : Prog C)
  | split (c c' : Fml C) (P Q : Prog C)
  /-- `c ⟹ ⟨[ P ]⟩ ; c`: the goal with `c` assumed, and `c` to prove. -/
  | check (c : Fml C) (P : Prog C)
  | done (b : Bool)
  /-- One goal per block, each in the statement's place, for every value of
  the locals it binds: `∀ xs. ⟨[ P ]⟩` (KeY's `T v;` with no initializer,
  which leaves `v` unconstrained). -/
  | branches (bs : List (List (PrimTy × Var) × Prog C))
  /-- Goals labelled as KeY labels a taclet's (`"send failed": \replacewith(…)`):
  each formula of `fs` to prove, then for each update `U` of `us` the rest
  after it, `{U} ⟨[ ..ω ]⟩ φ`, one per way the statement may end. -/
  | cases (fs : List (Fml C)) (us : List (Upd C))
  /-- A loop's invariant rule (`whileInvariantBox`, `whileInvariantDiamond`):
  the invariant `I` now ("invariant initially valid"), and, whatever the
  body's frame holds (`{anon(P)}`, `Fml.loopAnon`), from where `I` holds and
  after `U` (the variant's value, under the diamond), the body `P` to `post`
  where the condition `c` holds, the rest where `c'` does, and under the
  diamond one of them ("invariant preserved and used"). -/
  | inv (I : Fml C) (U : Upd C) (c c' : Fml C) (P : Prog C) (post : Fml C)

/-! ## solkey's branch labels -/

/-- solkey's labels of a taclet's goals, in order, as the rules above write
them (`"Holds": …`; the macro drops them): the two goals of a split or a
check, the outcomes of `branches`.  `Examples/ProofTree.lean` checks them
against this file's source. -/
def Taclet.branchLabels : List (String × List String) := [
  ("ifElseSplit", ["if s#se true", "if s#se false"]),
  ("requireSimple", ["Holds", "Reverts"]),
  ("assertSimple", ["Holds", "Violated"]),
  ("tryCallNoCallbackBox",
    ["call succeeded", "Error caught", "Panic caught", "other failure caught"]),
  ("sendNoCallbackBox", ["send succeeded", "send failed"]),
  ("sendNoCallbackDiamond", ["non-negative amount", "send succeeded", "send failed"]),
  ("loopExit", ["loop exited", "unwound to the end"]),
  ("whileInvariantBox", ["invariant initially valid", "invariant preserved and used"]),
  ("whileInvariantDiamond", ["invariant initially valid", "invariant preserved and used"])]

/-- The taclet whose goals a premise for the statement of head `c` labels:
an `if` splits by `ifElseSplit`, a `require` by `requireSimple`, an `assert`
by `assertSimple`, a `try` by `tryCallNoCallbackBox` (and
`CallbackTaclet.tryCallWithCallbackBox`, labelled alike), a send by
`sendNoCallbackBox`, or under the diamond (`diamond`) `sendNoCallbackDiamond`;
a loop by `loopExit`, the one rule of a loop with goals to label. -/
def Taclet.labelledBy (c : Lean.Name) (diamond : Bool := false) : Option String :=
  if c == ``Stmt.ite then some "ifElseSplit"
  else if c == ``Stmt.require then some "requireSimple"
  else if c == ``Stmt.assert then some "assertSimple"
  else if c == ``Stmt.tryCall then some "tryCallNoCallbackBox"
  else if c == ``Stmt.send then
    some (if diamond then "sendNoCallbackDiamond" else "sendNoCallbackBox")
  else if c == ``Stmt.loop then some "loopExit"
  else none

/-! ## Printing premises -/

section Print
open Lean Meta PrettyPrinter Delaborator SubExpr
set_option hygiene false

/-- The premise `e`; its goals labelled by `labels` (solkey's, `Taclet.branchLabels`),
the blocks of `branches` in the box's brackets when `box`. -/
def ppPremise? (e : Lean.Expr) (labels : List String := []) (box : Bool := false) :
    MetaM (Option (TSyntax `dl_premise)) := do
  let lbl (i : Nat) : Option (TSyntax `str) := labels[i]?.map Syntax.mkStrLit
  let l0 := lbl 0
  let l1 := lbl 1
  match_expr (← whnf (← instantiateMVars e)) with
  | Premise.update _ U => return some (← `(dl_premise| $(← ppUpd U):dl_upd ⟨[ ]⟩))
  | Premise.unfold _ P =>
    let some ss ← ppProg? P | return none
    return some (← `(dl_premise| ⟨[ $[$ss;]* ]⟩))
  | Premise.split _ c c' P Q =>
    let c ← ppFml c
    let c' ← ppFml c'
    match ← ppProg? P, ← ppProg? Q with
    | some ts, some fs =>
      if (← fvarName? P).isNone && (← fvarName? Q).isNone then
        return some (← `(dl_premise| $[$l0:str :]? $c:dl_fml ⟹ ⟨[ $[$ts;]* ]⟩ ;
          $[$l1:str :]? $c':dl_fml ⟹ ⟨[ $[$fs;]* ]⟩))
      else
        return some (← `(dl_premise| $[$l0:str :]? $c:dl_fml ⟹ ⟨[ $(← ppBlock P) ]⟩ ;
          $[$l1:str :]? $c':dl_fml ⟹ ⟨[ $(← ppBlock Q) ]⟩))
    | _, _ =>
      return some (← `(dl_premise| $[$l0:str :]? $c:dl_fml ⟹ ⟨[ $(← ppBlock P) ]⟩ ;
        $[$l1:str :]? $c':dl_fml ⟹ ⟨[ $(← ppBlock Q) ]⟩))
  | Premise.check _ c P =>
    let c ← ppFml c
    let some ts ← ppProg? P | return none
    return some (← `(dl_premise| $[$l0:str :]? $c:dl_fml ⟹ ⟨[ $[$ts;]* ]⟩ ; $[$l1:str :]? $c:dl_fml))
  | Premise.done _ b =>
    match_expr (← whnf b) with
    | Bool.true => return some (← `(dl_premise| true))
    | Bool.false => return some (← `(dl_premise| false))
    | _ => return none
  | Premise.branches _ bs =>
    -- a goal per block, `"label": ∀ xs. ⟨[ P ]⟩` (`[ P ]` for a box-only taclet)
    let some bs ← listElems? bs | return none
    let mut out : Array (TSyntax `dl_branch) := #[]
    for h : i in [0:bs.size] do
      let b := bs[i]
      let l := lbl i
      let b ← whnf b
      unless b.isAppOfArity ``Prod.mk 4 do return none
      let blk ← ppBlock (b.getArg! 3)
      let xs ← instantiateMVars (b.getArg! 2)
      let x? ← if let some n ← fvarName? xs then pure (some n)
        else if xs.isAppOfArity ``codeBinders 1 then fvarName? xs.appArg!
        else pure none
      let x? := x?.map fun x => nameIdent x
      if x?.isNone then
        let some #[] ← listElems? xs | return none
      out := out.push (← if box then `(dl_branch| $[$l:str :]? $[∀ $x?:ident .]? [ $blk ])
        else `(dl_branch| $[$l:str :]? $[∀ $x?:ident .]? ⟨[ $blk ]⟩))
    let some b := out[0]? | return none
    if out.size < 2 then return none
    return some (← `(dl_premise| $b:dl_branch ; $[$(out.extract 1 out.size)];*))
  | Premise.cases _ fs us =>
    -- `"label": φ` for each formula, then `"label": {U} ⟨[ ]⟩` for each update
    let some fs ← listElems? fs | return none
    let some us ← listElems? us | return none
    let mut out : Array (TSyntax `dl_case) := #[]
    for h : i in [0:fs.size] do
      let l := lbl i
      out := out.push (← `(dl_case| $[$l:str :]? $(← ppFml fs[i]):dl_fml))
    for h : j in [0:us.size] do
      let l := lbl (fs.size + j)
      out := out.push (← `(dl_case| $[$l:str :]? $(← ppUpd us[j]):dl_upd ⟨[ ]⟩))
    let some c := out[0]? | return none
    if out.size < 2 then return none
    return some (← `(dl_premise| $c:dl_case ; $[$(out.extract 1 out.size)];*))
  | Premise.inv _ I U c c' P post =>
    let I ← ppFml I
    let c ← ppFml c
    let c' ← ppFml c'
    let post ← ppFml post
    let b ← ppBlock P
    if let some #[] ← listElems? U then
      return some (← `(dl_premise| $[$l0:str :]? $I:dl_fml ; $[$l1:str :]? { anon($b) } ($I →
        $c:dl_fml ⟹ ⟨[ $b ]⟩ $post:dl_fml ; $c':dl_fml ⟹ ⟨[ ]⟩)))
    return some (← `(dl_premise| $[$l0:str :]? $I:dl_fml ; $[$l1:str :]? { anon($b) } ($I →
      $(← ppUpd U):dl_upd ($c:dl_fml ⟹ ⟨[ $b ]⟩ $post:dl_fml ; $c':dl_fml ⟹ ⟨[ ]⟩))))
  | _ => return none

/-- A premise standing alone: `dl{ p }`. -/
def delabPremise : Delab := do
  unless ← ppOn do failure
  fullApp
  let some p ← ppPremise? (← getExpr) | failure
  `(dl{ $p:dl_premise })

attribute [delab app.Solidity.Premise.update, delab app.Solidity.Premise.unfold,
  delab app.Solidity.Premise.split, delab app.Solidity.Premise.check,
  delab app.Solidity.Premise.done, delab app.Solidity.Premise.branches,
  delab app.Solidity.Premise.cases, delab app.Solidity.Premise.inv] delabPremise

/-- The type without its `autoParam` hypotheses (a taclet's side conditions),
which nothing after them depends on. -/
partial def dropSide : Lean.Expr → Lean.Expr
  | .forallE n t b bi =>
    let b' := dropSide b
    if t.isAppOfArity ``autoParam 2 && !b'.hasLooseBVar 0 then b'.lowerLooseBVars 1 1
    else .forallE n t b' bi
  | e => e

/-- The side condition `CallRet.isRets ret = b` of a taclet's type, its `b`. -/
partial def callSide : Lean.Expr → Option Lean.Expr
  | .forallE _ t b _ =>
    if t.isAppOfArity ``autoParam 2 then
      match (t.getArg! 0).eq? with
      | some (_, l, r) => if l.isAppOf ``CallRet.isRets then some r else callSide b
      | none => callSide b
    else callSide b
  | _ => none

/-- Whether a binder type of the telescope `e` mentions the bound variable `i`. -/
def usedInBinders : Lean.Expr → Nat → Bool
  | .forallE _ t b _, i => t.hasLooseBVar i || usedInBinders b (i + 1)
  | _, _ => false

/-- The binders of a taclet's type and its line.  The proof a name carries
(`hfld : C.fieldType R fld = …` for `fld`, `hgsp` for `gsp`, `hop` for `op`;
`hsep` for the arguments of a call `fbs`) stays out of sight, unless another
binder's type names it, the line saying it; binders of one type are
grouped, as Lean groups them. -/
partial def delabTacletBinders (names : Array Lean.Name)
    (acc : Array (Lean.Ident × Lean.Term × BinderInfo)) : DelabM Lean.Term := do
  let .forallE n t rest bi := ← getExpr | do
    let body ← delab
    -- consecutive binders of one type and kind, grouped
    let mut groups : Array (Array Lean.Ident × Lean.Term × BinderInfo) := #[]
    for (x, ty, bi) in acc do
      match groups.back? with
      | some (xs, ty', bi') =>
        if bi == bi' && ty.raw.structEq ty'.raw && bi != .instImplicit then
          groups := groups.pop.push (xs.push x, ty', bi')
        else groups := groups.push (#[x], ty, bi)
      | none => groups := groups.push (#[x], ty, bi)
    if groups.isEmpty then return body
    let bs ← groups.mapM fun (xs, ty, bi) => match bi with
      | .implicit => `(Lean.Parser.Term.bracketedBinderF| {$xs* : $ty})
      | .strictImplicit => `(Lean.Parser.Term.bracketedBinderF| ⦃$xs* : $ty⦄)
      | .instImplicit => `(Lean.Parser.Term.bracketedBinderF| [$(xs[0]!) : $ty])
      | .default => `(Lean.Parser.Term.bracketedBinderF| ($xs* : $ty))
    `(∀ $bs*, $body)
  -- `hx`, of a fact about the binder `x` before it
  let s := n.eraseMacroScopes.toString
  let carried ← if s == "hsep" then pure true else if !s.startsWith "h" then pure false else
    match (← getLCtx).findFromUserName? (Lean.Name.mkSimple (s.drop 1)) with
    | some d => pure (names.contains d.userName && t.containsFVar d.fvarId)
    | none => pure false
  let hide := bi == .implicit && carried && !(usedInBinders rest 0) && (← isProp t)
  let ty ← withBindingDomain delab
  withBindingBodyUnusedName fun x => do
    let x : Lean.Ident := ⟨x⟩
    let names := names.push x.getId
    if hide then return ← delabTacletBinders names acc
    delabTacletBinders names (acc.push (x, ty, bi))

end Print

end Solidity
