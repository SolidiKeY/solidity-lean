import Solidity.Calculus.RuleSyntax
import Solidity.Calculus.KeyTaclets

/-!
# The taclets

A taclet rewrites the *first active statement* of a modality:

```
      Γ ⟹ {U} ⟨ ω ⟩ φ                        Γ ⟹ ⟨ s₁; …; sₙ; ω ⟩ φ
  ─────────────────────── terminal     ───────────────────────── unfold / capture
      Γ ⟹ ⟨ s; ω ⟩ φ                          Γ ⟹ ⟨ s; ω ⟩ φ
```

(read bottom-up: to prove the conclusion, prove the premise).  In solkey a
taclet is text like (`solidityProgramRules.key`)

```
storageFieldWriteSave {
    \schemaVar \formula post;
    \schemaVar \program Path[storage,simple] sp;
    \schemaVar \program Field fld;
    \schemaVar \program SimpleExpression[primitive] se;
    \find(\modality{#mod}{c# s#sp.s#fld = s#se; #c}\endmodality(post))
    \replacewith({storage := save(storage, consr(sp, fld), se)}
        \modality{#mod}{c# #c}\endmodality(post))
};
```

Here the taclets are one inductive judgement, `s ⇒ p` ("statement `s`
rewrites to premise `p`"): one constructor per taclet, named as solkey names
it, the statement left of `⇝` its `\find`, the premise right of it its
`\replacewith`, each written in the calculus's notation (`RuleSyntax.lean`) and
printed back in it (mini-solkey's `Ch06_Taclets`).  `⟨[ ]⟩` is the
combined modality: the taclet fires under either, and its premise keeps the
one it found.  Only the two rules for `revert();` tell the modalities apart.

The storage rules are organised in three steps:

* **Step 1** unfolds a *read* whose receiver or index is not simple: it
  captures the offending part into a fresh local and re-enters;
* **Step 2** decomposes a *write*, capturing source, receiver and index in
  that order;
* **Step 3** turns a statement whose parts are all simple into an *update*.

A taclet says what fires: each constructor carries the side conditions
its schema variables state (`nsp` is not simple, `sp` is, a value written
to storage is not a conditional; `RuleSyntax.sideConds`), as hypotheses
that prove themselves (`side_cond`) and that the printers leave out, so the
rule still reads as its one line.  They are exactly what `Stmt.step`
(`Completeness.lean`) knows when it fires the rule, so every statement has
exactly one: `Stmt.complete` and `Taclet.eq_step` (`Uniqueness.lean`).
Where solkey leaves two taclets open on a statement and its strategy picks,
the side condition keeps only the one `Stmt.step` picks.

A rule over an operator is one constructor for the family (`⊕` is its
schema variable), and `++`/`--` one for all four (`⊕⊕`); solkey writes one
taclet per operator, and `KeyTaclets.lean` maps each instance back.
The rules are two lists.  `Taclet` is solkey's: every constructor transcribes
one of its taclets (`RuleShapes.tacletOrigins`), under its name, and the
`SolKey` reader walks exactly these.  `LeanTaclet` is the rules solkey does
not have (the capture of a call's argument), and `Rule` is either; the
calculus runs on `Rule`.  `Calculus/SolkeyFragment.lean` says where the first
list is enough.
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
  | .var _ => true
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

/-! ## The rule table -/

set_option hygiene false in
/-- `s ⇒ p`: the statement `s` rewrites to the premise `p`, under the
modality `m`, declaring its fresh variables at index `k`. -/
local notation:50 s:51 " ⇒ " p:51 => Taclet C k m s p

/-- The taclets. -/
inductive Taclet (C : Contract) (k : Nat) : Modality → Stmt C → Premise C → Prop where
  -- Step 1: unfold a storage read ----------------------------------------
  | storageFieldRead_unfold_rightFst :
      dl{ ⟨[ lhs = nsp.fld; ]⟩ ⇝ ⟨[ T storage sp = nsp; lhs = sp.fld; ]⟩ }
  | storageIndexRead_unfold_rightFst :
      dl{ ⟨[ lhs = nsp[e]; ]⟩ ⇝ ⟨[ T storage sp = nsp; lhs = sp[e]; ]⟩ }
  | storageIndexRead_unfold_rightSndIndex :
      dl{ ⟨[ lhs = sp[nse]; ]⟩ ⇝ ⟨[ T ie = nse; lhs = sp[ie]; ]⟩ }
  | storageFieldRead_unfold_rightSndResult :
      dl{ ⟨[ loc = sp.fld; ]⟩ ⇝ ⟨[ T storage sp' = sp.fld; loc = sp'; ]⟩ }
  | storageIndexRead_unfold_rightSndResult :
      dl{ ⟨[ loc = sp[ie]; ]⟩ ⇝ ⟨[ T storage sp' = sp[ie]; loc = sp'; ]⟩ }
  -- Step 2: decompose a storage write ------------------------------------
  | storageFieldWrite_unfold_leftFst :
      dl{ ⟨[ nsp.fld = e; ]⟩ ⇝ ⟨[ T se = e; T storage sp = nsp; sp.fld = se; ]⟩ }
  | storageFieldWriteStorageRef_unfold_leftFst :
      dl{ ⟨[ nsp.fld = path; ]⟩ ⇝ ⟨[ T storage sp = nsp; sp.fld = path; ]⟩ }
  | storageIndexWriteCaptureAllComplexRecv :
      dl{ ⟨[ nsp[e₁] = e₂; ]⟩ ⇝ ⟨[ T se = e₂; T storage sp = nsp; T ie = e₁; sp[ie] = se; ]⟩ }
  | storageIndexWriteStorageRefCaptureAllComplexRecv :
      dl{ ⟨[ nsp[e] = path; ]⟩ ⇝ ⟨[ T storage sp = nsp; T ie = e; sp[ie] = path; ]⟩ }
  | storageIndexWriteCaptureAllNonSimpleIndex :
      dl{ ⟨[ sp[nse₁] = e; ]⟩ ⇝ ⟨[ T se = e; T storage sp' = sp; T ie = nse₁; sp'[ie] = se; ]⟩ }
  | storageIndexWriteStorageRefCaptureAllNonSimpleIndex :
      dl{ ⟨[ sp[nse] = path; ]⟩ ⇝ ⟨[ T storage sp' = sp; T ie = nse; sp'[ie] = path; ]⟩ }
  | storageRootWriteValueRhsCapture :
      dl{ ⟨[ gsp = nse; ]⟩ ⇝ ⟨[ T se = nse; gsp = se; ]⟩ }
  | fieldWriteValueRhsCapture :
      dl{ ⟨[ sp.fld = nse; ]⟩ ⇝ ⟨[ T se = nse; sp.fld = se; ]⟩ }
  | indexWriteValueRhsCapture :
      dl{ ⟨[ sp[ie] = nse; ]⟩ ⇝ ⟨[ T se = nse; sp[ie] = se; ]⟩ }
  | storageFieldDelete_unfold_leftFst :
      dl{ ⟨[ delete nsp.fld; ]⟩ ⇝ ⟨[ T storage sp = nsp; delete sp.fld; ]⟩ }
  | storageIndexDelete_unfold_leftFst :
      dl{ ⟨[ delete nsp[e]; ]⟩ ⇝ ⟨[ T storage sp = nsp; delete sp[e]; ]⟩ }
  | storageIndexDeleteNonSimpleIndexCapture :
      dl{ ⟨[ delete sp[nse]; ]⟩ ⇝ ⟨[ T ie = nse; delete sp[ie]; ]⟩ }
  -- Declarations ---------------------------------------------------------
  | localValueDeclInitDrop :
      dl{ ⟨[ T v = e; ]⟩ ⇝ ⟨[ v = e; ]⟩ }
  | valueDeclSkip :
      dl{ ⟨[ T v; ]⟩ ⇝ { v := defVal(T) } ⟨[ ]⟩ }
  | storageLocalDeclInitDrop :
      dl{ ⟨[ T storage lsv = rhs; ]⟩ ⇝ ⟨[ lsv = rhs; ]⟩ }
  | storageLocalDeclSkip :
      dl{ ⟨[ T storage lsv; ]⟩ ⇝ ⟨[ ]⟩ }
  | memoryLocalDeclInitDrop :
      dl{ ⟨[ T memory mv = mrhs; ]⟩ ⇝ ⟨[ mv = mrhs; ]⟩ }
  | memoryReferenceDeclFreshAlloc :
      dl{ ⟨[ T memory mv; ]⟩ ⇝ { mv := freshId(addM(memory)) ‖ memory := addM(memory) } ⟨[ ]⟩ }
  -- Step 3: storage reads and writes as updates --------------------------
  | localValueAssign :
      dl{ ⟨[ v = se; ]⟩ ⇝ { v := se } ⟨[ ]⟩ }
  | storageRootReadSelect :
      dl{ ⟨[ v = gsp; ]⟩ ⇝ { v := find(storage, gsp) } ⟨[ ]⟩ }
  | storageFieldReadFind :
      dl{ ⟨[ v = sp.fld; ]⟩ ⇝ { v := find(storage, sp.fld) } ⟨[ ]⟩ }
  | storageIndexReadMappingFind :
      dl{ ⟨[ v = map[ie]; ]⟩ ⇝ { v := find(storage, map[ie]) } ⟨[ ]⟩ }
  | storageIndexReadArrayFind :
      dl{ ⟨[ v = arr[ie]; ]⟩ ⇝ { v := find(storage, arr[ie]) } ⟨[ ]⟩ }
  | storageRootWriteStore :
      dl{ ⟨[ gsp = se; ]⟩ ⇝ { storage := save(storage, gsp, se) } ⟨[ ]⟩ }
  | storageRootWriteCopySource :
      dl{ ⟨[ gsp = sp; ]⟩ ⇝ { storage := save(storage, gsp, find(storage, sp)) } ⟨[ ]⟩ }
  | storageFieldReadStoreRoot :
      dl{ ⟨[ gsp = sp.fr; ]⟩ ⇝ { storage := save(storage, gsp, find(storage, sp.fr)) } ⟨[ ]⟩ }
  | storageIndexReadMappingStoreRoot :
      dl{ ⟨[ gsp = map[ie]; ]⟩ ⇝ { storage := save(storage, gsp, find(storage, map[ie])) } ⟨[ ]⟩ }
  | storageIndexReadArrayStoreRoot :
      dl{ ⟨[ gsp = arr[ie]; ]⟩ ⇝ { storage := save(storage, gsp, find(storage, arr[ie])) } ⟨[ ]⟩ }
  | storageFieldWriteSave :
      dl{ ⟨[ sp.fld = se; ]⟩ ⇝ { storage := save(storage, sp.fld, se) } ⟨[ ]⟩ }
  | storageFieldWriteCopySource :
      dl{ ⟨[ sp1.fld = sp2; ]⟩ ⇝ { storage := save(storage, sp1.fld, find(storage, sp2)) } ⟨[ ]⟩ }
  | storageIndexWriteMappingSave :
      dl{ ⟨[ map[ie] = se; ]⟩ ⇝ { storage := save(storage, map[ie], se) } ⟨[ ]⟩ }
  | storageIndexWriteArraySave :
      dl{ ⟨[ arr[ie] = se; ]⟩ ⇝ { storage := save(storage, arr[ie], se) } ⟨[ ]⟩ }
  | storageIndexWriteMappingCopySource :
      dl{ ⟨[ map[ie] = sp2; ]⟩ ⇝ { storage := save(storage, map[ie], find(storage, sp2)) } ⟨[ ]⟩ }
  | storageIndexWriteArrayCopySource :
      dl{ ⟨[ arr[ie] = sp2; ]⟩ ⇝ { storage := save(storage, arr[ie], find(storage, sp2)) } ⟨[ ]⟩ }
  | storageLocalRootRebind :
      dl{ ⟨[ lsv = sp; ]⟩ ⇝ { lsv := sp } ⟨[ ]⟩ }
  | storageFieldReadBindLocalRoot :
      dl{ ⟨[ lsv = sp.fr; ]⟩ ⇝ { lsv := sp.fr } ⟨[ ]⟩ }
  | storageIndexReadMappingBindLocalRoot :
      dl{ ⟨[ lsv = map[ie]; ]⟩ ⇝ { lsv := map[ie] } ⟨[ ]⟩ }
  | storageIndexReadArrayBindLocalRoot :
      dl{ ⟨[ lsv = darr[ie]; ]⟩ ⇝ { lsv := darr[ie] } ⟨[ ]⟩ }
  | storageIndexReadArrayBindLocalRootMappingElement :
      dl{ ⟨[ lsv = marr[ie]; ]⟩ ⇝ { lsv := marr[ie] } ⟨[ ]⟩ }
  | storageRootDelete :
      dl{ ⟨[ delete gsp; ]⟩ ⇝ { storage := delAt(storage, gsp) } ⟨[ ]⟩ }
  | storageFieldDelete :
      dl{ ⟨[ delete sp.fld; ]⟩ ⇝ { storage := delAt(storage, sp.fld) } ⟨[ ]⟩ }
  | storageIndexDelete :
      dl{ ⟨[ delete map[ie]; ]⟩ ⇝ { storage := delAt(storage, map[ie]) } ⟨[ ]⟩ }
  | storageIndexArrayDelete :
      dl{ ⟨[ delete arr[ie]; ]⟩ ⇝ { storage := delAt(storage, arr[ie]) } ⟨[ ]⟩ }
  -- Lengths: KeY reads `.length` as the member `length` (`size`) ----------
  | storageLengthRead :
      dl{ ⟨[ v = sp.length; ]⟩ ⇝ { v := sp.length } ⟨[ ]⟩ }
  | storageLengthRead_unfold_rightFst :
      dl{ ⟨[ v = nsp.length; ]⟩ ⇝ ⟨[ T storage sp = nsp; v = sp.length; ]⟩ }
  | memoryLengthRead :
      dl{ ⟨[ v = mv.length; ]⟩ ⇝ { v := mv.length } ⟨[ ]⟩ }
  | memoryLengthRead_unfold_rightFst :
      dl{ ⟨[ v = nmp.length; ]⟩ ⇝ ⟨[ T memory mv = nmp; v = mv.length; ]⟩ }
  -- Operators ------------------------------------------------------------
  | binopAssignment :
      dl{ ⟨[ v = se₁ ⊕ se₂; ]⟩ ⇝ { v := se₁ ⊕ se₂ } ⟨[ ]⟩ }
  | binopUnfoldLeft :
      dl{ ⟨[ v = nse ⊕ e; ]⟩ ⇝ ⟨[ T se = nse; v = se ⊕ e; ]⟩ }
  /-- Not for `&&`/`||`: their right operand is evaluated only when the left
  does not decide (`logicalAndShortCircuitRhs`). -/
  | binopUnfoldRight (hsc : BinOp.shortCircuits op = false := by side_cond) :
      dl{ ⟨[ v = se ⊕ nse; ]⟩ ⇝ ⟨[ T se' = nse; v = se ⊕ se'; ]⟩ }
  | logicalAndShortCircuitRhs :
      dl{ ⟨[ v = se && nse; ]⟩ ⇝ ⟨[ if (se) { v = nse; v = v && true; } else { v = false; }; ]⟩ }
  | logicalOrShortCircuitRhs :
      dl{ ⟨[ v = se || nse; ]⟩ ⇝ ⟨[ if (se) { v = true; } else { v = nse; v = v || false; }; ]⟩ }
  | unopAssignment :
      dl{ ⟨[ v = ⊖se; ]⟩ ⇝ { v := ⊖se } ⟨[ ]⟩ }
  | unopCapture :
      dl{ ⟨[ v = ⊖nse; ]⟩ ⇝ ⟨[ T se = nse; v = ⊖se; ]⟩ }
  -- The conditional ------------------------------------------------------
  | ternaryToIf :
      dl{ ⟨[ lhs = se ? thenExpr : elseExpr; ]⟩ ⇝
          ⟨[ if (se) { lhs = thenExpr; } else { lhs = elseExpr; }; ]⟩ }
  | ternaryCaptureCond :
      dl{ ⟨[ lhs = nse ? thenExpr : elseExpr; ]⟩ ⇝
          ⟨[ bool se = nse; lhs = se ? thenExpr : elseExpr; ]⟩ }
  -- Compound assignment and `++`/`--` -------------------------------------
  | localOpAssign :
      dl{ ⟨[ v ⊕= se; ]⟩ ⇝ { v := v ⊕ se } ⟨[ ]⟩ }
  | storageRootOpAssign :
      dl{ ⟨[ gsp ⊕= se; ]⟩ ⇝ { storage := save(storage, gsp, gsp ⊕ se) } ⟨[ ]⟩ }
  | storageFieldOpAssign :
      dl{ ⟨[ sp.fld ⊕= se; ]⟩ ⇝ { storage := save(storage, sp.fld, sp.fld ⊕ se) } ⟨[ ]⟩ }
  | storageIndexMappingOpAssign :
      dl{ ⟨[ map[ie] ⊕= se; ]⟩ ⇝ { storage := save(storage, map[ie], map[ie] ⊕ se) } ⟨[ ]⟩ }
  | storageIndexArrayOpAssign :
      dl{ ⟨[ arr[ie] ⊕= se; ]⟩ ⇝ { storage := save(storage, arr[ie], arr[ie] ⊕ se) } ⟨[ ]⟩ }
  | memoryFieldOpAssign :
      dl{ ⟨[ mv.fld ⊕= se; ]⟩ ⇝ { memory := write(memory, mv.fld, mv.fld ⊕ se) } ⟨[ ]⟩ }
  | memoryIndexArrayOpAssign :
      dl{ ⟨[ mv[ie] ⊕= se; ]⟩ ⇝ { memory := write(memory, mv[ie], mv[ie] ⊕ se) } ⟨[ ]⟩ }
  | storageFieldOpAssignUnfoldLeftFst :
      dl{ ⟨[ nsp.fld ⊕= se; ]⟩ ⇝ ⟨[ T storage sp = nsp; sp.fld ⊕= se; ]⟩ }
  | storageIndexOpAssignUnfoldLeftFst :
      dl{ ⟨[ nsp[ie] ⊕= se; ]⟩ ⇝ ⟨[ T storage sp = nsp; sp[ie] ⊕= se; ]⟩ }
  | memoryFieldOpAssignUnfoldLeftFst :
      dl{ ⟨[ nmp.fld ⊕= se; ]⟩ ⇝ ⟨[ T memory mv = nmp; mv.fld ⊕= se; ]⟩ }
  | memoryIndexOpAssignUnfoldLeftFst :
      dl{ ⟨[ nmp[ie] ⊕= se; ]⟩ ⇝ ⟨[ T memory mv = nmp; mv[ie] ⊕= se; ]⟩ }
  | compoundAssignValueRhsCapture :
      dl{ ⟨[ l ⊕= nse; ]⟩ ⇝ ⟨[ T se = nse; l ⊕= se; ]⟩ }
  | localIncrement :
      dl{ ⟨[ v⊕⊕; ]⟩ ⇝ { v := v ± 1 } ⟨[ ]⟩ }
  | storageRootIncrement :
      dl{ ⟨[ gsp⊕⊕; ]⟩ ⇝ { storage := save(storage, gsp, gsp ± 1) } ⟨[ ]⟩ }
  | storageFieldIncrement :
      dl{ ⟨[ sp.fld⊕⊕; ]⟩ ⇝ { storage := save(storage, sp.fld, sp.fld ± 1) } ⟨[ ]⟩ }
  | storageIndexIncrement :
      dl{ ⟨[ sp[ie]⊕⊕; ]⟩ ⇝ { storage := save(storage, sp[ie], sp[ie] ± 1) } ⟨[ ]⟩ }
  | memoryFieldIncrement :
      dl{ ⟨[ mv.fld⊕⊕; ]⟩ ⇝ { memory := write(memory, mv.fld, mv.fld ± 1) } ⟨[ ]⟩ }
  | memoryIndexArrayIncrement :
      dl{ ⟨[ mv[ie]⊕⊕; ]⟩ ⇝ { memory := write(memory, mv[ie], mv[ie] ± 1) } ⟨[ ]⟩ }
  | storageFieldIncrementUnfoldLeftFst :
      dl{ ⟨[ nsp.fld⊕⊕; ]⟩ ⇝ ⟨[ T storage sp = nsp; sp.fld⊕⊕; ]⟩ }
  | storageIndexIncrementUnfoldLeftFst :
      dl{ ⟨[ nsp[ie]⊕⊕; ]⟩ ⇝ ⟨[ T storage sp = nsp; sp[ie]⊕⊕; ]⟩ }
  | memoryFieldIncrementUnfoldLeftFst :
      dl{ ⟨[ nmp.fld⊕⊕; ]⟩ ⇝ ⟨[ T memory mv = nmp; mv.fld⊕⊕; ]⟩ }
  | memoryIndexIncrementUnfoldLeftFst :
      dl{ ⟨[ nmp[ie]⊕⊕; ]⟩ ⇝ ⟨[ T memory mv = nmp; mv[ie]⊕⊕; ]⟩ }
  | localAssignIncrement :
      dl{ ⟨[ v = lv⊕⊕; ]⟩ ⇝ { lv := lv ± 1 ‖ v := lv⊕⊕ } ⟨[ ]⟩ }
  | storageRootIncrementAssignment :
      dl{ ⟨[ v = gsp⊕⊕; ]⟩ ⇝ { storage := save(storage, gsp, gsp ± 1) ‖ v := gsp⊕⊕ } ⟨[ ]⟩ }
  | storageFieldIncrementAssignment :
      dl{ ⟨[ v = sp.fld⊕⊕; ]⟩ ⇝
          { storage := save(storage, sp.fld, sp.fld ± 1) ‖ v := sp.fld⊕⊕ } ⟨[ ]⟩ }
  | storageIndexIncrementAssignment :
      dl{ ⟨[ v = sp[ie]⊕⊕; ]⟩ ⇝
          { storage := save(storage, sp[ie], sp[ie] ± 1) ‖ v := sp[ie]⊕⊕ } ⟨[ ]⟩ }
  | memoryFieldIncrementAssignment :
      dl{ ⟨[ v = mv.fld⊕⊕; ]⟩ ⇝
          { memory := write(memory, mv.fld, mv.fld ± 1) ‖ v := mv.fld⊕⊕ } ⟨[ ]⟩ }
  | memoryIndexArrayIncrementAssignment :
      dl{ ⟨[ v = mv[ie]⊕⊕; ]⟩ ⇝
          { memory := write(memory, mv[ie], mv[ie] ± 1) ‖ v := mv[ie]⊕⊕ } ⟨[ ]⟩ }
  -- Arrays ---------------------------------------------------------------
  | storagePushValueSave :
      dl{ ⟨[ sp.push(se); ]⟩ ⇝
          { storage := save(save(storage, sp[sp.length], se), sp.length, sp.length + 1) } ⟨[ ]⟩ }
  | storagePushValueCopySource :
      dl{ ⟨[ sp.push(path); ]⟩ ⇝
          { storage := save(save(storage, sp[sp.length], find(storage, path)), sp.length,
              sp.length + 1) } ⟨[ ]⟩ }
  | storagePushLengthSave :
      dl{ ⟨[ parr.push(); ]⟩ ⇝
          { storage := save(delAt(storage, parr[parr.length]), parr.length, parr.length + 1) }
          ⟨[ ]⟩ }
  | storagePushLengthSaveReferenceElement :
      dl{ ⟨[ rarr.push(); ]⟩ ⇝ { storage := save(storage, rarr.length, rarr.length + 1) } ⟨[ ]⟩ }
  | storagePushValue_unfold_rightSndArgument :
      dl{ ⟨[ sp.push(nse); ]⟩ ⇝ ⟨[ T se = nse; sp.push(se); ]⟩ }
  | storagePushValue_unfold_leftFstReceiver :
      dl{ ⟨[ nsp.push(src); ]⟩ ⇝ ⟨[ T storage sp = nsp; sp.push(src); ]⟩ }
  | storagePush_unfold_leftFstReceiver :
      dl{ ⟨[ nsp.push(); ]⟩ ⇝ ⟨[ T storage sp = nsp; sp.push(); ]⟩ }
  | storagePop_unfold_leftFstReceiver :
      dl{ ⟨[ nsp.pop(); ]⟩ ⇝ ⟨[ T storage sp = nsp; sp.pop(); ]⟩ }
  | storagePopSave :
      dl{ ⟨[ darr.pop(); ]⟩ ⇝
          { storage := save(delAt(storage, darr[darr.length - 1]), darr.length, darr.length - 1) }
          ⟨[ ]⟩ }
  | storagePopSaveMappingElement :
      dl{ ⟨[ marr.pop(); ]⟩ ⇝ { storage := save(storage, marr.length, marr.length - 1) } ⟨[ ]⟩ }
  | storageLocalRootPush_unfold_leftFstReceiver :
      dl{ ⟨[ lsv = nsp.push(); ]⟩ ⇝ ⟨[ T storage sp = nsp; lsv = sp.push(); ]⟩ }
  | storageLocalRootPushBind :
      dl{ ⟨[ lsv = darr.push(); ]⟩ ⇝
          { storage := save(storage, darr.length, darr.length + 1) ‖ lsv := darr[darr.length] }
          ⟨[ ]⟩ }
  | storageLocalRootPushBindMappingElement :
      dl{ ⟨[ lsv = marr.push(); ]⟩ ⇝
          { storage := save(storage, marr.length, marr.length + 1) ‖ lsv := marr[marr.length] }
          ⟨[ ]⟩ }
  -- Transfer -------------------------------------------------------------
  | transfer_unfold_leftFstReceiver :
      dl{ ⟨[ nadr.transfer(e); ]⟩ ⇝ ⟨[ uint se = nadr; se.transfer(e); ]⟩ }
  | transfer_unfold_rightSndArgument :
      dl{ ⟨[ sadr.transfer(nse); ]⟩ ⇝ ⟨[ uint se = nse; sadr.transfer(se); ]⟩ }
  /-- The payment on the ledger, under the box: `sadr`'s entry down by `se`,
  unless `sadr` is the contract itself (`this`), which books nothing; nothing
  else changes.  The box only: the diamond has no rule (`LeanTaclet.transferDiamond`). -/
  | transferNoCallbackBox :
      dl{ [ sadr.transfer(se); ] ⇝
          { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩ }
  -- Send -----------------------------------------------------------------
  | send_unfold_leftFstReceiver :
      dl{ ⟨[ pv = nadr.send(e); ]⟩ ⇝ ⟨[ uint se = nadr; pv = se.send(e); ]⟩ }
  | send_unfold_rightSndArgument :
      dl{ ⟨[ pv = sadr.send(nse); ]⟩ ⇝ ⟨[ uint se = nse; pv = sadr.send(se); ]⟩ }
  /-- A send under the box: taken, the payment booked as `transfer` books it
  and `pv` true; refused, nothing booked and `pv` false (`Semantics.sendAt`,
  where the transaction's oracle says which). -/
  | sendNoCallbackBox :
      dl{ [ pv = sadr.send(se); ] ⇝
          "send succeeded":
            { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) ‖ pv := true }
            ⟨[ ]⟩
        ; "send failed": { pv := false } ⟨[ ]⟩ }
  /-- The same under the diamond, and the amount owed non-negative: a send
  of a negative amount is stuck, as a `transfer` of one is. -/
  | sendNoCallbackDiamond :
      dl{ ⟨ pv = sadr.send(se); ⟩ ⇝
          "non-negative amount": 0 <= se
        ; "send succeeded":
            { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) ‖ pv := true }
            ⟨[ ]⟩
        ; "send failed": { pv := false } ⟨[ ]⟩ }
  -- Memory ---------------------------------------------------------------
  | memoryFieldRead_unfold_rightFst :
      dl{ ⟨[ lhs = nmp.fld; ]⟩ ⇝ ⟨[ T memory mv = nmp; lhs = mv.fld; ]⟩ }
  | memoryIndexRead_unfold_rightFst :
      dl{ ⟨[ lhs = nmp[e]; ]⟩ ⇝ ⟨[ T memory mv = nmp; lhs = mv[e]; ]⟩ }
  | memoryIndexRead_unfold_rightSndIndex :
      dl{ ⟨[ lhs = mv[nse]; ]⟩ ⇝ ⟨[ T ie = nse; lhs = mv[ie]; ]⟩ }
  | memoryFieldRead :
      dl{ ⟨[ v = mv.fld; ]⟩ ⇝ { v := read(memory, mv.fld) } ⟨[ ]⟩ }
  | memoryIndexReadArrayValue :
      dl{ ⟨[ v = mv[ie]; ]⟩ ⇝ { v := read(memory, mv[ie]) } ⟨[ ]⟩ }
  | memoryRootRebind :
      dl{ ⟨[ mv₁ = mv₂; ]⟩ ⇝ { mv₁ := mv₂ } ⟨[ ]⟩ }
  | memoryFieldReadAliasRoot :
      dl{ ⟨[ mv₁ = mv₂.fr; ]⟩ ⇝ { mv₁ := read(memory, mv₂.fr) } ⟨[ ]⟩ }
  | memoryIndexReadArrayMemory :
      dl{ ⟨[ mv₁ = mv₂[ie]; ]⟩ ⇝ { mv₁ := read(memory, mv₂[ie]) } ⟨[ ]⟩ }
  | memoryFieldWrite :
      dl{ ⟨[ mv.fld = se; ]⟩ ⇝ { memory := write(memory, mv.fld, se) } ⟨[ ]⟩ }
  | memoryIndexWriteArray :
      dl{ ⟨[ mv[ie] = se; ]⟩ ⇝ { memory := write(memory, mv[ie], se) } ⟨[ ]⟩ }
  | memoryFieldWriteCopy :
      dl{ ⟨[ mv.fld = mpath; ]⟩ ⇝ { memory := write(memory, mv.fld, mpath) } ⟨[ ]⟩ }
  | memoryIndexWriteCopy :
      dl{ ⟨[ mv[ie] = mpath; ]⟩ ⇝ { memory := write(memory, mv[ie], mpath) } ⟨[ ]⟩ }
  | memoryFieldWrite_unfold_leftFst :
      dl{ ⟨[ nmp.fld = msrc; ]⟩ ⇝ ⟨[ T memory mv = nmp; mv.fld = msrc; ]⟩ }
  | memoryIndexWriteCaptureAllComplexRecv :
      dl{ ⟨[ nmp[e₁] = e₂; ]⟩ ⇝ ⟨[ T se = e₂; T memory mv = nmp; T ie = e₁; mv[ie] = se; ]⟩ }
  | memoryIndexWriteMemRefCaptureAllComplexRecv :
      dl{ ⟨[ nmp[e] = mpath; ]⟩ ⇝ ⟨[ T memory mv = nmp; T ie = e; mv[ie] = mpath; ]⟩ }
  /-- KeY re-binds the receiver too (`T memory mv' = mv;`); a memory local is
  untyped (`MPath.var`), so that alias would not fix its array type, and it
  renames `mv` and nothing else. -/
  | memoryIndexWriteCaptureAllNonSimpleIndex :
      dl{ ⟨[ mv[nse₁] = e; ]⟩ ⇝ ⟨[ T se = e; T ie = nse₁; mv[ie] = se; ]⟩ }
  | memoryIndexWriteMemRefCaptureAllNonSimpleIndex :
      dl{ ⟨[ mv[nse] = mpath; ]⟩ ⇝ ⟨[ T ie = nse; mv[ie] = mpath; ]⟩ }
  | memoryFieldWriteUnfoldSource :
      dl{ ⟨[ mv.fld = nse; ]⟩ ⇝ ⟨[ T se = nse; mv.fld = se; ]⟩ }
  | memoryIndexWriteUnfoldSource :
      dl{ ⟨[ mv[ie] = nse; ]⟩ ⇝ ⟨[ T se = nse; mv[ie] = se; ]⟩ }
  /-- A memory local deleted is bound to a fresh default object. -/
  | memoryRootDeleteFreshRebind :
      dl{ ⟨[ delete mv; ]⟩ ⇝ { mv := freshId(addM(memory)) ‖ memory := addM(memory) } ⟨[ ]⟩ }
  | memoryFieldDeletePrimitive :
      dl{ ⟨[ delete mv.pfld; ]⟩ ⇝ { memory := write(memory, mv.pfld, defVal(T)) } ⟨[ ]⟩ }
  /-- A member of reference type deleted is written a fresh default object. -/
  | memoryFieldDeleteReference :
      dl{ ⟨[ delete mv.rfld; ]⟩ ⇝
          { memory := write(addM(memory), mv.rfld, freshId(addM(memory))) } ⟨[ ]⟩ }
  | memoryIndexDeletePrimitive :
      dl{ ⟨[ delete pmv[ie]; ]⟩ ⇝ { memory := write(memory, pmv[ie], defVal(T)) } ⟨[ ]⟩ }
  | memoryIndexDeleteReference :
      dl{ ⟨[ delete rmv[ie]; ]⟩ ⇝
          { memory := write(addM(memory), rmv[ie], freshId(addM(memory))) } ⟨[ ]⟩ }
  | memoryFieldDelete_unfold_leftFst :
      dl{ ⟨[ delete nmp.fld; ]⟩ ⇝ ⟨[ T memory mv = nmp; delete mv.fld; ]⟩ }
  | memoryIndexDelete_unfold_leftFst :
      dl{ ⟨[ delete nmp[e]; ]⟩ ⇝ ⟨[ T memory mv = nmp; delete mv[e]; ]⟩ }
  | memoryIndexDeleteNonSimpleIndexCapture :
      dl{ ⟨[ delete mv[nse]; ]⟩ ⇝ ⟨[ T ie = nse; delete mv[ie]; ]⟩ }
  /-- `new T(se)`: a fresh array of `se` defaults, bound to `mv`. -/
  | memoryArrayFreshAlloc :
      dl{ ⟨[ mv = new T(se); ]⟩ ⇝
          { mv := freshId(copySt(memory, newArr(se))) ‖ memory := copySt(memory, newArr(se)) }
          ⟨[ ]⟩ }
  /-- A fresh array written anywhere else is bound to a fresh memory local first. -/
  | newArrayCapture :
      dl{ ⟨[ tgt = new T(se); ]⟩ ⇝ ⟨[ T memory mv = new T(se); tgt = mv; ]⟩ }
  -- Storage and memory ---------------------------------------------------
  | memoryStorageCopy :
      dl{ ⟨[ mv = sp; ]⟩ ⇝
          { mv := freshId(copySt(memory, find(storage, sp))) ‖
            memory := copySt(memory, find(storage, sp)) } ⟨[ ]⟩ }
  | memoryStorageCopyUnfold :
      dl{ ⟨[ mv = nsp; ]⟩ ⇝ ⟨[ T storage sp = nsp; mv = sp; ]⟩ }
  | memoryToStorageStoreRoot :
      dl{ ⟨[ gsp = mpath; ]⟩ ⇝ { storage := save(storage, gsp, copyMem(mtSt, memory, mpath)) } ⟨[ ]⟩ }
  | memoryToStorageFieldCopyRoot :
      dl{ ⟨[ sp.fld = mpath; ]⟩ ⇝ { storage := save(storage, sp.fld, copyMem(mtSt, memory, mpath)) } ⟨[ ]⟩ }
  | memoryToStorageIndexMappingCopyRoot :
      dl{ ⟨[ map[ie] = mpath; ]⟩ ⇝ { storage := save(storage, map[ie], copyMem(mtSt, memory, mpath)) } ⟨[ ]⟩ }
  | memoryToStorageIndexArrayCopyRoot :
      dl{ ⟨[ arr[ie] = mpath; ]⟩ ⇝ { storage := save(storage, arr[ie], copyMem(mtSt, memory, mpath)) } ⟨[ ]⟩ }
  | memoryToStorageField_unfold_leftFst :
      dl{ ⟨[ nsp.fld = mpath; ]⟩ ⇝ ⟨[ T storage sp = nsp; sp.fld = mpath; ]⟩ }
  | memoryToStorageIndexCaptureAllComplexRecv :
      dl{ ⟨[ nsp[e] = mpath; ]⟩ ⇝ ⟨[ T storage sp = nsp; T ie = e; sp[ie] = mpath; ]⟩ }
  | memoryToStorageIndexCaptureAllNonSimpleIndex :
      dl{ ⟨[ sp[nse] = mpath; ]⟩ ⇝ ⟨[ T storage sp' = sp; T ie = nse; sp'[ie] = mpath; ]⟩ }
  -- Control flow ---------------------------------------------------------
  | ifElseUnfold :
      dl{ ⟨[ if (nse) thenStm else elseStm; ]⟩ ⇝ ⟨[ bool se = nse; if (se) thenStm else elseStm; ]⟩ }
  /-- Two goals: the `then` branch where `se` is `true`, the `else` branch where
  it is `false` (solkey's `\add(se = TRUE ==>)`). -/
  | ifElseSplit :
      dl{ ⟨[ if (se) thenStm else elseStm; ]⟩ ⇝
          "if s#se true": se = true ⟹ ⟨[ thenStm ]⟩ ; "if s#se false": se = false ⟹ ⟨[ elseStm ]⟩ }
  | requireConditionCapture :
      dl{ ⟨[ require(nse); ]⟩ ⇝ ⟨[ bool se = nse; require(se); ]⟩ }
  /-- A guard: if `se` holds the program goes on, if not it reverts. -/
  | requireSimple :
      dl{ ⟨[ require(se); ]⟩ ⇝ "Holds": se = true ⟹ ⟨[ ]⟩ ; "Reverts": se = false ⟹ ⟨[ revert(); ]⟩ }
  | assertConditionCapture :
      dl{ ⟨[ assert(nse); ]⟩ ⇝ ⟨[ bool se = nse; assert(se); ]⟩ }
  /-- A check: if `se` holds the program goes on, and `se` must hold, under
  either modality — a failed `assert` panics, which no modality accepts. -/
  | assertSimple :
      dl{ ⟨[ assert(se); ]⟩ ⇝ "Holds": se = true ⟹ ⟨[ ]⟩ ; "Violated": se = true }
  /-- A reverted run satisfies every box formula: the box closes to `true`. -/
  | revertBox :
      dl{ [ revert(); ] ⇝ true }
  /-- A reverted run satisfies no diamond formula: the diamond closes to `false`. -/
  | revertDiamond :
      dl{ ⟨ revert(); ⟩ ⇝ false }
  -- Calls ----------------------------------------------------------------
  /-- A call with targets (a tuple assignment's, a specification's
  obligation's) whose arguments are all simple runs its body: the
  parameters declared with the arguments, the return variables declared, the
  body; the targets are the statements after it (KeY's
  `expand_function_body`). -/
  | functionBodyExpand :
      dl{ ⟨[ fbs; ]⟩ ⇝ ⟨[ expand_function_body(fbs); ]⟩ }
  /-- Any other call whose arguments are all simple (`f(a);`, `y = f(a);`)
  runs its body: the parameters declared with the arguments, the return
  variable declared, the body, the result assigned. -/
  | internalCallExpand :
      dl{ ⟨[ ic; ]⟩ ⇝ ⟨[ expand_function_body(ic); ]⟩ }
  -- External calls -------------------------------------------------------
  /-- A `try` without callbacks: a goal for each way the call may end, the
  block of its clause in the statement's place, for every value of the
  locals the outcome binds.  The callee runs no code of this contract, so
  the state is the caller's; a call that reverts in the caller (no code at
  the address, data that does not decode) satisfies the box. -/
  | tryCallNoCallbackBox :
      dl{ [ try call returns (rets) body catch Error errorBody
              catch Panic (code) panicBody catch otherBody; ] ⇝
          "call succeeded": ∀ rets. [ body ] ; "Error caught": [ errorBody ]
          ; "Panic caught": ∀ code. [ panicBody ] ; "other failure caught": [ otherBody ] }

/-! ## The rules solkey does not have

`Taclet` is solkey's calculus: every constructor transcribes a taclet of
`solidityProgramRules.key` (`RuleShapes.tacletOrigins`).  `LeanTaclet` is the
rest of this calculus, the rules with no taclet upstream, each a proposal for
it.  On a program that never needs one (`Calculus/SolkeyFragment.lean`)
solkey's rules alone derive what the whole calculus derives. -/

/-- The rules with no solkey taclet. -/
inductive LeanTaclet (C : Contract) (k : Nat) : Modality → Stmt C → Premise C → Prop where
  /-- An argument that is not simple is captured into a fresh local first,
  the leftmost first: `y = f(x + 1);` is `uint se = x + 1; y = f(se);` (the
  `unfoldArgument` rule). -/
  | functionCallArgCapture {f : Name} {args : List (Arg C)} {hsep : Arg.separatedFrom [] args = true}
      {ret : CallRet} {body : List (Stmt C)} {a : Arg C}
      (hcap : Arg.firstNonSimple args = some a := by side_cond) :
      dl[LeanTaclet C k]{ ⟨[ ‹.call f args hsep ret body›; ]⟩ ⇝
        ⟨[ ‹.declLocal a.p (.fresh "se" k) (some a.e)›;
          ‹.call f (Arg.captureFirst (.fresh "se" k) args) (Arg.separatedFrom_captureFirst hsep)
            ret body›; ]⟩ }

  /-- A `try` under the diamond closes to `false`.  solkey has no diamond
  rule: the call may revert in the caller (no code at the address, data that
  does not decode), which no clause catches and no formula rules out. -/
  | tryCallDiamond :
      dl[LeanTaclet C k]{ ⟨ try call returns (rets) body catch Error errorBody
          catch Panic (code) panicBody catch otherBody; ⟩ ⇝ false }

  /-- A payment under the diamond closes to `false`.  solkey books a payment
  under the box only (`transferNoCallbackBox`): whether the world pays is not
  the calculus's (`Evm.compile_correct`, where a refused payment reverts the
  machine alone), so no diamond over a payment is derived. -/
  | transferDiamond :
      dl[LeanTaclet C k]{ ⟨ sadr.transfer(se); ⟩ ⇝ false }

  /-- solkey's `whileUnwind`, bounded: a loop that may still be unwound `n + 1`
  times is one iteration, then the loop that may be unwound `n` times (KeY's
  `if (s#cond) { s#body while (s#cond) s#body }`).  The bound is Lean's
  (`/// @custom:key unwind n`), so that symbolic execution ends; solkey's
  strategy unwinds without one. -/
  | whileUnwind {cond : Val C .bool} :
      dl[LeanTaclet C k]{ ⟨[ /// @custom:key unwind n + 1
          while (cond) body; ]⟩ ⇝
        ⟨[ if (cond) { body; /// @custom:key unwind n
          while (cond) body; }; ]⟩ }

  /-- A loop unwound to its bound ends there: the rest with the condition
  false assumed, and that it is false (`Premise.check`).  Not
  `assert(!cond)`, which would make running out of unwindings a failure of
  the program; and not a capture of the condition, which the loop must
  evaluate afresh.  A loop with no clause is `unwind 0`. -/
  | loopExit {cond : Val C .bool} :
      dl[LeanTaclet C k]{ ⟨[ /// @custom:key unwind 0
          while (cond) body; ]⟩ ⇝
        "loop exited": defined(cond) ∧ defined(false) ∧ cond ≐ false ⟹ ⟨[ ]⟩ ;
        "unwound to the end": defined(cond) ∧ defined(false) ∧ cond ≐ false }

  /-- A loop with an invariant closes to `false`, under either modality,
  until its rules land (`docs/loops.md`, stage L4: solkey's
  `whileInvariantBox`, `whileInvariantDiamond`): sound, and nothing about it
  is derived. -/
  | whileClose {cond : Val C .bool} :
      dl[LeanTaclet C k]{ ⟨[ /// @custom:key invariant inv
          while (cond) body; ]⟩ ⇝ false }

/-- A rule of the calculus: solkey's, or one it does not have. -/
inductive Rule (C : Contract) (k : Nat) (m : Modality) (s : Stmt C) (p : Premise C) : Prop where
  | key (d : Taclet C k m s p)
  | lean (d : LeanTaclet C k m s p)

/-! ## The callback taclets

`transferSemantics:withCallback`: `sadr.transfer(se);` when the recipient may
call back into the contract.  Its premise is `transferNoCallbackBox`'s, the
booking `{net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se)}`,
read differently (`Calculus/Callback.lean`): the contract invariant after
the booking ("invariant on exit"), and the rest of the program resumed from
any state the callee may leave in which the invariant holds ("resume after
callback").  The box only, as solkey's calculus of payments is.

They are not `Taclet` constructors: `Taclet` is sound for `Stmt.run`, which
books a transfer and returns, and these are sound for the callback reading
(`holdsC`), in which the other semantics' `transferNoCallbackBox` is not. -/

/-- The callback taclets: the statement they fire on, under the modality
they are for, and their premise: a transfer's booking, a
`try`'s blocks (read in `Calculus/Callback.lean` with the invariant on exit,
and the call's success resumed from any state the callee may leave in which
it holds). -/
inductive CallbackTaclet (C : Contract) : Modality → Stmt C → Premise C → Prop where
  | transferWithCallbackBox :
      dl[CallbackTaclet C]{ [ sadr.transfer(se); ] ⇝
        { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩ }
  | sendWithCallbackBox :
      dl[CallbackTaclet C]{ [ pv = sadr.send(se); ] ⇝
          "send succeeded":
            { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) ‖ pv := true }
            ⟨[ ]⟩
        ; "send failed": { pv := false } ⟨[ ]⟩ }
  | tryCallWithCallbackBox :
      dl[CallbackTaclet C]{ [ try call returns (rets) body catch Error errorBody
              catch Panic (code) panicBody catch otherBody; ] ⇝
          "call succeeded": ∀ rets. [ body ] ; "Error caught": [ errorBody ]
          ; "Panic caught": ∀ code. [ panicBody ] ; "other failure caught": [ otherBody ] }

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
  ("loopExit", ["loop exited", "unwound to the end"])]

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

/-! ## Printing taclets and premises

`#check @Taclet.storageFieldWriteSave` prints the taclet as it is written
above: the `\find` with the modality it is for, and the premise. -/

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
  | _ => return none

/-- `Taclet C k m s p`: `dl{ ⟨[ s; ]⟩ ⇝ p }`, with the modality it is for;
a rule of another judgement `dl[LeanTaclet C k]{ … }`, `dl[CallbackTaclet C]{ … }`. -/
@[delab app.Solidity.Taclet, delab app.Solidity.LeanTaclet, delab app.Solidity.CallbackTaclet]
def delabTaclet : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  -- the judgement's own arguments: `C k`, or `C` for `CallbackTaclet`
  let n := if c == ``CallbackTaclet then 1 else 2
  guard (e.getAppNumArgs == n + 3)
  let st ← whnf (e.getArg! (n + 1))
  let m ← whnf (e.getArg! n)
  let labels := (do (← Taclet.branchLabels.lookup
    (← Taclet.labelledBy (← st.getAppFn.constName?) (m.isConstOf ``Modality.diamond))))
  let some p ← ppPremise? (e.getArg! (n + 2)) (labels.getD []) (m.isConstOf ``Modality.box)
    | failure
  let s ← ppStmt (e.getArg! (n + 1))
  if isEscape s then failure
  -- `fbs`, `ic` are calls with simple arguments (`functionBodyExpand`'s,
  -- `internalCallExpand`'s); a rule of another judgement fires on other
  -- calls (`functionCallArgCapture`)
  let s ← match s with
    | `(sol_stmt| $x:ident) =>
      if (x.getId == `fbs || x.getId == `ic) && c != ``Taclet then
        `(sol_stmt| ‹$(← escapeTerm (e.getArg! (n + 1))):term›)
      else pure s
    | _ => pure s
  if c == ``Taclet then
    match_expr m with
    | Modality.box => `(dl{ [ $s:sol_stmt; ] ⇝ $p })
    | Modality.diamond => `(dl{ ⟨ $s:sol_stmt; ⟩ ⇝ $p })
    | _ => `(dl{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })
  else
    let args ← (List.range n).toArray.mapM fun i => withNaryArg i delab
    let J ← `($(mkIdent (← unresolveNameGlobal c)) $args*)
    match_expr m with
    | Modality.box => `(dl[ $J ]{ [ $s:sol_stmt; ] ⇝ $p })
    | Modality.diamond => `(dl[ $J ]{ ⟨ $s:sol_stmt; ⟩ ⇝ $p })
    | _ => `(dl[ $J ]{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })

/-- A premise standing alone: `dl{ p }`. -/
def delabPremise : Delab := do
  unless ← ppOn do failure
  fullApp
  let some p ← ppPremise? (← getExpr) | failure
  `(dl{ $p:dl_premise })

attribute [delab app.Solidity.Premise.update, delab app.Solidity.Premise.unfold,
  delab app.Solidity.Premise.split, delab app.Solidity.Premise.check,
  delab app.Solidity.Premise.done, delab app.Solidity.Premise.branches,
  delab app.Solidity.Premise.cases] delabPremise

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

/-- A taclet's side conditions and the proofs its names carry stay out of
sight (`delabTacletBinders`): `#check @Taclet.x` prints its schema variables
and its line, as `sideConds` read them off the line.  `set_option pp.sol.dl
false` shows them. -/
@[delab forallE]
def delabTacletSide : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  let b := e.getForallBody
  unless b.isAppOf ``Taclet || b.isAppOf ``LeanTaclet || b.isAppOf ``CallbackTaclet do failure
  -- a call without targets is KeY's `ic` (`hrets : CallRet.isRets ret = false`)
  let ic := (callSide e).any (·.isConstOf ``Bool.false)
  withTheReader Core.Context (fun c => { c with options := c.options.setBool `pp.sol.ic ic }) <|
    withTheReader SubExpr (fun s => { s with expr := dropSide e }) (delabTacletBinders #[] #[])

end Print

end Solidity
