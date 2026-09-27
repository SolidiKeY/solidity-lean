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
  | .index b i => b.isSimple && i.isSimple

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
condition assumed in each: `se = true` and `se = false`), or the whole
modality closed (`true`, `false`).  A condition can be stuck (a local read
before it is bound), so a branch's two conditions need not cover every
state: a box goal is true of a stuck run anyway, and a diamond goal owes
that one of them holds (`Proves.split`). -/
inductive Premise (C : Contract) where
  | update (U : Upd C)
  | unfold (P : Prog C)
  | split (c c' : Fml C) (P Q : Prog C)
  | done (b : Bool)

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
      dl{ ⟨[ v = gsp; ]⟩ ⇝ { v := select(storage, gsp) } ⟨[ ]⟩ }
  | storageFieldReadFind :
      dl{ ⟨[ v = sp.fld; ]⟩ ⇝ { v := find(storage, sp.fld) } ⟨[ ]⟩ }
  | storageIndexReadMappingFind :
      dl{ ⟨[ v = map[ie]; ]⟩ ⇝ { v := find(storage, map[ie]) } ⟨[ ]⟩ }
  | storageIndexReadArrayFind :
      dl{ ⟨[ v = arr[ie]; ]⟩ ⇝ { v := find(storage, arr[ie]) } ⟨[ ]⟩ }
  | storageRootWriteStore :
      dl{ ⟨[ gsp = se; ]⟩ ⇝ { storage := store(storage, gsp, se) } ⟨[ ]⟩ }
  | storageRootWriteCopySource :
      dl{ ⟨[ gsp = sp; ]⟩ ⇝ { storage := store(storage, gsp, find(storage, sp)) } ⟨[ ]⟩ }
  | storageFieldReadStoreRoot :
      dl{ ⟨[ gsp = sp.fr; ]⟩ ⇝ { storage := store(storage, gsp, find(storage, sp.fr)) } ⟨[ ]⟩ }
  | storageIndexReadMappingStoreRoot :
      dl{ ⟨[ gsp = map[ie]; ]⟩ ⇝ { storage := store(storage, gsp, find(storage, map[ie])) } ⟨[ ]⟩ }
  | storageIndexReadArrayStoreRoot :
      dl{ ⟨[ gsp = arr[ie]; ]⟩ ⇝ { storage := store(storage, gsp, find(storage, arr[ie])) } ⟨[ ]⟩ }
  | storageFieldWriteSave :
      dl{ ⟨[ sp.fld = se; ]⟩ ⇝ { storage := save(storage, sp.fld, se) } ⟨[ ]⟩ }
  | storageFieldWriteCopySource :
      dl{ ⟨[ sp.fld = sp2; ]⟩ ⇝ { storage := save(storage, sp.fld, find(storage, sp2)) } ⟨[ ]⟩ }
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
      dl{ ⟨[ lhs = se ? e₁ : e₂; ]⟩ ⇝ ⟨[ if (se) { lhs = e₁; } else { lhs = e₂; }; ]⟩ }
  | ternaryCaptureCond :
      dl{ ⟨[ lhs = nse ? e₁ : e₂; ]⟩ ⇝ ⟨[ bool se = nse; lhs = se ? e₁ : e₂; ]⟩ }
  -- Compound assignment and `++`/`--` -------------------------------------
  | localOpAssign :
      dl{ ⟨[ v ⊕= se; ]⟩ ⇝ { v := v ⊕ se } ⟨[ ]⟩ }
  | storageRootOpAssign :
      dl{ ⟨[ gsp ⊕= se; ]⟩ ⇝ { storage := store(storage, gsp, gsp ⊕ se) } ⟨[ ]⟩ }
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
      dl{ ⟨[ gsp⊕⊕; ]⟩ ⇝ { storage := store(storage, gsp, gsp ± 1) } ⟨[ ]⟩ }
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
      dl{ ⟨[ vp = v⊕⊕; ]⟩ ⇝ { v := v ± 1 ‖ vp := v⊕⊕ } ⟨[ ]⟩ }
  | storageRootIncrementAssignment :
      dl{ ⟨[ v = gsp⊕⊕; ]⟩ ⇝ { storage := store(storage, gsp, gsp ± 1) ‖ v := gsp⊕⊕ } ⟨[ ]⟩ }
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
  | transferNoCallback :
      dl{ ⟨[ sadr.transfer(se); ]⟩ ⇝ { transfer(sadr, se) } ⟨[ ]⟩ }
  -- Memory ---------------------------------------------------------------
  | memoryFieldRead_unfold_rightFst :
      dl{ ⟨[ lhs = nmp.fld; ]⟩ ⇝ ⟨[ T memory mv = nmp; lhs = mv.fld; ]⟩ }
  | memoryIndexRead_unfold_rightFst :
      dl{ ⟨[ lhs = nmp[e]; ]⟩ ⇝ ⟨[ T memory mv = nmp; lhs = mv[e]; ]⟩ }
  | memoryIndexRead_unfold_rightSndIndex :
      dl{ ⟨[ lhs = mv[nse]; ]⟩ ⇝ ⟨[ T ie = nse; lhs = mv[ie]; ]⟩ }
  | memoryFieldReadHeap :
      dl{ ⟨[ v = mv.fld; ]⟩ ⇝ { v := read(memory, mv.fld) } ⟨[ ]⟩ }
  | memoryIndexReadHeap :
      dl{ ⟨[ v = mv[ie]; ]⟩ ⇝ { v := read(memory, mv[ie]) } ⟨[ ]⟩ }
  | memoryRootAlias :
      dl{ ⟨[ mv₁ = mv₂; ]⟩ ⇝ { mv₁ := mv₂ } ⟨[ ]⟩ }
  | memoryFieldReadAliasRoot :
      dl{ ⟨[ mv₁ = mv₂.fr; ]⟩ ⇝ { mv₁ := read(memory, mv₂.fr) } ⟨[ ]⟩ }
  | memoryIndexReadAliasRoot :
      dl{ ⟨[ mv₁ = mv₂[ie]; ]⟩ ⇝ { mv₁ := read(memory, mv₂[ie]) } ⟨[ ]⟩ }
  | memoryFieldWriteStore :
      dl{ ⟨[ mv.fld = se; ]⟩ ⇝ { memory := write(memory, mv.fld, se) } ⟨[ ]⟩ }
  | memoryIndexWriteStore :
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
      dl{ ⟨[ gsp = mpath; ]⟩ ⇝ { storage := store(storage, gsp, copyMem(mtSt, memory, mpath)) } ⟨[ ]⟩ }
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
      dl{ ⟨[ if (nse) thn else els; ]⟩ ⇝ ⟨[ bool se = nse; if (se) thn else els; ]⟩ }
  /-- Two goals: the `then` branch where `se` is `true`, the `else` branch where
  it is `false` (solkey's `\add(se = TRUE ==>)`). -/
  | ifElseSplit :
      dl{ ⟨[ if (se) thn else els; ]⟩ ⇝ se = true ⟹ ⟨[ thn ]⟩ ; se = false ⟹ ⟨[ els ]⟩ }
  | requireConditionCapture :
      dl{ ⟨[ require(nse); ]⟩ ⇝ ⟨[ bool se = nse; require(se); ]⟩ }
  /-- A guard: if `se` holds the program goes on, if not it reverts. -/
  | requireSimple :
      dl{ ⟨[ require(se); ]⟩ ⇝ se = true ⟹ ⟨[ ]⟩ ; se = false ⟹ ⟨[ revert(); ]⟩ }
  | assertConditionCapture :
      dl{ ⟨[ assert(nse); ]⟩ ⇝ ⟨[ bool se = nse; assert(se); ]⟩ }
  | assertSimple :
      dl{ ⟨[ assert(se); ]⟩ ⇝ se = true ⟹ ⟨[ ]⟩ ; se = false ⟹ ⟨[ revert(); ]⟩ }
  /-- A reverted run satisfies every box formula: the box closes to `true`. -/
  | revertBox :
      dl{ [ revert(); ] ⇝ true }
  /-- A reverted run satisfies no diamond formula: the diamond closes to `false`. -/
  | revertDiamond :
      dl{ ⟨ revert(); ⟩ ⇝ false }

/-! ## Printing taclets and premises

`#check @Taclet.storageFieldWriteSave` prints the taclet as it is written
above: the `\find` with the modality it is for, and the premise. -/

section Print
open Lean Meta PrettyPrinter Delaborator SubExpr
set_option hygiene false

def ppPremise? (e : Lean.Expr) : MetaM (Option (TSyntax `dl_premise)) := do
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
        return some (← `(dl_premise| $c:dl_fml ⟹ ⟨[ $[$ts;]* ]⟩ ; $c':dl_fml ⟹ ⟨[ $[$fs;]* ]⟩))
      else
        return some (← `(dl_premise| $c:dl_fml ⟹ ⟨[ $(← ppBlock P) ]⟩ ; $c':dl_fml ⟹ ⟨[ $(← ppBlock Q) ]⟩))
    | _, _ =>
      return some (← `(dl_premise| $c:dl_fml ⟹ ⟨[ $(← ppBlock P) ]⟩ ; $c':dl_fml ⟹ ⟨[ $(← ppBlock Q) ]⟩))
  | Premise.done _ b =>
    match_expr (← whnf b) with
    | Bool.true => return some (← `(dl_premise| true))
    | Bool.false => return some (← `(dl_premise| false))
    | _ => return none
  | _ => return none

/-- `Taclet C k m s p`: `dl{ ⟨[ s; ]⟩ ⇝ p }`, with the modality it is for. -/
@[delab app.Solidity.Taclet]
def delabTaclet : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 5)
  let some p ← ppPremise? (e.getArg! 4) | failure
  let s ← ppStmt (e.getArg! 3)
  if isEscape s then failure
  match_expr (← whnf (e.getArg! 2)) with
  | Modality.box => `(dl{ [ $s:sol_stmt; ] ⇝ $p })
  | Modality.diamond => `(dl{ ⟨ $s:sol_stmt; ⟩ ⇝ $p })
  | _ => `(dl{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })

/-- A premise standing alone: `dl{ p }`. -/
def delabPremise : Delab := do
  unless ← ppOn do failure
  fullApp
  let some p ← ppPremise? (← getExpr) | failure
  `(dl{ $p:dl_premise })

attribute [delab app.Solidity.Premise.update, delab app.Solidity.Premise.unfold,
  delab app.Solidity.Premise.split, delab app.Solidity.Premise.done] delabPremise

/-- The type without its `autoParam` hypotheses (a taclet's side conditions),
which nothing after them depends on. -/
partial def dropSide : Lean.Expr → Lean.Expr
  | .forallE n t b bi =>
    let b' := dropSide b
    if t.isAppOfArity ``autoParam 2 && !b'.hasLooseBVar 0 then b'.lowerLooseBVars 1 1
    else .forallE n t b' bi
  | e => e

/-- A taclet's side conditions stay out of sight: `#check @Taclet.x` prints
its schema variables and its line, as `sideConds` read them off the line.
`set_option pp.sol.dl false` shows them. -/
@[delab forallE]
def delabTacletSide : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  unless e.getForallBody.isAppOf ``Taclet do failure
  let e' := dropSide e
  if e' == e then failure
  withTheReader SubExpr (fun s => { s with expr := e' }) delab

end Print

end Solidity
