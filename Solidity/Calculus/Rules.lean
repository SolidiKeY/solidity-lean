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
`\replacewith`, each written in the paper's notation (`RuleSyntax.lean`) and
printed back in it (mini-solkey's `Ch06_Taclets`).  `⟨[ ]⟩` is the paper's
combined modality: the taclet fires under either, and its premise keeps the
one it found.  Only the two rules for `revert();` tell the modalities apart.

The paper organises the storage rules in three steps:

* **Step 1** unfolds a *read* whose receiver or index is not simple: it
  captures the offending part into a fresh local and re-enters;
* **Step 2** decomposes a *write*, capturing source, receiver and index in
  that order;
* **Step 3** turns a statement whose parts are all simple into an *update*.

A taclet says what is *sound*, not what fires: the unfold rules hold of a
simple part too.  Which rule runs is `Stmt.step` (`Completeness.lean`), and
that each statement has exactly one is `rules_disjoint`/`rules_complete`
over the statements' shapes (`RuleShapes.lean`).

A rule over an operator is one constructor for the family (`⊕` is its
schema variable), and `++`/`--` one for all four (`⊕⊕`); solkey writes one
taclet per operator, and `KeyTaclets.lean` maps each instance back.
-/

namespace Solidity

variable {C : Contract}

/-! ## Where a read or a value lands

A read unfolded by Step 1 lands in one of several places, and the rule is the
same for all of them: the paper writes `lhs = nsp.fld`.  A hole is that
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

/-! ## Premises -/

/-- What a taclet leaves: an update in front of the rest (`{U} ⟨[ ]⟩`),
statements in its place (`⟨[ s₁; …; sₙ; ]⟩`), two goals (a branch, the
condition assumed in one and its negation in the other), or the whole
modality closed (`true`, `false`). -/
inductive Premise (C : Contract) where
  | update (U : Upd C)
  | unfold (P : Prog C)
  | split (c : Fml C) (P Q : Prog C)
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
      dl{ ⟨[ nsp.fld = sp2; ]⟩ ⇝ ⟨[ T storage sp = nsp; sp.fld = sp2; ]⟩ }
  | storageIndexWrite_unfold_leftFst :
      dl{ ⟨[ nsp[e₁] = e₂; ]⟩ ⇝ ⟨[ T se = e₂; T storage sp = nsp; T ie = e₁; sp[ie] = se; ]⟩ }
  | storageIndexWriteStorageRef_unfold_leftFst :
      dl{ ⟨[ nsp[e] = sp2; ]⟩ ⇝ ⟨[ T storage sp = nsp; T ie = e; sp[ie] = sp2; ]⟩ }
  | storageIndexWriteNonSimpleIndexCapture :
      dl{ ⟨[ sp[nse₁] = e; ]⟩ ⇝ ⟨[ T se = e; T ie = nse₁; sp[ie] = se; ]⟩ }
  | storageIndexWriteStorageRefNonSimpleIndexCapture :
      dl{ ⟨[ sp[nse] = sp2; ]⟩ ⇝ ⟨[ T ie = nse; sp[ie] = sp2; ]⟩ }
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
      dl{ ⟨[ lsv = arr[ie]; ]⟩ ⇝ { lsv := arr[ie] } ⟨[ ]⟩ }
  | storageRootDelete :
      dl{ ⟨[ delete gsp; ]⟩ ⇝ { storage := delAt(storage, gsp) } ⟨[ ]⟩ }
  | storageFieldDelete :
      dl{ ⟨[ delete sp.fld; ]⟩ ⇝ { storage := delAt(storage, sp.fld) } ⟨[ ]⟩ }
  | storageIndexDelete :
      dl{ ⟨[ delete sp[ie]; ]⟩ ⇝ { storage := delAt(storage, sp[ie]) } ⟨[ ]⟩ }
  -- Operators ------------------------------------------------------------
  | binopAssignment :
      dl{ ⟨[ v = se₁ ⊕ se₂; ]⟩ ⇝ { v := se₁ ⊕ se₂ } ⟨[ ]⟩ }
  | binopUnfoldLeft :
      dl{ ⟨[ v = nse ⊕ e; ]⟩ ⇝ ⟨[ T se = nse; v = se ⊕ e; ]⟩ }
  | binopUnfoldRight :
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
      dl{ ⟨[ x = se ? e₁ : e₂; ]⟩ ⇝ ⟨[ if (se) { x = e₁; } else { x = e₂; }; ]⟩ }
  | ternaryCaptureCond :
      dl{ ⟨[ x = nse ? e₁ : e₂; ]⟩ ⇝ ⟨[ bool se = nse; x = se ? e₁ : e₂; ]⟩ }
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
      dl{ ⟨[ sp.push(sp2); ]⟩ ⇝
          { storage := save(save(storage, sp[sp.length], find(storage, sp2)), sp.length,
              sp.length + 1) } ⟨[ ]⟩ }
  | storagePushLengthSave :
      dl{ ⟨[ sp.push(); ]⟩ ⇝
          { storage := save(delAt(storage, sp[sp.length]), sp.length, sp.length + 1) } ⟨[ ]⟩ }
  | storagePushValue_unfold_rightSndArgument :
      dl{ ⟨[ sp.push(nse); ]⟩ ⇝ ⟨[ T se = nse; sp.push(se); ]⟩ }
  | storagePushValue_unfold_leftFstReceiver :
      dl{ ⟨[ nsp.push(src); ]⟩ ⇝ ⟨[ T storage sp = nsp; sp.push(src); ]⟩ }
  | storagePush_unfold_leftFstReceiver :
      dl{ ⟨[ nsp.push(); ]⟩ ⇝ ⟨[ T storage sp = nsp; sp.push(); ]⟩ }
  | storagePop_unfold_leftFstReceiver :
      dl{ ⟨[ nsp.pop(); ]⟩ ⇝ ⟨[ T storage sp = nsp; sp.pop(); ]⟩ }
  | storagePopSave :
      dl{ ⟨[ sp.pop(); ]⟩ ⇝
          { storage := save(delAt(storage, sp[sp.length - 1]), sp.length, sp.length - 1) } ⟨[ ]⟩ }
  | storageLocalRootPush_unfold_leftFstReceiver :
      dl{ ⟨[ lsv = nsp.push(); ]⟩ ⇝ ⟨[ T storage sp = nsp; lsv = sp.push(); ]⟩ }
  | storageLocalRootPushBind :
      dl{ ⟨[ lsv = sp.push(); ]⟩ ⇝
          { storage := save(storage, sp.length, sp.length + 1) ‖ lsv := sp[sp.length] } ⟨[ ]⟩ }
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
  | memoryIndexWrite_unfold_leftFst :
      dl{ ⟨[ nmp[e] = msrc; ]⟩ ⇝ ⟨[ T memory mv = nmp; T ie = e; mv[ie] = msrc; ]⟩ }
  | memoryIndexWriteNonSimpleIndexCapture :
      dl{ ⟨[ mv[nse] = msrc; ]⟩ ⇝ ⟨[ T ie = nse; mv[ie] = msrc; ]⟩ }
  | memoryFieldWriteUnfoldSource :
      dl{ ⟨[ mv.fld = nse; ]⟩ ⇝ ⟨[ T se = nse; mv.fld = se; ]⟩ }
  | memoryIndexWriteUnfoldSource :
      dl{ ⟨[ mv[ie] = nse; ]⟩ ⇝ ⟨[ T se = nse; mv[ie] = se; ]⟩ }
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
  | memoryToStorageIndex_unfold_leftFst :
      dl{ ⟨[ nsp[e] = mpath; ]⟩ ⇝ ⟨[ T storage sp = nsp; sp[e] = mpath; ]⟩ }
  | memoryToStorageIndexNonSimpleIndexCapture :
      dl{ ⟨[ sp[nse] = mpath; ]⟩ ⇝ ⟨[ T ie = nse; sp[ie] = mpath; ]⟩ }
  -- Control flow ---------------------------------------------------------
  | ifElseUnfold :
      dl{ ⟨[ if (nse) thn else els; ]⟩ ⇝ ⟨[ bool se = nse; if (se) thn else els; ]⟩ }
  /-- Two goals: the `then` branch where `se` holds, the `else` branch where it
  does not (solkey's `\add(se = TRUE ==>)`). -/
  | ifElseSplit :
      dl{ ⟨[ if (se) thn else els; ]⟩ ⇝ se = true ⟹ ⟨[ thn ]⟩ ; ¬se = true ⟹ ⟨[ els ]⟩ }
  | requireConditionCapture :
      dl{ ⟨[ require(nse); ]⟩ ⇝ ⟨[ bool se = nse; require(se); ]⟩ }
  /-- A guard: if `se` holds the program goes on, if not it reverts. -/
  | requireSimple :
      dl{ ⟨[ require(se); ]⟩ ⇝ se = true ⟹ ⟨[ ]⟩ ; ¬se = true ⟹ ⟨[ revert(); ]⟩ }
  | assertConditionCapture :
      dl{ ⟨[ assert(nse); ]⟩ ⇝ ⟨[ bool se = nse; assert(se); ]⟩ }
  | assertSimple :
      dl{ ⟨[ assert(se); ]⟩ ⇝ se = true ⟹ ⟨[ ]⟩ ; ¬se = true ⟹ ⟨[ revert(); ]⟩ }
  /-- A reverted run satisfies every box formula: the box closes to `true`. -/
  | revertBox :
      dl{ [ revert(); ] ⇝ true }
  /-- A reverted run satisfies no diamond formula: the diamond closes to `false`. -/
  | revertDiamond :
      dl{ ⟨ revert(); ⟩ ⇝ false }

end Solidity
