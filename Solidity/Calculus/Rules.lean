import Solidity.Calculus.RuleKit
import Solidity.Calculus.RuleSyntax
import Solidity.Calculus.KeyTaclets
import Solidity.Semantics.Mutability

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
  -- Lean only: KeY binds nothing; `unset` makes a read through `lsv` revert
  | storageLocalDeclSkip :
      dl{ ⟨[ T storage lsv; ]⟩ ⇝ { lsv := unset } ⟨[ ]⟩ }
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
  of a negative amount reverts, as a `transfer` of one does. -/
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

  /-- solkey's `whileInvariantBox`.  The invariant holds now, and from every
  state the body's frame allows (`{anon(body)}`, solkey's `#loopAnon`) where
  it holds, the condition's value `b` (solkey's `bType b = cond;`) picks the
  body, which keeps the invariant, or the rest of the program.  A `b`
  neither `TRUE` nor `FALSE` (Lean's locals are untyped) is ruled out under
  the diamond, as a branch's cover is.  A body with no frame
  (`Prog.loopFrame`) has no invariant rule: one that writes memory, as in
  solkey, and, Lean's own refusals (`Stmt.within`), one that pushes, pops,
  rebinds an alias or calls out, which solkey frames as writing storage and
  the ledger. -/
  | whileInvariantBox {cond inv : Val C .bool}
      (hf : (Prog.loopFrame body).isSome = true := by side_cond) :
      dl[LeanTaclet C k]{ [ /// @custom:key invariant inv
          while (cond) body; ] ⇝
        "invariant initially valid": inv = TRUE ;
        "invariant preserved and used": {anon(body)} (inv = TRUE → { b := cond }
          (b = TRUE ⟹ ⟨[ body ]⟩ inv = TRUE ; b = FALSE ⟹ ⟨[ ]⟩)) }

  /-- solkey's `whileInvariantDiamond`: `whileInvariantBox` with the variant
  `dec`, its value before the iteration kept in a fresh local (KeY's skolem
  `variant`), and checked after the body only where the condition holds
  again (`{ b := cond } (b = TRUE → …)`): an iteration after which the loop
  ends need not decrease it.  Lean reads `dec` where solkey compares it
  (`dec = variant`), so the variant must be defined where the invariant
  holds. -/
  | whileInvariantDiamond {cond inv : Val C .bool} {dec : Val C .uint}
      (hf : (Prog.loopFrame body).isSome = true := by side_cond) :
      dl[LeanTaclet C k]{ ⟨ /// @custom:key invariant inv
          /// @custom:key decreases dec
          while (cond) body; ⟩ ⇝
        "invariant initially valid": inv = TRUE ;
        "invariant preserved and used": {anon(body)} (inv = TRUE → { variant := dec ‖ b := cond }
          (b = TRUE ⟹ ⟨[ body ]⟩ (inv = TRUE ∧ { b := cond } (b = TRUE → 0 <= dec ∧ dec < variant)) ;
            b = FALSE ⟹ ⟨[ ]⟩)) }

  /-- A loop with an invariant whose body has no frame closes to `false`,
  under either modality: sound, and nothing about it is derived.  solkey
  unwinds it instead (it has no annotation to choose by). -/
  | whileClose {cond : Val C .bool}
      (hf : (Prog.loopFrame body).isSome = false := by side_cond) :
      dl[LeanTaclet C k]{ ⟨[ /// @custom:key invariant inv
          while (cond) body; ]⟩ ⇝ false }

  /-- A loop with an invariant and no variant closes to `false` under the
  diamond: nothing says it ends.  solkey unwinds it instead. -/
  | whileNoVariantDiamond {cond : Val C .bool} {dec : Option (Val C .uint)}
      (hf : (Prog.loopFrame body).isSome = true := by side_cond)
      (hd : dec.isNone = true := by side_cond) :
      dl[LeanTaclet C k]{ ⟨ /// @custom:key invariant inv
          while (cond) body; ⟩ ⇝ false }

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

/-! ## Printing taclets and premises

`#check @Taclet.storageFieldWriteSave` prints the taclet as it is written
above: the `\find` with the modality it is for, and the premise. -/

section Print
open Lean Meta PrettyPrinter Delaborator SubExpr
set_option hygiene false

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
  -- a loop's goals are labelled by the rule its annotation picks
  let inv := (← whnf (e.getArg! (n + 2))).isAppOf ``Premise.inv
  let rule? : Option String := if inv then some "whileInvariantBox" else do
    Taclet.labelledBy (← st.getAppFn.constName?) (m.isConstOf ``Modality.diamond)
  let labels := (do (← Taclet.branchLabels.lookup (← rule?)))
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
