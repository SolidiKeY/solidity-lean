import Solidity.Calculus.Step
import Solidity.Calculus.RuleSyntax

/-!
# The taclets on scoped statements

The rule table over the scoped syntax (`docs/intrinsic.md`, W1 "rules";
its lines were copied from the unscoped table, which W4 `calc-del`
deleted).  Under `open scoped Solidity.Schema` a line
`dl{ ⟨[ s; ]⟩ ⇝ p }` writes the scoped taclet
(`RuleSyntax.schemaTacletCore`): the `\find` read in its context `Γ`, a
fresh local a position, the `\find`'s schema variables weakened past the
fresh locals before them (`.there`, `up`), the premise's fresh locals popped
after it (`Premise.unfold P (Ext.push^d .refl)`), a declaration's own local
bound (`Premise.bind`) or declared (`Upd.decl`), a branch of an `if` a
block.  `Calculus/Delab.lean` prints each line back;
`scripts/check-rule-text.sh` checks that every constructor is such a line,
but the two stated by hand (`blockEmpty`, `functionCallArgCapture`).

What a line needs is stated here first: the term symbols the lines write (`Tms`, the scoped `Term.find`,
`STerm.save`, …), the side conditions (`Loc.isTarget`, `Val.notTernary`,
the holes' `isTarget`), and a call's inlining (`Premise.expandCall`, the
premise `callStep` builds).

`Taclet.toStep` (`Calculus/Taclet.lean`) says each constructor is the
rule `Stmt.step` fires, so soundness comes from `Stmt.Sound`.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 IntOp Modality)

section Prelude

variable {C : Contract} {Γ : Ctx}

/-! ## The term symbols the rule lines write

The term symbols by their KeY sort and name (`Term.find`, `STerm.save`, …),
over `Update.lean`'s signature, at a context: the names the rule lines
write, turned into these under `Tms` (`RuleSyntax.coreNames`). -/

namespace Tms

@[reducible] def Term.lit (v : Semantics.Value) : Tm C Γ .val := .app0 (.lit v)
@[reducible] def Term.pv {p : PrimTy} (i : Idx Γ (.val p)) : Tm C Γ .val := .pvV i
@[reducible] def Term.binop (op : BinOp) (p : PrimTy) (a b : Tm C Γ .val) : Tm C Γ .val :=
  .app2 (.binop op p) a b
@[reducible] def Term.unop (op : UnOp) (p : PrimTy) (a : Tm C Γ .val) : Tm C Γ .val :=
  .app1 (.unop op p) rfl a
@[reducible] def Term.find (s : Tm C Γ .st) (p : Tm C Γ .path) : Tm C Γ .val := .app2 .find s p
@[reducible] def Term.len (s : Tm C Γ .st) (p : Tm C Γ .path) : Tm C Γ .val := .app2 .len s p
@[reducible] def Term.read (m : Tm C Γ .mem) (a : Tm C Γ .addr) : Tm C Γ .val := .app2 .read m a
@[reducible] def Term.mlen (m : Tm C Γ .mem) (i : Tm C Γ .ident) : Tm C Γ .val := .app2 .mlen m i
@[reducible] def Term.env (k : EnvKey) : Tm C Γ .val := .app0 (.env k)
@[reducible] def Term.net (a : Tm C Γ .val) : Tm C Γ .val := .app1 .net rfl a
@[reducible] def Term.delValue (t : Tm C Γ .val) : Tm C Γ .val := .app1 .delValue rfl t
@[reducible] def Term.bumped (op : IncDec) (p : PrimTy) (t : Tm C Γ .val) : Tm C Γ .val :=
  Tm.bumped op p t

@[reducible] def PTerm.root (r : Name) : Tm C Γ .path := .app0 (.root r)
@[reducible] def PTerm.pv {R : RefTy} (i : Idx Γ (.alias R)) : Tm C Γ .path := .pvP i
@[reducible] def PTerm.field (p : Tm C Γ .path) (f : Name) : Tm C Γ .path := .app1 (.field f) rfl p
@[reducible] def PTerm.at (p : Tm C Γ .path) (i : Tm C Γ .val) : Tm C Γ .path := .app2 .at p i
@[reducible] def PTerm.next (p : Tm C Γ .path) : Tm C Γ .path := .app1 .next rfl p

@[reducible] def STerm.storage : Tm C Γ .st := .app0 .storage
@[reducible] def STerm.save (s : Tm C Γ .st) (p : Tm C Γ .path) (v : Tm C Γ .sv) : Tm C Γ .st :=
  .app3 .save s p v
@[reducible] def STerm.delAt (s : Tm C Γ .st) (p : Tm C Γ .path) : Tm C Γ .st := .app2 .delAt s p
@[reducible] def STerm.push (s : Tm C Γ .st) (p : Tm C Γ .path) (v : Tm C Γ .sv) : Tm C Γ .st :=
  .app3 .push s p v
@[reducible] def STerm.pushSlot (s : Tm C Γ .st) (p : Tm C Γ .path) (E : Ty) : Tm C Γ .st :=
  .app2 (.pushSlot E) s p
@[reducible] def STerm.pop (s : Tm C Γ .st) (p : Tm C Γ .path) : Tm C Γ .st := .app2 .pop s p
@[reducible] def STerm.shrink (s : Tm C Γ .st) (p : Tm C Γ .path) : Tm C Γ .st := .app2 .shrink s p
@[reducible] def STerm.extend (s : Tm C Γ .st) (p : Tm C Γ .path) (E : Ty) : Tm C Γ .st :=
  .app2 (.extend E) s p
@[reducible] def STerm.select (s : Tm C Γ .st) (r : Name) : Tm C Γ .st := .app1 (.select r) rfl s

@[reducible] def SValT.val (t : Tm C Γ .val) : Tm C Γ .sv := .app1 .sval rfl t
@[reducible] def SValT.find (s : Tm C Γ .st) (p : Tm C Γ .path) : Tm C Γ .sv := .app2 .sfind s p
@[reducible] def SValT.copyMem (m : Tm C Γ .mem) (i : Tm C Γ .ident) : Tm C Γ .sv :=
  .app2 .copyMem m i
@[reducible] def SValT.newArr (R : RefTy) (n : Tm C Γ .val) : Tm C Γ .sv := .app1 (.newArr R) rfl n

@[reducible] def ITerm.pv {R : RefTy} (i : Idx Γ (.mem R)) : Tm C Γ .ident := .pvI i
@[reducible] def ITerm.read (m : Tm C Γ .mem) (a : Tm C Γ .addr) : Tm C Γ .ident := .app2 .iread m a
@[reducible] def ITerm.alloc (m : Tm C Γ .mem) (R : RefTy) : Tm C Γ .ident := .app1 (.alloc R) rfl m
@[reducible] def ITerm.copy (m : Tm C Γ .mem) (v : Tm C Γ .sv) : Tm C Γ .ident := .app2 .copy m v

@[reducible] def MAddr.field (i : Tm C Γ .ident) (f : Name) : Tm C Γ .addr := .app1 (.mfield f) rfl i
@[reducible] def MAddr.at (i : Tm C Γ .ident) (k : Tm C Γ .val) : Tm C Γ .addr := .app2 .mat i k

@[reducible] def MTerm.memory : Tm C Γ .mem := .app0 .memory
@[reducible] def MTerm.write (m : Tm C Γ .mem) (a : Tm C Γ .addr) (v : Tm C Γ .mv) : Tm C Γ .mem :=
  .app3 .write m a v
@[reducible] def MTerm.addM (m : Tm C Γ .mem) (R : RefTy) : Tm C Γ .mem := .app1 (.addM R) rfl m
@[reducible] def MTerm.copySt (m : Tm C Γ .mem) (v : Tm C Γ .sv) : Tm C Γ .mem := .app2 .copySt m v

@[reducible] def MValT.val (t : Tm C Γ .val) : Tm C Γ .mv := .app1 .mval rfl t
@[reducible] def MValT.ref (i : Tm C Γ .ident) : Tm C Γ .mv := .app1 .ref rfl i

end Tms

/-! ## Blocks read under a fresh local -/

/-- A block read with one local more on top: `Prog.wk up`, as `ifElseUnfold`
weakens its branches (`Calculus/Arms.lean`); an `up` to the printer,
which shows the block as written. -/
abbrev Prog.up {t : LTy} {Γ₁ : Ctx} (P : Prog C Γ Γ₁) :
    Prog C (t :: Γ) (P.wk (Solidity.up (t := t))).1 :=
  (P.wk Solidity.up).2.2

/-! ## Side conditions

`Rules.lean`'s, on scoped parts: what `Stmt.step` knows of a statement's
parts when it fires a rule. -/

/-- `total`: a state variable. -/
def Loc.isRoot {T : Ty} : Loc C Γ T → Bool
  | .root .. => true
  | _ => false

/-- A target every part of which is simple (`total`, `sp.fld`, `sp[ie]`). -/
def Loc.isTarget {T : Ty} : Loc C Γ T → Bool
  | .root .. => true
  | .field b _ _ => b.isSimple
  | .index _ b i => b.isSimple && i.isSimple

/-- A memory target every part of which is simple (`mv.fld`, `mv[ie]`). -/
def MLoc.isTarget {T : Ty} : MLoc C Γ T → Bool
  | .field b _ _ => b.isSimple
  | .index _ b i => b.isSimple && i.isSimple

/-- A memory path written as it is (`mv`, `mv.fld`, `mv[ie]`). -/
def MPath.isBindable {T : Ty} : MPath C Γ T → Bool
  | .var .. => true
  | .loc l => l.isTarget

/-- Not a conditional: a conditional written to storage or memory is lowered
to a branch (`ternaryToIf`), never captured. -/
def Val.notTernary {p : PrimTy} : Val C Γ p → Bool
  | .ternary .. => false
  | _ => true

/-- A hole whose statement is ready for its path to be unfolded. -/
def SHole.isTarget {T : Ty} : SHole C Γ T → Bool
  | .copy l _ => l.isTarget
  | _ => true

/-- A memory hole ready for its location to be unfolded. -/
def MHole.isTarget {T : Ty} : MHole C Γ T → Bool
  | .write l => l.isTarget
  | _ => true

/-- A value hole ready for its value to be lowered. -/
def VHole.isTarget {p : PrimTy} : VHole C Γ p → Bool
  | .mem l => l.isTarget
  | _ => true

/-- `side_cond`, the side conditions' `autoParam`: the predicates above
compute (`Taclet.lean`'s `coreSidePreds` names them for the tools). -/
macro_rules
  | `(tactic| side_cond) => `(tactic| first
      | rfl
      | assumption
      | (simp_all [SPath.isSimple, Val.isSimple, MPath.isSimple, Loc.isTarget, Loc.isRoot,
          MLoc.isTarget, MPath.isBindable, Val.notTernary, SHole.isTarget, MHole.isTarget,
          VHole.isTarget, SPath.elemMapping, SPath.elemPrim, Ty.elemIsMapping, Ty.elemIsPrim,
          Ty.isMapping, Ty.isPrimitive]; done)
      | fail "the rule's side condition does not hold: `Stmt.step` fires another rule here")

/-! ## Calls -/

/-- Whether a call returns its values to targets after it (`CallRet.rets`):
KeY's `FunctionBodyStatement` (`fbs`, `functionBodyExpand`), the call of a
tuple assignment or of a specification's obligation; any other call, a
memory return among them (`Person memory p = f();`, decision 19, rule-map
rows 54/55), is an `InternalCall` (`ic`, `internalCallExpand`). -/
def CallRet.isRets {rs Γ' : Ctx} (r : CallRet Γ rs Γ') : Bool :=
  CallRet.casesOn (motive := fun _ _ _ => Bool) r false (fun _ _ _ => false) (fun _ => true)
    (fun _ _ _ _ => false)

/-- The first argument that is not simple, if any (`functionCallArgCapture`
captures it). -/
def Args.firstNonSimple {ps : Ctx} (as : Args C Γ ps) : Option ((p : PrimTy) × Val C Γ p) :=
  (Args.capture as).map fun x => ⟨x.1, x.2.1⟩

/-- `expand_function_body(ic)`: the premise of a call whose arguments are
all simple, as `callStep` builds it (`Calculus/Blocks.lean`): the
parameters declared with the arguments, the return variables declared, the
body read under the caller as a block, the result assigned; the frame popped,
or dropped from under the return variables it leaves. -/
def Premise.expandCall (_k : Nat) {Γ' ps rs Γf : Ctx} (args : Args C Γ ps)
    (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) : Premise C Γ Γ' :=
  CallRet.casesOn (motive := fun rs Γ' _ => Prog C (rs ++ ps) Γf → Premise C Γ Γ') ret
    (fun body => .unfold (args.declsThen
      (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil)) (Ext.append Γ ps))
    (fun p r res body =>
      let result : Prog C (.val p :: (ps ++ Γ)) (.val p :: (ps ++ Γ)) := match res with
        | none => .nil
        | some j => .cons (.assignLocal (j.under ps).there (.simple (.local .here))) .nil
      .unfold (args.declsThen (.cons (.declLocal p r none)
        (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) result)))
        (.push (Ext.append Γ ps)))
    (fun {rs} bs body => .inline (args.declsThen (bs.declsThen
      (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil)))
      (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps))))
    (fun R r hd hm body => .inline (args.declsThen (.cons (.declMem R r none hd hm)
      (.cons (.block (body.wk (Thin.atop (.mem R :: ps) Γ)).2.2) .nil)))
      (.keep (Thin.ofExt (Ext.append Γ ps))))
    body

/-- `functionCallArgCapture`'s premise: the leftmost argument that is not
simple (`v : p`) captured into the fresh `se`, the call made with `as'`, the
arguments read with it on top; as `callStep` builds it. -/
def Premise.argCapture (k : Nat) (f : Name) {Γ' ps rs Γf : Ctx} (p : PrimTy) (v : Val C Γ p)
    (as' : Args C (.val p :: Γ) ps) (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) :
    Premise C Γ Γ' :=
  CallRet.casesOn (motive := fun rs Γ' _ => Prog C (rs ++ ps) Γf → Premise C Γ Γ') ret
    (fun body => .capture p (fse k) v (.call f as' .none body))
    (fun q r res body => .capture p (fse k) v (.call f as' (.val q r (res.map .there)) body))
    (fun {rs} bs body => .inline
      (.cons (.declLocal p (fse k) (some v)) (.cons (.call f as' (.rets bs) body) .nil))
      (Thin.keepAll rs (.drop .refl)))
    (fun R r hd hm body => .inline
      (.cons (.declLocal p (fse k) (some v)) (.cons (.call f as' (.mem R r hd hm) body) .nil))
      (.keep (.drop .refl)))
    body

end Prelude

/-! ## The rule table -/

open scoped Solidity.Schema

inductive Taclet (C : Contract) (k : Nat) :
    Modality → {Γ Γ' : Ctx} → Stmt C Γ Γ' → Premise C Γ Γ' → Prop where
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
  and `pv` true; refused, nothing booked and `pv` false (`TRun.send`,
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
  /-- KeY re-binds the receiver too (`T memory mv' = mv;`).  The receiver
  is already a simple memory local, typed by its position (`MPath.var`), so
  the rebinding only renames `mv`; it is left out to keep the rule text and
  its fresh names (`se`, `ie`) as they were.  A deviation in shape. -/
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
  /-- solkey's `blockEmpty`, scoped only: a block is its statements, its
  locals popped where it ends (`Premise.unfold`'s `Ext`); when they are done,
  the end goes (`Frames.exit`), KeY's `{} ⇝`.  Today's programs had no
  nested block, so today's table had no line for it. -/
  | blockEmpty {Γ Γ₁ : Ctx} {body : Prog C Γ Γ₁} :
      Taclet C k m (.block body) (.unfold body body.ext)

/-! ## The rules solkey does not have -/

inductive LeanTaclet (C : Contract) (k : Nat) :
    Modality → {Γ Γ' : Ctx} → Stmt C Γ Γ' → Premise C Γ Γ' → Prop where

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
  | whileUnwind {cond : Val C Γ .bool} :
      dl[LeanTaclet C k]{ ⟨[ /// @custom:key unwind n + 1
          while (cond) body; ]⟩ ⇝
        ⟨[ if (cond) { body; /// @custom:key unwind n
          while (cond) body; }; ]⟩ }

  /-- A loop unwound to its bound ends there: the rest with the condition
  false assumed, and that it is false (`Premise.check`).  Not
  `assert(!cond)`, which would make running out of unwindings a failure of
  the program; and not a capture of the condition, which the loop must
  evaluate afresh.  A loop with no clause is `unwind 0`. -/
  | loopExit {cond : Val C Γ .bool} :
      dl[LeanTaclet C k]{ ⟨[ /// @custom:key unwind 0
          while (cond) body; ]⟩ ⇝
        "loop exited": defined(cond) ∧ defined(false) ∧ cond ≐ false ⟹ ⟨[ ]⟩ ;
        "unwound to the end": defined(cond) ∧ defined(false) ∧ cond ≐ false }

  /-- solkey's `whileInvariantBox`.  The invariant holds now, and from every
  state the body's frame allows (`{anon(body)}`, solkey's `#loopAnon`) where
  it holds, the condition's value `b` (solkey's `bType b = cond;`) picks the
  body, which keeps the invariant, or the rest of the program; a `bool`
  local holds a `bool`, so the two goals cover every state.  A body with no
  frame (`Prog.frame`) has no invariant rule: one that writes memory, as in
  solkey, and, Lean's own refusals (`Stmt.within`), one that pushes, pops,
  rebinds an alias or calls out, which solkey frames as writing storage and
  the ledger. -/
  | whileInvariantBox {cond inv : Val C Γ .bool}
      (hf : Prog.frame body = some (xs, hv) := by side_cond) :
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
  | whileInvariantDiamond {cond inv : Val C Γ .bool} {dec : Val C Γ .uint}
      (hf : Prog.frame body = some (xs, hv) := by side_cond) :
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
  | whileClose {cond : Val C Γ .bool}
      (hf : Prog.frame body = none := by side_cond) :
      dl[LeanTaclet C k]{ ⟨[ /// @custom:key invariant inv
          while (cond) body; ]⟩ ⇝ false }

  /-- A loop with an invariant and no variant closes to `false` under the
  diamond: nothing says it ends.  solkey unwinds it instead. -/
  | whileNoVariantDiamond {cond : Val C Γ .bool} {dec : Option (Val C Γ .uint)}
      (hf : (Prog.frame body).isSome = true := by side_cond)
      (hd : dec.isNone = true := by side_cond) :
      dl[LeanTaclet C k]{ ⟨ /// @custom:key invariant inv
          while (cond) body; ⟩ ⇝ false }
  /-- An argument that is not simple is captured into a fresh local first,
  the leftmost first (`Args.capture`, the `unfoldArgument` rule): the call is
  closed over its frame, so the capture is the call's own premise. -/
  | functionCallArgCapture {Γ : Ctx} {f : Name} {ps : Ctx} {args : Args C Γ ps} {rs Γ' : Ctx}
      {ret : CallRet Γ rs Γ'} {Γf : Ctx} {body : Prog C (rs ++ ps) Γf} {p : PrimTy} {v : Val C Γ p}
      {as' : Args C (.val p :: Γ) ps} (hcap : Args.capture args = some ⟨p, v, as'⟩ := by side_cond) :
      LeanTaclet C k m (.call f args ret body) (Premise.argCapture k f p v as' ret body)

/-- A rule of the calculus: solkey's, or one it does not have. -/
inductive Rule (C : Contract) (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ')
    (p : Premise C Γ Γ') : Prop where
  | key (d : Taclet C k m s p)
  | lean (d : LeanTaclet C k m s p)

end Solidity
