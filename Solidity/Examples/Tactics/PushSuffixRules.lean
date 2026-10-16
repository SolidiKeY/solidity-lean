import Solidity.Calculus.SolkeyProves
import Solidity.Calculus.CallbackSound
import Solidity.SortCheck.Faithfulness
import Solidity.Tools.Taclet

/-!
# Native push rule correspondence

Each named upstream rule constructs the exact pair or guarded pair used by
the typed dispatcher, at every numeric element type and context. Receiver
captures of arithmetic push targets are explicitly Lean-only extensions.
-/

namespace Solidity.Examples.Tactics.PushSuffixRules

open scoped Solidity.Schema

/-- info: all 13 native push rule lines preserve their typed premises in both printed formats -/
#guard_msgs in
run_meta do
  let names := [``Taclet.storagePushAddAssign, ``Taclet.storagePushSubAssign,
    ``Taclet.storagePushMulAssign, ``Taclet.storagePushDivAssign,
    ``Taclet.storagePushModAssign, ``Taclet.storagePushPreincrement,
    ``Taclet.storagePushPostincrement, ``Taclet.storagePushPredecrement,
    ``Taclet.storagePushPostdecrement, ``Taclet.localValuePush_unfold_leftFstReceiver,
    ``Taclet.storagePushValue_unfold_rightFstPrimitiveArgument,
    ``Taclet.storagePushValue_unfold_rightFstReferenceArgument,
    ``Taclet.storagePushMemoryCopySource]
  for key in [false, true] do
    Lean.withOptions (fun o => o.setBool `pp.sol.key key) do
      for name in names do
        Lean.Meta.forallTelescope (← Lean.getConstInfo name).type fun _ body => do
          let some printed ← Delab.tacletTerm? body | throwError "no rule line: {name}"
          let text := (← Lean.PrettyPrinter.ppCategory `term printed).pretty 100000
          let .ok parsedSyntax := Lean.Parser.runParserCategory (← Lean.getEnv) `term text
            | throwError "printed rule does not parse: {name}\n{text}"
          let parsed ← Lean.Elab.Term.TermElabM.run' do
            let parsed ← Lean.Elab.Term.elabType parsedSyntax
            Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
            pure parsed
          Lean.Meta.forallTelescope parsed fun _ actual => do
            unless ← Lean.Meta.isDefEq body actual do
              throwError "roundtrip changed {name}:\n{body}\n{actual}"
  Lean.logInfo "all 13 native push rule lines preserve their typed premises in both printed formats"

variable {C : Contract} {Γ : Ctx} {k : Nat} {m : Modality} {p : PrimTy}
  (hp : p.isNumeric = true) (sp : SPath C Γ (.array (.prim p)))
  (hsp : sp.isSimple = true) (se : Simple C Γ p)

/-- `sp.push() += se` uses the native upstream rule. -/
example : Taclet C k m (.pushOpAssign .add rfl hp sp (.simple se))
    (.updates (Upd.nil.snoc (UpdElem.pushSlot sp))
      (PushSuffix.saveOp .add rfl hp sp se)) :=
  Taclet.storagePushAddAssign (hp := hp) (hlen := rfl) hsp

/-- `sp.push() -= se` uses the native upstream rule. -/
example : Taclet C k m (.pushOpAssign .sub rfl hp sp (.simple se))
    (.updates (Upd.nil.snoc (UpdElem.pushSlot sp))
      (PushSuffix.saveOp .sub rfl hp sp se)) :=
  Taclet.storagePushSubAssign (hp := hp) (hlen := rfl) hsp

/-- `sp.push() *= se` uses the native upstream rule. -/
example : Taclet C k m (.pushOpAssign .mul rfl hp sp (.simple se))
    (.updates (Upd.nil.snoc (UpdElem.pushSlot sp))
      (PushSuffix.saveOp .mul rfl hp sp se)) :=
  Taclet.storagePushMulAssign (hp := hp) (hlen := rfl) hsp

/-- `sp.push() /= se` uses the native upstream rule. -/
example : Taclet C k m (.pushOpAssign .div rfl hp sp (.simple se))
    (.guardedUpdates (PushSuffix.nonzero hp se) (Upd.nil.snoc (UpdElem.pushSlot sp))
      (PushSuffix.saveOp .div rfl hp sp se)) :=
  Taclet.storagePushDivAssign (hp := hp) (hlen := rfl) hsp

/-- `sp.push() %= se` uses the native upstream rule. -/
example : Taclet C k m (.pushOpAssign .mod rfl hp sp (.simple se))
    (.guardedUpdates (PushSuffix.nonzero hp se) (Upd.nil.snoc (UpdElem.pushSlot sp))
      (PushSuffix.saveOp .mod rfl hp sp se)) :=
  Taclet.storagePushModAssign (hp := hp) (hlen := rfl) hsp

/-- The `preInc` statement form of `sp.push()` uses its native upstream rule. -/
example : Taclet C k m (.pushIncDec .preInc hp sp)
    (.updates (Upd.nil.snoc (UpdElem.pushSlot sp))
      (PushSuffix.saveOp IncDec.preInc.binOp IncDec.preInc.binOp_compound hp sp
        (PushSuffix.oneSimple p hp))) :=
  Taclet.storagePushPreincrement (hp := hp) (hlen := rfl) hsp

/-- The `postInc` statement form of `sp.push()` uses its native upstream rule. -/
example : Taclet C k m (.pushIncDec .postInc hp sp)
    (.updates (Upd.nil.snoc (UpdElem.pushSlot sp))
      (PushSuffix.saveOp IncDec.postInc.binOp IncDec.postInc.binOp_compound hp sp
        (PushSuffix.oneSimple p hp))) :=
  Taclet.storagePushPostincrement (hp := hp) (hlen := rfl) hsp

/-- The `preDec` statement form of `sp.push()` uses its native upstream rule. -/
example : Taclet C k m (.pushIncDec .preDec hp sp)
    (.updates (Upd.nil.snoc (UpdElem.pushSlot sp))
      (PushSuffix.saveOp IncDec.preDec.binOp IncDec.preDec.binOp_compound hp sp
        (PushSuffix.oneSimple p hp))) :=
  Taclet.storagePushPredecrement (hp := hp) (hlen := rfl) hsp

/-- The `postDec` statement form of `sp.push()` uses its native upstream rule. -/
example : Taclet C k m (.pushIncDec .postDec hp sp)
    (.updates (Upd.nil.snoc (UpdElem.pushSlot sp))
      (PushSuffix.saveOp IncDec.postDec.binOp IncDec.postDec.binOp_compound hp sp
        (PushSuffix.oneSimple p hp))) :=
  Taclet.storagePushPostdecrement (hp := hp) (hlen := rfl) hsp

/-- `sp.push() += nse` admits the shared upstream RHS capture. -/
example (b : SPath C Γ (.array (.prim p))) (op : BinOp) (hop : op.hasCompoundAssign = true)
    (nse : Val C Γ p) (hnse : nse.isSimple = false) :
    (Stmt.pushOpAssign op hop hp b nse).keyStep m = true := by
  show (!nse.isSimple || b.isSimple) = true
  rw [hnse]
  rfl

/-- A complex push receiver needs the explicit Lean-only capture extension. -/
example (nsp : SPath C Γ (.array (.prim p))) (hnsp : nsp.isSimple = false) :
    (Stmt.pushIncDec .preInc hp nsp).keyStep m = false := hnsp

/-- `v = nsp.push()` exposes the upstream receiver capture as a native rule. -/
example (v : Idx Γ (.val p)) (nsp : SPath C Γ (.array (.prim p)))
    (hnsp : nsp.isSimple = false) :
    Taclet C k m (.assignLocalPush v nsp)
      (.captureSP (fsp k) nsp (.assignLocalPush v.there (.alias .here))) :=
  Taclet.localValuePush_unfold_leftFstReceiver hnsp

/-- `v = sp.push()` with a simple receiver still updates without capture. -/
example (v : Idx Γ (.val p)) :
    (Stmt.assignLocalPush v sp).step k m = .update (Upd.pushBindPrim v sp) :=
  Taclet.storageLocalPrimitivePushBind.toStep hsp

/-- A complex receiver's named rule is also admitted by the SolKey fragment. -/
example (v : Idx Γ (.val p)) (nsp : SPath C Γ (.array (.prim p))) :
    (Stmt.assignLocalPush v nsp).keyStep m = true := rfl

/-- `sp.push(nsp)` captures a primitive source's value into the upstream `source`. -/
example (nsp : SPath C Γ (.prim p)) (hnsp : nsp.isSimple = false) :
    Taclet C k m (.push sp (some (.val nsp.primitiveRead)) rfl)
      (.capture p (.fresh "source" k) nsp.primitiveRead
        (.push sp.up (some (.val (.simple (.local .here)))) rfl)) :=
  Taclet.storagePushValue_unfold_rightFstPrimitiveArgument hsp hnsp

/-- `sp.push(nsp)` binds a complex reference source before copying it. -/
example {R : RefTy} (b : SPath C Γ (.array (.ref R))) (h : b.isSimple = true)
    (nsp : SPath C Γ (.ref R)) (hnsp : nsp.isSimple = false)
    (hm : (Ty.ref R).mapFree = true) :
    Taclet C k m (.push b (some (.copy nsp hm)) rfl)
      (.captureSP (.fresh "source" k) nsp
        (.push b.up (some (.copy (.alias .here) hm)) rfl)) :=
  Taclet.storagePushValue_unfold_rightFstReferenceArgument h hnsp

/-- `sp.push(mv)` uses the native simultaneous copy/length update. -/
example {R : RefTy} (b : SPath C Γ (.array (.ref R))) (hb : b.isSimple = true)
    (mv : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    Taclet C k m (.push b (some (.copyMem (.var mv hm))) rfl)
      (.upd1 (UpdElem.push b (.copyMem (.var mv hm)))) :=
  Taclet.storagePushMemoryCopySource hb

/-- The native memory variable case is admitted by the SolKey rule set. -/
example {R : RefTy} (b : SPath C Γ (.array (.ref R)))
    (mv : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    (Stmt.push b (some (.copyMem (.var mv hm))) rfl).keyStep m = true := rfl

/-- A complex memory source uses the explicit Lean-only capture. -/
example {R : RefTy} (b : SPath C Γ (.array (.ref R))) (hb : b.isSimple = true)
    (nmp : MPath C Γ (.ref R)) (hnmp : nmp.isSimple = false) :
    LeanTaclet C k m (.push b (some (.copyMem nmp)) rfl)
      (.captureMV (.fresh "mv" k) nmp
        (.push b.up (some (.copyMem (.var .here nmp.mapFree))) rfl)) :=
  LeanTaclet.pushMemorySourceCapture hb hnmp

end Solidity.Examples.Tactics.PushSuffixRules
