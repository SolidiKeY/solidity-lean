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

open Solidity (IntOp Modality)

section Prelude

variable {C : Contract} {Γ : Ctx}

/-! ## The term symbols the rule lines write

The term symbols by their KeY sort and name (`Term.find`, `STerm.save`, …),
over the typed signature (`Signature.lean`), at a context: the names the
rule lines write, turned into these under `Tms` (`RuleSyntax.coreNames`).
A symbol takes the proofs its typed constructor carries: a root's, a
member's (`hgsp`, `hfld`: the name's own, as the program's `Loc` takes
them), an index's `IndexTy`/`ArrTy` (`it`, `ak`, `mk`), an operator's
(`Val.binop`'s `hop`/`hq`, `⊕=`'s `hop`/`hp`); a proof the line does not
name (that a type is free of mappings, a literal in range) is found by
`tm_side`. -/

/-- An element of an array free of mappings is free of them. -/
theorem ArrTy.mapFree_elem {R : RefTy} {E : Ty} (a : ArrTy R E) (h : (Ty.ref R).mapFree = true) :
    E.mapFree = true := by
  cases a <;> exact h

/-- The proofs a term symbol takes that a rule line does not name: a
literal in range, a type free of mappings (a fresh array's, a member's or an
element's of a memory object, a memory local's).  A hypothesis is taken
whole last: taken first, it could fix a schema variable's type (an array's
element type to the array's). -/
syntax "tm_side" : tactic
macro_rules
  | `(tactic| tm_side) => `(tactic| first
      | rfl
      | exact RefTy.mapFree_of_newArrOk ‹_›
      | (apply Ty.mapFree_field <;> assumption)
      | (apply ArrTy.mapFree_elem <;> assumption)
      | assumption
      | fail "a term symbol's side proof: none in scope")

namespace Tms

/-- A native `addmod`/`mulmod`, retaining its three typed operands. -/
@[reducible] def Term.modular (op : ModOp) (a b k : Tm C Γ (.val .uint)) :
    Tm C Γ (.val .uint) := .app3 (.modular op) a b k

@[reducible] def Term.lit {p : PrimTy} (v : p.Denote) : Tm C Γ (.val p) := .app0 (.lit v)
@[reducible] def Term.litB (b : Bool) : Tm C Γ (.val .bool) := .app0 (.lit (p := .bool) b)
/-- A numeral, a `uint`. -/
@[reducible] def Term.nat (n : Nat) (h : PrimTy.uint.inRange n = true := by tm_side) :
    Tm C Γ (.val .uint) :=
  .app0 (.lit (p := .uint) ⟨n, h⟩)
/-- `defVal(T)`. -/
@[reducible] def Term.dflt (p : PrimTy) : Tm C Γ (.val p) := .app0 (.lit (PrimTy.dflt p))
/-- `1` at a numeric type, the step of `++`/`--`. -/
@[reducible] def Term.one (p : PrimTy) (hp : p.isNumeric = true) : Tm C Γ (.val p) := Tm.one p hp
@[reducible] def Term.pv {p : PrimTy} (i : Idx Γ (.val p)) : Tm C Γ (.val p) := .pvV i
/-- `a ⊕ b` at a fixed operator and type. -/
@[reducible] def Term.binop (op : BinOp) (p : PrimTy) (a b : Tm C Γ (.val p))
    (h : op.accepts p = true := by tm_side) : Tm C Γ (.val (op.ret p)) :=
  .app2 (.binop op h) a b
/-- `a ⊕ b` of an operator schema variable, as `Val.binop op hop hq` lowers. -/
@[reducible] def Term.binopS {p q : PrimTy} (op : BinOp) (hop : op.accepts p = true)
    (hq : op.ret p = q) (a b : Tm C Γ (.val p)) : Tm C Γ (.val q) :=
  Tm.castV hq (.app2 (.binop op hop) a b)
/-- `l ⊕ se` in `l ⊕= se`, as `OpLoc.op` builds it. -/
@[reducible] def Term.binopC {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (a b : Tm C Γ (.val p)) : Tm C Γ (.val p) :=
  Tm.castV (BinOp.compound_ret hop p) (.app2 (.binop op (BinOp.compound_accepts hop hp)) a b)
/-- `t ± 1`, an increment's or a decrement's arithmetic. -/
@[reducible] def Term.binopI {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    (a b : Tm C Γ (.val p)) : Tm C Γ (.val p) :=
  Term.binopC op.binOp (IncDec.binOp_compound op) hp a b
/-- `⊖a` of an operator schema variable, as `Val.unop op hop hq` lowers. -/
@[reducible] def Term.unopS {p q : PrimTy} (op : UnOp) (hop : op.accepts p = true)
    (hq : op.ret p = q) (a : Tm C Γ (.val p)) : Tm C Γ (.val q) :=
  Tm.castV hq (.app1 (.unop op hop) a)
@[reducible] def Term.find {p : PrimTy} (s : Tm C Γ .st) (q : Tm C Γ (.path (.prim p))) :
    Tm C Γ (.val p) := .app2 .find s q
@[reducible] def Term.len {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    Tm C Γ (.val .uint) := .app2 .len s q
/-- `sp.length` read into a local of type `p`, as `Val.len … hlen` lowers. -/
@[reducible] def Term.lenH {p : PrimTy} {E : Ty} (hp : p = .uint) (s : Tm C Γ .st)
    (q : Tm C Γ (.path (.ref (.array E)))) : Tm C Γ (.val p) :=
  Tm.castV hp.symm (.app2 .len s q)
/-- `mv.length` read into a local of type `p`, as `Val.mlen … hlen` lowers. -/
@[reducible] def Term.mlenH {p : PrimTy} {E : Ty} (hp : p = .uint) (m : Tm C Γ .mem)
    (i : Tm C Γ (.ident (.array E))) : Tm C Γ (.val p) :=
  Tm.castV hp.symm (.app2 .mlen m i)
@[reducible] def Term.read {p : PrimTy} (m : Tm C Γ .mem) (a : Tm C Γ (.addr (.prim p))) :
    Tm C Γ (.val p) := .app2 .read m a
@[reducible] def Term.mlen {E : Ty} (m : Tm C Γ .mem) (i : Tm C Γ (.ident (.array E))) :
    Tm C Γ (.val .uint) := .app2 .mlen m i
/-- `hash(m, i)` read into a local of type `p`, as `Val.hash k … hk` lowers. -/
@[reducible] def Term.hashH {p : PrimTy} {R : RefTy} (k : HashKind) (hp : p = .uint)
    (m : Tm C Γ .mem) (i : Tm C Γ (.ident R)) : Tm C Γ (.val p) :=
  Tm.castV hp.symm (.app2 (.hash k) m i)
/-- `hash(m, i)`: the hash `k` of the object `i` in `m` (`keccak256`,
`sha256`, …). -/
@[reducible] def Term.hash {R : RefTy} (k : HashKind) (m : Tm C Γ .mem) (i : Tm C Γ (.ident R)) :
    Tm C Γ (.val .uint) := .app2 (.hash k) m i
@[reducible] def Term.env (k : EnvKey) : Tm C Γ (.val .uint) := .app0 (.env k)
@[reducible] def Term.net (a : Tm C Γ (.val .uint)) : Tm C Γ .kint := .app1 .net a
@[reducible] def Term.delValue {p : PrimTy} (t : Tm C Γ (.val p)) : Tm C Γ (.val p) :=
  .app1 .delValue t
@[reducible] def Term.bumped (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true)
    (t : Tm C Γ (.val p)) : Tm C Γ (.val p) :=
  Tm.bumped op hp t

@[reducible] def PTerm.root (r : Name) {T : Ty} (h : C.rootType r = some T) : Tm C Γ (.path T) :=
  .app0 (.root r h)
@[reducible] def PTerm.pv {R : RefTy} (i : Idx Γ (.alias R)) : Tm C Γ (.path (.ref R)) := .pvP i
@[reducible] def PTerm.field {s : Name} {T : Ty} (q : Tm C Γ (.path (.ref (.struct s)))) (f : Name)
    (h : C.fieldType s f = some T) : Tm C Γ (.path T) := .app1 (.field h) q
@[reducible] def PTerm.at {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    (q : Tm C Γ (.path (.ref R))) (i : Tm C Γ (.val k)) : Tm C Γ (.path V) :=
  .app2 (.at it) q i
@[reducible] def PTerm.next {E : Ty} (q : Tm C Γ (.path (.ref (.array E)))) : Tm C Γ (.path E) :=
  .app1 .next q

@[reducible] def STerm.storage : Tm C Γ .st := .app0 .storage
@[reducible] def STerm.save {T : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path T)) (v : Tm C Γ (.sv T)) :
    Tm C Γ .st := .app3 .save s q v
@[reducible] def STerm.delAt {T : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path T)) : Tm C Γ .st :=
  .app2 .delAt s q
@[reducible] def STerm.push {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E))))
    (v : Tm C Γ (.sv E)) : Tm C Γ .st := .app3 .push s q v
@[reducible] def STerm.pushSlot (s : Tm C Γ .st) {E : Ty} (q : Tm C Γ (.path (.ref (.array E))))
    (E' : Ty) (_h : E' = E := by rfl) : Tm C Γ .st := .app2 .pushSlot s q
@[reducible] def STerm.pop {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    Tm C Γ .st := .app2 .pop s q
@[reducible] def STerm.shrink {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    Tm C Γ .st := .app2 .shrink s q
@[reducible] def STerm.extend (s : Tm C Γ .st) {E : Ty} (q : Tm C Γ (.path (.ref (.array E))))
    (E' : Ty) (_h : E' = E := by rfl) : Tm C Γ .st := .app2 .extend s q
@[reducible] def STerm.select {sn : Name} (s : Tm C Γ .st) (r : Name)
    (h : C.rootType r = some (.ref (.struct sn))) : Tm C Γ (.sts sn) := .app1 (.select r h) s

@[reducible] def SValT.val {p : PrimTy} (t : Tm C Γ (.val p)) : Tm C Γ (.sv (.prim p)) :=
  .app1 .sval t
@[reducible] def SValT.find {T : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path T)) : Tm C Γ (.sv T) :=
  .app2 .sfind s q
@[reducible] def SValT.copyMem {R : RefTy} (m : Tm C Γ .mem) (i : Tm C Γ (.ident R)) :
    Tm C Γ (.sv (.ref R)) := .app2 .copyMem m i
@[reducible] def SValT.newArr (R : RefTy) (n : Tm C Γ (.val .uint))
    (h : R.newArrOk = true := by tm_side) : Tm C Γ (.sv (.ref R)) := .app1 (.newArr h) n
/-- A fixed array viewed at the destination type `R` it is copied to, the
witness found from the types (`FixedCopy.ofTarget`): `tm{ fixedCopy(R, v) }`. -/
@[reducible] def SValT.fixedCopyTo {E : Ty} {n : Nat} (R : RefTy) (v : Tm C Γ (.sv (.ref (.fixed E n))))
    (h : (FixedCopy.ofTarget E n R).isSome = true := by decide) : Tm C Γ (.sv (.ref R)) :=
  .app1 (.fixedCopy ((FixedCopy.ofTarget E n R).get h)) v

@[reducible] def ITerm.pv {R : RefTy} (i : Idx Γ (.mem R)) : Tm C Γ (.ident R) := .pvI i
@[reducible] def ITerm.read {R : RefTy} (m : Tm C Γ .mem) (a : Tm C Γ (.addr (.ref R))) :
    Tm C Γ (.ident R) := .app2 .iread m a
@[reducible] def ITerm.alloc (m : Tm C Γ .mem) (R : RefTy)
    (h : (Ty.ref R).mapFree = true := by tm_side) : Tm C Γ (.ident R) := .app1 (.alloc R h) m
@[reducible] def ITerm.copy {R : RefTy} (m : Tm C Γ .mem) (v : Tm C Γ (.sv (.ref R)))
    (h : (Ty.ref R).mapFree = true := by tm_side) : Tm C Γ (.ident R) := .app2 (.copy h) m v

@[reducible] def MAddr.field {s : Name} {T : Ty} (i : Tm C Γ (.ident (.struct s))) (f : Name)
    (h : C.fieldType s f = some T) : Tm C Γ (.addr T) := .app1 (.mfield h) i
@[reducible] def MAddr.at {R : RefTy} {E : Ty} (a : ArrTy R E) (i : Tm C Γ (.ident R))
    (k : Tm C Γ (.val .uint)) : Tm C Γ (.addr E) := .app2 (.mat a) i k

@[reducible] def MTerm.memory : Tm C Γ .mem := .app0 .memory
@[reducible] def MTerm.write {T : Ty} (m : Tm C Γ .mem) (a : Tm C Γ (.addr T)) (v : Tm C Γ (.mv T)) :
    Tm C Γ .mem := .app3 .write m a v
@[reducible] def MTerm.addM (m : Tm C Γ .mem) (R : RefTy)
    (h : (Ty.ref R).mapFree = true := by tm_side) : Tm C Γ .mem := .app1 (.addM R h) m
@[reducible] def MTerm.copySt {T : Ty} (m : Tm C Γ .mem) (v : Tm C Γ (.sv T))
    (h : T.mapFree = true := by tm_side) : Tm C Γ .mem := .app2 (.copySt h) m v

@[reducible] def MValT.val {p : PrimTy} (t : Tm C Γ (.val p)) : Tm C Γ (.mv (.prim p)) :=
  .app1 .mval t
@[reducible] def MValT.ref {R : RefTy} (i : Tm C Γ (.ident R)) : Tm C Γ (.mv (.ref R)) :=
  .app1 .ref i

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
    (fun _ _ => false)

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
    (fun R r body => .inline (args.declsThen (.cons (.declStorage R r none)
      (.cons (.block (body.wk (Thin.atop (.alias R :: ps) Γ)).2.2) .nil)))
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
    (fun R r body => .inline
      (.cons (.declLocal p (fse k) (some v)) (.cons (.call f as' (.storage R r) body) .nil))
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
  | storagePushAddAssign :
      dl{ ⟨[ sp.push() += se; ]⟩ ⇝
        { storage := save(storage, sp.length, sp.length + 1) }
        { storage := save(storage, sp[sp.length - 1], find(storage, sp[sp.length - 1]) + se) } ⟨[ ]⟩ }
  | storagePushSubAssign :
      dl{ ⟨[ sp.push() -= se; ]⟩ ⇝
        { storage := save(storage, sp.length, sp.length + 1) }
        { storage := save(storage, sp[sp.length - 1], find(storage, sp[sp.length - 1]) - se) } ⟨[ ]⟩ }
  | storagePushMulAssign :
      dl{ ⟨[ sp.push() *= se; ]⟩ ⇝
        { storage := save(storage, sp.length, sp.length + 1) }
        { storage := save(storage, sp[sp.length - 1], find(storage, sp[sp.length - 1]) * se) } ⟨[ ]⟩ }
  | storagePushDivAssign :
      dl{ ⟨[ sp.push() /= se; ]⟩ ⇝
        if se != 0 then ({ storage := save(storage, sp.length, sp.length + 1) }
          { storage := save(storage, sp[sp.length - 1], find(storage, sp[sp.length - 1]) / se) } ⟨[ ]⟩) else (⟨[ revert(); ]⟩) }
  | storagePushModAssign :
      dl{ ⟨[ sp.push() %= se; ]⟩ ⇝
        if se != 0 then ({ storage := save(storage, sp.length, sp.length + 1) }
          { storage := save(storage, sp[sp.length - 1], find(storage, sp[sp.length - 1]) % se) } ⟨[ ]⟩) else (⟨[ revert(); ]⟩) }
  | storagePushPreincrement :
      dl{ ⟨[ ++sp.push(); ]⟩ ⇝
        { storage := save(storage, sp.length, sp.length + 1) }
        { storage := save(storage, sp[sp.length - 1], find(storage, sp[sp.length - 1]) + 1) } ⟨[ ]⟩ }
  | storagePushPostincrement :
      dl{ ⟨[ (sp.push())++; ]⟩ ⇝
        { storage := save(storage, sp.length, sp.length + 1) }
        { storage := save(storage, sp[sp.length - 1], find(storage, sp[sp.length - 1]) + 1) } ⟨[ ]⟩ }
  | storagePushPredecrement :
      dl{ ⟨[ −−sp.push(); ]⟩ ⇝
        { storage := save(storage, sp.length, sp.length + 1) }
        { storage := save(storage, sp[sp.length - 1], find(storage, sp[sp.length - 1]) - 1) } ⟨[ ]⟩ }
  | storagePushPostdecrement :
      dl{ ⟨[ (sp.push())−−; ]⟩ ⇝
        { storage := save(storage, sp.length, sp.length + 1) }
        { storage := save(storage, sp[sp.length - 1], find(storage, sp[sp.length - 1]) - 1) } ⟨[ ]⟩ }
  | pushCompoundAssignValueRhsCapture :
      dl{ ⟨[ path.push() ⊕= nse; ]⟩ ⇝
        ⟨[ T se = nse; path.push() ⊕= se; ]⟩ }
  | storagePushValueSave :
      dl{ ⟨[ sp.push(se); ]⟩ ⇝
          { storage := save(save(storage, sp[sp.length], se), sp.length, sp.length + 1) } ⟨[ ]⟩ }
  | storagePushValueCopySource :
      dl{ ⟨[ sp1.push(sp2); ]⟩ ⇝
          { storage := save(save(storage, sp1[sp1.length], find(storage, sp2)), sp1.length,
              sp1.length + 1) } ⟨[ ]⟩ }
  /-- `rows.push(mv)` copies the memory object and advances the length together. -/
  | storagePushMemoryCopySource :
      dl{ ⟨[ sp.push(mv); ]⟩ ⇝
          { storage := save(save(storage, sp[sp.length], copyMem(mtSt, memory, mv)), sp.length,
              sp.length + 1) } ⟨[ ]⟩ }
  | storagePushValue_unfold_rightFstReferenceArgument :
      dl{ ⟨[ sp.push(nsp); ]⟩ ⇝
          ⟨[ T storage source = nsp; sp.push(source); ]⟩ }
  | storagePushValue_unfold_rightFstPrimitiveArgument :
      dl{ ⟨[ sp.push(nsp); ]⟩ ⇝
          ⟨[ T source = nsp; sp.push(source); ]⟩ }
  | storagePushLengthSave :
      dl{ ⟨[ parr.push(); ]⟩ ⇝
          { storage := save(storage, parr.length, parr.length + 1) }
          ⟨[ ]⟩ }
  | storagePushLengthSaveReferenceElement :
      dl{ ⟨[ rarr.push(); ]⟩ ⇝
          { storage := save(storage, rarr.length, rarr.length + 1) }
          ⟨[ ]⟩ }
  | storagePushLengthSaveMappingElement :
      dl{ ⟨[ marr.push(); ]⟩ ⇝ { storage := save(storage, marr.length, marr.length + 1) } ⟨[ ]⟩ }
  | storagePushValue_unfold_rightSndArgument :
      dl{ ⟨[ sp.push(nse); ]⟩ ⇝ ⟨[ T se = nse; sp.push(se); ]⟩ }
  | storagePushValue_unfold_leftFstReceiver :
      dl{ ⟨[ nsp.push(src); ]⟩ ⇝ ⟨[ T storage sp = nsp; sp.push(src); ]⟩ }
  | storagePush_unfold_leftFstReceiver :
      dl{ ⟨[ nsp.push(); ]⟩ ⇝ ⟨[ T storage sp = nsp; sp.push(); ]⟩ }
  | storagePop_unfold_leftFstReceiver :
      dl{ ⟨[ nsp.pop(); ]⟩ ⇝ ⟨[ T storage sp = nsp; sp.pop(); ]⟩ }
  /-- `f().push(e)` captures the storage-returning getter before the operand. -/
  | storagePushValue_unfold_leftCallReceiver :
      dl{ ⟨[ fc.push(e); ]⟩ ⇝ ⟨[ aliasType storage sp = fc; sp.push(e); ]⟩ }
  /-- `f().push()` captures the getter before the default append. -/
  | storagePush_unfold_leftCallReceiver :
      dl{ ⟨[ fc.push(); ]⟩ ⇝ ⟨[ aliasType storage sp = fc; sp.push(); ]⟩ }
  /-- `f().pop()` captures the getter before removing the selected element. -/
  | storagePop_unfold_leftCallReceiver :
      dl{ ⟨[ fc.pop(); ]⟩ ⇝ ⟨[ aliasType storage sp = fc; sp.pop(); ]⟩ }
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
          { storage := save(storage, darr.length, darr.length + 1)
            ‖ lsv := darr[darr.length] }
          ⟨[ ]⟩ }
  | storageLocalPrimitivePushBind :
      dl{ ⟨[ v = sp.push(); ]⟩ ⇝
          { storage := save(storage, sp.length, sp.length + 1)
            ‖ v := defVal(T) } ⟨[ ]⟩ }
  | localValuePush_unfold_leftFstReceiver :
      dl{ ⟨[ v = nsp.push(); ]⟩ ⇝ ⟨[ T storage sp = nsp; v = sp.push(); ]⟩ }
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

  /-- SolKey's `whileUnwind`: take one iteration, then the same loop.
  Automatic mode retains that mode; a written bound decreases by one.
  Both use the same taclet, with proof search bounded independently. -/
  | whileUnwind {cond : Val C Γ .bool} :
      dl{ ⟨[ while (cond) body; ]⟩ ⇝
        ⟨[ if (cond) { body; while (cond) body; }; ]⟩ }

  /-- solkey's `whileInvariantBox`.  The invariant holds now, and from every
  state the body's frame allows (`{anon(body)}`, solkey's `#loopAnon`) where
  it holds and the loop has not broken, the condition's value `b` (solkey's
  `bType b = cond;`) picks the body, which keeps the invariant or breaks
  and goes on to the rest, or the rest of the program; a `bool` local holds
  a `bool`, so the two goals cover every state.  `broke` is the loop's
  `break` flag read `true` (`loopBreak`, solkey's `\getLoopBreak`), none
  where the elaborator lowered no `break`: the condition starts with the
  flag's negation, so a body that sets it ends the loop.  Lean asks `¬broke`
  initially too, which solkey's lowering gives by declaring the flag `false`
  before the loop; the rule is sound for every loop.  A body with no
  frame (`Prog.frame`) has no invariant rule: one that writes memory, as in
  solkey, and, Lean's own refusals (`Stmt.within`), one that pushes, pops,
  rebinds an alias or calls out, which solkey frames as writing storage and
  the ledger. -/
  | whileInvariantBox {cond inv : Val C Γ .bool}
      (hf : Prog.frame body = some (xs, hv) := by side_cond) :
      dl{ [ /// @custom:key invariant inv
          while (cond) body; ] ⇝
        "invariant initially valid": inv = TRUE ∧ ¬broke ;
        "invariant preserved and used": {anon(body)} (inv = TRUE ∧ ¬broke → { b := cond }
          (b = TRUE ⟹ ⟨[ body ]⟩ (¬broke → inv = TRUE) ∧ (broke → ⟨[ ]⟩) ;
            b = FALSE ⟹ ⟨[ ]⟩)) }

  /-- solkey's `whileInvariantDiamond`: `whileInvariantBox` with the variant
  `dec`, its value before the iteration kept in a fresh local (KeY's skolem
  `variant`), and checked after the body only where the condition holds
  again (`{ b := cond } (b = TRUE → …)`): an iteration after which the loop
  ends need not decrease it.  The head's update reads `dec` under the
  diamond, so the variant must return where the invariant holds. -/
  | whileInvariantDiamond {cond inv : Val C Γ .bool} {dec : Val C Γ .uint}
      (hf : Prog.frame body = some (xs, hv) := by side_cond)
      (hq : qs = [] := by side_cond) :
      dl{ ⟨ /// @custom:key invariant inv
          /// @custom:key decreases dec
          while (cond) body; ⟩ ⇝
        "invariant initially valid": inv = TRUE ;
        "invariant preserved and used": {anon(body)} (inv = TRUE → { variant := dec ‖ b := cond }
          (b = TRUE ⟹ ⟨[ body ]⟩ (inv = TRUE ∧ { b := cond } (b = TRUE → 0 <= dec ∧ dec < variant)) ;
            b = FALSE ⟹ ⟨[ ]⟩)) }

/-! ## The rules solkey does not have -/

inductive LeanTaclet (C : Contract) (k : Nat) :
    Modality → {Γ Γ' : Ctx} → Stmt C Γ Γ' → Premise C Γ Γ' → Prop where

  /-- Native wide addition followed by reduction; the frozen upstream has no rule. -/
  | addmodAssignment :
      dl[LeanTaclet C k]{ ⟨[ v = addmod(e₁, e₂, e₃); ]⟩ ⇝
        { v := addmod(e₁, e₂, e₃) } ⟨[ ]⟩ }
  /-- Native wide multiplication followed by reduction. -/
  | mulmodAssignment :
      dl[LeanTaclet C k]{ ⟨[ v = mulmod(e₁, e₂, e₃); ]⟩ ⇝
        { v := mulmod(e₁, e₂, e₃) } ⟨[ ]⟩ }
  /-- A hash of a memory object (`keccak256`, `sha256`, `ripemd160`,
  `ecrecover`), read at once: a symbol of the memory (`docs/semantic-gaps.md`,
  "Hashing and the ABI"); solkey has no hash. -/
  | hashAssignment :
      dl[LeanTaclet C k]{ ⟨[ v = hash(mpath); ]⟩ ⇝
        { v := hash(memory, mpath) } ⟨[ ]⟩ }

  /-- A memory source embedded in a storage write is saved as its snapshot. -/
  | storageMemorySourceSave {Γ : Ctx} {T : Ty} {nlhs : Loc C Γ T} {src : Src C Γ T}
      (hmem : src.isMemory = true) :
      dl[LeanTaclet C k]{ ⟨[ nlhs = src; ]⟩ ⇝
        { storage := save(storage, nlhs, src) } ⟨[ ]⟩ }

  /-- A typed shape-compatible source saved through the ordinary copy update.
  This is the intrinsic adapter for KeY's erased `Struct` source sort. -/
  | storageFixedCopySave {Γ : Ctx} {T : Ty} {nlhs : Loc C Γ T} {src : Src C Γ T}
      (hshape : src.isFixedCopy = true) :
      dl[LeanTaclet C k]{ ⟨[ nlhs = src; ]⟩ ⇝
        { storage := save(storage, nlhs, src) } ⟨[ ]⟩ }

  /-- A shape-compatible snapshot pushed as one reference element. -/
  | pushFixedCopySave {Γ : Ctx} {E : Ty} {sp : SPath C Γ (.array E)} {src : Src C Γ E}
      (hshape : src.isFixedCopy = true) :
      dl[LeanTaclet C k]{ ⟨[ sp.push(src); ]⟩ ⇝
        { storage := save(save(storage, sp[sp.length], src), sp.length,
            sp.length + 1) } ⟨[ ]⟩ }

  /-- `rows.push(b.rows[i])` first captures its complex memory source. -/
  | pushMemorySourceCapture :
      dl[LeanTaclet C k]{ ⟨[ sp.push(nmp); ]⟩ ⇝
        ⟨[ T memory mv = nmp; sp.push(mv); ]⟩ }

  /-- Capture the receiver of `nsp.push() += se` once. Upstream's receiver
  rule matches a bare push statement, not a push used as a compound target. -/
  | pushCompoundUnfoldReceiver :
      dl[LeanTaclet C k]{ ⟨[ nsp.push() ⊕= se; ]⟩ ⇝
        ⟨[ T storage sp = nsp; sp.push() ⊕= se; ]⟩ }
  /-- Capture the receiver of `++nsp.push()` once. Upstream's receiver
  rule matches a bare push statement, not a push used as an increment target. -/
  | pushIncrementUnfoldReceiver :
      dl[LeanTaclet C k]{ ⟨[ (nsp.push())⊕⊕; ]⟩ ⇝
        ⟨[ T storage sp = nsp; (sp.push())⊕⊕; ]⟩ }

  /-- A `try` under the diamond closes to `false`.  solkey has no diamond
  rule: the call may revert in the caller (no code at the address, data that
  does not decode), which no clause catches and no formula rules out. -/
  | tryCallDiamond :
      dl[LeanTaclet C k]{ ⟨ try call returns (rets) body catch Error errorBody
          catch Panic (code) panicBody catch otherBody; ⟩ ⇝ false }

  /-- A `try` whose callee is the contract's own function (`Stmt.tryCall`'s
  `self`, `docs/options.md` O8; solkey has none: its `try` never runs a
  callee).  The receiver the contract itself, the callee's body inlined with
  the returned values as its targets, then the success block; the receiver
  another, the success block for every value of the returned data; each
  `catch` block from the state the call was made in, the `Panic` block
  behind the codes the callee may panic with (`panics(selfBody)`,
  `CodeBinder.guard`).  The `require`s are the case split: a goal whose
  receiver is not the case reverts, as one at address `0` does
  (`trySelfStep`). -/
  | tryCallSelfBox {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} {call : ExtCall C Γ} {rets : Binders ρ}
      {body : Prog C (ρ ++ Γ) Γ₁} {errorBody : Prog C Γ Γ₂} {code : CodeBinder κ}
      {panicBody : Prog C (κ ++ Γ) Γ₃} {otherBody : Prog C Γ Γ₄} {selfArgs : Args C Γ ps}
      {selfBody : Prog C (ρ ++ ps) Γf} :
      LeanTaclet C k .box
        (.tryCall call rets body errorBody code panicBody otherBody selfArgs selfBody true)
        -- its goals: "self call succeeded", "call succeeded", "Error caught",
        -- "Panic caught", "other failure caught"
        (trySelfStep call rets body errorBody code panicBody otherBody selfArgs selfBody)

  /-- A self-call `try` under the diamond closes to `false`, as any `try`. -/
  | tryCallSelfDiamond {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} {call : ExtCall C Γ} {rets : Binders ρ}
      {body : Prog C (ρ ++ Γ) Γ₁} {errorBody : Prog C Γ Γ₂} {code : CodeBinder κ}
      {panicBody : Prog C (κ ++ Γ) Γ₃} {otherBody : Prog C Γ Γ₄} {selfArgs : Args C Γ ps}
      {selfBody : Prog C (ρ ++ ps) Γf} :
      LeanTaclet C k .diamond
        (.tryCall call rets body errorBody code panicBody otherBody selfArgs selfBody true)
        (.done false)

  /-- A payment under the diamond closes to `false`.  solkey books a payment
  under the box only (`transferNoCallbackBox`): whether the world pays is not
  the calculus's (`Evm.compile_correct`, where a refused payment reverts the
  machine alone), so no diamond over a payment is derived. -/
  | transferDiamond :
      dl[LeanTaclet C k]{ ⟨ sadr.transfer(se); ⟩ ⇝ false }

  /-- A run assumed away closes to `true` under either modality: it halts
  as exhaustion does, which both accept (`ignoringOverflow { … }`,
  `docs/options.md` O5).  solkey has no such statement. -/
  | assumeFalse :
      dl[LeanTaclet C k]{ ⟨[ assume(false); ]⟩ ⇝ true }

  /-- A revert with data (`Stmt.revertData`, `docs/semantic-gaps.md`, "Revert
  data") closes as `revert();` does: the box to `true`, the diamond to
  `false`.  Neither modality reads the data; a `catch` does
  (`catchDataBox`).  solkey keeps no revert data. -/
  | revertDataBox {Γ : Ctx} {d : List (RevPart C Γ)} :
      LeanTaclet C k .box (.revertData d) (.done true)
  | revertDataDiamond {Γ : Ctx} {d : List (RevPart C Γ)} :
      LeanTaclet C k .diamond (.revertData d) (.done false)

  /-- A `catch` clause binding the data (`Stmt.catchData`): for a self-call
  whose callee's data are literal, a goal per datum the clause may bind, the
  datum written as a literal in front of the clause; another receiver's
  reason, any bytes, the clause for every fresh `bytes` of any contents
  (`Fml.allocAll`, `catchDataStep`).  solkey binds no data. -/
  | catchDataBox {Γ ρ ps Γf Γ₁ : Ctx} {call : ExtCall C Γ} {rets : Binders ρ}
      {selfArgs : Args C Γ ps} {selfBody : Prog C (ρ ++ ps) Γf} {self : Bool} {kind : CatchKind}
      {x : Var} {body : Prog C (.mem bytesR :: Γ) Γ₁} :
      LeanTaclet C k .box (.catchData call rets selfArgs selfBody self kind x body)
        (catchDataStep .box call selfBody self kind x body)
  /-- A `catch` clause binding the data, under the diamond: `false`, as any
  `try`. -/
  | catchDataDiamond {Γ ρ ps Γf Γ₁ : Ctx} {call : ExtCall C Γ} {rets : Binders ρ}
      {selfArgs : Args C Γ ps} {selfBody : Prog C (ρ ++ ps) Γf} {self : Bool} {kind : CatchKind}
      {x : Var} {body : Prog C (.mem bytesR :: Γ) Γ₁} :
      LeanTaclet C k .diamond (.catchData call rets selfArgs selfBody self kind x body) (.done false)

  /-- A recursive call (`Stmt.callRec`, `docs/kernel-port.md`, "Recursion")
  is the call of its body, the next frame of its unrolling, which the next
  step expands as any call (`internalCallExpand`, `functionBodyExpand`).
  solkey inlines a recursive callee as any other, without end. -/
  | recursiveCallUnfold {Γ Γ' ps rs : Ctx} {f : Name} {d : Nat} {args : Args C Γ ps}
      {ret : CallRet Γ rs Γ'} {body : Unit → Prog C (rs ++ ps) (rs ++ ps)} :
      LeanTaclet C k m (.callRec f d args ret body)
        (.unfold (.cons (.call f args ret (body ())) .nil) .refl)


  /-- A loop unwound to its bound ends there: the rest with the condition
  false assumed, and that it is false (`Premise.check`).  Not
  `assert(!cond)`, which would make running out of unwindings a failure of
  the program; and not a capture of the condition in the program, which the
  loop must evaluate afresh.  The condition is read as the invariant rules
  read it, by an update (`{ b := cond }`, under the diamond: it must
  return).  A written `unwind 0` requests this exit check. -/
  | loopExit {cond : Val C Γ .bool} :
      dl[LeanTaclet C k]{ ⟨[ /// @custom:key unwind 0
          while (cond) body; ]⟩ ⇝
        "loop exited": { b := cond } (b = FALSE) ⟹ ⟨[ ]⟩ ;
        "unwound to the end": { b := cond } (b = FALSE) }



  /-- A loop with an invariant whose body has no frame closes to `false`,
  under either modality: sound, and nothing about it is derived.  solkey
  unwinds it instead (it has no annotation to choose by). -/
  | whileClose {cond : Val C Γ .bool}
      (hf : Prog.frame body = none := by side_cond) :
      dl[LeanTaclet C k]{ ⟨[ /// @custom:key invariant inv
          while (cond) body; ]⟩ ⇝ false }

  /-- A loop with an invariant and no variant closes to `false` under the
  diamond: nothing says it ends.  solkey unwinds it instead.  So does one
  whose invariant has a quantified clause (`LoopQ`), which only the box rule
  reads. -/
  | whileNoVariantDiamond {cond : Val C Γ .bool} {dec : Option (Val C Γ .uint)}
      (hf : (Prog.frame body).isSome = true := by side_cond)
      (hd : (dec.isNone || !qs.isEmpty) = true := by side_cond) :
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
