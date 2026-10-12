import Solidity.Signature
import Solidity.Theory.Bridge.Copy
import Solidity.Theory.Bridge.Push
import Solidity.Theory.Bridge.Delete
import Solidity.Theory.Bridge.Find

/-!
# What a typed symbol denotes in the Theory, and the bridge

A formula's equation reads its terms in the Theory algebra (`Theory.StValue`,
KeY's total model: a read off the end of what is there is a node, not a
halt), so solkey's laws need no "the write lands" premise (the W9.8.0
decision, `docs/intrinsic.md`).  `Op0.denote` … `Op3.denote` read the typed
symbols of `Signature.lean` there, over the typed global part's storage
abstracted (`Storage.absT`); `Tm.denote` (`Calculus/Lands.lean`) is one
recursion over them.

**The bridge** (`Op0.denote_eval` … `Op3.denote_eval`): where the typed
evaluation returns (`OpN.eval`, `some`), the denotation is its value
abstracted, literally for a value and a path, up to `Equiv` for a storage
and a stored value (`Srt.Bridge`).  Each case is the storage operation's
erasure (`Semantics/StorageErase.lean`) composed with its Theory bridge
(`Theory/Bridge/Find`, `Save`, `Copy`, `Delete`, `Push`), on the storage
read as an untyped state (`Storage.sem`).

**Where it does not follow the Theory.**
- Arithmetic is the interpreter's checked arithmetic (`evalBinop`,
  `unopCheck`), and a halt reads `st mtSt` (`Res.toSt`).
- The memory island is not abstracted: `read`, `mlen` and `copyMem` denote
  the typed evaluation's value, and the memory sorts denote nothing.
- A path is not bounds-checked (`at`): that is KeY's guard, a premise of the
  laws.  `next` reads the length in the global storage, `nextIn` in its
  storage term.

This is the only Theory module that imports the signature (design R10).
-/

namespace Solidity

open Semantics (Value Seg Res lookupBy defaultForTy)
open Solidity (evalBinop unopCheck newArrVal)
open Theory Theory.StValue

variable {C : Contract}

/-! ## The Theory's sorts -/

/-- What a term of each sort denotes in the Theory: a value or a stored
value a Theory value, a path its segments, a storage a struct node; the
memory sorts denote nothing of their own. -/
@[reducible] def Srt.TDen : Srt → Type
  | .val _ => StValue
  | .path _ => List Seg
  | .st => Struct
  | .sv _ => StValue
  | .sts _ => Struct
  | .spath _ _ => List Seg
  | .ident _ | .addr _ | .mem | .mv _ => Unit

/-- A typed storage as an untyped state, for the Theory's bridge lemmas. -/
def Storage.sem (st : Storage C) : Semantics.State := { storage := st.erase }

theorem Storage.abs_sem (st : Storage C) : st.sem.abs = st.absT := rfl

/-- A typed storage reference as a Theory path. -/
def SRef.absT {U : Ty} (r : SRef C U) : List Seg := rootPath r.root r.path.erase

/-- A typed word's result as a Theory value: a halt reads as nothing. -/
def PrimTy.toSt {p : PrimTy} : Option p.Denote → StValue
  | some v => .prim (PrimTy.erase v)
  | none => .st .mtSt

/-! ## The symbols in the Theory -/

/-- A constant in the Theory. -/
def Op0.denote (g : State C []) {s : Srt} : Op0 C s → s.TDen
  | .lit v => .prim (PrimTy.erase v)
  | .env k => .prim (PrimTy.erase (g.envVal k))
  | .root r _ => rootPath r []
  | .storage => g.storage.absT
  | .memory => ()
  | .mtSt => (Storage.init C).absT
  | .member _ f _ => rootPath f []

/-- A unary symbol in the Theory, its argument's denotation given. -/
def Op1.denote (g : State C []) {a s : Srt} : Op1 C a s → a.TDen → s.TDen
  | @Op1.unop _ op p _, da => Res.toSt (do unopCheck op p (← Semantics.applyUnOp op (← da.toRes)))
  | .net, da => match da with
    | .prim (.int n) => .prim (.int ((lookupBy n g.net).getD 0))
    | _ => .st .mtSt
  | .delValue, da => StValue.delValue da
  | @Op1.field _ _ f _ _, dp => dp ++ [.field f]
  | .next, dp => dp ++ [.at (lenAt g.storage.absT dp)]
  | .sval, dt => dt
  | @Op1.newArr _ R _, dn => (newArrVal R (asInt dn)).abs
  | .alloc _ _, _ => ()
  | .mfield _, _ => ()
  | .addM _ _, _ => ()
  | .mval, _ => ()
  | .ref, _ => ()
  | .wt, _ => .prim (.bool true)
  | .select r _, ds => asStruct (selectSt ds (.field r))
  | @Op1.selectIn _ _ _ f _, ds => asStruct (selectSt ds (.field f))
  | @Op1.fieldIn _ _ _ f _ _, dp => dp ++ [.field f]

/-- A binary symbol in the Theory, its arguments' typed readings and
denotations given. -/
def Op2.denote (g : State C []) {a b s : Srt} :
    Op2 C a b s → Option (a.Den C g.H) → Option (b.Den C g.H) → a.TDen → b.TDen → s.TDen
  | @Op2.binop _ op p _, _, _, da, db => Res.toSt (do evalBinop op p (← da.toRes) db.toRes)
  | .find, _, _, ds, dp => findSt ds dp
  | .len, _, _, ds, dp => findSt ds (dp ++ [lengthSeg])
  | .read, x, y, _, _ => PrimTy.toSt (Op2.eval g .read x y)
  | .mlen, x, y, _, _ => PrimTy.toSt (Op2.eval g .mlen x y)
  | .at _, _, _, dp, di => dp ++ [.at (asInt di)]
  | .nextIn, _, _, ds, dp => dp ++ [.at (lenAt ds dp)]
  | .delAt, _, _, ds, dp => StValue.delAt ds dp
  | @Op2.pushSlot _ E, _, _, ds, dp => pushSlotT E.isPrimitive (defaultForTy E).abs ds dp
  | .pop, _, _, ds, dp => popT ds dp
  | .shrink, _, _, ds, dp => shrinkT ds dp
  | @Op2.extend _ E, _, _, ds, dp => pushSlotT E.isPrimitive (defaultForTy E).abs ds dp
  | .sfind, _, _, ds, dp => findSt ds dp
  | .copyMem, x, y, _, _ => match Op2.eval g .copyMem x y with
    | some w => w.absT
    | none => .st .mtSt
  | .iread, _, _, _, _ => ()
  | .copy _, _, _, _, _ => ()
  | .mat _, _, _, _, _ => ()
  | .copySt _, _, _, _, _ => ()
  | .findIn, _, _, ds, dp => findSt ds dp
  | .delAtIn, _, _, ds, dp => StValue.delAt ds dp
  | .sfindIn, _, _, ds, dp => findSt ds dp

/-- A ternary symbol in the Theory, its arguments' denotations given. -/
def Op3.denote {a b c s : Srt} : Op3 C a b c s → a.TDen → b.TDen → c.TDen → s.TDen
  | .ite, dc, da, db => match dc with
    | .prim (.bool true) => da
    | .prim (.bool false) => db
    | _ => .st .mtSt
  | .save, ds, dp, dv => copyTo ds dp dv
  | .push, ds, dp, dv => pushT ds dp (stripVal dv)
  | .atIn _, _, dp, di => dp ++ [.at (asInt di)]
  | .write, _, _, _ => ()
  | .saveIn, ds, dp, dv => copyTo ds dp dv

/-! ## The bridge -/

/-- A denotation agrees with a typed value: the value itself, the Theory
path, the storage or stored value up to `Equiv`. -/
def Srt.Bridge (C : Contract) (H : HTy) : (s : Srt) → s.TDen → s.Den C H → Prop
  | .val _, d, x => d = .prim (PrimTy.erase x)
  | .path _, d, r => d = r.absT
  | .st, d, w => Struct.Equiv d (Storage.absT w)
  | .sv _, d, w => StValue.Equiv d w.absT
  | .sts _, d, w => Struct.Equiv d (Storage.absT w)
  | .spath _ _, d, r => d = r.absT
  | .ident _, _, _ | .addr _, _, _ | .mem, _, _ | .mv _, _, _ => True

/-- A denotation agrees with a typed reading wherever it returns. -/
def Srt.BridgeO (C : Contract) (H : HTy) (s : Srt) (d : s.TDen) (x : Option (s.Den C H)) : Prop :=
  ∀ v, x = some v → Srt.Bridge C H s d v

section Bridge

variable (g : State C [])

/-- An index read as the Theory's `int`: the integer it is hashed as. -/
theorem asInt_erase_keyTy {k : PrimTy} (i : k.keyTy.Denote) :
    asInt (.prim (PrimTy.erase i)) = PrimTy.key i := by
  cases k <;> rfl

/-- A typed storage path's segments, a member further. -/
theorem SRef.absT_field {C : Contract} {s f : Name} {T : Ty} (r : SRef C (.ref (.struct s)))
    (h : C.fieldType s f = some T) : (r.field h).absT = r.absT ++ [Seg.field f] := by
  simp only [SRef.absT, SRef.field, SRef.append, Path.erase_append, rootPath, List.cons_append]
  rfl

/-- …an index further. -/
theorem SRef.absT_index {C : Contract} {R : RefTy} {k : PrimTy} {V : Ty} (r : SRef C (.ref R))
    (it : IndexTy R k V) (i : Int) : (r.index it i).absT = r.absT ++ [Seg.at i] := by
  simp only [SRef.absT, SRef.index, SRef.append, Path.erase_append, Path.erase_index, rootPath,
    List.cons_append]

/-- The value at a typed reference, as the Theory finds it. -/
theorem Storage.findSt_absT {C : Contract} {U : Ty} {st : Storage C} {r : SRef C U} {w : SVal U}
    (h : st.find r = some w) : findSt st.absT r.absT = w.absT := by
  have hf := Storage.findStorage_erase (σ := st.sem) (st := st) rfl r
  rw [h] at hf
  exact Semantics.State.abs_findStorage (σ := st.sem) hf

/-- The live length of a typed array, as the Theory reads it. -/
theorem Storage.lenAt_absT {C : Contract} {E : Ty} {st : Storage C}
    {r : SRef C (.ref (.array E))} {w : SVal (.ref (.array E))} (h : st.find r = some w) :
    lenAt st.absT r.absT = ((SVal.view w : ArrView E).n : Int) := by
  have hf := Storage.findStorage_erase (σ := st.sem) (st := st) rfl r
  rw [h] at hf
  cases w with
  | array e sh hn =>
    simp only [toRes, SVal.erase_array] at hf
    have := Semantics.State.abs_lenAt_of_array hf
    rw [SVec.length_erase] at this
    exact this

/-- `select(s, r)` on the erasure: the struct at `r`, its members erased. -/
theorem Storage.findStorage_selectT {C : Contract} {s r : Name} (σ : Semantics.State)
    (st : Storage C) (hs : σ.storage = st.erase) (h : C.rootType r = some (.ref (.struct s))) :
    σ.findStorage r [] = .ok (.struct (SFields.erase (Storage.selectT st h))) := by
  simp only [Semantics.State.findStorage, hs, Storage.erase, SFields.lookupBy_erase st h,
    Storage.selectT]
  generalize st.get h = w
  cases w
  simp only [SVal.erase_struct, Semantics.SVal.find]
  rfl

/-- `select(s, r)` in the Theory is the struct at `r`. -/
theorem Storage.select_absT {C : Contract} {s r : Name} {d : Struct} {st : Storage C}
    (hd : Struct.Equiv d st.absT) (h : C.rootType r = some (.ref (.struct s))) :
    Struct.Equiv (asStruct (selectSt d (.field r))) (Storage.selectT st h).absT := by
  have e3 : findSt st.sem.abs (rootPath r []) = (Semantics.SVal.struct
      (SFields.erase (Storage.selectT st h))).abs :=
    Semantics.State.abs_findStorage (Storage.findStorage_selectT st.sem st rfl h)
  have e5 := StValue.Equiv.asStruct (StValue.Equiv.findSt hd (rootPath r []))
  rw [Storage.abs_sem] at e3
  rw [e3] at e5
  exact e5

theorem Op0.denote_eval {s : Srt} (o : Op0 C s) : Srt.BridgeO C g.H s (o.denote g) (o.eval g) := by
  intro v hv
  rw [Op0.eval_eq_evalM] at hv
  cases o <;> simp only [Op0.evalM, Option.some.injEq] at hv <;> subst hv
  all_goals first | rfl | exact StValue.Equiv.refl _ | trivial

theorem Op1.denote_eval {a s : Srt} (o : Op1 C a s) {x : Option (a.Den C g.H)} {d : a.TDen}
    (hx : Srt.BridgeO C g.H a d x) : Srt.BridgeO C g.H s (o.denote g d) (o.eval g x) := by
  intro v hv
  rw [Op1.eval_eq_evalM] at hv
  cases x with
  | none => cases o <;> simp only [Op1.evalM, Option.bind_none, Option.map_none, reduceCtorEq] at hv
  | some u =>
  have hu := hx u rfl
  cases o with
  | unop op h =>
    simp only [Op1.evalM, Option.bind_some] at hv
    simp only [Srt.Bridge] at hu ⊢
    have he := UnOp.evalT_erase op h u
    rw [hv] at he
    simp only [Op1.denote, hu, StValue.toRes]
    exact congrArg Semantics.Res.toSt he
  | net =>
    simp only [Op1.evalM, Option.bind_some] at hv
    simp only [Srt.Bridge] at hu ⊢
    simp only [Op1.denote, hu]
    exact congrArg StValue.prim (PrimTy.erase_of_ofValue? hv).symm
  | delValue =>
    simp only [Op1.evalM, Option.map_some, Option.some.injEq] at hv
    subst hv
    simp only [Srt.Bridge] at hu ⊢
    rw [Op1.denote, hu]
    rename_i p
    cases p <;> rfl
  | field h =>
    simp only [Op1.evalM, Option.map_some, Option.some.injEq] at hv
    subst hv
    simp only [Srt.Bridge] at hu ⊢
    rw [Op1.denote, hu, SRef.absT_field]
  | next =>
    simp only [Op1.evalM, Option.bind_some, Storage.nextT, Option.map_eq_some_iff] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    simp only [Srt.Bridge] at hu ⊢
    rw [Op1.denote, hu, SRef.absT_index, Storage.lenAt_absT hw]
  | sval =>
    simp only [Op1.evalM, Option.map_some, Option.some.injEq] at hv
    subst hv
    simp only [Srt.Bridge] at hu ⊢
    rw [Op1.denote, hu, SVal.absT, SVal.erase_prim, Semantics.SVal.abs]
    exact StValue.Equiv.refl _
  | newArr h =>
    simp only [Op1.evalM, Option.map_some, Option.some.injEq] at hv
    subst hv
    simp only [Srt.Bridge] at hu ⊢
    rw [Op1.denote, hu, SVal.absT, newArrT_erase]
    exact StValue.Equiv.refl _
  | alloc | mfield | addM | mval | ref => trivial
  | wt =>
    simp only [Op1.evalM, Option.bind_some, Storage.wtT] at hv
    split at hv
    · cases hv; rfl
    · cases hv
  | select r h =>
    simp only [Op1.evalM, Option.map_some, Option.some.injEq] at hv
    subst hv
    exact Storage.select_absT hu h
  | selectIn h =>
    simp only [Op1.evalM, Option.map_some, Option.some.injEq] at hv
    subst hv
    exact Storage.select_absT hu h
  | fieldIn h =>
    simp only [Op1.evalM, Option.map_some, Option.some.injEq] at hv
    subst hv
    simp only [Srt.Bridge] at hu ⊢
    rw [Op1.denote, hu, SRef.absT_field]

/-- A push that returns had room. -/
theorem Storage.full_of_push {C : Contract} {E : Ty} {st st' : Storage C}
    {r : SRef C (.ref (.array E))} {val : SVal E → Option (SVal E)}
    (h : st.push r val = some st') : st.full r = false := by
  unfold Storage.push at h
  unfold Storage.full
  cases hf : st.find r with
  | none => rfl
  | some v =>
    simp only [hf, Option.bind_eq_bind, Option.bind_some] at h
    by_cases hb : (SVal.view v : ArrView E).n + 1 < 2 ^ 256
    · simp only [hb, decide_true, Bool.not_true]
    · exfalso
      revert h
      cases val (pushSlot E (SVal.view v : ArrView E).shadow.toList).1 <;>
        simp only [Option.bind_none, Option.bind_some, hb, dite_false, reduceCtorEq,
          imp_self]

/-- A push as a place that returns had room. -/
theorem Storage.full_of_pushPlace {C : Contract} {E : Ty} {st : Storage C}
    {r : SRef C (.ref (.array E))} {q : Storage C × Nat}
    (h : st.pushPlace r = some q) : st.full r = false := by
  unfold Storage.pushPlace at h
  unfold Storage.full
  cases hf : st.find r with
  | none => rfl
  | some v =>
    simp only [hf, Option.bind_eq_bind, Option.bind_some] at h
    by_cases hb : (SVal.view v : ArrView E).n + 1 < 2 ^ 256
    · simp only [hb, decide_true, Bool.not_true]
    · simp only [hb, dite_false, reduceCtorEq] at h

/-- A stored word is its value. -/
theorem SVal.absT_prim_view {p : PrimTy} (w : SVal (.prim p)) :
    w.absT = .prim (PrimTy.erase (SVal.view w : p.Denote)) := by
  cases w
  rw [SVal.absT, SVal.erase_prim, Semantics.SVal.abs]
  rfl

/-- A storage untyped with the typed one in place. -/
theorem Storage.abs_into_sem {C : Contract} (st st' : Storage C) :
    (Storage.into st.sem st').abs = st'.absT := rfl

/-- `find` on a typed storage, up to `Equiv` of the storage. -/
theorem Storage.findSt_equiv {C : Contract} {U : Ty} {d : Struct} {st : Storage C}
    (hd : Struct.Equiv d st.absT) {r : SRef C U} {w : SVal U} (h : st.find r = some w) :
    StValue.Equiv (findSt d r.absT) w.absT := by
  have e := StValue.Equiv.findSt hd r.absT
  rw [Storage.findSt_absT h] at e
  exact e

theorem Storage.delAt_equiv {C : Contract} {U : Ty} {d : Struct} {st st' : Storage C}
    (hd : Struct.Equiv d st.absT) {r : SRef C U} (h : st.delete r = some st') :
    Struct.Equiv (StValue.delAt d r.absT) st'.absT := by
  have he := Storage.delete_erase (σ := st.sem) (st := st) rfl r
  rw [h] at he
  obtain ⟨cur, h1, h2⟩ := Semantics.bind_ok_inv he
  exact StValue.Equiv.trans (Struct.Equiv.delAt hd _) (Semantics.State.abs_delete h1 h2)

theorem Storage.write_equiv {C : Contract} {U : Ty} {d : Struct} {st st' : Storage C}
    (hd : Struct.Equiv d st.absT) {r : SRef C U} {w : SVal U} {dv : StValue}
    (hv : StValue.Equiv dv w.absT) (h : st.write r w = some st') :
    Struct.Equiv (copyTo d r.absT dv) st'.absT := by
  have he := Storage.writeStorage_erase (σ := st.sem) (st := st) rfl r w
  rw [h] at he
  exact StValue.Equiv.trans (Struct.Equiv.copyTo hd hv _)
    (Semantics.State.abs_writeStorage (σ := st.sem) he)

theorem Op2.denote_eval {a b s : Srt} (o : Op2 C a b s) {x : Option (a.Den C g.H)}
    {y : Option (b.Den C g.H)} {da : a.TDen} {db : b.TDen}
    (hx : Srt.BridgeO C g.H a da x) (hy : Srt.BridgeO C g.H b db y) :
    Srt.BridgeO C g.H s (o.denote g x y da db) (o.eval g x y) := by
  intro v hv
  have hv' := hv
  rw [Op2.eval_eq_evalM] at hv
  cases x with
  | none => cases o <;> simp only [Op2.evalM, Option.bind_none, Option.bind_eq_bind,
      reduceCtorEq] at hv
  | some u =>
  have hu := hx u rfl
  cases o with
  | binop op h =>
    rename_i p
    simp only [Op2.evalM, Option.bind_some, binopT] at hv
    simp only [Srt.Bridge] at hu ⊢
    simp only [Op2.denote, hu, StValue.toRes]
    cases hs : op.shortT u with
    | some r =>
      rw [hs] at hv
      cases hv
      show Semantics.Res.toSt (evalBinop op p (PrimTy.erase u) _) = _
      rw [evalBinop_short hs]
      rfl
    | none =>
      rw [hs] at hv
      cases y with
      | none => cases hv
      | some w =>
        have hw : db = .prim (PrimTy.erase w) := hy w rfl
        simp only [Option.bind_some] at hv
        show Semantics.Res.toSt (evalBinop op p (PrimTy.erase u) _) = _
        rw [hw, evalBinop_long hs]
        have he := BinOp.evalT_erase op h u w
        rw [hv] at he
        show Semantics.Res.toSt (evalBinop op p (PrimTy.erase u) (.ok (PrimTy.erase w))) = _
        rw [he]
        rfl
  | read | mlen =>
    show PrimTy.toSt _ = _
    rw [hv']
    rfl
  | copyMem =>
    simp only [Op2.denote, hv']
    exact StValue.Equiv.refl _
  | iread | copy | mat | copySt => trivial
  | find | findIn =>
    cases y with
    | none => simp only [Op2.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        reduceCtorEq] at hv
    | some w =>
    have hw := hy w rfl
    simp only [Srt.Bridge] at hu hw ⊢
    simp only [Op2.evalM, Option.bind_some, Option.bind_eq_bind] at hv
    rw [Option.bind_eq_some_iff] at hv
    obtain ⟨sv, hsv, hv⟩ := hv
    cases hv
    rw [Op2.denote, hw, ← StValue.Equiv.prim_iff, ← SVal.absT_prim_view]
    exact Storage.findSt_equiv hu hsv
  | sfind | sfindIn =>
    cases y with
    | none => simp only [Op2.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        reduceCtorEq] at hv
    | some w =>
    have hw := hy w rfl
    simp only [Srt.Bridge] at hu hw ⊢
    simp only [Op2.evalM, Option.bind_some, Option.bind_eq_bind] at hv
    rw [Op2.denote, hw]
    exact Storage.findSt_equiv hu hv
  | delAt | delAtIn =>
    cases y with
    | none => simp only [Op2.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        reduceCtorEq] at hv
    | some w =>
    have hw := hy w rfl
    simp only [Srt.Bridge] at hu hw ⊢
    simp only [Op2.evalM, Option.bind_some, Option.bind_eq_bind] at hv
    rw [Op2.denote, hw]
    exact Storage.delAt_equiv hu hv
  | len =>
    cases y with
    | none => simp only [Op2.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        reduceCtorEq] at hv
    | some w =>
    have hw := hy w rfl
    simp only [Srt.Bridge] at hu hw ⊢
    simp only [Op2.evalM, Option.bind_some, Option.bind_eq_bind] at hv
    have he := Storage.arrayLen_erase (σ := u.sem) (st := u) rfl w
    rw [hv] at he
    have e3 : findSt u.absT (w.absT ++ [lengthSeg]) = .prim (PrimTy.erase v) :=
      Semantics.State.abs_arrayLen (σ := u.sem) he
    rw [Op2.denote, hw, ← StValue.Equiv.prim_iff, ← e3]
    exact StValue.Equiv.findSt hu _
  | «at» it =>
    cases y with
    | none => simp only [Op2.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        reduceCtorEq] at hv
    | some w =>
    have hw := hy w rfl
    simp only [Srt.Bridge] at hu hw ⊢
    simp only [Op2.evalM, Option.bind_some, Option.bind_eq_bind] at hv
    simp only [Storage.atT, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hv
    obtain ⟨_, _, rfl⟩ := hv
    rw [Op2.denote, hu, hw, asInt_erase_keyTy, SRef.absT_index]
  | nextIn =>
    cases y with
    | none => simp only [Op2.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        reduceCtorEq] at hv
    | some w =>
    have hw := hy w rfl
    simp only [Srt.Bridge] at hu hw ⊢
    simp only [Op2.evalM, Option.bind_some, Option.bind_eq_bind] at hv
    simp only [Storage.nextT, Option.map_eq_some_iff] at hv
    obtain ⟨sv, hsv, rfl⟩ := hv
    rw [Op2.denote, Struct.Equiv.lenAt hu, hw, SRef.absT_index, Storage.lenAt_absT hsv]
  | pushSlot =>
    cases y with
    | none => simp only [Op2.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        reduceCtorEq] at hv
    | some w =>
    have hw := hy w rfl
    simp only [Srt.Bridge] at hu hw ⊢
    simp only [Op2.evalM, Option.bind_some, Option.bind_eq_bind] at hv
    have he := Storage.pushAt_erase (σ := u.sem) (st := u) rfl w pure some (fun _ => rfl)
      (.inl (Storage.full_of_push hv))
    rw [hv] at he
    have e4 : v.absT = _ := Semantics.State.abs_pushAt_slot (σ := u.sem) he
    rw [Op2.denote, hw, e4]
    exact Struct.Equiv.pushSlotT _ _ hu _
  | pop =>
    cases y with
    | none => simp only [Op2.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        reduceCtorEq] at hv
    | some w =>
    have hw := hy w rfl
    simp only [Srt.Bridge] at hu hw ⊢
    simp only [Op2.evalM, Option.bind_some, Option.bind_eq_bind] at hv
    have he := Storage.popAt_erase (σ := u.sem) (st := u) rfl false w
    rw [hv] at he
    rw [Op2.denote, hw]
    exact StValue.Equiv.trans (Struct.Equiv.popT hu _) (Semantics.State.abs_pop (σ := u.sem) he)
  | shrink =>
    cases y with
    | none => simp only [Op2.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        reduceCtorEq] at hv
    | some w =>
    have hw := hy w rfl
    simp only [Srt.Bridge] at hu hw ⊢
    simp only [Op2.evalM, Option.bind_some, Option.bind_eq_bind] at hv
    have he := Storage.popAt_erase (σ := u.sem) (st := u) rfl true w
    rw [hv] at he
    have e4 : v.absT = _ := Semantics.State.abs_shrink (σ := u.sem) he
    rw [Op2.denote, hw, e4]
    exact Struct.Equiv.shrinkT hu _
  | extend =>
    cases y with
    | none => simp only [Op2.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        reduceCtorEq] at hv
    | some w =>
    have hw := hy w rfl
    simp only [Srt.Bridge] at hu hw ⊢
    simp only [Op2.evalM, Option.bind_some, Option.bind_eq_bind] at hv
    rw [Option.bind_eq_some_iff] at hv
    obtain ⟨⟨st', n⟩, hq, hv⟩ := hv
    cases hv
    have he := Storage.pushPlaceAt_erase (σ := u.sem) (st := u) rfl w
      (Storage.full_of_pushPlace hq)
    rw [hq] at he
    have e4 : st'.absT = _ := (Semantics.State.abs_pushPlaceAt (σ := u.sem) he).1
    rw [Op2.denote, hw, e4]
    exact Struct.Equiv.pushSlotT _ _ hu _


theorem Op3.denote_eval {a b c s : Srt} (o : Op3 C a b c s) {x : Option (a.Den C g.H)}
    {y : Option (b.Den C g.H)} {z : Option (c.Den C g.H)} {da : a.TDen} {db : b.TDen}
    {dc : c.TDen} (hx : Srt.BridgeO C g.H a da x) (hy : Srt.BridgeO C g.H b db y)
    (hz : Srt.BridgeO C g.H c dc z) :
    Srt.BridgeO C g.H s (o.denote da db dc) (o.eval g x y z) := by
  intro v hv
  rw [Op3.eval_eq_evalM] at hv
  cases x with
  | none => cases o <;> simp only [Op3.evalM, Option.bind_none, Option.bind_eq_bind,
      reduceCtorEq] at hv
  | some u =>
  have hu := hx u rfl
  cases o with
  | ite =>
    simp only [Op3.evalM, Option.bind_some] at hv
    simp only [Srt.Bridge] at hu
    cases u with
    | true => simp only [Op3.denote, hu, PrimTy.erase]; exact hy v hv
    | false => simp only [Op3.denote, hu, PrimTy.erase]; exact hz v hv
  | write => trivial
  | _ =>
    cases y with
    | none => simp only [Op3.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        reduceCtorEq] at hv
    | some w =>
    cases z with
    | none => simp only [Op3.evalM, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
        Option.map_none, Storage.push_none, reduceCtorEq] at hv
    | some t =>
    have hw := hy w rfl
    have ht := hz t rfl
    simp only [Srt.Bridge] at hu hw ht ⊢
    simp only [Op3.evalM, Option.bind_some, Option.bind_eq_bind, Option.map_some] at hv
    first
    | (rw [Op3.denote, hw]; exact Storage.write_equiv hu ht hv)
    | (simp only [Storage.atT, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at hv
       obtain ⟨_, _, rfl⟩ := hv
       rw [Op3.denote, hw, ht, asInt_erase_keyTy, SRef.absT_index])
    | (have he := Storage.pushAt_erase (σ := u.sem) (st := u) rfl w
          (fun _ => .ok t.strip.erase) (fun _ => some t.strip) (fun _ => rfl)
          (.inl (Storage.full_of_push hv))
       rw [hv] at he
       have e4 : v.absT = _ := Semantics.State.abs_pushAt_const (σ := u.sem) _ he
       rw [Op3.denote, hw, e4]
       refine Struct.Equiv.pushT hu ?_ _
       rw [SVal.strip_erase]
       exact StValue.Equiv.trans (StValue.Equiv.stripVal ht) (Semantics.SVal.abs_strip _))

end Bridge

end Solidity
