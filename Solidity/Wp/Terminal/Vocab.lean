import Solidity.Wp.Terminal.Table

/-!
# Vocabulary bridges

Each lemma equates one interpreter evaluator, on the syntactic shapes the
terminal rules admit, with the state-vocabulary reader of
`Table.lean`.  They are the only place the two sides meet; the
per-rule `_update` theorems in the sibling files are unfold-then-bridge.
-/

namespace Solidity
namespace Wp

open Semantics

/-! ## Shape predicates -/

/-- `p`, `p.f`, `p[se]` with `p` a variable and `se` simple. -/
def simplePathB : WrappedExpr -> Bool
  | WrappedExpr.var _ _ _ => true
  | WrappedExpr.field _ _ base _ => base.simple
  | WrappedExpr.index _ _ base ix => base.simple && ix.simple
  | _ => false

theorem resolveS_bool (s : State) (b : Bool) :
    resolveS s (WrappedExpr.bool b) = .error .stuck := by
  rw [resolveS] <;> simp

theorem resolveS_intLit (s : State) (t : Ty) (v : Int) :
    resolveS s (WrappedExpr.intLit t v) = .error .stuck := by
  rw [resolveS] <;> simp

theorem resolveMBase_bool (s : State) (b : Bool) :
    resolveMBase s (WrappedExpr.bool b) = .error .stuck := by
  rw [resolveMBase] <;> simp

theorem resolveMBase_intLit (s : State) (t : Ty) (v : Int) :
    resolveMBase s (WrappedExpr.intLit t v) = .error .stuck := by
  rw [resolveMBase] <;> simp

/-- A simple expression, or a simple storage/memory place. -/
def terminalRhsB (e : WrappedExpr) : Bool :=
  e.simple ||
    (match e with
      | WrappedExpr.field Kind.storage _ _ _ => simplePathB e
      | WrappedExpr.index Kind.storage _ _ _ => simplePathB e
      | WrappedExpr.field Kind.memory _ _ _ => simplePathB e
      | WrappedExpr.index Kind.memory _ _ _ => simplePathB e
      | _ => false)

/-! ## `Res` plumbing -/

theorem Except.map_bind_ok {α β : Type} (x : Res α) (f : α -> β) :
    (x.map f) = (x >>= fun a => Except.ok (f a)) := by
  cases x <;> rfl

/-! ## Storage paths -/

theorem resolveS_var (s : State) (k : Kind) (t : Ty) (fld : Field) :
    resolveS s (WrappedExpr.var k t fld) =
      (varPath s fld).map fun p => (s, p) := by
  rw [resolveS]
  unfold varPath
  cases lookupBy fld.name s.env with
  | none =>
      show (if fld.origin = some StorageOrigin.global then
          Except.ok (s, fld.name, []) else Except.error Halt.stuck) = _
      split <;> rfl
  | some b => cases b <;> rfl

theorem evalInt_simple (s : State) (e : WrappedExpr) (h : e.simple = true) :
    evalInt s e = (simpleInt s e).map fun i => (s, i) := by
  cases e with
  | bool b =>
      rw [evalInt, evalValue]
      simp only [simpleInt, simpleVal, bind, Except.bind]
      cases Value.asInt (Value.bool b) <;> rfl
  | intLit t v =>
      rw [evalInt, evalValue]
      simp only [simpleInt, simpleVal, bind, Except.bind]
      cases Value.asInt (Value.int v) <;> rfl
  | var k t fld =>
      cases k with
      | stack =>
          rw [evalInt, evalValue]
          simp only [simpleInt, simpleVal, stackVal, State.getEnv, bind,
            Except.bind]
          cases lookupBy fld.name s.env with
          | none => rfl
          | some b =>
              cases b with
              | val v => cases Value.asInt v <;> rfl
              | spath r sg => rfl
              | mref id => rfl
      | storage =>
          rw [evalInt, evalValue, resolveS_var]
          simp only [simpleInt, simpleVal, bind, Except.bind, Except.map]
          cases varPath s fld with
          | error e => rfl
          | ok p =>
              simp only []
              cases s.findStorage p.1 p.2 with
              | error e => rfl
              | ok v =>
                  simp only []
                  cases SVal.asValue v with
                  | error e => rfl
                  | ok w => cases Value.asInt w <;> rfl
      | memory =>
          rw [evalInt, evalValue]
          rfl
  | _ => exact absurd h (by simp [Typed.WrappedExpr.simple])

theorem resolveS_placePath (s : State) (e : WrappedExpr)
    (h : simplePathB e = true) :
    resolveS s e = (placePath s e).map fun p => (s, p) := by
  cases e with
  | var k t fld => exact resolveS_var s k t fld
  | field k t base f =>
      cases base with
      | var k' t' fld =>
          rw [resolveS, resolveS_var]
          simp only [placePath, bind, Except.bind, Except.map]
          cases varPath s fld with
          | error e => rfl
          | ok p => obtain ⟨r, sg⟩ := p; rfl
      | bool b => rw [resolveS, resolveS_bool]; rfl
      | intLit t' v => rw [resolveS, resolveS_intLit]; rfl
      | _ => exact absurd h (by simp [simplePathB, Typed.WrappedExpr.simple])
  | index k t base ix =>
      have hix : ix.simple = true := by
        cases base <;> simp_all [simplePathB, Typed.WrappedExpr.simple]
      cases base with
      | var k' t' fld =>
          rw [resolveS, resolveS_var]
          simp only [placePath, bind, Except.bind, Except.map]
          cases varPath s fld with
          | error e => rfl
          | ok p =>
              obtain ⟨r, sg⟩ := p
              simp only [evalInt_simple s ix hix, Except.map]
              cases simpleInt s ix <;> rfl
      | bool b => rw [resolveS, resolveS_bool]; rfl
      | intLit t' v => rw [resolveS, resolveS_intLit]; rfl
      | _ => exact absurd h (by simp [simplePathB, Typed.WrappedExpr.simple])
  | _ => exact absurd h (by simp [simplePathB])

/-! ## Memory places -/

theorem resolveMBase_var (s : State) (k : Kind) (t : Ty) (m : Field) :
    resolveMBase s (WrappedExpr.var k t m) =
      (memRef s m.name).map fun id => (s, id) := by
  rw [resolveMBase]
  simp only [memRef, State.getEnv, bind, Except.bind, Except.map]
  cases lookupBy m.name s.env with
  | none => rfl
  | some b => cases b <;> rfl

/-- `resolveMBase` on a simple base is the `memBase` reader. -/
theorem resolveMBase_simple (s : State) (base : WrappedExpr)
    (h : base.simple = true) :
    resolveMBase s base = (memBase s base).map fun id => (s, id) := by
  cases base with
  | var k t m => rw [resolveMBase_var]; rfl
  | bool b => rw [resolveMBase_bool]; rfl
  | intLit t v => rw [resolveMBase_intLit]; rfl
  | _ => exact absurd h (by simp [Typed.WrappedExpr.simple])

theorem readM_readMem (s : State) (e : WrappedExpr)
    (h : simplePathB e = true) :
    readM s e = (readMem s e).map fun v => (s, v) := by
  cases e with
  | var k t m =>
      rw [readM]
      simp only [readMem, memRef, State.getEnv, bind, Except.bind, Except.map]
      cases lookupBy m.name s.env with
      | none => rfl
      | some b => cases b <;> rfl
  | field k t base f =>
      have hb : base.simple = true := by simpa [simplePathB] using h
      rw [readM, resolveMBase_simple s base hb]
      simp only [readMem, bind, Except.bind, Except.map]
      cases memBase s base with
      | error e => rfl
      | ok id =>
          simp only []
          cases s.getObj id with
          | error e => rfl
          | ok obj =>
              cases obj with
              | struct fields =>
                  simp only [] <;> cases lookupBy f.name fields <;> rfl
              | array elems => rfl
  | index k t base ix =>
      have hbi : base.simple = true ∧ ix.simple = true := by
        simpa [simplePathB] using h
      have hb := hbi.1
      have hix := hbi.2
      rw [readM, resolveMBase_simple s base hb]
      simp only [readMem, bind, Except.bind, Except.map]
      cases memBase s base with
      | error e => rfl
      | ok id =>
          simp only [evalInt_simple s ix hix, Except.map]
          cases simpleInt s ix with
          | error e => rfl
          | ok i =>
              simp only []
              cases s.getObj id with
              | error e => rfl
              | ok obj =>
                  cases obj with
                  | struct fields => rfl
                  | array elems =>
                      simp only []
                      split <;> rfl
  | _ => exact absurd h (by simp [simplePathB])

/-! ## Values -/

theorem evalValue_readVal (s : State) (e : WrappedExpr)
    (h : terminalRhsB e = true) :
    evalValue s e = (readVal s e).map fun v => (s, v) := by
  cases e with
  | bool b => rw [evalValue]; rfl
  | intLit t v => rw [evalValue]; rfl
  | var k t fld =>
      cases k with
      | stack =>
          rw [evalValue]
          simp only [readVal, stackVal, State.getEnv, bind, Except.bind,
            Except.map]
          cases lookupBy fld.name s.env with
          | none => rfl
          | some b => cases b <;> rfl
      | storage =>
          rw [evalValue, resolveS_var]
          simp only [readVal, placePath, bind, Except.bind, Except.map]
          cases varPath s fld with
          | error e => rfl
          | ok p =>
              obtain ⟨r, sg⟩ := p
              simp only []
              cases s.findStorage r sg with
              | error e => rfl
              | ok v =>
                  simp only [] <;> cases SVal.asValue v <;> rfl
      | memory => rw [evalValue]; rfl
  | field k t base f =>
      have hp : simplePathB (WrappedExpr.field k t base f) = true := by
        cases k <;> simpa [terminalRhsB, Typed.WrappedExpr.simple] using h
      cases k with
      | storage =>
          rw [evalValue, resolveS_placePath s _ hp]
          simp only [readVal, bind, Except.bind, Except.map]
          cases placePath s (WrappedExpr.field Kind.storage t base f) with
          | error e => rfl
          | ok p =>
              obtain ⟨r, sg⟩ := p
              simp only []
              cases s.findStorage r sg with
              | error e => rfl
              | ok v =>
                  simp only [] <;> cases SVal.asValue v <;> rfl
      | memory =>
          rw [evalValue, readM_readMem s _ hp]
          simp only [readVal, bind, Except.bind, Except.map]
          cases readMem s (WrappedExpr.field Kind.memory t base f) with
          | error e => rfl
          | ok v =>
              simp only [] <;> cases MVal.asValue v <;> rfl
      | stack => exact absurd h (by simp [terminalRhsB, Typed.WrappedExpr.simple])
  | index k t base ix =>
      have hp : simplePathB (WrappedExpr.index k t base ix) = true := by
        cases k <;> simpa [terminalRhsB, Typed.WrappedExpr.simple] using h
      cases k with
      | storage =>
          rw [evalValue, resolveS_placePath s _ hp]
          simp only [readVal, bind, Except.bind, Except.map]
          cases placePath s (WrappedExpr.index Kind.storage t base ix) with
          | error e => rfl
          | ok p =>
              obtain ⟨r, sg⟩ := p
              simp only []
              cases s.findStorage r sg with
              | error e => rfl
              | ok v =>
                  simp only [] <;> cases SVal.asValue v <;> rfl
      | memory =>
          rw [evalValue, readM_readMem s _ hp]
          simp only [readVal, bind, Except.bind, Except.map]
          cases readMem s (WrappedExpr.index Kind.memory t base ix) with
          | error e => rfl
          | ok v =>
              simp only [] <;> cases MVal.asValue v <;> rfl
      | stack => exact absurd h (by simp [terminalRhsB, Typed.WrappedExpr.simple])
  | _ => exact absurd h (by simp [terminalRhsB, Typed.WrappedExpr.simple])

theorem evalInt_readInt (s : State) (e : WrappedExpr)
    (h : terminalRhsB e = true) :
    evalInt s e = (readInt s e).map fun i => (s, i) := by
  rw [evalInt, evalValue_readVal s e h]
  simp only [readInt, bind, Except.bind, Except.map]
  cases readVal s e with
  | error err => rfl
  | ok v =>
      simp only [] <;> cases Value.asInt v <;> rfl

theorem terminalRhsB_of_simple {e : WrappedExpr} (h : e.simple = true) :
    terminalRhsB e = true := by
  simp [terminalRhsB, h]

theorem simplePathB_of_storagePlace {e : WrappedExpr}
    (h : terminalRhsB e = true) (hs : e.simple = false) :
    simplePathB e = true := by
  cases e <;> simp_all [terminalRhsB, Typed.WrappedExpr.simple, simplePathB]
    <;> split at h <;> simp_all

/-! ## Right-hand sides -/

theorem rhsToSVal_rhsSVal (s : State) (rhs : WrappedExpr)
    (h : terminalRhsB rhs = true) :
    rhsToSVal s rhs = (rhsSVal s rhs).map fun v => (s, v) := by
  unfold rhsToSVal rhsSVal
  by_cases hp : rhs.ty.isPrimitive = true
  · rw [if_pos hp, if_pos hp, evalValue_readVal s rhs h]
    simp only [bind, Except.bind, Except.map]
    cases readVal s rhs <;> rfl
  · rw [if_neg hp, if_neg hp]
    cases hk : rhs.kind with
    | storage =>
        by_cases hm : tyHasMapping rhs.ty = true
        · rw [if_pos hm, if_pos hm]; rfl
        · rw [if_neg hm, if_neg hm]
          have hsp : simplePathB rhs = true := by
            cases rhs <;> simp_all [terminalRhsB, Typed.WrappedExpr.simple,
              simplePathB, Typed.WrappedExpr.kind]
          rw [resolveS_placePath s rhs hsp]
          simp only [bind, Except.bind, Except.map]
          cases placePath s rhs with
          | error e => rfl
          | ok p =>
              obtain ⟨r, sg⟩ := p
              simp only [] <;> cases s.findStorage r sg <;> rfl
    | memory =>
        have hsp : simplePathB rhs = true := by
          cases rhs <;> simp_all [terminalRhsB, Typed.WrappedExpr.simple,
            simplePathB, Typed.WrappedExpr.kind]
        rw [readM_readMem s rhs hsp]
        simp only [bind, Except.bind, Except.map]
        cases readMem s rhs with
        | error e => rfl
        | ok mv =>
            simp only [] <;> cases copyMem s mv <;> rfl
    | stack => rfl

theorem rhsToMVal_rhsMVal (s : State) (rhs : WrappedExpr)
    (h : terminalRhsB rhs = true) :
    rhsToMVal s rhs = rhsMVal s rhs := by
  unfold rhsToMVal rhsMVal
  by_cases hp : rhs.ty.isPrimitive = true
  · rw [if_pos hp, if_pos hp, evalValue_readVal s rhs h]
    simp only [bind, Except.bind, Except.map]
    cases readVal s rhs <;> rfl
  · rw [if_neg hp, if_neg hp]
    cases hk : rhs.kind with
    | memory =>
        have hsp : simplePathB rhs = true := by
          cases rhs <;> simp_all [terminalRhsB, Typed.WrappedExpr.simple,
            simplePathB, Typed.WrappedExpr.kind]
        simp only [readM_readMem s rhs hsp, Except.map] <;>
          (cases readMem s rhs <;> rfl)
    | storage =>
        have hsp : simplePathB rhs = true := by
          cases rhs <;> simp_all [terminalRhsB, Typed.WrappedExpr.simple,
            simplePathB, Typed.WrappedExpr.kind]
        rw [resolveS_placePath s rhs hsp]
        simp only [bind, Except.bind, Except.map]
        cases placePath s rhs with
        | error e => rfl
        | ok p =>
            obtain ⟨r, sg⟩ := p
            simp only [] <;> cases s.findStorage r sg <;> rfl
    | stack => rfl

/-! ## Assignment targets (`resolveLoc`) -/

theorem resolveLoc_var (s : State) (k : Kind) (t : Ty) (fld : Field) :
    resolveLoc s (WrappedExpr.var k t fld) =
      match k with
      | Kind.stack => .ok (s, Loc.stack fld.name)
      | Kind.memory => .ok (s, Loc.memoryRoot fld.name)
      | Kind.storage =>
          if fld.origin = some StorageOrigin.global then
            .ok (s, Loc.storage fld.name [])
          else .ok (s, Loc.storageLocal fld.name) := by
  cases k <;> rw [resolveLoc]

theorem resolveLoc_storageField (s : State) (t : Ty) (base : WrappedExpr)
    (f : Field) (hp : simplePathB (WrappedExpr.field Kind.storage t base f) = true) :
    resolveLoc s (WrappedExpr.field Kind.storage t base f) =
      (placePath s (WrappedExpr.field Kind.storage t base f)).map
        fun p => (s, Loc.storage p.1 p.2) := by
  cases base with
  | var k' t' fld =>
      rw [resolveLoc, resolveS, resolveS_var]
      simp only [placePath, bind, Except.bind, Except.map]
      cases varPath s fld with
      | error e => rfl
      | ok p => obtain ⟨r, sg⟩ := p; rfl
  | bool b => rw [resolveLoc, resolveS, resolveS_bool]; rfl
  | intLit t' v => rw [resolveLoc, resolveS, resolveS_intLit]; rfl
  | _ => exact absurd hp (by simp [simplePathB, Typed.WrappedExpr.simple])

theorem resolveLoc_storageIndex (s : State) (t : Ty) (base ix : WrappedExpr)
    (hp : simplePathB (WrappedExpr.index Kind.storage t base ix) = true) :
    resolveLoc s (WrappedExpr.index Kind.storage t base ix) =
      (placePath s (WrappedExpr.index Kind.storage t base ix)).map
        fun p => (s, Loc.storage p.1 p.2) := by
  have hix : ix.simple = true := by
    cases base <;> simp_all [simplePathB, Typed.WrappedExpr.simple]
  cases base with
  | var k' t' fld =>
      rw [resolveLoc, resolveS_var]
      simp only [placePath, bind, Except.bind, Except.map]
      cases varPath s fld with
      | error e => rfl
      | ok p =>
          obtain ⟨r, sg⟩ := p
          simp only [evalInt_simple s ix hix, Except.map]
          cases simpleInt s ix <;> rfl
  | bool b => rw [resolveLoc, resolveS_bool]; rfl
  | intLit t' v => rw [resolveLoc, resolveS_intLit]; rfl
  | _ => exact absurd hp (by simp [simplePathB, Typed.WrappedExpr.simple])

theorem resolveLoc_memoryField (s : State) (t : Ty) (base : WrappedExpr)
    (f : Field) (hb : base.simple = true) :
    resolveLoc s (WrappedExpr.field Kind.memory t base f) =
      (memBase s base).map fun id => (s, Loc.memoryField id f.name) := by
  rw [resolveLoc, resolveMBase_simple s base hb]
  simp only [bind, Except.bind, Except.map]
  cases memBase s base <;> rfl

theorem resolveLoc_memoryIndex (s : State) (t : Ty) (base ix : WrappedExpr)
    (hb : base.simple = true) (hix : ix.simple = true) :
    resolveLoc s (WrappedExpr.index Kind.memory t base ix) =
      (memBase s base >>= fun id => simpleInt s ix >>= fun i =>
        .ok (id, i)).map fun x => (s, Loc.memoryIndex x.1 x.2) := by
  rw [resolveLoc, resolveMBase_simple s base hb]
  simp only [bind, Except.bind, Except.map]
  cases memBase s base with
  | error e => rfl
  | ok id =>
      simp only [evalInt_simple s ix hix, Except.map]
      cases simpleInt s ix <;> rfl

/-- `resolveS` on any simple expression or simple place (a literal is
stuck on both sides). -/
theorem resolveS_pathB (s : State) (e : WrappedExpr)
    (h : (e.simple || simplePathB e) = true) :
    resolveS s e = (placePath s e).map fun p => (s, p) := by
  cases e with
  | bool b => rw [resolveS_bool]; rfl
  | intLit t v => rw [resolveS_intLit]; rfl
  | _ =>
      apply resolveS_placePath
      simpa [simplePathB, Typed.WrappedExpr.simple] using h

/-- `resolveS` on a push place is the state-changing `pushPath`. -/
theorem resolveS_pushPlace (s : State) (t : WrappedExpr)
    (h : (t.simple || simplePathB t) = true) :
    resolveS s (WrappedExpr.pushPlace t) = pushPath s t := by
  rw [resolveS, resolveS_pathB s t h]
  simp only [pushPath, bind, Except.bind, Except.map]
  cases placePath s t with
  | error e => rfl
  | ok p =>
      obtain ⟨r, sg⟩ := p
      simp only []
      cases s.findStorage r sg with
      | error e => rfl
      | ok arr =>
          simp only []
          cases arr with
          | array elems =>
              cases t.ty with
              | prim pt => cases pt <;> rfl
              | ref rt =>
                  cases rt with
                  | array elemTy =>
                      simp only []
                  | struct n => rfl
                  | mapping k v => rfl
          | prim p => cases p <;> rfl
          | struct fields => rfl
          | map entries dflt => rfl

/-! ## Operators -/

theorem evalValue_binop (s : State) (op : BinOp) (l r : WrappedExpr)
    (hl : terminalRhsB l = true) (hr : terminalRhsB r = true) :
    evalValue s (WrappedExpr.binop op l r) =
      (binopVal op l r s).map fun v => (s, v) := by
  rw [evalValue, evalValue_readVal s l hl]
  simp only [binopVal, bind, Except.bind, Except.map]
  cases readVal s l with
  | error e => rfl
  | ok lv =>
      simp only []
      split
      · rfl
      · rfl
      · rw [evalValue_readVal s r hr]
        simp only [bind, Except.bind, Except.map]
        cases readVal s r with
        | error e => rfl
        | ok rv =>
            simp only []
            cases applyBinOp op lv rv with
            | error e => rfl
            | ok v =>
                simp only [] <;> cases checkArith (op.retTy l.ty) v <;> rfl

theorem evalValue_unop (s : State) (op : UnOp) (a : WrappedExpr)
    (ha : terminalRhsB a = true) :
    evalValue s (WrappedExpr.unop op a) =
      (unopVal op a s).map fun v => (s, v) := by
  rw [evalValue, evalValue_readVal s a ha]
  simp only [unopVal, bind, Except.bind, Except.map]
  cases readVal s a with
  | error e => rfl
  | ok v =>
      simp only []
      cases applyUnOp op v with
      | error e => rfl
      | ok w =>
          simp only []
          generalize a.ty = ty
          cases op <;> cases ty with
          | prim pt =>
              cases pt <;> first | rfl | (cases checkArith Ty.int w <;> rfl)
          | ref r => rfl

/-- The targets `++`/`--` may have: a stack variable, a storage variable,
or a simple storage place. -/
def incDecTargetB : WrappedExpr -> Bool
  | WrappedExpr.var Kind.stack _ _ => true
  | WrappedExpr.var Kind.storage _ _ => true
  | WrappedExpr.bool _ => true
  | WrappedExpr.intLit _ _ => true
  | WrappedExpr.field Kind.storage _ base _ => base.simple
  | WrappedExpr.index Kind.storage _ base ix => base.simple && ix.simple
  -- The memory twins, for the memory-target arithmetic family.  A memory
  -- *root* stays out: it binds an identity, and `readLoc`/`writeLoc` are
  -- stuck on `Loc.memoryRoot`.
  | WrappedExpr.field Kind.memory _ base _ => base.simple
  | WrappedExpr.index Kind.memory _ base ix => base.simple && ix.simple
  | _ => false

theorem resolveLoc_bool (s : State) (b : Bool) :
    resolveLoc s (WrappedExpr.bool b) = .error .stuck := by
  rw [resolveLoc] <;> simp

theorem resolveLoc_intLit (s : State) (t : Ty) (v : Int) :
    resolveLoc s (WrappedExpr.intLit t v) = .error .stuck := by
  rw [resolveLoc] <;> simp

theorem readLoc_storage (s : State) (r : Name) (sg : List Seg) :
    readLoc s (Loc.storage r sg) = s.findStorage r sg >>= SVal.asValue := by
  simp only [readLoc, bind, Except.bind]

/-! ### Memory slots: `readLoc`/`writeLoc` are the vocabulary readers -/

theorem readLoc_memoryField (s : State) (id : Nat) (f : Name) :
    readLoc s (Loc.memoryField id f) = memFieldVal s id f := by
  simp only [readLoc, memFieldVal, bind, Except.bind]
  rfl

theorem readLoc_memoryIndex (s : State) (id : Nat) (i : Int) :
    readLoc s (Loc.memoryIndex id i) = memIndexVal s id i := by
  simp only [readLoc, memIndexVal, bind, Except.bind]
  rfl

theorem writeLoc_memoryField (s : State) (id : Nat) (f : Name) (v : Value) :
    writeLoc s (Loc.memoryField id f) v = writeMemField s id f v.toMVal := by
  simp only [writeLoc, writeMemField, bind, Except.bind]
  rfl

theorem writeLoc_memoryIndex (s : State) (id : Nat) (i : Int) (v : Value) :
    writeLoc s (Loc.memoryIndex id i) v = writeMemIndex s id i v.toMVal := by
  simp only [writeLoc, writeMemIndex, bind, Except.bind]
  rfl

theorem evalValue_incDec (s : State) (op : IncDec) (t : WrappedExpr)
    (ht : incDecTargetB t = true) :
    evalValue s (WrappedExpr.incDec op t) = incDecUpd op t s := by
  rw [evalValue]
  cases t with
  | var k ty fld =>
      cases k with
      | stack =>
          rw [resolveLoc_var]
          simp only [incDecUpd, readLoc, writeLoc, stackVal, State.getEnv,
            bind, Except.bind]
          cases lookupBy fld.name s.env with
          | none => rfl
          | some b =>
              cases b with
              | val old =>
                  simp only []
                  cases Value.asInt old with
                  | error e => rfl
                  | ok n =>
                      simp only []
              | spath r sg => rfl
              | mref id => rfl
      | storage =>
          rw [resolveLoc_var]
          simp only [incDecUpd, locPath, bind, Except.bind]
          by_cases hg : fld.origin = some StorageOrigin.global
          · rw [if_pos hg, if_pos hg]
            simp only [readLoc_storage, writeLoc, bind, Except.bind]
            cases s.findStorage fld.name [] with
            | error e => rfl
            | ok v =>
                simp only []
                cases SVal.asValue v with
                | error e => rfl
                | ok old =>
                    simp only []
                    cases Value.asInt old with
                    | error e => rfl
                    | ok n =>
                        simp only []
          · rw [if_neg hg, if_neg hg]
            rfl
      | memory => exact absurd ht (by simp [incDecTargetB])
  | field k ty base f =>
      cases k with
      | storage =>
          have hp : simplePathB (WrappedExpr.field Kind.storage ty base f) = true := by
            simpa [incDecTargetB, simplePathB] using ht
          rw [resolveLoc_storageField s ty base f hp]
          simp only [incDecUpd, locPath, bind, Except.bind, Except.map]
          cases placePath s (WrappedExpr.field Kind.storage ty base f) with
          | error e => rfl
          | ok p =>
              obtain ⟨r, sg⟩ := p
              simp only [readLoc_storage, writeLoc, bind, Except.bind]
              cases s.findStorage r sg with
              | error e => rfl
              | ok v =>
                  simp only []
                  cases SVal.asValue v with
                  | error e => rfl
                  | ok old =>
                      simp only []
                      cases Value.asInt old with
                      | error e => rfl
                      | ok n =>
                          simp only []
      | memory =>
          have hb : base.simple = true := by simpa [incDecTargetB] using ht
          rw [resolveLoc_memoryField s ty base f hb]
          simp only [incDecUpd, bind, Except.bind, Except.map]
          cases memBase s base with
          | error e => rfl
          | ok id =>
              simp only [readLoc_memoryField, writeLoc_memoryField]
              cases memFieldVal s id f.name with
              | error e => rfl
              | ok old =>
                  simp only []
                  cases Value.asInt old with
                  | error e => rfl
                  | ok n => simp only []
      | _ => exact absurd ht (by simp [incDecTargetB])
  | index k ty base ix =>
      cases k with
      | storage =>
          have hp : simplePathB (WrappedExpr.index Kind.storage ty base ix) = true := by
            simpa [incDecTargetB, simplePathB] using ht
          rw [resolveLoc_storageIndex s ty base ix hp]
          simp only [incDecUpd, locPath, bind, Except.bind, Except.map]
          cases placePath s (WrappedExpr.index Kind.storage ty base ix) with
          | error e => rfl
          | ok p =>
              obtain ⟨r, sg⟩ := p
              simp only [readLoc_storage, writeLoc, bind, Except.bind]
              cases s.findStorage r sg with
              | error e => rfl
              | ok v =>
                  simp only []
                  cases SVal.asValue v with
                  | error e => rfl
                  | ok old =>
                      simp only []
                      cases Value.asInt old with
                      | error e => rfl
                      | ok n =>
                          simp only []
      | memory =>
          have hbi : base.simple = true ∧ ix.simple = true := by
            simpa [incDecTargetB, Bool.and_eq_true] using ht
          rw [resolveLoc_memoryIndex s ty base ix hbi.1 hbi.2]
          simp only [incDecUpd, bind, Except.bind, Except.map]
          cases memBase s base with
          | error e => rfl
          | ok id =>
              simp only []
              cases simpleInt s ix with
              | error e => rfl
              | ok i =>
                  simp only [readLoc_memoryIndex, writeLoc_memoryIndex]
                  cases memIndexVal s id i with
                  | error e => rfl
                  | ok old =>
                      simp only []
                      cases Value.asInt old with
                      | error e => rfl
                      | ok n => simp only []
      | _ => exact absurd ht (by simp [incDecTargetB])
  | bool b => rw [resolveLoc_bool]; rfl
  | intLit ty v => rw [resolveLoc_intLit]; rfl
  | _ => exact absurd ht (by simp [incDecTargetB])

end Wp
end Solidity
