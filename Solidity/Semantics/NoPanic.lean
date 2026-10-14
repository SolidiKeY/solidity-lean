import Solidity.Semantics.Run

/-!
# Only an `assert` panics

`THalt.panic` is the halt no modality accepts, and the typed run raises it
in one place, a failed `assert` (`TRun.assert`).  Every other step halts
with `revert`, `exhausted` or `diverge`: an expression does not panic
(`Val.evalT_noPanic`, below), nor does a write, an
allocation, a call's entry or a `try`'s decoding.  So a program with no
`assert` in it (`Prog.asserts`, in a branch, a block, a loop or a called
body) never panics (`Prog.run_noPanic`), on every typed state, inside the
EVM fragment or not; master's statement over the untyped run, restated
over the typed one.

Each lemma follows its operation's definition, as `Semantics/Ends.lean`
does for `TRes.Ends`.
-/

namespace Solidity

variable {C : Contract}

/-! ## Typed results -/

/-- A typed result that does not panic (an expression's: it reverts or
diverges only). -/
def TRes.NoPanic {α : Type} (t : TRes α) : Prop := t ≠ .error .panic

theorem TRes.NoPanic.bind {α γ : Type} {t : TRes α} (h : t.NoPanic) {k : α → TRes γ}
    (hk : ∀ a, (k a).NoPanic) : (t >>= k).NoPanic := by
  match t with
  | .ok a => exact hk a
  | .error e => exact fun h' => h (by cases h'; rfl)

theorem TRes.NoPanic.ofOpt {α : Type} (x : Option α) : (TRes.ofOpt x).NoPanic := by
  cases x <;> exact fun h => nomatch h

/-! ## An expression does not panic -/

section Eval

variable {Γ : Ctx}

mutual

theorem SPath.resolveT_noPanic (σ : State C Γ) : {T : Ty} → (b : SPath C Γ T) →
    (b.resolveT σ).NoPanic
  | _, .alias i => by
    show (match (TEnv.get i σ.env : Option (SRef C _)) with
      | some r => .ok r
      | none => .error .revert : TRes _).NoPanic
    cases (TEnv.get i σ.env : Option (SRef C _)) <;> exact fun h => nomatch h
  | _, .loc l => l.resolveT_noPanic σ

theorem Loc.resolveT_noPanic (σ : State C Γ) : {T : Ty} → (l : Loc C Γ T) →
    (l.resolveT σ).NoPanic
  | _, .root .. => fun h => nomatch h
  | _, .field b _ _ => (b.resolveT_noPanic σ).bind fun _ => fun h => nomatch h
  | _, .index _ b i => (b.resolveT_noPanic σ).bind fun _ => (i.evalT_noPanic σ).bind fun _ =>
      (TRes.NoPanic.ofOpt _).bind fun _ => fun h => nomatch h

theorem MPath.mvalT_noPanic (σ : State C Γ) : {T : Ty} → (b : MPath C Γ T) →
    (b.mvalT σ).NoPanic
  | _, .var i _ => by
    show (match (TEnv.get i σ.env : Option (HRef σ.H _)) with
      | some r => .ok r
      | none => .error .revert : TRes _).NoPanic
    cases (TEnv.get i σ.env : Option (HRef σ.H _)) <;> exact fun h => nomatch h
  | _, .loc l => (l.addrT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _

theorem MLoc.addrT_noPanic (σ : State C Γ) : {T : Ty} → (l : MLoc C Γ T) →
    (l.addrT σ).NoPanic
  | _, .field b _ _ => (b.mvalT_noPanic σ).bind fun _ => fun h => nomatch h
  | _, .index _ b i => (b.mvalT_noPanic σ).bind fun _ => (i.evalT_noPanic σ).bind fun _ =>
      fun h => nomatch h

theorem Val.evalT_noPanic (σ : State C Γ) : {p : PrimTy} → (v : Val C Γ p) →
    (v.evalT σ).NoPanic
  | _, .simple _ => fun h => nomatch h
  | _, .read l => (l.resolveT_noPanic σ).bind fun _ => (TRes.NoPanic.ofOpt _).bind fun _ =>
      fun h => nomatch h
  | _, .binop op _ hq a b => by
    subst hq
    refine (a.evalT_noPanic σ).bind fun x => ?_
    show (match op.shortT x with
      | some y => pure y
      | none => do
        let y ← b.evalT σ
        TRes.ofOpt (op.evalT _ x y) : TRes _).NoPanic
    cases op.shortT x with
    | some _ => exact fun h => nomatch h
    | none => exact (b.evalT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _
  | _, .unop op _ hq a => by
    subst hq
    exact (a.evalT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _
  | _, .ternary c a b => (c.evalT_noPanic σ).bind fun x => by
    cases x
    · exact b.evalT_noPanic σ
    · exact a.evalT_noPanic σ
  | _, .readMem l => (l.addrT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _
  | _, .len b hp => by
    subst hp
    exact (b.resolveT_noPanic σ).bind fun _ => (TRes.NoPanic.ofOpt _).bind fun _ =>
      fun h => nomatch h
  | _, .mlen b hp => by
    subst hp
    exact (b.mvalT_noPanic σ).bind fun _ => fun h => nomatch h

end

theorem Src.valueT_noPanic (σ : State C Γ) {T : Ty} (r : Src C Γ T) : (r.valueT σ).NoPanic := by
  cases r with
  | val v => exact (v.evalT_noPanic σ).bind fun _ => fun h => nomatch h
  | copy p _ => exact (p.resolveT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _

end Eval

/-! ## Assertions -/

mutual
/-- Whether a statement has an `assert` (in a branch, a block, a loop or a
called body): only those panic. -/
def Stmt.asserts {Γ Γ' : Ctx} : Stmt C Γ Γ' → Bool
  | .assert _ => true
  | .ite _ t e => Prog.asserts t || Prog.asserts e
  | .block body => Prog.asserts body
  | .call _ _ _ body => Prog.asserts body
  | .tryCall _ _ ok err _ pnc other =>
    Prog.asserts ok || Prog.asserts err || Prog.asserts pnc || Prog.asserts other
  | .loop _ _ body => Prog.asserts body
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign ..
  | .incDec .. | .assignIncDec .. | .assignLocalPush .. | .push .. | .pop _ | .transfer ..
  | .send .. | .declMem ..
  | .rebindMem .. | .assignFromMem .. | .assignMem .. | .delete _ | .deleteMem .. | .assignNew ..
  | .require _ | .revert => false
/-- Whether a sequence has an `assert`. -/
def Prog.asserts {Γ Γ' : Ctx} : Prog C Γ Γ' → Bool
  | .nil => false
  | .cons s P => Stmt.asserts s || Prog.asserts P
end

/-! ## Results that do not panic -/

theorem TRes.NoPanic.ok {α : Type} (a : α) : TRes.NoPanic (Except.ok a : TRes α) :=
  fun h => nomatch h

theorem TRes.NoPanic.revert {α : Type} : TRes.NoPanic (Except.error .revert : TRes α) :=
  fun h => nomatch h

theorem TRes.NoPanic.exhausted {α : Type} : TRes.NoPanic (Except.error .exhausted : TRes α) :=
  fun h => nomatch h

theorem TRes.NoPanic.diverge {α : Type} : TRes.NoPanic (Except.error .diverge : TRes α) :=
  fun h => nomatch h

theorem TRes.NoPanic.map {α γ : Type} {t : TRes α} (h : t.NoPanic) (k : α → γ) :
    TRes.NoPanic (t.map k) := by
  match t with
  | .ok _ => exact fun h' => nomatch h'
  | .error e => exact fun h' => h (by cases (h' : Except.error e = .error .panic); rfl)

/-- A loop whose body and condition do not panic does not: it ends as an
iteration does, or diverges. -/
theorem TLoop.iterN_noPanic {α : Type} {body : α → TRes α} {c : α → TRes Bool}
    (hb : ∀ a, (body a).NoPanic) (hc : ∀ a, (c a).NoPanic) :
    ∀ (n : Nat) (σ : α) {r : TRes α}, TLoop.iterN body c n σ = .inr r → r.NoPanic
  | 0, _, _, h => nomatch h
  | n + 1, σ, r, h => by
    simp only [TLoop.iterN] at h
    split at h
    · exact TLoop.iterN_noPanic hb hc n _ h
    · rename_i r' hs
      cases h
      unfold TLoop.step at hs
      split at hs
      · rename_i e he
        cases hs
        exact fun h' => hc σ (by cases h'; exact he)
      · cases hs; exact TRes.NoPanic.ok _
      · split at hs
        · rename_i e he
          cases hs
          exact fun h' => hb σ (by cases h'; exact he)
        · cases hs

theorem TLoop.run_noPanic {α : Type} {body : α → TRes α} {c : α → TRes Bool}
    (hb : ∀ a, (body a).NoPanic) (hc : ∀ a, (c a).NoPanic) (σ : α) :
    (TLoop.run body c σ).NoPanic := by
  unfold TLoop.run
  split
  · rename_i h
    obtain ⟨n, hn⟩ := Classical.choose_spec h
    exact TLoop.iterN_noPanic hb hc n σ hn
  · exact TRes.NoPanic.diverge

/-! ## Operations do not panic -/

section Ops

variable {Γ : Ctx} (σ : State C Γ)

/-- `Calculus/SoundMem.lean`'s `MSrc.mvalT_noPanic`, below it. -/
private theorem MSrc.mvalT_noPanic' {T : Ty} : (r : MSrc C Γ T) → (r.mvalT σ).NoPanic
  | .val v => v.evalT_noPanic σ
  | .ref p => p.mvalT_noPanic σ

theorem ARhs.evalT_noPanic {R : RefTy} : (r : ARhs C Γ R) → (r.evalT σ).NoPanic
  | .path p => (p.resolveT_noPanic σ).bind fun _ => TRes.NoPanic.ok _
  | .push b _ => (b.resolveT_noPanic σ).bind fun r => by
    show (if σ.storage.full r then .error .exhausted else do
      let (st, n) ← TRes.ofOpt (σ.storage.pushPlace r)
      pure (st, r.index (.arr .dyn) n) : TRes _).NoPanic
    split
    · exact TRes.NoPanic.exhausted
    · exact (TRes.NoPanic.ofOpt _).bind fun _ => TRes.NoPanic.ok _

theorem MRhs.evalT_noPanic {R : RefTy} : (r : MRhs C Γ R) → (r.evalT σ).NoPanic
  | .alias p => (p.mvalT_noPanic σ).bind fun _ => TRes.NoPanic.ok _
  | .copy p _ => (p.resolveT_noPanic σ).bind fun _ => (TRes.NoPanic.ofOpt _).bind fun _ =>
      TRes.NoPanic.ok _
  | .newArr .. => TRes.NoPanic.ok _

theorem opStoreT_noPanic (op : BinOp) {p : PrimTy} (r : SRef C (.prim p)) (v : p.Denote) :
    (opStoreT σ op r v).NoPanic :=
  (TRes.NoPanic.ofOpt _).bind fun _ => (TRes.NoPanic.ofOpt _).bind fun _ =>
    (TRes.NoPanic.ofOpt _).bind fun _ => TRes.NoPanic.ok _

theorem opMemT_noPanic (op : BinOp) {p : PrimTy} (a : MAddr σ.H (.prim p)) (v : p.Denote) :
    (opMemT σ op a v).NoPanic :=
  (TRes.NoPanic.ofOpt _).bind fun _ => (TRes.NoPanic.ofOpt _).bind fun _ =>
    (TRes.NoPanic.ofOpt _).bind fun _ => TRes.NoPanic.ok _

theorem OpLoc.storeT_noPanic (op : BinOp) {p : PrimTy} : (l : OpLoc C Γ p) → (v : p.Denote) →
    (l.storeT σ op v).NoPanic
  | .local _, _ => (TRes.NoPanic.ofOpt _).bind fun _ => TRes.NoPanic.ok _
  | .root .., _ => opStoreT_noPanic σ op _ _
  | .field .., _ => (Loc.resolveT_noPanic σ _).bind fun _ => opStoreT_noPanic σ op _ _
  | .index .., _ => (Loc.resolveT_noPanic σ _).bind fun _ => opStoreT_noPanic σ op _ _
  | .mfield .., _ => (MLoc.addrT_noPanic σ _).bind fun _ => opMemT_noPanic σ op _ _
  | .mindex .., _ => (MLoc.addrT_noPanic σ _).bind fun _ => opMemT_noPanic σ op _ _

theorem bumpStoreT_noPanic (op : IncDec) {p : PrimTy} (r : SRef C (.prim p)) :
    (bumpStoreT σ op r).NoPanic :=
  (TRes.NoPanic.ofOpt _).bind fun _ => (TRes.NoPanic.ofOpt _).bind fun _ =>
    (TRes.NoPanic.ofOpt _).bind fun _ => TRes.NoPanic.ok _

theorem bumpMemT_noPanic (op : IncDec) {p : PrimTy} (a : MAddr σ.H (.prim p)) :
    (bumpMemT σ op a).NoPanic :=
  (TRes.NoPanic.ofOpt _).bind fun _ => (TRes.NoPanic.ofOpt _).bind fun _ =>
    (TRes.NoPanic.ofOpt _).bind fun _ => TRes.NoPanic.ok _

theorem OpLoc.bumpT_noPanic (op : IncDec) {p : PrimTy} : (l : OpLoc C Γ p) →
    (l.bumpT σ op).NoPanic
  | .local _ => (TRes.NoPanic.ofOpt _).bind fun _ => TRes.NoPanic.ok _
  | .root .. => bumpStoreT_noPanic σ op _
  | .field .. => (Loc.resolveT_noPanic σ _).bind fun _ => bumpStoreT_noPanic σ op _
  | .index .. => (Loc.resolveT_noPanic σ _).bind fun _ => bumpStoreT_noPanic σ op _
  | .mfield .. => (MLoc.addrT_noPanic σ _).bind fun _ => bumpMemT_noPanic σ op _
  | .mindex .. => (MLoc.addrT_noPanic σ _).bind fun _ => bumpMemT_noPanic σ op _

theorem Args.evalT_noPanic : {ps : Ctx} → (as : Args C Γ ps) → (as.evalT σ).NoPanic
  | _, .nil => TRes.NoPanic.ok _
  | _, .snoc as _ _ e => (Args.evalT_noPanic as).bind fun _ => (e.evalT_noPanic σ).bind fun _ =>
      TRes.NoPanic.ok _

end Ops

theorem Binders.decodeT_noPanic {H : HTy} : {ρ : Ctx} → (bs : Binders ρ) →
    (vs : List Semantics.Word) → (Binders.decodeT (C := C) (H := H) bs vs).NoPanic
  | _, .nil, _ => TRes.NoPanic.ok _
  | _, .snoc bs p _, vs => (Binders.decodeT_noPanic bs vs).bind fun (_, rest) => by
    dsimp only
    split
    · split
      · exact TRes.NoPanic.ok _
      · exact TRes.NoPanic.revert
    · exact TRes.NoPanic.revert

/-! ## Steps do not panic

Each step of `TRun` but `assert`, its sub-steps assumed not to panic. -/

namespace TRun

variable {Γ : Ctx}

theorem push_noPanic {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    (σ : State C Γ) : (push b v σ).NoPanic := by
  unfold push
  refine (b.resolveT_noPanic σ).bind fun ref => ?_
  cases v with
  | none =>
    dsimp only
    split
    · exact TRes.NoPanic.exhausted
    · exact (TRes.NoPanic.ofOpt _).bind fun _ => TRes.NoPanic.ok _
  | some r =>
    refine (r.valueT_noPanic σ).bind fun _ => ?_
    dsimp only
    split
    · exact TRes.NoPanic.exhausted
    · exact (TRes.NoPanic.ofOpt _).bind fun _ => TRes.NoPanic.ok _

theorem clearT_noPanic (σ : State C Γ) : {T : Ty} → (a : MAddr σ.H T) →
    (hm : T.mapFree = true) → (clearT σ a hm).NoPanic
  | .prim _, _, _ => (TRes.NoPanic.ofOpt _).bind fun _ => TRes.NoPanic.ok _
  | .ref R, a, hm => by
    simp only [clearT]
    split
    · exact TRes.NoPanic.ok _
    · exact TRes.NoPanic.revert

theorem deleteMem_noPanic {T : Ty} (p : MPath C Γ T) (σ : State C Γ) :
    (deleteMem p σ).NoPanic := by
  unfold deleteMem
  cases p with
  | var _ _ => exact TRes.NoPanic.ok _
  | loc l => exact (l.addrT_noPanic σ).bind fun a => clearT_noPanic σ a l.mapFree

theorem assignNew_noPanic {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (h : R.newArrOk = true) (σ : State C Γ) : (assignNew l n h σ).NoPanic := by
  unfold assignNew
  cases l with
  | store l => exact (l.resolveT_noPanic _).bind fun _ => (TRes.NoPanic.ofOpt _).bind fun _ =>
      TRes.NoPanic.ok _
  | mem l => exact (l.addrT_noPanic _).bind fun _ => (TRes.NoPanic.ofOpt _).bind fun _ =>
      TRes.NoPanic.ok _

theorem ite_noPanic {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁) (thn : TStep C Γ Γ₁)
    (h₂ : Ext Γ Γ₂) (els : TStep C Γ Γ₂) (ht : ∀ σ, (thn σ).NoPanic)
    (he : ∀ σ, (els σ).NoPanic) (σ : State C Γ) : (ite c h₁ thn h₂ els σ).NoPanic := by
  unfold ite
  refine (c.evalT_noPanic σ).bind fun v => ?_
  split
  · exact (ht σ).map _
  · exact (he σ).map _

theorem require_noPanic (c : Val C Γ .bool) (σ : State C Γ) : (require c σ).NoPanic := by
  unfold require
  refine (c.evalT_noPanic σ).bind fun v => ?_
  split
  · exact TRes.NoPanic.ok _
  · exact TRes.NoPanic.revert

theorem call_noPanic {Γ' ps rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (hb : Ext (rs ++ ps) Γf) (body : TStep C (rs ++ ps) Γf) (hbody : ∀ σ, (body σ).NoPanic)
    (σ : State C Γ) : (call args ret hb body σ).NoPanic := by
  unfold call
  exact (Args.evalT_noPanic σ args).bind fun _ => (hbody _).bind fun _ => TRes.NoPanic.ok _

theorem tryCall_noPanic {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (c : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : TStep C (ρ ++ Γ) Γ₁)
    (h₂ : Ext Γ Γ₂) (err : TStep C Γ Γ₂) (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : TStep C (κ ++ Γ) Γ₃)
    (h₄ : Ext Γ Γ₄) (other : TStep C Γ Γ₄) (hok : ∀ σ, (ok σ).NoPanic)
    (herr : ∀ σ, (err σ).NoPanic) (hpnc : ∀ σ, (pnc σ).NoPanic)
    (hother : ∀ σ, (other σ).NoPanic) (σ : State C Γ) :
    (tryCall c rets h₁ ok h₂ err code h₃ pnc h₄ other σ).NoPanic := by
  unfold tryCall
  split
  · exact TRes.NoPanic.revert
  · exact (Binders.decodeT_noPanic rets _).bind fun _ => (hok _).map _
  · exact (herr σ).map _
  · exact (hpnc _).map _
  · exact (hother σ).map _

theorem loop_noPanic {Γ₁ : Ctx} (c : Val C Γ .bool) (h : Ext Γ Γ₁) (body : TStep C Γ Γ₁)
    (hbody : ∀ σ, (body σ).NoPanic) (σ : State C Γ) : (loop c h body σ).NoPanic := by
  unfold loop
  exact TLoop.run_noPanic (fun o : Out C σ.H Γ => (hbody o.st).map _)
    (fun o : Out C σ.H Γ => c.evalT_noPanic o.st) _

theorem block_noPanic {Γ₁ : Ctx} (h : Ext Γ Γ₁) (body : TStep C Γ Γ₁)
    (hbody : ∀ σ, (body σ).NoPanic) (σ : State C Γ) : (block h body σ).NoPanic :=
  (hbody σ).map _

theorem seq_noPanic {Γ₁ Γ₂ : Ctx} (s : TStep C Γ Γ₁) (P : TStep C Γ₁ Γ₂)
    (hs : ∀ σ, (s σ).NoPanic) (hP : ∀ σ, (P σ).NoPanic) (σ : State C Γ) :
    (seq s P σ).NoPanic := by
  unfold seq
  split
  · exact (hP _).map _
  · rename_i e he
    exact fun h' => hs σ (by cases h'; exact he)

end TRun

/-! ## A program with no `assert` -/

mutual

/-- **Only an `assert` panics**: a statement with none in it never ends in
`panic`. -/
theorem Stmt.run_noPanic : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → s.asserts = false →
    ∀ σ : State C Γ, (s.run σ).NoPanic
  | _, _, .assign l r, _, σ => (r.valueT_noPanic σ).bind fun _ => (l.resolveT_noPanic σ).bind
      fun _ => (TRes.NoPanic.ofOpt _).bind fun _ => TRes.NoPanic.ok _
  | _, _, .rebind _ r, _, σ => (r.evalT_noPanic σ).bind fun _ => TRes.NoPanic.ok _
  | _, _, .assignLocal _ r, _, σ => (r.evalT_noPanic σ).bind fun _ => TRes.NoPanic.ok _
  | _, _, .declLocal p _ init, _, σ => by
    cases init with
    | none => exact TRes.NoPanic.ok _
    | some e => exact (e.evalT_noPanic σ).bind fun _ => TRes.NoPanic.ok _
  | _, _, .declStorage R _ init, _, σ => by
    cases init with
    | none => exact TRes.NoPanic.ok _
    | some r => exact (r.evalT_noPanic σ).bind fun _ => TRes.NoPanic.ok _
  | _, _, .opAssign op _ _ l r, _, σ => (r.evalT_noPanic σ).bind fun _ =>
      OpLoc.storeT_noPanic σ op l _
  | _, _, .incDec op _ l, _, σ => (OpLoc.bumpT_noPanic σ op l).bind fun _ => TRes.NoPanic.ok _
  | _, _, .assignIncDec _ op _ l _, _, σ => (OpLoc.bumpT_noPanic σ op l).bind fun _ =>
      TRes.NoPanic.ok _
  | _, _, .assignLocalPush i b _, _, σ => (TRun.push_noPanic b none σ).bind fun _ =>
      TRes.NoPanic.ok _
  | _, _, .push b v _, _, σ => TRun.push_noPanic b v σ
  | _, _, .pop b, _, σ => (b.resolveT_noPanic σ).bind fun _ => (TRes.NoPanic.ofOpt _).bind
      fun _ => TRes.NoPanic.ok _
  | _, _, .transfer r a, _, σ => (r.evalT_noPanic σ).bind fun _ => (a.evalT_noPanic σ).bind
      fun _ => TRes.NoPanic.ok _
  | _, _, .send _ r a, _, σ => (r.evalT_noPanic σ).bind fun _ => (a.evalT_noPanic σ).bind
      fun _ => TRes.NoPanic.ok _
  | _, _, .declMem R _ init _ _, _, σ => by
    cases init with
    | none => exact TRes.NoPanic.ok _
    | some r => exact (r.evalT_noPanic σ).bind fun _ => TRes.NoPanic.ok _
  | _, _, .rebindMem _ r, _, σ => (r.evalT_noPanic σ).bind fun _ => TRes.NoPanic.ok _
  | _, _, .assignFromMem l p, _, σ => (p.mvalT_noPanic σ).bind fun _ =>
      (l.resolveT_noPanic σ).bind fun _ => (TRes.NoPanic.ofOpt _).bind fun _ => TRes.NoPanic.ok _
  | _, _, .assignMem l r, _, σ => (MSrc.mvalT_noPanic' σ r).bind fun _ => (l.addrT_noPanic σ).bind
      fun _ => (TRes.NoPanic.ofOpt _).bind fun _ => TRes.NoPanic.ok _
  | _, _, .delete l, _, σ => (l.resolveT_noPanic σ).bind fun _ => (TRes.NoPanic.ofOpt _).bind
      fun _ => TRes.NoPanic.ok _
  | _, _, .deleteMem p _, _, σ => TRun.deleteMem_noPanic p σ
  | _, _, .assignNew l n h, _, σ => TRun.assignNew_noPanic l n h σ
  | _, _, .ite c thn els, h, σ => by
    simp only [Stmt.asserts, Bool.or_eq_false_iff] at h
    exact TRun.ite_noPanic c _ _ _ _ (Prog.run_noPanic thn h.1) (Prog.run_noPanic els h.2) σ
  | _, _, .require c, _, σ => TRun.require_noPanic c σ
  | _, _, .assert _, h, _ => nomatch h
  | _, _, .revert, _, _ => TRes.NoPanic.revert
  | _, _, .call _ args ret body, h, σ => by
    simp only [Stmt.asserts] at h
    exact TRun.call_noPanic args ret _ _ (Prog.run_noPanic body h) σ
  | _, _, .tryCall call rets ok err code pnc other, h, σ => by
    simp only [Stmt.asserts, Bool.or_eq_false_iff] at h
    obtain ⟨⟨⟨hok, herr⟩, hpnc⟩, hother⟩ := h
    exact TRun.tryCall_noPanic call rets _ _ _ _ code _ _ _ _ (Prog.run_noPanic ok hok)
      (Prog.run_noPanic err herr) (Prog.run_noPanic pnc hpnc) (Prog.run_noPanic other hother) σ
  | _, _, .loop _ c body, h, σ => by
    simp only [Stmt.asserts] at h
    exact TRun.loop_noPanic c _ _ (Prog.run_noPanic body h) σ
  | _, _, .block body, h, σ => by
    simp only [Stmt.asserts] at h
    exact TRun.block_noPanic _ _ (Prog.run_noPanic body h) σ

/-- **Only an `assert` panics**: a sequence with none in it never ends in
`panic`, from any typed state. -/
theorem Prog.run_noPanic : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → P.asserts = false →
    ∀ σ : State C Γ, (P.run σ).NoPanic
  | _, _, .nil, _, _ => TRes.NoPanic.ok _
  | _, _, .cons s P, h, σ => by
    simp only [Prog.asserts, Bool.or_eq_false_iff] at h
    exact TRun.seq_noPanic _ _ (Stmt.run_noPanic s h.1) (Prog.run_noPanic P h.2) σ

end

/-- `Prog.run_noPanic`, its result spelled out. -/
theorem Prog.run_ne_panic {Γ Γ' : Ctx} {P : Prog C Γ Γ'} (h : P.asserts = false)
    (σ : State C Γ) : P.run σ ≠ .error .panic :=
  Prog.run_noPanic P h σ

end Solidity
