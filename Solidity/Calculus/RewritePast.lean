import Solidity.Calculus.RewriteScoped

/-!
# Rewrites of a scoped line past the program

The rewrites a chain takes once its program is done, on the scoped line
(`Fml C Γ`), where `Calculus/RewriteScoped.lean`'s stop: the line the
strategy leaves past a declaration keeps a hidden binder between two
updates, a merge leaves a storage write the next one shadows, a capture
stays declared after its scope ended.  Each rewrite is a `FmlRw`, sound one
way (`holds σ ψ → holds σ φ`).

| `FmlRw` | line before ⇝ line after | sound by | solkey |
|---|---|---|---|
| `mergePast k n` | the `n + 1` updates from position `k` merged into one, through hidden binders (`Fml.merge2P`), over a storage or memory write, a shadowed state write dropped (`Upd.dropSh`) | `Fml.mergeRunP_sound` | `sequentialToParallel1-3` |

**A hidden binder absorbed.**  `bind x ({x := e ‖ U} φ)`, `e` and `U` not
reading `x`, is `{x :=decl e ‖ U} φ` (`Upd.absorb`, `holds_bind_absorb`):
the binder reads every value of `x`, and the update overwrites it before
anything reads it.  Decision 101's merge across a hidden binder: the
binder's local declared by the update, the two updates then merge as any
two do.  An update of locals only moves under the binder instead
(`Upd.lift?`, `Calculus/Merge.lean`), where it declares nothing.

**A shadowed state write.**  `{… ‖ storage := S ‖ … ‖ storage := T ‖ …}`,
`S` read before anything else of `T` (`Tm.onSpineS`), is the update without
`storage := S` (`Upd.dropSh`): no element reads the state it writes into
but the ledger, `T` writes the storage over `S`'s, and `T` halts where `S`
does.  So for memory writes (`Tm.onMemSpineS`).  The erased merge drops a
storage write so (`Surface.Upd.mergeStL`, `Surface.Upd.dropStorage_holds`).

These functions run once a link and use `match` on the indexed families,
under the exemption of `Calculus/RewriteScoped.lean`'s walks (proposal 104).
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)
open Semantics (Res)

variable {C : Contract}

/-! ## Out of the top local's scope -/

section Down

variable {Γ : Ctx} {u : LTy}

/-- A position of `u :: Γ` read in `Γ`: none for the top one. -/
def Idx.down? {t : LTy} : Idx (u :: Γ) t → Option (Idx Γ t)
  | .here => none
  | .there j => some j

/-- A term of `u :: Γ` read in `Γ`, where it does not read the top local. -/
def Tm.down? : {s : Srt} → Tm C (u :: Γ) s → Option (Tm C Γ s)
  | _, .pvV i => i.down?.map .pvV
  | _, .pvP i => i.down?.map .pvP
  | _, .pvS i => i.down?.map .pvS
  | _, .pvI i => i.down?.map .pvI
  | _, .netOf i a => do pure (.netOf (← i.down?) (← Tm.down? a))
  | _, .app0 o => some (.app0 o)
  | _, .app1 o ho x => (Tm.down? x).map (.app1 o ho)
  | _, .app2 o x y => do pure (.app2 o (← Tm.down? x) (← Tm.down? y))
  | _, .app3 o x y z => do pure (.app3 o (← Tm.down? x) (← Tm.down? y) (← Tm.down? z))

/-- A right-hand side of `u :: Γ` read in `Γ`. -/
def Rhs.down? : {t : LTy} → Rhs C (u :: Γ) t → Option (Rhs C Γ t)
  | _, .val t => t.down?.map .val
  | _, .path p => p.down?.map .path
  | _, .unset => some .unset
  | _, .mref i => i.down?.map .mref
  | _, .store s => s.down?.map .store
  | _, .saveNet => some .saveNet
  | _, .saveNetMt => some .saveNetMt

/-- An element whose right-hand sides are read in `u :: Γ`, read in `Γ`. -/
def UpdElem.down? {Δ : Ctx} : UpdElem C (u :: Γ) Δ → Option (UpdElem C Γ Δ)
  | .local i r => r.down?.map (.local i)
  | .storage s => s.down?.map .storage
  | .memory m => m.down?.map .memory
  | .selfBalance op a => a.down?.map (.selfBalance op)
  | .net r op a => do pure (.net (← r.down?) op (← a.down?))
  | .pay r a => do pure (.pay (← r.down?) (← a.down?))
  | .netMt r a => do pure (.netMt (← r.down?) (← a.down?))
  | .setBalance a => a.down?.map .setBalance

theorem Idx.down?_get {t : LTy} : (i : Idx (u :: Γ) t) → {j : Idx Γ t} → i.down? = some j →
    ∀ (v : u.Denote C) (e : Env C Γ), Env.get i ((v, e) : Env C (u :: Γ)) = Env.get j e
  | .there _, _, h, _, _ => by cases h; rfl

/-- **A term that does not read the top local reads alike below it.** -/
theorem Tm.eval_down? (σ : EState C Γ) (v : u.Denote C) :
    {s : Srt} → (t : Tm C (u :: Γ) s) → {t' : Tm C Γ s} → t.down? = some t' →
      t'.eval σ = t.eval (σ.push v)
  | _, .pvV i, _, h => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 h
    show pure (Env.get j σ.env) = pure (Env.get i (v, σ.env))
    rw [Idx.down?_get i hj]
  | _, .pvP i, _, h => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 h
    show aliasPath σ j = aliasPath (σ.push v) i
    simp only [aliasPath, EState.push, EState.withEnv, Idx.down?_get i hj]
  | _, .pvS i, _, h => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 h
    show pure { σ.glob with storage := Env.get j σ.env } =
      pure { (σ.push v).glob with storage := Env.get i (v, σ.env) }
    rw [Idx.down?_get i hj]; rfl
  | _, .pvI i, _, h => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 h
    show memRef σ j = memRef (σ.push v) i
    simp only [memRef, EState.push, EState.withEnv, Idx.down?_get i hj]
  | _, .netOf i a, _, h => by
    obtain ⟨j, hj, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show (do
        let l : List (Int × Int) := Env.get j σ.env
        pure (Semantics.Value.int ((Semantics.lookupBy (← (← a'.eval σ).asInt) l).getD 0))) =
      (do
        let l : List (Int × Int) := Env.get i (v, σ.env)
        pure (Semantics.Value.int ((Semantics.lookupBy (← (← a.eval (σ.push v)).asInt) l).getD 0)))
    rw [Idx.down?_get i hj, Tm.eval_down? σ v a ha]
  | _, .app0 _, _, h => by cases h; rfl
  | _, .app1 o ho x, _, h => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show o.eval σ.glob (x'.eval σ) = o.eval (σ.push v).glob (x.eval (σ.push v))
    rw [Tm.eval_down? σ v x hx]; rfl
  | _, .app2 o x y, _, h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.eval σ.glob (x'.eval σ) (y'.eval σ) =
      o.eval (σ.push v).glob (x.eval (σ.push v)) (y.eval (σ.push v))
    rw [Tm.eval_down? σ v x hx, Tm.eval_down? σ v y hy]; rfl
  | _, .app3 o x y z, _, h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.eval σ.glob (x'.eval σ) (y'.eval σ) (z'.eval σ) =
      o.eval (σ.push v).glob (x.eval (σ.push v)) (y.eval (σ.push v)) (z.eval (σ.push v))
    rw [Tm.eval_down? σ v x hx, Tm.eval_down? σ v y hy, Tm.eval_down? σ v z hz]; rfl

theorem Rhs.eval_down? (σ : EState C Γ) (v : u.Denote C) :
    {t : LTy} → (r : Rhs C (u :: Γ) t) → {r' : Rhs C Γ t} → r.down? = some r' →
      r'.eval σ = r.eval (σ.push v)
  | _, .val t, _, h => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Tm.eval_down? σ v t ht
  | _, .path p, _, h => by
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.1 h
    show (do pure (some (← p'.eval σ))) = (do pure (some (← p.eval (σ.push v))))
    rw [Tm.eval_down? σ v p hp]
  | _, .unset, _, h => by cases h; rfl
  | _, .mref i, _, h => by
    obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.1 h
    show (do pure (some (← i'.eval σ))) = (do pure (some (← i.eval (σ.push v))))
    rw [Tm.eval_down? σ v i hi]
  | _, .store s, _, h => by
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 h
    show (do pure (← s'.eval σ).storage) = (do pure (← s.eval (σ.push v)).storage)
    rw [Tm.eval_down? σ v s hs]
  | _, .saveNet, _, h => by cases h; rfl
  | _, .saveNetMt, _, h => by cases h; rfl

theorem UpdElem.write_down? {Δ : Ctx} (σ : EState C Γ) (v : u.Denote C) :
    (e : UpdElem C (u :: Γ) Δ) → {e' : UpdElem C Γ Δ} → e.down? = some e' →
      ∀ τ, e'.write σ τ = e.write (σ.push v) τ
  | .local i r, _, h, τ => by
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.write, Rhs.eval_down? σ v r hr]
  | .storage s, _, h, τ => by
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.write, Tm.eval_down? σ v s hs]
  | .memory m, _, h, τ => by
    obtain ⟨m', hm, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.write, Tm.eval_down? σ v m hm]
  | .selfBalance op a, _, h, τ => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.write, Tm.eval_down? σ v a ha]; rfl
  | .net r op a, _, h, τ => by
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [UpdElem.write, Tm.eval_down? σ v r hr, Tm.eval_down? σ v a ha]
  | .pay r a, _, h, τ => by
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [UpdElem.write, Tm.eval_down? σ v r hr, Tm.eval_down? σ v a ha]; rfl
  | .netMt r a, _, h, τ => by
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [UpdElem.write, Tm.eval_down? σ v r hr, Tm.eval_down? σ v a ha]
  | .setBalance a, _, h, τ => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.write, Tm.eval_down? σ v a ha]

end Down

/-! ## A hidden binder absorbed -/

section Absorb

variable {Γ : Ctx} {u : LTy}

/-- The first element of an absorbed update: `x := r`, `x` the binder's local. -/
def UpdElem.absorbHead (x : Var) : UpdElem C (u :: Γ) (u :: Γ) → Option (Upd C Γ (u :: Γ))
  | .local i r => match i, r with
    | .here, r => r.down?.map (.decl .nil x)
    | .there _, _ => none
  | _ => none

/-- `{V ‖ e}` absorbed, from `V` absorbed (`rec`): `e` alone on nothing is
the head. -/
def Upd.absorbSnoc (x : Var) : {Δ : Ctx} → Upd C (u :: Γ) Δ → UpdElem C (u :: Γ) Δ →
    Option (Upd C Γ Δ) → Option (Upd C Γ Δ)
  | _, .nil, e, _ => e.absorbHead x
  | _, .snoc .., e, rec | _, .decl .., e, rec | _, .pop .., e, rec | _, .drop .., e, rec => do
    pure (.snoc (← rec) (← e.down?))

/-- An update applied below a hidden binder of `x : u`, whose first element
sets `x` and which reads `x` nowhere: the update from above the binder, `x`
declared by its first element (`bind x ({x := e ‖ U} φ) ⇝ {x :=decl e ‖ U} φ`). -/
def Upd.absorb (x : Var) : {Δ : Ctx} → Upd C (u :: Γ) Δ → Option (Upd C Γ Δ)
  | _, .nil => none
  | _, .snoc V e => Upd.absorbSnoc x V e (Upd.absorb x V)
  | _, .decl V y r => do pure (.decl (← Upd.absorb x V) y (← r.down?))
  | _, .pop V h => (Upd.absorb x V).map (.pop · h)
  | _, .drop V h => (Upd.absorb x V).map (.drop · h)

theorem UpdElem.apply_absorbHead (x : Var) (σ : EState C Γ) (v : u.Denote C) :
    (e : UpdElem C (u :: Γ) (u :: Γ)) → {V' : Upd C Γ (u :: Γ)} → e.absorbHead x = some V' →
      V'.apply σ = (Upd.snoc .nil e).apply (σ.push v)
  | .local .here r, _, h => by
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    show (do let τ ← pure σ; pure (τ.push (← r'.eval σ))) =
      (do let τ ← pure (σ.push v); pure (τ.setLocal .here (← r.eval (σ.push v))))
    rw [Rhs.eval_down? σ v r hr]
    cases r.eval (σ.push v) <;> rfl
  | .local (.there _) _, _, h => by cases h
  | .storage _, _, h | .memory _, _, h | .selfBalance .., _, h | .net .., _, h | .pay .., _, h
  | .netMt .., _, h | .setBalance _, _, h => by cases h

/-- **The absorbed update runs from the state above the binder as the update
from any value of the binder's local.** -/
theorem Upd.apply_absorb (x : Var) (σ : EState C Γ) (v : u.Denote C) :
    {Δ : Ctx} → (V : Upd C (u :: Γ) Δ) → {V' : Upd C Γ Δ} → V.absorb x = some V' →
      V'.apply σ = V.apply (σ.push v)
  | _, .nil, _, h => by cases h
  | _, .snoc V e, V', h => by
    have hs : ∀ {Δ : Ctx} (V : Upd C (u :: Γ) Δ) (e : UpdElem C (u :: Γ) Δ) {W' : Upd C Γ Δ},
        (∀ {W : Upd C Γ Δ}, V.absorb x = some W → W.apply σ = V.apply (σ.push v)) →
        Upd.absorbSnoc x V e (V.absorb x) = some W' → W'.apply σ = (Upd.snoc V e).apply (σ.push v) := by
      intro Δ V e W' ih h
      cases V
      case nil => exact UpdElem.apply_absorbHead x σ v e h
      all_goals
        obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
        cases h
        show (do e'.write σ (← W.apply σ)) = (do e.write (σ.push v) (← Upd.apply (σ.push v) _))
        rw [ih hW]
        cases Upd.apply (σ.push v) _ with
        | error => rfl
        | ok τ => exact UpdElem.write_down? σ v e he τ
    exact hs V e (fun hW => Upd.apply_absorb x σ v V hW) h
  | _, .decl V y r, _, h => by
    obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show (do let τ ← W.apply σ; pure (τ.push (← r'.eval σ))) =
      (do let τ ← V.apply (σ.push v); pure (τ.push (← r.eval (σ.push v))))
    rw [Upd.apply_absorb x σ v V hW, Rhs.eval_down? σ v r hr]
  | _, .pop V hp, _, h => by
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
    show (W.apply σ).map _ = (V.apply (σ.push v)).map _
    rw [Upd.apply_absorb x σ v V hW]
  | _, .drop V hp, _, h => by
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
    show (W.apply σ).map _ = (V.apply (σ.push v)).map _
    rw [Upd.apply_absorb x σ v V hW]

/-- **`bind x ({x := e ‖ U} φ)` from `{x :=decl e ‖ U} φ`.** -/
theorem holds_bind_absorb {m m' : Modality} {x : Var} {Δ : Ctx} {V : Upd C (u :: Γ) Δ}
    {V' : Upd C Γ Δ} (hV : V.absorb x = some V') {ψ : Fml C Δ} (σ : State C Γ)
    (h : holds σ (.upd m' V' ψ)) : holds σ (.bind m x u (.upd m' V ψ)) :=
  Modality.forallB_intro fun w => by
    show m'.afterC (fun τ => ∀ σ' : State C _, σ'.erase = τ → (σ.push w).H <+: σ'.H → holds σ' ψ)
      (V.apply (σ.push w).erase)
    rw [State.push_erase, ← Upd.apply_absorb x σ.erase _ V hV]
    exact h

end Absorb

/-! ## A shadowed state write dropped -/

section Shadow

variable {Γ : Ctx}

/-- A storage operation over its first argument (`select`, `delAt`, a push
or pop's slot, `save`): what a storage spine runs through. -/
def Op1.stSpine {a s : Srt} : Op1 a s → Bool
  | .select _ => true
  | _ => false

@[inherit_doc Op1.stSpine]
def Op2.stSpine {a b s : Srt} : Op2 a b s → Bool
  | .delAt | .pushSlot _ | .pop | .shrink | .extend _ => true
  | _ => false

@[inherit_doc Op1.stSpine]
def Op3.stSpine {a b c s : Srt} : Op3 a b c s → Bool
  | .save | .push => true
  | _ => false

/-- A memory operation over its first argument (`addM`, `copySt`, `write`). -/
def Op1.memSpine {a s : Srt} : Op1 a s → Bool
  | .addM _ => true
  | _ => false

@[inherit_doc Op1.memSpine]
def Op2.memSpine {a b s : Srt} : Op2 a b s → Bool
  | .copySt => true
  | _ => false

@[inherit_doc Op1.memSpine]
def Op3.memSpine {a b c s : Srt} : Op3 a b c s → Bool
  | .write => true
  | _ => false

/-- `Tm.spineHas`' compiled twin. -/
def Tm.spineHasM (S : Tm C Γ .st) : {s : Srt} → Tm C Γ s → Bool
  | _, .app1 o _ a => o.stSpine && (a.beqR S || Tm.spineHasM S a)
  | _, .app2 o a _ => o.stSpine && (a.beqR S || Tm.spineHasM S a)
  | _, .app3 o a _ _ => o.stSpine && (a.beqR S || Tm.spineHasM S a)
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .netOf .. | _, .app0 _ => false

/-- `S` is read first, strictly inside `T`: `T` a storage operation over `S`
or over a term with `S` on its spine (`Surface.Tm.spineAny`).  Generic in
the sort, by the recursor. -/
@[implemented_by Tm.spineHasM]
def Tm.spineHas (S : Tm C Γ .st) {s : Srt} (T : Tm C Γ s) : Bool :=
  Tm.rec (motive := fun _ _ => Bool)
    (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ _ _ => false)
    (fun _ => false)
    (fun o _ a ih => o.stSpine && (a.beqR S || ih))
    (fun o a _ iha _ => o.stSpine && (a.beqR S || iha))
    (fun o a _ _ iha _ _ => o.stSpine && (a.beqR S || iha)) T

theorem Tm.spineHas_eq_spineHasM (S : Tm C Γ .st) {s : Srt} (T : Tm C Γ s) :
    Tm.spineHas S T = Tm.spineHasM S T := by
  induction T with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ _ | app0 _ => rfl
  | app1 o _ a ih => simp only [Tm.spineHasM, ← ih]; rfl
  | app2 o a _ ih _ => simp only [Tm.spineHasM, ← ih]; rfl
  | app3 o a _ _ ih _ _ => simp only [Tm.spineHasM, ← ih]; rfl

/-- `S` is read before anything else of `T` (`Surface.Tm.onSpine`): `T` is
`S`, or `S` is on its spine. -/
def Tm.onSpineS (T S : Tm C Γ .st) : Bool := T.beqR S || Tm.spineHas S T

/-- `Tm.memSpineHas`' compiled twin. -/
def Tm.memSpineHasM (M : Tm C Γ .mem) : {s : Srt} → Tm C Γ s → Bool
  | _, .app1 o _ a => o.memSpine && (a.beqR M || Tm.memSpineHasM M a)
  | _, .app2 o a _ => o.memSpine && (a.beqR M || Tm.memSpineHasM M a)
  | _, .app3 o a _ _ => o.memSpine && (a.beqR M || Tm.memSpineHasM M a)
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .netOf .. | _, .app0 _ => false

/-- `M` is read first, strictly inside `N`, on the memory spine
(`Surface.Tm.memSpineAny`), by the recursor. -/
@[implemented_by Tm.memSpineHasM]
def Tm.memSpineHas (M : Tm C Γ .mem) {s : Srt} (N : Tm C Γ s) : Bool :=
  Tm.rec (motive := fun _ _ => Bool)
    (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ _ _ => false)
    (fun _ => false)
    (fun o _ a ih => o.memSpine && (a.beqR M || ih))
    (fun o a _ iha _ => o.memSpine && (a.beqR M || iha))
    (fun o a _ _ iha _ _ => o.memSpine && (a.beqR M || iha)) N

theorem Tm.memSpineHas_eq_memSpineHasM (M : Tm C Γ .mem) {s : Srt} (N : Tm C Γ s) :
    Tm.memSpineHas M N = Tm.memSpineHasM M N := by
  induction N with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ _ | app0 _ => rfl
  | app1 o _ a ih => simp only [Tm.memSpineHasM, ← ih]; rfl
  | app2 o a _ ih _ => simp only [Tm.memSpineHasM, ← ih]; rfl
  | app3 o a _ _ ih _ _ => simp only [Tm.memSpineHasM, ← ih]; rfl

/-- `M` is read before anything else of `N` on the memory spine. -/
def Tm.onMemSpineS (N M : Tm C Γ .mem) : Bool := N.beqR M || Tm.memSpineHas M N

/-- An outcome that halted, at any sort. -/
def Srt.Halts : (s : Srt) → s.Ev → Prop
  | .val, r => ∃ e, r = .error e
  | .path, r => ∃ e, r = .error e
  | .st, r => ∃ e, r = .error e
  | .sv, r => ∃ e, r = .error e
  | .ident, r => ∃ e, r = .error e
  | .addr, r => ∃ e, r = .error e
  | .mem, r => ∃ e, r = .error e
  | .mv, r => ∃ e, r = .error e

/-- A term with `S` on its spine halts wherever `S` does. -/
theorem Tm.spineHas_haltsM {S : Tm C Γ .st} {σ : EState C Γ} {e : Semantics.Halt}
    (hS : S.eval σ = .error e) {s : Srt} (T : Tm C Γ s) (h : Tm.spineHasM S T = true) :
    Srt.Halts s (T.eval σ) := by
  induction T with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ _ | app0 _ => exact absurd h Bool.false_ne_true
  | app1 o ho a iha =>
    simp only [Tm.spineHasM, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨ho', h'⟩ := h
    cases o <;> simp only [Op1.stSpine, Bool.false_eq_true] at ho'
    all_goals
      obtain ⟨e', ha⟩ : ∃ e', a.eval σ = .error e' := by
        rcases h' with h' | h'
        · exact ⟨e, (Tm.eq_of_beqR h') ▸ hS⟩
        · exact iha h'
      exact ⟨e', by show Op1.eval _ _ (a.eval σ) = _; rw [ha]; rfl⟩
  | app2 o a b iha _ =>
    simp only [Tm.spineHasM, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨ho', h'⟩ := h
    cases o <;> simp only [Op2.stSpine, Bool.false_eq_true] at ho'
    all_goals
      obtain ⟨e', ha⟩ : ∃ e', a.eval σ = .error e' := by
        rcases h' with h' | h'
        · exact ⟨e, (Tm.eq_of_beqR h') ▸ hS⟩
        · exact iha h'
      first
        | exact ⟨e', by show Op2.eval _ _ (a.eval σ) (b.eval σ) = _; rw [ha]; rfl⟩
        | (show ∃ e'', Op2.eval _ _ (a.eval σ) (b.eval σ) = _
           rw [ha]
           generalize b.eval σ = r
           cases r <;> exact ⟨_, rfl⟩)
  | app3 o a b c iha _ _ =>
    simp only [Tm.spineHasM, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨ho', h'⟩ := h
    cases o <;> simp only [Op3.stSpine, Bool.false_eq_true] at ho'
    all_goals
      obtain ⟨e', ha⟩ : ∃ e', a.eval σ = .error e' := by
        rcases h' with h' | h'
        · exact ⟨e, (Tm.eq_of_beqR h') ▸ hS⟩
        · exact iha h'
      first
        | exact ⟨e', by show Op3.eval _ _ (a.eval σ) (b.eval σ) (c.eval σ) = _; rw [ha]; rfl⟩
        | (show ∃ e'', Op3.eval _ _ (a.eval σ) (b.eval σ) (c.eval σ) = _
           rw [ha]
           generalize c.eval σ = r
           cases r <;> exact ⟨_, rfl⟩)

/-- A term on the spine of `S` halts wherever `S` does. -/
theorem Tm.onSpineS_error {S : Tm C Γ .st} {σ : EState C Γ} {e : Semantics.Halt}
    (hS : S.eval σ = .error e) (T : Tm C Γ .st) (h : T.onSpineS S = true) :
    ∃ e', T.eval σ = .error e' := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [Tm.eq_of_beqR h]; exact ⟨e, hS⟩
  · exact Tm.spineHas_haltsM hS T (Tm.spineHas_eq_spineHasM S T ▸ h)

/-- A term with `M` on its memory spine halts wherever `M` does. -/
theorem Tm.memSpineHas_haltsM {M : Tm C Γ .mem} {σ : EState C Γ} {e : Semantics.Halt}
    (hM : M.eval σ = .error e) {s : Srt} (N : Tm C Γ s) (h : Tm.memSpineHasM M N = true) :
    Srt.Halts s (N.eval σ) := by
  induction N with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ _ | app0 _ => exact absurd h Bool.false_ne_true
  | app1 o ho a iha =>
    simp only [Tm.memSpineHasM, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨ho', h'⟩ := h
    cases o <;> simp only [Op1.memSpine, Bool.false_eq_true] at ho'
    all_goals
      obtain ⟨e', ha⟩ : ∃ e', a.eval σ = .error e' := by
        rcases h' with h' | h'
        · exact ⟨e, (Tm.eq_of_beqR h') ▸ hM⟩
        · exact iha h'
      exact ⟨e', by show Op1.eval _ _ (a.eval σ) = _; rw [ha]; rfl⟩
  | app2 o a b iha _ =>
    simp only [Tm.memSpineHasM, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨ho', h'⟩ := h
    cases o <;> simp only [Op2.memSpine, Bool.false_eq_true] at ho'
    all_goals
      obtain ⟨e', ha⟩ : ∃ e', a.eval σ = .error e' := by
        rcases h' with h' | h'
        · exact ⟨e, (Tm.eq_of_beqR h') ▸ hM⟩
        · exact iha h'
      first
        | exact ⟨e', by show Op2.eval _ _ (a.eval σ) (b.eval σ) = _; rw [ha]; rfl⟩
        | (show ∃ e'', Op2.eval _ _ (a.eval σ) (b.eval σ) = _
           rw [ha]
           generalize b.eval σ = r
           cases r <;> exact ⟨_, rfl⟩)
  | app3 o a b c iha _ _ =>
    simp only [Tm.memSpineHasM, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨ho', h'⟩ := h
    cases o <;> simp only [Op3.memSpine, Bool.false_eq_true] at ho'
    all_goals
      obtain ⟨e', ha⟩ : ∃ e', a.eval σ = .error e' := by
        rcases h' with h' | h'
        · exact ⟨e, (Tm.eq_of_beqR h') ▸ hM⟩
        · exact iha h'
      first
        | exact ⟨e', by show Op3.eval _ _ (a.eval σ) (b.eval σ) (c.eval σ) = _; rw [ha]; rfl⟩
        | (show ∃ e'', Op3.eval _ _ (a.eval σ) (b.eval σ) (c.eval σ) = _
           rw [ha]
           generalize c.eval σ = r
           cases r <;> exact ⟨_, rfl⟩)

/-- A term on the memory spine of `M` halts wherever `M` does. -/
theorem Tm.onMemSpineS_error {M : Tm C Γ .mem} {σ : EState C Γ} {e : Semantics.Halt}
    (hM : M.eval σ = .error e) (N : Tm C Γ .mem) (h : N.onMemSpineS M = true) :
    ∃ e', N.eval σ = .error e' := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [Tm.eq_of_beqR h]; exact ⟨e, hM⟩
  · exact Tm.memSpineHas_haltsM hM N (Tm.memSpineHas_eq_memSpineHasM M N ▸ h)

/-- The update with each storage write whose storage a later one reads first
dropped (`P` the storage terms written later), and so each memory write
(`Q`). -/
def Upd.dropSh (P : List (Tm C Γ .st)) (Q : List (Tm C Γ .mem)) :
    {Δ : Ctx} → Upd C Γ Δ → Upd C Γ Δ
  | _, .nil => .nil
  | _, .snoc U e => match e with
    | .storage S =>
      if P.any (·.onSpineS S) then Upd.dropSh P Q U else .snoc (Upd.dropSh (S :: P) Q U) (.storage S)
    | .memory M =>
      if Q.any (·.onMemSpineS M) then Upd.dropSh P Q U else .snoc (Upd.dropSh P (M :: Q) U) (.memory M)
    | e => .snoc (Upd.dropSh P Q U) e
  | _, .decl U x r => .decl (Upd.dropSh P Q U) x r
  | _, .pop U h => .pop (Upd.dropSh P Q U) h
  | _, .drop U h => .drop (Upd.dropSh P Q U) h

/-- A state with its storage and memory replaced. -/
def EState.withSHN {Δ : Ctx} (τ : EState C Δ) (st : List (Name × Semantics.SVal))
    (hp : List (Nat × Semantics.MObj)) (n : Nat) : EState C Δ :=
  { τ with storage := st, heap := hp, nextId := n }

theorem EState.withSHN_self {Δ : Ctx} (τ : EState C Δ) : τ.withSHN τ.storage τ.heap τ.nextId = τ := rfl

/-- An element that writes neither the storage nor the memory runs alike from
a state with another storage and memory. -/
theorem UpdElem.write_withSHN {Δ : Ctx} (σ₀ : EState C Γ) (st : List (Name × Semantics.SVal))
    (hp : List (Nat × Semantics.MObj)) (n : Nat) (τ : EState C Δ) :
    (e : UpdElem C Γ Δ) → (∀ S, e ≠ .storage S) → (∀ M, e ≠ .memory M) →
      e.write σ₀ (τ.withSHN st hp n) = (e.write σ₀ τ).map (·.withSHN st hp n)
  | .local i r, _, _ => by
    simp only [UpdElem.write]
    cases r.eval σ₀ <;> rfl
  | .storage S, h, _ => absurd rfl (h S)
  | .memory M, _, h => absurd rfl (h M)
  | .selfBalance op a, _, _ => by
    simp only [UpdElem.write]
    cases a.eval σ₀ with
    | error => rfl
    | ok v => cases v <;> rfl
  | .net r op a, _, _ => by
    simp only [UpdElem.write]
    cases r.eval σ₀ with
    | error => rfl
    | ok v =>
      cases v with
      | bool => rfl
      | int =>
        cases a.eval σ₀ with
        | error => rfl
        | ok w => cases w <;> rfl
  | .pay r a, _, _ => by
    simp only [UpdElem.write]
    cases r.eval σ₀ with
    | error => rfl
    | ok v =>
      cases v with
      | bool => rfl
      | int =>
        cases a.eval σ₀ with
        | error => rfl
        | ok w =>
          cases w with
          | bool => rfl
          | int =>
            simp only [bind, Except.bind, Semantics.Value.asInt, pure, Except.pure]
            split <;> rfl
  | .netMt r a, _, _ => by
    simp only [UpdElem.write]
    cases r.eval σ₀ with
    | error => rfl
    | ok v =>
      cases v with
      | bool => rfl
      | int =>
        cases a.eval σ₀ with
        | error => rfl
        | ok w => cases w <;> rfl
  | .setBalance a, _, _ => by
    simp only [UpdElem.write]
    cases a.eval σ₀ with
    | error => rfl
    | ok v => cases v <;> rfl

theorem UpdElem.write_storage_ok {Δ : Ctx} {σ₀ : EState C Γ} {S : Tm C Γ .st} {g : Semantics.State}
    (hs : S.eval σ₀ = .ok g) (τ : EState C Δ) :
    (UpdElem.storage S).write σ₀ τ = .ok (τ.withGlob { τ.glob with storage := g.storage }) := by
  simp only [UpdElem.write, hs]; rfl

theorem UpdElem.write_storage_error {Δ : Ctx} {σ₀ : EState C Γ} {S : Tm C Γ .st} {e : Semantics.Halt}
    (hs : S.eval σ₀ = .error e) (τ : EState C Δ) : (UpdElem.storage S).write σ₀ τ = .error e := by
  simp only [UpdElem.write, hs]; rfl

theorem UpdElem.write_memory_ok {Δ : Ctx} {σ₀ : EState C Γ} {M : Tm C Γ .mem} {g : Semantics.State}
    (hs : M.eval σ₀ = .ok g) (τ : EState C Δ) :
    (UpdElem.memory M).write σ₀ τ = .ok (τ.withGlob { τ.glob with heap := g.heap, nextId := g.nextId }) := by
  simp only [UpdElem.write, hs]; rfl

theorem UpdElem.write_memory_error {Δ : Ctx} {σ₀ : EState C Γ} {M : Tm C Γ .mem} {e : Semantics.Halt}
    (hs : M.eval σ₀ = .error e) (τ : EState C Δ) : (UpdElem.memory M).write σ₀ τ = .error e := by
  simp only [UpdElem.write, hs]; rfl

/-- How a run and its run with the shadowed writes dropped (`P`, `Q` the
writes still to come) relate: one state but for the storage (where a write
is to come) and the memory, or both halted, or the first halted on a write
whose shadowing write halts too. -/
def ShRel (σ₀ : EState C Γ) (P : List (Tm C Γ .st)) (Q : List (Tm C Γ .mem)) {Δ : Ctx}
    (a b : Res (EState C Δ)) : Prop :=
  (∃ τ st hp n, a = .ok τ ∧ b = .ok (τ.withSHN st hp n) ∧ (P = [] → st = τ.storage) ∧
      (Q = [] → hp = τ.heap ∧ n = τ.nextId)) ∨
    ((∃ e, a = .error e) ∧ ((∃ e, b = .error e) ∨ (∃ T ∈ P, ∃ e, T.eval σ₀ = .error e) ∨
      (∃ M ∈ Q, ∃ e, M.eval σ₀ = .error e)))

theorem ShRel.bind_write {σ₀ : EState C Γ} {P : List (Tm C Γ .st)} {Q : List (Tm C Γ .mem)}
    {Δ : Ctx} {a b : Res (EState C Δ)} (h : ShRel σ₀ P Q a b) (e : UpdElem C Γ Δ)
    (hS : ∀ S, e ≠ .storage S) (hM : ∀ M, e ≠ .memory M) :
    ShRel σ₀ P Q (a >>= e.write σ₀) (b >>= e.write σ₀) := by
  rcases h with ⟨τ, st, hp, n, rfl, rfl, h₁, h₂⟩ | ⟨⟨e₁, rfl⟩, h⟩
  · show ShRel σ₀ P Q (e.write σ₀ τ) (e.write σ₀ (τ.withSHN st hp n))
    rw [UpdElem.write_withSHN σ₀ st hp n τ e hS hM]
    have hτ := UpdElem.write_withSHN σ₀ τ.storage τ.heap τ.nextId τ e hS hM
    rw [EState.withSHN_self] at hτ
    cases hw : e.write σ₀ τ with
    | error e₂ => exact .inr ⟨⟨e₂, rfl⟩, .inl ⟨e₂, rfl⟩⟩
    | ok ρ =>
      rw [hw] at hτ
      have hρ : ρ = ρ.withSHN τ.storage τ.heap τ.nextId := by
        simp only [Except.map] at hτ; exact Except.ok.inj hτ
      refine .inl ⟨ρ, st, hp, n, rfl, rfl, fun hP => ?_, fun hQ => ?_⟩
      · rw [h₁ hP, hρ]; rfl
      · obtain ⟨rfl, rfl⟩ := h₂ hQ; rw [hρ]; exact ⟨rfl, rfl⟩
  · refine .inr ⟨⟨e₁, rfl⟩, ?_⟩
    rcases h with ⟨e₂, rfl⟩ | h
    · exact .inl ⟨e₂, rfl⟩
    · exact .inr h

/-- **Dropping the shadowed writes leaves the run, or a halt a halt.** -/
theorem Upd.dropSh_rel (σ₀ : EState C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    (P : List (Tm C Γ .st)) → (Q : List (Tm C Γ .mem)) →
      ShRel σ₀ P Q (U.apply σ₀) ((U.dropSh P Q).apply σ₀)
  | _, .nil, P, Q => .inl ⟨σ₀, σ₀.storage, σ₀.heap, σ₀.nextId, rfl, rfl, fun _ => rfl, fun _ => ⟨rfl, rfl⟩⟩
  | _, .snoc U (.storage S), P, Q => by
    simp only [Upd.dropSh]
    split
    · rename_i hP
      obtain ⟨T, hT, hTS⟩ := List.any_eq_true.1 hP
      show ShRel σ₀ P Q (U.apply σ₀ >>= UpdElem.write σ₀ (.storage S)) ((U.dropSh P Q).apply σ₀)
      rcases Upd.dropSh_rel σ₀ U P Q with ⟨τ, st, hp, n, ha, hb, h₁, h₂⟩ | ⟨⟨e₁, ha⟩, h⟩
      · rw [ha, hb]
        show ShRel σ₀ P Q (UpdElem.write σ₀ (.storage S) τ) _
        cases hs : S.eval σ₀ with
        | error e₂ =>
          rw [UpdElem.write_storage_error hs]
          exact .inr ⟨⟨e₂, rfl⟩, .inr (.inl ⟨T, hT, Tm.onSpineS_error hs T hTS⟩)⟩
        | ok g =>
          rw [UpdElem.write_storage_ok hs]
          refine .inl ⟨τ.withGlob { τ.glob with storage := g.storage }, st, hp, n, rfl, rfl,
            fun hP' => absurd hP' (List.ne_nil_of_mem hT), fun hQ => ?_⟩
          obtain ⟨rfl, rfl⟩ := h₂ hQ; exact ⟨rfl, rfl⟩
      · rw [ha]
        exact .inr ⟨⟨e₁, rfl⟩, h⟩
    · show ShRel σ₀ P Q (U.apply σ₀ >>= UpdElem.write σ₀ (.storage S))
        ((U.dropSh (S :: P) Q).apply σ₀ >>= UpdElem.write σ₀ (.storage S))
      rcases Upd.dropSh_rel σ₀ U (S :: P) Q with ⟨τ, st, hp, n, ha, hb, h₁, h₂⟩ | ⟨⟨e₁, ha⟩, h⟩
      · rw [ha, hb]
        show ShRel σ₀ P Q (UpdElem.write σ₀ (.storage S) τ)
          (UpdElem.write σ₀ (.storage S) (τ.withSHN st hp n))
        cases hs : S.eval σ₀ with
        | error e₂ =>
          rw [UpdElem.write_storage_error hs, UpdElem.write_storage_error hs]
          exact .inr ⟨⟨e₂, rfl⟩, .inl ⟨e₂, rfl⟩⟩
        | ok g =>
          rw [UpdElem.write_storage_ok hs, UpdElem.write_storage_ok hs]
          refine .inl ⟨τ.withGlob { τ.glob with storage := g.storage }, g.storage, hp, n, rfl, rfl,
            fun _ => rfl, fun hQ => ?_⟩
          obtain ⟨rfl, rfl⟩ := h₂ hQ; exact ⟨rfl, rfl⟩
      · rw [ha]
        refine .inr ⟨⟨e₁, rfl⟩, ?_⟩
        rcases h with ⟨e₂, hb⟩ | ⟨T, hT, e₂, hTe⟩ | hM
        · rw [hb]; exact .inl ⟨e₂, rfl⟩
        · rcases List.mem_cons.1 hT with rfl | hT
          · cases hb : (U.dropSh (T :: P) Q).apply σ₀ with
            | error e₃ => exact .inl ⟨e₃, rfl⟩
            | ok ρ => exact .inl ⟨e₂, UpdElem.write_storage_error hTe ρ⟩
          · exact .inr (.inl ⟨T, hT, e₂, hTe⟩)
        · exact .inr (.inr hM)
  | _, .snoc U (.memory M), P, Q => by
    simp only [Upd.dropSh]
    split
    · rename_i hQ
      obtain ⟨N, hN, hNM⟩ := List.any_eq_true.1 hQ
      show ShRel σ₀ P Q (U.apply σ₀ >>= UpdElem.write σ₀ (.memory M)) ((U.dropSh P Q).apply σ₀)
      rcases Upd.dropSh_rel σ₀ U P Q with ⟨τ, st, hp, n, ha, hb, h₁, h₂⟩ | ⟨⟨e₁, ha⟩, h⟩
      · rw [ha, hb]
        show ShRel σ₀ P Q (UpdElem.write σ₀ (.memory M) τ) _
        cases hs : M.eval σ₀ with
        | error e₂ =>
          rw [UpdElem.write_memory_error hs]
          exact .inr ⟨⟨e₂, rfl⟩, .inr (.inr ⟨N, hN, Tm.onMemSpineS_error hs N hNM⟩)⟩
        | ok g =>
          rw [UpdElem.write_memory_ok hs]
          refine .inl ⟨τ.withGlob { τ.glob with heap := g.heap, nextId := g.nextId }, st, hp, n, rfl,
            rfl, fun hP => ?_, fun hQ' => absurd hQ' (List.ne_nil_of_mem hN)⟩
          rw [h₁ hP]; rfl
      · rw [ha]
        exact .inr ⟨⟨e₁, rfl⟩, h⟩
    · show ShRel σ₀ P Q (U.apply σ₀ >>= UpdElem.write σ₀ (.memory M))
        ((U.dropSh P (M :: Q)).apply σ₀ >>= UpdElem.write σ₀ (.memory M))
      rcases Upd.dropSh_rel σ₀ U P (M :: Q) with ⟨τ, st, hp, n, ha, hb, h₁, h₂⟩ | ⟨⟨e₁, ha⟩, h⟩
      · rw [ha, hb]
        show ShRel σ₀ P Q (UpdElem.write σ₀ (.memory M) τ)
          (UpdElem.write σ₀ (.memory M) (τ.withSHN st hp n))
        cases hs : M.eval σ₀ with
        | error e₂ =>
          rw [UpdElem.write_memory_error hs, UpdElem.write_memory_error hs]
          exact .inr ⟨⟨e₂, rfl⟩, .inl ⟨e₂, rfl⟩⟩
        | ok g =>
          rw [UpdElem.write_memory_ok hs, UpdElem.write_memory_ok hs]
          refine .inl ⟨τ.withGlob { τ.glob with heap := g.heap, nextId := g.nextId }, st, g.heap,
            g.nextId, rfl, rfl, fun hP => ?_, fun _ => ⟨rfl, rfl⟩⟩
          rw [h₁ hP]; rfl
      · rw [ha]
        refine .inr ⟨⟨e₁, rfl⟩, ?_⟩
        rcases h with ⟨e₂, hb⟩ | hP | ⟨N, hN, e₂, hNe⟩
        · rw [hb]; exact .inl ⟨e₂, rfl⟩
        · exact .inr (.inl hP)
        · rcases List.mem_cons.1 hN with rfl | hN
          · cases hb : (U.dropSh P (N :: Q)).apply σ₀ with
            | error e₃ => exact .inl ⟨e₃, rfl⟩
            | ok ρ => exact .inl ⟨e₂, UpdElem.write_memory_error hNe ρ⟩
          · exact .inr (.inr ⟨N, hN, e₂, hNe⟩)
  | _, .snoc U (.local i r), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_write _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.selfBalance op a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_write _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.net r op a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_write _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.pay r a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_write _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.netMt r a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_write _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.setBalance a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_write _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .decl U x r, P, Q => by
    have ih := Upd.dropSh_rel σ₀ U P Q
    show ShRel σ₀ P Q (do let τ ← U.apply σ₀; pure (τ.push (← r.eval σ₀)))
      (do let τ ← (U.dropSh P Q).apply σ₀; pure (τ.push (← r.eval σ₀)))
    rcases ih with ⟨τ, st, hp, n, ha, hb, h₁, h₂⟩ | ⟨⟨e₁, ha⟩, h⟩
    · rw [ha, hb]
      cases hr : r.eval σ₀ with
      | error e₂ => exact .inr ⟨⟨e₂, rfl⟩, .inl ⟨e₂, rfl⟩⟩
      | ok w => exact .inl ⟨τ.push w, st, hp, n, rfl, rfl, h₁, h₂⟩
    · rw [ha]
      refine .inr ⟨⟨e₁, rfl⟩, ?_⟩
      rcases h with ⟨e₂, hb⟩ | h
      · rw [hb]; exact .inl ⟨e₂, rfl⟩
      · exact .inr h
  | _, .pop U hd, P, Q => by
    have ih := Upd.dropSh_rel σ₀ U P Q
    show ShRel σ₀ P Q ((U.apply σ₀).map (EState.drop hd)) (((U.dropSh P Q).apply σ₀).map (EState.drop hd))
    rcases ih with ⟨τ, st, hp, n, ha, hb, h₁, h₂⟩ | ⟨⟨e₁, ha⟩, h⟩
    · rw [ha, hb]; exact .inl ⟨τ.drop hd, st, hp, n, rfl, rfl, h₁, h₂⟩
    · rw [ha]
      refine .inr ⟨⟨e₁, rfl⟩, ?_⟩
      rcases h with ⟨e₂, hb⟩ | h
      · rw [hb]; exact .inl ⟨e₂, rfl⟩
      · exact .inr h
  | _, .drop U hd, P, Q => by
    have ih := Upd.dropSh_rel σ₀ U P Q
    show ShRel σ₀ P Q ((U.apply σ₀).map (EState.thin hd)) (((U.dropSh P Q).apply σ₀).map (EState.thin hd))
    rcases ih with ⟨τ, st, hp, n, ha, hb, h₁, h₂⟩ | ⟨⟨e₁, ha⟩, h⟩
    · rw [ha, hb]; exact .inl ⟨τ.thin hd, st, hp, n, rfl, rfl, h₁, h₂⟩
    · rw [ha]
      refine .inr ⟨⟨e₁, rfl⟩, ?_⟩
      rcases h with ⟨e₂, hb⟩ | h
      · rw [hb]; exact .inl ⟨e₂, rfl⟩
      · exact .inr h

/-- **`{U} φ` from `U` with its shadowed writes dropped.** -/
theorem holds_upd_dropSh {m : Modality} {Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ} (σ : State C Γ)
    (h : holds σ (.upd m (U.dropSh [] []) φ)) : holds σ (.upd m U φ) := by
  show m.afterC _ (U.apply σ.erase)
  have h : m.afterC _ ((U.dropSh [] []).apply σ.erase) := h
  rcases Upd.dropSh_rel σ.erase U [] [] with ⟨τ, st, hp, n, ha, hb, h₁, h₂⟩ | ⟨⟨e₁, ha⟩, h'⟩
  · obtain ⟨rfl, rfl⟩ := h₂ rfl
    rw [h₁ rfl, EState.withSHN_self] at hb
    rw [ha]; rw [hb] at h; exact h
  · rcases h' with ⟨e₂, hb⟩ | ⟨_, hT, _⟩ | ⟨_, hM, _⟩
    · rw [ha]; rw [hb] at h; exact h
    · nomatch hT
    · nomatch hM

end Shadow

/-! ## Two updates merged -/

section Merge

/-- The modality `{U}_m {V}_m'` merges under: theirs where they agree, the
other's where one cannot halt (`Upd.totalB`, `ut`, `vt`). -/
def Modality.mergeP (m : Modality) (ut : Bool) (m' : Modality) (vt : Bool) : Option Modality :=
  if m' = m then some m else if ut then some m' else if vt then some m else none

/-- An update that cannot halt reads alike under either modality. -/
theorem holds_upd_total {m m' : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} (hU : U.totalB = true)
    {φ : Fml C Δ} (σ : State C Γ) (h : holds σ (.upd m U φ)) : holds σ (.upd m' U φ) := by
  obtain ⟨τ, hτ⟩ := Upd.totalB_apply σ.erase U hU
  show m'.afterC _ (U.apply σ.erase)
  have h : m.afterC _ (U.apply σ.erase) := h
  rw [hτ] at h ⊢
  exact h

/-- `{U}{V}` as one update, by the first merge that reads it: `V` read in
`U`'s state (`Upd.seqPar`), over a storage write (`Upd.mergeSt?`), a memory
write (`Upd.mergeMem?`), locals then a memory write (`Upd.mergeMemL?`). -/
def Upd.mergeK? {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂) : Option (Upd C Γ Δ₂) :=
  match U.seqPar V with
  | some W => some W
  | none => match U.mergeSt? V with
    | some W => some W
    | none => match U.mergeMem? V with
      | some W => some W
      | none => U.mergeMemL? V

theorem holds_upd_mergeK {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.mergeK? V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) := by
  unfold Upd.mergeK? at hW
  split at hW
  · rename_i hs; cases hW; exact holds_upd_seqPar hs σ h
  · split at hW
    · rename_i hs; cases hW; exact holds_upd_mergeSt hs σ h
    · split at hW
      · rename_i hs; cases hW; exact holds_upd_mergeMem hs σ h
      · exact holds_upd_mergeMemL hW σ h

/-- **`sequentialToParallel` past the program**: `{U}_m {V}_m'` as one
update and its modality, the shadowed state writes dropped. -/
def Upd.mergeP? {Γ Δ₁ Δ₂ : Ctx} (m : Modality) (U : Upd C Γ Δ₁) (m' : Modality)
    (V : Upd C Δ₁ Δ₂) : Option (Modality × Upd C Γ Δ₂) :=
  (Modality.mergeP m U.totalB m' V.totalB).bind fun mm =>
    (U.mergeK? V).map fun W => (mm, W.dropSh [] [])

theorem holds_upd_mergeP {m m' : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {r : Modality × Upd C Γ Δ₂} (hr : Upd.mergeP? m U m' V = some r) {φ : Fml C Δ₂}
    (σ : State C Γ) (h : holds σ (.upd r.1 r.2 φ)) : holds σ (.upd m U (.upd m' V φ)) := by
  obtain ⟨mm, hmm, hr⟩ := Option.bind_eq_some_iff.1 hr
  obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 hr
  have h₂ : holds σ (.upd mm U (.upd mm V φ)) := holds_upd_mergeK hW σ (holds_upd_dropSh σ h)
  unfold Modality.mergeP at hmm
  split at hmm
  · rename_i he; cases hmm; rw [he]; exact h₂
  · split at hmm
    · rename_i hu; cases hmm; exact holds_upd_total hu σ h₂
    · split at hmm
      · rename_i hv; cases hmm
        exact holds_upd_mono (fun τ hτ => holds_upd_total hv τ hτ) σ h₂
      · cases hmm

/-- `{U}_m bind x ψ` merged where `ψ` is an update that sets `x` first: the
binder absorbed (`Upd.absorb`), then the two merged. -/
def Fml.absorbMergeP (m : Modality) {Γ Δ : Ctx} (U : Upd C Γ Δ) (x : Var) {t : LTy}
    (ψ : Fml C (t :: Δ)) : Option (Fml C Γ) :=
  match ψ with
  | .upd m'' V χ => (V.absorb x).bind fun V' => (Upd.mergeP? m U m'' V').map fun r => .upd r.1 r.2 χ
  | _ => none

theorem Fml.absorbMergeP_sound {m m' : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {x : Var} {t : LTy}
    {ψ : Fml C (t :: Δ)} {φ : Fml C Γ} (h : Fml.absorbMergeP m U x ψ = some φ) (σ : State C Γ)
    (hφ : holds σ φ) : holds σ (.upd m U (.bind m' x t ψ)) := by
  unfold Fml.absorbMergeP at h
  split at h
  · rename_i m'' V χ
    obtain ⟨V', hV', h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    exact holds_upd_mono (fun τ hτ => holds_bind_absorb hV' τ hτ) σ (holds_upd_mergeP hr σ hφ)
  · cases h

/-- `{U}_m φ` merged with the update at the head of `φ`, through a hidden
binder: absorbed where the update sets its local first (`Fml.absorbMergeP`),
or `U` moved under it with its scope ends (`Upd.liftG?`, as
`Calculus/Merge.lean`'s `Fml.merge2` moves one). -/
def Fml.merge2P (m : Modality) : {Γ Δ : Ctx} → Upd C Γ Δ → Fml C Δ → Option (Fml C Γ)
  | _, _, U, .upd m' V ψ => (Upd.mergeP? m U m' V).map fun r => .upd r.1 r.2 ψ
  | _, _, U, .bind m' x t ψ =>
    match Fml.absorbMergeP m U x ψ with
    | some φ => some φ
    | none =>
      if (t.notMem || U.keepsNext) = true then
        (U.liftG? (t := t)).bind fun U' => (Fml.merge2P m U' ψ).map (.bind m' x t)
      else none
  | _, _, _, _ => none

theorem Fml.merge2P_sound {m : Modality} : {Γ Δ : Ctx} → (U : Upd C Γ Δ) →
    (φ : Fml C Δ) → {ψ : Fml C Γ} → Fml.merge2P m U φ = some ψ →
      ∀ σ, holds σ ψ → holds σ (.upd m U φ)
  | _, _, U, .upd m' V χ, ψ, h => by
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hψ => holds_upd_mergeP hr σ hψ
  | _, _, U, .bind m' x t χ, ψ, h => by
    simp only [Fml.merge2P] at h
    split at h
    · rename_i φ hφ
      cases h
      exact fun σ hψ => Fml.absorbMergeP_sound hφ σ hψ
    · split at h
      · rename_i ht
        obtain ⟨U', hU', h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨χ', hχ', rfl⟩ := Option.map_eq_some_iff.1 h
        intro σ hψ
        exact Fml.upd_bind_of_apply (fun τ w => Upd.apply_liftG? τ w U hU') ht σ
          (Modality.forallB_imp (fun v h => Fml.merge2P_sound U' χ hχ' _ h) hψ)
      · cases h
  | _, _, _, .tt, _, h | _, _, _, .eq .., _, h | _, _, _, .defined _, _, h | _, _, _, .not _, _, h
  | _, _, _, .and .., _, h | _, _, _, .imp .., _, h | _, _, _, .modal .., _, h
  | _, _, _, .havoc _, _, h | _, _, _, .all .., _, h | _, _, _, .anon .., _, h => nomatch h

/-- `sequentialToParallel` past the program on the updates at positions `k`
and `k + 1` of the line's update spine, under its quantifiers and hidden
binders. -/
def Fml.mergeAtP {Γ : Ctx} : Nat → Fml C Γ → Option (Fml C Γ)
  | k, .all x p φ => (Fml.mergeAtP k φ).map (.all x p)
  | k, .bind m x t φ => (Fml.mergeAtP k φ).map (.bind m x t)
  | 0, .upd m U φ => Fml.merge2P m U φ
  | k + 1, .upd m U φ => (Fml.mergeAtP k φ).map (.upd m U)
  | _, _ => none

/-- `Fml.mergeAtP` `n` times: the `n + 1` updates from position `k` merged
into one, the innermost pair first (`NFml.mergeRun`'s order: a merge over
a memory write asks the write last in the update before, which the pair
after it is merged into first). -/
def Fml.mergeRunP {Γ : Ctx} (k : Nat) : Nat → Fml C Γ → Option (Fml C Γ)
  | 0, φ => some φ
  | n + 1, φ => (φ.mergeAtP (k + n)).bind (Fml.mergeRunP k n)

theorem Fml.mergeAtP_sound : {Γ : Ctx} → (k : Nat) → (φ : Fml C Γ) → {ψ : Fml C Γ} →
    φ.mergeAtP k = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | _, k, .all x p φ, ψ₀, h => by
    have h : (Fml.mergeAtP k φ).map (Fml.all x p) = some ψ₀ := by rw [← h]; cases k <;> rfl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs v => Fml.mergeAtP_sound k φ hψ _ (hs v)
  | _, k, .bind m x t φ, ψ₀, h => by
    have h : (Fml.mergeAtP k φ).map (Fml.bind m x t) = some ψ₀ := by rw [← h]; cases k <;> rfl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Modality.forallB_imp (fun v => Fml.mergeAtP_sound k φ hψ _) hs
  | _, 0, .upd m U φ, _, h => Fml.merge2P_sound U φ h
  | _, k + 1, .upd m U φ, _, h => by
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Modality.afterC_imp hs fun τ a σ' e hx =>
      Fml.mergeAtP_sound k φ hψ σ' (a σ' e hx)
  | _, k, .tt, _, h | _, k, .eq .., _, h | _, k, .defined _, _, h | _, k, .not _, _, h
  | _, k, .and .., _, h | _, k, .imp .., _, h | _, k, .modal .., _, h | _, k, .havoc _, _, h
  | _, k, .anon .., _, h => by
    cases k <;> cases h

theorem Fml.mergeRunP_sound {Γ : Ctx} (k : Nat) : (n : Nat) → (φ : Fml C Γ) → {ψ : Fml C Γ} →
    φ.mergeRunP k n = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | 0, φ, _, h => by cases h; exact fun _ h => h
  | n + 1, φ, _, h => by
    obtain ⟨χ, hχ, h⟩ := Option.bind_eq_some_iff.1 h
    exact fun σ hψ => Fml.mergeAtP_sound (k + n) φ hχ σ (Fml.mergeRunP_sound k n χ h σ hψ)

/-- **`sequentialToParallel` past the program**: the `n + 1` updates from
position `k` of the spine merged (`Fml.mergeRunP`). -/
def FmlRw.mergePast (k n : Nat) : FmlRw C where
  apply := fun φ => φ.mergeRunP k (n + 1)
  sound := fun h σ hψ => Fml.mergeRunP_sound k (n + 1) _ h σ hψ

end Merge

/-! ## A storage write applied to a first-order line (`applyStorageBox`)

`[{storage := S}] φ ⇝ φ[S/storage]`, `φ` first-order and every storage
read of it a `storage` term (`Tm.stExplicitS`): the erasure's
`NFml.withSt_box`, on the scoped line.  An equation reads its terms
through `denote`, so the substitution is exact up to `Equiv`: `S` denotes
the storage its run leaves (`Tm.denote_eval`), and the rest of the state is
the one before (`Semantics.State.Keeps`, `Tm.eval_st_glob`). -/

section WithSt

variable {Γ : Ctx}

open Theory Theory.StValue

/-- `storage` replaced by `S`. -/
def Op0.withStS (S : Tm C Γ .st) : {s : Srt} → Op0 s → Tm C Γ s
  | _, .storage => S
  | _, .lit v => .app0 (.lit v)
  | _, .env k => .app0 (.env k)
  | _, .root r => .app0 (.root r)
  | _, .memory => .app0 .memory
  | _, .mtSt vs => .app0 (.mtSt vs)

/-- A term with `S` for every `storage` (`Surface.Tm.withSt`). -/
def Tm.withStS (S : Tm C Γ .st) : {s : Srt} → Tm C Γ s → Tm C Γ s
  | _, .pvV i => .pvV i
  | _, .pvP i => .pvP i
  | _, .pvS i => .pvS i
  | _, .pvI i => .pvI i
  | _, .netOf i a => .netOf i (Tm.withStS S a)
  | _, .app0 o => o.withStS S
  | _, .app1 o ho a => .app1 o ho (Tm.withStS S a)
  | _, .app2 o a b => .app2 o (Tm.withStS S a) (Tm.withStS S b)
  | _, .app3 o a b c => .app3 o (Tm.withStS S a) (Tm.withStS S b) (Tm.withStS S c)

/-- Every storage read of the term is a `storage` term, and no ledger
variable is read (`Surface.Tm.stExplicit`). -/
def Tm.stExplicitS : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ => true
  | _, .netOf _ _ => false
  | _, .app0 o => o.stExplicit
  | _, .app1 o _ a => o.stExplicit && a.stExplicitS
  | _, .app2 o a b => o.stExplicit && a.stExplicitS && b.stExplicitS
  | _, .app3 _ a b c => a.stExplicitS && b.stExplicitS && c.stExplicitS

/-- The state after `{storage := S}`, `S` returning `τ`. -/
abbrev EState.afterSt (σ : EState C Γ) (τ : Semantics.State) : EState C Γ :=
  σ.withGlob { σ.glob with storage := τ.storage }

theorem EState.afterSt_glob {σ : EState C Γ} {τ : Semantics.State} (hk : σ.glob.Keeps τ) :
    (σ.afterSt τ).glob = τ := hk

/-- **Read before `{storage := S}`, the substituted term reads what the term
reads after it.** -/
theorem Tm.withStS_eval {S : Tm C Γ .st} {σ : EState C Γ} {τ : Semantics.State}
    (hs : S.eval σ = .ok τ) (hk : σ.glob.Keeps τ) :
    {s : Srt} → (t : Tm C Γ s) → t.stExplicitS = true →
      (Tm.withStS S t).eval σ = t.eval (σ.afterSt τ)
  | _, .pvV _, _ | _, .pvP _, _ | _, .pvS _, _ | _, .pvI _, _ => rfl
  | _, .netOf _ _, he => absurd he Bool.false_ne_true
  | _, .app0 o, he => by
    cases o with
    | storage => show S.eval σ = pure (σ.afterSt τ).glob; rw [hs, EState.afterSt_glob hk]; rfl
    | memory => exact absurd he Bool.false_ne_true
    | lit _ | root _ => rfl
    | env _ | mtSt _ => show _ = Op0.eval (σ.afterSt τ).glob _; rw [EState.afterSt_glob hk, ← hk]; rfl
  | _, .app1 o ho a, he => by
    simp only [Tm.stExplicitS, Bool.and_eq_true] at he
    show o.eval σ.glob ((Tm.withStS S a).eval σ) = o.eval (σ.afterSt τ).glob (a.eval (σ.afterSt τ))
    rw [Tm.withStS_eval hs hk a he.2, EState.afterSt_glob hk]
    exact o.eval_keeps hk he.1 _
  | _, .app2 o a b, he => by
    simp only [Tm.stExplicitS, Bool.and_eq_true] at he
    show o.eval σ.glob ((Tm.withStS S a).eval σ) ((Tm.withStS S b).eval σ) =
      o.eval (σ.afterSt τ).glob (a.eval (σ.afterSt τ)) (b.eval (σ.afterSt τ))
    rw [Tm.withStS_eval hs hk a he.1.2, Tm.withStS_eval hs hk b he.2, EState.afterSt_glob hk]
    exact o.eval_keeps hk he.1.1 _ _
  | _, .app3 o a b c, he => by
    simp only [Tm.stExplicitS, Bool.and_eq_true] at he
    show o.eval σ.glob ((Tm.withStS S a).eval σ) ((Tm.withStS S b).eval σ) ((Tm.withStS S c).eval σ) =
      o.eval (σ.afterSt τ).glob (a.eval (σ.afterSt τ)) (b.eval (σ.afterSt τ)) (c.eval (σ.afterSt τ))
    rw [Tm.withStS_eval hs hk a he.1.1, Tm.withStS_eval hs hk b he.1.2,
      Tm.withStS_eval hs hk c he.2]
    rfl

/-- **Read before `{storage := S}`, the substituted term denotes, up to
`Equiv`, what the term denotes after it.** -/
theorem Tm.withStS_denote {S : Tm C Γ .st} {σ : EState C Γ} {τ : Semantics.State}
    (hs : S.eval σ = .ok τ) (hk : σ.glob.Keeps τ) :
    {s : Srt} → (t : Tm C Γ s) → t.stExplicitS = true →
      Srt.DEquiv s ((Tm.withStS S t).denote σ) (t.denote (σ.afterSt τ))
  | _, .pvV _, _ | _, .pvS _, _ => Equiv.refl _
  | _, .pvP _, _ => rfl
  | _, .pvI _, _ => trivial
  | _, .netOf _ _, he => absurd he Bool.false_ne_true
  | _, .app0 o, he => by
    cases o with
    | storage =>
      show Struct.Equiv (S.denote σ) (Op0.denote (σ.afterSt τ).glob .storage)
      rw [EState.afterSt_glob hk]
      exact Tm.denote_eval σ S τ hs
    | memory => exact absurd he Bool.false_ne_true
    | lit _ | root _ | mtSt _ => exact Srt.DEquiv.refl _ _
    | env _ =>
      show Srt.DEquiv _ (Op0.denote σ.glob _) (Op0.denote (σ.afterSt τ).glob _)
      rw [EState.afterSt_glob hk, ← hk]; exact Srt.DEquiv.refl _ _
  | _, .app1 o ho a, he => by
    simp only [Tm.stExplicitS, Bool.and_eq_true] at he
    show Srt.DEquiv _ (o.denote σ.glob ((Tm.withStS S a).denote σ))
      (o.denote (σ.afterSt τ).glob (a.denote (σ.afterSt τ)))
    rw [EState.afterSt_glob hk]
    exact Srt.DEquiv.of_eq (o.denote_keeps hk he.1 _) (o.denote_congr (Tm.withStS_denote hs hk a he.2))
  | _, .app2 o a b, he => by
    simp only [Tm.stExplicitS, Bool.and_eq_true] at he
    show Srt.DEquiv _ (o.denote σ.glob ((Tm.withStS S a).eval σ) ((Tm.withStS S b).eval σ)
        ((Tm.withStS S a).denote σ) ((Tm.withStS S b).denote σ))
      (o.denote (σ.afterSt τ).glob (a.eval (σ.afterSt τ)) (b.eval (σ.afterSt τ))
        (a.denote (σ.afterSt τ)) (b.denote (σ.afterSt τ)))
    rw [EState.afterSt_glob hk]
    exact Srt.DEquiv.of_eq (o.denote_keeps hk he.1.1 _ (a.eval (σ.afterSt τ)) _
        (b.eval (σ.afterSt τ)) _ _)
      (o.denote_congr (Op2.opaque_of_stExplicit he.1.1) (Tm.withStS_denote hs hk a he.1.2)
        (Tm.withStS_denote hs hk b he.2))
  | _, .app3 o a b c, he => by
    simp only [Tm.stExplicitS, Bool.and_eq_true] at he
    exact o.denote_congr (Tm.withStS_denote hs hk a he.1.1) (Tm.withStS_denote hs hk b he.1.2)
      (Tm.withStS_denote hs hk c he.2)

/-- A first-order formula with `S` for every `storage`, where every storage
read of it is a `storage` term; `none` past anything else. -/
def Fml.withStS (S : Tm C Γ .st) : Fml C Γ → Option (Fml C Γ)
  | .tt => some .tt
  | .eq a b => if (a.stExplicitS && b.stExplicitS) = true then some (.eq (Tm.withStS S a) (Tm.withStS S b))
    else none
  | .defined t => if t.stExplicitS = true then some (.defined (Tm.withStS S t)) else none
  | .not φ => (Fml.withStS S φ).map .not
  | .and φ ψ => do pure (.and (← Fml.withStS S φ) (← Fml.withStS S ψ))
  | .imp φ ψ => do pure (.imp (← Fml.withStS S φ) (← Fml.withStS S ψ))
  | _ => none

/-- **A first-order formula with `S` for `storage` holds before the write as
the formula holds after it.** -/
theorem Fml.withStS_holds {S : Tm C Γ .st} {σ : State C Γ} {τ : Semantics.State}
    (hs : S.eval σ.erase = .ok τ) (σ' : State C Γ) (he : σ'.erase = σ.erase.afterSt τ) :
    (φ : Fml C Γ) → {φ' : Fml C Γ} → Fml.withStS S φ = some φ' → (holds σ φ' ↔ holds σ' φ)
  | .tt, _, h => by cases h; exact Iff.rfl
  | .eq a b, _, h => by
    simp only [Fml.withStS] at h
    split at h
    · rename_i hab
      cases h
      simp only [Bool.and_eq_true] at hab
      have hk : σ.erase.glob.Keeps τ := (Tm.eval_st_glob σ.erase S τ hs).symm
      have ea := Tm.withStS_denote hs hk a hab.1
      have eb := Tm.withStS_denote hs hk b hab.2
      show Equiv ((Tm.withStS S a).denote σ.erase) ((Tm.withStS S b).denote σ.erase) ↔
        Equiv (a.denote σ'.erase) (b.denote σ'.erase)
      rw [he]
      exact ⟨fun e => (ea.symm.trans e).trans eb, fun e => (ea.trans e).trans eb.symm⟩
    · cases h
  | .defined t, _, h => by
    simp only [Fml.withStS] at h
    split at h
    · rename_i ht
      cases h
      have hk : σ.erase.glob.Keeps τ := (Tm.eval_st_glob σ.erase S τ hs).symm
      show (∃ x, (Tm.withStS S t).eval σ.erase = .ok x) ↔ (∃ x, t.eval σ'.erase = .ok x)
      rw [Tm.withStS_eval hs hk t ht, he]
    · cases h
  | .not φ, _, h => by
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact not_congr (Fml.withStS_holds hs σ' he φ hφ)
  | .and φ ψ, _, h => by
    obtain ⟨φ', hφ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact and_congr (Fml.withStS_holds hs σ' he φ hφ) (Fml.withStS_holds hs σ' he ψ hψ)
  | .imp φ ψ, _, h => by
    obtain ⟨φ', hφ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact imp_congr (Fml.withStS_holds hs σ' he φ hφ) (Fml.withStS_holds hs σ' he ψ hψ)
  | .upd .., _, h | .modal .., _, h | .havoc _, _, h | .all .., _, h | .bind .., _, h
  | .anon .., _, h => by cases h

/-- `[{storage := S}] φ ⇝ φ[S/storage]` on the update in front. -/
def Fml.applyStTop {Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) : Option (Fml C Γ) :=
  match m, U with
  | .box, .snoc .nil (.storage S) => Fml.withStS S φ
  | _, _ => none

theorem Fml.applyStTop_sound {Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ}
    {ψ : Fml C Γ} (h : Fml.applyStTop m U φ = some ψ) (σ : State C Γ) (hψ : holds σ ψ) :
    holds σ (.upd m U φ) := by
  cases m with
  | diamond => cases h
  | box =>
    cases U with
    | snoc U e =>
      cases U with
      | nil =>
        cases e with
        | storage S =>
          have h : Fml.withStS S φ = some ψ := h
          show Modality.afterC .box _ ((Upd.snoc .nil (UpdElem.storage S)).apply σ.erase)
          cases hs : S.eval σ.erase with
          | error e =>
            rw [show (Upd.snoc .nil (UpdElem.storage S)).apply σ.erase = .error e from
              UpdElem.write_storage_error hs σ.erase]
            trivial
          | ok τ =>
            rw [show (Upd.snoc .nil (UpdElem.storage S)).apply σ.erase = .ok (σ.erase.afterSt τ) from
              UpdElem.write_storage_ok hs σ.erase]
            exact fun σ' he _ => (Fml.withStS_holds hs σ' he φ h).1 hψ
        | _ => cases h
      | _ => cases h
    | _ => cases h

/-- **`applyStorageBox`** past the program, at position `i` of the spine:
`[{storage := S}] φ ⇝ φ[S/storage]` (`Fml.applyStTop`). -/
def FmlRw.applyStorageBoxP (i : Nat) : FmlRw C :=
  FmlRw.atSpine (fun m U φ => Fml.applyStTop m U φ) (fun h σ hψ => Fml.applyStTop_sound h σ hψ) i

end WithSt

/-! ## Out of a thinning's scope

The locals a thinning `h : Thin Γ' Γ` drops, taken out of a term, an update
and a formula (`Tm.thinS?`, `Upd.thinIO`, `Fml.thinS?`): where nothing reads
them, the formula reads the state with them dropped (`EState.thin`) as the
formula read the state with them.  An update may also drop locals it
declares (`Upd.thinIO`'s `dropDecl`): every write to one goes, and a scope
end pops what is left of its scope (`Thin.popExt`).  A dropped write must
not halt (`Rhs.totalB`), so the update halts where it did. -/

section Thinning

/-- A position of `Δ` read in `Γ`, where the thinning keeps it. -/
def Idx.unwk? : {Γ Δ : Ctx} → {t : LTy} → Thin Γ Δ → Idx Δ t → Option (Idx Γ t)
  | _, _, _, .refl, i => some i
  | _, _, _, .keep _, .here => some .here
  | _, _, _, .keep h, .there i => (Idx.unwk? h i).map .there
  | _, _, _, .drop _, .here => none
  | _, _, _, .drop h, .there i => Idx.unwk? h i

theorem Idx.unwk?_wk : {Γ Δ : Ctx} → {t : LTy} → (h : Thin Γ Δ) → (i : Idx Δ t) →
    {j : Idx Γ t} → Idx.unwk? h i = some j → j.wk h = i
  | _, _, _, .refl, _, _, hj => by cases hj; exact Idx.wk_refl _
  | _, _, _, .keep _, .here, _, hj => by cases hj; rfl
  | _, _, _, .keep h, .there i, _, hj => by
    obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.1 hj
    exact congrArg Idx.there (Idx.unwk?_wk h i hj')
  | _, _, _, .drop _, .here, _, hj => by cases hj
  | _, _, _, .drop h, .there i, _, hj => congrArg Idx.there (Idx.unwk?_wk h i hj)

theorem Env.thin_set_some : {Γ Δ : Ctx} → (h : Thin Γ Δ) → {t : LTy} → (i : Idx Δ t) →
    {j : Idx Γ t} → Idx.unwk? h i = some j → (v : t.Denote C) → (e : Env C Δ) →
      Env.thin h (Env.set i v e) = Env.set j v (Env.thin h e)
  | _, _, .refl, _, _, _, hj, _, _ => by cases hj; rfl
  | _, _, .keep _, _, .here, _, hj, _, _ => by cases hj; rfl
  | _, _, .keep h, _, .there i, _, hj, v, e => by
    obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.1 hj
    show (e.1, Env.thin h (Env.set i v e.2)) = (e.1, Env.set j' v (Env.thin h e.2))
    rw [Env.thin_set_some h i hj' v e.2]
  | _, _, .drop _, _, .here, _, hj, _, _ => by cases hj
  | _, _, .drop h, _, .there i, _, hj, v, e => Env.thin_set_some h i hj v e.2

theorem Env.thin_set_none : {Γ Δ : Ctx} → (h : Thin Γ Δ) → {t : LTy} → (i : Idx Δ t) →
    Idx.unwk? h i = none → (v : t.Denote C) → (e : Env C Δ) →
      Env.thin h (Env.set i v e) = Env.thin h e
  | _, _, .refl, _, _, hj, _, _ => by cases hj
  | _, _, .keep _, _, .here, hj, _, _ => by cases hj
  | _, _, .keep h, _, .there i, hj, v, e => by
    show (e.1, Env.thin h (Env.set i v e.2)) = (e.1, Env.thin h e.2)
    rw [Env.thin_set_none h i (Option.map_eq_none_iff.1 hj) v e.2]
  | _, _, .drop _, _, .here, _, _, _ => rfl
  | _, _, .drop h, _, .there i, hj, v, e => Env.thin_set_none h i hj v e.2

/-- A scope end's top local over a thinning (`Thin.popExt`), the rest of
the scope end popped by `rec`. -/
def Thin.popCons {Δo Δ₁ : Ctx} {t : LTy} (h : Ext Δo Δ₁)
    (rec : {Δ' : Ctx} → Thin Δ' Δ₁ → (Δo' : Ctx) × Thin Δo' Δo × Ext Δo' Δ') :
    {Δ' : Ctx} → Thin Δ' (t :: Δ₁) → (Δo' : Ctx) × Thin Δo' Δo × Ext Δo' Δ'
  | _, .refl => ⟨_, .refl, .push h⟩
  | _, .keep th =>
    let r := rec th
    ⟨r.1, r.2.1, .push r.2.2⟩
  | _, .drop th => rec th

/-- A scope end over a thinning: what it pops of the locals kept, and the
thinning left. -/
def Thin.popExt {Δo : Ctx} : {Δ : Ctx} → Ext Δo Δ → {Δ' : Ctx} → Thin Δ' Δ →
    (Δo' : Ctx) × Thin Δo' Δo × Ext Δo' Δ'
  | _, .refl, _, th => ⟨_, th, .refl⟩
  | _, .push h, _, th => Thin.popCons h (fun th' => Thin.popExt h th') th

theorem Env.drop_popExt {Δo : Ctx} : {Δ : Ctx} → (h : Ext Δo Δ) → {Δ' : Ctx} → (th : Thin Δ' Δ) →
    (e : Env C Δ) →
      Env.drop (Thin.popExt h th).2.2 (Env.thin th e) = Env.thin (Thin.popExt h th).2.1 (Env.drop h e)
  | _, .refl, _, _, _ => rfl
  | _, .push _, _, .refl, _ => rfl
  | _, .push h, _, .keep th, e => Env.drop_popExt h th e.2
  | _, .push h, _, .drop th, e => Env.drop_popExt h th e.2

/-- `Thin.meet`'s step at a kept local. -/
def Thin.meetKeep {Δ₁ Δo₁ : Ctx} {t : LTy} (h : Thin Δo₁ Δ₁)
    (rec : {Δ' : Ctx} → Thin Δ' Δ₁ → (X : Ctx) × Thin X Δo₁ × Thin X Δ') :
    {Δ' : Ctx} → Thin Δ' (t :: Δ₁) → (X : Ctx) × Thin X (t :: Δo₁) × Thin X Δ'
  | _, .refl => ⟨_, .refl, .keep h⟩
  | _, .keep th =>
    let r := rec th
    ⟨_, .keep r.2.1, .keep r.2.2⟩
  | _, .drop th =>
    let r := rec th
    ⟨r.1, .drop r.2.1, r.2.2⟩

/-- `Thin.meet`'s step at a dropped local. -/
def Thin.meetDrop {Δ₁ Δo : Ctx} {t : LTy} (h : Thin Δo Δ₁)
    (rec : {Δ' : Ctx} → Thin Δ' Δ₁ → (X : Ctx) × Thin X Δo × Thin X Δ') :
    {Δ' : Ctx} → Thin Δ' (t :: Δ₁) → (X : Ctx) × Thin X Δo × Thin X Δ'
  | _, .refl => ⟨_, .refl, .drop h⟩
  | _, .keep th =>
    let r := rec th
    ⟨r.1, r.2.1, .drop r.2.2⟩
  | _, .drop th => rec th

/-- A scope's frame end (`Upd.drop`'s thinning `h`) over a thinning `th`:
the locals both keep, as kept by each. -/
def Thin.meet : {Δo Δ : Ctx} → Thin Δo Δ → {Δ' : Ctx} → Thin Δ' Δ →
    (X : Ctx) × Thin X Δo × Thin X Δ'
  | _, _, .refl, _, th => ⟨_, th, .refl⟩
  | _, _, .keep h, _, th => Thin.meetKeep h (fun th' => Thin.meet h th') th
  | _, _, .drop h, _, th => Thin.meetDrop h (fun th' => Thin.meet h th') th

theorem Env.thin_meet : {Δo Δ : Ctx} → (h : Thin Δo Δ) → {Δ' : Ctx} → (th : Thin Δ' Δ) →
    (e : Env C Δ) →
      Env.thin (Thin.meet h th).2.2 (Env.thin th e) = Env.thin (Thin.meet h th).2.1 (Env.thin h e)
  | _, _, .refl, _, _, _ => rfl
  | _, _, .keep _, _, .refl, _ => rfl
  | _, _, .keep h, _, .keep th, e => congrArg (Prod.mk e.1) (Env.thin_meet h th e.2)
  | _, _, .keep h, _, .drop th, e => Env.thin_meet h th e.2
  | _, _, .drop _, _, .refl, _ => rfl
  | _, _, .drop h, _, .keep th, e => Env.thin_meet h th e.2
  | _, _, .drop h, _, .drop th, e => Env.thin_meet h th e.2

variable {Γ Γ' : Ctx}

/-- A term of `Γ` read in `Γ'`, where it reads no local the thinning drops. -/
def Tm.thinS? (h : Thin Γ' Γ) : {s : Srt} → Tm C Γ s → Option (Tm C Γ' s)
  | _, .pvV i => (Idx.unwk? h i).map .pvV
  | _, .pvP i => (Idx.unwk? h i).map .pvP
  | _, .pvS i => (Idx.unwk? h i).map .pvS
  | _, .pvI i => (Idx.unwk? h i).map .pvI
  | _, .netOf i a => do pure (.netOf (← Idx.unwk? h i) (← Tm.thinS? h a))
  | _, .app0 o => some (.app0 o)
  | _, .app1 o ho x => (Tm.thinS? h x).map (.app1 o ho)
  | _, .app2 o x y => do pure (.app2 o (← Tm.thinS? h x) (← Tm.thinS? h y))
  | _, .app3 o x y z => do pure (.app3 o (← Tm.thinS? h x) (← Tm.thinS? h y) (← Tm.thinS? h z))

theorem Env.get_unwk? {h : Thin Γ' Γ} {t : LTy} {i : Idx Γ t} {j : Idx Γ' t}
    (hj : Idx.unwk? h i = some j) (e : Env C Γ) : Env.get j (Env.thin h e) = Env.get i e := by
  rw [Env.get_thin, Idx.unwk?_wk h i hj]

/-- **A term that reads no dropped local reads alike with them dropped.** -/
theorem Tm.eval_thinS? (h : Thin Γ' Γ) (σ : EState C Γ) :
    {s : Srt} → (t : Tm C Γ s) → {t' : Tm C Γ' s} → Tm.thinS? h t = some t' →
      t'.eval (σ.thin h) = t.eval σ
  | _, .pvV i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    show pure (Env.get j (Env.thin h σ.env)) = pure (Env.get i σ.env)
    rw [Env.get_unwk? hj]
  | _, .pvP i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    show aliasPath (σ.thin h) j = aliasPath σ i
    simp only [aliasPath, EState.thin, EState.withEnv, Env.get_unwk? hj]
  | _, .pvS i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    show pure { (σ.thin h).glob with storage := Env.get j (Env.thin h σ.env) } =
      pure { σ.glob with storage := Env.get i σ.env }
    rw [Env.get_unwk? hj]; rfl
  | _, .pvI i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    show memRef (σ.thin h) j = memRef σ i
    simp only [memRef, EState.thin, EState.withEnv, Env.get_unwk? hj]
  | _, .netOf i a, _, ht => by
    obtain ⟨j, hj, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨a', ha, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    show (do
        let l : List (Int × Int) := Env.get j (Env.thin h σ.env)
        pure (Semantics.Value.int ((Semantics.lookupBy (← (← a'.eval (σ.thin h)).asInt) l).getD 0))) =
      (do
        let l : List (Int × Int) := Env.get i σ.env
        pure (Semantics.Value.int ((Semantics.lookupBy (← (← a.eval σ).asInt) l).getD 0)))
    rw [Env.get_unwk? hj, Tm.eval_thinS? h σ a ha]
  | _, .app0 _, _, ht => by cases ht; rfl
  | _, .app1 o ho x, _, ht => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 ht
    show o.eval (σ.thin h).glob (x'.eval (σ.thin h)) = o.eval σ.glob (x.eval σ)
    rw [Tm.eval_thinS? h σ x hx]; rfl
  | _, .app2 o x y, _, ht => by
    obtain ⟨x', hx, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨y', hy, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    show o.eval (σ.thin h).glob (x'.eval (σ.thin h)) (y'.eval (σ.thin h)) =
      o.eval σ.glob (x.eval σ) (y.eval σ)
    rw [Tm.eval_thinS? h σ x hx, Tm.eval_thinS? h σ y hy]; rfl
  | _, .app3 o x y z, _, ht => by
    obtain ⟨x', hx, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨y', hy, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨z', hz, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    show o.eval (σ.thin h).glob (x'.eval (σ.thin h)) (y'.eval (σ.thin h)) (z'.eval (σ.thin h)) =
      o.eval σ.glob (x.eval σ) (y.eval σ) (z.eval σ)
    rw [Tm.eval_thinS? h σ x hx, Tm.eval_thinS? h σ y hy, Tm.eval_thinS? h σ z hz]; rfl

/-- **A term that reads no dropped local denotes alike with them dropped.** -/
theorem Tm.denote_thinS? (h : Thin Γ' Γ) (σ : EState C Γ) :
    {s : Srt} → (t : Tm C Γ s) → {t' : Tm C Γ' s} → Tm.thinS? h t = some t' →
      t'.denote (σ.thin h) = t.denote σ
  | _, .pvV i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    show Theory.StValue.prim (Env.get j (Env.thin h σ.env)) = .prim (Env.get i σ.env)
    rw [Env.get_unwk? hj]
  | _, .pvP i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.denote, aliasPath, EState.thin, EState.withEnv, Env.get_unwk? hj]
  | _, .pvS i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.denote, EState.thin, EState.withEnv, Env.get_unwk? hj]
  | _, .pvI i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    rfl
  | _, .netOf i a, _, ht => by
    obtain ⟨j, hj, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨a', ha, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    have ha' := Tm.denote_thinS? h σ a ha
    simp only [EState.thin, EState.withEnv] at ha'
    simp only [Tm.denote, EState.thin, EState.withEnv, Env.get_unwk? hj, ha']
  | _, .app0 _, _, ht => by cases ht; rfl
  | _, .app1 o ho x, _, ht => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 ht
    show o.denote (σ.thin h).glob (x'.denote (σ.thin h)) = o.denote σ.glob (x.denote σ)
    rw [Tm.denote_thinS? h σ x hx]; rfl
  | _, .app2 o x y, _, ht => by
    obtain ⟨x', hx, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨y', hy, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    show o.denote (σ.thin h).glob (x'.eval (σ.thin h)) (y'.eval (σ.thin h)) (x'.denote (σ.thin h))
        (y'.denote (σ.thin h)) = o.denote σ.glob (x.eval σ) (y.eval σ) (x.denote σ) (y.denote σ)
    rw [Tm.denote_thinS? h σ x hx, Tm.denote_thinS? h σ y hy, Tm.eval_thinS? h σ x hx,
      Tm.eval_thinS? h σ y hy]; rfl
  | _, .app3 o x y z, _, ht => by
    obtain ⟨x', hx, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨y', hy, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨z', hz, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    show o.denote (x'.denote (σ.thin h)) (y'.denote (σ.thin h)) (z'.denote (σ.thin h)) =
      o.denote (x.denote σ) (y.denote σ) (z.denote σ)
    rw [Tm.denote_thinS? h σ x hx, Tm.denote_thinS? h σ y hy, Tm.denote_thinS? h σ z hz]

/-- A right-hand side of `Γ` read in `Γ'`. -/
def Rhs.thinS? (h : Thin Γ' Γ) : {t : LTy} → Rhs C Γ t → Option (Rhs C Γ' t)
  | _, .val t => (Tm.thinS? h t).map .val
  | _, .path p => (Tm.thinS? h p).map .path
  | _, .unset => some .unset
  | _, .mref i => (Tm.thinS? h i).map .mref
  | _, .store s => (Tm.thinS? h s).map .store
  | _, .saveNet => some .saveNet
  | _, .saveNetMt => some .saveNetMt

theorem Rhs.eval_thinS? (h : Thin Γ' Γ) (σ : EState C Γ) :
    {t : LTy} → (r : Rhs C Γ t) → {r' : Rhs C Γ' t} → Rhs.thinS? h r = some r' →
      r'.eval (σ.thin h) = r.eval σ
  | _, .val t, _, hr => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hr
    exact Tm.eval_thinS? h σ t ht
  | _, .path p, _, hr => by
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.1 hr
    show (do pure (some (← p'.eval (σ.thin h)))) = (do pure (some (← p.eval σ)))
    rw [Tm.eval_thinS? h σ p hp]
  | _, .unset, _, hr => by cases hr; rfl
  | _, .mref i, _, hr => by
    obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.1 hr
    show (do pure (some (← i'.eval (σ.thin h)))) = (do pure (some (← i.eval σ)))
    rw [Tm.eval_thinS? h σ i hi]
  | _, .store s, _, hr => by
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 hr
    show (do pure (← s'.eval (σ.thin h)).storage) = (do pure (← s.eval σ).storage)
    rw [Tm.eval_thinS? h σ s hs]
  | _, .saveNet, _, hr => by cases hr; rfl
  | _, .saveNetMt, _, hr => by cases hr; rfl

/-- An element that sets no local, its right-hand sides read in `Γ'`, at
another target context. -/
def UpdElem.thinG? (h : Thin Γ' Γ) {Δ Δ' : Ctx} : UpdElem C Γ Δ → Option (UpdElem C Γ' Δ')
  | .local .. => none
  | .storage s => (Tm.thinS? h s).map .storage
  | .memory m => (Tm.thinS? h m).map .memory
  | .selfBalance op a => (Tm.thinS? h a).map (.selfBalance op)
  | .net r op a => do pure (.net (← Tm.thinS? h r) op (← Tm.thinS? h a))
  | .pay r a => do pure (.pay (← Tm.thinS? h r) (← Tm.thinS? h a))
  | .netMt r a => do pure (.netMt (← Tm.thinS? h r) (← Tm.thinS? h a))
  | .setBalance a => (Tm.thinS? h a).map .setBalance

/-- An element that sets no local, written into a state with locals
dropped, writes what it wrote with them dropped. -/
theorem UpdElem.write_thinG? (h : Thin Γ' Γ) (σ₀ : EState C Γ) {Δ Δ' : Ctx} (th : Thin Δ' Δ)
    (τ : EState C Δ) : (e : UpdElem C Γ Δ) → {e' : UpdElem C Γ' Δ'} → e.thinG? h = some e' →
      e'.write (σ₀.thin h) (τ.thin th) = (e.write σ₀ τ).map (EState.thin th)
  | .local .., _, he => by cases he
  | .storage s, _, he => by
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 he
    simp only [UpdElem.write, Tm.eval_thinS? h σ₀ s hs]
    cases s.eval σ₀ <;> rfl
  | .memory m, _, he => by
    obtain ⟨m', hm, rfl⟩ := Option.map_eq_some_iff.1 he
    simp only [UpdElem.write, Tm.eval_thinS? h σ₀ m hm]
    cases m.eval σ₀ <;> rfl
  | .selfBalance op a, _, he => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 he
    simp only [UpdElem.write, Tm.eval_thinS? h σ₀ a ha]
    cases a.eval σ₀ with
    | error => rfl
    | ok v => cases v <;> rfl
  | .net r op a, _, he => by
    obtain ⟨r', hr, he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨a', ha, he⟩ := Option.bind_eq_some_iff.1 he
    cases he
    simp only [UpdElem.write, Tm.eval_thinS? h σ₀ r hr, Tm.eval_thinS? h σ₀ a ha]
    cases r.eval σ₀ with
    | error => rfl
    | ok v =>
      cases v with
      | bool => rfl
      | int =>
        cases a.eval σ₀ with
        | error => rfl
        | ok w => cases w <;> rfl
  | .pay r a, _, he => by
    obtain ⟨r', hr, he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨a', ha, he⟩ := Option.bind_eq_some_iff.1 he
    cases he
    simp only [UpdElem.write, Tm.eval_thinS? h σ₀ r hr, Tm.eval_thinS? h σ₀ a ha]
    cases r.eval σ₀ with
    | error => rfl
    | ok v =>
      cases v with
      | bool => rfl
      | int =>
        cases a.eval σ₀ with
        | error => rfl
        | ok w =>
          cases w with
          | bool => rfl
          | int =>
            simp only [bind, Except.bind, Semantics.Value.asInt, pure, Except.pure]
            split <;> rfl
  | .netMt r a, _, he => by
    obtain ⟨r', hr, he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨a', ha, he⟩ := Option.bind_eq_some_iff.1 he
    cases he
    simp only [UpdElem.write, Tm.eval_thinS? h σ₀ r hr, Tm.eval_thinS? h σ₀ a ha]
    cases r.eval σ₀ with
    | error => rfl
    | ok v =>
      cases v with
      | bool => rfl
      | int =>
        cases a.eval σ₀ with
        | error => rfl
        | ok w => cases w <;> rfl
  | .setBalance a, _, he => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 he
    simp only [UpdElem.write, Tm.eval_thinS? h σ₀ a ha]
    cases a.eval σ₀ with
    | error => rfl
    | ok v => cases v <;> rfl

/-- A scope end, none where it pops nothing. -/
def Upd.popOrSkip {Δ' : Ctx} : {Δ : Ctx} → Upd C Γ' Δ → Ext Δ' Δ → Upd C Γ' Δ'
  | _, U, .refl => U
  | _, U, .push h => .pop U (.push h)

theorem Upd.apply_popOrSkip {Δ' : Ctx} (σ : EState C Γ') :
    {Δ : Ctx} → (U : Upd C Γ' Δ) → (h : Ext Δ' Δ) → (U.popOrSkip h).apply σ = (U.apply σ).map (EState.drop h)
  | _, U, .refl => by
    show U.apply σ = _
    cases U.apply σ <;> rfl
  | _, _, .push _ => rfl

/-- A frame end, none where it drops nothing. -/
def Upd.dropOrSkip {Δ' : Ctx} : {Δ : Ctx} → Upd C Γ' Δ → Thin Δ' Δ → Upd C Γ' Δ'
  | _, U, .refl => U
  | _, U, .keep h => .drop U (.keep h)
  | _, U, .drop h => .drop U (.drop h)

theorem Upd.apply_dropOrSkip {Δ' : Ctx} (σ : EState C Γ') :
    {Δ : Ctx} → (U : Upd C Γ' Δ) → (h : Thin Δ' Δ) →
      (U.dropOrSkip h).apply σ = (U.apply σ).map (EState.thin h)
  | _, U, .refl => by
    show U.apply σ = _
    cases U.apply σ <;> rfl
  | _, _, .keep _ | _, _, .drop _ => rfl

/-- An update thinned: the context it leaves, that context's thinning into
the update's, and the update. -/
structure UThin (C : Contract) (Γ' Δ : Ctx) where
  {Δ' : Ctx}
  th : Thin Δ' Δ
  U : Upd C Γ' Δ'

/-- `Thin.norm`'s step at a kept local: a thinning that keeps everything
below is the identity. -/
def Thin.normKeep {t : LTy} : {Δ' Δ : Ctx} → Thin Δ' Δ → Thin (t :: Δ') (t :: Δ)
  | _, _, .refl => .refl
  | _, _, .keep h => .keep (.keep h)
  | _, _, .drop h => .keep (.drop h)

/-- A thinning that drops nothing written as the identity. -/
def Thin.norm : {Δ' Δ : Ctx} → Thin Δ' Δ → Thin Δ' Δ
  | _, _, .refl => .refl
  | _, _, .keep h => Thin.normKeep (Thin.norm h)
  | _, _, .drop h => .drop (Thin.norm h)

theorem Env.thin_normKeep {t : LTy} {Δ' Δ : Ctx} (h : Thin Δ' Δ) (e : Env C (t :: Δ)) :
    Env.thin (Thin.normKeep h) e = (e.1, Env.thin h e.2) := by
  cases h <;> rfl

theorem Env.thin_norm : {Δ' Δ : Ctx} → (h : Thin Δ' Δ) → (e : Env C Δ) →
    Env.thin (Thin.norm h) e = Env.thin h e
  | _, _, .refl, _ => rfl
  | _, _, .keep h, e => by
    show Env.thin (Thin.normKeep (Thin.norm h)) e = (e.1, Env.thin h e.2)
    rw [Env.thin_normKeep, Env.thin_norm h e.2]
  | _, _, .drop h, e => Env.thin_norm h e.2

/-- The update, where the thinning is the identity. -/
def Thin.closeU {Δ' Δ : Ctx} : Thin Δ' Δ → Upd C Γ' Δ' → Option (Upd C Γ' Δ)
  | .refl, U => some U
  | .keep _, _ => none
  | .drop _, _ => none

/-- The update, where its thinning drops nothing. -/
def UThin.close? {Δ : Ctx} (R : UThin C Γ' Δ) : Option (Upd C Γ' Δ) :=
  Thin.closeU (Thin.norm R.th) R.U

theorem Thin.closeU_apply {Δ' Δ : Ctx} {n : Thin Δ' Δ} {U : Upd C Γ' Δ'} {U' : Upd C Γ' Δ}
    (h : Thin.closeU n U = some U') (σ : EState C Γ') (x : Res (EState C Δ))
    (hx : U.apply σ = x.map (EState.thin n)) : U'.apply σ = x := by
  cases n with
  | refl =>
    cases h
    rw [hx]
    cases x <;> rfl
  | keep _ => cases h
  | drop _ => cases h

theorem UThin.close?_apply {Δ : Ctx} {R : UThin C Γ' Δ} {U' : Upd C Γ' Δ} (h : R.close? = some U')
    (σ : EState C Γ') (x : Res (EState C Δ)) (hx : R.U.apply σ = x.map (EState.thin R.th)) :
    U'.apply σ = x := by
  refine Thin.closeU_apply h σ x ?_
  rw [hx]
  have he : EState.thin (Thin.norm R.th) = EState.thin (C := C) R.th := by
    funext τ
    simp only [EState.thin, Env.thin_norm]
  rw [he]

/-- **An update with locals dropped**: its right-hand sides read in `Γ'`
(`h`), the declarations `dropDecl` names left out (counted from the first),
every write to a dropped local left out, which must not halt, and each scope
end popping what is left of its scope.  The number of declarations seen, and
the update. -/
def Upd.thinIO (h : Thin Γ' Γ) (dropDecl : Nat → Bool) : {Δ : Ctx} → Upd C Γ Δ →
    Option (Nat × UThin C Γ' Δ)
  | _, .nil => some (0, ⟨h, .nil⟩)
  | _, .snoc U e => do
    let (n, R) ← Upd.thinIO h dropDecl U
    match e with
    | .local i r =>
      match Idx.unwk? R.th i with
      | some j => pure (n, ⟨R.th, .snoc R.U (.local j (← Rhs.thinS? h r))⟩)
      | none => if r.totalB then pure (n, R) else none
    | e => pure (n, ⟨R.th, .snoc R.U (← e.thinG? h)⟩)
  | _, .decl U y r => do
    let (n, R) ← Upd.thinIO h dropDecl U
    if dropDecl n then
      if r.totalB then pure (n + 1, ⟨.drop R.th, R.U⟩) else none
    else pure (n + 1, ⟨.keep R.th, .decl R.U y (← Rhs.thinS? h r)⟩)
  | _, .pop U e => do
    let (n, R) ← Upd.thinIO h dropDecl U
    let r := Thin.popExt e R.th
    pure (n, ⟨r.2.1, R.U.popOrSkip r.2.2⟩)
  | _, .drop U e => do
    let (n, R) ← Upd.thinIO h dropDecl U
    let r := Thin.meet e R.th
    pure (n, ⟨r.2.1, R.U.dropOrSkip r.2.2⟩)

/-- **The thinned update runs as the update, its locals thinned.** -/
theorem Upd.apply_thinIO (h : Thin Γ' Γ) (dd : Nat → Bool) (σ₀ : EState C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → {n : Nat} → {R : UThin C Γ' Δ} →
      U.thinIO h dd = some (n, R) → R.U.apply (σ₀.thin h) = (U.apply σ₀).map (EState.thin R.th)
  | _, .nil, _, _, hU => by cases hU; rfl
  | _, .snoc U e, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    have ih := Upd.apply_thinIO h dd σ₀ U hR
    cases e with
    | «local» i r =>
      simp only at hU
      split at hU
      · rename_i j hj
        obtain ⟨r', hr, hU⟩ := Option.bind_eq_some_iff.1 hU
        cases hU
        show (do (UpdElem.local j r').write (σ₀.thin h) (← R.U.apply (σ₀.thin h))) =
          (do (UpdElem.local i r).write σ₀ (← U.apply σ₀)).map _
        rw [ih]
        cases U.apply σ₀ with
        | error => rfl
        | ok τ =>
          show (do pure ((τ.thin R.th).setLocal j (← r'.eval (σ₀.thin h)))) =
            (do pure (τ.setLocal i (← r.eval σ₀))).map _
          rw [Rhs.eval_thinS? h σ₀ r hr]
          cases r.eval σ₀ with
          | error => rfl
          | ok v =>
            show Except.ok ((τ.thin R.th).withEnv (Env.set j v (Env.thin R.th τ.env))) =
              Except.ok ((τ.withEnv (Env.set i v τ.env)).withEnv (Env.thin R.th (Env.set i v τ.env)))
            rw [Env.thin_set_some R.th i hj v τ.env]; rfl
      · rename_i hj
        split at hU
        · rename_i ht
          cases hU
          rw [ih]
          obtain ⟨v, hv⟩ := Rhs.totalB_eval σ₀ r ht
          show Except.map _ (U.apply σ₀) = Except.map _ (do (UpdElem.local i r).write σ₀ (← U.apply σ₀))
          cases U.apply σ₀ with
          | error => rfl
          | ok τ =>
            show Except.ok _ = (do pure (τ.setLocal i (← r.eval σ₀))).map _
            rw [hv]
            show Except.ok (τ.withEnv (Env.thin _ τ.env)) =
              Except.ok ((τ.withEnv (Env.set i v τ.env)).withEnv (Env.thin _ (Env.set i v τ.env)))
            rw [Env.thin_set_none _ i hj v τ.env]; rfl
        · cases hU
    | _ =>
      obtain ⟨e', he, hU⟩ := Option.bind_eq_some_iff.1 hU
      cases hU
      show (do e'.write (σ₀.thin h) (← R.U.apply (σ₀.thin h))) = (do UpdElem.write σ₀ _ (← U.apply σ₀)).map _
      rw [ih]
      cases U.apply σ₀ with
      | error => rfl
      | ok τ => exact UpdElem.write_thinG? h σ₀ R.th τ _ he
  | _, .decl U y r, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    have ih := Upd.apply_thinIO h dd σ₀ U hR
    simp only at hU
    split at hU
    · split at hU
      · rename_i ht
        cases hU
        rw [ih]
        obtain ⟨v, hv⟩ := Rhs.totalB_eval σ₀ r ht
        show _ = (do let τ ← U.apply σ₀; pure (τ.push (← r.eval σ₀))).map _
        rw [hv]
        cases U.apply σ₀ <;> rfl
      · cases hU
    · obtain ⟨r', hr, hU⟩ := Option.bind_eq_some_iff.1 hU
      cases hU
      show (do let τ ← R.U.apply (σ₀.thin h); pure (τ.push (← r'.eval (σ₀.thin h)))) =
        (do let τ ← U.apply σ₀; pure (τ.push (← r.eval σ₀))).map _
      rw [ih, Rhs.eval_thinS? h σ₀ r hr]
      cases U.apply σ₀ with
      | error => rfl
      | ok τ => cases r.eval σ₀ <;> rfl
  | _, .pop U e, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    have ih := Upd.apply_thinIO h dd σ₀ U hR
    cases hU
    show (R.U.popOrSkip _).apply (σ₀.thin h) = ((U.apply σ₀).map (EState.drop e)).map _
    rw [Upd.apply_popOrSkip, ih]
    cases U.apply σ₀ with
    | error => rfl
    | ok τ =>
      show Except.ok ((τ.withEnv (Env.thin R.th τ.env)).withEnv (Env.drop _ (Env.thin R.th τ.env))) =
        Except.ok ((τ.withEnv (Env.drop e τ.env)).withEnv (Env.thin _ (Env.drop e τ.env)))
      rw [Env.drop_popExt e R.th τ.env]; rfl
  | _, .drop U e, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    have ih := Upd.apply_thinIO h dd σ₀ U hR
    cases hU
    show (R.U.dropOrSkip _).apply (σ₀.thin h) = ((U.apply σ₀).map (EState.thin e)).map _
    rw [Upd.apply_dropOrSkip, ih]
    cases U.apply σ₀ with
    | error => rfl
    | ok τ =>
      show Except.ok ((τ.withEnv (Env.thin R.th τ.env)).withEnv (Env.thin _ (Env.thin R.th τ.env))) =
        Except.ok ((τ.withEnv (Env.thin e τ.env)).withEnv (Env.thin _ (Env.thin e τ.env)))
      rw [Env.thin_meet e R.th τ.env]; rfl

/-- A first-order formula of `Γ` read in `Γ'` (no update, no modality). -/
def Fml.thinFO? : {Γ' Γ : Ctx} → Thin Γ' Γ → Fml C Γ → Option (Fml C Γ')
  | _, _, _, .tt => some .tt
  | _, _, h, .eq a b => do pure (.eq (← Tm.thinS? h a) (← Tm.thinS? h b))
  | _, _, h, .defined t => (Tm.thinS? h t).map .defined
  | _, _, h, .not φ => (Fml.thinFO? h φ).map .not
  | _, _, h, .and φ ψ => do pure (.and (← Fml.thinFO? h φ) (← Fml.thinFO? h ψ))
  | _, _, h, .imp φ ψ => do pure (.imp (← Fml.thinFO? h φ) (← Fml.thinFO? h ψ))
  | _, _, h, .all x p φ => (Fml.thinFO? (.keep h) φ).map (.all x p)
  | _, _, _, _ => none

/-- **A first-order formula that reads no dropped local holds alike with
them dropped.** -/
theorem Fml.thinFO?_holds : {Γ' Γ : Ctx} → (h : Thin Γ' Γ) → (φ : Fml C Γ) → {φ' : Fml C Γ'} →
    Fml.thinFO? h φ = some φ' → ∀ σ : State C Γ, (holds (σ.thin h) φ' ↔ holds σ φ)
  | _, _, _, .tt, _, hφ, _ => by cases hφ; exact Iff.rfl
  | _, _, h, .eq a b, _, hφ, σ => by
    obtain ⟨a', ha, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    obtain ⟨b', hb, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    cases hφ
    show Theory.StValue.Equiv (a'.denote (σ.thin h).erase) (b'.denote (σ.thin h).erase) ↔
      Theory.StValue.Equiv (a.denote σ.erase) (b.denote σ.erase)
    rw [State.thin_erase, Tm.denote_thinS? h σ.erase a ha, Tm.denote_thinS? h σ.erase b hb]
  | _, _, h, .defined t, _, hφ, σ => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hφ
    show (∃ x, t'.eval (σ.thin h).erase = .ok x) ↔ (∃ x, t.eval σ.erase = .ok x)
    rw [State.thin_erase, Tm.eval_thinS? h σ.erase t ht]
  | _, _, h, .not φ, _, hφ, σ => by
    obtain ⟨φ', hφ', rfl⟩ := Option.map_eq_some_iff.1 hφ
    exact not_congr (Fml.thinFO?_holds h φ hφ' σ)
  | _, _, h, .and φ ψ, _, hφ, σ => by
    obtain ⟨φ', h₁, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    obtain ⟨ψ', h₂, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    cases hφ
    exact and_congr (Fml.thinFO?_holds h φ h₁ σ) (Fml.thinFO?_holds h ψ h₂ σ)
  | _, _, h, .imp φ ψ, _, hφ, σ => by
    obtain ⟨φ', h₁, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    obtain ⟨ψ', h₂, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    cases hφ
    exact imp_congr (Fml.thinFO?_holds h φ h₁ σ) (Fml.thinFO?_holds h ψ h₂ σ)
  | _, _, h, .all x p φ, _, hφ, σ => by
    obtain ⟨φ', hφ', rfl⟩ := Option.map_eq_some_iff.1 hφ
    exact forall_congr' fun v => Fml.thinFO?_holds (.keep h) φ hφ' (σ.push (t := .val p) v)
  | _, _, _, .upd .., _, hφ, _ | _, _, _, .modal .., _, hφ, _ | _, _, _, .havoc _, _, hφ, _
  | _, _, _, .bind .., _, hφ, _ | _, _, _, .anon .., _, hφ, _ => by cases hφ

/-- A formula of `Γ` read in `Γ'`: first-order where it is read both ways
(under `¬`, left of `→`), and through updates and binders elsewhere. -/
def Fml.thinS? : {Γ' Γ : Ctx} → Thin Γ' Γ → Fml C Γ → Option (Fml C Γ')
  | _, _, _, .tt => some .tt
  | _, _, h, .eq a b => do pure (.eq (← Tm.thinS? h a) (← Tm.thinS? h b))
  | _, _, h, .defined t => (Tm.thinS? h t).map .defined
  | _, _, h, .not φ => (Fml.thinFO? h φ).map .not
  | _, _, h, .and φ ψ => do pure (.and (← Fml.thinS? h φ) (← Fml.thinS? h ψ))
  | _, _, h, .imp φ ψ => do pure (.imp (← Fml.thinFO? h φ) (← Fml.thinS? h ψ))
  | _, _, h, .upd m U φ => do
    let (_, R) ← U.thinIO h (fun _ => false)
    match R.close? with
    | some U' => pure (.upd m U' φ)
    | none => pure (.upd m R.U (← Fml.thinS? R.th φ))
  | _, _, h, .all x p φ => (Fml.thinS? (.keep h) φ).map (.all x p)
  | _, _, h, .bind m x t φ => (Fml.thinS? (.keep h) φ).map (.bind m x t)
  | _, _, _, _ => none

/-- **A formula that reads no dropped local holds where it holds with them
dropped.** -/
theorem Fml.thinS?_holds : {Γ' Γ : Ctx} → (h : Thin Γ' Γ) → (φ : Fml C Γ) → {φ' : Fml C Γ'} →
    Fml.thinS? h φ = some φ' → ∀ σ : State C Γ, holds (σ.thin h) φ' → holds σ φ
  | _, _, _, .tt, _, _, _, _ => trivial
  | _, _, h, .eq a b, _, hφ, σ, hs => by
    obtain ⟨a', ha, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    obtain ⟨b', hb, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    cases hφ
    exact (Fml.thinFO?_holds h (.eq a b) (by simp only [Fml.thinFO?, ha, hb]; rfl) σ).1 hs
  | _, _, h, .defined t, _, hφ, σ, hs => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hφ
    exact (Fml.thinFO?_holds h (.defined t) (by simp only [Fml.thinFO?, ht]; rfl) σ).1 hs
  | _, _, h, .not φ, _, hφ, σ, hs => by
    obtain ⟨φ', hφ', rfl⟩ := Option.map_eq_some_iff.1 hφ
    exact fun hn => hs ((Fml.thinFO?_holds h φ hφ' σ).2 hn)
  | _, _, h, .and φ ψ, _, hφ, σ, hs => by
    obtain ⟨φ', h₁, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    obtain ⟨ψ', h₂, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    cases hφ
    exact ⟨Fml.thinS?_holds h φ h₁ σ hs.1, Fml.thinS?_holds h ψ h₂ σ hs.2⟩
  | _, _, h, .imp φ ψ, _, hφ, σ, hs => by
    obtain ⟨φ', h₁, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    obtain ⟨ψ', h₂, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    cases hφ
    exact fun ha => Fml.thinS?_holds h ψ h₂ σ (hs ((Fml.thinFO?_holds h φ h₁ σ).2 ha))
  | _, _, h, .upd m U φ, _, hφ, σ, hs => by
    obtain ⟨⟨n, R⟩, hR, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    have hap := Upd.apply_thinIO h (fun _ => false) σ.erase U hR
    show m.afterC _ (U.apply σ.erase)
    simp only at hφ
    split at hφ
    · rename_i U' hc
      cases hφ
      have hs : m.afterC _ (U'.apply (σ.thin h).erase) := hs
      rw [State.thin_erase, UThin.close?_apply hc _ _ hap] at hs
      exact hs
    · obtain ⟨φ', h₁, hφ⟩ := Option.bind_eq_some_iff.1 hφ
      cases hφ
      have hs : m.afterC _ (R.U.apply (σ.thin h).erase) := hs
      rw [State.thin_erase, hap] at hs
      cases hU : U.apply σ.erase with
      | error e => rw [hU] at hs; exact hs
      | ok τ =>
        rw [hU] at hs
        intro σ' he hH
        exact Fml.thinS?_holds R.th φ h₁ σ' (hs (σ'.thin R.th) (by rw [State.thin_erase, he]) hH)
  | _, _, h, .all x p φ, _, hφ, σ, hs => by
    obtain ⟨φ', hφ', rfl⟩ := Option.map_eq_some_iff.1 hφ
    exact fun v => Fml.thinS?_holds (.keep h) φ hφ' (σ.push (t := .val p) v) (hs v)
  | _, _, h, .bind m x t φ, _, hφ, σ, hs => by
    obtain ⟨φ', hφ', rfl⟩ := Option.map_eq_some_iff.1 hφ
    exact Modality.forallB_intro fun v =>
      Fml.thinS?_holds (.keep h) φ hφ' (σ.push v) (Modality.forallB_all hs v)
  | _, _, _, .modal .., _, hφ, _, _ | _, _, _, .havoc _, _, hφ, _, _
  | _, _, _, .anon .., _, hφ, _, _ => by cases hφ

end Thinning

/-! ## `simplifyUpdate` past the program

`{U}_m ψ` with the locals `U` declares and no one reads afterwards dropped,
with every write to them (`Upd.thinIO`): those `U` pops itself, and those
`ψ` does not read (`Fml.thinS?`, `ψ` read without them), the erasure's
`dropEffectless` (`NFml.simplifyAt`) on the scoped line.  Before, the scope
ends `ψ` begins with are merged into `U` (`Fml.absorbPops`) and the writes
a later one shadows dropped (`Upd.shadow`); a hidden binder in front of
`U` whose local `U` sets first is absorbed (`Upd.absorb`), so its local
goes too where nothing reads it.  A dropped write must not halt
(`Rhs.totalB`). -/

section SimpPast

variable {Γ : Ctx}

/-- Which positions of `Δ` a thinning keeps, the newest first. -/
def Thin.mask : {Δ' Δ : Ctx} → Thin Δ' Δ → List Bool
  | _, Δ, .refl => List.replicate Δ.length true
  | _, _, .keep h => true :: Thin.mask h
  | _, _, .drop h => false :: Thin.mask h

/-- The declarations an update ends itself, counted from the first: a
stack of the context's positions (`some k` the `k`th declaration), popped
at each scope end and thinned at each drop. -/
def Upd.declStack : {Δ : Ctx} → Upd C Γ Δ → Nat × List (Option Nat) × List Nat
  | _, .nil => (0, List.replicate Γ.length none, [])
  | _, .snoc U _ => Upd.declStack U
  | _, .decl U _ _ =>
    let r := Upd.declStack U
    (r.1 + 1, some r.1 :: r.2.1, r.2.2)
  | _, .pop U h =>
    let r := Upd.declStack U
    (r.1, r.2.1.drop h.depth, r.2.2 ++ (r.2.1.take h.depth).filterMap id)
  | _, .drop U h =>
    let r := Upd.declStack U
    let ps := r.2.1.zip (Thin.mask h)
    (r.1, (ps.filter (·.2)).map (·.1), r.2.2 ++ (ps.filter (!·.2)).filterMap (·.1))

/-- `{U}_m ψ` with the declarations of `U` that `drop` names dropped, `ψ`
read without those still in scope. -/
def Fml.dropDeclsTop {Δ : Ctx} (drop : Nat → Bool) (m : Modality) (U : Upd C Γ Δ) (ψ : Fml C Δ) :
    Option (Fml C Γ) := do
  let (_, R) ← U.thinIO .refl drop
  match R.close? with
  | some U' => pure (.upd m U' ψ)
  | none => pure (.upd m R.U (← Fml.thinS? R.th ψ))

theorem Fml.dropDeclsTop_sound {Δ : Ctx} {drop : Nat → Bool} {m : Modality} {U : Upd C Γ Δ}
    {ψ : Fml C Δ} {φ : Fml C Γ} (h : Fml.dropDeclsTop drop m U ψ = some φ) (σ : State C Γ)
    (hφ : holds σ φ) : holds σ (.upd m U ψ) := by
  obtain ⟨⟨n, R⟩, hR, h⟩ := Option.bind_eq_some_iff.1 h
  have hap := Upd.apply_thinIO .refl drop σ.erase U hR
  rw [show σ.erase.thin .refl = σ.erase from rfl] at hap
  show m.afterC _ (U.apply σ.erase)
  simp only at h
  split at h
  · rename_i U' hc
    cases h
    have hφ : m.afterC _ (U'.apply σ.erase) := hφ
    rw [UThin.close?_apply hc _ _ hap] at hφ
    exact hφ
  · obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have hφ : m.afterC _ (R.U.apply σ.erase) := hφ
    rw [hap] at hφ
    cases hU : U.apply σ.erase with
    | error e => rw [hU] at hφ; exact hφ
    | ok τ =>
      rw [hU] at hφ
      intro σ' he hH
      exact Fml.thinS?_holds R.th ψ hψ σ' (hφ (σ'.thin R.th) (by rw [State.thin_erase, he]) hH)

/-- **`simplifyUpdate`** on `{U}_m ψ` past the program: the scope ends after
it merged in, the shadowed writes dropped, then every declaration nothing
reads afterwards, else the ones `U` pops itself; `none` where nothing
goes. -/
def Fml.simpPastTop {Δ : Ctx} (every : Bool) (m : Modality) (U : Upd C Γ Δ) (ψ : Fml C Δ) :
    Option (Fml C Γ) :=
  match (Fml.absorbPops m U ψ).updHead? with
  | some ⟨m', W, ψ'⟩ =>
    let W' := W.shadow m'.isBoxS
    let popped := (Upd.declStack W').2.2
    let r := Fml.dropDeclsTop (fun k => every || popped.contains k) m' W' ψ'
    r.bind fun φ => match φ.updHead? with
      | some h => if h.U.size < W'.size then some φ else none
      | none => none
  | none => none

theorem Fml.simpPastTop_sound {Δ : Ctx} {every : Bool} {m : Modality} {U : Upd C Γ Δ} {ψ : Fml C Δ}
    {φ : Fml C Γ} (h : Fml.simpPastTop every m U ψ = some φ) (σ : State C Γ) (hφ : holds σ φ) :
    holds σ (.upd m U ψ) := by
  unfold Fml.simpPastTop at h
  split at h
  · rename_i m' W ψ' hW
    refine Fml.absorbPops_holds σ ?_
    rw [Fml.updHead?_eq hW]
    refine holds_upd_shadow σ ?_
    dsimp only at h
    obtain ⟨φ'', hφ'', hr'⟩ := Option.bind_eq_some_iff.1 h
    have heq : φ'' = φ := by
      split at hr'
      · split at hr'
        · exact Option.some.inj hr'
        · cases hr'
      · cases hr'
    subst heq
    exact Fml.dropDeclsTop_sound hφ'' σ hφ
  · cases h

/-- `bind x ({U} χ)` with the binder dropped, where `U` pops its local and
reads it nowhere (`Upd.thinIO`, the binder's local thinned out of `U`'s
state). -/
def Fml.dropBindTop {Δ : Ctx} {t : LTy} : Fml C (t :: Δ) → Option (Fml C Δ)
  | .upd m U χ => match U.thinIO (Thin.drop .refl) (fun _ => false) with
    | some (_, ⟨.refl, U'⟩) => some (.upd m U' χ)
    | _ => none
  | _ => none

theorem Fml.dropBindTop_sound {Δ : Ctx} {t : LTy} {m₀ : Modality} {x : Var} {ψ : Fml C (t :: Δ)}
    {φ : Fml C Δ} (h : Fml.dropBindTop ψ = some φ) (σ : State C Δ) (hφ : holds σ φ) :
    holds σ (.bind m₀ x t ψ) := by
  cases ψ with
  | upd m U χ =>
    simp only [Fml.dropBindTop] at h
    split at h
    · rename_i n U' hU
      cases h
      refine Modality.forallB_intro fun w => ?_
      have hap := Upd.apply_thinIO (Thin.drop .refl) (fun _ => false) (σ.erase.push
        (LTy.TDenote.erase t w)) U hU
      show m.afterC _ (U.apply (σ.push w).erase)
      have hφ : m.afterC _ (U'.apply σ.erase) := hφ
      rw [State.push_erase]
      rw [show U'.apply σ.erase = U'.apply ((σ.erase.push (LTy.TDenote.erase t w)).thin
        (Thin.drop .refl)) from rfl, hap] at hφ
      cases hU' : U.apply (σ.erase.push (LTy.TDenote.erase t w)) with
      | error e => rw [hU'] at hφ; exact hφ
      | ok τ =>
        rw [hU'] at hφ
        exact hφ
    · cases h
  | _ => cases h

/-- `{U}_m ψ` simplified where it can be, else as it is. -/
def Fml.simpPastD {Γ : Ctx} (every : Bool) : Fml C Γ → Fml C Γ
  | .upd m U ψ => (Fml.simpPastTop every m U ψ).getD (.upd m U ψ)
  | φ => φ

theorem Fml.simpPastD_sound {Γ : Ctx} (every : Bool) (φ : Fml C Γ) (σ : State C Γ)
    (h : holds σ (φ.simpPastD every)) : holds σ φ := by
  cases φ with
  | upd m U ψ =>
    simp only [Fml.simpPastD] at h
    cases hs : Fml.simpPastTop every m U ψ with
    | none => rw [hs] at h; exact h
    | some χ => rw [hs] at h; exact Fml.simpPastTop_sound hs σ h
  | _ => exact h

/-- `simplifyUpdate` past the program at position `n` of the spine, a hidden
binder in front of the update absorbed where the update sets it first, or
dropped where the update pops its local and reads it nowhere. -/
def Fml.simpPastAt (every : Bool) : {Γ : Ctx} → Nat → Fml C Γ → Option (Fml C Γ)
  | _, n, .all x p φ => (Fml.simpPastAt every n φ).map (.all x p)
  | _, 0, .bind m x t φ =>
    match (match φ with
      | .upd m' V ψ => (V.absorb x).bind fun V' => Fml.simpPastTop every m' V' ψ
      | _ => none) with
    | some ψ => some ψ
    | none => match Fml.dropBindTop φ with
      | some ψ => some (ψ.simpPastD every)
      | none => (Fml.simpPastAt every 0 φ).map (.bind m x t)
  | _, n + 1, .bind m x t φ => (Fml.simpPastAt every (n + 1) φ).map (.bind m x t)
  | _, 0, .upd m U φ => Fml.simpPastTop every m U φ
  | _, n + 1, .upd m U φ => (Fml.simpPastAt every n φ).map (.upd m U)
  | _, _, _ => none

theorem Fml.simpPastAt_sound (every : Bool) : {Γ : Ctx} → (n : Nat) → (φ : Fml C Γ) → {ψ : Fml C Γ} →
    Fml.simpPastAt every n φ = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | _, n, .all x p φ, ψ₀, h => by
    have h : (Fml.simpPastAt every n φ).map (Fml.all x p) = some ψ₀ := by rw [← h]; cases n <;> rfl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs v => Fml.simpPastAt_sound every n φ hψ _ (hs v)
  | _, 0, .bind m x t φ, ψ₀, h => by
    simp only [Fml.simpPastAt] at h
    split at h
    · rename_i ψ hψ
      cases h
      split at hψ
      · rename_i m' V χ
        obtain ⟨V', hV', hψ⟩ := Option.bind_eq_some_iff.1 hψ
        exact fun σ hs => holds_bind_absorb hV' σ (Fml.simpPastTop_sound hψ σ hs)
      · cases hψ
    · split at h
      · rename_i ψ hψ
        cases h
        exact fun σ hs => Fml.dropBindTop_sound hψ σ (Fml.simpPastD_sound every ψ σ hs)
      · obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
        exact fun σ hs => Modality.forallB_imp (fun v => Fml.simpPastAt_sound every 0 φ hψ _) hs
  | _, n + 1, .bind m x t φ, ψ₀, h => by
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Modality.forallB_imp (fun v => Fml.simpPastAt_sound every (n + 1) φ hψ _) hs
  | _, 0, .upd m U φ, _, h => fun σ hs => Fml.simpPastTop_sound h σ hs
  | _, n + 1, .upd m U φ, _, h => by
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Modality.afterC_imp hs fun τ a σ' e hx =>
      Fml.simpPastAt_sound every n φ hψ σ' (a σ' e hx)
  | _, n, .tt, _, h | _, n, .eq .., _, h | _, n, .defined _, _, h | _, n, .not _, _, h
  | _, n, .and .., _, h | _, n, .imp .., _, h | _, n, .modal .., _, h | _, n, .havoc _, _, h
  | _, n, .anon .., _, h => by
    cases n <;> cases h

/-- **`simplifyUpdate`** past the program, at position `n` of the spine
(`Fml.simpPastAt`): every declaration nothing reads afterwards (`every`),
else the ones the update ends itself, which does not ask the line after
what it reads. -/
def FmlRw.simplifyPast (n : Nat) (every : Bool) : FmlRw C where
  apply := fun φ => Fml.simpPastAt every n φ
  sound := fun h σ hψ => Fml.simpPastAt_sound every n _ h σ hψ

end SimpPast

end Solidity
