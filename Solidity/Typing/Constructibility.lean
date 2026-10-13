import Solidity.Typing.Fits

/-!
# Which storages are reachable, exactly

`Typing/Reachability.lean` and `Typing/Tight.lean` prove reachable ⇒
canonical and tight.  The converse: everything canonical and tight is
reachable when its mapping keys and array slots are in range
(`SVal.Fits`: what a literal can write, `Simple.lit`), by one scoped program
(`Build.rootsProg`, over `Syntax/Scoped.lean`): a word is assigned; a struct
is filled member by member through an alias bound to it; a dynamic array is
pushed to its whole run of slots, then each slot past the end is bound to an
alias, popped, and filled through the alias (the only way to write past an
end), then the live elements are filled; a fixed-size array element by
element; a mapping entry by entry, each created by a `delete` so that an
entry holding the default is there too.  Each alias is declared in a block
of its own (`Build.bound`), so a fill leaves the context it starts in and
its caller's aliases, read by position, as they were.

The builder runs by the typed run (`TRuns`), each step read on `TRun.*`
(`run_push`, `run_pop`, …): no step loops or pushes onto `2^256 - 1`
elements, and none allocates, so a fill ends in its start state with only
the storage replaced.  The proof tracks the value at the path being filled
as a chain of saves at that path (`Wrote`), which is why every fill starts
from the default, at a path where saving the default changes nothing.
-/

namespace Solidity

open Semantics (structDef lookupBy setBy nodupKeysB)

variable {C : Contract}

/-- A sequence followed by another. -/
def Prog.append {Γ Δ Ε : Ctx} : Prog C Γ Δ → Prog C Δ Ε → Prog C Γ Ε
  | .nil, Q => Q
  | .cons s P, Q => .cons s (P.append Q)

/-- One statement `n` times. -/
def Prog.rep {Γ : Ctx} (n : Nat) (s : Stmt C Γ Γ) : Prog C Γ Γ :=
  match n with
  | 0 => .nil
  | n + 1 => .cons s (Prog.rep n s)

namespace Build

/-! ## The builder -/

/-- The name of the alias a fill at depth `d` binds. -/
def slot (d : Nat) : Var := .fresh "slot" d

theorem inRange_of_lt {j : Nat} (h : j < 2 ^ 256) : PrimTy.uint.inRange (j : Int) = true := by
  simp only [PrimTy.inRange, decide_eq_true_eq]
  omega

/-- The literal `n` at the numeric type `p`, or `0` where `n` is out of its
range (an index the builder writes has none, `SVal.Fits`). -/
def numLit {Γ : Ctx} (p : PrimTy) (hp : p.isNumeric = true) (n : Int) : Simple C Γ p :=
  if h : p.inRange n = true then .lit n h
  else .lit 0 (by cases p <;> first | rfl | exact absurd hp (by decide))

theorem numLit_eq {Γ : Ctx} {p : PrimTy} {hp : p.isNumeric = true} {n : Int}
    (h : p.inRange n = true) : numLit (C := C) (Γ := Γ) p hp n = .lit n h := dif_pos h

/-- The key `n` at the key type `p`: a numeric literal, or `true` for `1` and
`false` otherwise. -/
def keyLit {Γ : Ctx} : (p : PrimTy) → Int → Simple C Γ p
  | .bool, n => .bool (n == 1)
  | .uint, n => numLit .uint rfl n
  | .int, n => numLit .int rfl n

/-- A word as a literal. -/
def litOf {Γ : Ctx} : (p : PrimTy) → p.Denote → Simple C Γ p
  | .bool, b => .bool b
  | .uint, v => .lit v.1 v.2
  | .int, v => .lit v.1 v.2

/-- `{ R storage slot d = q; body }`: the alias bound for the body, which
fills through it, and ended with the block. -/
def bound {Γ : Ctx} (d : Nat) (R : RefTy) (q : SPath C Γ (.ref R))
    (body : Prog C (.alias R :: Γ) (.alias R :: Γ)) : Prog C Γ Γ :=
  .cons (.block (.cons (.declStorage R (slot d) (some (.path q))) body)) .nil

mutual

/-- A program that turns the default at `q : T` into `v`.  A word is
assigned.  Anything else binds an alias to `q` in a block and fills through
it: a struct member by member; a dynamic array by pushing every slot it has,
popping those past its end one at a time (each bound to a deeper alias
before its `pop`, and filled through it after), then filling the live
elements; a fixed-size array element by element; a mapping entry by entry,
each created by a `delete` first. -/
def fill {Γ : Ctx} (d : Nat) : {T : Ty} → SPath C Γ T → SVal T → Prog C Γ Γ
  | .prim _, .loc l, .prim v => .cons (.assign l (.val (.simple (litOf _ v)))) .nil
  | .ref (.struct _), q, .struct fs =>
    bound d _ q (fillFields d .here (fun _ _ hm => lookupBy_of_nodup (structDef_nodup _) hm) fs)
  | .ref (.array E), q, @SVal.array _ n e sh _ =>
    bound d _ q
      (if hE : E.defaultOkS = true then
        (Prog.rep (n + sh.length)
            (.push (.alias .here : SPath C _ (.array E)) none (by simp only [Option.isSome_none,
                hE, Bool.or_true]))).append
          ((fillShadow d .here n sh).append (fillElems d (ArrTy.dyn (E := E)) .here 0 e))
      else .nil)
  | .ref (.fixed E n), q, .fixed e => bound d _ q (fillElems d (ArrTy.fixed (E := E) (n := n)) .here 0 e)
  | .ref (.mapping K _), q, .map m _ =>
    match K, q with
    | .prim k, q => bound d _ q (fillEntries d k .here m)
    | .ref _, _ => .nil

/-- The members of a struct bound to `a`, one after another. -/
def fillFields {Γ : Ctx} (d : Nat) {s : Name} (a : Idx Γ (.alias (.struct s))) :
    {fs : List (Name × Ty)} → (∀ f T, (f, T) ∈ fs → lookupBy f (structDef s) = some T) →
    SFields fs → Prog C Γ Γ
  | _, _, .nil => .nil
  | (f, T) :: _, hsub, .cons v rest =>
      (fill (d + 1) (.loc (.field (.alias a) f (hsub f T List.mem_cons_self))) v).append
        (fillFields d a (fun g U hm => hsub g U (List.mem_cons_of_mem _ hm)) rest)

/-- The slots past the end of the array bound to `a`, from the last: slot
`i` bound, popped, then filled through its alias.  A word slot is only
popped (it is cleared). -/
def fillShadow {Γ : Ctx} (d : Nat) {E : Ty} (a : Idx Γ (.alias (.array E))) (i : Nat) :
    SList E → Prog C Γ Γ
  | .nil => .nil
  | .cons w rest =>
      (fillShadow d a (i + 1) rest).append
        (match (generalizing := false) hE : E with
         | .prim _ => .cons (.pop (.alias a)) .nil
         | .ref R => bound (d + 1) R
             (hE ▸ .loc (.index (.arr .dyn) (.alias a) (.simple (numLit .uint rfl (i : Int)))))
             (.cons (.pop (.alias a.there)) (fill (d + 1) (hE ▸ .alias .here) w)))

/-- The live elements of the array bound to `a`, from index `j`. -/
def fillElems {Γ : Ctx} (d : Nat) {R : RefTy} {E : Ty} (ak : ArrTy R E) (a : Idx Γ (.alias R))
    (j : Nat) : {n : Nat} → SVec E n → Prog C Γ Γ
  | _, .nil => .nil
  | _, .cons w rest =>
      (fill (d + 1) (.loc (.index (.arr ak) (.alias a) (.simple (numLit .uint rfl (j : Int))))) w).append
        (fillElems d ak a (j + 1) rest)

/-- The entries of the mapping bound to `a`: each created by `delete`, then
filled. -/
def fillEntries {Γ : Ctx} (d : Nat) (k : PrimTy) {V : Ty}
    (a : Idx Γ (.alias (.mapping (.prim k) V))) : SMap V → Prog C Γ Γ
  | .nil => .nil
  | .cons key w rest =>
      .cons (.delete (.index .map (.alias a) (.simple (keyLit k key)) : Loc C Γ V))
        ((fill (d + 1) (.loc (.index .map (.alias a) (.simple (keyLit k key)))) w).append
          (fillEntries d k a rest))

end

/-! ## Saves at one path -/

section Wrote

variable {st₀ st st' : Storage C} {U : Ty} {r : SRef C U}

/-- A save, by its compiled form. -/
theorem Storage.save_eq {X : SVal U} :
    st.save r X = ((st.get r.hroot).saveM r.path X).map (st.set r.hroot) := by
  simp only [Storage.save, SVal.save_eq_saveM, Option.bind_eq_bind]
  cases (st.get r.hroot).saveM r.path X <;> rfl

/-- `st` is `st₀` with `X` saved at `r`. -/
def Wrote (st₀ st : Storage C) {U : Ty} (r : SRef C U) (X : SVal U) : Prop := st₀.save r X = some st

theorem Wrote.find {X : SVal U} (h : Wrote st₀ st r X) : st.find r = some X := by
  unfold Wrote at h
  rw [Storage.save_eq] at h
  cases hv : (st₀.get r.hroot).saveM r.path X with
  | none => rw [hv] at h; exact nomatch h
  | some v =>
    rw [hv] at h
    cases h
    show ((st₀.set r.hroot v).get r.hroot).find r.path = some X
    rw [SFields.get_set_same, SVal.find_eq_findM]
    exact SVal.findM_saveM _ _ _ hv

theorem Wrote.idem {X : SVal U} (h : Wrote st₀ st r X) : st.save r X = some st := by
  unfold Wrote at h
  rw [Storage.save_eq] at h ⊢
  cases hv : (st₀.get r.hroot).saveM r.path X with
  | none => rw [hv] at h; exact nomatch h
  | some v =>
    rw [hv] at h
    cases h
    rw [SFields.get_set_same, SVal.saveM_idem _ _ _ hv]
    simp only [Option.map_some, SFields.set_set]

theorem Wrote.trans {X Y : SVal U} (h : Wrote st₀ st r X) (h' : st.save r Y = some st') :
    Wrote st₀ st' r Y := by
  unfold Wrote at h ⊢
  rw [Storage.save_eq] at h h' ⊢
  cases hv : (st₀.get r.hroot).saveM r.path X with
  | none => rw [hv] at h; exact nomatch h
  | some v =>
    rw [hv] at h
    cases h
    rw [SFields.get_set_same] at h'
    cases hv' : v.saveM r.path Y with
    | none => rw [hv'] at h'; exact nomatch h'
    | some v' =>
      rw [hv'] at h'
      cases h'
      rw [SVal.saveM_saveM _ _ _ _ hv hv']
      simp only [Option.map_some, SFields.set_set]

/-- A child saved below a path written: the value written there changes. -/
theorem Wrote.child {N : SVal U} {W : Ty} {q : Path U W} {w : SVal W} (h : Wrote st₀ st r N)
    (h' : st.save (r.append q) w = some st') :
    ∃ N', N.saveM q w = some N' ∧ Wrote st₀ st' r N' := by
  have hf := h.find
  rw [Storage.save_eq] at h'
  cases hv : (st.get r.hroot).saveM (r.path.append q) w with
  | none =>
    change ((st.get r.hroot).saveM (r.path.append q) w).map _ = _ at h'
    rw [hv] at h'; exact nomatch h'
  | some v =>
    change ((st.get r.hroot).saveM (r.path.append q) w).map _ = _ at h'
    rw [hv] at h'
    cases h'
    obtain ⟨y, y', hy, hy', hv'⟩ := SVal.saveM_append _ _ _ _ hv
    have hN : y = N := by
      have : (st.get r.hroot).find r.path = some N := hf
      rw [SVal.find_eq_findM, hy] at this
      exact Option.some.inj this
    subst hN
    refine ⟨y', hy', h.trans ?_⟩
    rw [Storage.save_eq, hv']
    rfl

/-- Saving the value a child already holds, below a path written, changes
nothing. -/
theorem Wrote.childNoop {N : SVal U} {W : Ty} {q : Path U W} {D : SVal W} (h : Wrote st₀ st r N)
    (hq : N.saveM q D = some N) : st.save (r.append q) D = some st := by
  have hf := h.find
  have hi := h.idem
  rw [Storage.save_eq] at hi ⊢
  change ((st.get r.hroot).saveM (r.path.append q) D).map _ = _
  rw [SVal.saveM_append_eq]
  have hy : (st.get r.hroot).findM r.path = some N := by
    rw [← SVal.find_eq_findM]; exact hf
  rw [hy]
  simp only [Option.bind_some, hq]
  exact hi

end Wrote

/-! ## Runs -/

section Steps

variable {Γ : Ctx}

/-- `P` runs, by the typed run, from `σ` to `τ`. -/
def TRuns {Γ' : Ctx} (σ : State C Γ) (P : Prog C Γ Γ') (τ : State C Γ') : Prop :=
  ∃ o : Out C σ.H Γ', P.run σ = .ok o ∧ o.st = τ

/-- `s` runs, by the typed run, from `σ` to `τ`. -/
def SRuns {Γ' : Ctx} (σ : State C Γ) (s : Stmt C Γ Γ') (τ : State C Γ') : Prop :=
  ∃ o : Out C σ.H Γ', s.run σ = .ok o ∧ o.st = τ

theorem TRuns.nil (σ : State C Γ) : TRuns σ (.nil : Prog C Γ Γ) σ := ⟨_, rfl, rfl⟩

theorem TRuns.cons {Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂}
    {τ : State C Γ₁} {υ : State C Γ₂} (hs : SRuns σ s τ) (hP : TRuns τ P υ) :
    TRuns σ (.cons s P) υ := by
  obtain ⟨o, ho, rfl⟩ := hs
  obtain ⟨o', ho', rfl⟩ := hP
  exact ⟨_, by rw [Prog.run_cons_ok ho, ho']; rfl, rfl⟩

theorem TRuns.cons_inv {Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂}
    {υ : State C Γ₂} (h : TRuns σ (.cons s P) υ) : ∃ τ, SRuns σ s τ ∧ TRuns τ P υ := by
  obtain ⟨o, ho, rfl⟩ := h
  cases hs : s.run σ with
  | error e =>
    have he : Prog.run σ (.cons s P) = .error e := by
      show TRun.seq s.runR P.runR σ = _
      simp only [TRun.seq, Stmt.run] at hs ⊢
      rw [hs]
    rw [he] at ho
    cases ho
  | ok o₁ =>
    rw [Prog.run_cons_ok hs] at ho
    cases hp : Prog.run o₁.st P with
    | error e => rw [hp] at ho; cases ho
    | ok o₂ =>
      rw [hp] at ho
      cases ho
      exact ⟨o₁.st, ⟨o₁, hs, rfl⟩, ⟨o₂, hp, rfl⟩⟩

theorem TRuns.append : {Γ Δ Ε : Ctx} → {σ : State C Γ} → {P : Prog C Γ Δ} →
    {Q : Prog C Δ Ε} → {τ : State C Δ} → {υ : State C Ε} → TRuns σ P τ → TRuns τ Q υ →
    TRuns σ (P.append Q) υ
  | _, _, _, _, .nil, _, _, _, hP, hQ => by
    obtain ⟨o, ho, rfl⟩ := hP
    cases ho
    exact hQ
  | _, _, _, _, .cons _ _, _, _, _, hP, hQ =>
    let ⟨_, hs, hP'⟩ := hP.cons_inv
    TRuns.cons hs (TRuns.append hP' hQ)

theorem TRuns.single {Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'} {τ : State C Γ'}
    (h : SRuns σ s τ) : TRuns σ (.cons s .nil) τ :=
  TRuns.cons h (TRuns.nil _)

/-! ### Paths the builder resolves -/

theorem resolveT_alias {σ : State C Γ} {R : RefTy} {a : Idx Γ (.alias R)} {ref : SRef C (.ref R)}
    (h : TEnv.get a σ.env = some ref) : (SPath.alias a).resolveT σ = .ok ref := by
  show (match (TEnv.get a σ.env : Option (SRef C _)) with
    | some r => .ok r
    | none => .error .revert : TRes _) = _
  rw [h]

theorem resolveT_field {σ : State C Γ} {s f : Name} {T : Ty} {a : Idx Γ (.alias (.struct s))}
    {ref : SRef C (.ref (.struct s))} (hf : C.fieldType s f = some T)
    (h : TEnv.get a σ.env = some ref) :
    (Loc.field (C := C) (.alias a) f hf).resolveT σ = .ok (ref.field hf) := by
  show (do let r ← (SPath.alias a).resolveT σ; pure (r.field hf) : TRes _) = _
  rw [resolveT_alias h]
  rfl

theorem keyLit_key (σ : State C Γ) {k : PrimTy} {key : Int} (hr : k.keyFits key = true) :
    PrimTy.key ((keyLit (C := C) (Γ := Γ) k key).evalT σ) = key := by
  cases k with
  | bool =>
    simp only [PrimTy.keyFits, Bool.or_eq_true, beq_iff_eq] at hr
    rcases hr with rfl | rfl <;> rfl
  | uint => rw [keyLit, numLit_eq (p := .uint) hr]; rfl
  | int => rw [keyLit, numLit_eq (p := .int) hr]; rfl

/-- An index the storage takes, at a literal. -/
theorem resolveT_index_lit {σ : State C Γ} {R : RefTy} {E : Ty} (ak : ArrTy R E)
    {a : Idx Γ (.alias R)} {ref : SRef C (.ref R)} {j : Nat} (hb : j < 2 ^ 256)
    (h : TEnv.get a σ.env = some ref)
    (hck : σ.storage.checkIndex ref (.arr ak) (j : Int) = some ()) :
    (Loc.index (C := C) (.arr ak) (.alias a) (.simple (numLit .uint rfl (j : Int)))).resolveT σ =
      .ok (ref.index (.arr ak) (j : Int)) := by
  rw [numLit_eq (inRange_of_lt hb)]
  show (do
    let r ← (SPath.alias a).resolveT σ
    let k ← (Val.simple (Simple.lit (C := C) (Γ := Γ) (p := .uint) (j : Int) _)).evalT σ
    TRes.ofOpt (σ.storage.checkIndex r (.arr ak) (PrimTy.key k))
    pure (r.atKey (.arr ak) k) : TRes _) = _
  rw [resolveT_alias h]
  simp only [bind, Except.bind, Val.evalT, Simple.evalT]
  rw [show PrimTy.key (PrimTy.ofLit .uint (j : Int) (inRange_of_lt hb)) = (j : Int) from rfl, hck]
  rfl

theorem resolveT_index_map {σ : State C Γ} {k : PrimTy} {V : Ty} {key : Int}
    (hk : k.keyFits key = true) {a : Idx Γ (.alias (.mapping (.prim k) V))}
    {ref : SRef C (.ref (.mapping (.prim k) V))} (h : TEnv.get a σ.env = some ref)
    (hfind : ∃ v, σ.storage.find ref = some v) :
    (Loc.index (C := C) (V := V) .map (.alias a) (.simple (keyLit k key))).resolveT σ =
      .ok (ref.index .map key) := by
  obtain ⟨v, hv⟩ := hfind
  have hck : σ.storage.checkIndex ref (.map (V := V)) key = some () := by
    simp only [Storage.checkIndex, hv, Option.bind_eq_bind, Option.bind_some]
    rfl
  show (do
    let r ← (SPath.alias a).resolveT σ
    let x ← (Val.simple (keyLit (C := C) (Γ := Γ) k key)).evalT σ
    TRes.ofOpt (σ.storage.checkIndex r .map (PrimTy.key x))
    pure (r.atKey .map x) : TRes _) = _
  rw [resolveT_alias h]
  simp only [bind, Except.bind, Val.evalT]
  rw [keyLit_key σ hk, hck]
  show Except.ok (ref.index .map (PrimTy.key ((keyLit (C := C) (Γ := Γ) k key).evalT σ))) = _
  rw [keyLit_key σ hk]

/-! ### One statement at a time

Each step of the builder, from a state whose storage is `st₀` with `X`
written at a reference, leaves the state with only its storage replaced, by
`st₀` with what the step makes of `X` written there. -/

/-- A save lands where a value is found. -/
theorem Wrote.save_exists {st₀ st : Storage C} {U : Ty} {r : SRef C U} {X : SVal U}
    (h : Wrote st₀ st r X) (Y : SVal U) : ∃ st', st.save r Y = some st' := by
  have hf : (st.get r.hroot).findM r.path = some X := by rw [← SVal.find_eq_findM]; exact h.find
  obtain ⟨v, hv⟩ := SVal.saveM_of_findM _ _ hf Y
  exact ⟨_, by rw [Storage.save_eq, hv]; rfl⟩

theorem litOf_evalT (σ : State C Γ) : (p : PrimTy) → (v : p.Denote) →
    (litOf (C := C) (Γ := Γ) p v).evalT σ = v
  | .bool, _ => rfl
  | .uint, _ => rfl
  | .int, _ => rfl

/-- `l = v;` for a word `v`. -/
theorem run_assign {σ : State C Γ} {p : PrimTy} {l : Loc C Γ (.prim p)} {ref : SRef C (.prim p)}
    (hl : l.resolveT σ = .ok ref) {st₀ : Storage C} {X : SVal (.prim p)}
    (hW : Wrote st₀ σ.storage ref X) (v : p.Denote) :
    ∃ st', SRuns σ (.assign l (.val (.simple (litOf p v)))) (σ.withStorage st') ∧
      Wrote st₀ st' ref (.prim v) := by
  obtain ⟨st', hs⟩ := hW.save_exists (.prim v)
  refine ⟨st', ⟨⟨σ.withStorage st', List.prefix_refl _⟩, ?_, rfl⟩, hW.trans hs⟩
  show TRun.assign l (.val (.simple (litOf p v))) σ = _
  simp only [TRun.assign, Src.valueT, Val.evalT, litOf_evalT, bind, Except.bind, pure, Except.pure]
  rw [hl]
  simp only [Storage.write, SVal.isPrim, Ty.isPrimitive, ↓reduceIte, hs, TRes.ofOpt]

/-- The literal array of `L` and `S`. -/
def arrOf {E : Ty} (L S : List (SVal E)) (h : L.length < 2 ^ 256) : SVal (.ref (.array E)) :=
  .array (SVec.ofList L) (SList.ofList S) h

theorem arrOf_eq {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
    (h : e.toList.length < 2 ^ 256) : arrOf e.toList sh.toList h = .array e sh hn :=
  SVal.array_ext _ _ _ _ _ _ (SVec.toList_ofList _) (SList.toList_ofList _)

theorem len_snoc {α : Type} {L : List α} {x : α} (hb : L.length + 1 < 2 ^ 256) :
    (L ++ [x]).length < 2 ^ 256 := by
  rw [List.length_append, List.length_singleton]; exact hb

/-- `a.push();` on an array with nothing past its end, below the bound. -/
theorem run_push {σ : State C Γ} {E : Ty} {a : Idx Γ (.alias (.array E))}
    {ref : SRef C (.ref (.array E))} (hd : (none.isSome || E.defaultOkS) = true)
    (ha : TEnv.get a σ.env = some ref) {st₀ : Storage C} {L : List (SVal E)}
    {hL : L.length < 2 ^ 256} (hW : Wrote st₀ σ.storage ref (arrOf L [] hL))
    (hb : L.length + 1 < 2 ^ 256) :
    ∃ st', SRuns σ (.push (C := C) (.alias a : SPath C Γ (.array E)) none hd)
        (σ.withStorage st') ∧
      Wrote st₀ st' ref (arrOf (L ++ [SVal.dflt E]) [] (len_snoc hb)) := by
  have hf := hW.find
  have hb' : L.length + 1 < 2 ^ 256 := hb
  have hfull : σ.storage.full ref = false := by
    simp only [Storage.full, hf, arrOf, SVal.view_array, hb', decide_true, Bool.not_true]
  obtain ⟨st', hs⟩ := hW.save_exists (arrOf (L ++ [SVal.dflt E]) [] (len_snoc hb))
  refine ⟨st', ⟨⟨σ.withStorage st', List.prefix_refl _⟩, ?_, rfl⟩, hW.trans hs⟩
  show TRun.push (.alias a) none σ = _
  simp only [TRun.push, bind, Except.bind, pure, Except.pure]
  rw [resolveT_alias ha]
  simp only [hfull, Bool.false_eq_true, ↓reduceIte, Storage.push, hf, arrOf, SVal.view_array,
    Option.bind_eq_bind, Option.bind_some, Option.getD_none]
  rw [dif_pos hb']
  have hX : ∀ pf, SVal.array (SVec.ofList ((SVec.ofList L).toList ++
      [(pushSlot E (SList.ofList ([] : List (SVal E))).toList).fst]))
      (SList.ofList (pushSlot E (SList.ofList ([] : List (SVal E))).toList).snd) pf =
      arrOf (L ++ [SVal.dflt E]) [] (len_snoc hb) := fun _ =>
    SVal.array_ext _ _ _ _ _ _ (by simp only [SVec.toList_ofList, SList.toList_ofList, pushSlot])
      (by simp only [SList.toList_ofList, pushSlot])
  rw [hX, hs]
  rfl

/-- `a.pop();` on an array whose live elements end in `last`. -/
theorem run_pop {σ : State C Γ} {E : Ty} {a : Idx Γ (.alias (.array E))}
    {ref : SRef C (.ref (.array E))} (ha : TEnv.get a σ.env = some ref) {st₀ : Storage C}
    {L S : List (SVal E)} {last : SVal E} {hL : (L ++ [last]).length < 2 ^ 256}
    (hW : Wrote st₀ σ.storage ref (arrOf (L ++ [last]) S hL)) :
    ∃ st', SRuns σ (.pop (C := C) (E := E) (.alias a)) (σ.withStorage st') ∧
      Wrote st₀ st' ref (arrOf L ((if E.isMapping then last else last.defaultOf) :: S)
        (Nat.lt_of_le_of_lt (by rw [List.length_append]; omega) hL)) := by
  have hf := hW.find
  obtain ⟨st', hs⟩ := hW.save_exists (arrOf L ((if E.isMapping then last else last.defaultOf) :: S)
    (Nat.lt_of_le_of_lt (by rw [List.length_append]; omega) hL))
  refine ⟨st', ⟨⟨σ.withStorage st', List.prefix_refl _⟩, ?_, rfl⟩, hW.trans hs⟩
  show TRun.pop (.alias a) σ = _
  simp only [TRun.pop, bind, Except.bind, pure, Except.pure]
  rw [resolveT_alias ha]
  simp only [Storage.pop, hf, arrOf, SVal.view_array, Option.bind_eq_bind, Option.bind_some,
    SVec.toList_ofList, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, SList.toList_ofList]
  have hX : ∀ pf, SVal.array (SVec.ofList (SVec.ofList (L ++ [last])).toList.dropLast)
      (SList.ofList ((if E.isMapping then last else last.defaultOf) :: S)) pf =
      arrOf L ((if E.isMapping then last else last.defaultOf) :: S)
        (Nat.lt_of_le_of_lt (by rw [List.length_append]; omega) hL) := fun _ =>
    SVal.array_ext _ _ _ _ _ _ (by simp only [SVec.toList_ofList, List.dropLast_concat]) rfl
  rw [hX, hs]
  rfl

/-- `delete l;`. -/
theorem run_delete {σ : State C Γ} {T : Ty} {l : Loc C Γ T} {ref : SRef C T}
    (hl : l.resolveT σ = .ok ref) {cur : SVal T} (hf : σ.storage.find ref = some cur)
    {st' : Storage C} (hs : σ.storage.save ref cur.defaultOf = some st') :
    SRuns σ (.delete l) (σ.withStorage st') := by
  refine ⟨⟨σ.withStorage st', List.prefix_refl _⟩, ?_, rfl⟩
  show TRun.delete l σ = _
  simp only [TRun.delete, bind, Except.bind]
  rw [hl]
  simp only [Storage.delete, hf, Option.bind_eq_bind, Option.bind_some, hs, TRes.ofOpt]
  rfl

/-- The alias a `bound` block declares, bound to `q`. -/
theorem run_decl {d : Nat} {R : RefTy} {σ : State C Γ} {q : SPath C Γ (.ref R)}
    {ref : SRef C (.ref R)} (hq : q.resolveT σ = .ok ref) :
    SRuns σ (.declStorage R (slot d) (some (.path q))) (σ.push (t := .alias R) (some ref)) := by
  refine ⟨⟨σ.push (t := .alias R) (some ref), List.prefix_refl _⟩, ?_, rfl⟩
  show TRun.declStorage R (some (.path q)) σ = _
  simp only [TRun.declStorage, ARhs.evalT, bind, Except.bind, pure, Except.pure]
  rw [hq]
  rfl

theorem run_block {Γ₁ : Ctx} (σ : State C Γ) (P : Prog C Γ Γ₁) :
    Stmt.run σ (.block P) = (Prog.run σ P).map fun o => ⟨o.st.drop P.ext, o.ext⟩ := rfl

/-- A block that binds an alias to `q` and runs `body` through it, changing
only the storage. -/
theorem run_bound {d : Nat} {R : RefTy} {σ : State C Γ} {q : SPath C Γ (.ref R)}
    {ref : SRef C (.ref R)} (hq : q.resolveT σ = .ok ref)
    {body : Prog C (.alias R :: Γ) (.alias R :: Γ)} {st' : Storage C}
    (hb : TRuns (σ.push (t := .alias R) (some ref)) body
      ((σ.push (t := .alias R) (some ref)).withStorage st')) :
    TRuns σ (bound d R q body) (σ.withStorage st') := by
  obtain ⟨o, ho, he⟩ := TRuns.cons (run_decl (d := d) hq) hb
  have h : TRuns σ (bound d R q body) (o.st.drop (.push .refl)) := by
    refine TRuns.single ⟨⟨o.st.drop (.push .refl), o.ext⟩, ?_, rfl⟩
    rw [run_block, ho, Ext.eq_of_depth (Prog.ext _) (.push .refl)]
    rfl
  rw [he] at h
  exact h

end Steps

end Build

end Solidity
