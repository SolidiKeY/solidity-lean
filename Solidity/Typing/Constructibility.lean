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

theorem arrOf_congr {E : Ty} {L L' S : List (SVal E)} {h : L.length < 2 ^ 256}
    {h' : L'.length < 2 ^ 256} (hL : L = L') : arrOf L S h = arrOf L' S h' := by
  subst hL; rfl

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

/-! ## The builder writes what it is given -/

section Fills

/-! ### Saves at one slot -/

theorem arrOf_saveM_live {E : Ty} {L S : List (SVal E)} (h : L.length < 2 ^ 256) {i : Nat}
    (hi : i < L.length) (x : SVal E) :
    (arrOf L S h).saveM (.at (i : Int) .nil) x =
      some (arrOf (L.set i x) S (by rw [List.length_set]; exact h)) := by
  have hl : i < (L ++ S).length := by rw [List.length_append]; omega
  simp only [arrOf, SVal.saveM, Int.natCast_nonneg, ↓reduceIte, SVec.toList_ofList,
    SList.toList_ofList, Int.toNat_natCast, List.getElem?_eq_getElem hl, SVal.saveM_nil,
    Option.bind_eq_bind, Option.bind_some]
  congr 1
  apply SVal.array_ext
  · simp only [SVec.toList_ofList]
    rw [List.set_append_left _ _ hi, List.take_left' (List.length_set ..)]
  · simp only [SList.toList_ofList]
    rw [List.set_append_left _ _ hi, List.drop_left' (List.length_set ..)]

theorem arrOf_saveM_shadow {E : Ty} {L S : List (SVal E)} (h : L.length < 2 ^ 256) {i : Nat}
    (hi : L.length ≤ i) (hi' : i < L.length + S.length) (x : SVal E) :
    (arrOf L S h).saveM (.at (i : Int) .nil) x = some (arrOf L (S.set (i - L.length) x) h) := by
  have hl : i < (L ++ S).length := by rw [List.length_append]; omega
  simp only [arrOf, SVal.saveM, Int.natCast_nonneg, ↓reduceIte, SVec.toList_ofList,
    SList.toList_ofList, Int.toNat_natCast, List.getElem?_eq_getElem hl, SVal.saveM_nil,
    Option.bind_eq_bind, Option.bind_some]
  congr 1
  apply SVal.array_ext
  · simp only [SVec.toList_ofList]
    rw [List.set_append_right _ _ hi, List.take_left' rfl]
  · simp only [SList.toList_ofList]
    rw [List.set_append_right _ _ hi, List.drop_left' rfl]

theorem fixed_saveM {E : Ty} {n : Nat} (e : SVec E n) {i : Nat} (hi : i < n) (x : SVal E) :
    (SVal.fixed e).saveM (.atF (i : Int) .nil) x = some (.fixed (e.set i x)) := by
  have hl : i < e.toList.length := by rw [SVec.length_toList]; exact hi
  simp only [SVal.saveM, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast,
    List.getElem?_eq_getElem hl, SVal.saveM_nil, Option.bind_eq_bind, Option.bind_some]

theorem map_saveM {K V : Ty} (m : SMap V) (d : SVal V) (k : Int) (x : SVal V) :
    (SVal.map (K := K) m d).saveM (.key k .nil) x = some (.map (.ofList (setBy k x m.toList)) d) := by
  simp only [SVal.saveM]
  split <;> simp only [SVal.saveM_nil, Option.bind_eq_bind, Option.bind_some]

/-! ### A child filled -/

/-- What `fill` does for one value `v`: from a path where saving the default
changes nothing, in any context, it leaves `v` there, changing nothing but
the storage. -/
def FillOK (C : Contract) {T : Ty} (v : SVal T) : Prop :=
  ∀ (d : Nat) (Γ : Ctx) (q : SPath C Γ T) (σ : State C Γ) (ref : SRef C T),
    v.Canon → v.Tight → v.Fits → q.resolveT σ = .ok ref →
    σ.storage.save ref (SVal.dflt T) = some σ.storage →
    ∃ st', TRuns σ (fill d q v) (σ.withStorage st') ∧ σ.storage.save ref v = some st'

variable {Γ : Ctx}

/-- A child filled below the node written at `ref`: the node, `N`, becomes
`N'`. -/
theorem child_step {d : Nat} {T W : Ty} {q : SPath C Γ W} {σ : State C Γ} {st₀ : Storage C}
    {ref : SRef C T} {N N' : SVal T} {p : Path T W} {w : SVal W}
    (hw : FillOK C w) (hc : w.Canon) (ht : w.Tight) (hf : w.Fits)
    (hq : q.resolveT σ = .ok (ref.append p)) (hW : Wrote st₀ σ.storage ref N)
    (hnoop : N.saveM p (SVal.dflt W) = some N) (hs : N.saveM p w = some N') :
    ∃ st', TRuns σ (fill (d + 1) q w) (σ.withStorage st') ∧ Wrote st₀ st' ref N' := by
  obtain ⟨st', hrun, hsave⟩ := hw (d + 1) Γ q σ (ref.append p) hc ht hf hq (hW.childNoop hnoop)
  obtain ⟨N'', hN'', hW'⟩ := hW.child hsave
  rw [hs] at hN''
  cases hN''
  exact ⟨st', hrun, hW'⟩

/-- `child_step` at a location. -/
theorem child_stepL {d : Nat} {T W : Ty} {l : Loc C Γ W} {σ : State C Γ} {st₀ : Storage C}
    {ref : SRef C T} {N N' : SVal T} {p : Path T W} {w : SVal W}
    (hw : FillOK C w) (hc : w.Canon) (ht : w.Tight) (hf : w.Fits)
    (hq : l.resolveT σ = .ok (ref.append p)) (hW : Wrote st₀ σ.storage ref N)
    (hnoop : N.saveM p (SVal.dflt W) = some N) (hs : N.saveM p w = some N') :
    ∃ st', TRuns σ (fill (d + 1) (.loc l) w) (σ.withStorage st') ∧ Wrote st₀ st' ref N' :=
  child_step hw hc ht hf hq hW hnoop hs

/-- `a.push();` `k` times on an array with nothing past its end, below the
bound. -/
theorem pushes_run {E : Ty} {a : Idx Γ (.alias (.array E))} {ref : SRef C (.ref (.array E))}
    (hd : (none.isSome || E.defaultOkS) = true) {st₀ : Storage C} :
    ∀ (k : Nat) (L : List (SVal E)) (σ : State C Γ) (hL : L.length < 2 ^ 256),
      TEnv.get a σ.env = some ref → Wrote st₀ σ.storage ref (arrOf L [] hL) →
      (hk : L.length + k < 2 ^ 256) →
      ∃ st', TRuns σ (Prog.rep k (Stmt.push (C := C) (.alias a : SPath C Γ (.array E)) none hd))
        (σ.withStorage st') ∧
        Wrote st₀ st' ref (arrOf (L ++ List.replicate k (SVal.dflt E)) []
          (by rw [List.length_append, List.length_replicate]; exact hk))
  | 0, L, σ, hL, _, hW, _ => ⟨σ.storage, TRuns.nil σ, by simpa only [List.replicate_zero,
      List.append_nil] using hW⟩
  | k + 1, L, σ, hL, ha, hW, hk => by
    obtain ⟨st₁, hs₁, hW₁⟩ := run_push hd ha hW (by omega)
    obtain ⟨st', hrun, hW'⟩ := pushes_run hd k (L ++ [SVal.dflt E]) (σ.withStorage st₁) _ ha hW₁
      (by rw [List.length_append, List.length_singleton]; omega)
    refine ⟨st', TRuns.cons hs₁ hrun, ?_⟩
    simpa only [List.append_assoc, List.replicate_succ, List.singleton_append] using hW'

/-! ### Structs, member by member -/

/-- What `fillFields` does for the members `x` (a suffix of the struct's):
from a node `N` holding the default at each member still to fill and the
target `tgt` at every other, it leaves the target there. -/
def FieldsOK (C : Contract) {fs : List (Name × Ty)} (x : SFields fs) : Prop :=
  ∀ (s : Name) (d : Nat) (Γ : Ctx) (a : Idx Γ (.alias (.struct s)))
    (hsub : ∀ f T, (f, T) ∈ fs → lookupBy f (structDef s) = some T) (σ : State C Γ)
    (ref : SRef C (.ref (.struct s))) (st₀ : Storage C) (N tgt : SFields (structDef s)),
    TEnv.get a σ.env = some ref → Wrote st₀ σ.storage ref (.struct N) →
    (∀ g U (hg : lookupBy g (structDef s) = some U), (∃ V, (g, V) ∈ fs) → N.get hg = SVal.dflt U) →
    (∀ g U (hg : lookupBy g (structDef s) = some U), (¬∃ V, (g, V) ∈ fs) → N.get hg = tgt.get hg) →
    (∀ g U (h' : lookupBy g fs = some U) (hg : lookupBy g (structDef s) = some U),
      x.get h' = tgt.get hg) →
    x.All canonH → x.All tightH → x.All fitsH → nodupKeysB fs = true →
    ∃ st', TRuns σ (fillFields d a hsub x) (σ.withStorage st') ∧ Wrote st₀ st' ref (.struct tgt)

theorem fields_nil : FieldsOK C SFields.nil := by
  intro s d Γ a hsub σ ref st₀ N tgt _ hW _ h2 _ _ _ _ _
  have hN : N = tgt := SFields.ext_get (structDef_nodup s) N tgt fun g U hg =>
    h2 g U hg fun ⟨_, hm⟩ => nomatch hm
  subst hN
  exact ⟨σ.storage, TRuns.nil σ, hW⟩

theorem fields_cons {f : Name} {T : Ty} {fs : List (Name × Ty)} {v : SVal T} {rest : SFields fs}
    (hv : FillOK C v) (hrest : FieldsOK C rest) :
    FieldsOK C (SFields.cons (f := f) v rest) := by
  intro s d Γ a hsub σ ref st₀ N tgt ha hW h1 h2 hag hc ht hf hnd
  simp only [SFields.All] at hc ht hf
  simp only [nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hnd
  have hfT : lookupBy f (structDef s) = some T := hsub f T List.mem_cons_self
  have hN : N.get hfT = SVal.dflt T := h1 f T hfT ⟨T, List.mem_cons_self⟩
  have hhead : v = tgt.get hfT := by
    have h0 : lookupBy f ((f, T) :: fs) = some T := by simp only [lookupBy, ↓reduceIte]
    have := hag f T h0 hfT
    simp only [SFields.get_cons, dite_true] at this
    exact this
  have hnoop : (SVal.struct N).saveM (.field hfT .nil) (SVal.dflt T) = some (.struct N) := by
    simp only [SVal.saveM, SVal.saveM_nil, Option.bind_eq_bind, Option.bind_some]
    rw [← hN, SFields.set_get_self]
  have hs : (SVal.struct N).saveM (.field hfT .nil) v = some (.struct (N.set hfT v)) := by
    simp only [SVal.saveM, SVal.saveM_nil, Option.bind_eq_bind, Option.bind_some]
  obtain ⟨st₁, hrun₁, hW₁⟩ := child_stepL (d := d) (p := .field hfT .nil) hv hc.1 ht.1 hf.1 (resolveT_field hfT ha) hW hnoop hs
  have hne : ∀ g, (∃ V, (g, V) ∈ fs) → g ≠ f := fun g ⟨V, hm⟩ he => by
    have := lookupBy_isSome_of_mem' hm
    rw [he, hnd.1] at this
    exact nomatch this
  obtain ⟨st', hrun₂, hW'⟩ := hrest s d Γ a (fun g U hm => hsub g U (List.mem_cons_of_mem _ hm))
    (σ.withStorage st₁) ref st₀ (N.set hfT v) tgt ha hW₁
    (fun g U hg hm => by
      rw [SFields.get_set_ne N hfT hg (hne g hm).symm]
      exact h1 g U hg (let ⟨V, hV⟩ := hm; ⟨V, List.mem_cons_of_mem _ hV⟩))
    (fun g U hg hm => by
      by_cases hgf : g = f
      · subst hgf
        have hU : U = T := Option.some.inj (hg.symm.trans hfT)
        subst hU
        rw [SFields.get_set_same, hhead]
      · rw [SFields.get_set_ne N hfT hg (Ne.symm hgf)]
        refine h2 g U hg fun ⟨V, hV⟩ => ?_
        rcases List.mem_cons.mp hV with hV | hV
        · exact hgf (congrArg Prod.fst hV)
        · exact hm ⟨V, hV⟩)
    (fun g U h' hg => by
      have hgf : g ≠ f := hne g ⟨U, lookupBy_mem' h'⟩
      have h0 : lookupBy g ((f, T) :: fs) = some U := by
        simp only [lookupBy, hgf, ↓reduceIte]; exact h'
      have := hag g U h0 hg
      simp only [SFields.get_cons, hgf, dite_false] at this
      exact this)
    hc.2 ht.2 hf.2 hnd.2
  exact ⟨st', TRuns.append hrun₁ hrun₂, hW'⟩

/-- A struct filled member by member through an alias bound to it. -/
theorem fill_struct {s : Name} {fs : SFields (structDef s)} (hfs : FieldsOK C fs) :
    FillOK C (SVal.struct fs) := by
  intro d Γ q σ ref hc ht hf hq h0
  simp only [SVal.All] at hc ht hf
  rw [SVal.dflt_struct] at h0
  obtain ⟨st', hrun, hW⟩ := hfs s d _ .here
    (fun _ _ hm => lookupBy_of_nodup (structDef_nodup _) hm)
    (σ.push (t := .alias (.struct s)) (some ref)) ref σ.storage (SFields.dflt (structDef s)) fs
    rfl h0 (fun g U hg _ => SFields.get_dflt hg)
    (fun g U hg hm => absurd ⟨U, lookupBy_mem' hg⟩ hm) (fun _ _ _ _ => rfl) hc ht hf
    (structDef_nodup s)
  exact ⟨st', run_bound hq hrun, hW⟩

/-! ### Arrays, element by element -/

theorem checkIndex_dyn {st : Storage C} {E : Ty} {ref : SRef C (.ref (.array E))}
    {L S : List (SVal E)} {hL : L.length < 2 ^ 256} (hf : st.find ref = some (arrOf L S hL))
    {j : Nat} (hj : j < L.length) : st.checkIndex ref (.arr .dyn) (j : Int) = some () := by
  simp only [Storage.checkIndex, hf, Option.bind_eq_bind, Option.bind_some]
  show (if 0 ≤ (j : Int) ∧ (j : Int).toNat < L.length then some () else none) = some ()
  rw [if_pos ⟨Int.natCast_nonneg j, by rw [Int.toNat_natCast]; exact hj⟩]

theorem checkIndex_fixed {st : Storage C} {E : Ty} {n : Nat} {ref : SRef C (.ref (.fixed E n))}
    {e : SVec E n} (hf : st.find ref = some (.fixed e)) {j : Nat} (hj : j < n) :
    st.checkIndex ref (.arr .fixed) (j : Int) = some () := by
  simp only [Storage.checkIndex, hf, Option.bind_eq_bind, Option.bind_some]
  show (if 0 ≤ (j : Int) ∧ (j : Int).toNat < n then some () else none) = some ()
  rw [if_pos ⟨Int.natCast_nonneg j, by rw [Int.toNat_natCast]; exact hj⟩]

/-- What `fillElems` does for the live elements `x` of a dynamic array, from
index `pre.length`. -/
def ElemsOK (C : Contract) {E : Ty} {n : Nat} (x : SVec E n) : Prop :=
  ∀ (d : Nat) (Γ : Ctx) (a : Idx Γ (.alias (.array E))) (σ : State C Γ)
    (ref : SRef C (.ref (.array E))) (st₀ : Storage C) (pre S : List (SVal E))
    (hL : (pre ++ List.replicate n (SVal.dflt E)).length < 2 ^ 256),
    TEnv.get a σ.env = some ref →
    Wrote st₀ σ.storage ref (arrOf (pre ++ List.replicate n (SVal.dflt E)) S hL) →
    x.All canonH → x.All tightH → x.All fitsH →
    ∃ st' hL', TRuns σ (fillElems d (ArrTy.dyn (E := E)) a pre.length x) (σ.withStorage st') ∧
      Wrote st₀ st' ref (arrOf (pre ++ x.toList) S hL')

theorem elems_nil {E : Ty} : ElemsOK C (SVec.nil (E := E)) := by
  intro d Γ a σ ref st₀ pre S hL _ hW _ _ _
  refine ⟨σ.storage, by simpa only [SVec.toList_nil, List.append_nil, List.replicate_zero]
    using hL, TRuns.nil σ, ?_⟩
  simpa only [SVec.toList_nil, List.replicate_zero] using hW

theorem elems_cons {E : Ty} {n : Nat} {v : SVal E} {rest : SVec E n}
    (hv : FillOK C v) (hrest : ElemsOK C rest) : ElemsOK C (SVec.cons v rest) := by
  intro d Γ a σ ref st₀ pre S hL ha hW hc ht hf
  simp only [SVec.All] at hc ht hf
  have hlen : (pre ++ List.replicate (n + 1) (SVal.dflt E)).length = pre.length + n + 1 := by
    simp only [List.length_append, List.length_replicate]; omega
  have hj : pre.length < (pre ++ List.replicate (n + 1) (SVal.dflt E)).length := by omega
  have hq := resolveT_index_lit (C := C) (ArrTy.dyn (E := E)) (by omega) ha
    (checkIndex_dyn hW.find hj)
  rw [show (ref.index (.arr .dyn) (pre.length : Int)) = ref.append (.at (pre.length : Int) .nil)
    by simp only [SRef.index, Path.index_dyn]] at hq
  have hset : ∀ x : SVal E, (pre ++ List.replicate (n + 1) (SVal.dflt E)).set pre.length x =
      (pre ++ [x]) ++ List.replicate n (SVal.dflt E) := by
    intro x
    rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.replicate_succ,
      List.set_cons_zero, List.append_assoc, List.singleton_append]
  have hnoop : (arrOf (pre ++ List.replicate (n + 1) (SVal.dflt E)) S hL).saveM
      (.at (pre.length : Int) .nil) (SVal.dflt E) =
      some (arrOf (pre ++ List.replicate (n + 1) (SVal.dflt E)) S hL) := by
    rw [arrOf_saveM_live hL hj]
    exact congrArg some (arrOf_congr (by rw [hset, List.append_assoc, List.singleton_append,
      ← List.replicate_succ]))
  have hs : (arrOf (pre ++ List.replicate (n + 1) (SVal.dflt E)) S hL).saveM
      (.at (pre.length : Int) .nil) v =
      some (arrOf ((pre ++ [v]) ++ List.replicate n (SVal.dflt E)) S (by
        simp only [List.length_append, List.length_singleton, List.length_replicate]; omega)) := by
    rw [arrOf_saveM_live hL hj]
    exact congrArg some (arrOf_congr (hset v))
  obtain ⟨st₁, hrun₁, hW₁⟩ := child_stepL (d := d) hv hc.1 ht.1 hf.1 hq hW hnoop hs
  obtain ⟨st', hL', hrun₂, hW'⟩ := hrest d Γ a (σ.withStorage st₁) ref st₀ (pre ++ [v]) S _ ha hW₁
    hc.2 ht.2 hf.2
  refine ⟨st', by simpa only [SVec.toList_cons, List.append_assoc, List.singleton_append]
      using hL', TRuns.append hrun₁ ?_, ?_⟩
  · simpa only [List.length_append, List.length_singleton] using hrun₂
  · simpa only [SVec.toList_cons, List.append_assoc, List.singleton_append] using hW'

/-- What `fillElems` does for the elements `x` of a fixed-size array, from
index `pre.length`. -/
def FixedOK (C : Contract) {E : Ty} {m : Nat} (x : SVec E m) : Prop :=
  ∀ (d : Nat) (Γ : Ctx) {N : Nat} (a : Idx Γ (.alias (.fixed E N))) (σ : State C Γ)
    (ref : SRef C (.ref (.fixed E N))) (st₀ : Storage C) (pre : List (SVal E)) (cur : SVec E N),
    N ≤ 2 ^ 256 → cur.toList = pre ++ List.replicate m (SVal.dflt E) →
    TEnv.get a σ.env = some ref → Wrote st₀ σ.storage ref (.fixed cur) →
    x.All canonH → x.All tightH → x.All fitsH →
    ∃ (st' : Storage C) (cur' : SVec E N), cur'.toList = pre ++ x.toList ∧
      TRuns σ (fillElems d (ArrTy.fixed (E := E) (n := N)) a pre.length x) (σ.withStorage st') ∧
      Wrote st₀ st' ref (.fixed cur')

theorem fixedElems_nil {E : Ty} : FixedOK C (SVec.nil (E := E)) := by
  intro d Γ N a σ ref st₀ pre cur _ hcur _ hW _ _ _
  exact ⟨σ.storage, cur, by simpa only [SVec.toList_nil, List.append_nil,
    List.replicate_zero] using hcur, TRuns.nil σ, hW⟩

theorem fixedElems_cons {E : Ty} {m : Nat} {v : SVal E} {rest : SVec E m}
    (hv : FillOK C v) (hrest : FixedOK C rest) : FixedOK C (SVec.cons v rest) := by
  intro d Γ N a σ ref st₀ pre cur hN hcur ha hW hc ht hf
  simp only [SVec.All] at hc ht hf
  have hj : pre.length < N := by
    have := congrArg List.length hcur
    simp only [SVec.length_toList, List.length_append, List.length_replicate] at this
    omega
  have hq := resolveT_index_lit (C := C) (ArrTy.fixed (E := E) (n := N)) (by omega) ha
    (checkIndex_fixed hW.find hj)
  rw [show (ref.index (.arr .fixed) (pre.length : Int)) =
    ref.append (.atF (pre.length : Int) .nil) by simp only [SRef.index, Path.index_fixed]] at hq
  have hset : ∀ x : SVal E, (cur.set pre.length x).toList =
      (pre ++ [x]) ++ List.replicate m (SVal.dflt E) := by
    intro x
    rw [SVec.toList_set, hcur, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self,
      List.replicate_succ, List.set_cons_zero, List.append_assoc, List.singleton_append]
  have hnoop : (SVal.fixed cur).saveM (.atF (pre.length : Int) .nil) (SVal.dflt E) =
      some (.fixed cur) := by
    rw [fixed_saveM cur hj]
    congr 2
    apply SVec.eq_of_toList_eq
    rw [hset, hcur, List.append_assoc, List.singleton_append, ← List.replicate_succ]
  obtain ⟨st₁, hrun₁, hW₁⟩ := child_stepL (d := d) hv hc.1 ht.1 hf.1 hq hW hnoop
    (fixed_saveM cur hj v)
  obtain ⟨st', cur', hcur', hrun₂, hW'⟩ := hrest d Γ a (σ.withStorage st₁) ref st₀ (pre ++ [v])
    (cur.set pre.length v) hN (hset v) ha hW₁ hc.2 ht.2 hf.2
  refine ⟨st', cur', by simpa only [SVec.toList_cons, List.append_assoc, List.singleton_append]
      using hcur', TRuns.append hrun₁ ?_, hW'⟩
  simpa only [List.length_append, List.length_singleton] using hrun₂

end Fills

end Build

end Solidity
