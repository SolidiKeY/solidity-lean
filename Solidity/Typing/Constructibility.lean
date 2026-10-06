import Solidity.Typing.Reachability

/-!
# Which storages are reachable, exactly

`Reachability.lean` proves reachable ⇒ canonical (`reachable_canon`).  The
converse needs four more facts, which every run keeps and `SVal.canon` does
not say; `SVal.tight` is exactly them:

- an array whose element type has no well-formed default (`BadDup[]`) has
  no slots at all: `push()` needs the default, and nothing else makes one;
- the slots past the end of an array of words are cleared: `pop`, `delete`
  and a shorter copy clear what they leave, and past an end only a reference
  reaches, never a word;
- a fixed-size array has nothing past its end;
- a mapping keyed by anything but a number has no entries: a key is read
  with `Value.asInt`, so a `bool` key is stuck.

Everything canonical and tight is reachable, by one checked program
(`Build.rootsProg`): a word is assigned; a struct is filled member by member
through an alias bound to it; a dynamic array is pushed to its whole run of
slots, then each slot past the end is bound to an alias, popped, and filled
through the alias (the only way to write past an end), then the live
elements are filled; a fixed-size array element by element; a mapping entry
by entry, each created by a `delete` so that an entry holding the default is
there too.  The aliases are `slot d`, one per nesting depth, so a fill never
disturbs the alias its caller is filling through.  The proof tracks the
root's value as a chain of writes at one path (`Wrote`), which is why every
fill starts from the default and from a path where writing what is there
changes nothing.

The other direction is `Prog.run_tight`, a traversal of the interpreter
beside `Prog.run_canon`, for a contract whose types have well-formed
defaults all the way down (`Ty.okDeep`).  It needs two facts about paths:
a word is written only into a live slot (`IdxLive`, from
`State.checkIndex`), and an alias is bound only along numeric keys
(`KeysOK`, which the environment keeps).  Under `Ty.okDeep` the first clause
of `SVal.tight` is vacuous, so no memory object needs tracking: a copy out
of memory has no mapping and nothing past its ends (`SVal.plain`).  Whether
that clause is also necessary for a contract with, say, a `BadDup[]` root is
not proved here: it would need the store typing to claim memory objects only
at types with well-formed defaults, threaded through every allocation.
-/

namespace Solidity

open Semantics
open SemanticsProperties (lookupBy_eq_some_mem lookupBy_defaultForFields SVal.find_nil
  SVal.save_nil SVal.find_append SVal.save_append Prog.run_append Prog.run_cons
  State.findStorage_append State.saveStorage_append)
open Semantics.SVal.canon (canonFields canonElems canonEntries)

variable {C : Contract}

/-! ## The tight values -/

/-- What every reachable value satisfies beyond `SVal.canon`: an array whose
elements have no well-formed default has no slots at all, the slots past the
end of an array of words are cleared, a fixed-size array has no slots past
its end, and a mapping that cannot be indexed has no entries. -/
def Semantics.SVal.tight : SVal → Ty → Prop
  | SVal.struct fields, Ty.ref (RefTy.struct s) => tightFields s fields
  | SVal.array elems shadow _, Ty.ref (RefTy.array E) =>
      (E.defaultOkS = false → elems = [] ∧ shadow = []) ∧
      (E.isPrimitive = true → ∀ w ∈ shadow, w = defaultForTy E) ∧
      tightElems E elems ∧ tightElems E shadow
  | SVal.array elems shadow _, Ty.ref (RefTy.fixed E _) => shadow = [] ∧ tightElems E elems
  | SVal.map entries _, Ty.ref (RefTy.mapping K V) =>
      (K.numericKey = false → entries = []) ∧ tightEntries V entries
  | _, _ => True
where
  tightFields (s : Name) : List (Name × SVal) → Prop
    | [] => True
    | (n, v) :: rest =>
        (match lookupBy n (structDef s) with
         | some T => v.tight T
         | none => True) ∧ tightFields s rest
  tightElems (E : Ty) : List SVal → Prop
    | [] => True
    | v :: rest => v.tight E ∧ tightElems E rest
  tightEntries (V : Ty) : List (Int × SVal) → Prop
    | [] => True
    | (_, v) :: rest => v.tight V ∧ tightEntries V rest

open Semantics.SVal.tight (tightFields tightElems tightEntries)

/-- Every root canonical and tight at its declared type. -/
def TightStorage (C : Contract) (st : List (Name × SVal)) : Prop :=
  ∀ r T v, lookupBy r C.vars = some T → lookupBy r st = some v → v.tight T

namespace Build

/-! ## The builder -/

/-- The storage alias the builder binds at depth `d`. -/
def slot (d : Nat) : Var := .fresh "slot" d

/-- A word written at `l`: `alice.age = 3;`. -/
def primProg : (p : PrimTy) → Loc C (.prim p) → SVal → Prog C
  | .bool, l, .bool b => [.assign l (.val (.simple (.bool b)))]
  | .uint, l, .int z => [.assign l (.val (.simple (.lit z rfl)))]
  | .int, l, .int z => [.assign l (.val (.simple (.lit z rfl)))]
  | _, _, _ => []

mutual

/-- A program that turns the default at `q : T` into `v`, using the aliases
`slot d` and deeper.  A word is assigned.  Anything else binds `slot d` to
`q` and fills through it: a struct member by member; a dynamic array by
pushing every slot it has, popping those past its end one at a time (each
bound to `slot (d+1)` before its `pop`, and filled through it after), then
filling the live elements; a fixed-size array element by element; a mapping
entry by entry, each created by a `delete` first. -/
def fill (d : Nat) : (T : Ty) → SPath C T → SVal → Prog C
  | .prim p, .loc l, v => primProg p l v
  | .ref (.struct s), q, .struct fields =>
      .declStorage (.struct s) (slot d) (some (.path q)) :: fillFields d s fields
  | .ref (.array E), q, .array elems shadow _ =>
      .declStorage (.array E) (slot d) (some (.path q)) ::
        (if hE : E.defaultOkS = true then
          List.replicate (elems.length + shadow.length)
              (.push (.alias (slot d) : SPath C (.array E)) none (by simp [hE])) ++
            fillShadow d E elems.length shadow ++ fillElems d (ArrTy.dyn (E := E)) 0 elems
        else [])
  | .ref (.fixed E n), q, .array elems _ _ =>
      .declStorage (.fixed E n) (slot d) (some (.path q)) ::
        fillElems d (ArrTy.fixed (E := E) (n := n)) 0 elems
  | .ref (.mapping (.prim k) V), q, .map entries _ =>
      .declStorage (.mapping (.prim k) V) (slot d) (some (.path q)) ::
        (if hk : k.isNumeric = true then fillEntries d k V hk entries else [])
  | _, _, _ => []

/-- The members of a struct bound to `slot d`, one after another. -/
def fillFields (d : Nat) (s : Name) : List (Name × SVal) → Prog C
  | [] => []
  | (n, w) :: rest =>
      (match h : lookupBy n (structDef s) with
       | some T => fill (d + 1) T (.loc (.field (.alias (slot d)) n h)) w
       | none => []) ++ fillFields d s rest

/-- The slots past the end of the array bound to `slot d`, from the last:
slot `i` bound, popped, then filled through its alias.  A word slot is only
popped (it is cleared). -/
def fillShadow (d : Nat) (E : Ty) (i : Nat) : List SVal → Prog C
  | [] => []
  | w :: rest =>
      fillShadow d E (i + 1) rest ++
        match E with
        | .prim p => [.pop (E := .prim p) (.alias (slot d))]
        | .ref R =>
            [.declStorage R (slot (d + 1))
                (some (.path (.loc (.index (.arr .dyn) (.alias (slot d))
                  (.simple (.lit (i : Int) rfl)))))),
              .pop (E := .ref R) (.alias (slot d))] ++
              fill (d + 1) (.ref R) (.alias (slot (d + 1))) w

/-- The live elements of the array bound to `slot d`, from index `j`. -/
def fillElems {R : RefTy} {E : Ty} (d : Nat) (a : ArrTy R E) (j : Nat) : List SVal → Prog C
  | [] => []
  | w :: rest =>
      fill (d + 1) E (.loc (.index (.arr a) (.alias (slot d)) (.simple (.lit (j : Int) rfl)))) w ++
        fillElems d a (j + 1) rest

/-- The entries of the mapping bound to `slot d`: each created by `delete`,
then filled. -/
def fillEntries (d : Nat) (k : PrimTy) (V : Ty) (hk : k.isNumeric = true) :
    List (Int × SVal) → Prog C
  | [] => []
  | (key, w) :: rest =>
      .delete (.index .map (.alias (slot d)) (.simple (.lit key hk)) : Loc C V) ::
        (fill (d + 1) V (.loc (.index .map (.alias (slot d)) (.simple (.lit key hk)))) w ++
          fillEntries d k V hk rest)

end

/-- The whole program: every root filled. -/
def rootsProg (C : Contract) : List (Name × SVal) → Prog C
  | [] => []
  | (r, v) :: rest =>
      (match h : C.rootType r with
       | some T => fill 0 T (.loc (.root r h)) v
       | none => []) ++ rootsProg C rest

/-! ## Storage algebra

Reads and writes at a root, as lists: `putSt` is `State.saveStorage`'s
storage, `getSt` is `State.findStorage`. -/

open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne setBy_setBy_self)

/-- The storage `State.saveStorage` leaves. -/
def putSt (st : List (Name × SVal)) (r : Name) (segs : List Seg) (X : SVal) :
    Res (List (Name × SVal)) :=
  match lookupBy r st with
  | some V => do let u ← V.save segs X; pure (setBy r u st)
  | none => .error .stuck

/-- `st'` is `st` with `X` saved at `r.segs`. -/
def Wrote (st st' : List (Name × SVal)) (r : Name) (segs : List Seg) (X : SVal) : Prop :=
  putSt st r segs X = .ok st'

/-- `putSt` at a state's storage is `State.storeRes`. -/
theorem putSt_eq (σ : State) (r : Name) (segs : List Seg) (X : SVal) :
    putSt σ.storage r segs X = σ.storeRes r segs X := rfl

theorem saveStorage_ok {σ : State} {r : Name} {segs : List Seg} {X : SVal}
    {st : List (Name × SVal)} (h : putSt σ.storage r segs X = .ok st) :
    σ.saveStorage r segs X = .ok { σ with storage := st } := by
  rw [SemanticsProperties.State.saveStorage_eq, ← putSt_eq, h]; rfl

theorem putSt_of_saveStorage {σ τ : State} {r : Name} {segs : List Seg} {X : SVal}
    (h : σ.saveStorage r segs X = .ok τ) : putSt σ.storage r segs X = .ok τ.storage := by
  rw [SemanticsProperties.State.saveStorage_eq, ← putSt_eq] at h
  obtain ⟨st, hst, h⟩ := bind_ok_inv h
  cases h; exact hst

theorem setBy_of_lookupBy [DecidableEq κ] {k : κ} {v : α} :
    ∀ {l : List (κ × α)}, lookupBy k l = some v → setBy k v l = l
  | [], h => nomatch h
  | (k', v') :: rest, h => by
    by_cases hk : k = k'
    · subst hk; simp [lookupBy] at h; subst h; simp [setBy]
    · simp only [lookupBy, if_neg hk] at h
      simp [setBy, hk, setBy_of_lookupBy h]

/-- Saving twice at one path keeps the second: `alice.age = 1; alice.age = 2;`. -/
theorem save_save : ∀ {segs : List Seg} {v v₁ a : SVal} (b : SVal),
    v.save segs a = .ok v₁ → v₁.save segs b = v.save segs b
  | [], v, v₁, a, b, h => by
    rw [SVal.save_nil] at h; cases h; rw [SVal.save_nil, SVal.save_nil]
  | .field n :: rest, .struct fields, v₁, a, b, h => by
    simp only [SVal.save] at h ⊢
    split at h
    · rename_i old hold
      obtain ⟨u, hu, h⟩ := bind_ok_inv h
      cases h
      simp only [SVal.save, lookupBy_setBy_self, save_save b hu]
      cases old.save rest b <;> simp [setBy_setBy_self]
    · exact nomatch h
  | .at i :: rest, .array elems sh fx, v₁, a, b, h => by
    simp only [SVal.save] at h
    split at h
    · rename_i hb
      obtain ⟨u, hu, h⟩ := bind_ok_inv h
      cases h
      have hlen : ((elems ++ sh).set i.toNat u).length = (elems ++ sh).length := List.length_set ..
      have hb' : 0 ≤ i ∧ i.toNat < (((elems ++ sh).set i.toNat u).take elems.length ++
          ((elems ++ sh).set i.toNat u).drop elems.length).length := by
        rw [List.take_append_drop, hlen]; exact hb
      simp only [SVal.save, dif_pos hb', dif_pos hb]
      have hget : (((elems ++ sh).set i.toNat u).take elems.length ++
          ((elems ++ sh).set i.toNat u).drop elems.length).get ⟨i.toNat, hb'.2⟩ = u := by
        simp [List.take_append_drop, List.getElem_set_self]
      rw [hget, save_save b hu]
      have htl : (((elems ++ sh).set i.toNat u).take elems.length).length = elems.length := by
        simp
      cases ((elems ++ sh).get ⟨i.toNat, hb.2⟩).save rest b <;>
        simp [List.take_append_drop, htl]
    · exact nomatch h
  | .at i :: rest, .map entries dflt, v₁, a, b, h => by
    simp only [SVal.save] at h
    split at h
    · rename_i old hold
      obtain ⟨u, hu, h⟩ := bind_ok_inv h
      cases h
      simp only [SVal.save, lookupBy_setBy_self, hold, save_save b hu]
      cases old.save rest b <;> simp [setBy_setBy_self]
    · rename_i hold
      obtain ⟨u, hu, h⟩ := bind_ok_inv h
      cases h
      simp only [SVal.save, lookupBy_setBy_self, hold, save_save b hu]
      cases dflt.save rest b <;> simp [setBy_setBy_self]
  | .field _ :: _, .prim _, _, _, _, h | .at _ :: _, .prim _, _, _, _, h
  | .at _ :: _, .struct _, _, _, _, h | .field _ :: _, .array .., _, _, _, h
  | .field _ :: _, .map .., _, _, _, h => by simp [SVal.save] at h

/-! ### Chains of writes at one path -/

theorem Wrote.trans {st₀ st₁ st₂ : List (Name × SVal)} {r : Name} {segs : List Seg}
    {X Y : SVal} (h₁ : Wrote st₀ st₁ r segs X) (h₂ : Wrote st₁ st₂ r segs Y) :
    Wrote st₀ st₂ r segs Y := by
  unfold Wrote putSt at *
  split at h₁
  · rename_i V hV
    obtain ⟨u, hu, h₁⟩ := bind_ok_inv h₁
    cases h₁
    rw [lookupBy_setBy_self] at h₂
    simp only [save_save Y hu] at h₂
    obtain ⟨u', hu', h₂⟩ := bind_ok_inv h₂
    cases h₂
    simp [hu', setBy_setBy_self]; rfl
  · exact nomatch h₁

/-- After a write, saving the same value again changes nothing. -/
theorem Wrote.noop {st₀ st : List (Name × SVal)} {r : Name} {segs : List Seg} {X : SVal}
    (h : Wrote st₀ st r segs X) : Wrote st st r segs X := by
  unfold Wrote putSt at *
  split at h
  · rename_i V hV
    obtain ⟨u, hu, h⟩ := bind_ok_inv h
    cases h
    rw [lookupBy_setBy_self]
    simp only [save_save X hu, hu]
    simp [setBy_setBy_self]; rfl
  · exact nomatch h

/-- After a write, the path reads what was written. -/
theorem Wrote.find {st₀ st : List (Name × SVal)} {r : Name} {segs : List Seg} {X : SVal}
    (h : Wrote st₀ st r segs X) :
    ∃ V, lookupBy r st = some V ∧ V.find segs = .ok X := by
  unfold Wrote putSt at h
  split at h
  · obtain ⟨u, hu, h⟩ := bind_ok_inv h
    cases h
    exact ⟨u, lookupBy_setBy_self _ _ _, SemanticsProperties.SVal.find_save_same hu⟩
  · exact nomatch h

theorem Wrote.findStorage {σ : State} {st₀ : List (Name × SVal)} {r : Name} {segs : List Seg}
    {X : SVal} (h : Wrote st₀ σ.storage r segs X) : σ.findStorage r segs = .ok X := by
  obtain ⟨V, hV, hf⟩ := h.find
  simp [State.findStorage, hV, hf]

/-- A write below `segs` is a write at `segs` of what is there, updated. -/
theorem Wrote.up {st st' : List (Name × SVal)} {r : Name} {segs rest : List Seg}
    {N N' w : SVal} (hN : ∃ V, lookupBy r st = some V ∧ V.find segs = .ok N)
    (hs : N.save rest w = .ok N') (h : Wrote st st' r (segs ++ rest) w) :
    Wrote st st' r segs N' := by
  obtain ⟨V, hV, hf⟩ := hN
  unfold Wrote putSt at *
  simp only [hV] at h ⊢
  rw [SVal.save_append V segs rest w N hf, hs] at h
  exact h

/-! ### One step down -/

theorem save_field {fs : List (Name × SVal)} {n : Name} {c : SVal} (w : SVal)
    (h : lookupBy n fs = some c) :
    (SVal.struct fs).save [.field n] w = .ok (.struct (setBy n w fs)) := by
  simp [SVal.save, h, SVal.save_nil]; rfl

theorem save_at_map (es : List (Int × SVal)) (dflt : SVal) (k : Int) (w : SVal) :
    (SVal.map es dflt).save [.at k] w = .ok (.map (setBy k w es) dflt) := by
  simp only [SVal.save]
  split <;> rfl

/-- The first slot past the end, written: a popped slot filled through its alias. -/
theorem save_at_shadow (es sh : List SVal) (x w : SVal) (fx : Bool) :
    (SVal.array es (x :: sh) fx).save [.at (es.length : Int)] w = .ok (.array es (w :: sh) fx) := by
  have hb : 0 ≤ (es.length : Int) ∧ (es.length : Int).toNat < (es ++ x :: sh).length := by
    simp
  simp only [SVal.save]
  rw [dif_pos hb]
  simp [bind, Except.bind, List.set_append_right]

/-- A live element written: `values[j] = w;`. -/
theorem save_at_live (es rest sh : List SVal) (x w : SVal) (fx : Bool) :
    (SVal.array (es ++ x :: rest) sh fx).save [.at (es.length : Int)] w =
      .ok (.array (es ++ w :: rest) sh fx) := by
  have hb : 0 ≤ (es.length : Int) ∧ (es.length : Int).toNat < (es ++ x :: rest ++ sh).length := by
    simp
  simp only [SVal.save]
  rw [dif_pos hb]
  have hset : (es ++ x :: rest ++ sh).set (es.length : Int).toNat w = (es ++ w :: rest) ++ sh := by
    simp [List.set_append_right]
  have hl : (es ++ x :: rest).length = (es ++ w :: rest).length := by simp
  simp only [bind, Except.bind, hset, hl, List.take_left', List.drop_left']

/-- Saving what a path already holds, one step below a no-op write, is a no-op. -/
theorem Wrote.down {st : List (Name × SVal)} {r : Name} {segs rest : List Seg} {N c : SVal}
    (h : Wrote st st r segs N) (hs : N.save rest c = .ok N) : Wrote st st r (segs ++ rest) c := by
  obtain ⟨V, hV, hf⟩ := h.find
  unfold Wrote putSt at *
  simp only [hV] at h ⊢
  rw [SVal.save_append V segs rest c N hf, hs]
  exact h

/-! ## One statement at a time -/

/-- `slot d` is bound to `r.segs`. -/
def Bound (σ : State) (d : Nat) (r : Name) (segs : List Seg) : Prop :=
  lookupBy (slot d) σ.env = some (.spath r segs)

/-- The aliases above depth `d` are as they were. -/
def Keep (d : Nat) (σ σ' : State) : Prop :=
  ∀ j < d, lookupBy (slot j) σ'.env = lookupBy (slot j) σ.env

theorem Keep.refl (d : Nat) (σ : State) : Keep d σ σ := fun _ _ => rfl

theorem Keep.trans {d : Nat} {σ₁ σ₂ σ₃ : State} (h₁ : Keep d σ₁ σ₂) (h₂ : Keep d σ₂ σ₃) :
    Keep d σ₁ σ₃ := fun j hj => (h₂ j hj).trans (h₁ j hj)

theorem Keep.of_env {d : Nat} {σ σ' : State} (h : σ'.env = σ.env) : Keep d σ σ' :=
  fun j _ => by rw [h]

theorem Keep.mono {d e : Nat} {σ σ' : State} (h : Keep e σ σ') (hde : d ≤ e) : Keep d σ σ' :=
  fun j hj => h j (by omega)

theorem slot_inj {j k : Nat} (h : slot j = slot k) : j = k := by
  simp only [slot, Var.fresh.injEq] at h; exact h.2

/-- Binding `slot d` keeps the aliases above it. -/
theorem Keep.setEnv (d : Nat) (σ : State) (b : Binding) : Keep d σ (σ.setEnv (slot d) b) := by
  intro j hj
  show lookupBy (slot j) (setBy (slot d) b σ.env) = _
  rw [lookupBy_setBy_ne (fun h => by have := slot_inj h; omega)]

theorem Keep.bound {d e : Nat} {σ σ' : State} {r : Name} {segs : List Seg} (h : Keep e σ σ')
    (hd : d < e) (hb : Bound σ d r segs) : Bound σ' d r segs := by
  unfold Bound; rw [h d hd]; exact hb

theorem aliasPath_slot {σ : State} {d : Nat} {r : Name} {segs : List Seg}
    (h : Bound σ d r segs) : aliasPath σ (slot d) = .ok (r, segs) := by
  unfold Bound at h
  simp [aliasPath, State.getEnv, h]; rfl

theorem resolve_alias {σ : State} {d : Nat} {R : RefTy} {r : Name} {segs : List Seg}
    (h : Bound σ d r segs) : (SPath.alias (C := C) (R := R) (slot d)).resolve σ = .ok (r, segs) := by
  unfold Bound at h
  simp [SPath.resolve, aliasPath, State.getEnv, h]; rfl

theorem resolve_field {σ : State} {d : Nat} {s n : Name} {T : Ty} {r : Name} {segs : List Seg}
    (hf : C.fieldType s n = some T) (h : Bound σ d r segs) :
    (SPath.loc (Loc.field (.alias (slot d)) n hf)).resolve σ = .ok (r, segs ++ [.field n]) := by
  simp [SPath.resolve, Loc.resolve, aliasPath_slot h, bind, Except.bind]
  rfl

theorem resolve_index_arr {σ : State} {d : Nat} {R : RefTy} {E : Ty} (a : ArrTy R E) {j : Nat}
    {r : Name} {segs : List Seg} {es sh : List SVal} {fx : Bool} (h : Bound σ d r segs)
    (hf : σ.findStorage r segs = .ok (.array es sh fx)) (hj : j < es.length) :
    (SPath.loc (C := C) (Loc.index (.arr a) (.alias (slot d)) (.simple (.lit (j : Int) rfl)))).resolve σ =
      .ok (r, segs ++ [.at (j : Int)]) := by
  simp [SPath.resolve, Loc.resolve, aliasPath_slot h, Val.eval, Simple.eval, Value.asInt,
    State.checkIndex, hf, hj, bind, Except.bind, pure, Except.pure]

theorem resolve_index_map {σ : State} {d : Nat} {k : PrimTy} {V : Ty} {key : Int}
    (hk : k.isNumeric = true) {r : Name} {segs : List Seg} {es : List (Int × SVal)} {dflt : SVal}
    (h : Bound σ d r segs) (hf : σ.findStorage r segs = .ok (.map es dflt)) :
    (SPath.loc (C := C) (Loc.index (V := V) .map (.alias (slot d)) (.simple (.lit key hk)))).resolve σ =
      .ok (r, segs ++ [.at key]) := by
  simp [SPath.resolve, Loc.resolve, aliasPath_slot h, Val.eval, Simple.eval, Value.asInt,
    State.checkIndex, hf, bind, Except.bind, pure, Except.pure]

theorem run_decl {σ : State} {R : RefTy} {x : Var} {q : SPath C (.ref R)} {r : Name}
    {segs : List Seg} (hq : q.resolve σ = .ok (r, segs)) :
    Stmt.run σ (.declStorage R x (some (.path q))) = .ok (σ.setEnv x (.spath r segs)) := by
  simp [Stmt.run, ARhs.bind, hq, bind, Except.bind, pure, Except.pure]

theorem run_push {σ : State} {d : Nat} {E : Ty} {r : Name} {segs : List Seg} {es : List SVal}
    {fx : Bool} (hd : (none.isSome || E.defaultOkS) = true) (hb : Bound σ d r segs)
    (hf : σ.findStorage r segs = .ok (.array es [] fx)) :
    Stmt.run σ (.push (C := C) (.alias (slot d) : SPath C (.array E)) none hd) =
      σ.saveStorage r segs (.array (es ++ [defaultForTy E]) [] fx) := by
  simp [Stmt.run, resolve_alias hb, pushAt, hf, pushSlot, Src.pushVal, bind, Except.bind, pure,
    Except.pure]

theorem run_pop {σ : State} {d : Nat} {E : Ty} {r : Name} {segs : List Seg}
    {es sh : List SVal} {last : SVal} {fx : Bool} (hb : Bound σ d r segs)
    (hf : σ.findStorage r segs = .ok (.array (es ++ [last]) sh fx)) :
    Stmt.run σ (.pop (C := C) (E := E) (.alias (slot d))) =
      σ.saveStorage r segs
        (.array es ((if E.isMapping then last else last.defaultOf) :: sh) fx) := by
  simp [Stmt.run, resolve_alias hb, popAt, hf, bind, Except.bind]

theorem run_delete {σ : State} {T : Ty} {l : Loc C T} {r : Name} {segs : List Seg} {cur : SVal}
    (hl : l.resolve σ = .ok (r, segs)) (hf : σ.findStorage r segs = .ok cur) :
    Stmt.run σ (.delete l) = σ.saveStorage r segs cur.defaultOf := by
  simp [Stmt.run, hl, hf, bind, Except.bind]

theorem run_primProg {σ : State} {p : PrimTy} {l : Loc C (.prim p)} {r : Name} {segs : List Seg}
    {v : SVal} (hl : l.resolve σ = .ok (r, segs)) (hv : v.canon (.prim p)) :
    Prog.run σ (primProg p l v) = σ.saveStorage r segs v := by
  cases p <;> cases v <;> try (exact hv.elim)
  all_goals rename_i pv; cases pv <;> try (exact hv.elim)
  all_goals simp [primProg, Prog.run, Stmt.run, Src.value, Val.eval, Simple.eval, hl,
    Value.toSVal, bind, Except.bind, pure, Except.pure]
  all_goals cases σ.saveStorage r segs _ <;> rfl

/-! ## Defaults and association lists -/

/-- `delete` of a fresh default changes nothing: a popped fresh slot and a
deleted absent mapping entry are the type's default. -/
theorem defaultOf_default (T : Ty) : (defaultForTy T).defaultOf = defaultForTy T := by
  induction T using defaultForTy.induct
    (motive2 := fun l => SVal.defaultOf.defaultOfFields (defaultForFields l) = defaultForFields l)
    with
  | case1 => simp [defaultForTy, SVal.defaultOf]
  | case2 => simp [defaultForTy, SVal.defaultOf]
  | case3 => simp [defaultForTy, SVal.defaultOf]
  | case4 name ih => rw [defaultForTy]; simp only [SVal.defaultOf, ih]
  | case5 elem => simp [defaultForTy, SVal.defaultOf, SVal.defaultOf.defaultOfElems]
  | case6 elem n ih =>
    rw [defaultForTy]; simp only [SVal.defaultOf]
    congr 1
    induction n with
    | zero => rfl
    | succ k ihk => simp only [List.replicate_succ, SVal.defaultOf.defaultOfElems, ih, ihk]
  | case7 key value ih => rw [defaultForTy]; rfl
  | case8 => simp [defaultForFields, SVal.defaultOf.defaultOfFields]
  | case9 n t rest iht ihrest =>
    simp only [defaultForFields, SVal.defaultOf.defaultOfFields, iht, ihrest]

/-- The structs `defaultOkS` admits: no member name twice, and every member
of a type `defaultOkS` admits. -/
theorem struct_ok {s : Name} (h : s ∈ defaultOkStructs) :
    nodupKeysB (structDef s) = true ∧ ∀ nt ∈ structDef s, nt.2.defaultOkS = true := by
  simp only [defaultOkStructs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨by decide, ?_⟩ <;> simp [structDef, Ty.defaultOkS, defaultOkStructs]

theorem lookupBy_append_left_none [DecidableEq κ] {k : κ} {l₂ : List (κ × α)} :
    ∀ {l₁ : List (κ × α)}, lookupBy k l₁ = none → lookupBy k (l₁ ++ l₂) = lookupBy k l₂
  | [], _ => rfl
  | (k', v') :: rest, h => by
    by_cases hk : k = k'
    · simp [lookupBy, hk] at h
    · simp only [lookupBy, if_neg hk] at h
      simp [lookupBy, hk, lookupBy_append_left_none h]

theorem setBy_append_left_none [DecidableEq κ] {k : κ} {v : α} {l₂ : List (κ × α)} :
    ∀ {l₁ : List (κ × α)}, lookupBy k l₁ = none → setBy k v (l₁ ++ l₂) = l₁ ++ setBy k v l₂
  | [], _ => rfl
  | (k', v') :: rest, h => by
    by_cases hk : k = k'
    · simp [lookupBy, hk] at h
    · simp only [lookupBy, if_neg hk] at h
      simp [setBy, hk, setBy_append_left_none h]

/-- Writing a member that is there, in the middle: `alice.age = 3;`. -/
theorem setBy_mid [DecidableEq κ] {k : κ} {v x : α} {l₁ l₂ : List (κ × α)}
    (h : lookupBy k l₁ = none) : setBy k v (l₁ ++ (k, x) :: l₂) = l₁ ++ (k, v) :: l₂ := by
  rw [setBy_append_left_none h]; simp [setBy]

theorem lookupBy_mid [DecidableEq κ] {k : κ} {x : α} {l₁ l₂ : List (κ × α)}
    (h : lookupBy k l₁ = none) : lookupBy k (l₁ ++ (k, x) :: l₂) = some x := by
  rw [lookupBy_append_left_none h]; simp [lookupBy]

theorem nodupKeysB_mid [DecidableEq κ] {k : κ} {x : α} {l₂ : List (κ × α)} :
    ∀ {l₁ : List (κ × α)}, nodupKeysB (l₁ ++ (k, x) :: l₂) = true → lookupBy k l₁ = none
  | [], _ => rfl
  | (k', v') :: rest, h => by
    simp only [List.cons_append, nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    by_cases hk : k = k'
    · subst hk
      rw [lookupBy_mid (nodupKeysB_mid h.2)] at h
      exact nomatch h.1
    · simp [lookupBy, hk, nodupKeysB_mid h.2]

/-- A write succeeds where another write along the same path did. -/
theorem save_ok_any : ∀ {segs : List Seg} {v v₁ a : SVal} (b : SVal),
    v.save segs a = .ok v₁ → ∃ v₂, v.save segs b = .ok v₂
  | [], v, _, _, b, _ => ⟨b, SVal.save_nil v b⟩
  | .field n :: rest, .struct fields, v₁, a, b, h => by
    simp only [SVal.save] at h ⊢
    split at h
    · rename_i old hold
      obtain ⟨u, hu, -⟩ := bind_ok_inv h
      obtain ⟨u', hu'⟩ := save_ok_any b hu
      simp only [hu']; exact ⟨_, rfl⟩
    · exact nomatch h
  | .at i :: rest, .array elems sh fx, v₁, a, b, h => by
    simp only [SVal.save] at h ⊢
    split at h
    · rename_i hb
      obtain ⟨u, hu, -⟩ := bind_ok_inv h
      obtain ⟨u', hu'⟩ := save_ok_any b hu
      rw [dif_pos hb, hu']; exact ⟨_, rfl⟩
    · exact nomatch h
  | .at i :: rest, .map entries dflt, v₁, a, b, h => by
    simp only [SVal.save] at h ⊢
    split at h
    · rename_i old hold
      obtain ⟨u, hu, -⟩ := bind_ok_inv h
      obtain ⟨u', hu'⟩ := save_ok_any b hu
      simp only [hu']; exact ⟨_, rfl⟩
    · rename_i hold
      obtain ⟨u, hu, -⟩ := bind_ok_inv h
      obtain ⟨u', hu'⟩ := save_ok_any b hu
      simp only [hu']; exact ⟨_, rfl⟩
  | .field _ :: _, .prim _, _, _, _, h | .at _ :: _, .prim _, _, _, _, h
  | .at _ :: _, .struct _, _, _, _, h | .field _ :: _, .array .., _, _, _, h
  | .field _ :: _, .map .., _, _, _, h => by simp [SVal.save] at h

theorem Wrote.any {st₀ st : List (Name × SVal)} {r : Name} {segs : List Seg} {X : SVal}
    (h : Wrote st₀ st r segs X) (Y : SVal) : ∃ st', Wrote st₀ st' r segs Y := by
  unfold Wrote putSt at *
  split at h
  · obtain ⟨u, hu, -⟩ := bind_ok_inv h
    obtain ⟨u', hu'⟩ := save_ok_any Y hu
    rw [hu']; exact ⟨_, rfl⟩
  · exact nomatch h

/-- A statement that only saves at `r.segs`, as a chain step. -/
theorem Wrote.save {σ τ : State} {st₀ : List (Name × SVal)} {r : Name} {segs : List Seg}
    {X Y : SVal} (hc : Wrote st₀ σ.storage r segs X) (h : σ.saveStorage r segs Y = .ok τ) :
    Wrote st₀ τ.storage r segs Y :=
  hc.trans (putSt_of_saveStorage h)

theorem saveStorage_env {σ τ : State} {r : Name} {segs : List Seg} {Y : SVal}
    (h : σ.saveStorage r segs Y = .ok τ) : τ.env = σ.env :=
  (SemanticsProperties.State.saveStorage_frame h).2.2.1

theorem Wrote.saveStorage {σ : State} {st₀ : List (Name × SVal)} {r : Name} {segs : List Seg}
    {X : SVal} (hc : Wrote st₀ σ.storage r segs X) (Y : SVal) :
    ∃ τ, σ.saveStorage r segs Y = .ok τ ∧ Wrote st₀ τ.storage r segs Y ∧ τ.env = σ.env := by
  obtain ⟨st', h'⟩ := hc.noop.any Y
  have h := saveStorage_ok h'
  exact ⟨_, h, hc.save h, saveStorage_env h⟩

/-! ## The builder writes what it is given -/

/-- What `fill` does for one value `v`: from the default at `q`, it leaves
`v` there, changing nothing else, and keeps the aliases above depth `d`. -/
def FillOK (C : Contract) (v : SVal) : Prop :=
  ∀ (T : Ty) (d : Nat) (q : SPath C T) (σ : State) (r : Name) (segs : List Seg),
    v.canon T → v.tight T → T.defaultOkS = true → q.resolve σ = .ok (r, segs) →
    Wrote σ.storage σ.storage r segs (defaultForTy T) →
    ∃ σ', Prog.run σ (fill d T q v) = .ok σ' ∧ Wrote σ.storage σ'.storage r segs v ∧ Keep d σ σ'

/-- A child filled below the node at `r.segs`: the node, `N`, becomes `N'`. -/
theorem child_step {d : Nat} {T : Ty} {q : SPath C T} {σ : State} {st₀ : List (Name × SVal)}
    {r : Name} {segs : List Seg} {seg : Seg} {N N' w : SVal}
    (hw : FillOK C w) (hc : w.canon T) (ht : w.tight T) (hok : T.defaultOkS = true)
    (hq : q.resolve σ = .ok (r, segs ++ [seg])) (hchain : Wrote st₀ σ.storage r segs N)
    (hnoop : N.save [seg] (defaultForTy T) = .ok N) (hs : N.save [seg] w = .ok N') :
    ∃ σ', Prog.run σ (fill (d + 1) T q w) = .ok σ' ∧ Wrote st₀ σ'.storage r segs N' ∧
      Keep (d + 1) σ σ' := by
  obtain ⟨σ', hrun, hW, hK⟩ :=
    hw T (d + 1) q σ r (segs ++ [seg]) hc ht hok hq (hchain.noop.down hnoop)
  exact ⟨σ', hrun, hchain.trans (Wrote.up hchain.noop.find hs hW), hK⟩

theorem fillFields_run {d : Nat} {s r : Name} {segs : List Seg} :
    ∀ (todo pre : List (Name × SVal)) (sdRest : List (Name × Ty)) (σ : State)
      (st₀ : List (Name × SVal)),
      (∀ nw ∈ todo, FillOK C nw.2) → canonFields s todo → tightFields s todo →
      todo.map (·.1) = sdRest.map (·.1) →
      (∀ nt ∈ sdRest, lookupBy nt.1 (structDef s) = some nt.2 ∧ nt.2.defaultOkS = true ∧
        lookupBy nt.1 pre = none) →
      nodupKeysB sdRest = true →
      Bound σ d r segs → Wrote st₀ σ.storage r segs (.struct (pre ++ defaultForFields sdRest)) →
      ∃ σ', Prog.run σ (fillFields (C := C) d s todo) = .ok σ' ∧
        Wrote st₀ σ'.storage r segs (.struct (pre ++ todo)) ∧ Keep (d + 1) σ σ'
  | [], pre, sdRest, σ, st₀, _, _, _, hmap, _, _, _, hW => by
    cases sdRest with
    | cons _ _ => simp at hmap
    | nil => exact ⟨σ, rfl, by simpa [defaultForFields] using hW, Keep.refl _ _⟩
  | (n, w) :: todo, pre, sdRest, σ, st₀, hIH, hc, ht, hmap, hsd, hnd, hB, hW => by
    cases sdRest with
    | nil => simp at hmap
    | cons nt sdRest =>
      obtain ⟨n', t⟩ := nt
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨rfl, hmap⟩ := hmap
      obtain ⟨hlook, hok, hpre⟩ := hsd (n, t) (List.mem_cons_self ..)
      dsimp only at hlook hok hpre
      simp only [nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hnd
      simp only [canonFields, hlook] at hc
      simp only [tightFields, hlook] at ht
      simp only [fillFields]
      rw [Prog.run_append]
      split
      · rename_i T heq
        have hT : T = t := by rw [hlook] at heq; exact (Option.some.inj heq).symm
        subst hT
        have hN : (SVal.struct (pre ++ defaultForFields ((n, T) :: sdRest))).save [.field n]
            (defaultForTy T) = .ok (.struct (pre ++ defaultForFields ((n, T) :: sdRest))) := by
          simp only [defaultForFields]
          rw [save_field _ (lookupBy_mid hpre), setBy_of_lookupBy (lookupBy_mid hpre)]
        have hs : (SVal.struct (pre ++ defaultForFields ((n, T) :: sdRest))).save [.field n] w =
            .ok (.struct ((pre ++ [(n, w)]) ++ defaultForFields sdRest)) := by
          simp only [defaultForFields]
          rw [save_field _ (lookupBy_mid hpre), setBy_mid hpre]; simp
        obtain ⟨σ₁, hrun₁, hW₁, hK₁⟩ := child_step (hIH (n, w) (List.mem_cons_self ..)) hc.1 ht.1
          hok (resolve_field _ hB) hW hN hs
        obtain ⟨σ₂, hrun₂, hW₂, hK₂⟩ := fillFields_run todo (pre ++ [(n, w)]) sdRest σ₁ st₀
          (fun nw hm => hIH nw (List.mem_cons_of_mem _ hm)) hc.2 ht.2 hmap
          (fun nt hm => by
            obtain ⟨h1, h2, h3⟩ := hsd nt (List.mem_cons_of_mem _ hm)
            refine ⟨h1, h2, ?_⟩
            rw [lookupBy_append_left_none h3]
            have hne : nt.1 ≠ n := by
              intro he
              have := lookupBy_isSome_of_mem (k := nt.1) (v := nt.2) hm
              rw [he, hnd.1] at this; exact nomatch this
            simp [lookupBy, hne])
          hnd.2 (hK₁.bound (Nat.lt_succ_self d) hB) hW₁
        refine ⟨σ₂, by rw [hrun₁]; exact hrun₂, by simpa using hW₂, hK₁.trans hK₂⟩
      · rename_i heq; rw [hlook] at heq; exact nomatch heq

theorem fillElems_run {R : RefTy} {E : Ty} {d : Nat} (a : ArrTy R E) {r : Name}
    {segs : List Seg} (hE : E.defaultOkS = true) :
    ∀ (L pre sh : List SVal) (fx : Bool) (σ : State) (st₀ : List (Name × SVal)),
      (∀ w ∈ L, FillOK C w) → canonElems E L → tightElems E L → Bound σ d r segs →
      Wrote st₀ σ.storage r segs (.array (pre ++ List.replicate L.length (defaultForTy E)) sh fx) →
      ∃ σ', Prog.run σ (fillElems (C := C) d a pre.length L) = .ok σ' ∧
        Wrote st₀ σ'.storage r segs (.array (pre ++ L) sh fx) ∧ Keep (d + 1) σ σ'
  | [], pre, sh, fx, σ, st₀, _, _, _, _, hW => ⟨σ, rfl, by simpa using hW, Keep.refl _ _⟩
  | w :: L, pre, sh, fx, σ, st₀, hIH, hc, ht, hB, hW => by
    simp only [fillElems]
    rw [Prog.run_append]
    simp only [List.length_cons, List.replicate_succ] at hW
    have hq := resolve_index_arr (C := C) a (j := pre.length) hB hW.findStorage (by simp)
    obtain ⟨σ₁, hrun₁, hW₁, hK₁⟩ := child_step (d := d) (hIH w (List.mem_cons_self ..)) hc.1 ht.1
      hE hq hW (save_at_live ..) (save_at_live ..)
    obtain ⟨σ₂, hrun₂, hW₂, hK₂⟩ := fillElems_run a hE L (pre ++ [w]) sh fx σ₁ st₀
      (fun w hm => hIH w (List.mem_cons_of_mem _ hm)) hc.2 ht.2
      (hK₁.bound (Nat.lt_succ_self d) hB) (by simpa using hW₁)
    refine ⟨σ₂, ?_, by simpa using hW₂, hK₁.trans hK₂⟩
    rw [hrun₁]; simpa using hrun₂

/-- `values.push();` `n` times on an array with nothing past its end. -/
theorem pushes_run {E : Ty} {d : Nat} {r : Name} {segs : List Seg}
    (hd : (none.isSome || E.defaultOkS) = true) :
    ∀ (n : Nat) (es : List SVal) (σ : State) (st₀ : List (Name × SVal)),
      Bound σ d r segs → Wrote st₀ σ.storage r segs (.array es [] false) →
      ∃ σ', Prog.run σ (List.replicate n
          (Stmt.push (C := C) (.alias (slot d) : SPath C (.array E)) none hd)) = .ok σ' ∧
        Wrote st₀ σ'.storage r segs (.array (es ++ List.replicate n (defaultForTy E)) [] false) ∧
        σ'.env = σ.env
  | 0, es, σ, st₀, _, hW => ⟨σ, rfl, by simpa using hW, rfl⟩
  | n + 1, es, σ, st₀, hB, hW => by
    obtain ⟨τ, hτ, hWτ, henv⟩ := hW.saveStorage (.array (es ++ [defaultForTy E]) [] false)
    have hB' : Bound τ d r segs := by unfold Bound; rw [henv]; exact hB
    obtain ⟨σ', hrun, hW', henv'⟩ := pushes_run hd n (es ++ [defaultForTy E]) τ st₀ hB' hWτ
    refine ⟨σ', ?_, by simpa using hW', henv'.trans henv⟩
    rw [List.replicate_succ, Prog.run_cons, run_push hd hB hW.findStorage, hτ]
    exact hrun

theorem fillShadow_run {E : Ty} {d : Nat} {r : Name} {segs : List Seg}
    (hE : E.defaultOkS = true) :
    ∀ (S SH : List SVal) (i : Nat) (σ : State) (st₀ : List (Name × SVal)),
      (∀ w ∈ S, FillOK C w) → canonElems E S → tightElems E S →
      (E.isPrimitive = true → ∀ w ∈ S, w = defaultForTy E) → Bound σ d r segs →
      Wrote st₀ σ.storage r segs (.array (List.replicate (i + S.length) (defaultForTy E)) SH false) →
      ∃ σ', Prog.run σ (fillShadow (C := C) d E i S) = .ok σ' ∧
        Wrote st₀ σ'.storage r segs (.array (List.replicate i (defaultForTy E)) (S ++ SH) false) ∧
        Keep (d + 1) σ σ'
  | [], SH, i, σ, st₀, _, _, _, _, _, hW => ⟨σ, rfl, by simpa using hW, Keep.refl _ _⟩
  | w :: S, SH, i, σ, st₀, hIH, hc, ht, hprim, hB, hW => by
    simp only [fillShadow]
    rw [Prog.run_append]
    obtain ⟨σ₁, hrun₁, hW₁, hK₁⟩ := fillShadow_run hE S SH (i + 1) σ st₀
      (fun w hm => hIH w (List.mem_cons_of_mem _ hm)) hc.2 ht.2
      (fun hp w hm => hprim hp w (List.mem_cons_of_mem _ hm)) hB
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using hW)
    rw [hrun₁]
    have hB₁ : Bound σ₁ d r segs := hK₁.bound (Nat.lt_succ_self d) hB
    rw [List.replicate_succ'] at hW₁
    simp only [bind, Except.bind]
    obtain ⟨τ, hτ, hWτ, henv⟩ := hW₁.saveStorage
      (.array (List.replicate i (defaultForTy E)) (defaultForTy E :: (S ++ SH)) false)
    have hpop : Stmt.run σ₁ (.pop (C := C) (E := E) (.alias (slot d))) = .ok τ := by
      rw [run_pop hB₁ hW₁.findStorage]
      have : (if E.isMapping = true then defaultForTy E else (defaultForTy E).defaultOf) =
          defaultForTy E := by
        split <;> simp [defaultOf_default]
      rw [this]; exact hτ
    cases E with
    | prim p =>
      have hw : w = defaultForTy (.prim p) := hprim rfl w (List.mem_cons_self ..)
      subst hw
      refine ⟨τ, ?_, by simpa using hWτ, hK₁.trans (Keep.of_env henv)⟩
      simp only [Prog.run_cons, hpop, bind, Except.bind]; rfl
    | ref R =>
      dsimp only
      have hq := resolve_index_arr (C := C) (ArrTy.dyn (E := .ref R)) (j := i) hB₁
        hW₁.findStorage (by simp)
      have hB₂ : Bound (σ₁.setEnv (slot (d + 1)) (.spath r (segs ++ [.at (i : Int)]))) d r segs :=
        (Keep.setEnv (d + 1) σ₁ _).bound (Nat.lt_succ_self d) hB₁
      obtain ⟨τ', hτ', hτ'st, hτ'env⟩ : ∃ τ', Stmt.run
          (σ₁.setEnv (slot (d + 1)) (.spath r (segs ++ [.at (i : Int)])))
          (.pop (C := C) (E := .ref R) (.alias (slot d))) = .ok τ' ∧ τ'.storage = τ.storage ∧
          τ'.env = setBy (slot (d + 1)) (.spath r (segs ++ [.at (i : Int)])) σ₁.env := by
        refine ⟨{ σ₁.setEnv (slot (d + 1)) (.spath r (segs ++ [.at (i : Int)])) with
          storage := τ.storage }, ?_, rfl, rfl⟩
        rw [run_pop hB₂ hW₁.findStorage]
        have : (if (Ty.ref R).isMapping = true then defaultForTy (.ref R)
            else (defaultForTy (.ref R)).defaultOf) = defaultForTy (.ref R) := by
          split <;> simp [defaultOf_default]
        rw [this]
        exact saveStorage_ok (σ := σ₁.setEnv (slot (d + 1)) (.spath r (segs ++ [.at (i : Int)])))
          (putSt_of_saveStorage (σ := σ₁) hτ)
      have hBτ : Bound τ' (d + 1) r (segs ++ [.at (i : Int)]) := by
        unfold Bound; rw [hτ'env]; exact lookupBy_setBy_self _ _ _
      have hsh : ∀ x : SVal, (SVal.array (List.replicate i (defaultForTy (.ref R)))
          (defaultForTy (.ref R) :: (S ++ SH)) false).save [.at (i : Int)] x =
          .ok (.array (List.replicate i (defaultForTy (.ref R))) (x :: (S ++ SH)) false) := by
        intro x
        have := save_at_shadow (List.replicate i (defaultForTy (.ref R))) (S ++ SH)
          (defaultForTy (.ref R)) x false
        simpa using this
      obtain ⟨σ₂, hrun₂, hW₂, hK₂⟩ := child_step (d := d) (hIH w (List.mem_cons_self ..)) hc.1 ht.1
        hE (resolve_alias hBτ) (show Wrote st₀ τ'.storage r segs _ by rw [hτ'st]; exact hWτ)
        (hsh _) (hsh w)
      refine ⟨σ₂, ?_, by simpa using hW₂, ?_⟩
      · simp only [List.cons_append, List.nil_append, Prog.run_cons, run_decl hq, bind,
          Except.bind, hτ']
        exact hrun₂
      · refine hK₁.trans (Keep.trans ?_ hK₂)
        intro j hj
        rw [hτ'env, lookupBy_setBy_ne (fun h => by have := slot_inj h; omega)]

theorem fillEntries_run {d : Nat} {k : PrimTy} {V : Ty} (hk : k.isNumeric = true) {r : Name}
    {segs : List Seg} (hV : V.defaultOkS = true) :
    ∀ (todo done : List (Int × SVal)) (σ : State) (st₀ : List (Name × SVal)),
      (∀ kw ∈ todo, FillOK C kw.2) → canonEntries V todo → tightEntries V todo →
      nodupKeysB (done ++ todo) = true → Bound σ d r segs →
      Wrote st₀ σ.storage r segs (.map done (defaultForTy V)) →
      ∃ σ', Prog.run σ (fillEntries (C := C) d k V hk todo) = .ok σ' ∧
        Wrote st₀ σ'.storage r segs (.map (done ++ todo) (defaultForTy V)) ∧ Keep (d + 1) σ σ'
  | [], done, σ, st₀, _, _, _, _, _, hW => ⟨σ, rfl, by simpa using hW, Keep.refl _ _⟩
  | (key, w) :: todo, done, σ, st₀, hIH, hc, ht, hnd, hB, hW => by
    have hkey : lookupBy key done = none := nodupKeysB_mid hnd
    have hq := resolve_index_map (C := C) (V := V) (key := key) hk hB hW.findStorage
    -- `delete balances[key];` creates the entry at the default
    have hcur : σ.findStorage r (segs ++ [.at key]) = .ok (defaultForTy V) := by
      rw [State.findStorage_append, hW.findStorage]
      simp only [bind, Except.bind, SVal.find, hkey, SVal.find_nil]
    have hdel := run_delete (C := C) (l := Loc.index .map (.alias (slot d)) (.simple (.lit key hk)))
      (by simpa only [SPath.resolve] using hq) hcur
    rw [defaultOf_default] at hdel
    have hmid : ∀ x y : SVal, setBy key y (done ++ [(key, x)]) = done ++ [(key, y)] :=
      fun x y => setBy_mid hkey
    have hN₁ : (SVal.map done (defaultForTy V)).save [.at key] (defaultForTy V) =
        .ok (.map (done ++ [(key, defaultForTy V)]) (defaultForTy V)) := by
      rw [save_at_map, show done = done ++ [] from (List.append_nil _).symm,
        setBy_append_left_none hkey]
      simp [setBy]
    obtain ⟨τ, hτ, hWτ, henv⟩ := hW.saveStorage (.map (done ++ [(key, defaultForTy V)]) (defaultForTy V))
    have hdel' : Stmt.run σ (.delete (C := C)
        (Loc.index .map (.alias (slot d)) (.simple (.lit key hk)) : Loc C V)) = .ok τ := by
      rw [hdel, State.saveStorage_append hW.findStorage, hN₁]; exact hτ
    have hBτ : Bound τ d r segs := by unfold Bound; rw [henv]; exact hB
    have hqτ := resolve_index_map (C := C) (V := V) (key := key) hk hBτ hWτ.findStorage
    obtain ⟨σ₂, hrun₂, hW₂, hK₂⟩ := child_step (d := d) (hIH (key, w) (List.mem_cons_self ..)) hc.1
      ht.1 hV hqτ hWτ (by rw [save_at_map, hmid]) (by rw [save_at_map, hmid])
    obtain ⟨σ₃, hrun₃, hW₃, hK₃⟩ := fillEntries_run hk hV todo (done ++ [(key, w)]) σ₂ st₀
      (fun kw hm => hIH kw (List.mem_cons_of_mem _ hm)) hc.2 ht.2 (by simpa using hnd)
      (hK₂.bound (Nat.lt_succ_self d) hBτ) hW₂
    refine ⟨σ₃, ?_, by simpa using hW₃, ?_⟩
    · simp only [fillEntries, Prog.run_cons, hdel', bind, Except.bind]
      rw [Prog.run_append, hrun₂]; exact hrun₃
    · exact (Keep.of_env henv).trans (hK₂.trans hK₃)

theorem sizeOf_lt_fields {fields : List (Name × SVal)} {nw : Name × SVal} (h : nw ∈ fields) :
    sizeOf nw.2 < sizeOf (SVal.struct fields) := by
  have := List.sizeOf_lt_of_mem h
  obtain ⟨n, w⟩ := nw
  simp at this ⊢; omega

theorem sizeOf_lt_elems {elems shadow : List SVal} {fx : Bool} {w : SVal} (h : w ∈ elems) :
    sizeOf w < sizeOf (SVal.array elems shadow fx) := by
  have := List.sizeOf_lt_of_mem h
  simp; omega

theorem sizeOf_lt_shadow {elems shadow : List SVal} {fx : Bool} {w : SVal} (h : w ∈ shadow) :
    sizeOf w < sizeOf (SVal.array elems shadow fx) := by
  have := List.sizeOf_lt_of_mem h
  simp; omega

theorem sizeOf_lt_entries {entries : List (Int × SVal)} {dflt : SVal} {kw : Int × SVal}
    (h : kw ∈ entries) : sizeOf kw.2 < sizeOf (SVal.map entries dflt) := by
  have := List.sizeOf_lt_of_mem h
  obtain ⟨k, w⟩ := kw
  simp at this ⊢; omega

/-- **The builder writes what it is given**: from the default at a typed
path, `fill` leaves any canonical, tight value there. -/
theorem fill_ok : ∀ v : SVal, FillOK C v
  | .prim pv => by
    intro T d q σ r segs hc ht hok hq h0
    cases T with
    | ref R => cases pv <;> cases R <;> simp [SVal.canon] at hc
    | prim p =>
      cases q with
      | loc l =>
        have hl : l.resolve σ = .ok (r, segs) := by simpa only [SPath.resolve] using hq
        obtain ⟨τ, hτ, hWτ, henv⟩ := h0.saveStorage (.prim pv)
        refine ⟨τ, ?_, hWτ, Keep.of_env henv⟩
        show Prog.run σ (primProg p l (.prim pv)) = _
        rw [run_primProg hl hc, hτ]
  | .struct fields => by
    intro T d q σ r segs hc ht hok hq h0
    cases T with
    | prim p => simp [SVal.canon] at hc
    | ref R =>
      cases R with
      | struct s =>
        obtain ⟨hnames, hcf⟩ := hc
        have hs : s ∈ defaultOkStructs := by simpa [Ty.defaultOkS] using hok
        obtain ⟨hnd, hmok⟩ := struct_ok hs
        have hB : Bound (σ.setEnv (slot d) (.spath r segs)) d r segs := lookupBy_setBy_self ..
        obtain ⟨σ', hrun, hW, hK⟩ := fillFields_run (C := C) (d := d) (s := s) fields []
          (structDef s) (σ.setEnv (slot d) (.spath r segs)) σ.storage
          (fun nw _ => fill_ok nw.2) hcf ht hnames
          (fun nt hm => ⟨lookupBy_eq_of_nodup hnd hm, hmok nt hm, rfl⟩) hnd hB
          (by rw [defaultForTy] at h0; simpa using h0)
        refine ⟨σ', ?_, by simpa using hW, (Keep.setEnv d σ _).trans (hK.mono (Nat.le_succ d))⟩
        simp only [fill, Prog.run_cons, run_decl hq, bind, Except.bind]; exact hrun
      | array _ => simp [SVal.canon] at hc
      | fixed _ _ => simp [SVal.canon] at hc
      | mapping _ _ => simp [SVal.canon] at hc
  | .array elems shadow fx => by
    intro T d q σ r segs hc ht hok hq h0
    cases T with
    | prim p => simp [SVal.canon] at hc
    | ref R =>
      cases R with
      | struct _ => simp [SVal.canon] at hc
      | mapping _ _ => simp [SVal.canon] at hc
      | array E =>
        obtain ⟨hfx, hce, hcs⟩ := hc
        subst hfx
        obtain ⟨hne, hpr, hte, hts⟩ := ht
        have hB : Bound (σ.setEnv (slot d) (.spath r segs)) d r segs := lookupBy_setBy_self ..
        have h0' : Wrote σ.storage (σ.setEnv (slot d) (.spath r segs)).storage r segs
            (.array [] [] false) := by rw [defaultForTy] at h0; exact h0
        by_cases hE : E.defaultOkS = true
        · obtain ⟨σ₂, hrun₂, hW₂, henv₂⟩ := pushes_run (C := C) (E := E) (d := d)
            (by simp [hE]) (elems.length + shadow.length) [] _ σ.storage hB h0'
          have hB₂ : Bound σ₂ d r segs := by unfold Bound; rw [henv₂]; exact hB
          obtain ⟨σ₃, hrun₃, hW₃, hK₃⟩ := fillShadow_run (C := C) hE shadow [] elems.length σ₂
            σ.storage (fun w _ => fill_ok w) hcs hts hpr hB₂ (by simpa using hW₂)
          obtain ⟨σ₄, hrun₄, hW₄, hK₄⟩ := fillElems_run (C := C) (ArrTy.dyn (E := E)) hE elems []
            shadow false σ₃ σ.storage (fun w _ => fill_ok w) hce hte
            (hK₃.bound (Nat.lt_succ_self d) hB₂) (by simpa using hW₃)
          refine ⟨σ₄, ?_, by simpa using hW₄, ?_⟩
          · simp only [fill, dif_pos hE, Prog.run_cons, run_decl hq, bind, Except.bind]
            rw [Prog.run_append, Prog.run_append, hrun₂]
            simp only [bind, Except.bind]
            rw [hrun₃]
            exact hrun₄
          · exact ((Keep.setEnv d σ _).trans (Keep.of_env henv₂)).trans
              ((hK₃.trans hK₄).mono (Nat.le_succ d))
        · obtain ⟨rfl, rfl⟩ := hne (by simpa using hE)
          refine ⟨σ.setEnv (slot d) (.spath r segs), ?_, h0', Keep.setEnv d σ _⟩
          simp only [fill, dif_neg hE, Prog.run_cons, run_decl hq, bind, Except.bind]; rfl
      | fixed E n =>
        obtain ⟨hfx, hlen, hce, -⟩ := hc
        subst hfx; subst hlen
        obtain ⟨hsh, hte⟩ := ht
        subst hsh
        have hE : E.defaultOkS = true := by simpa [Ty.defaultOkS] using hok
        have hB : Bound (σ.setEnv (slot d) (.spath r segs)) d r segs := lookupBy_setBy_self ..
        obtain ⟨σ', hrun, hW, hK⟩ := fillElems_run (C := C) (ArrTy.fixed (E := E) (n := elems.length))
          hE elems [] [] true (σ.setEnv (slot d) (.spath r segs)) σ.storage (fun w _ => fill_ok w)
          hce hte hB (by rw [defaultForTy] at h0; simpa using h0)
        refine ⟨σ', ?_, by simpa using hW, (Keep.setEnv d σ _).trans (hK.mono (Nat.le_succ d))⟩
        simp only [fill, Prog.run_cons, run_decl hq, bind, Except.bind]; exact hrun
  | .map entries dflt => by
    intro T d q σ r segs hc ht hok hq h0
    cases T with
    | prim p => simp [SVal.canon] at hc
    | ref R =>
      cases R with
      | struct _ => simp [SVal.canon] at hc
      | array _ => simp [SVal.canon] at hc
      | fixed _ _ => simp [SVal.canon] at hc
      | mapping K V =>
        obtain ⟨hnd, hce, hd, -⟩ := hc
        subst hd
        obtain ⟨hkey, hte⟩ := ht
        have hV : V.defaultOkS = true := by simpa [Ty.defaultOkS] using hok
        have hB : Bound (σ.setEnv (slot d) (.spath r segs)) d r segs := lookupBy_setBy_self ..
        have h0' : Wrote σ.storage (σ.setEnv (slot d) (.spath r segs)).storage r segs
            (.map [] (defaultForTy V)) := by rw [defaultForTy] at h0; exact h0
        cases K with
        | ref R' =>
          obtain rfl := hkey rfl
          exact ⟨σ, rfl, h0', Keep.refl _ _⟩
        | prim k =>
          by_cases hk : k.isNumeric = true
          · obtain ⟨σ', hrun, hW, hK⟩ := fillEntries_run (C := C) (d := d) hk hV entries []
              (σ.setEnv (slot d) (.spath r segs)) σ.storage (fun kw _ => fill_ok kw.2) hce hte
              (by simpa using hnd) hB h0'
            refine ⟨σ', ?_, by simpa using hW,
              (Keep.setEnv d σ _).trans (hK.mono (Nat.le_succ d))⟩
            simp only [fill, dif_pos hk, Prog.run_cons, run_decl hq, bind, Except.bind]; exact hrun
          · obtain rfl := hkey (by simpa [Ty.numericKey] using hk)
            refine ⟨σ.setEnv (slot d) (.spath r segs), ?_, h0', Keep.setEnv d σ _⟩
            simp only [fill, dif_neg hk, Prog.run_cons, run_decl hq, bind, Except.bind]; rfl
termination_by v => sizeOf v
decreasing_by
  all_goals first
    | exact sizeOf_lt_fields (by assumption)
    | exact sizeOf_lt_elems (by assumption)
    | exact sizeOf_lt_shadow (by assumption)
    | exact sizeOf_lt_entries (by assumption)

/-! ## The builder's locals check -/

/-- The context keeps the aliases above depth `d`. -/
def KeepΓ (d : Nat) (Γ Γ' : Ctx) : Prop :=
  ∀ j < d, lookupBy (slot j) Γ' = lookupBy (slot j) Γ

theorem KeepΓ.refl (d : Nat) (Γ : Ctx) : KeepΓ d Γ Γ := fun _ _ => rfl

theorem KeepΓ.trans {d : Nat} {Γ₁ Γ₂ Γ₃ : Ctx} (h₁ : KeepΓ d Γ₁ Γ₂) (h₂ : KeepΓ d Γ₂ Γ₃) :
    KeepΓ d Γ₁ Γ₃ := fun j hj => (h₂ j hj).trans (h₁ j hj)

theorem KeepΓ.mono {d e : Nat} {Γ Γ' : Ctx} (h : KeepΓ e Γ Γ') (hde : d ≤ e) : KeepΓ d Γ Γ' :=
  fun j hj => h j (by omega)

theorem KeepΓ.setBy (d : Nat) (Γ : Ctx) (b : BTy) : KeepΓ d Γ (setBy (slot d) b Γ) := by
  intro j hj
  rw [lookupBy_setBy_ne (fun h => by have := slot_inj h; omega)]

theorem KeepΓ.lookup {d e : Nat} {Γ Γ' : Ctx} {b : BTy} (h : KeepΓ e Γ Γ') (hd : d < e)
    (hb : lookupBy (slot d) Γ = some b) : lookupBy (slot d) Γ' = some b := by
  rw [h d hd]; exact hb

theorem Prog.wt_append' (Γ : Ctx) :
    (P Q : Prog C) → Prog.wt Γ (P ++ Q) = (Prog.wt Γ P).bind (fun Γ₁ => Prog.wt Γ₁ Q)
  | [], Q => rfl
  | s :: P, Q => by
    simp only [List.cons_append, Prog.wt]
    cases s.wt Γ with
    | none => rfl
    | some Γ₁ => exact Prog.wt_append' Γ₁ P Q

/-- What `fill` needs of the locals for one value: `q` checks. -/
def WtOK (C : Contract) (v : SVal) : Prop :=
  ∀ (T : Ty) (d : Nat) (q : SPath C T) (Γ : Ctx), q.wt Γ = true →
    ∃ Γ', Prog.wt Γ (fill d T q v) = some Γ' ∧ KeepΓ d Γ Γ'

theorem fillFields_wt {d : Nat} {s : Name} :
    ∀ (fields : List (Name × SVal)) (Γ : Ctx), (∀ nw ∈ fields, WtOK C nw.2) →
      lookupBy (slot d) Γ = some (.path (.ref (.struct s))) →
      ∃ Γ', Prog.wt Γ (fillFields (C := C) d s fields) = some Γ' ∧ KeepΓ (d + 1) Γ Γ'
  | [], Γ, _, _ => ⟨Γ, rfl, KeepΓ.refl _ _⟩
  | (n, w) :: rest, Γ, hIH, hΓ => by
    simp only [fillFields]
    rw [Prog.wt_append']
    split
    · rename_i T h
      obtain ⟨Γ₁, h₁, hK₁⟩ := hIH (n, w) (List.mem_cons_self ..) T (d + 1)
        (.loc (.field (.alias (slot d)) n h)) Γ (by simp [SPath.wt, Loc.wt, hΓ])
      obtain ⟨Γ₂, h₂, hK₂⟩ := fillFields_wt rest Γ₁ (fun nw hm => hIH nw (List.mem_cons_of_mem _ hm))
        (hK₁.lookup (Nat.lt_succ_self d) hΓ)
      exact ⟨Γ₂, by rw [h₁]; exact h₂, hK₁.trans hK₂⟩
    · obtain ⟨Γ₂, h₂, hK₂⟩ := fillFields_wt rest Γ (fun nw hm => hIH nw (List.mem_cons_of_mem _ hm))
        hΓ
      exact ⟨Γ₂, h₂, hK₂⟩

theorem fillElems_wt {R : RefTy} {E : Ty} {d : Nat} (a : ArrTy R E) :
    ∀ (L : List SVal) (j : Nat) (Γ : Ctx), (∀ w ∈ L, WtOK C w) →
      lookupBy (slot d) Γ = some (.path (.ref R)) →
      ∃ Γ', Prog.wt Γ (fillElems (C := C) d a j L) = some Γ' ∧ KeepΓ (d + 1) Γ Γ'
  | [], _, Γ, _, _ => ⟨Γ, rfl, KeepΓ.refl _ _⟩
  | w :: L, j, Γ, hIH, hΓ => by
    simp only [fillElems]
    rw [Prog.wt_append']
    obtain ⟨Γ₁, h₁, hK₁⟩ := hIH w (List.mem_cons_self ..) E (d + 1)
      (.loc (.index (.arr a) (.alias (slot d)) (.simple (.lit (j : Int) rfl)))) Γ
      (by simp [SPath.wt, Loc.wt, Val.wt, Simple.wt, hΓ])
    obtain ⟨Γ₂, h₂, hK₂⟩ := fillElems_wt a L (j + 1) Γ₁
      (fun w hm => hIH w (List.mem_cons_of_mem _ hm)) (hK₁.lookup (Nat.lt_succ_self d) hΓ)
    exact ⟨Γ₂, by rw [h₁]; exact h₂, hK₁.trans hK₂⟩

theorem fillShadow_wt {E : Ty} {d : Nat} :
    ∀ (S : List SVal) (i : Nat) (Γ : Ctx), (∀ w ∈ S, WtOK C w) →
      lookupBy (slot d) Γ = some (.path (.ref (.array E))) →
      ∃ Γ', Prog.wt Γ (fillShadow (C := C) d E i S) = some Γ' ∧ KeepΓ (d + 1) Γ Γ'
  | [], _, Γ, _, _ => ⟨Γ, rfl, KeepΓ.refl _ _⟩
  | w :: S, i, Γ, hIH, hΓ => by
    simp only [fillShadow]
    rw [Prog.wt_append']
    obtain ⟨Γ₁, h₁, hK₁⟩ := fillShadow_wt S (i + 1) Γ
      (fun w hm => hIH w (List.mem_cons_of_mem _ hm)) hΓ
    have hΓ₁ := hK₁.lookup (Nat.lt_succ_self d) hΓ
    rw [h₁]
    cases E with
    | prim p =>
      exact ⟨Γ₁, by simp [Prog.wt, Stmt.wt, SPath.wt, hΓ₁], hK₁⟩
    | ref R =>
      have hΓ₂ : lookupBy (slot d) (setBy (slot (d + 1)) (.path (.ref R)) Γ₁) =
          some (.path (.ref (.array (.ref R)))) := (KeepΓ.setBy (d + 1) Γ₁ _).lookup
            (Nat.lt_succ_self d) hΓ₁
      obtain ⟨Γ₃, h₃, hK₃⟩ := hIH w (List.mem_cons_self ..) (.ref R) (d + 1)
        (.alias (slot (d + 1))) (setBy (slot (d + 1)) (.path (.ref R)) Γ₁)
        (by simp [SPath.wt])
      refine ⟨Γ₃, ?_, hK₁.trans ((KeepΓ.setBy (d + 1) Γ₁ _).trans hK₃)⟩
      simp only [Option.bind, List.cons_append, List.nil_append, Prog.wt, Stmt.wt, ARhs.wt,
        SPath.wt, Loc.wt, Val.wt, Simple.wt, hΓ₁]
      simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
      simp only [hΓ₂, beq_self_eq_true, ↓reduceIte]
      exact h₃

theorem fillEntries_wt {d : Nat} {k : PrimTy} {V : Ty} (hk : k.isNumeric = true) :
    ∀ (todo : List (Int × SVal)) (Γ : Ctx), (∀ kw ∈ todo, WtOK C kw.2) →
      lookupBy (slot d) Γ = some (.path (.ref (.mapping (.prim k) V))) →
      ∃ Γ', Prog.wt Γ (fillEntries (C := C) d k V hk todo) = some Γ' ∧ KeepΓ (d + 1) Γ Γ'
  | [], Γ, _, _ => ⟨Γ, rfl, KeepΓ.refl _ _⟩
  | (key, w) :: todo, Γ, hIH, hΓ => by
    simp only [fillEntries]
    obtain ⟨Γ₁, h₁, hK₁⟩ := hIH (key, w) (List.mem_cons_self ..) V (d + 1)
      (.loc (.index .map (.alias (slot d)) (.simple (.lit key hk)))) Γ
      (by simp [SPath.wt, Loc.wt, Val.wt, Simple.wt, hΓ])
    obtain ⟨Γ₂, h₂, hK₂⟩ := fillEntries_wt hk todo Γ₁
      (fun kw hm => hIH kw (List.mem_cons_of_mem _ hm)) (hK₁.lookup (Nat.lt_succ_self d) hΓ)
    refine ⟨Γ₂, ?_, hK₁.trans hK₂⟩
    simp only [Prog.wt, Stmt.wt, Loc.wt, SPath.wt, Val.wt, Simple.wt, hΓ, beq_self_eq_true,
      Bool.and_self, ↓reduceIte]
    rw [Prog.wt_append', h₁]; exact h₂

theorem primProg_wt {p : PrimTy} {l : Loc C (.prim p)} {Γ : Ctx} (hl : l.wt Γ = true) (v : SVal) :
    Prog.wt Γ (primProg p l v) = some Γ := by
  cases p <;> cases v <;> try rfl
  all_goals rename_i pv; cases pv <;> simp [primProg, Prog.wt, Stmt.wt, Src.wt, Val.wt,
    Simple.wt, hl]

/-- **The builder's locals check**: `fill` checks wherever its path does. -/
theorem fill_wt : ∀ v : SVal, WtOK C v
  | .prim pv => by
    intro T d q Γ hq
    cases T with
    | ref R =>
      cases R with
      | mapping K V => cases K <;> exact ⟨Γ, by clear hq; simp [fill, Prog.wt], KeepΓ.refl _ _⟩
      | _ => exact ⟨Γ, by clear hq; simp [fill, Prog.wt], KeepΓ.refl _ _⟩
    | prim p =>
      cases q with
      | loc l => exact ⟨Γ, primProg_wt hq _, KeepΓ.refl _ _⟩
  | .struct fields => by
    intro T d q Γ hq
    cases T with
    | prim p => cases q; exact ⟨Γ, by clear hq; simp [fill, primProg, Prog.wt], KeepΓ.refl _ _⟩
    | ref R =>
      cases R with
      | struct s =>
        obtain ⟨Γ', h, hK⟩ := fillFields_wt (C := C) (d := d) (s := s) fields
          (setBy (slot d) (.path (.ref (.struct s))) Γ) (fun nw _ => fill_wt nw.2)
          (lookupBy_setBy_self ..)
        refine ⟨Γ', ?_, (KeepΓ.setBy d Γ _).trans (hK.mono (Nat.le_succ d))⟩
        simp only [fill, Prog.wt, Stmt.wt, ARhs.wt, hq, ↓reduceIte]; exact h
      | array _ | fixed _ _ => exact ⟨Γ, by clear hq; simp [fill, Prog.wt], KeepΓ.refl _ _⟩
      | mapping K V => cases K <;> exact ⟨Γ, by clear hq; simp [fill, Prog.wt], KeepΓ.refl _ _⟩
  | .array elems shadow fx => by
    intro T d q Γ hq
    cases T with
    | prim p => cases q; exact ⟨Γ, by clear hq; simp [fill, primProg, Prog.wt], KeepΓ.refl _ _⟩
    | ref R =>
      cases R with
      | struct _ => exact ⟨Γ, by clear hq; simp [fill, Prog.wt], KeepΓ.refl _ _⟩
      | mapping K V => cases K <;> exact ⟨Γ, by clear hq; simp [fill, Prog.wt], KeepΓ.refl _ _⟩
      | array E =>
        have hΓ : lookupBy (slot d) (setBy (slot d) (.path (.ref (.array E))) Γ) =
            some (.path (.ref (.array E))) := lookupBy_setBy_self ..
        by_cases hE : E.defaultOkS = true
        · obtain ⟨Γ₁, h₁, hK₁⟩ := fillShadow_wt (C := C) (E := E) (d := d) shadow elems.length _
            (fun w _ => fill_wt w) hΓ
          obtain ⟨Γ₂, h₂, hK₂⟩ := fillElems_wt (C := C) (d := d) (ArrTy.dyn (E := E)) elems 0 Γ₁
            (fun w _ => fill_wt w) (hK₁.lookup (Nat.lt_succ_self d) hΓ)
          refine ⟨Γ₂, ?_, (KeepΓ.setBy d Γ _).trans ((hK₁.trans hK₂).mono (Nat.le_succ d))⟩
          have hpush : ∀ n, Prog.wt (setBy (slot d) (.path (.ref (.array E))) Γ)
              (List.replicate n (Stmt.push (C := C) (.alias (slot d) : SPath C (.array E)) none
                (by simp [hE]))) = some (setBy (slot d) (.path (.ref (.array E))) Γ) := by
            intro n
            induction n with
            | zero => rfl
            | succ n ih =>
              rw [List.replicate_succ]
              simp only [Prog.wt, Stmt.wt, SPath.wt, hΓ, Option.all]
              simpa using ih
          simp only [fill, dif_pos hE, Prog.wt, Stmt.wt, ARhs.wt, hq, ↓reduceIte]
          rw [Prog.wt_append', Prog.wt_append', hpush]
          simp only [Option.bind, h₁]; exact h₂
        · refine ⟨setBy (slot d) (.path (.ref (.array E))) Γ, ?_, KeepΓ.setBy d Γ _⟩
          simp [fill, dif_neg hE, Prog.wt, Stmt.wt, ARhs.wt, hq]
      | fixed E n =>
        obtain ⟨Γ', h, hK⟩ := fillElems_wt (C := C) (d := d) (ArrTy.fixed (E := E) (n := n)) elems 0
          (setBy (slot d) (.path (.ref (.fixed E n))) Γ) (fun w _ => fill_wt w)
          (lookupBy_setBy_self ..)
        refine ⟨Γ', ?_, (KeepΓ.setBy d Γ _).trans (hK.mono (Nat.le_succ d))⟩
        simp only [fill, Prog.wt, Stmt.wt, ARhs.wt, hq, ↓reduceIte]; exact h
  | .map entries dflt => by
    intro T d q Γ hq
    cases T with
    | prim p => cases q; exact ⟨Γ, by clear hq; simp [fill, primProg, Prog.wt], KeepΓ.refl _ _⟩
    | ref R =>
      cases R with
      | struct _ | array _ | fixed _ _ => exact ⟨Γ, by clear hq; simp [fill, Prog.wt], KeepΓ.refl _ _⟩
      | mapping K V =>
        cases K with
        | ref _ => exact ⟨Γ, by clear hq; simp [fill, Prog.wt], KeepΓ.refl _ _⟩
        | prim k =>
          by_cases hk : k.isNumeric = true
          · obtain ⟨Γ', h, hK⟩ := fillEntries_wt (C := C) (d := d) (V := V) hk entries
              (setBy (slot d) (.path (.ref (.mapping (.prim k) V))) Γ) (fun kw _ => fill_wt kw.2)
              (lookupBy_setBy_self ..)
            refine ⟨Γ', ?_, (KeepΓ.setBy d Γ _).trans (hK.mono (Nat.le_succ d))⟩
            simp only [fill, dif_pos hk, Prog.wt, Stmt.wt, ARhs.wt, hq, ↓reduceIte]; exact h
          · refine ⟨setBy (slot d) (.path (.ref (.mapping (.prim k) V))) Γ, ?_, KeepΓ.setBy d Γ _⟩
            simp [fill, dif_neg hk, Prog.wt, Stmt.wt, ARhs.wt, hq]
termination_by v => sizeOf v
decreasing_by
  all_goals first
    | exact sizeOf_lt_fields (by assumption)
    | exact sizeOf_lt_elems (by assumption)
    | exact sizeOf_lt_shadow (by assumption)
    | exact sizeOf_lt_entries (by assumption)

/-! ## Every root -/

theorem rootsProg_wt : ∀ (st : List (Name × SVal)) (Γ : Ctx),
    ∃ Γ', Prog.wt Γ (rootsProg C st) = some Γ'
  | [], Γ => ⟨Γ, rfl⟩
  | (r, v) :: rest, Γ => by
    simp only [rootsProg]
    rw [Prog.wt_append']
    split
    · rename_i T h
      obtain ⟨Γ₁, h₁, -⟩ := fill_wt v T 0 (.loc (.root r h)) Γ (by simp [SPath.wt, Loc.wt])
      obtain ⟨Γ₂, h₂⟩ := rootsProg_wt rest Γ₁
      exact ⟨Γ₂, by rw [h₁]; exact h₂⟩
    · exact rootsProg_wt rest Γ

theorem rootsProg_run :
    ∀ (todo done cf : List (Name × SVal)) (σ : State),
      σ.storage = done ++ cf → cf.map (·.1) = todo.map (·.1) → nodupKeysB (done ++ todo) = true →
      (∀ rv ∈ cf, ∃ T, lookupBy rv.1 C.vars = some T ∧ rv.2 = defaultForTy T) →
      (∀ rv ∈ todo, ∃ T, lookupBy rv.1 C.vars = some T ∧ rv.2.canon T ∧ rv.2.tight T ∧
        T.defaultOkS = true) →
      ∃ σ', Prog.run σ (rootsProg C todo) = .ok σ' ∧ σ'.storage = done ++ todo
  | [], done, cf, σ, hst, hmap, _, _, _ => by
    cases cf with
    | cons _ _ => simp at hmap
    | nil => exact ⟨σ, rfl, by simpa using hst⟩
  | (r, v) :: todo, done, cf, σ, hst, hmap, hnd, hcf, htodo => by
    cases cf with
    | nil => simp at hmap
    | cons rx cf =>
      obtain ⟨r', x⟩ := rx
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hr, hmap⟩ := hmap
      subst r'
      obtain ⟨T', hT', rfl⟩ := hcf (r, x) (List.mem_cons_self ..)
      obtain ⟨T, hT, hc, ht, hok⟩ := htodo (r, v) (List.mem_cons_self ..)
      dsimp only at hT' hT hc ht hok
      have hTT : T' = T := by rw [hT] at hT'; exact (Option.some.inj hT').symm
      subst T'
      have hdone : lookupBy r done = none := nodupKeysB_mid hnd
      have hlook : lookupBy r σ.storage = some (defaultForTy T) := by rw [hst, lookupBy_mid hdone]
      simp only [rootsProg]
      rw [Prog.run_append]
      split
      · rename_i T₀ h
        have hT₀ : T₀ = T := by
          have h' : lookupBy r C.vars = some T₀ := h
          rw [hT] at h'; exact (Option.some.inj h').symm
        subst T₀
        have h0 : Wrote σ.storage σ.storage r [] (defaultForTy T) := by
          unfold Wrote putSt
          simp only [hlook, SVal.save_nil, bind, Except.bind, pure, Except.pure,
            setBy_of_lookupBy hlook]
        obtain ⟨σ₁, hrun₁, hW₁, -⟩ := fill_ok v T 0 (.loc (.root r h)) σ r [] hc ht hok
          (by simp [SPath.resolve, Loc.resolve]; rfl) h0
        have hst₁ : σ₁.storage = (done ++ [(r, v)]) ++ cf := by
          unfold Wrote putSt at hW₁
          simp only [hlook, SVal.save_nil, bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at hW₁
          rw [← hW₁, hst, setBy_mid hdone]; simp
        obtain ⟨σ₂, hrun₂, hst₂⟩ := rootsProg_run todo (done ++ [(r, v)]) cf σ₁ hst₁ hmap
          (by simpa using hnd) (fun rv hm => hcf rv (List.mem_cons_of_mem _ hm))
          (fun rv hm => htodo rv (List.mem_cons_of_mem _ hm))
        exact ⟨σ₂, by rw [hrun₁]; exact hrun₂, by simpa using hst₂⟩
      · rename_i h
        have h' : lookupBy r C.vars = none := h
        rw [hT] at h'; exact nomatch h'

end Build

open Build

/-- Keys decide `nodupKeysB`. -/
theorem nodupKeysB_of_map_fst_eq {α β : Type} :
    ∀ {l : List (Name × α)} {l' : List (Name × β)}, l.map (·.1) = l'.map (·.1) →
      nodupKeysB l' = true → nodupKeysB l = true
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp at h
  | (a, x) :: l, (b, y) :: l', h, hnd => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hnd ⊢
    refine ⟨?_, nodupKeysB_of_map_fst_eq h hnd.2⟩
    cases hl : lookupBy a l with
    | none => rfl
    | some _ =>
      have := lookupBy_isSome_of_map_fst (k := a) h.symm (by simp [hl])
      rw [hnd.1] at this; exact nomatch this

/-- **Canonical and tight ⇒ reachable, by one program**: `Build.rootsProg`
checks, and run from `C`'s initial state it leaves exactly `st`. -/
theorem storage_tight (hnd : nodupKeysB C.vars = true) (hok : C.vars.all (·.2.defaultOkS) = true)
    {st : List (Name × SVal)} (hc : CanonStorage C st) (ht : TightStorage C st) :
    (∃ Γ', Prog.wt [] (rootsProg C st) = some Γ') ∧
      ∃ σ, Prog.run C.initState (rootsProg C st) = .ok σ ∧ σ.storage = st := by
  refine ⟨rootsProg_wt st [], ?_⟩
  have hstnd : nodupKeysB st = true := nodupKeysB_of_map_fst_eq hc.1 hnd
  have hroots : ∀ rv ∈ st, ∃ T, lookupBy rv.1 C.vars = some T ∧ rv.2.canon T ∧ rv.2.tight T ∧
      T.defaultOkS = true := by
    intro rv hmem
    have hname : rv.1 ∈ C.vars.map (·.1) := by rw [← hc.1]; exact List.mem_map_of_mem hmem
    obtain ⟨g, hg, hg1⟩ := List.mem_map.mp hname
    have hlook : lookupBy rv.1 C.vars = some g.2 := by
      rw [← hg1]; exact lookupBy_eq_of_nodup hnd hg
    have hrv : lookupBy rv.1 st = some rv.2 := lookupBy_eq_of_nodup hstnd hmem
    obtain ⟨v, hv, hcv⟩ := hc.2 rv.1 g.2 hlook
    rw [hrv] at hv; cases hv
    exact ⟨g.2, hlook, hcv, ht rv.1 g.2 rv.2 hlook hrv, List.all_eq_true.mp hok g hg⟩
  have hdefs : ∀ rv ∈ C.initStorage, ∃ T, lookupBy rv.1 C.vars = some T ∧ rv.2 = defaultForTy T := by
    intro rv hmem
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hmem
    exact ⟨g.2, lookupBy_eq_of_nodup hnd hg, rfl⟩
  obtain ⟨σ, hrun, hst⟩ := rootsProg_run st [] C.initStorage C.initState rfl
    (by rw [hc.1]; simp [Contract.initStorage]) (by simpa using hstnd) hdefs hroots
  exact ⟨σ, hrun, by simpa using hst⟩

/-- **Canonical and tight ⇒ reachable.** -/
theorem canon_reachable (hnd : nodupKeysB C.vars = true) (hok : C.vars.all (·.2.defaultOkS) = true)
    {st : List (Name × SVal)} (hc : CanonStorage C st) (ht : TightStorage C st) :
    Reachable C st := by
  obtain ⟨⟨Γ', hwt⟩, σ, hrun, hst⟩ := storage_tight hnd hok hc ht
  exact ⟨rootsProg C st, Γ', σ, hwt, hrun, hst⟩

/-- **Nothing inferable is missing**: a property of storage that holds
initially and that every checked program keeps, from any well-typed
canonical state, holds of every canonical, tight storage. -/
theorem no_hidden_invariant (hnd : nodupKeysB C.vars = true)
    (hok : C.vars.all (·.2.defaultOkS) = true) (P : List (Name × SVal) → Prop)
    (hinit : P C.initStorage)
    (hstep : ∀ (σ σ' : State) (prog : Prog C) (Γ' : Ctx), RunWT C [] [] σ → Canon C [] σ →
      Prog.wt [] prog = some Γ' → Prog.run σ prog = .ok σ' → P σ.storage → P σ'.storage)
    (st : List (Name × SVal)) (hc : CanonStorage C st) (ht : TightStorage C st) : P st := by
  obtain ⟨⟨Γ', hwt⟩, σ, hrun, rfl⟩ := storage_tight hnd hok hc ht
  exact hstep _ _ _ _ (RunWT.init hnd hok rfl rfl) (Canon.init hok rfl) hwt hrun hinit

/-! ## Reachable storages are tight

The converse direction: every storage a checked program reaches is tight,
for a contract whose types have well-formed defaults all the way down
(`Ty.okDeep`: no array of a struct `defaultOkS` refuses, like `BadDup[]`).
Then the first clause of `SVal.tight` is vacuous, no memory object matters,
and what is left is kept by every write: a word is written into a live slot
(`State.checkIndex`, `IdxLive`), a mapping is indexed only at a number
(`KeysOK`: an alias was bound along such a path), and `pop`, `delete`, a
copy, a push leave cleared words and nothing past a fixed-size array's end. -/

section Exact

open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne)

/-- `T`'s default is well-formed all the way down: a struct `defaultOkS`
admits, and arrays and mappings of such. -/
def Ty.okDeep : Ty → Bool
  | .prim _ => true
  | .ref (.struct s) => s ∈ defaultOkStructs
  | .ref (.array E) => E.okDeep
  | .ref (.fixed E _) => E.okDeep
  | .ref (.mapping _ V) => V.okDeep

theorem struct_okDeep {s : Name} (h : s ∈ defaultOkStructs) :
    ∀ nt ∈ structDef s, nt.2.okDeep = true := by
  simp only [defaultOkStructs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [structDef, Ty.okDeep, defaultOkStructs]

theorem okDeep_defaultOkS : ∀ {T : Ty}, T.okDeep = true → T.defaultOkS = true
  | .prim _, _ => rfl
  | .ref (.struct _), h => by simpa [Ty.okDeep, Ty.defaultOkS] using h
  | .ref (.array _), _ => rfl
  | .ref (.fixed E _), h => by
    simp only [Ty.okDeep] at h; simpa [Ty.defaultOkS] using okDeep_defaultOkS (T := E) h
  | .ref (.mapping _ V), h => by
    simp only [Ty.okDeep] at h; simpa [Ty.defaultOkS] using okDeep_defaultOkS (T := V) h

theorem okDeep_segTy {T T' : Ty} {seg : Seg} (h : T.okDeep = true) (hs : segTy T seg = some T') :
    T'.okDeep = true := by
  cases T with
  | prim _ => cases seg <;> simp [segTy] at hs
  | ref R =>
    cases R with
    | struct s =>
      cases seg with
      | field n =>
        simp only [segTy] at hs
        exact struct_okDeep (by simpa [Ty.okDeep] using h) (n, T') (lookupBy_eq_some_mem hs)
      | «at» _ => simp [segTy] at hs
    | array E => cases seg <;> simp [segTy] at hs; subst hs; simpa [Ty.okDeep] using h
    | fixed E _ => cases seg <;> simp [segTy] at hs; subst hs; simpa [Ty.okDeep] using h
    | mapping _ V => cases seg <;> simp [segTy] at hs; subst hs; simpa [Ty.okDeep] using h

theorem okDeep_tyAtSegs : ∀ {segs : List Seg} {T T' : Ty}, T.okDeep = true →
    tyAtSegs T segs = some T' → T'.okDeep = true
  | [], T, T', h, hs => by simp [tyAtSegs] at hs; subst hs; exact h
  | seg :: rest, T, T', h, hs => by
    simp only [tyAtSegs] at hs
    split at hs
    · rename_i Tm hm; exact okDeep_tyAtSegs (okDeep_segTy h hm) hs
    · exact nomatch hs

/-- Every mapping on the way is indexed by a number: an alias bound along
the path, or a path resolved, took its keys from `uint`/`int` values. -/
def KeysOK : Ty → List Seg → Prop
  | _, [] => True
  | T, seg :: rest => (∀ K V, T = .ref (.mapping K V) → K.numericKey = true) ∧
      (match segTy T seg with
       | some T' => KeysOK T' rest
       | none => True)

theorem KeysOK_append : ∀ {segs : List Seg} {T T₁ : Ty} (seg : Seg),
    KeysOK T segs → tyAtSegs T segs = some T₁ →
    (∀ K V, T₁ = .ref (.mapping K V) → K.numericKey = true) → KeysOK T (segs ++ [seg])
  | [], T, T₁, seg, _, hs, hk => by
    simp only [tyAtSegs, Option.some.injEq] at hs; subst hs
    refine ⟨hk, ?_⟩
    split <;> trivial
  | s :: rest, T, T₁, seg, hk₀, hs, hk => by
    simp only [tyAtSegs] at hs
    obtain ⟨hk₁, hk₂⟩ := hk₀
    refine ⟨hk₁, ?_⟩
    split at hs
    · rename_i Tm hm
      simp only [hm] at hk₂ ⊢
      exact KeysOK_append seg hk₂ hs hk
    · exact nomatch hs

/-- A word written through an index is written into a live slot: the index
was checked against the length where the path was taken. -/
def IdxLive (v : SVal) (segs : List Seg) : Prop :=
  ∀ pre i, segs = pre ++ [.at i] → ∀ es sh fx, v.find pre = .ok (.array es sh fx) →
    0 ≤ i ∧ i.toNat < es.length

/-! ### Tight lists -/

theorem tightElems_iff {E : Ty} : ∀ {l : List SVal}, tightElems E l ↔ ∀ v ∈ l, v.tight E
  | [] => by simp [tightElems]
  | v :: rest => by simp [tightElems, tightElems_iff (l := rest)]

theorem tightEntries_iff {V : Ty} :
    ∀ {l : List (Int × SVal)}, tightEntries V l ↔ ∀ kv ∈ l, kv.2.tight V
  | [] => by simp [tightEntries]
  | (k, v) :: rest => by simp [tightEntries, tightEntries_iff (l := rest)]

theorem tightFields_lookup {s : Name} {fields : List (Name × SVal)} {n : Name} {v : SVal}
    {T : Ty} (h : tightFields s fields) (hl : lookupBy n fields = some v)
    (hT : lookupBy n (structDef s) = some T) : v.tight T := by
  induction fields with
  | nil => simp [lookupBy] at hl
  | cons p rest ih =>
    obtain ⟨n', v'⟩ := p
    simp only [tightFields] at h
    by_cases hn : n = n'
    · subst hn
      simp [lookupBy] at hl; subst hl
      simpa [hT] using h.1
    · simp [lookupBy, hn] at hl
      exact ih h.2 hl

theorem tightFields_setBy {s : Name} {fields : List (Name × SVal)} {n : Name} {w : SVal} {T : Ty}
    (h : tightFields s fields) (hd : lookupBy n (structDef s) = some T) (hw : w.tight T) :
    tightFields s (setBy n w fields) := by
  induction fields with
  | nil => simp [setBy, tightFields, hd, hw]
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [tightFields] at h
    by_cases hn : n = k
    · subst hn; simp [setBy, tightFields, hd, hw, h.2]
    · simp only [setBy, if_neg hn, tightFields]; exact ⟨h.1, ih h.2⟩

theorem tightEntries_setBy {V : Ty} {entries : List (Int × SVal)} {i : Int} {w : SVal}
    (h : tightEntries V entries) (hw : w.tight V) : tightEntries V (setBy i w entries) := by
  induction entries with
  | nil => simp [setBy, tightEntries, hw]
  | cons p rest ih =>
    obtain ⟨j, v⟩ := p
    by_cases hi : i = j
    · subst hi; simp [setBy, tightEntries, hw, h.2]
    · simp only [setBy, if_neg hi, tightEntries]; exact ⟨h.1, ih h.2⟩

theorem tightEntries_lookup {V : Ty} {entries : List (Int × SVal)} {i : Int} {v : SVal}
    (h : tightEntries V entries) (hl : lookupBy i entries = some v) : v.tight V :=
  tightEntries_iff.mp h (i, v) (lookupBy_eq_some_mem hl)

theorem mem_set_or {l : List SVal} {i : Nat} {u v : SVal} (h : v ∈ l.set i u) : v ∈ l ∨ v = u := by
  rcases List.mem_or_eq_of_mem_set h with h | h
  · exact Or.inl h
  · exact Or.inr h

/-! ### Defaults, reads, writes -/

/-- A fresh default is tight. -/
theorem defaultForTy_tight : ∀ {T : Ty}, T.defaultOkS = true → (defaultForTy T).tight T := by
  intro T
  induction T using defaultForTy.induct
    (motive2 := fun l => ∀ (s : Name), (∀ nt ∈ l, lookupBy nt.1 (structDef s) = some nt.2 ∧
      nt.2.defaultOkS = true) → tightFields s (defaultForFields l)) with
  | case1 => intro _; simp [defaultForTy, SVal.tight]
  | case2 => intro _; simp [defaultForTy, SVal.tight]
  | case3 => intro _; simp [defaultForTy, SVal.tight]
  | case4 name ih =>
    intro h
    have hs : name ∈ defaultOkStructs := by simpa [Ty.defaultOkS] using h
    obtain ⟨hnd, hok⟩ := struct_ok hs
    rw [defaultForTy]
    exact ih name fun nt hm => ⟨lookupBy_eq_of_nodup hnd hm, hok nt hm⟩
  | case5 elem => intro _; simp [defaultForTy, SVal.tight, tightElems]
  | case6 elem n ih =>
    intro h
    have hE : elem.defaultOkS = true := by simpa [Ty.defaultOkS] using h
    rw [defaultForTy]
    refine ⟨rfl, tightElems_iff.mpr fun v hv => ?_⟩
    rw [List.eq_of_mem_replicate hv]; exact ih hE
  | case7 key value ih =>
    intro _
    rw [defaultForTy]
    exact ⟨fun _ => rfl, trivial⟩
  | case8 => simp [defaultForFields, tightFields]
  | case9 n t rest iht ihrest =>
    rename_i s h
    obtain ⟨hl, hok⟩ := h (n, t) (List.mem_cons_self ..)
    simp only [defaultForFields, tightFields, hl]
    exact ⟨iht hok, ihrest s fun nt hm => h nt (List.mem_cons_of_mem _ hm)⟩

/-- What `find` reaches in a tight value is tight. -/
theorem find_tight : ∀ {segs : List Seg} {v : SVal} {T T' : Ty} {w : SVal},
    v.canon T → v.tight T → T.okDeep = true → tyAtSegs T segs = some T' → v.find segs = .ok w →
      w.tight T'
  | [], v, T, T', w, _, ht, _, hs, hf => by
    simp only [tyAtSegs, Option.some.injEq] at hs
    subst hs
    rw [SVal.find_nil] at hf; cases hf; exact ht
  | seg :: rest, v, T, T', w, h, ht, hok, hs, hf => by
    simp only [tyAtSegs] at hs
    cases hseg : segTy T seg with
    | none => rw [hseg] at hs; exact nomatch hs
    | some Tm =>
      rw [hseg] at hs
      have hokm := okDeep_segTy hok hseg
      cases seg with
      | field n =>
        cases T with
        | prim _ => simp [segTy] at hseg
        | ref r =>
          cases r with
          | struct s =>
            obtain ⟨fields, rfl, -, hfs⟩ := canon_struct h
            simp only [segTy] at hseg
            simp only [SVal.find] at hf
            split at hf
            · rename_i v' hl
              obtain ⟨Tf, hd, hv⟩ := canonFields_lookup hfs hl
              rw [hseg] at hd; cases hd
              exact find_tight hv (tightFields_lookup ht hl hseg) hokm hs hf
            · exact nomatch hf
          | array _ => simp [segTy] at hseg
          | fixed _ _ => simp [segTy] at hseg
          | mapping _ _ => simp [segTy] at hseg
      | «at» i =>
        cases T with
        | prim _ => simp [segTy] at hseg
        | ref r =>
          cases r with
          | struct _ => simp [segTy] at hseg
          | array E =>
            obtain ⟨elems, sh, rfl, he, hsh⟩ := canon_array h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            obtain ⟨-, -, hte, hts⟩ := ht
            simp only [SVal.find] at hf
            split at hf
            · have hm := List.get_mem (elems ++ sh) ⟨i.toNat, by omega⟩
              refine find_tight (canonElems_mem (canonElems_append he hsh) hm) ?_ hokm hs hf
              rcases List.mem_append.mp hm with hm | hm
              · exact tightElems_iff.mp hte _ hm
              · exact tightElems_iff.mp hts _ hm
            · exact nomatch hf
          | fixed E _ =>
            obtain ⟨elems, sh, rfl, -, he, hsh⟩ := canon_fixed h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            obtain ⟨rfl, hte⟩ := ht
            simp only [SVal.find] at hf
            split at hf
            · have hm := List.get_mem (elems ++ []) ⟨i.toNat, by omega⟩
              refine find_tight (canonElems_mem (canonElems_append he hsh) hm) ?_ hokm hs hf
              exact tightElems_iff.mp hte _ (by simp)
            · exact nomatch hf
          | mapping K V =>
            obtain ⟨es, d, rfl, -, hes, hdd, hd⟩ := canon_map h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            obtain ⟨-, htes⟩ := ht
            simp only [SVal.find] at hf
            split at hf
            · rename_i v' hl
              exact find_tight (canonEntries_lookup hes hl) (tightEntries_lookup htes hl) hokm hs hf
            · subst hdd
              exact find_tight hd (defaultForTy_tight (okDeep_defaultOkS hokm)) hokm hs hf

theorem IdxLive.child {v c : SVal} {seg : Seg} {rest : List Seg} (h : IdxLive v (seg :: rest))
    (hc : v.find [seg] = .ok c) : IdxLive c rest := by
  intro pre i hrest es sh fx hf
  refine h (seg :: pre) i (by simp [hrest]) es sh fx ?_
  have := SVal.find_append v [seg] pre
  simp only [List.singleton_append] at this
  rw [this, hc]; exact hf

/-- A word at a primitive type has no path below it. -/
theorem save_prim_cons {v : SVal} {p : PrimTy} (hc : v.canon (.prim p)) (seg : Seg)
    (rest : List Seg) (new : SVal) : ∃ e, v.save (seg :: rest) new = .error e := by
  cases v with
  | prim _ => cases seg <;> exact ⟨_, rfl⟩
  | struct _ => cases p <;> simp [SVal.canon] at hc
  | array _ _ _ => cases p <;> simp [SVal.canon] at hc
  | map _ _ => cases p <;> simp [SVal.canon] at hc

/-- Saving a tight value at a path whose mappings are indexed by numbers,
into a live slot when it is a word, keeps the tree tight. -/
theorem save_tight : ∀ {segs : List Seg} {v : SVal} {T T' : Ty} {new w : SVal},
    v.canon T → v.tight T → T.okDeep = true → tyAtSegs T segs = some T' → KeysOK T segs →
    (T'.isPrimitive = true → IdxLive v segs) → new.tight T' → v.save segs new = .ok w →
      w.tight T
  | [], v, T, T', new, w, _, _, _, hs, _, _, hn, hf => by
    simp only [tyAtSegs, Option.some.injEq] at hs
    subst hs
    rw [SVal.save_nil] at hf; cases hf; exact hn
  | seg :: rest, v, T, T', new, w, h, ht, hok, hs, hk, hlive, hn, hf => by
    simp only [tyAtSegs] at hs
    obtain ⟨hk₁, hk₂⟩ := hk
    cases hseg : segTy T seg with
    | none => rw [hseg] at hs; exact nomatch hs
    | some Tm =>
      rw [hseg] at hs
      simp only [hseg] at hk₂
      have hokm := okDeep_segTy hok hseg
      cases seg with
      | field n =>
        cases T with
        | prim _ => simp [segTy] at hseg
        | ref r =>
          cases r with
          | struct s =>
            obtain ⟨fields, rfl, -, hfs⟩ := canon_struct h
            simp only [segTy] at hseg
            simp only [SVal.save] at hf
            split at hf
            · rename_i old hl
              obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              obtain ⟨Tf, hd, hv⟩ := canonFields_lookup hfs hl
              rw [hseg] at hd; cases hd
              have hchild : (SVal.struct fields).find [.field n] = .ok old := by
                simp [SVal.find, hl, SVal.find_nil]
              exact tightFields_setBy ht hseg (save_tight hv (tightFields_lookup ht hl hseg) hokm
                hs hk₂ (fun hp => (hlive hp).child hchild) hn hup)
            · exact nomatch hf
          | array _ => simp [segTy] at hseg
          | fixed _ _ => simp [segTy] at hseg
          | mapping _ _ => simp [segTy] at hseg
      | «at» i =>
        cases T with
        | prim _ => simp [segTy] at hseg
        | ref r =>
          cases r with
          | struct _ => simp [segTy] at hseg
          | array E =>
            obtain ⟨elems, sh, rfl, he, hsh⟩ := canon_array h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            obtain ⟨-, hpr, hte, hts⟩ := ht
            simp only [SVal.save] at hf
            split at hf
            · rename_i hb
              obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              have hm := List.get_mem (elems ++ sh) ⟨i.toNat, hb.2⟩
              have hct : ((elems ++ sh).get ⟨i.toNat, hb.2⟩).tight E := by
                rcases List.mem_append.mp hm with hm | hm
                · exact tightElems_iff.mp hte _ hm
                · exact tightElems_iff.mp hts _ hm
              have hcc := canonElems_mem (canonElems_append he hsh) hm
              have hchild : (SVal.array elems sh false).find [.at i] =
                  .ok ((elems ++ sh).get ⟨i.toNat, hb.2⟩) := by
                simp only [SVal.find, dif_pos hb, SVal.find_nil]
              have hupt := save_tight hcc hct hokm hs hk₂ (fun hp => (hlive hp).child hchild) hn hup
              have hall : ∀ x ∈ (elems ++ sh).set i.toNat up, x.tight E := by
                intro x hx
                rcases mem_set_or hx with hx | rfl
                · rcases List.mem_append.mp hx with hx | hx
                  · exact tightElems_iff.mp hte _ hx
                  · exact tightElems_iff.mp hts _ hx
                · exact hupt
              refine ⟨fun hf => absurd hf (by simp [okDeep_defaultOkS hokm]), ?_,
                tightElems_iff.mpr fun x hx => hall x (List.mem_of_mem_take hx),
                tightElems_iff.mpr fun x hx => hall x (List.mem_of_mem_drop hx)⟩
              intro hp
              cases rest with
              | cons s' r' =>
                obtain ⟨p, rfl⟩ : ∃ p, E = .prim p := by
                  cases E with
                  | prim p => exact ⟨p, rfl⟩
                  | ref _ => simp [Ty.isPrimitive] at hp
                obtain ⟨e, he'⟩ := save_prim_cons hcc s' r' new
                rw [he'] at hup; exact nomatch hup
              | nil =>
                simp only [tyAtSegs, Option.some.injEq] at hs
                subst hs
                have hl := hlive hp [] i rfl elems sh false (SVal.find_nil _)
                have hdrop : ((elems ++ sh).set i.toNat up).drop elems.length = sh := by
                  rw [List.set_append_left _ _ hl.2, List.drop_left' (by simp)]
                rw [hdrop]
                exact hpr hp
            · exact nomatch hf
          | fixed E n =>
            obtain ⟨elems, sh, rfl, hlen, he, hsh⟩ := canon_fixed h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            obtain ⟨rfl, hte⟩ := ht
            simp only [SVal.save] at hf
            split at hf
            · rename_i hb
              obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              have hm := List.get_mem (elems ++ []) ⟨i.toNat, hb.2⟩
              have hmm : (elems ++ []).get ⟨i.toNat, hb.2⟩ ∈ elems := by simp
              have hcc := canonElems_mem (canonElems_append he hsh) hm
              have hchild : (SVal.array elems [] true).find [.at i] =
                  .ok ((elems ++ []).get ⟨i.toNat, hb.2⟩) := by
                simp only [SVal.find, dif_pos hb, SVal.find_nil]
              have hupt := save_tight hcc (tightElems_iff.mp hte _ hmm) hokm hs hk₂
                (fun hp => (hlive hp).child hchild) hn hup
              refine ⟨?_, tightElems_iff.mpr fun x hx => ?_⟩
              · simp
              · have hx' := List.mem_of_mem_take hx
                rcases mem_set_or hx' with hx' | rfl
                · exact tightElems_iff.mp hte _ (by simpa using hx')
                · exact hupt
            · exact nomatch hf
          | mapping K V =>
            obtain ⟨es, d, rfl, -, hes, hdd, hd⟩ := canon_map h
            simp only [segTy, Option.some.injEq] at hseg
            subst hseg
            obtain ⟨-, htes⟩ := ht
            have hkey : K.numericKey = true := hk₁ K V rfl
            simp only [SVal.save] at hf
            split at hf
            · rename_i old hl
              obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              have hchild : (SVal.map es d).find [.at i] = .ok old := by
                simp [SVal.find, hl, SVal.find_nil]
              exact ⟨fun h => absurd h (by simp [hkey]), tightEntries_setBy htes
                (save_tight (canonEntries_lookup hes hl) (tightEntries_lookup htes hl) hokm hs hk₂
                  (fun hp => (hlive hp).child hchild) hn hup)⟩
            · rename_i hl
              obtain ⟨up, hup, hf⟩ := bind_ok_inv hf
              cases hf
              have hchild : (SVal.map es d).find [.at i] = .ok d := by
                simp [SVal.find, hl, SVal.find_nil]
              subst hdd
              exact ⟨fun h => absurd h (by simp [hkey]), tightEntries_setBy htes
                (save_tight hd (defaultForTy_tight (okDeep_defaultOkS hokm)) hokm hs hk₂
                  (fun hp => (hlive hp).child hchild) hn hup)⟩

/-! ### `delete`, copies, pushes -/

theorem defaultOf_prim {v : SVal} {p : PrimTy} (h : v.canon (.prim p)) :
    v.defaultOf = defaultForTy (.prim p) := by
  cases v with
  | prim pv => cases p <;> cases pv <;> simp_all [SVal.canon, SVal.defaultOf, defaultForTy]
  | struct _ => cases p <;> simp [SVal.canon] at h
  | array _ _ _ => cases p <;> simp [SVal.canon] at h
  | map _ _ => cases p <;> simp [SVal.canon] at h

theorem defaultOfElems_prim {p : PrimTy} : ∀ {elems : List SVal}, canonElems (.prim p) elems →
    ∀ w ∈ SVal.defaultOf.defaultOfElems elems, w = defaultForTy (.prim p)
  | [], _, w, hw => by simp [SVal.defaultOf.defaultOfElems] at hw
  | v :: rest, h, w, hw => by
    simp only [SVal.defaultOf.defaultOfElems, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact defaultOf_prim h.1
    · exact defaultOfElems_prim h.2 w hw

theorem member_okDeep {s n : Name} {T : Ty} (hs : (Ty.ref (.struct s)).okDeep = true)
    (h : lookupBy n (structDef s) = some T) : T.okDeep = true :=
  struct_okDeep (by simpa [Ty.okDeep] using hs) (n, T) (lookupBy_eq_some_mem h)

mutual

/-- `delete` keeps a value tight: words cleared, arrays emptied into their
cleared slots, mappings untouched. -/
theorem SVal.defaultOf_tight : ∀ {v : SVal} {T : Ty}, v.canon T → v.tight T → T.okDeep = true →
    v.defaultOf.tight T
  | .prim pv, .prim _, _, _, _ => by cases pv <;> trivial
  | .struct fields, .ref (.struct s), hc, ht, hok =>
    SVal.defaultOfFields_tight hc.2 ht (fun hl => member_okDeep hok hl)
  | .array elems sh false, .ref (.array E), hc, ht, hok => by
    have hE : E.okDeep = true := by simpa [Ty.okDeep] using hok
    refine ⟨fun hf => absurd hf (by simp [okDeep_defaultOkS hE]), fun hp w hw => ?_, trivial,
      tightElems_iff.mpr fun w hw => ?_⟩
    · rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨p, rfl⟩ : ∃ p, E = .prim p := by
          cases E with
          | prim p => exact ⟨p, rfl⟩
          | ref _ => simp [Ty.isPrimitive] at hp
        exact defaultOfElems_prim hc.2.1 w hw
      · exact ht.2.1 hp w hw
    · rcases List.mem_append.mp hw with hw | hw
      · exact tightElems_iff.mp (SVal.defaultOfElems_tight hc.2.1 ht.2.2.1 hE) w hw
      · exact tightElems_iff.mp ht.2.2.2 w hw
  | .array elems sh true, .ref (.fixed E n), hc, ht, hok =>
    ⟨ht.1, SVal.defaultOfElems_tight hc.2.2.1 ht.2 (by simpa [Ty.okDeep] using hok)⟩
  | .array _ _ true, .ref (.array _), hc, _, _ => nomatch hc.1
  | .array _ _ false, .ref (.fixed _ _), hc, _, _ => nomatch hc.1
  | .map _ _, .ref (.mapping _ _), _, ht, _ => ht
  | .prim pv, .ref _, hc, _, _ => by cases pv <;> exact hc.elim
  | .struct _, .prim _, hc, _, _ | .array _ _ _, .prim _, hc, _, _ | .map _ _, .prim _, hc, _, _ =>
    hc.elim
  | .struct _, .ref (.array _), hc, _, _ | .struct _, .ref (.mapping _ _), hc, _, _
  | .struct _, .ref (.fixed _ _), hc, _, _ => hc.elim
  | .array _ _ _, .ref (.struct _), hc, _, _ | .array _ _ _, .ref (.mapping _ _), hc, _, _ =>
    hc.elim
  | .map _ _, .ref (.struct _), hc, _, _ | .map _ _, .ref (.array _), hc, _, _
  | .map _ _, .ref (.fixed _ _), hc, _, _ => hc.elim

theorem SVal.defaultOfFields_tight {s : Name} :
    ∀ {fields : List (Name × SVal)}, canonFields s fields → tightFields s fields →
      (∀ {n T}, lookupBy n (structDef s) = some T → T.okDeep = true) →
      tightFields s (SVal.defaultOf.defaultOfFields fields)
  | [], _, _, _ => trivial
  | (n, v) :: rest, hc, ht, hok => by
    refine ⟨?_, SVal.defaultOfFields_tight hc.2 ht.2 hok⟩
    have h1 := hc.1
    have h2 := ht.1
    revert h1 h2
    cases hl : lookupBy n (structDef s) with
    | none => intro _ _; trivial
    | some T => intro h1 h2; exact SVal.defaultOf_tight h1 h2 (hok hl)

theorem SVal.defaultOfElems_tight {E : Ty} :
    ∀ {elems : List SVal}, canonElems E elems → tightElems E elems → E.okDeep = true →
      tightElems E (SVal.defaultOf.defaultOfElems elems)
  | [], _, _, _ => trivial
  | _ :: _, hc, ht, hE =>
    ⟨SVal.defaultOf_tight hc.1 ht.1 hE, SVal.defaultOfElems_tight hc.2 ht.2 hE⟩

end

mutual

/-- A value laid on fresh slots is tight: nothing is past its arrays' ends. -/
theorem SVal.strip_tight : ∀ {v : SVal} {T : Ty}, v.tight T → v.strip.tight T
  | .prim _, _, h => by simpa only [SVal.strip] using h
  | .struct fields, .ref (.struct _), h => SVal.stripFields_tight h
  | .array _ _ _, .ref (.array _), h =>
    ⟨(fun hE => by obtain ⟨h1, -⟩ := h.1 hE; subst h1; exact ⟨rfl, rfl⟩),
      (fun _ w hw => by simp at hw), SVal.stripElems_tight h.2.2.1, trivial⟩
  | .array _ _ _, .ref (.fixed _ _), h => ⟨rfl, SVal.stripElems_tight h.2⟩
  | .map _ _, _, h => by simpa only [SVal.strip] using h
  | .struct _, .prim _, _ | .struct _, .ref (.array _), _ | .struct _, .ref (.mapping _ _), _
  | .struct _, .ref (.fixed _ _), _ => trivial
  | .array _ _ _, .prim _, _ | .array _ _ _, .ref (.struct _), _
  | .array _ _ _, .ref (.mapping _ _), _ => trivial

theorem SVal.stripFields_tight {s : Name} :
    ∀ {fields : List (Name × SVal)}, tightFields s fields →
      tightFields s (SVal.strip.stripFields fields)
  | [], _ => trivial
  | (n, v) :: rest, h => by
    refine ⟨?_, SVal.stripFields_tight h.2⟩
    have h1 := h.1
    revert h1
    cases lookupBy n (structDef s) with
    | none => intro _; trivial
    | some T => exact fun h => SVal.strip_tight h

theorem SVal.stripElems_tight {E : Ty} :
    ∀ {elems : List SVal}, tightElems E elems → tightElems E (SVal.strip.stripElems elems)
  | [], _ => trivial
  | _ :: _, h => ⟨SVal.strip_tight h.1, SVal.stripElems_tight h.2⟩

end

mutual

/-- **A copy keeps storage tight**: the old slots past the new length are
cleared, the ones past the old length kept, and a fixed-size array is
copied over one of its own length. -/
theorem SVal.overlay_tight {old new : SVal} {T : Ty} (hoc : old.canon T) (hot : old.tight T)
    (hnc : new.canon T) (hnt : new.tight T) (hok : T.okDeep = true) :
    (old.overlay new).tight T := by
  match new with
  | .prim p => cases old <;> simpa [SVal.overlay, SVal.strip] using hnt
  | .struct nfs =>
      cases old with
      | struct ofs =>
          cases T with
          | prim p => cases p <;> exact hnc.elim
          | ref r =>
              cases r with
              | struct s =>
                  exact SVal.overlayFields_tight hoc.2 hot hnc.2 hnt
                    (fun hl => member_okDeep hok hl)
              | array _ => exact hnc.elim
              | fixed _ _ => exact hnc.elim
              | mapping _ _ => exact hnc.elim
      | prim _ => simp only [SVal.overlay]; exact SVal.strip_tight hnt
      | array _ _ _ => simp only [SVal.overlay]; exact SVal.strip_tight hnt
      | map _ _ => simp only [SVal.overlay]; exact SVal.strip_tight hnt
  | .array nel nsh nfx =>
      cases old with
      | array oel osh ofx =>
          cases T with
          | prim p => cases p <;> exact hnc.elim
          | ref r =>
              cases r with
              | array E =>
                  have hE : E.okDeep = true := by simpa [Ty.okDeep] using hok
                  simp only [SVal.overlay]
                  refine ⟨fun hf => absurd hf (by simp [okDeep_defaultOkS hE]), fun hp w hw => ?_,
                    SVal.overlayElems_tight (canonElems_append hoc.2.1 hoc.2.2)
                      (tightElems_iff.mpr fun x hx => ?_) hnc.2.1 hnt.2.2.1 hE,
                    tightElems_iff.mpr fun x hx => ?_⟩
                  · rcases List.mem_append.mp hw with hw | hw
                    · obtain ⟨p, rfl⟩ : ∃ p, E = .prim p := by
                        cases E with
                        | prim p => exact ⟨p, rfl⟩
                        | ref _ => simp [Ty.isPrimitive] at hp
                      exact defaultOfElems_prim (canonElems_drop _ hoc.2.1) w hw
                    · exact hot.2.1 hp w (List.mem_of_mem_drop hw)
                  · rcases List.mem_append.mp hx with hx | hx
                    · exact tightElems_iff.mp hot.2.2.1 x hx
                    · exact tightElems_iff.mp hot.2.2.2 x hx
                  · rcases List.mem_append.mp hx with hx | hx
                    · exact tightElems_iff.mp (SVal.defaultOfElems_tight
                        (canonElems_drop _ hoc.2.1)
                        (tightElems_iff.mpr fun y hy =>
                          tightElems_iff.mp hot.2.2.1 y (List.mem_of_mem_drop hy)) hE) x hx
                    · exact tightElems_iff.mp hot.2.2.2 x (List.mem_of_mem_drop hx)
              | fixed E n =>
                  have hE : E.okDeep = true := by simpa [Ty.okDeep] using hok
                  have holen : oel.length = n := hoc.2.1
                  have hnlen : nel.length = n := hnc.2.1
                  obtain ⟨hsh, hote⟩ := hot
                  subst hsh
                  simp only [SVal.overlay]
                  refine ⟨?_, SVal.overlayElems_tight (canonElems_append hoc.2.2.1 hoc.2.2.2)
                    (by simpa using hote) hnc.2.2.1 hnt.2 hE⟩
                  rw [hnlen, ← holen]; simp [SVal.defaultOf.defaultOfElems]
              | struct _ => exact hnc.elim
              | mapping _ _ => exact hnc.elim
      | prim _ => simp only [SVal.overlay]; exact SVal.strip_tight hnt
      | struct _ => simp only [SVal.overlay]; exact SVal.strip_tight hnt
      | map _ _ => simp only [SVal.overlay]; exact SVal.strip_tight hnt
  | .map ne nd =>
      cases old with
      | map oe od => simpa only [SVal.overlay] using hot
      | prim _ => simp only [SVal.overlay]; exact SVal.strip_tight hnt
      | struct _ => simp only [SVal.overlay]; exact SVal.strip_tight hnt
      | array _ _ _ => simp only [SVal.overlay]; exact SVal.strip_tight hnt

theorem SVal.overlayFields_tight {s : Name} {ofs nfs : List (Name × SVal)}
    (hoc : canonFields s ofs) (hot : tightFields s ofs) (hnc : canonFields s nfs)
    (hnt : tightFields s nfs) (hok : ∀ {n T}, lookupBy n (structDef s) = some T → T.okDeep = true) :
    tightFields s (SVal.overlay.overlayFields ofs nfs) := by
  match nfs with
  | [] => trivial
  | (n, v) :: rest =>
      refine ⟨?_, SVal.overlayFields_tight hoc hot hnc.2 hnt.2 hok⟩
      have h1 := hnc.1
      have h2 := hnt.1
      revert h1 h2
      cases hdef : lookupBy n (structDef s) with
      | none => intro _ _; trivial
      | some T =>
          intro h1 h2
          cases hl : lookupBy n ofs with
          | none => exact SVal.strip_tight h2
          | some o =>
              obtain ⟨T', hd', hoc'⟩ := canonFields_lookup hoc hl
              rw [hdef] at hd'
              cases hd'
              exact SVal.overlay_tight hoc' (tightFields_lookup hot hl hdef) h1 h2 (hok hdef)

theorem SVal.overlayElems_tight {E : Ty} {olds news : List SVal}
    (hoc : canonElems E olds) (hot : tightElems E olds) (hnc : canonElems E news)
    (hnt : tightElems E news) (hE : E.okDeep = true) :
    tightElems E (SVal.overlay.overlayElems olds news) := by
  match olds, news with
  | o :: os, v :: rest =>
    exact ⟨SVal.overlay_tight hoc.1 hot.1 hnc.1 hnt.1 hE,
      SVal.overlayElems_tight hoc.2 hot.2 hnc.2 hnt.2 hE⟩
  | [], rest => simpa only [SVal.overlay.overlayElems] using SVal.stripElems_tight hnt
  | _ :: _, [] => trivial

end

/-! ### Memory copied back -/

/-- A value with no mapping and nothing past its arrays' ends: what a copy
out of memory gives. -/
def Semantics.SVal.plain : SVal → Prop
  | .prim _ => True
  | .struct fields => plainFields fields
  | .array elems shadow _ => shadow = [] ∧ plainElems elems
  | .map _ _ => False
where
  plainFields : List (Name × SVal) → Prop
    | [] => True
    | (_, v) :: rest => v.plain ∧ plainFields rest
  plainElems : List SVal → Prop
    | [] => True
    | v :: rest => v.plain ∧ plainElems rest

open Semantics.SVal.plain (plainFields plainElems)

mutual

theorem plain_tight : ∀ {v : SVal} {T : Ty}, v.plain → v.canon T → T.okDeep = true → v.tight T
  | .prim _, .prim _, _, _, _ => trivial
  | .prim pv, .ref _, _, hc, _ => by cases pv <;> exact hc.elim
  | .struct fields, .ref (.struct s), hp, hc, hok =>
    plainFields_tight hp hc.2 (fun hl => member_okDeep hok hl)
  | .array elems sh _, .ref (.array E), hp, hc, hok => by
    obtain ⟨rfl, hpe⟩ := hp
    have hE : E.okDeep = true := by simpa [Ty.okDeep] using hok
    exact ⟨fun hf => absurd hf (by simp [okDeep_defaultOkS hE]), fun _ w hw => by simp at hw,
      plainElems_tight hpe hc.2.1 hE, trivial⟩
  | .array elems sh _, .ref (.fixed E _), hp, hc, hok => by
    obtain ⟨rfl, hpe⟩ := hp
    exact ⟨rfl, plainElems_tight hpe hc.2.2.1 (by simpa [Ty.okDeep] using hok)⟩
  | .map _ _, .prim _, hp, _, _ | .map _ _, .ref _, hp, _, _ => hp.elim
  | .struct _, .prim _, _, _, _ | .struct _, .ref (.array _), _, _, _
  | .struct _, .ref (.mapping _ _), _, _, _ | .struct _, .ref (.fixed _ _), _, _, _ => trivial
  | .array _ _ _, .prim _, _, _, _ | .array _ _ _, .ref (.struct _), _, _, _
  | .array _ _ _, .ref (.mapping _ _), _, _, _ => trivial

theorem plainFields_tight {s : Name} :
    ∀ {fields : List (Name × SVal)}, plainFields fields → canonFields s fields →
      (∀ {n T}, lookupBy n (structDef s) = some T → T.okDeep = true) → tightFields s fields
  | [], _, _, _ => trivial
  | (n, v) :: rest, hp, hc, hok => by
    refine ⟨?_, plainFields_tight hp.2 hc.2 hok⟩
    have h1 := hc.1
    revert h1
    cases hl : lookupBy n (structDef s) with
    | none => intro _; trivial
    | some T => intro h1; exact plain_tight hp.1 h1 (hok hl)

theorem plainElems_tight {E : Ty} :
    ∀ {elems : List SVal}, plainElems elems → canonElems E elems → E.okDeep = true →
      tightElems E elems
  | [], _, _, _ => trivial
  | _ :: _, hp, hc, hE => ⟨plain_tight hp.1 hc.1 hE, plainElems_tight hp.2 hc.2 hE⟩

end

theorem copyMFields_plain {s : State} {rem : List Nat}
    (IH : ∀ {mv : MVal} {sv : SVal}, copyMToSt s rem mv = .ok sv → sv.plain) :
    ∀ {fields : List (Name × MVal)} {sfields : List (Name × SVal)},
      copyMFields s rem fields = .ok sfields → plainFields sfields
  | [], sfields, hcopy => by
    simp only [copyMFields, Except.ok.injEq] at hcopy
    subst hcopy; trivial
  | (n, v) :: rest, sfields, hcopy => by
    rw [copyMFields] at hcopy
    obtain ⟨sv, hv, hcopy⟩ := bind_ok_inv hcopy
    obtain ⟨srest, hrest, hcopy⟩ := bind_ok_inv hcopy
    cases hcopy
    exact ⟨IH hv, copyMFields_plain IH hrest⟩

theorem copyMElems_plain {s : State} {rem : List Nat}
    (IH : ∀ {mv : MVal} {sv : SVal}, copyMToSt s rem mv = .ok sv → sv.plain) :
    ∀ {elems : List MVal} {selems : List SVal}, copyMElems s rem elems = .ok selems →
      plainElems selems
  | [], selems, hcopy => by
    simp only [copyMElems, Except.ok.injEq] at hcopy
    subst hcopy; trivial
  | v :: rest, selems, hcopy => by
    rw [copyMElems] at hcopy
    obtain ⟨sv, hv, hcopy⟩ := bind_ok_inv hcopy
    obtain ⟨srest, hrest, hcopy⟩ := bind_ok_inv hcopy
    cases hcopy
    exact ⟨IH hv, copyMElems_plain IH hrest⟩

/-- A copy out of memory has no mapping and nothing past its arrays' ends. -/
theorem copyMToSt_plain {s : State} {rem : List Nat} :
    ∀ {mv : MVal} {sv : SVal}, copyMToSt s rem mv = .ok sv → sv.plain := by
  intro mv sv hcopy
  cases mv with
  | prim p =>
    cases p <;> simp only [copyMToSt, Except.ok.injEq] at hcopy <;> subst hcopy <;> trivial
  | ref id =>
    by_cases hmem : id ∈ rem
    · simp only [copyMToSt, hmem, dif_pos] at hcopy
      split at hcopy
      · obtain ⟨sfields, hfs, hcopy⟩ := bind_ok_inv hcopy
        cases hcopy
        exact copyMFields_plain (fun hc' => copyMToSt_plain hc') hfs
      · obtain ⟨selems, hes, hcopy⟩ := bind_ok_inv hcopy
        cases hcopy
        exact ⟨rfl, copyMElems_plain (fun hc' => copyMToSt_plain hc') hes⟩
      · exact nomatch hcopy
    · simp only [copyMToSt, hmem, dif_neg, not_false_iff] at hcopy
      exact nomatch hcopy
termination_by rem.length
decreasing_by all_goals
  (have h1 := List.length_erase_of_mem hmem
   have h2 := List.length_pos_of_mem hmem
   omega)

/-! ### The state -/

/-- Every alias the environment binds was bound along a path whose mappings
are indexed by numbers. -/
def TightEnv (C : Contract) (env : List (Var × Binding)) : Prop :=
  ∀ x r segs, lookupBy x env = some (.spath r segs) →
    ∃ T, lookupBy r C.vars = some T ∧ KeysOK T segs

/-- What a run keeps beyond `Canon`: tight storage, and aliases bound along
numeric keys. -/
structure Tight (C : Contract) (σ : State) : Prop where
  storage : TightStorage C σ.storage
  env : TightEnv C σ.env

/-- Every root's type has well-formed defaults all the way down. -/
def DeepOk (C : Contract) : Prop := ∀ r T, lookupBy r C.vars = some T → T.okDeep = true

namespace Tight

variable {H : HeapTy} {σ σ' : State}

theorem of_eq (ht : Tight C σ) (hs : σ'.storage = σ.storage) (he : σ'.env = σ.env) :
    Tight C σ' := ⟨hs ▸ ht.storage, he ▸ ht.env⟩

/-- Binding a local to a value or a memory object keeps the aliases. -/
theorem setEnv (ht : Tight C σ) (x : Var) {b : Binding} (hb : ∀ r segs, b ≠ .spath r segs) :
    Tight C (σ.setEnv x b) := by
  refine ⟨ht.storage, fun y r segs hy => ?_⟩
  change lookupBy y (setBy x b σ.env) = _ at hy
  by_cases h : y = x
  · subst h; rw [lookupBy_setBy_self] at hy; cases hy; exact absurd rfl (hb r segs)
  · rw [lookupBy_setBy_ne h] at hy; exact ht.env y r segs hy

/-- Binding an alias along numeric keys keeps the aliases so. -/
theorem setEnv_path (ht : Tight C σ) (x : Var) {r : Name} {segs : List Seg}
    (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs) (hr : ∃ T, lookupBy r C.vars = some T) :
    Tight C (σ.setEnv x (.spath r segs)) := by
  refine ⟨ht.storage, fun y r' segs' hy => ?_⟩
  change lookupBy y (setBy x _ σ.env) = _ at hy
  by_cases h : y = x
  · subst h; rw [lookupBy_setBy_self] at hy; cases hy
    obtain ⟨T, hT⟩ := hr
    exact ⟨T, hT, hk T hT⟩
  · rw [lookupBy_setBy_ne h] at hy; exact ht.env y r' segs' hy

theorem find (hd : DeepOk C) (hc : Canon C H σ) (ht : Tight C σ) {r : Name} {segs : List Seg}
    {T' : Ty} {w : SVal} (hT : C.layout.tyAt r segs = some T') (hf : σ.findStorage r segs = .ok w) :
    w.tight T' := by
  obtain ⟨T, hr, hs⟩ := Layout.tyAt_split hT
  obtain ⟨V, hV, hcV⟩ := hc.storage.2 r T hr
  simp only [State.findStorage, hV] at hf
  exact find_tight hcV (ht.storage r T V hr hV) (hd r T hr) hs hf

theorem save (hd : DeepOk C) (hc : Canon C H σ) (ht : Tight C σ) {r : Name} {segs : List Seg}
    {T' : Ty} {new : SVal} (hT : C.layout.tyAt r segs = some T')
    (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (hlive : T'.isPrimitive = true → ∀ V, lookupBy r σ.storage = some V → IdxLive V segs)
    (hnew : new.tight T') (h : σ.saveStorage r segs new = .ok σ') : Tight C σ' := by
  obtain ⟨T, hr, hs⟩ := Layout.tyAt_split hT
  obtain ⟨V, hV, hcV⟩ := hc.storage.2 r T hr
  obtain ⟨_, up, hV', hup, rfl⟩ := SemanticsProperties.State.saveStorage_ok_inv h
  cases hV.symm.trans hV'
  refine ⟨fun r' T'' v hr' hv => ?_, ht.env⟩
  change lookupBy r' (setBy r up σ.storage) = _ at hv
  by_cases he : r' = r
  · subst he
    rw [lookupBy_setBy_self] at hv; cases hv
    cases hr.symm.trans hr'
    exact save_tight hcV (ht.storage r' T V hr hV) (hd r' T hr) hs (hk T hr)
      (fun hp => hlive hp V hV) hnew hup
  · rw [lookupBy_setBy_ne he] at hv; exact ht.storage r' T'' v hr' hv

theorem write (hd : DeepOk C) (hc : Canon C H σ) (ht : Tight C σ) {r : Name} {segs : List Seg}
    {T' : Ty} {new : SVal} (hT : C.layout.tyAt r segs = some T')
    (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (hlive : T'.isPrimitive = true → ∀ V, lookupBy r σ.storage = some V → IdxLive V segs)
    (hnc : new.canon T') (hnt : new.tight T') (h : σ.writeStorage r segs new = .ok σ') :
    Tight C σ' := by
  rcases State.writeStorage_ok_inv h with h | ⟨cur, hcur, h⟩
  · exact ht.save hd hc hT hk hlive hnt h
  · obtain ⟨T, hr, hs⟩ := Layout.tyAt_split hT
    exact ht.save hd hc hT hk hlive (SVal.overlay_tight (hc.find hT hcur) (ht.find hd hc hT hcur)
      hnc hnt (okDeep_tyAtSegs (hd r T hr) hs)) h

end Tight

/-! ### Paths -/

section Paths

variable {Γ : Ctx} {H : HeapTy} {σ : State}

theorem eval_key_numeric (hwt : RunWT C Γ H σ) {k : PrimTy} {i : Val C k} {w : Value} {iv : Int}
    (hw : i.wt Γ = true) (he : i.eval σ = .ok w) (hi : w.asInt = .ok iv) : k.isNumeric = true := by
  have := Val.eval_wt hwt i hw he
  cases w with
  | int n => cases k <;> simp_all [Value.toSVal, SVal.hasTy, PrimTy.isNumeric]
  | bool b => simp [Value.asInt] at hi

mutual

/-- A checked path resolves along numeric keys. -/
theorem SPath.resolve_keys (hwt : RunWT C Γ H σ) (hte : TightEnv C σ.env) :
    ∀ {T : Ty} (p : SPath C T) {r : Name} {segs : List Seg},
      p.wt Γ = true → p.resolve σ = .ok (r, segs) → ∀ T₀, lookupBy r C.vars = some T₀ →
        KeysOK T₀ segs
  | _, .alias x, r, segs, _, h, T₀, hr => by
    simp only [SPath.resolve, aliasPath, State.getEnv] at h
    cases hx : lookupBy x σ.env with
    | none => simp [hx, bind, Except.bind] at h
    | some b =>
      cases b with
      | spath r' segs' =>
        simp only [hx, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨T, hT, hk⟩ := hte x r' segs' hx
        rw [hr] at hT; cases hT; exact hk
      | val _ => simp [hx, bind, Except.bind] at h
      | mref _ => simp [hx, bind, Except.bind] at h
      | store _ => simp [hx, bind, Except.bind] at h
      | ledger _ => simp [hx, bind, Except.bind] at h
  | _, .loc l, r, segs, hw, h, T₀, hr => Loc.resolve_keys hwt hte l hw h T₀ hr

theorem Loc.resolve_keys (hwt : RunWT C Γ H σ) (hte : TightEnv C σ.env) :
    ∀ {T : Ty} (l : Loc C T) {r : Name} {segs : List Seg},
      l.wt Γ = true → l.resolve σ = .ok (r, segs) → ∀ T₀, lookupBy r C.vars = some T₀ →
        KeysOK T₀ segs
  | _, .root r' _, r, segs, _, h, T₀, _ => by
    simp only [Loc.resolve, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; trivial
  | _, .field b f hf, r, segs, hw, h, T₀, hr => by
    obtain ⟨⟨r0, s0⟩, h0, h⟩ := bind_ok_inv h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb := SPath.resolve_wt hwt b hw h0
    obtain ⟨T, hT, hs⟩ := Layout.tyAt_split hb
    cases hr.symm.trans hT
    exact KeysOK_append _ (SPath.resolve_keys hwt hte b hw h0 T₀ hr) hs
      (fun K V h => nomatch h)
  | _, .index it b i, r, segs, hw, h, T₀, hr => by
    simp only [Loc.wt, Bool.and_eq_true] at hw
    obtain ⟨⟨r0, s0⟩, h0, h⟩ := bind_ok_inv h
    obtain ⟨w, hwv, h⟩ := bind_ok_inv h
    obtain ⟨iv, hiv, h⟩ := bind_ok_inv h
    bind_inv h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb := SPath.resolve_wt hwt b hw.1 h0
    obtain ⟨T, hT, hs⟩ := Layout.tyAt_split hb
    cases hr.symm.trans hT
    refine KeysOK_append _ (SPath.resolve_keys hwt hte b hw.1 h0 T₀ hr) hs ?_
    intro K V hKV
    cases it with
    | map =>
      simp only [Ty.ref.injEq, RefTy.mapping.injEq] at hKV
      obtain ⟨rfl, rfl⟩ := hKV
      exact eval_key_numeric hwt hw.2 hwv hiv
    | arr a => cases a <;> exact nomatch hKV

end

theorem append_single_ne {l l' : List Seg} {a b : Seg} (h : l ++ [a] = l' ++ [b]) :
    l = l' ∧ a = b := by
  have := List.append_inj' h rfl
  simpa using this

/-- A checked index is live where the path is taken. -/
theorem Loc.resolve_live : ∀ {T : Ty} (l : Loc C T) {r : Name} {segs : List Seg},
    l.resolve σ = .ok (r, segs) → ∀ V, lookupBy r σ.storage = some V → IdxLive V segs
  | _, .root r' _, r, segs, h, V, _ => by
    simp only [Loc.resolve, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro pre i hseg; simp at hseg
  | _, .field b f hf, r, segs, h, V, _ => by
    obtain ⟨⟨r0, s0⟩, h0, h⟩ := bind_ok_inv h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro pre i hseg
    exact nomatch (append_single_ne hseg).2
  | _, .index it b i, r, segs, h, V, hV => by
    obtain ⟨⟨r0, s0⟩, h0, h⟩ := bind_ok_inv h
    obtain ⟨w, hwv, h⟩ := bind_ok_inv h
    obtain ⟨iv, hiv, h⟩ := bind_ok_inv h
    obtain ⟨u, hck, h⟩ := bind_ok_inv h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro pre j hseg es sh fx hf
    obtain ⟨rfl, hj⟩ := append_single_ne hseg
    cases hj
    simp only [State.checkIndex, State.findStorage, hV, hf, bind, Except.bind] at hck
    split at hck
    · assumption
    · exact nomatch hck

end Paths

/-! ### Pushes and pops -/

section Effects

variable {H : HeapTy} {σ σ' : State}

theorem pushSlot_tight {E : Ty} {shadow : List SVal} (hE : E.defaultOkS = true)
    (hsh : tightElems E shadow) :
    (pushSlot E shadow).1.tight E ∧ (∀ w ∈ (pushSlot E shadow).2, w ∈ shadow) := by
  cases shadow with
  | nil => exact ⟨defaultForTy_tight hE, fun w hw => by simp [pushSlot] at hw⟩
  | cons c rest =>
    refine ⟨?_, fun w hw => List.mem_cons_of_mem _ hw⟩
    simp only [pushSlot]
    split
    · exact defaultForTy_tight hE
    · exact hsh.1

/-- An array one element longer, the slot it took gone from past its end. -/
theorem pushed_tight {E : Ty} {elems shadow shadow' : List SVal} {x : SVal}
    (hE : E.okDeep = true) (ht : (SVal.array elems shadow false).tight (.ref (.array E)))
    (hx : x.tight E) (hsub : ∀ w ∈ shadow', w ∈ shadow) :
    (SVal.array (elems ++ [x]) shadow' false).tight (.ref (.array E)) := by
  obtain ⟨-, hpr, hte, hts⟩ := ht
  refine ⟨fun hf => absurd hf (by simp [okDeep_defaultOkS hE]), fun hp w hw => hpr hp w (hsub w hw),
    tightElems_iff.mpr fun w hw => ?_, tightElems_iff.mpr fun w hw => tightElems_iff.mp hts w (hsub w hw)⟩
  rcases List.mem_append.mp hw with hw | hw
  · exact tightElems_iff.mp hte w hw
  · simp at hw; subst hw; exact hx

theorem arr_okDeep {E : Ty} (hd : DeepOk C) {r : Name} {segs : List Seg}
    (hT : C.layout.tyAt r segs = some (.ref (.array E))) : E.okDeep = true := by
  obtain ⟨T, hr, hs⟩ := Layout.tyAt_split hT
  simpa [Ty.okDeep] using okDeep_tyAtSegs (hd r T hr) hs

theorem pushAt_tight (hd : DeepOk C) (hc : Canon C H σ) (ht : Tight C σ) {E : Ty} {r : Name}
    {segs : List Seg} {val : SVal → Res SVal} (hT : C.layout.tyAt r segs = some (.ref (.array E)))
    (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (hval : ∀ slot v, slot.tight E → val slot = .ok v → v.tight E)
    (h : pushAt σ E r segs val = .ok σ') : Tight C σ' := by
  have hE := arr_okDeep hd hT
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hts := ht.find hd hc hT hsv
  obtain ⟨elems, shadow, rfl, -, -⟩ := canon_array (hc.find hT hsv)
  obtain ⟨newElem, hnew, h⟩ := bind_ok_inv h
  obtain ⟨hs1, hs2⟩ := pushSlot_tight (okDeep_defaultOkS hE) hts.2.2.2
  exact ht.save hd hc hT hk (fun hp => by simp [Ty.isPrimitive] at hp)
    (pushed_tight hE hts (hval _ _ hs1 hnew) hs2) h

theorem pushPlaceAt_tight (hd : DeepOk C) (hc : Canon C H σ) (ht : Tight C σ) {E : Ty} {r : Name}
    {segs : List Seg} {n : Int} (hT : C.layout.tyAt r segs = some (.ref (.array E)))
    (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (h : pushPlaceAt σ E r segs = .ok (σ', n)) : Tight C σ' := by
  have hE := arr_okDeep hd hT
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hts := ht.find hd hc hT hsv
  obtain ⟨elems, shadow, rfl, -, -⟩ := canon_array (hc.find hT hsv)
  obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
  cases h
  obtain ⟨hs1, hs2⟩ := pushSlot_tight (okDeep_defaultOkS hE) hts.2.2.2
  exact ht.save hd hc hT hk (fun hp => by simp [Ty.isPrimitive] at hp)
    (pushed_tight hE hts hs1 hs2) hσ₁

theorem popAt_tight (hd : DeepOk C) (hc : Canon C H σ) (ht : Tight C σ) {E : Ty} {r : Name}
    {segs : List Seg} (hT : C.layout.tyAt r segs = some (.ref (.array E)))
    (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (h : popAt σ E.isMapping r segs = .ok σ') : Tight C σ' := by
  have hE := arr_okDeep hd hT
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hts := ht.find hd hc hT hsv
  obtain ⟨elems, shadow, rfl, he, hsh⟩ := canon_array (hc.find hT hsv)
  obtain ⟨-, hpr, hte, htsh⟩ := hts
  simp only at h
  split at h
  · exact nomatch h
  · rename_i last restRev hrev
    have hmem : ∀ v, v ∈ last :: restRev → v ∈ elems := by
      intro v hv; rw [← hrev] at hv; exact List.mem_reverse.mp hv
    have hlc := canonElems_mem he (hmem last List.mem_cons_self)
    have hlt := tightElems_iff.mp hte last (hmem last List.mem_cons_self)
    refine ht.save hd hc hT hk (fun hp => by simp [Ty.isPrimitive] at hp) ?_ h
    refine ⟨fun hf => absurd hf (by simp [okDeep_defaultOkS hE]), fun hp w hw => ?_,
      tightElems_iff.mpr fun v hv => tightElems_iff.mp hte v
        (hmem v (List.mem_cons_of_mem _ (List.mem_reverse.mp hv))), ?_⟩
    · rcases List.mem_cons.mp hw with rfl | hw
      · obtain ⟨p, rfl⟩ : ∃ p, E = .prim p := by
          cases E with
          | prim p => exact ⟨p, rfl⟩
          | ref _ => simp [Ty.isPrimitive] at hp
        simp only [Ty.isMapping, Bool.false_eq_true, ↓reduceIte]
        exact defaultOf_prim hlc
      · exact hpr hp w hw
    · refine ⟨?_, htsh⟩
      split
      · exact hlt
      · exact SVal.defaultOf_tight hlc hlt hE

end Effects

/-! ### What does not touch storage or aliases -/

section Frames

variable {σ σ' : State}

/-- Storage and locals as they were: a write into memory, an allocation. -/
def SE (σ σ' : State) : Prop := σ'.storage = σ.storage ∧ σ'.env = σ.env

theorem SE.tight (h : SE σ σ') (ht : Tight C σ) : Tight C σ' := ht.of_eq h.1 h.2

theorem SE.trans {σ₁ σ₂ σ₃ : State} (h₁ : SE σ₁ σ₂) (h₂ : SE σ₂ σ₃) : SE σ₁ σ₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem memWriteField_se {id : Nat} {f : Name} {mv : MVal}
    (h : memWriteField σ id f mv = .ok σ') : SE σ σ' := by
  obtain ⟨o, _, h⟩ := bind_ok_inv h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · exact nomatch h

theorem memWriteIndex_se {id : Nat} {i : Int} {mv : MVal}
    (h : memWriteIndex σ id i mv = .ok σ') : SE σ σ' := by
  obtain ⟨o, _, h⟩ := bind_ok_inv h
  split at h
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · exact nomatch h
  · exact nomatch h

theorem writeLoc_se {loc : Addr} {v : Value} (h : writeLoc σ loc v = .ok σ') : SE σ σ' := by
  cases loc with
  | memoryField id f =>
    obtain ⟨o, _, h⟩ := bind_ok_inv h
    split at h
    · cases h; exact ⟨rfl, rfl⟩
    · exact nomatch h
  | memoryIndex id i =>
    obtain ⟨o, _, h⟩ := bind_ok_inv h
    split at h
    · split at h
      · cases h; exact ⟨rfl, rfl⟩
      · exact nomatch h
    · exact nomatch h

theorem writeAddr_se {a : Addr} {mv : MVal} (h : writeAddr σ mv a = .ok σ') : SE σ σ' := by
  cases a with
  | memoryField id f => exact memWriteField_se h
  | memoryIndex id i => exact memWriteIndex_se h

theorem opMem_se {op : BinOp} {p : PrimTy} {loc : Addr} {v : Value}
    (h : opMem σ op p loc v = .ok σ') : SE σ σ' :=
  let ⟨_, _, _, _, _, h⟩ := opMem_ok_inv h
  writeLoc_se h

theorem bumpMem_se {op : IncDec} {p : PrimTy} {loc : Addr} {w : Value}
    (h : bumpMem σ op p loc = .ok (σ', w)) : SE σ σ' :=
  let ⟨_, _, _, h, _⟩ := bumpMem_ok_inv h
  writeLoc_se h

theorem MLoc.write_se {mv : MVal} : ∀ {T : Ty} (l : MLoc C T), l.write σ mv = .ok σ' → SE σ σ'
  | _, .field b f _, h => by
    iterate 2 bind_inv h
    exact memWriteField_se h
  | _, .index _ b i, h => by
    iterate 4 bind_inv h
    exact memWriteIndex_se h

theorem copyStToM_se {v : SVal} {mv : MVal} (h : copyStToM σ v = .ok (σ', mv)) : SE σ σ' := by
  have := SemanticsProperties.copyStToM_frame σ v σ' mv h
  exact ⟨this.1, this.2.1⟩

theorem allocDefault_se {R : RefTy} {id : Nat} (h : allocDefault σ R = .ok (σ', id)) : SE σ σ' := by
  simp only [allocDefault] at h
  split at h
  · rename_i hc; cases h; exact copyStToM_se hc
  · exact nomatch h
  · exact nomatch h

theorem memClear_se {a : Addr} : ∀ {T : Ty}, memClear σ a T = .ok σ' → SE σ σ'
  | .prim _, h => writeAddr_se h
  | .ref _, h => by
    obtain ⟨⟨σ₁, id⟩, h₁, h⟩ := bind_ok_inv h
    exact (allocDefault_se h₁).trans (writeAddr_se h)

theorem transferAt_se {addr amt : Int} (h : transferAt σ addr amt = .ok σ') : SE σ σ' := by
  unfold transferAt at h
  split at h
  · exact nomatch h
  · cases h; rw [State.pay_eq]; exact ⟨rfl, rfl⟩

theorem pay_se (addr amt : Int) : SE σ (σ.pay addr amt) := by
  rw [State.pay_eq]; exact ⟨rfl, rfl⟩

theorem MRhs.bind_se {x : Var} {R : RefTy} {r : MRhs C R} (h : r.bind σ x = .ok σ') :
    ∃ σ₁ id, SE σ σ₁ ∧ σ' = σ₁.setEnv x (.mref id) := by
  cases r with
  | alias p =>
    bind_inv h
    obtain ⟨id, _, h⟩ := bind_ok_inv h
    cases h
    exact ⟨σ, id, ⟨rfl, rfl⟩, rfl⟩
  | copy p _ =>
    iterate 2 bind_inv h
    obtain ⟨⟨σ₁, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id, _, h⟩ := bind_ok_inv h
    cases h
    exact ⟨σ₁, id, copyStToM_se hcopy, rfl⟩
  | newArr n _ =>
    iterate 2 bind_inv h
    obtain ⟨⟨σ₁, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id, _, h⟩ := bind_ok_inv h
    cases h
    exact ⟨σ₁, id, copyStToM_se hcopy, rfl⟩

theorem Arg.bindSeq_tight {args : List (Arg C)} {σ σ' : State} (ht : Tight C σ)
    (h : Arg.bindSeq args σ = .ok σ') : Tight C σ' :=
  Arg.bindSeq_induct (fun _ x _ ht => ht.setEnv x (fun _ _ h => Binding.noConfusion h)) ht h

theorem bindData_tight {xs : List (PrimTy × Var)} {vs : List Value} {σ σ' : State}
    (ht : Tight C σ) (h : bindData xs vs σ = .ok σ') : Tight C σ' :=
  bindData_induct (fun _ x _ ht => ht.setEnv x (fun _ _ h => Binding.noConfusion h)) ht h

theorem CallRet.enter_tight (ht : Tight C σ) (ret : CallRet) : Tight C (ret.enter σ) :=
  CallRet.enter_induct (fun _ _ _ ht => ht.setEnv _ (fun _ _ h => Binding.noConfusion h)) ret ht

theorem CallRet.leave_tight (ht : Tight C σ) (ret : CallRet)
    (h : CallRet.leave (C := C) σ ret = .ok σ') : Tight C σ' :=
  CallRet.leave_induct (fun _ x _ ht => ht.setEnv x (fun _ _ h => Binding.noConfusion h)) ret ht h

end Frames

/-! ### Statements -/

section Run

variable {Γ : Ctx} {H : HeapTy} {σ σ' : State}

theorem IdxLive.nil (V : SVal) : IdxLive V [] := fun _ _ h => by simp at h

theorem Src.value_tight (hd : DeepOk C) (hwt : RunWT C Γ H σ) (hc : Canon C H σ)
    (ht : Tight C σ) {T : Ty} {r : Src C T} {sv : SVal} (hw : r.wt Γ = true)
    (h : r.value σ = .ok sv) : sv.tight T := by
  cases r with
  | val v =>
    obtain ⟨w, _, h⟩ := bind_ok_inv h
    cases h; cases w <;> trivial
  | copy p _ =>
    obtain ⟨⟨r, segs⟩, hr, h⟩ := bind_ok_inv h
    exact ht.find hd hc (SPath.resolve_wt hwt p hw hr) h

/-- A word written back at a checked path: `alice.age += 1;`. -/
theorem Tight.saveWord (hd : DeepOk C) (hc : Canon C H σ) (ht : Tight C σ) {r : Name}
    {segs : List Seg} {p : PrimTy} {v : Value} (hT : C.layout.tyAt r segs = some (.prim p))
    (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (hlive : ∀ V, lookupBy r σ.storage = some V → IdxLive V segs)
    (h : σ.saveStorage r segs v.toSVal = .ok σ') : Tight C σ' :=
  ht.save hd hc hT hk (fun _ => hlive) (by cases v <;> trivial) h

theorem opStore_tight (hd : DeepOk C) (hc : Canon C H σ) (ht : Tight C σ) {op : BinOp}
    {p : PrimTy} {r : Name} {segs : List Seg} {v : Value}
    (hT : C.layout.tyAt r segs = some (.prim p)) (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (hlive : ∀ V, lookupBy r σ.storage = some V → IdxLive V segs)
    (h : opStore σ op p r segs v = .ok σ') : Tight C σ' :=
  let ⟨_, _, _, _, _, h⟩ := opStore_ok_inv h
  ht.saveWord hd hc hT hk hlive h

theorem bumpStore_tight (hd : DeepOk C) (hc : Canon C H σ) (ht : Tight C σ) {op : IncDec}
    {p : PrimTy} {r : Name} {segs : List Seg} {w : Value}
    (hT : C.layout.tyAt r segs = some (.prim p)) (hk : ∀ T, lookupBy r C.vars = some T → KeysOK T segs)
    (hlive : ∀ V, lookupBy r σ.storage = some V → IdxLive V segs)
    (h : bumpStore σ op p r segs = .ok (σ', w)) : Tight C σ' :=
  let ⟨_, _, _, h, _⟩ := bumpStore_ok_inv h
  ht.saveWord hd hc hT hk hlive h

theorem OpLoc.store_tight (hd : DeepOk C) (hwt : RunWT C Γ H σ) (hc : Canon C H σ)
    (ht : Tight C σ) {op : BinOp} :
    ∀ {p : PrimTy} (l : OpLoc C p) {v : Value}, l.wt Γ = true → l.store σ op v = .ok σ' →
      Tight C σ'
  | p, .local x, v, hw, h => by
    obtain ⟨b, hb, _⟩ := hwt.lookup hw
    simp only [OpLoc.store, opLocal, hb, bind, Except.bind] at h
    cases b with
    | val old =>
      simp only [pure, Except.pure] at h
      split at h
      · exact nomatch h
      · split at h
        · exact nomatch h
        · cases h; exact ht.setEnv x (fun _ _ h => Binding.noConfusion h)
    | spath _ _ => exact nomatch h
    | mref _ => exact nomatch h
    | store _ => exact nomatch h
    | ledger _ => exact nomatch h
  | p, .root r hr, v, _, h =>
    opStore_tight hd hc ht (Contract.layout_tyAt_root hr) (fun _ _ => trivial)
      (fun V _ => IdxLive.nil V) h
  | p, .field b f hf, v, hw, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    exact opStore_tight hd hc ht (Loc.resolve_wt hwt (.field b f hf) hw hr)
      (Loc.resolve_keys hwt ht.env (.field b f hf) hw hr) (Loc.resolve_live (.field b f hf) hr) h
  | p, .index it b i, v, hw, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    exact opStore_tight hd hc ht (Loc.resolve_wt hwt (.index it b (.simple i)) hw hr)
      (Loc.resolve_keys hwt ht.env (.index it b (.simple i)) hw hr)
      (Loc.resolve_live (.index it b (.simple i)) hr) h
  | p, .mfield b f hf, v, _, h => by
    iterate 2 bind_inv h
    exact (opMem_se h).tight ht
  | p, .mindex ak b i, v, _, h => by
    iterate 4 bind_inv h
    exact (opMem_se h).tight ht

theorem OpLoc.bump_tight (hd : DeepOk C) (hwt : RunWT C Γ H σ) (hc : Canon C H σ)
    (ht : Tight C σ) {op : IncDec} :
    ∀ {p : PrimTy} (l : OpLoc C p) {w : Value}, l.wt Γ = true → l.bump σ op = .ok (σ', w) →
      Tight C σ'
  | p, .local x, w, hw, h => by
    obtain ⟨b, hb, _⟩ := hwt.lookup hw
    simp only [OpLoc.bump, bumpLocal, hb, bind, Except.bind] at h
    cases b with
    | val old =>
      simp only [pure, Except.pure] at h
      split at h
      · exact nomatch h
      · split at h
        · exact nomatch h
        · cases h; exact ht.setEnv x (fun _ _ h => Binding.noConfusion h)
    | spath _ _ => exact nomatch h
    | mref _ => exact nomatch h
    | store _ => exact nomatch h
    | ledger _ => exact nomatch h
  | p, .root r hr, w, _, h =>
    bumpStore_tight hd hc ht (Contract.layout_tyAt_root hr) (fun _ _ => trivial)
      (fun V _ => IdxLive.nil V) h
  | p, .field b f hf, w, hw, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    exact bumpStore_tight hd hc ht (Loc.resolve_wt hwt (.field b f hf) hw hr)
      (Loc.resolve_keys hwt ht.env (.field b f hf) hw hr) (Loc.resolve_live (.field b f hf) hr) h
  | p, .index it b i, w, hw, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    exact bumpStore_tight hd hc ht (Loc.resolve_wt hwt (.index it b (.simple i)) hw hr)
      (Loc.resolve_keys hwt ht.env (.index it b (.simple i)) hw hr)
      (Loc.resolve_live (.index it b (.simple i)) hr) h
  | p, .mfield b f hf, w, _, h => by
    iterate 2 bind_inv h
    exact (bumpMem_se h).tight ht
  | p, .mindex ak b i, w, _, h => by
    iterate 4 bind_inv h
    exact (bumpMem_se h).tight ht

/-- A storage write through a checked location: `alice.age = 3;`, `alice = bob;`. -/
theorem Tight.writeLoc (hd : DeepOk C) (hwt : RunWT C Γ H σ) (hc : Canon C H σ)
    (ht : Tight C σ) {T : Ty} {l : Loc C T} {r : Name} {segs : List Seg} {sv : SVal}
    (hw : l.wt Γ = true) (hr : l.resolve σ = .ok (r, segs)) (hsc : sv.canon T)
    (hst : sv.tight T) (h : σ.writeStorage r segs sv = .ok σ') : Tight C σ' :=
  ht.write hd hc (Loc.resolve_wt hwt l hw hr) (Loc.resolve_keys hwt ht.env l hw hr)
    (fun _ => Loc.resolve_live l hr) hsc hst h

/-- A copy out of memory stored at a checked location: `alice = m;`. -/
theorem copyMToSt_tight (hd : DeepOk C) {s : State} {rem : List Nat} {mv : MVal} {sv : SVal}
    {r : Name} {segs : List Seg} {T : Ty} (hT : C.layout.tyAt r segs = some T)
    (hsc : sv.canon T) (h : copyMToSt s rem mv = .ok sv) : sv.tight T := by
  obtain ⟨T₀, hr, hs⟩ := Layout.tyAt_split hT
  exact plain_tight (copyMToSt_plain h) hsc (okDeep_tyAtSegs (hd r T₀ hr) hs)

end Run

section RunAll

variable {Γ : Ctx} {H : HeapTy} {σ σ' : State}

theorem tyAt_okDeep (hd : DeepOk C) {r : Name} {segs : List Seg} {T : Ty}
    (hT : C.layout.tyAt r segs = some T) : T.okDeep = true := by
  obtain ⟨T₀, hr, hs⟩ := Layout.tyAt_split hT
  exact okDeep_tyAtSegs (hd r T₀ hr) hs

/-- `p = alice;`, `p = persons.push();` bind an alias along numeric keys. -/
theorem ARhs.bind_tight (hd : DeepOk C) (hwt : RunWT C Γ H σ) (hc : Canon C H σ)
    (ht : Tight C σ) {x : Var} {R : RefTy} {r : ARhs C R} (hw : r.wt Γ = true)
    (h : r.bind σ x = .ok σ') : Tight C σ' := by
  cases r with
  | path p =>
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨T, hT, -⟩ := Layout.tyAt_split (SPath.resolve_wt hwt p hw hr)
    exact ht.setEnv_path x (SPath.resolve_keys hwt ht.env p hw hr) ⟨T, hT⟩
  | push b hdo =>
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨⟨σ₁, n⟩, hpush, h⟩ := bind_ok_inv h
    cases h
    have hty := SPath.resolve_wt hwt b hw hr
    have hk := SPath.resolve_keys hwt ht.env b hw hr
    obtain ⟨T, hT, hs⟩ := Layout.tyAt_split hty
    refine (pushPlaceAt_tight hd hc ht hty hk hpush).setEnv_path x ?_ ⟨T, hT⟩
    intro T₀ hT₀
    cases hT.symm.trans hT₀
    exact KeysOK_append _ (hk T hT) hs (fun K V h => nomatch h)

mutual

/-- **Tightness, statement level**: a checked statement run from a
well-typed, canonical, tight state ends in a tight one. -/
theorem Stmt.run_tight (hd : DeepOk C) : ∀ (s : Stmt C) {Γ Γ' : Ctx} {H : HeapTy} {σ σ' : State},
    RunWT C Γ H σ → Canon C H σ → Tight C σ → s.wt Γ = some Γ' → s.run σ = .ok σ' →
      Tight C σ'
  | .assign l r, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    exact ht.writeLoc hd hwt hcn hc.1 hr (Src.value_canon hwt hcn hc.2 hsv)
      (Src.value_tight hd hwt hcn ht hc.2 hsv) h
  | .rebind x r, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    exact ARhs.bind_tight hd hwt hcn ht hc.2 h
  | .assignLocal x r, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨w, _, h⟩ := bind_ok_inv h
    cases h
    exact ht.setEnv x (fun _ _ h => Binding.noConfusion h)
  | .declLocal p x init, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    simp only [Stmt.run] at h
    cases init <;>
    · obtain ⟨w, _, h⟩ := bind_ok_inv h
      cases h
      exact ht.setEnv x (fun _ _ h => Binding.noConfusion h)
  | .declStorage R x init, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    cases init with
    | none => cases h; exact ht
    | some r =>
      obtain ⟨hc, rfl⟩ := wt_if hs
      exact ARhs.bind_tight hd hwt hcn ht hc h
  | .opAssign op hop hp l r, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨v, _, h⟩ := bind_ok_inv h
    exact OpLoc.store_tight hd hwt hcn ht l hc.1 h
  | .incDec op hp l, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    obtain ⟨⟨σ₁, w⟩, hb, h⟩ := bind_ok_inv h
    cases h
    exact OpLoc.bump_tight hd hwt hcn ht l hc hb
  | .assignIncDec x op hp l _, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨σ₁, w⟩, hb, h⟩ := bind_ok_inv h
    cases h
    exact (OpLoc.bump_tight hd hwt hcn ht l hc.2 hb).setEnv x
      (fun _ _ h => Binding.noConfusion h)
  | .push b v hdo, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    refine pushAt_tight hd hcn ht (SPath.resolve_wt hwt b hc.1 hr)
      (SPath.resolve_keys hwt ht.env b hc.1 hr) ?_ h
    intro slot w hslot hw
    cases v with
    | none => cases hw; exact hslot
    | some r =>
      obtain ⟨v, hv, hw⟩ := bind_ok_inv hw
      cases hw
      exact SVal.strip_tight (Src.value_tight hd hwt hcn ht (by simpa using hc.2) hv)
  | .pop b, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    exact popAt_tight hd hcn ht (SPath.resolve_wt hwt b hc hr)
      (SPath.resolve_keys hwt ht.env b hc hr) h
  | .transfer r a, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    iterate 4 bind_inv h
    exact (transferAt_se h).tight ht
  | .send pv r a, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    iterate 4 bind_inv h
    unfold sendAt at h
    split at h
    · exact nomatch h
    · split at h <;> cases h
      · exact ((pay_se _ _).tight ht).setEnv pv (fun _ _ h => Binding.noConfusion h)
      · exact ((pay_se _ _).tight ht).setEnv pv (fun _ _ h => Binding.noConfusion h)
      · exact ht.setEnv pv (fun _ _ h => Binding.noConfusion h)
  | .declMem R x init hdo, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    cases init with
    | none =>
      obtain ⟨⟨σ₁, id⟩, ha, h⟩ := bind_ok_inv h
      cases h
      exact ((allocDefault_se ha).tight ht).setEnv x (fun _ _ h => Binding.noConfusion h)
    | some r =>
      obtain ⟨σ₁, id, hse, rfl⟩ := MRhs.bind_se h
      exact (hse.tight ht).setEnv x (fun _ _ h => Binding.noConfusion h)
  | .rebindMem x r, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨σ₁, id, hse, rfl⟩ := MRhs.bind_se h
    exact (hse.tight ht).setEnv x (fun _ _ h => Binding.noConfusion h)
  | .assignFromMem l p, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    have hm := MPath.mval_wt hwt p hc.2 hm0
    rw [MVal.asRef_ok hid] at hm
    have hT := Loc.resolve_wt hwt l hc.1 hr
    have hsc := copyMToSt_canon hwt.heap hcn.heap hm hsv
    exact ht.writeLoc hd hwt hcn hc.1 hr hsc (copyMToSt_tight hd hT hsc hsv) h
  | .assignMem l r, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨mv, _, h⟩ := bind_ok_inv h
    exact (MLoc.write_se l h).tight ht
  | .delete l, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨cur, hcur, h⟩ := bind_ok_inv h
    have hty := Loc.resolve_wt hwt l hc hr
    exact ht.save hd hcn hty (Loc.resolve_keys hwt ht.env l hc hr)
      (fun _ => Loc.resolve_live l hr)
      (SVal.defaultOf_tight (hcn.find hty hcur) (ht.find hd hcn hty hcur) (tyAt_okDeep hd hty)) h
  | @Stmt.deleteMem _ T p hdo, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    cases p with
    | var x =>
      obtain ⟨⟨σ₁, id⟩, ha, h⟩ := bind_ok_inv h
      cases h
      exact ((allocDefault_se ha).tight ht).setEnv x (fun _ _ h => Binding.noConfusion h)
    | loc l =>
      obtain ⟨a, _, h⟩ := bind_ok_inv h
      exact (memClear_se h).tight ht
  | .assignNew l n hn, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    bind_inv h
    obtain ⟨nv, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨σ₁, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have ht₁ := (copyStToM_se hcopy).tight ht
    cases l with
    | store l =>
      obtain ⟨H', hout, hmv⟩ := copyStToM_canon hwt.heapTyNodup hwt.heap hwt.heapWf hcn.heap
        (newArrVal_hasTy hn nv) (newArrVal_canon hn nv) hcopy
      rw [MVal.asRef_ok hid] at hmv
      have hwt₁ := hwt.ofCopyOut hout.out
      have hcn₁ : Canon C H' σ₁ := ⟨hout.out.storage ▸ hcn.storage, hout.canon⟩
      obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
      obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
      have hT := Loc.resolve_wt hwt₁ l hc.1 hr
      have hsc := copyMToSt_canon hwt₁.heap hcn₁.heap hmv hsv
      exact ht₁.writeLoc hd hwt₁ hcn₁ hc.1 hr hsc (copyMToSt_tight hd hT hsc hsv) h
    | mem l => exact (MLoc.write_se l h).tight ht₁
  | .ite c thn els, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    simp only [Stmt.wt] at hs
    split at hs
    · split at hs
      · rename_i Γt Γe htt he
        obtain ⟨_, rfl⟩ := wt_if hs
        obtain ⟨cv, _, h⟩ := bind_ok_inv h
        split at h
        · exact Prog.run_tight hd thn hwt hcn ht htt h
        · exact Prog.run_tight hd els hwt hcn ht he h
        · exact nomatch h
      · exact nomatch hs
    · exact nomatch hs
  | .require c, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨cv, _, h⟩ := bind_ok_inv h
    unfold guardOk at h
    split at h
    · cases h; exact ht
    · exact nomatch h
    · exact nomatch h
  | .assert c, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    obtain ⟨cv, _, h⟩ := bind_ok_inv h
    unfold assertOk at h
    split at h
    · cases h; exact ht
    · exact nomatch h
    · exact nomatch h
  | .revert, _, _, _, _, _, _, _, _, _, h => nomatch h
  | .call _ args _ ret body, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    simp only [Stmt.wt] at hs
    split at hs
    · rename_i Γ₁ h₁
      split at hs
      · rename_i Γ₂ h₂
        obtain ⟨hr, rfl⟩ := wt_if hs
        simp only [Stmt.run] at h
        obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
        obtain ⟨σ₂, hσ₂, h⟩ := bind_ok_inv h
        obtain ⟨hs₁, hh₁⟩ := Arg.bindSeq_locals hσ₁
        obtain ⟨hs₁', hh₁'⟩ : (ret.enter σ₁).storage = σ.storage ∧ (ret.enter σ₁).heap = σ.heap :=
          CallRet.enter_induct (P := fun τ => τ.storage = σ.storage ∧ τ.heap = σ.heap)
            (fun _ _ _ h => h) ret ⟨hs₁, hh₁⟩
        have hcn₁ : Canon C H (ret.enter σ₁) := hcn.of_eq hs₁' hh₁'
        have ht₂ := Prog.run_tight hd body (CallRet.enter_wt (Arg.bindSeq_wt hwt h₁ hσ₁) ret) hcn₁
          (CallRet.enter_tight (Arg.bindSeq_tight ht hσ₁) ret) h₂ hσ₂
        exact CallRet.leave_tight ht₂ ret h
      · exact nomatch hs
    · exact nomatch hs
  | .tryCall c rets ok err code pnc other, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    simp only [Stmt.wt] at hs
    split at hs
    · split at hs
      · rename_i Γ₁ Γ₂ Γ₃ Γ₄ h₁ h₂ h₃ h₄
        obtain ⟨_, rfl⟩ := wt_if hs
        simp only [Stmt.run] at h
        obtain ⟨k, _, h⟩ := bind_ok_inv h
        split at h
        · exact nomatch h
        · obtain ⟨σ₁, hb, h⟩ := bind_ok_inv h
          obtain ⟨hs₁, hh₁⟩ := bindData_locals hb
          exact Prog.run_tight hd ok (bindData_wt hwt hb) (hcn.of_eq hs₁ hh₁)
            (bindData_tight ht hb) h₁ h
        · exact Prog.run_tight hd err hwt hcn ht h₂ h
        · obtain ⟨σ₁, hb, h⟩ := bind_ok_inv h
          obtain ⟨hs₁, hh₁⟩ := bindData_locals hb
          exact Prog.run_tight hd pnc (bindData_wt hwt hb) (hcn.of_eq hs₁ hh₁)
            (bindData_tight ht hb) h₃ h
        · exact Prog.run_tight hd other hwt hcn ht h₄ h
      · exact nomatch hs
    · exact nomatch hs

/-- **Tightness, block level.** -/
theorem Prog.run_tight (hd : DeepOk C) : ∀ (P : List (Stmt C)) {Γ Γ' : Ctx} {H : HeapTy}
    {σ σ' : State}, RunWT C Γ H σ → Canon C H σ → Tight C σ → Prog.wt Γ P = some Γ' →
      Prog.run σ P = .ok σ' → Tight C σ'
  | [], Γ, Γ', H, σ, σ', _, _, ht, _, h => by cases h; exact ht
  | s :: P, Γ, Γ', H, σ, σ', hwt, hcn, ht, hs, h => by
    simp only [Prog.wt] at hs
    split at hs
    · rename_i Γ₁ h₁
      obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
      obtain ⟨H₁, _, hwt₁, hcn₁⟩ := Stmt.run_canon s hwt hcn h₁ hσ₁
      exact Prog.run_tight hd P hwt₁ hcn₁ (Stmt.run_tight hd s hwt hcn ht h₁ hσ₁) hs h
    · exact nomatch hs

end

end RunAll

/-! ### The characterisation -/

theorem deepOk_of_all (h : C.vars.all (·.2.okDeep) = true) : DeepOk C :=
  fun _ _ hr => List.all_eq_true.mp h _ (lookupBy_eq_some_mem hr)

theorem defaultOkS_of_deep (h : C.vars.all (·.2.okDeep) = true) :
    C.vars.all (·.2.defaultOkS) = true :=
  List.all_eq_true.mpr fun g hg => okDeep_defaultOkS (List.all_eq_true.mp h g hg)

/-- A contract starts tight: each root at its type's default, no alias. -/
theorem Tight.init (hd : DeepOk C) : Tight C C.initState := by
  refine ⟨fun r T v hr hv => ?_, fun x r segs h => nomatch h⟩
  simp only [Contract.initState, Contract.initStorage, lookupBy_map_snd, hr, Option.map_some,
    Option.some.injEq] at hv
  subst hv
  exact defaultForTy_tight (okDeep_defaultOkS (hd r T hr))

/-- **Reachable ⇒ tight.** -/
theorem reachable_tight (hnd : nodupKeysB C.vars = true) (hdeep : C.vars.all (·.2.okDeep) = true)
    {st : List (Name × SVal)} (h : Reachable C st) : TightStorage C st := by
  obtain ⟨P, Γ', σ, hP, hrun, rfl⟩ := h
  have hok := defaultOkS_of_deep hdeep
  exact (Prog.run_tight (deepOk_of_all hdeep) P (RunWT.init hnd hok rfl rfl) (Canon.init hok rfl)
    (Tight.init (deepOk_of_all hdeep)) hP hrun).storage

/-- **The reachable storages, exactly**: for a contract whose types have
well-formed defaults all the way down, a storage is reachable by a checked
program iff it is canonical and tight. -/
theorem reachable_iff (hnd : nodupKeysB C.vars = true) (hdeep : C.vars.all (·.2.okDeep) = true)
    {st : List (Name × SVal)} : Reachable C st ↔ CanonStorage C st ∧ TightStorage C st :=
  ⟨fun h => ⟨(reachable_canon hnd (defaultOkS_of_deep hdeep) h).2, reachable_tight hnd hdeep h⟩,
    fun ⟨hc, ht⟩ => canon_reachable hnd (defaultOkS_of_deep hdeep) hc ht⟩

/-! ### What is reachable and what is not -/

section Witnesses

/-- One `uint[]` root. -/
def Words : Contract := contract!{ uint[] xs; }

/-- One `uint[2]` root. -/
def Pairs : Contract := contract!{ uint[2] pair; }

/-- One `bool`-keyed mapping root. -/
def BoolKeyed : Contract := contract!{ mapping(bool => uint) flags; }

/-- One `Token[]` root. -/
def Tokens : Contract := contract!{ Token[] tokens; }

/-- A word past the end of a `uint[]` that is not cleared: canonical, not
reachable, since `pop`, `delete` and a shorter copy clear the words they
leave behind and nothing writes past the end of an array of words. -/
theorem dirty_word_not_reachable :
    CanonStorage Words [("xs", .array [] [.int 5] false)] ∧
      ¬ Reachable Words [("xs", .array [] [.int 5] false)] := by
  refine ⟨⟨rfl, fun r T hr => ?_⟩, fun h => ?_⟩
  · simp only [Words, lookupBy] at hr
    split at hr
    · rename_i he; subst he; cases hr
      exact ⟨_, rfl, rfl, trivial, trivial, trivial⟩
    · exact nomatch hr
  · have ht := reachable_tight (by decide) (by decide) h "xs" _ _ rfl rfl
    have := ht.2.1 rfl (.int 5) (by simp)
    simp [defaultForTy] at this

/-- A slot past the end of a fixed-size array: canonical, not reachable. -/
theorem fixed_past_end_not_reachable :
    CanonStorage Pairs [("pair", .array [.int 0, .int 0] [.int 0] true)] ∧
      ¬ Reachable Pairs [("pair", .array [.int 0, .int 0] [.int 0] true)] := by
  refine ⟨⟨rfl, fun r T hr => ?_⟩, fun h => ?_⟩
  · simp only [Pairs, lookupBy] at hr
    split at hr
    · rename_i he; subst he; cases hr
      exact ⟨_, rfl, rfl, rfl, ⟨trivial, trivial, trivial⟩, trivial, trivial⟩
    · exact nomatch hr
  · have ht := reachable_tight (by decide) (by decide) h "pair" _ _ rfl rfl
    exact nomatch ht.1

/-- An entry in a `bool`-keyed mapping: canonical, not reachable, since a
key is read as a number (`Value.asInt`) and a `bool` is not one. -/
theorem bool_key_not_reachable :
    CanonStorage BoolKeyed [("flags", .map [(1, .int 3)] (.int 0))] ∧
      ¬ Reachable BoolKeyed [("flags", .map [(1, .int 3)] (.int 0))] := by
  refine ⟨⟨rfl, fun r T hr => ?_⟩, fun h => ?_⟩
  · simp only [BoolKeyed, lookupBy] at hr
    split at hr
    · rename_i he; subst he; cases hr
      exact ⟨_, rfl, rfl, ⟨trivial, trivial⟩, defaultForTy_uint.symm, trivial⟩
    · exact nomatch hr
  · have ht := reachable_tight (by decide) (by decide) h "flags" _ _ rfl rfl
    exact nomatch ht.1 rfl

/-- A `Token` past the end of `tokens`, written through a reference taken
before its `pop`: reachable, by the builder. -/
theorem dangling_slot_reachable :
    Reachable Tokens [("tokens", .array [] [.struct [("value", .int 7)]] false)] := by
  refine canon_reachable (by decide) (by decide) ⟨rfl, fun r T hr => ?_⟩ fun r T v hr hv => ?_
  · simp only [Tokens, lookupBy] at hr
    split at hr
    · rename_i he; subst he; cases hr
      exact ⟨_, rfl, rfl, trivial, ⟨⟨rfl, trivial, trivial⟩, trivial⟩⟩
    · exact nomatch hr
  · simp only [Tokens, lookupBy] at hr
    split at hr
    · rename_i he; subst he; cases hr
      simp only [lookupBy, if_pos] at hv
      cases hv
      exact ⟨fun h => absurd h (by decide), (fun h => nomatch h), trivial, ⟨⟨trivial, trivial⟩, trivial⟩⟩
    · exact nomatch hr

end Witnesses

end Exact

end Solidity
